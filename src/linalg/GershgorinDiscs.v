(* ========================================================================= *)
(*        GERSHGORIN DISCS — Eigenvalue Localization over Q                  *)
(*                                                                           *)
(*  The Gershgorin circle theorem for 2×2 matrices, plus applications:       *)
(*  diagonal dominance, spectral radius bounds, eigenvalue localization.     *)
(*                                                                           *)
(*  STATUS: ~20 Qed, 0 Admitted                                             *)
(*  AXIOMS: classic (for nonzero component extraction)                       *)
(*  Author: Horsocrates | Date: March 2026                                   *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs List Lia ZArith.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import LinearAlgebra.
From ToS Require Import CauchyReal.
From ToS Require Import physics.InnerProductSpace.
From ToS Require Import physics.QState.
From ToS Require Import physics.Orthogonality.
From ToS Require Import physics.QObservable.
From ToS Require Import physics.SpinChain.
From ToS Require Import linalg.MatrixOps.
From ToS Require Import linalg.EigenvalueTheory.

From Stdlib Require Import Classical.

(* ========================================================================= *)
(*  PART I: Nonzero component extraction                                     *)
(* ========================================================================= *)

Lemma nonzero_component_exists : forall {n} (v : QVec n),
  ~ qv_eq v (qv_zero n) ->
  exists i, (i < n)%nat /\ ~ (qv_nth v i == 0).
Proof.
  intros n v Hne.
  destruct (classic (exists i, (i < n)%nat /\ ~ (qv_nth v i == 0))) as [H | H].
  - exact H.
  - exfalso. apply Hne. intros i Hi. rewrite qv_zero_nth; [| exact Hi].
    destruct (classic (qv_nth v i == 0)) as [Hz | Hnz].
    + exact Hz.
    + exfalso. apply H. exists i. exact (conj Hi Hnz).
Qed.

Lemma nonzero_component_positive_abs : forall {n} (v : QVec n) i,
  ~ (qv_nth v i == 0) -> 0 < Qabs (qv_nth v i).
Proof.
  intros n v i Hne.
  destruct (Qlt_le_dec (qv_nth v i) 0) as [Hn | Hp].
  - rewrite Qabs_neg; lra.
  - rewrite Qabs_pos; [| exact Hp].
    destruct (Qeq_dec (qv_nth v i) 0) as [Hz | Hnz]; [exfalso; exact (Hne Hz) | lra].
Qed.

(* ========================================================================= *)
(*  PART II: Eigenvalue equation helper                                      *)
(* ========================================================================= *)

Lemma eigenvalue_component : forall {n} (M : QMat n n) v lambda i,
  (i < n)%nat ->
  qv_eq (mat_vec_mul M v) (qv_scale lambda v) ->
  dot_product (mat_row M i) v == lambda * qv_nth v i.
Proof.
  intros n M v lambda i Hi Heig.
  specialize (Heig i Hi).
  rewrite mat_vec_mul_nth in Heig; [| exact Hi].
  rewrite qv_scale_nth in Heig; [| exact Hi].
  exact Heig.
Qed.

(** 2-element dot product expansion *)
Lemma dot_product_2 : forall (u v : QVec 2),
  dot_product u v == qv_nth u 0 * qv_nth v 0 + qv_nth u 1 * qv_nth v 1.
Proof.
  intros [du Hlu] [dv Hlv].
  unfold dot_product, qv_nth. simpl.
  destruct du as [| a [| b [| ? ?]]]; simpl in Hlu; try lia.
  destruct dv as [| c [| d [| ? ?]]]; simpl in Hlv; try lia.
  simpl. ring.
Qed.

(** For 2×2 eigenvalue: expand to entry-level equations *)
Lemma eigenvalue_2x2_equations : forall (M : QMat 2 2) v lambda,
  qv_eq (mat_vec_mul M v) (qv_scale lambda v) ->
  mat_entry M 0 0 * qv_nth v 0 + mat_entry M 0 1 * qv_nth v 1 == lambda * qv_nth v 0 /\
  mat_entry M 1 0 * qv_nth v 0 + mat_entry M 1 1 * qv_nth v 1 == lambda * qv_nth v 1.
Proof.
  intros M v lambda Heig.
  assert (H0 := eigenvalue_component M v lambda 0%nat ltac:(lia) Heig).
  assert (H1 := eigenvalue_component M v lambda 1%nat ltac:(lia) Heig).
  rewrite dot_product_2 in H0. rewrite dot_product_2 in H1.
  (* H0 now has qv_nth (mat_row M 0) 0/1 — these are mat_entry M 0 0/1 *)
  change (qv_nth (mat_row M 0%nat) 0%nat) with (mat_entry M 0%nat 0%nat) in H0.
  change (qv_nth (mat_row M 0%nat) 1%nat) with (mat_entry M 0%nat 1%nat) in H0.
  change (qv_nth (mat_row M 1%nat) 0%nat) with (mat_entry M 1%nat 0%nat) in H1.
  change (qv_nth (mat_row M 1%nat) 1%nat) with (mat_entry M 1%nat 1%nat) in H1.
  split; [exact H0 | exact H1].
Qed.

(* ========================================================================= *)
(*  PART III: Gershgorin Theorem for 2×2                                     *)
(* ========================================================================= *)

(** Gershgorin for 2×2: eigenvalue in at least one disc *)
Theorem gershgorin_2x2 : forall (M : QMat 2 2) lambda,
  is_eigenvalue M lambda ->
  (Qabs (lambda - mat_entry M 0 0) <= Qabs (mat_entry M 0 1)) \/
  (Qabs (lambda - mat_entry M 1 1) <= Qabs (mat_entry M 1 0)).
Proof.
  intros M lambda [v [Hne Heig]].
  destruct (eigenvalue_2x2_equations M v lambda Heig) as [H0 H1].
  destruct (classic (qv_nth v 0%nat == 0)) as [Hv0z | Hv0nz];
  destruct (classic (qv_nth v 1%nat == 0)) as [Hv1z | Hv1nz].
  - exfalso. apply Hne. intros i Hi. rewrite qv_zero_nth; [| exact Hi].
    destruct i as [| [| ?]]; try lia; assumption.
  - (* v[0]=0, v[1]≠0: lambda = M[1,1] *)
    right.
    setoid_rewrite Hv0z in H1.
    assert (Hentry : (lambda - mat_entry M 1%nat 1%nat) * qv_nth v 1%nat == 0) by lra.
    destruct (Qmult_integral _ _ Hentry) as [Hd | Hvz].
    + setoid_replace (lambda - mat_entry M 1%nat 1%nat) with 0 by lra.
      rewrite Qabs_pos; [| lra]. apply Qabs_nonneg.
    + exfalso. exact (Hv1nz Hvz).
  - (* v[0]≠0, v[1]=0: lambda = M[0,0] *)
    left.
    setoid_rewrite Hv1z in H0.
    assert (Hentry : (lambda - mat_entry M 0%nat 0%nat) * qv_nth v 0%nat == 0) by lra.
    destruct (Qmult_integral _ _ Hentry) as [Hd | Hvz].
    + setoid_replace (lambda - mat_entry M 0%nat 0%nat) with 0 by lra.
      rewrite Qabs_pos; [| lra]. apply Qabs_nonneg.
    + exfalso. exact (Hv0nz Hvz).
  - (* Both nonzero: pick max component *)
    destruct (Qlt_le_dec (Qabs (qv_nth v 0%nat)) (Qabs (qv_nth v 1%nat))) as [Hgt1 | Hge0].
    + right.
      assert (Hpos : 0 < Qabs (qv_nth v 1%nat))
        by (apply nonzero_component_positive_abs; exact Hv1nz).
      assert (Heq : (lambda - mat_entry M 1%nat 1%nat) * qv_nth v 1%nat ==
                     mat_entry M 1%nat 0%nat * qv_nth v 0%nat) by lra.
      assert (Habs_eq : Qabs ((lambda - mat_entry M 1%nat 1%nat) * qv_nth v 1%nat) ==
                         Qabs (mat_entry M 1%nat 0%nat * qv_nth v 0%nat))
        by (apply Qabs_wd; exact Heq).
      rewrite !Qabs_Qmult in Habs_eq.
      assert (Hle : Qabs (mat_entry M 1%nat 0%nat) * Qabs (qv_nth v 0%nat) <=
                     Qabs (mat_entry M 1%nat 0%nat) * Qabs (qv_nth v 1%nat)).
      { rewrite (Qmult_comm (Qabs (mat_entry M 1%nat 0%nat)) (Qabs (qv_nth v 0%nat))).
        rewrite (Qmult_comm (Qabs (mat_entry M 1%nat 0%nat)) (Qabs (qv_nth v 1%nat))).
        apply Qmult_le_compat_r; [lra | apply Qabs_nonneg]. }
      apply Qmult_le_r with (z := Qabs (qv_nth v 1%nat)); [exact Hpos |]. lra.
    + left.
      assert (Hpos : 0 < Qabs (qv_nth v 0%nat))
        by (apply nonzero_component_positive_abs; exact Hv0nz).
      assert (Heq : (lambda - mat_entry M 0%nat 0%nat) * qv_nth v 0%nat ==
                     mat_entry M 0%nat 1%nat * qv_nth v 1%nat) by lra.
      assert (Habs_eq : Qabs ((lambda - mat_entry M 0%nat 0%nat) * qv_nth v 0%nat) ==
                         Qabs (mat_entry M 0%nat 1%nat * qv_nth v 1%nat))
        by (apply Qabs_wd; exact Heq).
      rewrite !Qabs_Qmult in Habs_eq.
      assert (Hle : Qabs (mat_entry M 0%nat 1%nat) * Qabs (qv_nth v 1%nat) <=
                     Qabs (mat_entry M 0%nat 1%nat) * Qabs (qv_nth v 0%nat)).
      { rewrite (Qmult_comm (Qabs (mat_entry M 0%nat 1%nat)) (Qabs (qv_nth v 1%nat))).
        rewrite (Qmult_comm (Qabs (mat_entry M 0%nat 1%nat)) (Qabs (qv_nth v 0%nat))).
        apply Qmult_le_compat_r; [lra | apply Qabs_nonneg]. }
      apply Qmult_le_r with (z := Qabs (qv_nth v 0%nat)); [exact Hpos |]. lra.
Qed.

(* ========================================================================= *)
(*  PART IV: Applications                                                    *)
(* ========================================================================= *)

(** Disc always contains its center *)
Lemma gershgorin_disc_contains_center : forall (M : QMat 2 2) (i : nat),
  (i < 2)%nat ->
  Qabs (mat_entry M i i - mat_entry M i i) <= Qabs (mat_entry M i (1 - i)).
Proof.
  intros M i Hi.
  setoid_replace (mat_entry M i i - mat_entry M i i) with 0 by ring.
  rewrite Qabs_pos; [| lra]. apply Qabs_nonneg.
Qed.

(** Identity matrix: all eigenvalues = 1 *)
Theorem gershgorin_id : forall n,
  (0 < n)%nat ->
  forall lambda, is_eigenvalue (id_mat n) lambda -> lambda == 1.
Proof.
  intros n Hn lambda [v [Hne Heig]].
  destruct (nonzero_component_exists v Hne) as [i [Hi Hni]].
  assert (Hcomp := eigenvalue_component (id_mat n) v lambda i Hi Heig).
  unfold mat_row, id_mat in Hcomp. simpl in Hcomp.
  rewrite (nth_map_general _ (seq 0 n) 0%nat (qv_zero n) i) in Hcomp;
    [| rewrite seq_length; exact Hi].
  rewrite seq_nth in Hcomp; [| exact Hi]. simpl in Hcomp.
  rewrite dot_basis_extracts in Hcomp; [| exact Hi].
  assert (Hdiff : (1 - lambda) * qv_nth v i == 0) by lra.
  destruct (Qmult_integral _ _ Hdiff) as [Hd | Hvz]; [lra | exfalso; exact (Hni Hvz)].
Qed.

(** Diagonal matrix: eigenvalues = diagonal entries *)
Theorem gershgorin_diag : forall {n} (eigenvals : QVec n) lambda,
  (0 < n)%nat ->
  is_eigenvalue (diag_mat eigenvals) lambda ->
  exists j, (j < n)%nat /\ lambda == qv_nth eigenvals j.
Proof.
  intros n eigenvals lambda Hn [v [Hne Heig]].
  destruct (nonzero_component_exists v Hne) as [i [Hi Hni]].
  exists i. split; [exact Hi |].
  (* Use diag_mat_action directly on the eigenvector equation *)
  specialize (Heig i Hi).
  rewrite diag_mat_action in Heig; [| exact Hi].
  rewrite qv_scale_nth in Heig; [| exact Hi].
  assert (Hdiff : (qv_nth eigenvals i - lambda) * qv_nth v i == 0) by lra.
  destruct (Qmult_integral _ _ Hdiff) as [Hd | Hvz]; [lra | exfalso; exact (Hni Hvz)].
Qed.

(** Spectral radius bound for 2×2 *)
Definition Qmax2 (a b : Q) : Q := if Qle_bool a b then b else a.

Lemma Qmax2_le_l : forall a b, a <= Qmax2 a b.
Proof.
  intros a b. unfold Qmax2.
  destruct (Qle_bool a b) eqn:E.
  - apply Qle_bool_iff in E. exact E.
  - lra.
Qed.

Lemma Qmax2_le_r : forall a b, b <= Qmax2 a b.
Proof.
  intros a b. unfold Qmax2.
  destruct (Qle_bool a b) eqn:E.
  - lra.
  - assert (Hab : ~ a <= b).
    { intro H. apply Qle_bool_iff in H. rewrite H in E. discriminate. }
    lra.
Qed.

Definition spectral_radius_bound_2x2 (M : QMat 2 2) : Q :=
  Qmax2 (Qabs (mat_entry M 0 0) + Qabs (mat_entry M 0 1))
        (Qabs (mat_entry M 1 1) + Qabs (mat_entry M 1 0)).

Theorem spectral_radius_bound_correct : forall (M : QMat 2 2) lambda,
  is_eigenvalue M lambda ->
  Qabs lambda <= spectral_radius_bound_2x2 M.
Proof.
  intros M lambda Hev.
  assert (Hg := gershgorin_2x2 M lambda Hev).
  unfold spectral_radius_bound_2x2.
  destruct Hg as [H0 | H1].
  - assert (Htri : Qabs lambda <=
      Qabs (mat_entry M 0%nat 0%nat) + Qabs (lambda - mat_entry M 0%nat 0%nat)).
    { setoid_replace lambda
        with (mat_entry M 0%nat 0%nat + (lambda - mat_entry M 0%nat 0%nat)) at 1 by ring.
      apply Qabs_triangle. }
    apply Qle_trans with (Qabs (mat_entry M 0%nat 0%nat) + Qabs (mat_entry M 0%nat 1%nat));
      [lra | apply Qmax2_le_l].
  - assert (Htri : Qabs lambda <=
      Qabs (mat_entry M 1%nat 1%nat) + Qabs (lambda - mat_entry M 1%nat 1%nat)).
    { setoid_replace lambda
        with (mat_entry M 1%nat 1%nat + (lambda - mat_entry M 1%nat 1%nat)) at 1 by ring.
      apply Qabs_triangle. }
    apply Qle_trans with (Qabs (mat_entry M 1%nat 1%nat) + Qabs (mat_entry M 1%nat 0%nat));
      [lra | apply Qmax2_le_r].
Qed.

(** Strictly diag dominant 2×2 → no zero eigenvalue *)
Definition is_strictly_diag_dominant_2x2 (M : QMat 2 2) : Prop :=
  Qabs (mat_entry M 0 1) < Qabs (mat_entry M 0 0) /\
  Qabs (mat_entry M 1 0) < Qabs (mat_entry M 1 1).

Theorem strictly_diag_dominant_no_zero_ev : forall (M : QMat 2 2),
  is_strictly_diag_dominant_2x2 M ->
  ~ is_eigenvalue M 0.
Proof.
  intros M [Hdd0 Hdd1] [v [Hne Heig]].
  destruct (eigenvalue_2x2_equations M v 0 Heig) as [H0 H1].
  simpl in H0, H1.
  (* H0: M[0,0]*v0 + M[0,1]*v1 == 0, H1: M[1,0]*v0 + M[1,1]*v1 == 0 *)
  destruct (classic (qv_nth v 0%nat == 0)) as [Hv0z | Hv0nz];
  destruct (classic (qv_nth v 1%nat == 0)) as [Hv1z | Hv1nz].
  - apply Hne. intros i Hi. rewrite qv_zero_nth; [| exact Hi].
    destruct i as [| [| ?]]; try lia; assumption.
  - (* v = (0, v1): M[1,1]*v1 = 0, v1 ≠ 0 → M[1,1] = 0 *)
    setoid_rewrite Hv0z in H1.
    assert (Hentry : mat_entry M 1%nat 1%nat * qv_nth v 1%nat == 0) by lra.
    destruct (Qmult_integral _ _ Hentry) as [Hz | Hvz].
    + assert (Habs : Qabs (mat_entry M 1%nat 1%nat) == 0).
      { rewrite Hz. rewrite Qabs_pos; lra. }
      assert (Hnn : 0 <= Qabs (mat_entry M 1%nat 0%nat)) by apply Qabs_nonneg. lra.
    + exfalso. exact (Hv1nz Hvz).
  - (* v = (v0, 0): M[0,0]*v0 = 0, v0 ≠ 0 → M[0,0] = 0 *)
    setoid_rewrite Hv1z in H0.
    assert (Hentry : mat_entry M 0%nat 0%nat * qv_nth v 0%nat == 0) by lra.
    destruct (Qmult_integral _ _ Hentry) as [Hz | Hvz].
    + assert (Habs : Qabs (mat_entry M 0%nat 0%nat) == 0).
      { rewrite Hz. rewrite Qabs_pos; lra. }
      assert (Hnn : 0 <= Qabs (mat_entry M 0%nat 1%nat)) by apply Qabs_nonneg. lra.
    + exfalso. exact (Hv0nz Hvz).
  - (* Both nonzero: use Gershgorin *)
    assert (Hg := gershgorin_2x2 M 0 (ex_intro _ v (conj Hne Heig))).
    destruct Hg as [Hdisc0 | Hdisc1].
    + setoid_replace (0 - mat_entry M 0%nat 0%nat) with (- mat_entry M 0%nat 0%nat) in Hdisc0 by ring.
      rewrite Qabs_opp in Hdisc0. lra.
    + setoid_replace (0 - mat_entry M 1%nat 1%nat) with (- mat_entry M 1%nat 1%nat) in Hdisc1 by ring.
      rewrite Qabs_opp in Hdisc1. lra.
Qed.

(** Symmetric 2×2: eigenvalue localization in intervals *)
Theorem eigenvalue_in_interval_2x2 : forall (M : QMat 2 2) lambda,
  is_symmetric M ->
  is_eigenvalue M lambda ->
  let a := mat_entry M 0 0 in
  let b := Qabs (mat_entry M 0 1) in
  let d := mat_entry M 1 1 in
  (a - b <= lambda /\ lambda <= a + b) \/
  (d - b <= lambda /\ lambda <= d + b).
Proof.
  intros M lambda Hsym Hev a b d.
  assert (Hsym01 := Hsym 0%nat 1%nat ltac:(lia) ltac:(lia)).
  assert (Hg := gershgorin_2x2 M lambda Hev).
  destruct Hg as [H0 | H1].
  - left. fold a b in H0.
    destruct (Qlt_le_dec (lambda - a) 0) as [Hn | Hp].
    + rewrite Qabs_neg in H0; [| lra]. split; lra.
    + rewrite Qabs_pos in H0; [| exact Hp]. split; lra.
  - right.
    setoid_replace (mat_entry M 1%nat 0%nat) with (mat_entry M 0%nat 1%nat) in H1
      by (symmetry; exact Hsym01).
    fold b d in H1.
    destruct (Qlt_le_dec (lambda - d) 0) as [Hn | Hp].
    + rewrite Qabs_neg in H1; [| lra]. split; lra.
    + rewrite Qabs_pos in H1; [| exact Hp]. split; lra.
Qed.

(** Example: [[3,1],[1,2]] discs contain eigenvalues *)
Lemma gershgorin_2x2_example :
  forall lambda, is_eigenvalue (qmat2x2 3 1 1 2) lambda ->
  (Qabs (lambda - 3) <= 1) \/ (Qabs (lambda - 2) <= 1).
Proof.
  intros lambda Hev.
  assert (Hg := gershgorin_2x2 (qmat2x2 3 1 1 2) lambda Hev).
  destruct Hg as [H0 | H1].
  - left. unfold mat_entry, mat_row, qmat2x2, qvec2, qv_nth in H0. simpl in H0. exact H0.
  - right. unfold mat_entry, mat_row, qmat2x2, qvec2, qv_nth in H1. simpl in H1. exact H1.
Qed.

(** Shifted Gershgorin: shifting by σ shifts disc centers *)
Lemma gershgorin_shift_2x2 : forall (M : QMat 2 2) lambda sigma,
  is_eigenvalue M lambda ->
  (Qabs (lambda - sigma - (mat_entry M 0 0 - sigma)) <= Qabs (mat_entry M 0 1)) \/
  (Qabs (lambda - sigma - (mat_entry M 1 1 - sigma)) <= Qabs (mat_entry M 1 0)).
Proof.
  intros M lambda sigma Hev.
  assert (Hg := gershgorin_2x2 M lambda Hev).
  destruct Hg as [H0 | H1].
  - left. setoid_replace (lambda - sigma - (mat_entry M 0%nat 0%nat - sigma))
      with (lambda - mat_entry M 0%nat 0%nat) by ring. exact H0.
  - right. setoid_replace (lambda - sigma - (mat_entry M 1%nat 1%nat - sigma))
      with (lambda - mat_entry M 1%nat 1%nat) by ring. exact H1.
Qed.

(** Column sums = row sums for symmetric 2×2 *)
Lemma col_sum_equals_row_sum_symmetric : forall (M : QMat 2 2),
  is_symmetric M ->
  Qabs (mat_entry M 0 1) == Qabs (mat_entry M 1 0).
Proof.
  intros M Hsym. apply Qabs_wd. exact (Hsym 0%nat 1%nat ltac:(lia) ltac:(lia)).
Qed.

(** Diagonal dominant with positive diagonal → eigenvalues > 0 *)
Lemma diag_dominant_positive_eigenvalues_2x2 : forall (M : QMat 2 2) lambda,
  is_strictly_diag_dominant_2x2 M ->
  0 < mat_entry M 0 0 ->
  0 < mat_entry M 1 1 ->
  is_eigenvalue M lambda ->
  0 < lambda.
Proof.
  intros M lambda [Hdd0 Hdd1] Hpos0 Hpos1 Hev.
  assert (Hg := gershgorin_2x2 M lambda Hev).
  destruct Hg as [H0 | H1].
  - destruct (Qlt_le_dec (lambda - mat_entry M 0%nat 0%nat) 0) as [Hn | Hp].
    + rewrite Qabs_neg in H0; [| lra].
      rewrite (Qabs_pos (mat_entry M 0%nat 0%nat)) in Hdd0; [| lra]. lra.
    + lra.
  - destruct (Qlt_le_dec (lambda - mat_entry M 1%nat 1%nat) 0) as [Hn | Hp].
    + rewrite Qabs_neg in H1; [| lra].
      rewrite (Qabs_pos (mat_entry M 1%nat 1%nat)) in Hdd1; [| lra]. lra.
    + lra.
Qed.

(** Gershgorin summary *)
Theorem gershgorin_summary :
  (* 1. 2×2 Gershgorin *)
  (forall (M : QMat 2 2) lambda, is_eigenvalue M lambda ->
    (Qabs (lambda - mat_entry M 0 0) <= Qabs (mat_entry M 0 1)) \/
    (Qabs (lambda - mat_entry M 1 1) <= Qabs (mat_entry M 1 0))) /\
  (* 2. Identity eigenvalues = 1 *)
  (forall n, (0 < n)%nat ->
    forall lambda, is_eigenvalue (id_mat n) lambda -> lambda == 1) /\
  (* 3. Diagonal eigenvalues = diagonal entries *)
  (forall {n} (eigenvals : QVec n) lambda, (0 < n)%nat ->
    is_eigenvalue (diag_mat eigenvals) lambda ->
    exists j, (j < n)%nat /\ lambda == qv_nth eigenvals j) /\
  (* 4. Spectral radius bound *)
  (forall (M : QMat 2 2) lambda, is_eigenvalue M lambda ->
    Qabs lambda <= spectral_radius_bound_2x2 M).
Proof.
  repeat split.
  - exact gershgorin_2x2.
  - exact gershgorin_id.
  - intros n eigenvals lambda Hn Hev. exact (gershgorin_diag eigenvals lambda Hn Hev).
  - exact spectral_radius_bound_correct.
Qed.

(* ========================================================================= *)
(*  SUMMARY                                                                  *)
(* ========================================================================= *)
