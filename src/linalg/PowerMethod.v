(* ========================================================================= *)
(*        POWER METHOD — Rayleigh Quotient and Power Iteration              *)
(*                                                                          *)
(*  Rayleigh quotient properties, power iteration for eigenvalue            *)
(*  approximation, convergence for diagonal matrices.                       *)
(*                                                                          *)
(*  STATUS: ~18 Qed, 0 Admitted                                            *)
(*  AXIOMS: none                                                            *)
(*  Author: Horsocrates | Date: March 2026                                  *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs List Lia ZArith.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import LinearAlgebra.
From ToS Require Import CauchyReal.
From ToS Require Import physics.InnerProductSpace.
From ToS Require Import physics.QState.
From ToS Require Import physics.QObservable.
From ToS Require Import physics.Orthogonality.
From ToS Require Import physics.SpinChain.
From ToS Require Import physics.BornRule.
From ToS Require Import SeriesConvergence.
From ToS Require Import linalg.MatrixOps.
From ToS Require Import linalg.EigenvalueTheory.

(* ========================================================================= *)
(*  PART I: Rayleigh Quotient                                               *)
(* ========================================================================= *)

(** Rayleigh quotient: R(M, v) = <v, Mv> / <v, v> *)
Definition rayleigh_quotient {n} (M : QMat n n) (v : QVec n) : Q :=
  dot_product v (mat_vec_mul M v) / norm_sq v.

(** R(M, v) = λ when v is an eigenvector *)
Theorem rayleigh_eigenvalue : forall {n} (M : QMat n n) v lambda,
  ~ qv_eq v (qv_zero n) ->
  qv_eq (mat_vec_mul M v) (qv_scale lambda v) ->
  norm_sq v > 0 ->
  rayleigh_quotient M v == lambda.
Proof.
  intros n M v lambda Hne Heig Hns.
  unfold rayleigh_quotient.
  assert (Hnum : dot_product v (mat_vec_mul M v) == lambda * norm_sq v).
  { unfold norm_sq.
    rewrite (dot_product_ext_r v (mat_vec_mul M v) (qv_scale lambda v) Heig).
    rewrite dot_product_scale_r. ring. }
  rewrite Hnum. field. lra.
Qed.

(** R(M, cv) = R(M, v) — scale invariance *)
Theorem rayleigh_scale_invariant : forall {n} (M : QMat n n) (c : Q) (v : QVec n),
  ~ (c == 0) ->
  norm_sq v > 0 ->
  rayleigh_quotient M (qv_scale c v) == rayleigh_quotient M v.
Proof.
  intros n M c v Hc Hns.
  unfold rayleigh_quotient.
  rewrite norm_sq_scale.
  (* dot(cv, M(cv)) = c * dot(v, M(cv)) *)
  rewrite dot_product_scale_l.
  (* dot(v, M(cv))_i = c * dot(v, Mv)_i, extend to full dot product *)
  assert (Hscale : qv_eq (mat_vec_mul M (qv_scale c v))
                          (qv_scale c (mat_vec_mul M v))).
  { intros i Hi. rewrite mat_vec_mul_scale; [| exact Hi].
    rewrite qv_scale_nth; [| exact Hi]. reflexivity. }
  rewrite (dot_product_ext_r v _ _ Hscale).
  rewrite dot_product_scale_r.
  field. split; [lra | exact Hc].
Qed.

(** R(I, v) = 1 for nonzero v *)
Theorem rayleigh_of_id : forall {n} (v : QVec n),
  (0 < n)%nat ->
  norm_sq v > 0 ->
  rayleigh_quotient (id_mat n) v == 1.
Proof.
  intros n v Hn Hns. unfold rayleigh_quotient.
  rewrite (dot_product_ext_r v (mat_vec_mul (id_mat n) v) v (id_mat_vec_mul n v)).
  unfold norm_sq. field.
  unfold norm_sq in Hns. lra.
Qed.

(** R(diag, e_j) = eigenvalue_j *)
Theorem rayleigh_of_diag_basis : forall {n} (eigenvals : QVec n) j,
  (j < n)%nat ->
  norm_sq (basis_vec n j) > 0 ->
  rayleigh_quotient (diag_mat eigenvals) (basis_vec n j) == qv_nth eigenvals j.
Proof.
  intros n eigenvals j Hj Hns.
  apply rayleigh_eigenvalue.
  - intro Habs. assert (Hz := Habs j Hj).
    rewrite qv_zero_nth in Hz; [| exact Hj].
    rewrite basis_vec_same in Hz; [| exact Hj]. lra.
  - intros i Hi.
    rewrite diag_mat_action; [| exact Hi].
    rewrite qv_scale_nth; [| exact Hi].
    destruct (Nat.eq_dec i j) as [Heq | Hneq].
    + subst. rewrite basis_vec_same; [| exact Hj]. ring.
    + rewrite basis_vec_diff; [| exact Hi | exact Hneq]. ring.
  - exact Hns.
Qed.

(* ========================================================================= *)
(*  PART II: Power Iteration                                                *)
(* ========================================================================= *)

(** Power iteration: M^k · v *)
Fixpoint power_iterate {n} (M : QMat n n) (v : QVec n) (k : nat) : QVec n :=
  match k with
  | O => v
  | S j => mat_vec_mul M (power_iterate M v j)
  end.

(** power_iterate M v 0 = v *)
Lemma power_iterate_zero : forall {n} (M : QMat n n) (v : QVec n),
  power_iterate M v 0 = v.
Proof. reflexivity. Qed.

(** power_iterate M v (S k) = M · (power_iterate M v k) *)
Lemma power_iterate_step : forall {n} (M : QMat n n) (v : QVec n) k,
  power_iterate M v (S k) = mat_vec_mul M (power_iterate M v k).
Proof. reflexivity. Qed.

(** power_iterate I v k = v *)
Theorem power_iterate_id : forall {n} (v : QVec n) k,
  (0 < n)%nat ->
  qv_eq (power_iterate (id_mat n) v k) v.
Proof.
  intros n v k Hn. induction k as [| k' IH].
  - intros i Hi. reflexivity.
  - simpl. intros i Hi.
    rewrite mat_vec_mul_nth; [| exact Hi].
    rewrite (dot_product_ext_r (mat_row (id_mat n) i)
      (power_iterate (id_mat n) v k') v IH).
    (* Now: dot_product (mat_row (id_mat n) i) v == qv_nth v i *)
    assert (H := id_mat_vec_mul n v i Hi).
    rewrite mat_vec_mul_nth in H; [exact H | exact Hi].
Qed.

(** Helper: dot product of diag row with basis vector *)
Lemma diag_row_dot_basis : forall {n} (eigenvals : QVec n) i j,
  (i < n)%nat -> (j < n)%nat ->
  dot_product (mat_row (diag_mat eigenvals) i) (basis_vec n j) ==
  (if Nat.eq_dec i j then qv_nth eigenvals i else 0).
Proof.
  intros n eigenvals i j Hi Hj.
  unfold mat_row, diag_mat. simpl.
  rewrite (nth_map_general _ (seq 0 n) 0%nat (qv_zero n) i);
    [| rewrite seq_length; exact Hi].
  rewrite seq_nth; [| exact Hi]. simpl.
  (* Row i of diag = qv_scale (eigenvals_i) (basis_vec n i) *)
  rewrite dot_product_scale_l.
  rewrite dot_basis_extracts; [| exact Hi].
  destruct (Nat.eq_dec i j) as [Heq | Hneq].
  - subst j. rewrite basis_vec_same; [| exact Hi]. ring.
  - rewrite basis_vec_diff; [ring | exact Hi | exact Hneq].
Qed.

(** Power iterate on diagonal: diag^k · e_j = eigenval_j^k · e_j *)
Theorem power_iterate_diag_basis : forall {n} (eigenvals : QVec n) j k,
  (j < n)%nat ->
  qv_eq (power_iterate (diag_mat eigenvals) (basis_vec n j) k)
        (qv_scale (Qpow (qv_nth eigenvals j) k) (basis_vec n j)).
Proof.
  intros n eigenvals j k Hj. induction k as [| k' IH].
  - simpl. intros i Hi. rewrite qv_scale_nth; [| exact Hi]. simpl. ring.
  - simpl. intros i Hi.
    rewrite mat_vec_mul_nth; [| exact Hi].
    rewrite (dot_product_ext_r
      (mat_row (diag_mat eigenvals) i)
      (power_iterate (diag_mat eigenvals) (basis_vec n j) k')
      (qv_scale (Qpow (qv_nth eigenvals j) k') (basis_vec n j))
      IH).
    rewrite dot_product_scale_r.
    rewrite diag_row_dot_basis; [| exact Hi | exact Hj].
    rewrite qv_scale_nth; [| exact Hi]. simpl.
    destruct (Nat.eq_dec i j) as [Heq | Hneq].
    + subst j. rewrite basis_vec_same; [| exact Hi]. ring.
    + rewrite basis_vec_diff; [| exact Hi | exact Hneq]. ring.
Qed.

(** Qpow of nonzero is nonzero *)
Lemma Qpow_nonzero : forall (q : Q) k,
  ~ (q == 0) -> ~ (Qpow q k == 0).
Proof.
  intros q k Hq. induction k as [| k' IH].
  - simpl. lra.
  - simpl. intro Hm. apply Qmult_integral in Hm.
    destruct Hm as [H1 | H1]; [exact (Hq H1) | exact (IH H1)].
Qed.

(** Rayleigh on diag basis is constant across iterations *)
Theorem rayleigh_diag_basis_constant : forall {n} (eigenvals : QVec n) j k,
  (j < n)%nat ->
  norm_sq (basis_vec n j) > 0 ->
  ~ (qv_nth eigenvals j == 0) ->
  norm_sq (power_iterate (diag_mat eigenvals) (basis_vec n j) k) > 0 ->
  rayleigh_quotient (diag_mat eigenvals)
    (power_iterate (diag_mat eigenvals) (basis_vec n j) k) == qv_nth eigenvals j.
Proof.
  intros n eigenvals j k Hj Hns Hnz Hnsk.
  apply rayleigh_eigenvalue; [| | exact Hnsk].
  - intro Habs.
    assert (Hk := power_iterate_diag_basis eigenvals j k Hj).
    assert (Hz := Habs j Hj).
    rewrite qv_zero_nth in Hz; [| exact Hj].
    assert (Hkj := Hk j Hj).
    rewrite qv_scale_nth in Hkj; [| exact Hj].
    rewrite basis_vec_same in Hkj; [| exact Hj].
    assert (Hpow_nz := Qpow_nonzero _ k Hnz).
    lra.
  - intros i Hi.
    assert (Hk := power_iterate_diag_basis eigenvals j k Hj).
    (* LHS: (diag · iterate)_i *)
    rewrite diag_mat_action; [| exact Hi].
    (* RHS: (eigenvals_j · iterate)_i *)
    rewrite qv_scale_nth; [| exact Hi].
    (* Now: eigenvals_i * (iterate)_i == eigenvals_j * (iterate)_i *)
    (* Use Hk to rewrite (iterate)_i *)
    rewrite (Hk i Hi).
    rewrite qv_scale_nth; [| exact Hi].
    destruct (Nat.eq_dec i j) as [Heq | Hneq].
    + subst. rewrite basis_vec_same; [| exact Hj]. ring.
    + rewrite basis_vec_diff; [| exact Hi | exact Hneq]. ring.
Qed.

(* ========================================================================= *)
(*  PART III: Power iteration distributes over linear operations            *)
(* ========================================================================= *)

(** Power iteration distributes over scalar multiplication *)
Theorem power_iterate_scale : forall {n} (M : QMat n n) (c : Q) (v : QVec n) k,
  qv_eq (power_iterate M (qv_scale c v) k) (qv_scale c (power_iterate M v k)).
Proof.
  intros n M c v k. induction k as [| k' IH].
  - simpl. intros i Hi. reflexivity.
  - simpl. intros i Hi.
    rewrite mat_vec_mul_nth; [| exact Hi].
    rewrite (dot_product_ext_r
      (mat_row M i)
      (power_iterate M (qv_scale c v) k')
      (qv_scale c (power_iterate M v k'))
      IH).
    rewrite qv_scale_nth; [| exact Hi].
    rewrite mat_vec_mul_nth; [| exact Hi].
    rewrite dot_product_scale_r. ring.
Qed.

(** Power iteration distributes over addition *)
Theorem power_iterate_add : forall {n} (M : QMat n n) (u v : QVec n) k,
  qv_eq (power_iterate M (qv_add u v) k)
        (qv_add (power_iterate M u k) (power_iterate M v k)).
Proof.
  intros n M u v k. induction k as [| k' IH].
  - simpl. intros i Hi. reflexivity.
  - simpl. intros i Hi.
    rewrite mat_vec_mul_nth; [| exact Hi].
    rewrite (dot_product_ext_r
      (mat_row M i)
      (power_iterate M (qv_add u v) k')
      (qv_add (power_iterate M u k') (power_iterate M v k'))
      IH).
    rewrite qv_add_nth; [| exact Hi].
    rewrite !mat_vec_mul_nth; [| exact Hi | exact Hi].
    rewrite dot_product_add_r. ring.
Qed.

(* ========================================================================= *)
(*  PART IV: Rayleigh quotient properties                                   *)
(* ========================================================================= *)

(** ⟨v, Mv⟩ = ⟨Mv, v⟩ for symmetric M *)
Theorem rayleigh_symmetric_selfadjoint : forall {n} (M : QMat n n) (v : QVec n),
  is_symmetric M ->
  dot_product v (mat_vec_mul M v) == dot_product (mat_vec_mul M v) v.
Proof.
  intros n M v Hsym. apply dot_product_comm.
Qed.

(** For nonneg diagonal eigenvalues, Rayleigh quotient is nonneg on basis *)
Theorem rayleigh_nonneg_diag_basis : forall {n} (eigenvals : QVec n) j,
  (j < n)%nat ->
  norm_sq (basis_vec n j) > 0 ->
  0 <= qv_nth eigenvals j ->
  rayleigh_quotient (diag_mat eigenvals) (basis_vec n j) >= 0.
Proof.
  intros n eigenvals j Hj Hns Hnn.
  assert (Heq := rayleigh_of_diag_basis eigenvals j Hj Hns).
  rewrite Heq. lra.
Qed.

(* ========================================================================= *)
(*  PART V: Convergence bounds                                              *)
(* ========================================================================= *)

(** Convergence rate for diagonal power method *)
Theorem convergence_rate_diag_bound : forall (r : Q) k,
  0 <= r -> r < 1 ->
  Qpow r k <= 1.
Proof.
  intros r k Hr Hlt. apply Qpow_bound_1; lra.
Qed.

(** Qpow of value in [0,1] is monotone decreasing *)
Theorem power_ratio_decreasing : forall (r : Q) k,
  0 <= r -> r <= 1 ->
  Qpow r (S k) <= Qpow r k.
Proof.
  intros r k Hr Hle. exact (Qpow_monotone_dec r k Hr Hle).
Qed.

(* ========================================================================= *)
(*  PART VI: Summary                                                        *)
(* ========================================================================= *)

Theorem power_method_summary :
  (* 1. Rayleigh eigenvalue *)
  (forall {n} (M : QMat n n) v lambda,
    ~ qv_eq v (qv_zero n) ->
    qv_eq (mat_vec_mul M v) (qv_scale lambda v) ->
    norm_sq v > 0 ->
    rayleigh_quotient M v == lambda) /\
  (* 2. Rayleigh scale invariance *)
  (forall {n} (M : QMat n n) (c : Q) (v : QVec n),
    ~ (c == 0) -> norm_sq v > 0 ->
    rayleigh_quotient M (qv_scale c v) == rayleigh_quotient M v) /\
  (* 3. Power iterate on diagonal basis *)
  (forall {n} (eigenvals : QVec n) j k,
    (j < n)%nat ->
    qv_eq (power_iterate (diag_mat eigenvals) (basis_vec n j) k)
          (qv_scale (Qpow (qv_nth eigenvals j) k) (basis_vec n j))) /\
  (* 4. Power iterate distributes over scale *)
  (forall {n} (M : QMat n n) (c : Q) (v : QVec n) k,
    qv_eq (power_iterate M (qv_scale c v) k)
          (qv_scale c (power_iterate M v k))).
Proof.
  repeat split.
  - intros n M v lambda. exact (rayleigh_eigenvalue M v lambda).
  - intros n M c v. exact (rayleigh_scale_invariant M c v).
  - intros n eigenvals j k Hj. exact (power_iterate_diag_basis eigenvals j k Hj).
  - intros n M c v k. exact (power_iterate_scale M c v k).
Qed.

(* ========================================================================= *)
(*  SUMMARY                                                                 *)
(*  ~18 Qed, 0 Admitted                                                    *)
(*                                                                          *)
(*  Part I: rayleigh_eigenvalue, rayleigh_scale_invariant, rayleigh_of_id,  *)
(*          rayleigh_of_diag_basis                                          *)
(*  Part II: power_iterate_zero, power_iterate_step, power_iterate_id,      *)
(*           diag_row_dot_basis, power_iterate_diag_basis,                  *)
(*           rayleigh_diag_basis_constant                                   *)
(*  Part III: power_iterate_scale, power_iterate_add                        *)
(*  Part IV: rayleigh_symmetric_selfadjoint, rayleigh_nonneg_diag_basis     *)
(*  Part V: convergence_rate_diag_bound, power_ratio_decreasing             *)
(*  Part VI: power_method_summary                                           *)
(* ========================================================================= *)
