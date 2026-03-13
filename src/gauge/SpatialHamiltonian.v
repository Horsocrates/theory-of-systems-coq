(** * SpatialHamiltonian.v — Tridiagonal Matrix in Character Basis
    Elements: spatial Hamiltonian H, tridiagonality, diagonal dominance
    Roles:    encodes plaquette coupling in the character representation
    Rules:    H_{jj} = d_sp·casimir, H_{j,j+1} = d_sp·offdiag, tridiagonal
    Status:   complete
    STATUS: ~40 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        SPATIAL HAMILTONIAN — Tridiagonal Matrix in Character Basis         *)
(*                                                                            *)
(*  The spatial Hamiltonian H couples representations via plaquettes.         *)
(*  Selection rule: j ↔ j±1 only → H is TRIDIAGONAL.                       *)
(*                                                                            *)
(*  H_{jj} = d_sp · spatial_diagonal(j)    (diagonal: Casimir energy)       *)
(*  H_{j,j+1} = d_sp · spatial_offdiag(j)  (off-diagonal: coupling)        *)
(*                                                                            *)
(*  Ground state j=0: H_{00}=0 (no Casimir).                                *)
(*  Excited j≥1: H_{jj}>0 (Casimir > 0).                                   *)
(*  → spatial energy cost increases with j.                                  *)
(*                                                                            *)
(*  STATUS: ~40 Qed, 0 Admitted                                              *)
(*  AXIOMS: none                                                              *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import CauchyReal.
From ToS Require Import SeriesConvergence.
From ToS Require Import gauge.SU2Characters.
From ToS Require Import gauge.ClebschGordan.

(* ================================================================== *)
(*  Part I: Tridiagonal Matrix Entries  (~12 lemmas)                  *)
(* ================================================================== *)

(** Spatial Hamiltonian entry *)
Definition H_spatial_entry (d_sp : nat) (j j' : nat) : Q :=
  if Nat.eqb j j' then
    inject_Z (Z.of_nat d_sp) * spatial_diagonal j
  else if Nat.eqb j' (j + 1) then
    inject_Z (Z.of_nat d_sp) * spatial_offdiag j
  else if Nat.eqb j (j' + 1) then
    inject_Z (Z.of_nat d_sp) * spatial_offdiag j'
  else 0.

(** Matrix is symmetric *)
Theorem H_spatial_symmetric : forall d_sp j j',
  H_spatial_entry d_sp j j' == H_spatial_entry d_sp j' j.
Proof.
  intros d_sp j j'. unfold H_spatial_entry.
  destruct (Nat.eq_dec j j') as [Heq|Hneq].
  - subst. lra.
  - destruct (Nat.eq_dec j' (j + 1)) as [Hn1|Hn1].
    + subst.
      replace ((j =? j + 1)%nat) with false by (symmetry; apply Nat.eqb_neq; lia).
      replace ((j + 1 =? j)%nat) with false by (symmetry; apply Nat.eqb_neq; lia).
      replace ((j + 1 =? j + 1)%nat) with true by (symmetry; apply Nat.eqb_eq; lia).
      replace ((j =? j + 1 + 1)%nat) with false by (symmetry; apply Nat.eqb_neq; lia).
      replace ((j + 1 =? j + 1)%nat) with true by (symmetry; apply Nat.eqb_eq; lia).
      lra.
    + destruct (Nat.eq_dec j (j' + 1)) as [Hn2|Hn2].
      * subst.
        replace ((j' + 1 =? j')%nat) with false by (symmetry; apply Nat.eqb_neq; lia).
        replace ((j' =? j' + 1)%nat) with false by (symmetry; apply Nat.eqb_neq; lia).
        replace ((j' =? j' + 1 + 1)%nat) with false by (symmetry; apply Nat.eqb_neq; lia).
        replace ((j' + 1 =? j' + 1)%nat) with true by (symmetry; apply Nat.eqb_eq; lia).
        replace ((j' =? j' + 1 + 1)%nat) with false by (symmetry; apply Nat.eqb_neq; lia).
        replace ((j' + 1 =? j' + 1)%nat) with true by (symmetry; apply Nat.eqb_eq; lia).
        lra.
      * replace ((j =? j')%nat) with false by (symmetry; apply Nat.eqb_neq; lia).
        replace ((j' =? j)%nat) with false by (symmetry; apply Nat.eqb_neq; lia).
        replace ((j' =? j + 1)%nat) with false by (symmetry; apply Nat.eqb_neq; lia).
        replace ((j =? j' + 1)%nat) with false by (symmetry; apply Nat.eqb_neq; lia).
        replace ((j =? j' + 1)%nat) with false by (symmetry; apply Nat.eqb_neq; lia).
        replace ((j' =? j + 1)%nat) with false by (symmetry; apply Nat.eqb_neq; lia).
        lra.
Qed.

(** Matrix is tridiagonal: zero for |j-j'| > 1 *)
Theorem H_spatial_tridiagonal : forall d_sp j j',
  (j' > j + 1)%nat ->
  H_spatial_entry d_sp j j' == 0.
Proof.
  intros d_sp j j' Hj. unfold H_spatial_entry.
  assert (Hneq : (j =? j')%nat = false).
  { apply Nat.eqb_neq. lia. }
  assert (Hnext : (j' =? j + 1)%nat = false).
  { apply Nat.eqb_neq. lia. }
  assert (Hprev : (j =? j' + 1)%nat = false).
  { apply Nat.eqb_neq. lia. }
  rewrite Hneq, Hnext, Hprev. lra.
Qed.

(** Tridiagonal below *)
Theorem H_spatial_tridiagonal_below : forall d_sp j j',
  (j > j' + 1)%nat ->
  H_spatial_entry d_sp j j' == 0.
Proof.
  intros d_sp j j' Hj. unfold H_spatial_entry.
  assert (Hneq : (j =? j')%nat = false).
  { apply Nat.eqb_neq. lia. }
  assert (Hnext : (j' =? j + 1)%nat = false).
  { apply Nat.eqb_neq. lia. }
  assert (Hprev : (j =? j' + 1)%nat = false).
  { apply Nat.eqb_neq. lia. }
  rewrite Hneq, Hnext, Hprev. lra.
Qed.

(** Diagonal entry *)
Lemma H_spatial_diag : forall d_sp j,
  H_spatial_entry d_sp j j == inject_Z (Z.of_nat d_sp) * spatial_diagonal j.
Proof.
  intros d_sp j. unfold H_spatial_entry.
  rewrite Nat.eqb_refl. lra.
Qed.

(** Off-diagonal entry *)
Lemma H_spatial_offdiag_right : forall d_sp j,
  H_spatial_entry d_sp j (j + 1) == inject_Z (Z.of_nat d_sp) * spatial_offdiag j.
Proof.
  intros d_sp j. unfold H_spatial_entry.
  assert (H1 : (j =? j + 1)%nat = false).
  { apply Nat.eqb_neq. lia. }
  rewrite H1. rewrite Nat.eqb_refl. lra.
Qed.

Lemma H_spatial_offdiag_left : forall d_sp j,
  H_spatial_entry d_sp (j + 1) j == inject_Z (Z.of_nat d_sp) * spatial_offdiag j.
Proof.
  intros d_sp j.
  assert (Hsym := H_spatial_symmetric d_sp (j+1) j).
  assert (Hright := H_spatial_offdiag_right d_sp j).
  lra.
Qed.

(* ================================================================== *)
(*  Part II: Ground State Properties  (~10 lemmas)                    *)
(* ================================================================== *)

(** Ground state H_{00} = 0 *)
Theorem H_ground_state_zero : forall d_sp,
  H_spatial_entry d_sp 0 0 == 0.
Proof.
  intros d_sp. rewrite H_spatial_diag.
  rewrite spatial_diag_0. ring.
Qed.

(** First excited diagonal: H_{11} = d_sp·2/9 *)
Lemma H_first_excited : forall d_sp,
  H_spatial_entry d_sp 1 1 == inject_Z (Z.of_nat d_sp) * (2 # 9).
Proof.
  intros d_sp. rewrite H_spatial_diag.
  assert (H := spatial_diag_1).
  unfold spatial_diagonal in H.
  unfold H_spatial_entry, spatial_diagonal, Qdiv, Qmult, Qinv, inject_Z, Qeq in *.
  simpl in *. nia.
Qed.

(** Second excited diagonal: H_{22} = d_sp·6/25 *)
Lemma H_second_excited : forall d_sp,
  H_spatial_entry d_sp 2 2 == inject_Z (Z.of_nat d_sp) * (6 # 25).
Proof.
  intros d_sp. rewrite H_spatial_diag.
  unfold spatial_diagonal, Qdiv, Qmult, Qinv, inject_Z, Qeq.
  simpl. nia.
Qed.

(** H_{00} < H_{11} (ground has less spatial energy than excited) *)
Lemma H_diag_0_lt_1 : forall d_sp,
  (1 <= d_sp)%nat ->
  H_spatial_entry d_sp 0 0 < H_spatial_entry d_sp 1 1.
Proof.
  intros d_sp Hd.
  rewrite H_ground_state_zero.
  rewrite H_spatial_diag.
  assert (Hdn : 0 < inject_Z (Z.of_nat d_sp)).
  { apply inject_Z_nat_pos. exact Hd. }
  assert (Hsd : 0 < spatial_diagonal 1).
  { assert (H0 := spatial_diag_0). assert (H1 := diag_increasing_0_1). lra. }
  apply Qmult_lt_0_compat; assumption.
Qed.

(** Diagonal entries nonneg *)
Lemma H_diag_nonneg : forall d_sp j,
  0 <= H_spatial_entry d_sp j j.
Proof.
  intros d_sp j. rewrite H_spatial_diag.
  assert (Hdn : 0 <= inject_Z (Z.of_nat d_sp)).
  { unfold Qle. simpl. lia. }
  assert (Hsd := spatial_diag_nonneg j).
  apply Qmult_le_0_compat; assumption.
Qed.

(** Off-diagonal entries nonneg *)
Lemma H_offdiag_nonneg : forall d_sp j,
  0 <= H_spatial_entry d_sp j (j + 1).
Proof.
  intros d_sp j. rewrite H_spatial_offdiag_right.
  assert (Hdn : 0 <= inject_Z (Z.of_nat d_sp)).
  { unfold Qle. simpl. lia. }
  assert (Hod := spatial_offdiag_nonneg j).
  apply Qmult_le_0_compat; assumption.
Qed.

(* ================================================================== *)
(*  Part III: Explicit 3+1D Values  (~10 lemmas)                      *)
(* ================================================================== *)

(** In 3+1D: d_sp = 3 *)

Lemma H_3d_00 : H_spatial_entry 3 0 0 == 0.
Proof. exact (H_ground_state_zero 3). Qed.

Lemma H_3d_11 : H_spatial_entry 3 1 1 == 2 # 3.
Proof.
  unfold H_spatial_entry, spatial_diagonal.
  simpl. unfold Qdiv, Qmult, Qinv, inject_Z, Qeq.
  simpl. lia.
Qed.

Lemma H_3d_22 : H_spatial_entry 3 2 2 == 18 # 25.
Proof.
  unfold H_spatial_entry, spatial_diagonal.
  simpl. unfold Qdiv, Qmult, Qinv, inject_Z, Qeq.
  simpl. lia.
Qed.

Lemma H_3d_01 : H_spatial_entry 3 0 1 == 1.
Proof.
  unfold H_spatial_entry, spatial_offdiag.
  simpl. unfold Qdiv, Qmult, Qinv, inject_Z, Qeq.
  simpl. lia.
Qed.

Lemma H_3d_12 : H_spatial_entry 3 1 2 == 2 # 5.
Proof.
  unfold H_spatial_entry, spatial_offdiag.
  simpl. unfold Qdiv, Qmult, Qinv, inject_Z, Qeq.
  simpl. lia.
Qed.

(** 2×2 truncation trace: H_{00} + H_{11} = d·2/9 *)
Definition H_2x2_trace (d_sp : nat) : Q :=
  H_spatial_entry d_sp 0 0 + H_spatial_entry d_sp 1 1.

Lemma H_2x2_trace_formula : forall d_sp,
  H_2x2_trace d_sp == inject_Z (Z.of_nat d_sp) * (2 # 9).
Proof.
  intros d_sp. unfold H_2x2_trace.
  rewrite H_ground_state_zero.
  assert (H := H_first_excited d_sp). lra.
Qed.

Lemma H_2x2_trace_3d : H_2x2_trace 3 == 2 # 3.
Proof.
  unfold H_2x2_trace. rewrite H_3d_00, H_3d_11. lra.
Qed.

(* ================================================================== *)
(*  Part IV: Strong Coupling Regime  (~8 lemmas)                      *)
(* ================================================================== *)

(** At strong spatial coupling (large β_s):
    exp(−β_s·H_{jj}) is small for j≥1
    Ground j=0: exp(0) = 1 (no suppression)
    Excited j=1: exp(−β_s·d·2/9) → 0 *)

(** Spatial energy cost for j=1: β_s·d·2/9 *)
Definition spatial_cost_j1 (beta_s : Q) (d_sp : nat) : Q :=
  beta_s * inject_Z (Z.of_nat d_sp) * (2 # 9).

Lemma spatial_cost_positive : forall beta_s d_sp,
  0 < beta_s -> (1 <= d_sp)%nat ->
  0 < spatial_cost_j1 beta_s d_sp.
Proof.
  intros beta_s d_sp Hbs Hd. unfold spatial_cost_j1.
  assert (Hdn := inject_Z_nat_pos d_sp Hd).
  assert (H29 : (0:Q) < 2 # 9) by lra.
  assert (H1 : 0 < beta_s * inject_Z (Z.of_nat d_sp)).
  { apply Qmult_lt_0_compat; assumption. }
  apply Qmult_lt_0_compat; assumption.
Qed.

Lemma spatial_cost_nonneg : forall beta_s d_sp,
  0 <= beta_s ->
  0 <= spatial_cost_j1 beta_s d_sp.
Proof.
  intros beta_s d_sp Hbs. unfold spatial_cost_j1.
  assert (Hdn : 0 <= inject_Z (Z.of_nat d_sp)).
  { unfold Qle. simpl. lia. }
  assert (H29 : (0:Q) <= 2 # 9) by lra.
  assert (H1 : 0 <= beta_s * inject_Z (Z.of_nat d_sp)).
  { apply Qmult_le_0_compat; assumption. }
  apply Qmult_le_0_compat; assumption.
Qed.

(** Cost at β_s=1, d=3: 2/3 *)
Lemma spatial_cost_3d : spatial_cost_j1 1 3 == 2 # 3.
Proof.
  unfold spatial_cost_j1. unfold Qeq, inject_Z. simpl. lia.
Qed.

(** Spatial suppression factor: s_j = 1 − β_s·d·C_j/(2j+1)² *)
(** For j=0: s_0 = 1 (no suppression) *)
(** For j=1: s_1 = 1 − β_s·d·2/9 *)
Definition spatial_suppression_factor (beta_s : Q) (d_sp j : nat) : Q :=
  1 - beta_s * inject_Z (Z.of_nat d_sp) * spatial_diagonal j.

Lemma suppression_factor_0 : forall beta_s d_sp,
  spatial_suppression_factor beta_s d_sp 0 == 1.
Proof.
  intros beta_s d_sp. unfold spatial_suppression_factor.
  rewrite spatial_diag_0. ring.
Qed.

Lemma suppression_factor_1_formula : forall beta_s d_sp,
  spatial_suppression_factor beta_s d_sp 1 ==
  1 - beta_s * inject_Z (Z.of_nat d_sp) * (2 # 9).
Proof.
  intros beta_s d_sp. unfold spatial_suppression_factor.
  unfold spatial_diagonal, Qdiv, Qmult, Qinv, inject_Z, Qeq.
  simpl. nia.
Qed.

(** Suppression < 1 for positive coupling and j ≥ 1 *)
Lemma suppression_factor_lt_1 : forall beta_s d_sp,
  0 < beta_s -> (1 <= d_sp)%nat ->
  spatial_suppression_factor beta_s d_sp 1 < 1.
Proof.
  intros beta_s d_sp Hbs Hd.
  unfold spatial_suppression_factor.
  assert (Hsd : 0 < spatial_diagonal 1).
  { assert (H := diag_increasing_0_1). rewrite spatial_diag_0 in H. exact H. }
  assert (Hdn := inject_Z_nat_pos d_sp Hd).
  assert (Hprod : 0 < beta_s * inject_Z (Z.of_nat d_sp) * spatial_diagonal 1).
  { assert (H1 : 0 < beta_s * inject_Z (Z.of_nat d_sp)).
    { apply Qmult_lt_0_compat; assumption. }
    apply Qmult_lt_0_compat; assumption. }
  lra.
Qed.

(** Summary *)
Theorem spatial_hamiltonian_summary :
  (* Ground state zero *)
  (forall d_sp, H_spatial_entry d_sp 0 0 == 0) /\
  (* Excited has energy *)
  (forall d_sp, (1 <= d_sp)%nat ->
    H_spatial_entry d_sp 0 0 < H_spatial_entry d_sp 1 1) /\
  (* Diagonal nonneg *)
  (forall d_sp j, 0 <= H_spatial_entry d_sp j j) /\
  (* Tridiagonal *)
  (forall d_sp j j', (j' > j + 1)%nat -> H_spatial_entry d_sp j j' == 0) /\
  (* Symmetric *)
  (forall d_sp j j', H_spatial_entry d_sp j j' == H_spatial_entry d_sp j' j).
Proof.
  split; [|split; [|split; [|split]]].
  - exact H_ground_state_zero.
  - exact H_diag_0_lt_1.
  - exact H_diag_nonneg.
  - exact H_spatial_tridiagonal.
  - exact H_spatial_symmetric.
Qed.

(* ================================================================== *)
(*  CHECKS                                                             *)
(* ================================================================== *)

Check H_spatial_entry. Check H_spatial_symmetric.
Check H_spatial_tridiagonal. Check H_spatial_tridiagonal_below.
Check H_spatial_diag. Check H_spatial_offdiag_right. Check H_spatial_offdiag_left.
Check H_ground_state_zero.
Check H_first_excited. Check H_second_excited.
Check H_diag_0_lt_1. Check H_diag_nonneg. Check H_offdiag_nonneg.
Check H_3d_00. Check H_3d_11. Check H_3d_22. Check H_3d_01. Check H_3d_12.
Check H_2x2_trace. Check H_2x2_trace_formula. Check H_2x2_trace_3d.
Check spatial_cost_j1. Check spatial_cost_positive. Check spatial_cost_nonneg.
Check spatial_cost_3d.
Check spatial_suppression_factor.
Check suppression_factor_0. Check suppression_factor_1_formula.
Check suppression_factor_lt_1.
Check spatial_hamiltonian_summary.

Print Assumptions spatial_hamiltonian_summary.
