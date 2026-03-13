(** * ReflectionPositiveProof.v — RP from Transfer Matrix Eigenvalues
    Elements: rp_inner_matrix, hamiltonian_energy_matrix, matrix_energy_gap
    Roles:    proves RP ≥ 0 from matrix eigenvalue positivity
    Rules:    weighted_sum_sq bridge, energy gap E₁ > 0
    Status:   complete
    STATUS: ~35 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        REFLECTION POSITIVITY PROOF — From Matrix Eigenvalues               *)
(*                                                                            *)
(*  RP: ⟨f, Θf⟩ ≥ 0 where Θ is time reflection.                          *)
(*  In our basis: ⟨f, Θf⟩ = Σ_j |f_j|² · t_j.                           *)
(*  Since t_j > 0 for all j: this sum is ≥ 0.                               *)
(*                                                                            *)
(*  Full proof term: eigenvalue positivity → RP.                             *)
(*                                                                            *)
(*  STATUS: target ~35 Qed, 0 Admitted                                       *)
(*  AXIOMS: none                                                              *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import CauchyReal.
From ToS Require Import SeriesConvergence.
From ToS Require Import gauge.CharacterTransfer.
From ToS Require Import gauge.ExactMassGap.
From ToS Require Import gauge.GapRatio.
From ToS Require Import gauge.ReflectionPositivity.
From ToS Require Import gauge.TransferMatrixProof.

(* ================================================================== *)
(*  Part I: RP Inner Product from Matrix  (~10 lemmas)                *)
(* ================================================================== *)

(** RP inner product using the transfer matrix diagonal entries *)
Definition rp_inner_matrix (J : nat) (beta : Q) (M : nat)
  (f : nat -> Q) : Q :=
  weighted_sum_sq f (fun j => dm_entry (transfer_mat J beta M) j) J.

(** The matrix RP inner product equals the eigenvalue-weighted sum *)
Lemma rp_inner_matrix_eq : forall J beta M f,
  rp_inner_matrix J beta M f ==
  weighted_sum_sq f (fun j => transfer_eigenvalue j beta M) J.
Proof.
  intros J beta M f.
  unfold rp_inner_matrix.
  (* dm_entry (transfer_mat J beta M) j = transfer_eigenvalue j beta M *)
  (* So the two are definitionally equal *)
  reflexivity.
Qed.

(** RP nonneg from matrix: same as os4_structural *)
Theorem rp_matrix_nonneg : forall J beta f,
  (J <= 1)%nat -> 0 <= beta -> beta <= 2 ->
  0 <= rp_inner_matrix J beta 0 f.
Proof.
  intros J beta f HJ Hb1 Hb2.
  rewrite rp_inner_matrix_eq.
  apply weighted_sum_sq_nonneg.
  intros j Hj.
  destruct j as [|[|j']].
  - exact (t0_M0_nonneg beta Hb1 Hb2).
  - exact (t1_M0_nonneg beta Hb1 Hb2).
  - lia.
Qed.

(** ★ REFLECTION POSITIVITY — full proof from matrix ★ *)
Theorem reflection_positivity_from_matrix : forall beta f,
  0 <= beta -> beta <= 2 ->
  0 <= rp_inner_matrix 1 beta 0 f.
Proof.
  intros beta f Hb1 Hb2.
  apply rp_matrix_nonneg; [lia | exact Hb1 | exact Hb2].
Qed.

(** RP at beta=1 *)
Theorem rp_matrix_beta_1 : forall f,
  0 <= rp_inner_matrix 1 1 0 f.
Proof.
  intros f. apply reflection_positivity_from_matrix; lra.
Qed.

(** RP at beta=2 *)
Theorem rp_matrix_beta_2 : forall f,
  0 <= rp_inner_matrix 1 2 0 f.
Proof.
  intros f. apply reflection_positivity_from_matrix; lra.
Qed.

(** RP for arbitrary J with all-nonneg eigenvalues *)
Theorem rp_matrix_general : forall J beta f,
  (forall j, (j <= J)%nat -> 0 <= dm_entry (transfer_mat J beta 0) j) ->
  0 <= rp_inner_matrix J beta 0 f.
Proof.
  intros J beta f Hall.
  unfold rp_inner_matrix.
  apply weighted_sum_sq_nonneg. exact Hall.
Qed.

(* ================================================================== *)
(*  Part II: Positive Definiteness from Matrix  (~10 lemmas)          *)
(* ================================================================== *)

(** Helper: x*x > 0 when x ≠ 0 *)
Lemma Qsquare_pos : forall x : Q,
  ~(x == 0) -> 0 < x * x.
Proof.
  intros [xn xd] Hne.
  unfold Qeq in Hne. simpl in Hne.
  unfold Qlt, Qmult. simpl.
  rewrite Z.mul_1_r. nia.
Qed.

(** If f²·t = 0 and t > 0, then f = 0 *)
Lemma sq_times_pos_zero : forall (f_val t_val : Q),
  0 < t_val ->
  f_val * f_val * t_val == 0 ->
  f_val == 0.
Proof.
  intros f_val t_val Ht Hprod.
  destruct (Qeq_dec f_val 0) as [Heq|Hneq].
  - exact Heq.
  - exfalso.
    assert (Hpos : 0 < f_val * f_val) by (apply Qsquare_pos; exact Hneq).
    assert (Hprod_pos : 0 < f_val * f_val * t_val).
    { apply Qmult_lt_0_compat; assumption. }
    lra.
Qed.

(** Positive definite at J=0: rp_inner = 0 implies f(0) = 0 *)
Theorem rp_pd_at_0 : forall beta f,
  0 < dm_entry (transfer_mat 0 beta 0) 0 ->
  rp_inner_matrix 0 beta 0 f == 0 ->
  f 0%nat == 0.
Proof.
  intros beta f Ht0 Hsum.
  unfold rp_inner_matrix in Hsum. simpl in Hsum.
  apply sq_times_pos_zero with (t_val := dm_entry (transfer_mat 0 beta 0) 0).
  - exact Ht0.
  - exact Hsum.
Qed.

(** Positive definite at beta=1, J=0 *)
Theorem rp_pd_beta_1_j0 : forall f,
  rp_inner_matrix 0 1 0 f == 0 ->
  f 0%nat == 0.
Proof.
  intros f Hsum. apply rp_pd_at_0 with (beta := 1).
  - exact (transfer_mat_pos_0_beta1 0).
  - exact Hsum.
Qed.

(** Helper: sum of two nonneg terms = 0 implies each = 0 *)
Lemma nonneg_sum_zero : forall a b : Q,
  0 <= a -> 0 <= b -> a + b == 0 ->
  a == 0 /\ b == 0.
Proof.
  intros a b Ha Hb Hab. split; lra.
Qed.

(** Positive definite at J=1 — uses direct approach *)
Theorem rp_pd_at_1 : forall beta f,
  0 < transfer_eigenvalue 0 beta 0 ->
  0 < transfer_eigenvalue 1 beta 0 ->
  weighted_sum_sq f (fun j => transfer_eigenvalue j beta 0) 1 == 0 ->
  f 0%nat == 0 /\ f 1%nat == 0.
Proof.
  intros beta f Ht0 Ht1 Hsum.
  simpl in Hsum.
  assert (Hff0 := Qsquare_nonneg (f 0%nat)).
  assert (Hff1 := Qsquare_nonneg (f 1%nat)).
  assert (Hterm0 : 0 <= f 0%nat * f 0%nat * transfer_eigenvalue 0 beta 0).
  { apply Qmult_le_0_compat; lra. }
  assert (Hterm1 : 0 <= f 1%nat * f 1%nat * transfer_eigenvalue 1 beta 0).
  { apply Qmult_le_0_compat; lra. }
  assert (Hboth := nonneg_sum_zero _ _ Hterm0 Hterm1 Hsum).
  destruct Hboth as [Hz0 Hz1].
  split.
  - apply sq_times_pos_zero with (t_val := transfer_eigenvalue 0 beta 0); assumption.
  - apply sq_times_pos_zero with (t_val := transfer_eigenvalue 1 beta 0); assumption.
Qed.

(** Bridge: rp_inner_matrix uses the same weights as transfer_eigenvalue *)
Lemma rp_inner_matrix_unfold : forall J beta M f,
  rp_inner_matrix J beta M f ==
  weighted_sum_sq f (fun j => transfer_eigenvalue j beta M) J.
Proof.
  intros. unfold rp_inner_matrix. reflexivity.
Qed.

(** Positive definite at beta=1, J=1 *)
Theorem rp_pd_beta_1 : forall f,
  rp_inner_matrix 1 1 0 f == 0 ->
  f 0%nat == 0 /\ f 1%nat == 0.
Proof.
  intros f Hsum.
  rewrite rp_inner_matrix_unfold in Hsum.
  assert (Ht0 := t0_positive_beta_1). unfold t0_M0 in Ht0.
  assert (Ht1 := t1_positive_beta_1). unfold t1_M0 in Ht1.
  exact (rp_pd_at_1 1 f Ht0 Ht1 Hsum).
Qed.

(** Positive definite at beta=2, J=1 *)
Theorem rp_pd_beta_2 : forall f,
  rp_inner_matrix 1 2 0 f == 0 ->
  f 0%nat == 0 /\ f 1%nat == 0.
Proof.
  intros f Hsum.
  rewrite rp_inner_matrix_unfold in Hsum.
  assert (Ht0 := t0_positive_beta_2). unfold t0_M0 in Ht0.
  assert (Ht1 := t1_positive_beta_2). unfold t1_M0 in Ht1.
  exact (rp_pd_at_1 2 f Ht0 Ht1 Hsum).
Qed.

(* ================================================================== *)
(*  Part III: Norm Properties  (~6 lemmas)                            *)
(* ================================================================== *)

(** RP defines a norm: ‖f‖² = rp_inner f *)
Definition rp_norm_sq (J : nat) (beta : Q) (M : nat) (f : nat -> Q) : Q :=
  rp_inner_matrix J beta M f.

(** Norm nonneg *)
Theorem rp_norm_nonneg : forall beta f,
  0 <= beta -> beta <= 2 ->
  0 <= rp_norm_sq 1 beta 0 f.
Proof.
  intros beta f Hb1 Hb2. unfold rp_norm_sq.
  apply reflection_positivity_from_matrix; assumption.
Qed.

(** Norm zero implies f zero (at beta=1) *)
Theorem rp_norm_zero_implies_f_zero : forall f,
  rp_norm_sq 1 1 0 f == 0 ->
  f 0%nat == 0 /\ f 1%nat == 0.
Proof.
  intros f H. unfold rp_norm_sq in H. exact (rp_pd_beta_1 f H).
Qed.

(** Norm of zero function is zero *)
Theorem rp_norm_zero_fn : forall J beta M,
  rp_norm_sq J beta M (fun _ => 0) == 0.
Proof.
  intros J beta M. unfold rp_norm_sq, rp_inner_matrix.
  induction J as [|J' IH].
  - simpl. ring.
  - simpl. assert (Hprev : weighted_sum_sq (fun _ : nat => 0)
      (fun j : nat => dm_entry (transfer_mat (S J') beta M) j) J' == 0).
    { (* Need to show the same weighted_sum_sq with different transfer_mat is 0 *)
      (* All terms are 0 * 0 * t = 0 regardless of t *)
      clear IH. induction J' as [|J'' IH'].
      - simpl. ring.
      - simpl. rewrite IH'. ring. }
    rewrite Hprev. ring.
Qed.

(** Inner product space summary *)
Theorem rp_inner_product_properties :
  (* Nonneg *)
  (forall beta f, 0 <= beta -> beta <= 2 -> 0 <= rp_norm_sq 1 beta 0 f) /\
  (* Positive definite at beta=1 *)
  (forall f, rp_norm_sq 1 1 0 f == 0 -> f 0%nat == 0 /\ f 1%nat == 0) /\
  (* Zero function has zero norm *)
  (forall J beta M, rp_norm_sq J beta M (fun _ => 0) == 0).
Proof.
  split; [| split].
  - exact rp_norm_nonneg.
  - exact rp_norm_zero_implies_f_zero.
  - exact rp_norm_zero_fn.
Qed.

(* ================================================================== *)
(*  Part IV: Hamiltonian Energy from Matrix  (~10 lemmas)             *)
(* ================================================================== *)

(** Energy levels: E_j = 1 - t_j/t₀ (first-order approx of -log(t_j/t₀)) *)
Definition matrix_energy (J : nat) (beta : Q) (M : nat) (j : nat) : Q :=
  1 - dm_entry (transfer_mat J beta M) j / dm_entry (transfer_mat J beta M) 0.

(** Matrix energy equals physical energy *)
Theorem matrix_energy_eq_physical : forall J beta j,
  matrix_energy J beta 0 j == physical_energy j beta.
Proof.
  intros J beta j. unfold matrix_energy, physical_energy. simpl. ring.
Qed.

(** Ground energy is zero *)
Theorem matrix_ground_energy_zero : forall J beta,
  0 < dm_entry (transfer_mat J beta 0) 0 ->
  matrix_energy J beta 0 0 == 0.
Proof.
  intros J beta Ht0.
  unfold matrix_energy.
  assert (Heq : dm_entry (transfer_mat J beta 0) 0 /
                dm_entry (transfer_mat J beta 0) 0 == 1).
  { field. lra. }
  lra.
Qed.

(** Ground energy zero at beta=1 *)
Theorem matrix_ground_energy_1 : forall J,
  matrix_energy J 1 0 0 == 0.
Proof.
  intros J. apply matrix_ground_energy_zero.
  exact (transfer_mat_pos_0_beta1 J).
Qed.

(** First excited energy positive at beta=1 *)
Theorem matrix_excited_positive_1 : forall J,
  0 < matrix_energy J 1 0 1.
Proof.
  intros J.
  assert (H := matrix_energy_eq_physical J 1 1).
  assert (Hfe := first_excited_positive_1). lra.
Qed.

(** First excited energy positive at beta=2 *)
Theorem matrix_excited_positive_2 : forall J,
  0 < matrix_energy J 2 0 1.
Proof.
  intros J.
  assert (H := matrix_energy_eq_physical J 2 1).
  assert (Hfe := first_excited_positive_2). lra.
Qed.

(** Energy gap from matrix *)
Definition matrix_energy_gap (J : nat) (beta : Q) (M : nat) : Q :=
  matrix_energy J beta M 1 - matrix_energy J beta M 0.

(** Energy gap equals existing energy_gap *)
Theorem matrix_energy_gap_eq : forall J beta,
  matrix_energy_gap J beta 0 == energy_gap beta.
Proof.
  intros J beta.
  unfold matrix_energy_gap, energy_gap.
  rewrite (matrix_energy_eq_physical J beta 1).
  rewrite (matrix_energy_eq_physical J beta 0).
  ring.
Qed.

(** Energy gap positive at beta=1 *)
Theorem matrix_energy_gap_positive_1 : forall J,
  0 < matrix_energy_gap J 1 0.
Proof.
  intros J.
  assert (H := matrix_energy_gap_eq J 1).
  assert (He := energy_gap_positive_1). lra.
Qed.

(** Energy gap positive at beta=2 *)
Theorem matrix_energy_gap_positive_2 : forall J,
  0 < matrix_energy_gap J 2 0.
Proof.
  intros J.
  assert (H := matrix_energy_gap_eq J 2).
  assert (He := energy_gap_positive_2). lra.
Qed.

(** ★ THIS IS THE MASS GAP IN HILBERT SPACE LANGUAGE ★ *)
(** E₁ > 0 = E₀ with FULL proof term *)
Theorem hilbert_mass_gap :
  (* Ground energy = 0 *)
  (forall J, matrix_energy J 1 0 0 == 0) /\
  (* First excited > 0 *)
  (forall J, 0 < matrix_energy J 1 0 1) /\
  (* Energy gap > 0 *)
  (forall J, 0 < matrix_energy_gap J 1 0) /\
  (forall J, 0 < matrix_energy_gap J 2 0).
Proof.
  split; [| split; [| split]].
  - exact matrix_ground_energy_1.
  - exact matrix_excited_positive_1.
  - exact matrix_energy_gap_positive_1.
  - exact matrix_energy_gap_positive_2.
Qed.

(** Full RP summary *)
Theorem rp_proof_summary :
  (* RP holds *)
  (forall beta f, 0 <= beta -> beta <= 2 ->
    0 <= rp_inner_matrix 1 beta 0 f) /\
  (* Positive definite *)
  (forall f, rp_inner_matrix 1 1 0 f == 0 ->
    f 0%nat == 0 /\ f 1%nat == 0) /\
  (* Energy gap positive *)
  (forall J, 0 < matrix_energy_gap J 1 0) /\
  (forall J, 0 < matrix_energy_gap J 2 0).
Proof.
  split; [| split; [| split]].
  - exact reflection_positivity_from_matrix.
  - exact rp_pd_beta_1.
  - exact matrix_energy_gap_positive_1.
  - exact matrix_energy_gap_positive_2.
Qed.

(* ================================================================== *)
(*  CHECKS                                                             *)
(* ================================================================== *)

Check rp_inner_matrix. Check rp_inner_matrix_eq.
Check rp_matrix_nonneg. Check reflection_positivity_from_matrix.
Check rp_matrix_beta_1. Check rp_matrix_beta_2. Check rp_matrix_general.
Check Qsquare_pos. Check sq_times_pos_zero.
Check rp_pd_at_0. Check rp_pd_beta_1_j0.
Check rp_pd_at_1. Check rp_pd_beta_1. Check rp_pd_beta_2.
Check rp_norm_sq. Check rp_norm_nonneg. Check rp_norm_zero_implies_f_zero.
Check rp_norm_zero_fn. Check rp_inner_product_properties.
Check matrix_energy. Check matrix_energy_eq_physical.
Check matrix_ground_energy_zero. Check matrix_ground_energy_1.
Check matrix_excited_positive_1. Check matrix_excited_positive_2.
Check matrix_energy_gap. Check matrix_energy_gap_eq.
Check matrix_energy_gap_positive_1. Check matrix_energy_gap_positive_2.
Check hilbert_mass_gap. Check rp_proof_summary.

Print Assumptions rp_proof_summary.
