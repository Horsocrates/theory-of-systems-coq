(** * ClebschGordan.v — Selection Rules and Coupling Coefficients
    Elements: CG selection rules, coupling coefficients, spatial energy
    Roles:    encodes SU(2) tensor product decomposition for gauge plaquettes
    Rules:    χ_j·χ_1 = χ_{j-1}+χ_j+χ_{j+1}, tridiagonal selection
    Status:   complete
    STATUS: ~40 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        CLEBSCH-GORDAN — Selection Rules and Coupling Coefficients          *)
(*                                                                           *)
(*  SU(2) tensor product: j ⊗ 1 = (j-1) ⊕ j ⊕ (j+1) for j ≥ 1          *)
(*  In characters: χ_j·χ_1 = χ_{j-1} + χ_j + χ_{j+1}                     *)
(*  Selection rule: coupling j ↔ j' only if |j-j'| ≤ 1                    *)
(*  → spatial Hamiltonian is TRIDIAGONAL                                    *)
(*                                                                           *)
(*  Coupling coefficients from Casimir:                                     *)
(*    Diagonal: j(j+1)/(2j+1)²                                             *)
(*    Off-diagonal: (j+1)/((2j+1)(2j+3))                                   *)
(*                                                                           *)
(*  STATUS: ~40 Qed, 0 Admitted                                             *)
(*  AXIOMS: none                                                             *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import CauchyReal.
From ToS Require Import SeriesConvergence.
From ToS Require Import gauge.SU2Characters.

(* ================================================================== *)
(*  Part I: Character Product Identities  (~12 lemmas)                *)
(* ================================================================== *)

(** Character product: χ_0·χ_1 = χ_1 (trivial rep ⊗ adjoint) *)
Theorem character_product_0_1 : forall c,
  su2_character 0 c * su2_character 1 c == su2_character 1 c.
Proof. intros c. unfold su2_character. simpl. ring. Qed.

(** Character product: χ_1·χ_1 = χ_0 + χ_1 + χ_2 *)
(** Verifies: (4c²-1)² = 1 + (4c²-1) + (16c⁴-12c²+1) *)
Theorem character_product_1_1 : forall c,
  su2_character 1 c * su2_character 1 c ==
  su2_character 0 c + su2_character 1 c + su2_character 2 c.
Proof. intros c. unfold su2_character. simpl. ring. Qed.

(** Character product: χ_2·χ_1 = χ_1 + χ_2 + χ_3 *)
Theorem character_product_2_1 : forall c,
  su2_character 2 c * su2_character 1 c ==
  su2_character 1 c + su2_character 2 c + su2_character 3 c.
Proof. intros c. unfold su2_character. simpl. ring. Qed.

(** Dimension check: (2j+1)·3 = (2(j-1)+1) + (2j+1) + (2(j+1)+1) *)
Lemma dimension_check : forall j,
  (1 <= j)%nat ->
  ((2*j+1) * 3 = (2*(j-1)+1) + (2*j+1) + (2*(j+1)+1))%nat.
Proof. intros j Hj. lia. Qed.

(** Dimension at c=1: χ_j(1)=2j+1, product dimensions match *)
Lemma product_dimension_0 :
  su2_character 0 1 * su2_character 1 1 == 1 * 3.
Proof. unfold su2_character. simpl. lra. Qed.

Lemma product_dimension_1 :
  su2_character 1 1 * su2_character 1 1 == 3 * 3.
Proof. unfold su2_character. simpl. lra. Qed.

Lemma product_decomp_dim_1 :
  su2_character 0 1 + su2_character 1 1 + su2_character 2 1 == 9.
Proof. unfold su2_character. simpl. lra. Qed.

Lemma product_dimension_2 :
  su2_character 2 1 * su2_character 1 1 == 5 * 3.
Proof. unfold su2_character. simpl. lra. Qed.

(** Selection rule: j ⊗ 1 couples only to j-1, j, j+1 *)
Definition coupling_allowed (j j' : nat) : Prop :=
  (j' = j \/ j' = j + 1 \/ j = j' + 1)%nat.

Lemma coupling_allowed_self : forall j, coupling_allowed j j.
Proof. intros j. left. reflexivity. Qed.

Lemma coupling_allowed_next : forall j, coupling_allowed j (j + 1).
Proof. intros j. right. left. reflexivity. Qed.

Lemma coupling_allowed_prev : forall j, (1 <= j)%nat -> coupling_allowed j (j - 1).
Proof. intros j Hj. right. right. lia. Qed.

(* ================================================================== *)
(*  Part II: Coupling Coefficients  (~12 lemmas)                      *)
(* ================================================================== *)

(** Diagonal coupling: Casimir j(j+1)/(2j+1)² *)
Definition spatial_diagonal (j : nat) : Q :=
  inject_Z (Z.of_nat (j * (j + 1)))
  / inject_Z (Z.of_nat ((2 * j + 1) * (2 * j + 1))).

Lemma spatial_diag_0 : spatial_diagonal 0 == 0.
Proof.
  unfold spatial_diagonal. unfold Qdiv, Qmult, Qinv, inject_Z, Qeq.
  simpl. lia.
Qed.

Lemma spatial_diag_1 : spatial_diagonal 1 == 2 # 9.
Proof.
  unfold spatial_diagonal. unfold Qdiv, Qmult, Qinv, inject_Z, Qeq.
  simpl. lia.
Qed.

Lemma spatial_diag_2 : spatial_diagonal 2 == 6 # 25.
Proof.
  unfold spatial_diagonal. unfold Qdiv, Qmult, Qinv, inject_Z, Qeq.
  simpl. lia.
Qed.

Lemma spatial_diag_3 : spatial_diagonal 3 == 12 # 49.
Proof.
  unfold spatial_diagonal. unfold Qdiv, Qmult, Qinv, inject_Z, Qeq.
  simpl. lia.
Qed.

(** Diagonal is nonneg *)
Lemma spatial_diag_nonneg : forall j, 0 <= spatial_diagonal j.
Proof.
  intros j. unfold spatial_diagonal.
  apply Qle_shift_div_l.
  - unfold Qlt. simpl. lia.
  - unfold Qle. simpl. lia.
Qed.

(** Off-diagonal coupling: (j+1)/((2j+1)(2j+3)) *)
Definition spatial_offdiag (j : nat) : Q :=
  inject_Z (Z.of_nat (j + 1))
  / inject_Z (Z.of_nat ((2 * j + 1) * (2 * j + 3))).

Lemma spatial_offdiag_0 : spatial_offdiag 0 == 1 # 3.
Proof.
  unfold spatial_offdiag. unfold Qdiv, Qmult, Qinv, inject_Z, Qeq.
  simpl. lia.
Qed.

Lemma spatial_offdiag_1 : spatial_offdiag 1 == 2 # 15.
Proof.
  unfold spatial_offdiag. unfold Qdiv, Qmult, Qinv, inject_Z, Qeq.
  simpl. lia.
Qed.

Lemma spatial_offdiag_2 : spatial_offdiag 2 == 3 # 35.
Proof.
  unfold spatial_offdiag. unfold Qdiv, Qmult, Qinv, inject_Z, Qeq.
  simpl. lia.
Qed.

(** Off-diagonal is nonneg *)
Lemma spatial_offdiag_nonneg : forall j, 0 <= spatial_offdiag j.
Proof.
  intros j. unfold spatial_offdiag.
  apply Qle_shift_div_l.
  - unfold Qlt. simpl. lia.
  - unfold Qle. simpl. lia.
Qed.

(** Diagonal increasing: d(j) < d(j+1) for j ≥ 0 *)
Lemma diag_increasing_0_1 : spatial_diagonal 0 < spatial_diagonal 1.
Proof.
  rewrite spatial_diag_0. rewrite spatial_diag_1. lra.
Qed.

Lemma diag_increasing_1_2 : spatial_diagonal 1 < spatial_diagonal 2.
Proof.
  unfold spatial_diagonal. unfold Qlt, Qdiv, Qmult, Qinv, inject_Z. simpl. lia.
Qed.

Lemma diag_increasing_2_3 : spatial_diagonal 2 < spatial_diagonal 3.
Proof.
  unfold spatial_diagonal. unfold Qlt, Qdiv, Qmult, Qinv, inject_Z. simpl. lia.
Qed.

(** Off-diagonal decreasing: o(j+1) < o(j) *)
Lemma offdiag_decreasing_0_1 : spatial_offdiag 1 < spatial_offdiag 0.
Proof.
  unfold spatial_offdiag. unfold Qlt, Qdiv, Qmult, Qinv, inject_Z. simpl. lia.
Qed.

Lemma offdiag_decreasing_1_2 : spatial_offdiag 2 < spatial_offdiag 1.
Proof.
  unfold spatial_offdiag. unfold Qlt, Qdiv, Qmult, Qinv, inject_Z. simpl. lia.
Qed.

(* ================================================================== *)
(*  Part III: Spatial Energy  (~8 lemmas)                             *)
(* ================================================================== *)

(** Spatial plaquette energy for state |j⟩ *)
Definition spatial_energy (beta_s : Q) (d_sp : nat) (j : nat) : Q :=
  beta_s * inject_Z (Z.of_nat d_sp) * spatial_diagonal j.

(** Ground state j=0: no Casimir energy *)
Lemma spatial_energy_ground : forall beta_s d_sp,
  spatial_energy beta_s d_sp 0 == 0.
Proof.
  intros beta_s d_sp. unfold spatial_energy.
  rewrite spatial_diag_0. ring.
Qed.

(** Spatial gap contribution: E(1) - E(0) = β_s·d_sp·2/9 *)
Definition spatial_gap_contribution (beta_s : Q) (d_sp : nat) : Q :=
  beta_s * inject_Z (Z.of_nat d_sp) * spatial_diagonal 1.

Lemma spatial_gap_equals_energy_1 : forall beta_s d_sp,
  spatial_gap_contribution beta_s d_sp ==
  spatial_energy beta_s d_sp 1 - spatial_energy beta_s d_sp 0.
Proof.
  intros beta_s d_sp. unfold spatial_gap_contribution, spatial_energy.
  rewrite spatial_diag_0. ring.
Qed.

Lemma spatial_gap_formula : forall beta_s d_sp,
  spatial_gap_contribution beta_s d_sp ==
  beta_s * inject_Z (Z.of_nat d_sp) * (2 # 9).
Proof.
  intros beta_s d_sp. unfold spatial_gap_contribution.
  assert (H := spatial_diag_1).
  unfold spatial_diagonal in H.
  unfold spatial_gap_contribution. unfold spatial_diagonal.
  unfold Qdiv, Qmult, Qinv, inject_Z, Qeq in *.
  simpl in *. nia.
Qed.

(** Helper: inject_Z of positive nat is positive *)
Lemma inject_Z_nat_pos : forall n,
  (1 <= n)%nat -> 0 < inject_Z (Z.of_nat n).
Proof.
  intros n Hn. unfold Qlt. simpl. lia.
Qed.

(** Spatial gap positive when β_s > 0 and d_sp ≥ 1 *)
Theorem spatial_gap_positive : forall beta_s d_sp,
  0 < beta_s -> (1 <= d_sp)%nat ->
  0 < spatial_gap_contribution beta_s d_sp.
Proof.
  intros beta_s d_sp Hbs Hd.
  assert (Hf := spatial_gap_formula beta_s d_sp).
  assert (H29 : (0:Q) < 2 # 9) by lra.
  assert (Hdn := inject_Z_nat_pos d_sp Hd).
  (* spatial_gap = beta_s * d_sp * (2/9) > 0 *)
  assert (H1 : 0 < beta_s * inject_Z (Z.of_nat d_sp)).
  { apply Qmult_lt_0_compat; assumption. }
  assert (H2 : 0 < beta_s * inject_Z (Z.of_nat d_sp) * (2 # 9)).
  { apply Qmult_lt_0_compat; assumption. }
  lra.
Qed.

Lemma spatial_gap_nonneg : forall beta_s d_sp,
  0 <= beta_s -> (1 <= d_sp)%nat ->
  0 <= spatial_gap_contribution beta_s d_sp.
Proof.
  intros beta_s d_sp Hbs Hd.
  assert (Hf := spatial_gap_formula beta_s d_sp).
  assert (H29 : (0:Q) <= 2 # 9) by lra.
  assert (Hdn : 0 <= inject_Z (Z.of_nat d_sp)).
  { unfold Qle. simpl. lia. }
  assert (H1 : 0 <= beta_s * inject_Z (Z.of_nat d_sp)).
  { apply Qmult_le_0_compat; assumption. }
  assert (H2 : 0 <= beta_s * inject_Z (Z.of_nat d_sp) * (2 # 9)).
  { apply Qmult_le_0_compat; assumption. }
  lra.
Qed.

(* ================================================================== *)
(*  Part IV: Plaquette Count  (~6 lemmas)                             *)
(* ================================================================== *)

(** Number of spatial plaquettes in (d+1)D with minimal lattice *)
(** d_sp = number of spatial dimensions *)
(** 2+1D (d_sp=2): 1 plaquette, 3+1D (d_sp=3): 3 plaquettes *)
Definition spatial_plaquette_count (d_sp : nat) : nat :=
  (d_sp * (d_sp - 1) / 2)%nat.

Lemma plaquettes_1d : spatial_plaquette_count 1 = 0%nat.
Proof. unfold spatial_plaquette_count. simpl. reflexivity. Qed.

Lemma plaquettes_2plus1 : spatial_plaquette_count 2 = 1%nat.
Proof. unfold spatial_plaquette_count. simpl. reflexivity. Qed.

Lemma plaquettes_3plus1 : spatial_plaquette_count 3 = 3%nat.
Proof. unfold spatial_plaquette_count. simpl. reflexivity. Qed.

Lemma plaquettes_4plus1 : spatial_plaquette_count 4 = 6%nat.
Proof. unfold spatial_plaquette_count. simpl. reflexivity. Qed.

(** Plaquette count grows *)
Lemma plaquettes_increasing_2_3 :
  (spatial_plaquette_count 2 <= spatial_plaquette_count 3)%nat.
Proof. unfold spatial_plaquette_count. simpl. lia. Qed.

Lemma plaquettes_increasing_3_4 :
  (spatial_plaquette_count 3 <= spatial_plaquette_count 4)%nat.
Proof. unfold spatial_plaquette_count. simpl. lia. Qed.

(* ================================================================== *)
(*  CHECKS                                                             *)
(* ================================================================== *)

Check character_product_0_1. Check character_product_1_1.
Check character_product_2_1.
Check dimension_check.
Check product_dimension_0. Check product_dimension_1.
Check product_decomp_dim_1. Check product_dimension_2.
Check coupling_allowed. Check coupling_allowed_self.
Check coupling_allowed_next. Check coupling_allowed_prev.
Check spatial_diagonal. Check spatial_diag_0.
Check spatial_diag_1. Check spatial_diag_2. Check spatial_diag_3.
Check spatial_diag_nonneg.
Check spatial_offdiag. Check spatial_offdiag_0.
Check spatial_offdiag_1. Check spatial_offdiag_2. Check spatial_offdiag_nonneg.
Check diag_increasing_0_1. Check diag_increasing_1_2. Check diag_increasing_2_3.
Check offdiag_decreasing_0_1. Check offdiag_decreasing_1_2.
Check spatial_energy. Check spatial_energy_ground.
Check spatial_gap_contribution. Check spatial_gap_equals_energy_1.
Check spatial_gap_formula.
Check inject_Z_nat_pos. Check spatial_gap_positive. Check spatial_gap_nonneg.
Check spatial_plaquette_count.
Check plaquettes_1d. Check plaquettes_2plus1.
Check plaquettes_3plus1. Check plaquettes_4plus1.
Check plaquettes_increasing_2_3. Check plaquettes_increasing_3_4.

Print Assumptions spatial_gap_positive.
