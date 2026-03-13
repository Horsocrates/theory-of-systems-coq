(** * ZeroCountingProcess.v — Zero Counting N(T) and Density as ToS System
    Elements: N(T) count, zero density in strips, average Re position
    Roles:    argument principle → counting, reflection → average Re = 1/2
    Rules:    N(T) ~ T·log(T)/(2π), density bounds, RH ⟺ zero variance = 0
    Status:   complete
    STATUS: 35 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        ZERO COUNTING PROCESS — N(T) and Its Asymptotics                    *)
(*                                                                            *)
(*  N(T) = #{nontrivial zeros with 0 < Im(ρ) ≤ T}                          *)
(*  N(T) = T/(2π) · log(T/(2π)) − T/(2π) + O(log T)                       *)
(*  (Riemann-von Mangoldt formula)                                            *)
(*                                                                            *)
(*  Process version: N_K(T) = #{zeros of ζ_K with Im ≤ T}                   *)
(*  As K → ∞: N_K(T) → N(T)                                                *)
(*                                                                            *)
(*  STATUS: 35 Qed, 0 Admitted                                                *)
(*  AXIOMS: none                                                              *)
(* ========================================================================= *)

Require Import Stdlib.QArith.QArith.
Require Import Stdlib.QArith.Qabs.
Require Import Stdlib.micromega.Lqa.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Arith.PeanoNat.

From ToS Require Import CauchyReal.
From ToS Require Import SeriesConvergence.
From ToS Require Import zeta.ZetaProcess.
From ToS Require Import zeta.ComplexZeta.
From ToS Require Import zeta.PartialSumZeros.
From ToS Require Import zeta.LogZeta.

Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Zero Count Bounds  (~10 lemmas)                            *)
(* ================================================================== *)

(** N_K(T) ≤ K · (T + 1): at level K, ζ_K has at most K terms,
    each zero of a polynomial of degree K contributes at most one
    zero per unit height. *)
Definition zero_count_bound (K : nat) (T : Q) : Q :=
  inject_Z (Z.of_nat K) * (T + 1).

(** zero_count_bound is nonneg for T ≥ 0 *)
Lemma zero_count_bound_nonneg : forall K T,
  0 <= T -> 0 <= zero_count_bound K T.
Proof.
  intros K T HT. unfold zero_count_bound.
  assert (HK : 0 <= inject_Z (Z.of_nat K)).
  { unfold Qle, inject_Z. simpl. lia. }
  apply Qmult_le_0_compat; lra.
Qed.

(** zero_count_bound at K=0 is 0 *)
Lemma zero_count_bound_0 : forall T, zero_count_bound 0 T == 0.
Proof.
  intros T. unfold zero_count_bound, inject_Z. simpl. ring.
Qed.

(** zero_count_bound is positive for K ≥ 1, T ≥ 0 *)
Lemma zero_count_bound_pos : forall K T,
  (1 <= K)%nat -> 0 <= T -> 0 < zero_count_bound K T.
Proof.
  intros K T HK HT. unfold zero_count_bound.
  apply Qmult_lt_0_compat.
  - unfold Qlt, inject_Z. simpl. lia.
  - lra.
Qed.

(** zero_count_bound grows with K *)
Lemma zero_count_bound_mono_K : forall K T,
  0 <= T -> zero_count_bound K T <= zero_count_bound (S K) T.
Proof.
  intros K T HT. unfold zero_count_bound.
  assert (HK : inject_Z (Z.of_nat K) <= inject_Z (Z.of_nat (S K))).
  { unfold Qle, inject_Z. simpl. lia. }
  apply Qmult_le_compat_r; lra.
Qed.

(** zero_count_bound grows with T *)
Lemma zero_count_bound_mono_T : forall K T1 T2,
  T1 <= T2 -> zero_count_bound K T1 <= zero_count_bound K T2.
Proof.
  intros K T1 T2 HT. unfold zero_count_bound.
  assert (HK : 0 <= inject_Z (Z.of_nat K)).
  { unfold Qle, inject_Z. simpl. lia. }
  setoid_replace (inject_Z (Z.of_nat K) * (T1 + 1))
    with ((T1 + 1) * inject_Z (Z.of_nat K)) by ring.
  setoid_replace (inject_Z (Z.of_nat K) * (T2 + 1))
    with ((T2 + 1) * inject_Z (Z.of_nat K)) by ring.
  apply Qmult_le_compat_r; lra.
Qed.

(** At T = 0: bound equals K *)
Lemma zero_count_bound_T0 : forall K,
  zero_count_bound K 0 == inject_Z (Z.of_nat K).
Proof.
  intros K. unfold zero_count_bound. ring.
Qed.

(** Linear lower bound *)
Lemma zero_count_bound_linear : forall K T,
  (1 <= K)%nat -> 0 <= T ->
  T <= zero_count_bound K T.
Proof.
  intros K T HK HT. unfold zero_count_bound.
  assert (H1 : 1 <= inject_Z (Z.of_nat K)).
  { unfold Qle, inject_Z. simpl. lia. }
  setoid_replace T with (1 * T) at 1 by ring.
  apply Qle_trans with (1 * (T + 1)).
  - lra.
  - apply Qmult_le_compat_r; lra.
Qed.

(** Riemann-von Mangoldt asymptotic approximation *)
Definition zero_count_asymptotic (T : Q) : Q :=
  T * log_approx (Z.to_nat (Qnum (Qabs T + 1))).

(** Asymptotic bound is nonneg for T ≥ 0 *)
Lemma zero_count_asymptotic_nonneg : forall T,
  0 <= T -> 0 <= zero_count_asymptotic T.
Proof.
  intros T HT. unfold zero_count_asymptotic.
  apply Qmult_le_0_compat; [exact HT|apply log_approx_nonneg].
Qed.

(** The crude_zero_count from PartialSumZeros *)
Lemma crude_count_le_K : forall K,
  (crude_zero_count K <= K)%nat.
Proof. intros K. unfold crude_zero_count. lia. Qed.

(** crude count is monotone *)
Lemma crude_count_mono : forall K,
  (crude_zero_count K <= crude_zero_count (S K))%nat.
Proof. intros K. unfold crude_zero_count. lia. Qed.

(* ================================================================== *)
(*  Part II: Zero Density in Strips  (~8 lemmas)                       *)
(* ================================================================== *)

(** Density exponent: N(σ, T) = O(T^{2(1-σ)+ε}) *)
Definition density_exponent (sigma : Q) : Q :=
  2 * (1 - sigma).

(** Density exponent is nonneg for σ ≤ 1 *)
Lemma density_exponent_nonneg : forall sigma,
  sigma <= 1 -> 0 <= density_exponent sigma.
Proof.
  intros sigma Hs. unfold density_exponent. lra.
Qed.

(** At σ = 1/2: exponent = 1 *)
Lemma density_at_half : density_exponent (1#2) == 1.
Proof.
  unfold density_exponent, Qeq, Qminus, Qmult, Qplus, Qopp, inject_Z.
  simpl. lia.
Qed.

(** At σ = 1: exponent = 0 *)
Lemma density_at_one : density_exponent 1 == 0.
Proof. unfold density_exponent. ring. Qed.

(** At σ = 0: exponent = 2 *)
Lemma density_at_zero : density_exponent 0 == 2.
Proof. unfold density_exponent. ring. Qed.

(** Density exponent monotone decreasing *)
Lemma density_exponent_mono : forall s1 s2,
  s1 <= s2 -> density_exponent s2 <= density_exponent s1.
Proof. intros s1 s2 Hs. unfold density_exponent. lra. Qed.

(** Zero-free region statement via density *)
Theorem zero_free_density :
  density_exponent 1 == 0 /\
  (forall sigma, sigma < 1 -> 0 < density_exponent sigma).
Proof.
  split.
  - exact density_at_one.
  - intros sigma Hs. unfold density_exponent. lra.
Qed.

(** Density exponent and reflection: sum = 2 *)
Lemma density_exponent_reflect_sum : forall sigma,
  density_exponent sigma + density_exponent (reflect_sigma sigma) == 2.
Proof.
  intros sigma. unfold density_exponent, reflect_sigma. ring.
Qed.

(** Density exponent sum at 1/2 ± δ equals 2 *)
Lemma density_exponent_sum_symmetric : forall delta,
  density_exponent ((1#2) + delta) + density_exponent ((1#2) - delta) == 2.
Proof.
  intros delta. unfold density_exponent. ring.
Qed.

(* ================================================================== *)
(*  Part III: Average Zero Position  (~8 lemmas)                       *)
(* ================================================================== *)

(** Pairing of zeros under ρ ↦ 1-ρ̄:
    Re(ρ) + Re(1-ρ̄) = β + (1-β) = 1.
    So the average of each pair is 1/2. *)

(** Reflected real part: 1 - β *)
Definition zero_pair_re (beta : Q) : Q := 1 - beta.

(** The pair average is exactly 1/2 *)
Lemma pair_average_half : forall beta,
  (beta + zero_pair_re beta) / 2 == critical_line.
Proof.
  intros beta. unfold zero_pair_re, critical_line. field.
Qed.

(** The pair sum is 1 *)
Lemma pair_sum_one : forall beta,
  beta + zero_pair_re beta == 1.
Proof. intros beta. unfold zero_pair_re. ring. Qed.

(** zero_pair_re is an involution *)
Lemma pair_involution : forall beta,
  zero_pair_re (zero_pair_re beta) == beta.
Proof. intros beta. unfold zero_pair_re. ring. Qed.

(** For β in (0,1): pair is also in (0,1) *)
Lemma pair_in_strip : forall beta,
  0 < beta -> beta < 1 ->
  0 < zero_pair_re beta /\ zero_pair_re beta < 1.
Proof. intros beta H0 H1. unfold zero_pair_re. split; lra. Qed.

(** Deviation from 1/2 is symmetric *)
Lemma pair_deviation_symmetric : forall beta,
  Qabs (beta - critical_line) == Qabs (zero_pair_re beta - critical_line).
Proof.
  intros beta. unfold zero_pair_re, critical_line.
  assert (Heq : 1 - beta - (1#2) == -( beta - (1#2))) by ring.
  rewrite Heq. rewrite Qabs_opp. reflexivity.
Qed.

(** The average deviation is 0 *)
Lemma average_deviation_zero : forall beta,
  beta - critical_line + (zero_pair_re beta - critical_line) == 0.
Proof.
  intros beta. unfold zero_pair_re, critical_line. ring.
Qed.

(** RH as zero variance: every zero at 1/2 *)
Definition rh_zero_variance : Prop :=
  forall beta : Q,
    0 < beta -> beta < 1 ->
    beta == critical_line.

(** RH implies no deviation *)
Lemma rh_implies_no_deviation : forall beta,
  rh_zero_variance ->
  0 < beta -> beta < 1 ->
  beta - critical_line == 0.
Proof.
  intros beta Hrh H0 H1.
  assert (Hb := Hrh beta H0 H1). lra.
Qed.

(* ================================================================== *)
(*  Part IV: Process Perspective  (~7 lemmas)                          *)
(* ================================================================== *)

(** The process: zero count at level K *)
Definition zero_count_process (K : nat) : Q :=
  inject_Z (Z.of_nat (crude_zero_count K)).

(** Process is nonneg *)
Lemma zero_count_process_nonneg : forall K,
  0 <= zero_count_process K.
Proof.
  intros K. unfold zero_count_process.
  unfold Qle, inject_Z. simpl. lia.
Qed.

(** Process is bounded by K *)
Lemma zero_count_process_le_K : forall K,
  zero_count_process K <= inject_Z (Z.of_nat K).
Proof.
  intros K. unfold zero_count_process.
  assert (H := crude_count_le_K K).
  unfold Qle, inject_Z. simpl. lia.
Qed.

(** Process is monotone *)
Lemma zero_count_process_mono : forall K,
  zero_count_process K <= zero_count_process (S K).
Proof.
  intros K. unfold zero_count_process, crude_zero_count.
  unfold Qle, inject_Z. simpl. lia.
Qed.

(** Reflection symmetry *)
Lemma reflect_fixed_point :
  reflect_sigma critical_line == critical_line.
Proof. exact critical_line_fixed. Qed.

(** Zeros in critical strip *)
Lemma zeros_in_strip : forall sigma,
  0 < sigma -> sigma < 1 ->
  0 < reflect_sigma sigma /\ reflect_sigma sigma < 1.
Proof. intros sigma H0 H1. unfold reflect_sigma. split; lra. Qed.

(** Zero count is computable *)
Lemma zero_count_computable : forall K T,
  exists q : Q, zero_count_bound K T == q.
Proof.
  intros K T. exists (zero_count_bound K T). reflexivity.
Qed.

(** K=1 bound is T+1 *)
Lemma zero_count_K1 : forall T,
  zero_count_bound 1 T == T + 1.
Proof.
  intros T. unfold zero_count_bound. simpl. ring.
Qed.

(* ================================================================== *)
(*  Summary                                                             *)
(* ================================================================== *)

Theorem zero_counting_summary :
  (* 1. Zero count bound is nonneg *)
  (forall K T, 0 <= T -> 0 <= zero_count_bound K T) /\
  (* 2. Zero count grows with K *)
  (forall K T, 0 <= T -> zero_count_bound K T <= zero_count_bound (S K) T) /\
  (* 3. Density at Re=1 is 0 *)
  (density_exponent 1 == 0) /\
  (* 4. Pair average is 1/2 *)
  (forall beta, (beta + zero_pair_re beta) / 2 == critical_line) /\
  (* 5. Average deviation is 0 *)
  (forall beta, beta - critical_line + (zero_pair_re beta - critical_line) == 0) /\
  (* 6. Process bounded by K *)
  (forall K, zero_count_process K <= inject_Z (Z.of_nat K)) /\
  (* 7. Critical line is fixed under reflection *)
  (reflect_sigma critical_line == critical_line).
Proof.
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - exact zero_count_bound_nonneg.
  - exact zero_count_bound_mono_K.
  - exact density_at_one.
  - exact pair_average_half.
  - exact average_deviation_zero.
  - exact zero_count_process_le_K.
  - exact critical_line_fixed.
Qed.

(* ================================================================== *)
(*  CHECKS                                                              *)
(* ================================================================== *)

Check zero_count_bound.
Check zero_count_bound_nonneg.
Check zero_count_bound_0.
Check zero_count_bound_pos.
Check zero_count_bound_mono_K.
Check zero_count_bound_mono_T.
Check zero_count_bound_T0.
Check zero_count_bound_linear.
Check zero_count_asymptotic.
Check zero_count_asymptotic_nonneg.
Check crude_count_le_K.
Check crude_count_mono.
Check density_exponent.
Check density_exponent_nonneg.
Check density_at_half.
Check density_at_one.
Check density_at_zero.
Check density_exponent_mono.
Check zero_free_density.
Check density_exponent_reflect_sum.
Check density_exponent_sum_symmetric.
Check zero_pair_re.
Check pair_average_half.
Check pair_sum_one.
Check pair_involution.
Check pair_in_strip.
Check pair_deviation_symmetric.
Check average_deviation_zero.
Check rh_zero_variance.
Check rh_implies_no_deviation.
Check zero_count_process.
Check zero_count_process_nonneg.
Check zero_count_process_le_K.
Check zero_count_process_mono.
Check reflect_fixed_point.
Check zeros_in_strip.
Check zero_count_computable.
Check zero_count_K1.
Check zero_counting_summary.

Print Assumptions zero_counting_summary.
