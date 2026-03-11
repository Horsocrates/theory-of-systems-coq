(* ========================================================================= *)
(*        GAP DECAY RATE — How fast mass gap vanishes along RG orbit         *)
(*                                                                           *)
(*  Along exact RG: β_k = 8 - ε/2^k where ε = 8-β.                       *)
(*  U(1) gap: mass_gap_2x2(β_k) = ε/(4·2^k) → 0                         *)
(*  SU(2) gap: su2_mass_gap(β_k) = (1+ε/(8·2^k))² · ε/(4·2^k)           *)
(*            bounded: u1_gap ≤ su2_gap ≤ 4·u1_gap                        *)
(*  Both → 0 exponentially.                                                *)
(*                                                                           *)
(*  STATUS: ~22 Qed, 0 Admitted                                             *)
(*  Author: Horsocrates | Date: March 2026                                   *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs List Lia ZArith.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import CauchyReal.
From ToS Require Import SeriesConvergence.
From ToS Require Import gauge.TransferMatrix.
From ToS Require Import gauge.SU2TransferMatrix.
From ToS Require Import gauge.LargerLattice.
From ToS Require Import gauge.GapMatching.
From ToS Require Import gauge.ExactRGProcess.

(* ========================================================================= *)
(*  PART I: Coupling along RG orbit                                          *)
(* ========================================================================= *)

(** Coupling at stage k of RG orbit *)
Definition beta_k (beta : Q) (k : nat) : Q := exact_rg 0 k beta.

(** Deviation from critical coupling β=8 *)
Definition epsilon_k (beta : Q) (k : nat) : Q := 8 - beta_k beta k.

(** beta_k at stage 0 is β *)
Lemma beta_k_at_0 : forall beta, beta_k beta 0 == beta.
Proof.
  intros beta. unfold beta_k. apply exact_rg_0.
Qed.

(** beta_k stays in (0, 8) *)
Lemma beta_k_range : forall beta k,
  0 < beta -> beta < 8 ->
  0 < beta_k beta k /\ beta_k beta k < 8.
Proof.
  intros beta k Hb1 Hb2. unfold beta_k.
  apply exact_rg_range; assumption.
Qed.

(** beta_k is increasing *)
Lemma beta_k_increasing : forall beta k,
  0 < beta -> beta < 8 ->
  beta_k beta k <= beta_k beta (S k).
Proof.
  intros beta k Hb1 Hb2. unfold beta_k.
  apply exact_rg_increasing; assumption.
Qed.

(** epsilon_k is positive *)
Lemma epsilon_k_positive : forall beta k,
  0 < beta -> beta < 8 ->
  0 < epsilon_k beta k.
Proof.
  intros beta k Hb1 Hb2. unfold epsilon_k.
  assert (H := beta_k_range beta k Hb1 Hb2). lra.
Qed.

(** epsilon_k is decreasing (beta_k increasing → 8-beta_k decreasing) *)
Lemma epsilon_k_decreasing : forall beta k,
  0 < beta -> beta < 8 ->
  epsilon_k beta (S k) <= epsilon_k beta k.
Proof.
  intros beta k Hb1 Hb2. unfold epsilon_k.
  assert (H := beta_k_increasing beta k Hb1 Hb2). lra.
Qed.

(** epsilon_k at stage 0 *)
Lemma epsilon_k_at_0 : forall beta,
  epsilon_k beta 0 == 8 - beta.
Proof.
  intros beta. unfold epsilon_k.
  assert (H := beta_k_at_0 beta). lra.
Qed.

(* ========================================================================= *)
(*  PART II: U(1) gap at stage k                                             *)
(* ========================================================================= *)

(** U(1) mass gap at stage k *)
Definition u1_gap_at_k (beta : Q) (k : nat) : Q :=
  mass_gap_2x2 (beta_k beta k).

(** U(1) gap is positive *)
Lemma u1_gap_positive : forall beta k,
  0 < beta -> beta < 8 ->
  0 < u1_gap_at_k beta k.
Proof.
  intros beta k Hb1 Hb2. unfold u1_gap_at_k.
  apply mass_gap_2x2_positive; apply beta_k_range; assumption.
Qed.

(** U(1) gap equals gap_lower_N *)
Lemma u1_gap_eq_gap_lower : forall beta k,
  u1_gap_at_k beta k == gap_lower_N 0 (Nat.pow 2 k) beta.
Proof.
  intros beta k. unfold u1_gap_at_k, beta_k.
  apply gap_matching_preserves_gap.
Qed.

(** U(1) gap is decreasing *)
Lemma u1_gap_decreasing : forall beta k,
  0 < beta -> beta < 8 ->
  u1_gap_at_k beta (S k) <= u1_gap_at_k beta k.
Proof.
  intros beta k Hb1 Hb2.
  assert (Heq1 := u1_gap_eq_gap_lower beta (S k)).
  assert (Heq2 := u1_gap_eq_gap_lower beta k).
  assert (Hle := gap_lower_pow2_chain 0 k beta Hb1 Hb2).
  lra.
Qed.

(** U(1) gap is quarter of epsilon *)
Lemma u1_gap_quarter_epsilon : forall beta k,
  u1_gap_at_k beta k == epsilon_k beta k * (1#4).
Proof.
  intros beta k.
  unfold u1_gap_at_k, epsilon_k, beta_k,
         mass_gap_2x2, transfer_eigenvalue_0, transfer_eigenvalue_1.
  lra.
Qed.

(* ========================================================================= *)
(*  PART III: SU(2) gap bounds                                                *)
(* ========================================================================= *)

(** SU(2) mass gap at stage k *)
Definition su2_gap_at_k (beta : Q) (k : nat) : Q :=
  su2_mass_gap (beta_k beta k).

(** SU(2) gap is positive *)
Lemma su2_gap_positive_all_k : forall beta k,
  0 < beta -> beta < 8 ->
  0 < su2_gap_at_k beta k.
Proof.
  intros beta k Hb1 Hb2. unfold su2_gap_at_k.
  apply su2_mass_gap_positive; apply beta_k_range; assumption.
Qed.

(** SU(2) gap lower bound: su2_gap ≥ u1_gap *)
Lemma su2_gap_lower : forall beta k,
  0 < beta -> beta < 8 ->
  u1_gap_at_k beta k <= su2_gap_at_k beta k.
Proof.
  intros beta k Hb1 Hb2. unfold su2_gap_at_k, u1_gap_at_k.
  assert (Hrange := beta_k_range beta k Hb1 Hb2).
  apply Qlt_le_weak.
  apply su2_gap_vs_u1; [lra | lra].
Qed.

(** SU(2) enhancement factor bounded: (2-β/8)² < 4 for β > 0 *)
Lemma su2_factor_lt_4 : forall beta,
  0 < beta -> beta < 8 ->
  su2_mass_gap_factor beta < 4.
Proof.
  intros beta H1 H2. unfold su2_mass_gap_factor. nra.
Qed.

(** SU(2) gap upper bound: su2_gap < 4 · u1_gap *)
Lemma su2_gap_upper : forall beta k,
  0 < beta -> beta < 8 ->
  su2_gap_at_k beta k < 4 * u1_gap_at_k beta k.
Proof.
  intros beta k Hb1 Hb2. unfold su2_gap_at_k, u1_gap_at_k.
  assert (Hrange := beta_k_range beta k Hb1 Hb2).
  set (b := beta_k beta k) in *.
  assert (Hfact := su2_gap_factored b).
  assert (Hflt : su2_mass_gap_factor b < 4) by (apply su2_factor_lt_4; lra).
  assert (Hgap : 0 < mass_gap_2x2 b) by (apply mass_gap_2x2_positive; lra).
  (* su2_mass_gap b == factor * mass_gap, and factor < 4, gap > 0 *)
  assert (Hprod : su2_mass_gap_factor b * mass_gap_2x2 b < 4 * mass_gap_2x2 b).
  { apply Qmult_lt_r; assumption. }
  lra.
Qed.

(** SU(2) gap bounded by epsilon *)
Lemma su2_gap_le_epsilon : forall beta k,
  0 < beta -> beta < 8 ->
  su2_gap_at_k beta k < epsilon_k beta k.
Proof.
  intros beta k Hb1 Hb2.
  assert (Hupper := su2_gap_upper beta k Hb1 Hb2).
  assert (Hquarter := u1_gap_quarter_epsilon beta k).
  (* su2_gap < 4 * u1_gap = 4 * (epsilon/4) = epsilon *)
  lra.
Qed.

(* ========================================================================= *)
(*  PART IV: Gap vanishing — connecting to Qpow for limit                    *)
(* ========================================================================= *)

(** Connecting lemma: 1/2^k as Qpow *)
Lemma inv_pow2_eq_Qpow_half : forall k,
  / inject_Z (Z.of_nat (Nat.pow 2 k)) == Qpow (1#2) k.
Proof.
  induction k.
  - unfold Qeq. simpl. lia.
  - change (Qpow (1#2) (S k)) with ((1#2) * Qpow (1#2) k).
    transitivity ((1#2) * / inject_Z (Z.of_nat (Nat.pow 2 k))).
    2: { apply Qmult_comp; [reflexivity | exact IHk]. }
    assert (Hpow2 : Nat.pow 2 (S k) = (2 * Nat.pow 2 k)%nat) by (simpl; lia).
    rewrite Hpow2.
    assert (Hk_pos : (1 <= Nat.pow 2 k)%nat) by (apply pow2_pos).
    assert (Hz_pos : (0 < Z.of_nat (Nat.pow 2 k))%Z) by lia.
    rewrite Nat2Z.inj_mul. simpl (Z.of_nat 2).
    destruct (Z.of_nat (Nat.pow 2 k)) as [|p|p] eqn:Hz.
    + lia.
    + unfold Qeq. simpl. lia.
    + lia.
Qed.

(** epsilon_k expressed via Qpow *)
Lemma epsilon_k_via_Qpow : forall beta k,
  epsilon_k beta k == (8 - beta) * Qpow (1#2) k.
Proof.
  intros beta k.
  assert (Hinv := inv_pow2_eq_Qpow_half k).
  unfold epsilon_k, beta_k, exact_rg, gap_inverse, gap_lower_N,
         mass_gap_2x2, transfer_eigenvalue_0, transfer_eigenvalue_1.
  setoid_rewrite Hinv.
  lra.
Qed.

(** SU(2) gap vanishes: for any threshold, gap eventually drops below *)
Theorem su2_gap_vanishes : forall beta eps,
  0 < beta -> beta < 8 -> 0 < eps ->
  exists k, su2_gap_at_k beta k < eps.
Proof.
  intros beta epsil Hb1 Hb2 Heps.
  (* su2_gap < epsilon_k = (8-beta) * (1/2)^k *)
  (* By Qpow_limit_zero: exists k such that (1/2)^k < eps/(8-beta) *)
  assert (Hpos : 0 < 8 - beta) by lra.
  assert (Htarget : 0 < epsil * / (8 - beta)).
  { apply Qmult_lt_0_compat; [exact Heps |].
    apply Qinv_lt_0_compat. exact Hpos. }
  destruct (Qpow_limit_zero (1#2) ltac:(lra) ltac:(lra)
    (epsil * / (8 - beta)) Htarget) as [N HN].
  exists N.
  assert (Hle := su2_gap_le_epsilon beta N Hb1 Hb2).
  assert (Hek := epsilon_k_via_Qpow beta N).
  (* su2_gap < epsilon_k = (8-beta) * Qpow(1/2, N) < (8-beta) * eps/(8-beta) = eps *)
  assert (HpowN := HN N ltac:(lia)).
  assert (Hbound : epsilon_k beta N < epsil).
  { assert (Heq : epsilon_k beta N == (8 - beta) * Qpow (1 # 2) N) by exact Hek.
    assert (Hprod : (8 - beta) * Qpow (1 # 2) N < (8 - beta) * (epsil * / (8 - beta))).
    { setoid_replace ((8 - beta) * Qpow (1 # 2) N)
        with (Qpow (1 # 2) N * (8 - beta)) by ring.
      setoid_replace ((8 - beta) * (epsil * / (8 - beta)))
        with ((epsil * / (8 - beta)) * (8 - beta)) by ring.
      apply Qmult_lt_compat_r; [exact Hpos | exact HpowN]. }
    assert (Hsimp : (8 - beta) * (epsil * / (8 - beta)) == epsil).
    { field. lra. }
    lra. }
  lra.
Qed.

(** U(1) gap also vanishes *)
Theorem u1_gap_vanishes : forall beta eps,
  0 < beta -> beta < 8 -> 0 < eps ->
  exists k, u1_gap_at_k beta k < eps.
Proof.
  intros beta epsil Hb1 Hb2 Heps.
  destruct (su2_gap_vanishes beta epsil Hb1 Hb2 Heps) as [k Hk].
  exists k.
  assert (Hlower := su2_gap_lower beta k Hb1 Hb2).
  lra.
Qed.

(* ========================================================================= *)
(*  PART V: Summary                                                           *)
(* ========================================================================= *)

(** ★ Gap decay main theorem ★ *)
Theorem gap_decay_main :
  (* 1. SU(2) gap is positive at every stage *)
  (forall beta k, 0 < beta -> beta < 8 -> 0 < su2_gap_at_k beta k) /\
  (* 2. SU(2) gap is bounded by epsilon_k *)
  (forall beta k, 0 < beta -> beta < 8 -> su2_gap_at_k beta k < epsilon_k beta k) /\
  (* 3. SU(2) gap vanishes *)
  (forall beta eps, 0 < beta -> beta < 8 -> 0 < eps ->
    exists k, su2_gap_at_k beta k < eps) /\
  (* 4. Enhancement factor bounded *)
  (forall beta, 0 < beta -> beta < 8 -> su2_mass_gap_factor beta < 4).
Proof.
  split; [exact su2_gap_positive_all_k |].
  split; [exact su2_gap_le_epsilon |].
  split; [exact su2_gap_vanishes |].
  exact su2_factor_lt_4.
Qed.

(** Our model predicts gap → 0 but gap(k) > 0 at every stage *)
Theorem our_model_vs_reality :
  (* Our model: gap → 0 *)
  (forall beta eps, 0 < beta -> beta < 8 -> 0 < eps ->
    exists k, su2_gap_at_k beta k < eps) /\
  (* But gap(k) > 0 at every finite k *)
  (forall beta k, 0 < beta -> beta < 8 -> 0 < su2_gap_at_k beta k) /\
  (* Reality: gap should stabilize (confinement) *)
  (* We can't prove this — it requires confinement correction *)
  True.
Proof.
  split; [exact su2_gap_vanishes |].
  split; [exact su2_gap_positive_all_k |].
  exact I.
Qed.

(** End marker *)
Theorem total_count : True.
Proof. exact I. Qed.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  ~22 Qed, 0 Admitted                                                       *)
(*                                                                            *)
(*  Part I: beta_k_at_0, beta_k_range, beta_k_increasing,                   *)
(*          epsilon_k_positive, epsilon_k_decreasing, epsilon_k_at_0 (6)     *)
(*  Part II: u1_gap_positive, u1_gap_eq_gap_lower, u1_gap_decreasing,        *)
(*           u1_gap_quarter_epsilon (4)                                      *)
(*  Part III: su2_gap_positive_all_k, su2_gap_lower, su2_factor_lt_4,        *)
(*            su2_gap_upper, su2_gap_le_epsilon (5)                          *)
(*  Part IV: inv_pow2_eq_Qpow_half, epsilon_k_via_Qpow,                     *)
(*           su2_gap_vanishes, u1_gap_vanishes (4)                           *)
(*  Part V: gap_decay_main, our_model_vs_reality, total_count (3)            *)
(* ========================================================================= *)
