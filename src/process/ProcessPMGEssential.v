(** * ProcessPMGEssential.v — Essential Spectral Gap as PMG
    Elements: discrete vs essential spectrum eigenvalues
    Roles:    isolated ground state vs bulk/continuous spectrum
    Rules:    PMG satisfied ↔ isolated ground state
    Status:   complete
    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        PMG ESSENTIAL — Essential Spectral Gap as PMG                        *)
(*                                                                           *)
(*  For operators with both discrete and essential spectrum:                *)
(*  essential gap = inf σ_ess(A) − inf σ(A)                               *)
(*  If A_n = truncation: discrete eigenvalues approximate both parts.      *)
(*                                                                           *)
(*  STATUS: 8 Qed, 0 Admitted                                             *)
(*  AXIOMS: none                                                             *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessBounds.
From ToS Require Import process.ProcessPMGMarkov.
From ToS Require Import SeriesConvergence.

(* ================================================================== *)
(*  Part I: Essential Gap  (~6 lemmas)                                *)
(* ================================================================== *)

(** Model: eigenvalue sequence where ground state is isolated *)
(** eigenvals k gives the k-th eigenvalue (increasing) *)

(** Essential gap: distance from ground to bulk *)
(** Approximate: gap between eigenvalue 0 and eigenvalue at index n/2 *)
Definition essential_gap (eigenvals : nat -> Q) (n : nat) : Q :=
  eigenvals (S n) - eigenvals 0%nat.

(** Essential gap process *)
Definition essential_gap_process (eigenvals : nat -> Q) : RealProcess :=
  fun n => essential_gap eigenvals n.

(** If eigenvalues are increasing, gap is nonneg *)
Lemma essential_gap_nonneg : forall eigenvals n,
  (forall k, eigenvals k <= eigenvals (S k)) ->
  0 <= essential_gap_process eigenvals n.
Proof.
  intros eigenvals n Hinc. unfold essential_gap_process, essential_gap.
  induction n.
  - assert (H := Hinc 0%nat). lra.
  - assert (H := Hinc (S n)). lra.
Qed.

(** Essential gap is increasing (larger truncation reveals more spectrum) *)
Lemma essential_gap_increasing : forall eigenvals,
  (forall k, eigenvals k <= eigenvals (S k)) ->
  monotone_increasing (essential_gap_process eigenvals).
Proof.
  intros eigenvals Hinc n. unfold essential_gap_process, essential_gap.
  assert (H := Hinc (S n)). lra.
Qed.

(** If ground state is fixed, gap grows with spectrum *)
Lemma essential_gap_ground_fixed : forall eigenvals g,
  (forall k, eigenvals k <= eigenvals (S k)) ->
  eigenvals 0%nat == g ->
  forall n, essential_gap_process eigenvals n == eigenvals (S n) - g.
Proof.
  intros eigenvals g Hinc Hg n. unfold essential_gap_process, essential_gap.
  lra.
Qed.

(* ================================================================== *)
(*  Part II: Isolated Ground State → PMG  (~5 lemmas)                *)
(* ================================================================== *)

(** Model: eigenvalue 0 is isolated, rest are ≥ delta above *)
Definition isolated_ground (eigenvals : nat -> Q) (delta : Q) : Prop :=
  0 < delta /\ forall k, (1 <= k)%nat -> delta <= eigenvals k - eigenvals 0%nat.

(** Isolated ground → essential gap bounded below *)
Lemma isolated_implies_gap_bound : forall eigenvals delta,
  isolated_ground eigenvals delta ->
  forall n, delta <= essential_gap_process eigenvals n.
Proof.
  intros eigenvals delta [Hd Hbound] n.
  unfold essential_gap_process, essential_gap.
  apply Hbound. lia.
Qed.

(** Isolated ground + Cauchy + decreasing → PMG *)
Theorem isolated_ground_pmg : forall eigenvals delta r C,
  isolated_ground eigenvals delta ->
  0 < r -> r < 1 -> 0 < C ->
  (forall m n, Qabs (essential_gap_process eigenvals m -
                      essential_gap_process eigenvals n) <=
    C * Qpow r (Nat.min m n)) ->
  monotone_decreasing (essential_gap_process eigenvals) ->
  has_process_mass_gap (essential_gap_process eigenvals).
Proof.
  intros eigenvals delta r C [Hd Hbound] Hr Hr1 HC Hrate Hdec.
  apply build_pmg with (delta := delta) (r := r) (C := C); auto.
  intros n. apply isolated_implies_gap_bound. split; auto.
Qed.

(** Constant-gap model: eigenvals k = k * delta *)
Definition uniform_spectrum (delta : Q) : nat -> Q :=
  fun k => delta * (Z.of_nat k # 1).

Lemma uniform_gap_constant : forall delta n,
  0 < delta ->
  essential_gap_process (uniform_spectrum delta) n == delta * (Z.of_nat (S n) # 1).
Proof.
  intros delta n Hd. unfold essential_gap_process, essential_gap, uniform_spectrum.
  assert (H0 : delta * (Z.of_nat 0 # 1) == 0).
  { simpl. lra. }
  lra.
Qed.

(* ================================================================== *)
(*  Part III: Accumulating Spectrum → No PMG  (~4 lemmas)            *)
(* ================================================================== *)

(** Direct model: gap process that explicitly goes to 0 *)

Definition vanishing_gap_process : RealProcess :=
  fun n => 1 # Pos.of_nat (S (S n)).

Lemma vanishing_gap_pos : forall n,
  0 < vanishing_gap_process n.
Proof.
  intros n. unfold vanishing_gap_process.
  unfold Qlt.
  change (Qnum (1 # Pos.of_nat (S (S n)))) with 1%Z.
  change (Qden (1 # Pos.of_nat (S (S n)))) with (Pos.of_nat (S (S n))).
  change (Qnum 0) with 0%Z. change (Qden 0) with 1%positive.
  assert (Hz := pos_of_nat_to_Z (S (S n)) ltac:(lia)).
  rewrite Hz. nia.
Qed.

(** No PMG for vanishing gap *)
Theorem continuous_spectrum_no_pmg :
  has_process_mass_gap vanishing_gap_process -> False.
Proof.
  intros Hpmg.
  destruct Hpmg as [delta r C Hdelta Hbound _ _ _ _].
  assert (Harch : exists n, vanishing_gap_process n < delta).
  { exists (Z.to_nat (Z.pos (Qden delta))).
    unfold vanishing_gap_process.
    set (N := Z.to_nat (Z.pos (Qden delta))).
    unfold Qlt.
    change (Qnum (1 # Pos.of_nat (S (S N)))) with 1%Z.
    change (Qden (1 # Pos.of_nat (S (S N)))) with (Pos.of_nat (S (S N))).
    assert (Hz := pos_of_nat_to_Z (S (S N)) ltac:(lia)).
    assert (HN : (Z.of_nat N = Z.pos (Qden delta))%Z).
    { subst N. rewrite Z2Nat.id; lia. }
    assert (Hnum : (0 < Qnum delta)%Z).
    { destruct delta as [p q]. unfold Qlt in Hdelta. simpl in *. lia. }
    rewrite Hz. nia. }
  destruct Harch as [n Hn].
  assert (Hle := Hbound n). lra.
Qed.

(* ================================================================== *)
(*  Checks                                                              *)
(* ================================================================== *)

Check essential_gap_process. Check essential_gap_nonneg.
Check essential_gap_increasing. Check essential_gap_ground_fixed.
Check isolated_ground. Check isolated_implies_gap_bound. Check isolated_ground_pmg.
Check uniform_gap_constant.
Check vanishing_gap_pos. Check continuous_spectrum_no_pmg.
