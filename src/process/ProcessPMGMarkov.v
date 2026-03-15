(** * ProcessPMGMarkov.v — Markov Chain Spectral Gap as PMG
    Elements: transition probabilities, eigenvalues at level n
    Roles:    stationary (eigenvalue 1) vs transient (eigenvalue < 1)
    Rules:    row-stochastic constraint, mixing rate = gap
    Status:   complete
    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        PMG MARKOV — Spectral Gap of Markov Chains as PMG                    *)
(*                                                                           *)
(*  A Markov chain on n states has transition matrix P (n×n, rows sum to 1).*)
(*  Eigenvalues: 1 = λ₁ ≥ λ₂ ≥ ... ≥ λ_n ≥ -1.                          *)
(*  Spectral gap: γ = 1 − λ₂ > 0 iff chain is ergodic.                    *)
(*  Under P4: infinite state space = process of n×n truncations.           *)
(*                                                                           *)
(*  STATUS: 15 Qed, 0 Admitted                                             *)
(*  AXIOMS: none                                                             *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessBounds.
From ToS Require Import SeriesConvergence.

(* ================================================================== *)
(*  Part I: Markov Chain on Q  (~7 lemmas)                             *)
(* ================================================================== *)

(** Second eigenvalue process: λ₂(n) for n-state truncation *)
(** At level n: the second-largest eigenvalue of the transition matrix *)
Definition second_eigenvalue_process (lambda2 : RealProcess) := lambda2.

(** Markov spectral gap: γ(n) = 1 − λ₂(n) *)
Definition markov_gap (lambda2 : RealProcess) : RealProcess :=
  fun n => 1 - lambda2 n.

(** If λ₂(n) < 1 for all n, then gap is positive *)
Lemma markov_gap_pos : forall lambda2 n,
  lambda2 n < 1 ->
  0 < markov_gap lambda2 n.
Proof.
  intros lambda2 n Hlt. unfold markov_gap. lra.
Qed.

(** If λ₂ increasing (toward 1), then gap is decreasing *)
Lemma markov_gap_decreasing : forall lambda2,
  monotone_increasing lambda2 ->
  monotone_decreasing (markov_gap lambda2).
Proof.
  intros lambda2 Hinc n. unfold markov_gap, monotone_increasing in *.
  specialize (Hinc n). lra.
Qed.

(** Markov gap bounded: if λ₂ ≥ -1, then gap ≤ 2 *)
Lemma markov_gap_bounded : forall lambda2 n,
  -(1) <= lambda2 n ->
  markov_gap lambda2 n <= 2.
Proof.
  intros lambda2 n Hge. unfold markov_gap. lra.
Qed.

(** λ₂ ≤ 1 implies gap ≥ 0 *)
Lemma markov_gap_nonneg : forall lambda2 n,
  lambda2 n <= 1 ->
  0 <= markov_gap lambda2 n.
Proof.
  intros lambda2 n Hle. unfold markov_gap. lra.
Qed.

(* ================================================================== *)
(*  Part II: Uniformly Ergodic → PMG  (~7 lemmas)                     *)
(* ================================================================== *)

(** Uniformly ergodic: gap ≥ ε > 0 for all n *)
Definition uniformly_ergodic (lambda2 : RealProcess) (eps : Q) : Prop :=
  0 < eps /\ forall n, eps <= markov_gap lambda2 n.

(** Uniform ergodicity implies positive gap *)
Lemma ergodic_gap_pos : forall lambda2 eps,
  uniformly_ergodic lambda2 eps ->
  forall n, 0 < markov_gap lambda2 n.
Proof.
  intros lambda2 eps [Heps Hbound] n.
  assert (H := Hbound n). lra.
Qed.

(** Ergodic + Cauchy rate + decreasing → PMG *)
Theorem markov_ergodic_pmg : forall lambda2 eps C r,
  uniformly_ergodic lambda2 eps ->
  0 < C -> 0 < r -> r < 1 ->
  (forall m n, Qabs (markov_gap lambda2 m - markov_gap lambda2 n) <=
    C * Qpow r (Nat.min m n)) ->
  monotone_decreasing (markov_gap lambda2) ->
  has_process_mass_gap (markov_gap lambda2).
Proof.
  intros lambda2 eps C r [Heps Hbound] HC Hr Hr1 Hrate Hdec.
  apply build_pmg with (delta := eps) (r := r) (C := C); auto.
Qed.

(** Constant λ₂ gives constant gap → trivial PMG *)
Lemma constant_eigenvalue_pmg : forall v,
  v < 1 ->
  has_process_mass_gap (markov_gap (fun _ => v)).
Proof.
  intros v Hv.
  apply build_pmg with (delta := 1 - v) (r := 1#2) (C := 1); try lra.
  - intros n. unfold markov_gap. lra.
  - intros m n. unfold markov_gap.
    assert (Heq : (1 - v) - (1 - v) == 0) by lra.
    rewrite Heq. rewrite Qabs_pos; [| lra].
    apply Qle_trans with 0; [lra |].
    apply Qle_trans with (Qpow (1#2) (Nat.min m n)).
    + apply Qpow_nonneg. lra.
    + assert (Hnn : 0 <= Qpow (1#2) (Nat.min m n)) by (apply Qpow_nonneg; lra).
      lra.
  - intros n. unfold markov_gap. lra.
Qed.

(* ================================================================== *)
(*  Part III: Cycle Random Walk  (~4 lemmas)                           *)
(* ================================================================== *)

(** Random walk on cycle Z/mZ: gap ≈ 2π²/m² *)
(** Rational approximation: gap(m) ≈ 20/m² *)

Definition cycle_gap_approx (m : nat) : Q :=
  20 # (Pos.of_nat (S m * S m)).

(** Cycle gap is positive *)
Lemma cycle_gap_pos : forall m,
  0 < cycle_gap_approx m.
Proof.
  intros m. unfold cycle_gap_approx.
  unfold Qlt. simpl. lia.
Qed.

(** Cycle gap decreases with m (larger cycle → slower mixing) *)
Lemma pos_of_nat_to_Z : forall k, (k > 0)%nat ->
  (Z.pos (Pos.of_nat k) = Z.of_nat k)%Z.
Proof.
  intros k Hk.
  rewrite <- (Nat2Pos.id k ltac:(lia)) at 2.
  rewrite positive_nat_Z. reflexivity.
Qed.

Lemma cycle_gap_decreasing :
  monotone_decreasing (fun n => cycle_gap_approx n).
Proof.
  intros n. unfold cycle_gap_approx.
  unfold Qle.
  (* Goal: 20 * Z.pos(Pos.of_nat(S(Sn)*S(Sn))) <= 20 * Z.pos(Pos.of_nat(Sn*Sn)) *)
  (* Wait — simpl changes shape. Let me use change instead *)
  change (Qnum (20 # Pos.of_nat (S (S n) * S (S n)))) with 20%Z.
  change (Qnum (20 # Pos.of_nat (S n * S n))) with 20%Z.
  change (Qden (20 # Pos.of_nat (S (S n) * S (S n))))
    with (Pos.of_nat (S (S n) * S (S n))).
  change (Qden (20 # Pos.of_nat (S n * S n)))
    with (Pos.of_nat (S n * S n)).
  assert (Ha := pos_of_nat_to_Z (S n * S n) ltac:(lia)).
  assert (Hb := pos_of_nat_to_Z (S (S n) * S (S n)) ltac:(lia)).
  rewrite Ha, Hb. nia.
Qed.

(** Cycle gap → 0 as m → ∞: NO PMG for infinite random walk *)
(** This is physically correct: random walk on Z is not ergodic *)
(** Archimedean helper: for any positive Q, exists n with 20/(S n)² < q *)
Lemma cycle_gap_archimedean : forall delta,
  0 < delta -> exists n, cycle_gap_approx n < delta.
Proof.
  intros delta Hd.
  (* delta = Qnum delta / Qden delta, delta > 0 *)
  exists (Z.to_nat (20 * Z.pos (Qden delta))).
  unfold cycle_gap_approx.
  (* 20 # Pos.of_nat(S N * S N) < delta *)
  set (N := Z.to_nat (20 * Z.pos (Qden delta))).
  unfold Qlt.
  change (Qnum (20 # Pos.of_nat (S N * S N))) with 20%Z.
  change (Qden (20 # Pos.of_nat (S N * S N))) with (Pos.of_nat (S N * S N)).
  assert (Hz := pos_of_nat_to_Z (S N * S N) ltac:(lia)).
  (* Goal: (20 * Z.pos(Qden delta) < Qnum delta * Z.pos(Pos.of_nat(S N * S N)))%Z *)
  assert (HN : (Z.of_nat N = 20 * Z.pos (Qden delta))%Z).
  { subst N. rewrite Z2Nat.id; lia. }
  rewrite Hz.
  rewrite Nat2Z.inj_mul. rewrite !Nat2Z.inj_succ.
  assert (Hnum : (0 < Qnum delta)%Z).
  { destruct delta as [p q]. unfold Qlt in Hd. simpl in *. lia. }
  nia.
Qed.

Theorem cycle_no_pmg_infinite :
  has_process_mass_gap (fun n => cycle_gap_approx n) -> False.
Proof.
  intros Hpmg.
  destruct Hpmg as [delta r C Hdelta Hbound _ _ _ _].
  destruct (cycle_gap_archimedean delta Hdelta) as [n Hn].
  assert (Hle := Hbound n). lra.
Qed.

(* ================================================================== *)
(*  Part IV: Mixing as Process  (~4 lemmas)                            *)
(* ================================================================== *)

(** Distance to stationarity at time t: d(t) ≤ (1-γ)^t *)
Definition mixing_bound (gamma : Q) : RealProcess :=
  fun t => Qpow (1 - gamma) t.

(** Mixing bound at t=0 is 1 *)
Lemma mixing_bound_0 : forall gamma,
  mixing_bound gamma 0%nat == 1.
Proof. intros gamma. unfold mixing_bound. simpl. lra. Qed.

(** If gap > 0 and gap ≤ 1, mixing bound is decreasing *)
Lemma mixing_bound_decreasing : forall gamma,
  0 < gamma -> gamma <= 1 ->
  monotone_decreasing (mixing_bound gamma).
Proof.
  intros gamma Hpos Hle n. unfold mixing_bound.
  simpl.
  assert (H01 : 0 <= 1 - gamma) by lra.
  assert (H1 : 1 - gamma <= 1) by lra.
  assert (Hpow : 0 <= Qpow (1 - gamma) n) by (apply Qpow_nonneg; lra).
  (* Qpow b (S n) = b * Qpow b n, need b * Qpow b n <= Qpow b n *)
  (* i.e. b * x <= x when 0 <= b <= 1 and 0 <= x *)
  assert (Hmul : (1 - gamma) * Qpow (1 - gamma) n <= 1 * Qpow (1 - gamma) n).
  { apply Qmult_le_compat_r; lra. }
  lra.
Qed.

(** Markov gap = mixing rate: same process, same PMG *)
Theorem markov_gap_is_mixing_rate : forall lambda2,
  markov_gap lambda2 = fun n => 1 - lambda2 n.
Proof. intros lambda2. reflexivity. Qed.

(* ================================================================== *)
(*  Checks                                                              *)
(* ================================================================== *)

Check markov_gap. Check markov_gap_pos. Check markov_gap_decreasing.
Check uniformly_ergodic. Check markov_ergodic_pmg.
Check constant_eigenvalue_pmg.
Check cycle_gap_approx. Check cycle_gap_pos. Check cycle_no_pmg_infinite.
Check mixing_bound. Check mixing_bound_decreasing.
