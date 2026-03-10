(**
  CoulombFull3D.v — Full 3D Hydrogen with Angular Momentum
  =========================================================

  File 7 of the Experimental Verification module (Phase 3).

  Extends CoulombTower.v from radial-only (1/n) to full 3D with angular
  momentum. Product basis |n_r, l⟩ where n_r = radial quantum number,
  l = angular momentum quantum number.

  Hamiltonian = H_radial + H_centrifugal(l), all diagonal.
  Centrifugal barrier: l(l+1)/(2r²) lifts degeneracy at finite N.

  KEY RESULTS:
  - Partial degeneracy: same n_r, different l → same limit (centrifugal vanishes)
  - No accidental degeneracy: same principal n, different n_r → different limits
  - Ground state is minimum across all (n_r, l)
  - Convergence: each (n_r, l) converges to hydrogen_limit(n_r)
  - Splitting rate: O(1/K) from centrifugal

  HONEST LIMITATION: 1/n² spectrum and accidental degeneracy require
  off-diagonal Coulomb coupling, not present in diagonal approximation.

  STATUS: target ~48 Qed, 0 Admitted
  AXIOMS: classic (via MonotoneConvergence)
*)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.PeanoNat.

Open Scope Q_scope.

From ToS Require Import CauchyReal.
From ToS Require Import SeriesConvergence.
From ToS Require Import MonotoneConvergence.
From ToS Require Import experimental.CoulombTower.

(* ========================================================================= *)
(*              DEFINITIONS                                                   *)
(* ========================================================================= *)

(** Centrifugal contribution (K-scaled): l(l+1) / (2 * (S n_r)² * K)
    where K = inject_Z(Z.of_nat(S N)).
    This is the centrifugal energy multiplied by K (same scaling as scaled_energy). *)
Definition centrifugal_scaled (N n_r l : nat) : Q :=
  inject_Z (Z.of_nat (l * (S l))) /
  (2 * Qpow (inject_Z (Z.of_nat (S n_r))) 2 * inject_Z (Z.of_nat (S N))).

(** Full 3D scaled energy = radial (from CoulombTower) + centrifugal *)
Definition scaled_energy_3d (N n_r l : nat) : Q :=
  scaled_energy N n_r + centrifugal_scaled N n_r l.

(** Hydrogen limit in 3D: centrifugal vanishes, same as 1D *)
Definition hydrogen_limit_3d (n_r l : nat) : Q := hydrogen_limit n_r.

(** Principal quantum number n = n_r + l + 1 *)
Definition principal_n (n_r l : nat) : nat := n_r + l + 1.

(** Degeneracy process: energy splitting between angular momentum l and l=0
    at the same radial quantum number n_r *)
Definition degeneracy_process (n_r l : nat) : nat -> Q :=
  fun N => scaled_energy_3d N n_r l - scaled_energy_3d N n_r 0.

(** Nat partial sum for degeneracy counting: Σ_{k=0}^{N} f(k) *)
Fixpoint sum_nat (f : nat -> nat) (N : nat) : nat :=
  match N with
  | O => f O
  | S n' => sum_nat f n' + f (S n')
  end.

(* ========================================================================= *)
(*              PART I: CENTRIFUGAL PROPERTIES                               *)
(* ========================================================================= *)

(** For l=0: centrifugal = 0 (s-wave, recovers CoulombTower) *)
Lemma centrifugal_scaled_l0 : forall N n_r,
  centrifugal_scaled N n_r 0 == 0.
Proof.
  intros N n_r. unfold centrifugal_scaled.
  simpl (0 * 1)%nat. change (inject_Z (Z.of_nat 0)) with 0.
  unfold Qdiv. rewrite Qmult_0_l. reflexivity.
Qed.

(** Centrifugal is non-negative for all l *)
Lemma centrifugal_scaled_nonneg : forall N n_r l,
  0 <= centrifugal_scaled N n_r l.
Proof.
  intros N n_r l. unfold centrifugal_scaled.
  unfold Qdiv, Qle, Qmult, Qinv. simpl.
  change (Qpow (inject_Z (Z.of_nat (S n_r))) 2) with
    (inject_Z (Z.of_nat (S n_r)) * (inject_Z (Z.of_nat (S n_r)) * 1)).
  unfold Qmult, Qinv. simpl.
  assert (Hnum : (0 <= Z.of_nat (l * S l))%Z) by lia.
  assert (Hn : (0 < Z.of_nat (S n_r))%Z) by lia.
  assert (HN : (0 < Z.of_nat (S N))%Z) by lia.
  destruct (Z.of_nat (S n_r)) eqn:Esn; [lia| |lia].
  destruct (Z.of_nat (S N)) eqn:EsN; [lia| |lia].
  simpl. nia.
Qed.

(** For l >= 1: centrifugal is strictly positive *)
Lemma centrifugal_scaled_positive : forall N n_r l,
  (1 <= l)%nat -> 0 < centrifugal_scaled N n_r l.
Proof.
  intros N n_r l Hl. unfold centrifugal_scaled.
  assert (Hnum : (2 <= l * S l)%nat).
  { destruct l; [lia|]. simpl. lia. }
  assert (HnumZ : (2 <= Z.of_nat (l * S l))%Z) by lia.
  assert (Hden1 : 0 < inject_Z (Z.of_nat (S n_r))) by apply inject_Z_S_pos.
  assert (Hden2 : 0 < inject_Z (Z.of_nat (S N))) by apply inject_Z_S_pos.
  destruct (inject_Z (Z.of_nat (S n_r))) as [sn sd] eqn:Hsn.
  destruct (inject_Z (Z.of_nat (S N))) as [sN sNd] eqn:HsN.
  unfold Qlt in Hden1, Hden2. simpl in Hden1, Hden2.
  unfold Qdiv, Qlt, Qmult, Qinv. simpl.
  change (Qpow (sn # sd) 2) with ((sn # sd) * ((sn # sd) * 1)).
  unfold Qmult. simpl.
  destruct sn as [|sp|]; [lia| |lia].
  destruct sN as [|sNp|]; [lia| |lia].
  simpl. nia.
Qed.

(** Concrete: centrifugal_scaled 3 0 1 *)
Lemma centrifugal_at_l1 : centrifugal_scaled 3 0 1 == (1#4).
Proof. vm_compute. reflexivity. Qed.

(** Concrete: centrifugal_scaled 3 0 2 *)
Lemma centrifugal_at_l2 : centrifugal_scaled 3 0 2 == (3#4).
Proof. vm_compute. reflexivity. Qed.

(** For l=0, 3D energy equals 1D energy from CoulombTower *)
Lemma scaled_energy_3d_l0 : forall N n_r,
  scaled_energy_3d N n_r 0 == scaled_energy N n_r.
Proof.
  intros N n_r. unfold scaled_energy_3d.
  rewrite centrifugal_scaled_l0. ring.
Qed.

(** Degeneracy counting: Σ_{l=0}^{0} (2l+1) = 1 *)
Lemma degeneracy_sum_1 : sum_nat (fun l => (2 * l + 1)%nat) 0 = 1%nat.
Proof. vm_compute. reflexivity. Qed.

(** Degeneracy counting: Σ_{l=0}^{1} (2l+1) = 4 = 2² *)
Lemma degeneracy_sum_2 : sum_nat (fun l => (2 * l + 1)%nat) 1 = 4%nat.
Proof. vm_compute. reflexivity. Qed.

(** Degeneracy counting: Σ_{l=0}^{2} (2l+1) = 9 = 3² *)
Lemma degeneracy_sum_3 : sum_nat (fun l => (2 * l + 1)%nat) 2 = 9%nat.
Proof. vm_compute. reflexivity. Qed.

(** General: Σ_{l=0}^{n} (2l+1) = (n+1)² *)
Lemma degeneracy_sum_general : forall n : nat,
  sum_nat (fun l => (2 * l + 1)%nat) n = ((S n) * (S n))%nat.
Proof.
  induction n as [|n' IH].
  - reflexivity.
  - change (sum_nat (fun l : nat => (2 * l + 1)%nat) (S n'))
      with ((sum_nat (fun l : nat => (2 * l + 1)%nat) n' + (2 * S n' + 1)))%nat.
    rewrite IH. lia.
Qed.

(* ========================================================================= *)
(*              PART II: CONCRETE VALUES + BASIC PROPERTIES                  *)
(* ========================================================================= *)

(** Concrete 3D energy values *)
Lemma energy_3d_3_0_0 : scaled_energy_3d 3 0 0 == -(7#32).
Proof. vm_compute. reflexivity. Qed.

Lemma energy_3d_3_0_1 : scaled_energy_3d 3 0 1 == (1#32).
Proof. vm_compute. reflexivity. Qed.

Lemma energy_3d_3_1_0 : scaled_energy_3d 3 1 0 == -(3#32).
Proof. vm_compute. reflexivity. Qed.

Lemma energy_3d_9_0_1 : scaled_energy_3d 9 0 1 == -(11#80).
Proof. vm_compute. reflexivity. Qed.

(** 3D hydrogen limit ground state *)
Lemma hydrogen_limit_3d_ground : hydrogen_limit_3d 0 0 == -(1#4).
Proof. unfold hydrogen_limit_3d. vm_compute. reflexivity. Qed.

(** 3D limit equals 1D limit (l-independent) *)
Lemma hydrogen_limit_3d_eq_1d : forall n_r l,
  hydrogen_limit_3d n_r l == hydrogen_limit n_r.
Proof. intros. unfold hydrogen_limit_3d. reflexivity. Qed.

(** ★ PARTIAL DEGENERACY: same n_r, different l → same limit ★ *)
Theorem partial_degeneracy : forall n_r l1 l2,
  hydrogen_limit_3d n_r l1 == hydrogen_limit_3d n_r l2.
Proof. intros. unfold hydrogen_limit_3d. reflexivity. Qed.

(** Different n_r → different limits (no false degeneracy) *)
Theorem no_false_degeneracy : forall n_r1 n_r2,
  n_r1 <> n_r2 ->
  ~ (hydrogen_limit_3d n_r1 0 == hydrogen_limit_3d n_r2 0).
Proof.
  intros n_r1 n_r2 Hneq Heq.
  unfold hydrogen_limit_3d, hydrogen_limit in Heq.
  unfold Qeq in Heq. simpl in Heq. lia.
Qed.

(** All 3D limits are negative *)
Lemma limit_3d_negative : forall n_r l,
  hydrogen_limit_3d n_r l < 0.
Proof.
  intros. unfold hydrogen_limit_3d. apply limit_negative.
Qed.

(** S-wave energy ratios: E_{n_r}/E_0 = 1/(n_r+1) *)
Theorem s_wave_ratios : forall n_r,
  hydrogen_limit_3d n_r 0 / hydrogen_limit_3d 0 0 ==
  1 / inject_Z (Z.of_nat (S n_r)).
Proof.
  intros. unfold hydrogen_limit_3d. apply limit_ratio.
Qed.

(* ========================================================================= *)
(*              PART III: ENERGY ORDERING                                     *)
(* ========================================================================= *)

(** Adding angular momentum RAISES energy (centrifugal barrier) *)
Theorem angular_momentum_raises : forall N n_r l,
  (1 <= l)%nat ->
  scaled_energy_3d N n_r 0 < scaled_energy_3d N n_r l.
Proof.
  intros N n_r l Hl. unfold scaled_energy_3d.
  rewrite centrifugal_scaled_l0.
  assert (Hpos := centrifugal_scaled_positive N n_r l Hl).
  lra.
Qed.

(** S-wave radial ordering: higher n_r → higher energy (for l=0) *)
Theorem energy_ordering_s_wave : forall N n_r,
  scaled_energy_3d N n_r 0 < scaled_energy_3d N (S n_r) 0.
Proof.
  intros N n_r. rewrite !scaled_energy_3d_l0.
  apply energy_increases_with_n.
Qed.

(** Ground state (n_r=0, l=0) is the minimum energy *)
Theorem ground_state_minimum : forall N n_r l,
  scaled_energy_3d N 0 0 <= scaled_energy_3d N n_r l.
Proof.
  intros N n_r l.
  (* Step 1: ground(0,0) ≤ energy(n_r, 0) by radial ordering *)
  assert (Hrad : scaled_energy_3d N 0 0 <= scaled_energy_3d N n_r 0).
  { induction n_r as [|n_r' IH].
    - lra.
    - apply Qle_trans with (scaled_energy_3d N n_r' 0).
      + exact IH.
      + apply Qlt_le_weak. apply energy_ordering_s_wave. }
  (* Step 2: energy(n_r, 0) ≤ energy(n_r, l) by centrifugal ≥ 0 *)
  apply Qle_trans with (scaled_energy_3d N n_r 0).
  - exact Hrad.
  - unfold scaled_energy_3d. rewrite centrifugal_scaled_l0.
    assert (Hcent := centrifugal_scaled_nonneg N n_r l). lra.
Qed.

(** Ground state is negative in 3D *)
Lemma ground_negative_3d : forall N,
  scaled_energy_3d N 0 0 < 0.
Proof.
  intros N. rewrite scaled_energy_3d_l0. apply ground_negative.
Qed.

(** P4 finiteness: every state has a definite energy *)
Lemma p4_finiteness_3d : forall N n_r l,
  exists q : Q, scaled_energy_3d N n_r l == q.
Proof.
  intros. exists (scaled_energy_3d N n_r l). reflexivity.
Qed.

(** At finite N, different l gives different energy (centrifugal breaks degeneracy) *)
Theorem finite_splitting : forall N n_r l,
  (1 <= l)%nat ->
  scaled_energy_3d N n_r 0 <> scaled_energy_3d N n_r l.
Proof.
  intros N n_r l Hl Heq.
  assert (Hlt := angular_momentum_raises N n_r l Hl).
  rewrite Heq in Hlt. apply (Qlt_irrefl _ Hlt).
Qed.

(** Principal quantum number examples *)
Lemma principal_n_examples :
  principal_n 0 0 = 1%nat /\ principal_n 1 0 = 2%nat /\ principal_n 0 1 = 2%nat.
Proof.
  unfold principal_n. repeat split; lia.
Qed.

(** Energy at principal number maps to hydrogen_limit *)
Lemma energy_at_principal : forall n,
  (1 <= n)%nat ->
  hydrogen_limit_3d (n - 1) 0 == hydrogen_limit (n - 1).
Proof.
  intros. unfold hydrogen_limit_3d. reflexivity.
Qed.

(* ========================================================================= *)
(*              PART IV: CONVERGENCE + DEGENERACY PROCESS                    *)
(* ========================================================================= *)

(** Deviation formula for 3D: deviation = 1/(8K) + centrifugal *)
Theorem deviation_3d_formula : forall N n_r l,
  scaled_energy_3d N n_r l - hydrogen_limit_3d n_r l ==
  1 / (8 * inject_Z (Z.of_nat (S N))) + centrifugal_scaled N n_r l.
Proof.
  intros N n_r l.
  unfold scaled_energy_3d, hydrogen_limit_3d.
  assert (Hdev := deviation_formula N n_r).
  setoid_replace (scaled_energy N n_r + centrifugal_scaled N n_r l -
    hydrogen_limit n_r)
    with ((scaled_energy N n_r - hydrogen_limit n_r) +
      centrifugal_scaled N n_r l) by ring.
  rewrite Hdev. reflexivity.
Qed.

(** Deviation is always positive *)
Lemma deviation_3d_positive : forall N n_r l,
  0 < scaled_energy_3d N n_r l - hydrogen_limit_3d n_r l.
Proof.
  intros N n_r l.
  rewrite deviation_3d_formula.
  assert (H1 : 0 < 1 / (8 * inject_Z (Z.of_nat (S N)))).
  { assert (HK := inject_Z_S_pos N).
    unfold Qdiv, Qlt in *. simpl in *. nia. }
  assert (H2 := centrifugal_scaled_nonneg N n_r l).
  lra.
Qed.

(** Degeneracy process equals centrifugal contribution *)
Theorem degeneracy_process_formula : forall n_r l N,
  degeneracy_process n_r l N == centrifugal_scaled N n_r l.
Proof.
  intros. unfold degeneracy_process, scaled_energy_3d.
  rewrite centrifugal_scaled_l0. ring.
Qed.

(** Degeneracy process is zero for l=0 *)
Lemma degeneracy_process_l0 : forall n_r N,
  degeneracy_process n_r 0 N == 0.
Proof.
  intros. rewrite degeneracy_process_formula. apply centrifugal_scaled_l0.
Qed.

(** Degeneracy process is positive for l >= 1 *)
Lemma degeneracy_process_positive : forall n_r l N,
  (1 <= l)%nat -> 0 < degeneracy_process n_r l N.
Proof.
  intros. rewrite degeneracy_process_formula.
  apply centrifugal_scaled_positive. exact H.
Qed.

(** Helper: upper bound on centrifugal: centrifugal_scaled N n_r l ≤ l(l+1)/(2K) *)
Lemma centrifugal_upper_bound : forall N n_r l,
  centrifugal_scaled N n_r l <=
  inject_Z (Z.of_nat (l * S l)) / (2 * inject_Z (Z.of_nat (S N))).
Proof.
  intros N n_r l.
  unfold centrifugal_scaled.
  assert (HK := inject_Z_S_pos N).
  assert (Hn := inject_Z_S_pos n_r).
  assert (Hnum : (0 <= Z.of_nat (l * S l))%Z) by lia.
  (* Qpow(S n_r, 2) >= 1, so denom is larger, fraction is smaller *)
  unfold Qdiv, Qle, Qmult, Qinv. simpl.
  change (Qpow (inject_Z (Z.of_nat (S n_r))) 2) with
    (inject_Z (Z.of_nat (S n_r)) * (inject_Z (Z.of_nat (S n_r)) * 1)).
  unfold Qmult, Qinv. simpl. nia.
Qed.

(** Helper: bound/K < eps when bound/eps < K (for positive bound, eps, K) *)
Lemma Q_bound_over_K (bound eps K : Q) :
  0 < bound -> 0 < eps -> 0 < K ->
  bound / eps < K -> bound / K < eps.
Proof.
  intros Hb He HK Hlt.
  destruct bound as [bn bd], eps as [en ed], K as [kn kd].
  unfold Qlt in Hb, He, HK. simpl in Hb, He, HK.
  destruct bn as [|bp|]; [lia| |lia].
  destruct en as [|ep|]; [lia| |lia].
  destruct kn as [|kp|]; [lia| |lia].
  unfold Qdiv, Qlt, Qmult, Qinv in *. simpl in *.
  nia.
Qed.

(** ★ CONVERGENCE for each (n_r, l) ★ *)
Theorem convergence_3d : forall n_r l (eps : Q),
  0 < eps ->
  exists M : nat, forall N, (M <= N)%nat ->
    Qabs (scaled_energy_3d N n_r l - hydrogen_limit_3d n_r l) < eps.
Proof.
  intros n_r l eps Heps.
  (* Deviation = 1/(8K) + cent(N,n_r,l) ≤ 1/(8K) + l(l+1)/(2K) *)
  (* = (1/8 + l(l+1)/2) / K = C / K where C = (1 + 4*l(l+1))/8 *)
  (* Actually, easier: both terms ≤ some_bound / K *)
  (* Use bound: deviation ≤ (1 + inject_Z(l*(S l))) / K *)
  set (bound := 1 + inject_Z (Z.of_nat (l * S l))).
  assert (Hbound_pos : 0 < bound).
  { unfold bound.
    assert (Hnn : 0 <= inject_Z (Z.of_nat (l * S l))).
    { unfold Qle, inject_Z. simpl. lia. }
    lra. }
  assert (H01 : (0 < 1)) by lra.
  destruct (nat_archimedean (bound / eps) 1 H01) as [K0 HK0].
  exists K0. intros N HN.
  assert (Hdev := deviation_3d_positive N n_r l).
  pose proof (Qabs_pos _ (Qlt_le_weak _ _ Hdev)) as Habs_eq.
  setoid_rewrite Habs_eq.
  rewrite deviation_3d_formula.
  assert (HK := inject_Z_S_pos N).
  set (K := inject_Z (Z.of_nat (S N))) in *.
  (* 1/(8K) ≤ 1/K since K ≥ 1 *)
  assert (H8K : 1 / (8 * K) <= 1 / K).
  { unfold Qdiv, Qle, Qlt in *. simpl in *. nia. }
  assert (Hcent_bound := centrifugal_upper_bound N n_r l).
  fold K in Hcent_bound.
  assert (Hcent_bound2 : centrifugal_scaled N n_r l <=
    inject_Z (Z.of_nat (l * S l)) / (2 * K)).
  { exact Hcent_bound. }
  assert (Hcent_bound3 : inject_Z (Z.of_nat (l * S l)) / (2 * K) <=
    inject_Z (Z.of_nat (l * S l)) / K).
  { unfold Qdiv, Qle. simpl. nia. }
  assert (Htotal : 1 / (8 * K) + centrifugal_scaled N n_r l <=
    1 / K + inject_Z (Z.of_nat (l * S l)) / K).
  { lra. }
  assert (Hsum : 1 / K + inject_Z (Z.of_nat (l * S l)) / K == bound / K).
  { unfold bound. field. apply inject_Z_S_neq_0. }
  assert (Htotal2 : 1 / (8 * K) + centrifugal_scaled N n_r l <= bound / K).
  { apply Qle_trans with (1 / K + inject_Z (Z.of_nat (l * S l)) / K).
    - exact Htotal.
    - rewrite Hsum. apply Qle_refl. }
  apply Qle_lt_trans with (bound / K).
  { exact Htotal2. }
  (* Now need bound/K < eps, i.e., bound/eps < K *)
  assert (Htrans : bound / eps < K).
  { apply Qlt_le_trans with (inject_Z (Z.of_nat K0)).
    - lra.
    - unfold Qle. simpl. lia. }
  exact (Q_bound_over_K bound eps K Hbound_pos Heps HK Htrans).
Qed.

(** Splitting vanishes: degeneracy is restored in the limit *)
Theorem splitting_vanishes : forall n_r l (eps : Q),
  0 < eps ->
  exists M : nat, forall N, (M <= N)%nat ->
    Qabs (degeneracy_process n_r l N) < eps.
Proof.
  intros n_r l eps Heps.
  destruct l as [|l'].
  - (* l = 0: process is identically 0 *)
    exists 0%nat. intros N _.
    assert (H0 := degeneracy_process_l0 n_r N).
    assert (Habs : Qabs (degeneracy_process n_r 0 N) == 0).
    { rewrite H0. apply Qabs_pos. lra. }
    rewrite Habs. exact Heps.
  - (* l = S l': use centrifugal bound *)
    set (l := S l').
    set (bound := inject_Z (Z.of_nat (l * S l))).
    assert (Hbound_pos : 0 < bound).
    { unfold bound, l. assert (H : (2 <= S l' * S (S l'))%nat) by lia.
      unfold Qlt. simpl. lia. }
    destruct (nat_archimedean (bound / (2 * eps)) 1 ltac:(lra)) as [K0 HK0].
    exists K0. intros N HN.
    assert (Hpos := degeneracy_process_positive n_r l N ltac:(unfold l; lia)).
    pose proof (Qabs_pos _ (Qlt_le_weak _ _ Hpos)) as Habs_eq.
    setoid_rewrite Habs_eq.
    rewrite degeneracy_process_formula.
    assert (HK := inject_Z_S_pos N).
    set (K := inject_Z (Z.of_nat (S N))) in *.
    assert (Hcent_bound := centrifugal_upper_bound N n_r l).
    fold K in Hcent_bound.
    apply Qle_lt_trans with (bound / (2 * K)).
    { exact Hcent_bound. }
    (* Need: bound/(2*K) < eps, use Q_bound_over_K with bound'=bound, K'=2*K *)
    assert (H2Kpos : 0 < 2 * K) by lra.
    apply (Q_bound_over_K bound eps (2 * K) Hbound_pos Heps H2Kpos).
    (* Need: bound/eps < 2*K *)
    assert (Htrans : bound / (2 * eps) < K).
    { apply Qlt_le_trans with (inject_Z (Z.of_nat K0)).
      - lra.
      - unfold Qle. simpl. lia. }
    setoid_replace (bound / eps) with (2 * (bound / (2 * eps))) by (field; lra).
    lra.
Qed.

(** Splitting rate: O(l(l+1)/K) *)
Theorem splitting_rate : forall n_r l N,
  Qabs (degeneracy_process n_r l N) <=
  inject_Z (Z.of_nat (l * S l)) / (2 * inject_Z (Z.of_nat (S N))).
Proof.
  intros n_r l N.
  destruct l as [|l'].
  - (* l = 0: both sides are 0 *)
    rewrite degeneracy_process_l0.
    rewrite Qabs_pos by lra.
    simpl (0 * 1)%nat. change (inject_Z (Z.of_nat 0)) with 0.
    unfold Qdiv. rewrite Qmult_0_l. lra.
  - (* l >= 1: use positivity + upper bound *)
    set (l := S l').
    assert (Hpos := degeneracy_process_positive n_r l N ltac:(unfold l; lia)).
    rewrite Qabs_pos by lra.
    rewrite degeneracy_process_formula.
    apply centrifugal_upper_bound.
Qed.

(** Degeneracy process is Cauchy *)
Theorem degeneracy_is_cauchy : forall n_r l,
  is_cauchy (degeneracy_process n_r l).
Proof.
  intros n_r l.
  unfold is_cauchy. intros eps Heps.
  assert (Heps2 : 0 < eps * (1#2)).
  { unfold Qlt, Qmult. simpl.
    unfold Qlt in Heps. simpl in Heps. lia. }
  destruct (splitting_vanishes n_r l (eps * (1#2)) Heps2) as [M HM].
  exists M. intros m n Hm Hn.
  assert (H1 := HM m Hm).
  assert (H2 := HM n Hn).
  set (fm := degeneracy_process n_r l m) in *.
  set (fn := degeneracy_process n_r l n) in *.
  (* |fm - fn| ≤ |fm| + |fn| by triangle inequality *)
  assert (Htri : Qabs (fm - fn) <= Qabs fm + Qabs fn).
  { setoid_replace (fm - fn) with (fm + (-fn)) by ring.
    apply Qle_trans with (Qabs fm + Qabs (-fn)).
    - apply Qabs_triangle.
    - assert (Hopp : Qabs (-fn) == Qabs fn) by apply Qabs_opp.
      lra. }
  assert (Heps_eq : eps * (1 # 2) + eps * (1 # 2) == eps).
  { ring. }
  lra.
Qed.

(** Degeneracy limit is zero (convenience alias) *)
Theorem degeneracy_limit_zero : forall n_r l (eps : Q),
  0 < eps ->
  exists M : nat, forall N, (M <= N)%nat ->
    Qabs (degeneracy_process n_r l N) < eps.
Proof. exact splitting_vanishes. Qed.

(** S-wave convergence reduces to CoulombTower *)
Theorem convergence_3d_s_wave : forall n_r (eps : Q),
  0 < eps ->
  exists M : nat, forall N, (M <= N)%nat ->
    Qabs (scaled_energy_3d N n_r 0 - hydrogen_limit n_r) < eps.
Proof.
  intros n_r eps Heps.
  destruct (convergence_general n_r eps Heps) as [M HM].
  exists M. intros N HN.
  assert (H3d : scaled_energy_3d N n_r 0 == scaled_energy N n_r).
  { apply scaled_energy_3d_l0. }
  setoid_rewrite H3d. exact (HM N HN).
Qed.

(** Ionization in 3D *)
Theorem ionization_3d : forall l (eps : Q),
  0 < eps ->
  exists n0 : nat, forall n_r, (n0 <= n_r)%nat ->
    Qabs (hydrogen_limit_3d n_r l) < eps.
Proof.
  intros l eps Heps.
  destruct (ionization eps Heps) as [n0 Hn0].
  exists n0. intros n_r Hn.
  unfold hydrogen_limit_3d. exact (Hn0 n_r Hn).
Qed.

(* ========================================================================= *)
(*              PART V: SUMMARY THEOREMS                                     *)
(* ========================================================================= *)

(** Summary of all 3D Coulomb results *)
Theorem coulomb_3d_summary :
  (* 1. P4: finite energy at every stage *)
  (forall N n_r l, exists q, scaled_energy_3d N n_r l == q) /\
  (* 2. Ground state is minimum *)
  (forall N n_r l, scaled_energy_3d N 0 0 <= scaled_energy_3d N n_r l) /\
  (* 3. Partial degeneracy: same n_r → same limit *)
  (forall n_r l1 l2, hydrogen_limit_3d n_r l1 == hydrogen_limit_3d n_r l2) /\
  (* 4. Splitting vanishes as N → ∞ *)
  (forall n_r l eps, 0 < eps -> exists M, forall N, (M <= N)%nat ->
    Qabs (degeneracy_process n_r l N) < eps).
Proof.
  refine (conj _ (conj _ (conj _ _))).
  - exact p4_finiteness_3d.
  - exact ground_state_minimum.
  - exact partial_degeneracy.
  - exact splitting_vanishes.
Qed.

(** Honest limitation: diagonal approximation breaks accidental degeneracy *)
Theorem coulomb_3d_honest_limitation :
  (* Our limit depends on n_r, not on principal n = n_r + l + 1 *)
  (* States with same principal n but different n_r have different limits *)
  ~ (hydrogen_limit_3d 1 0 == hydrogen_limit_3d 0 1) /\
  (* Textbook 1/n² requires off-diagonal Coulomb coupling *)
  (hydrogen_limit_3d 1 0 / hydrogen_limit_3d 0 0 == 1 / inject_Z 2).
Proof.
  split.
  - intro H. unfold hydrogen_limit_3d, hydrogen_limit in H.
    unfold Qeq in H. simpl in H. lia.
  - unfold hydrogen_limit_3d. apply limit_ratio.
Qed.

(** Principal energy ratio: E_n/E_1 = 1/n for s-wave *)
Theorem principal_energy_ratio : forall n,
  (1 <= n)%nat ->
  hydrogen_limit (n - 1) / hydrogen_limit 0 ==
  1 / inject_Z (Z.of_nat n).
Proof.
  intros n Hn.
  destruct n as [|n']; [lia|].
  simpl (S n' - 1)%nat. replace (n' - 0)%nat with n' by lia.
  apply limit_ratio.
Qed.

(** No accidental degeneracy: 2S ≠ 2P in our model *)
Theorem no_accidental_degeneracy :
  ~ (hydrogen_limit_3d 1 0 == hydrogen_limit_3d 0 1).
Proof.
  intro H. unfold hydrogen_limit_3d, hydrogen_limit in H.
  unfold Qeq in H. simpl in H. lia.
Qed.

(** Partial vs full degeneracy *)
Theorem partial_vs_full_degeneracy :
  (* Partial: same n_r, any l → same limit *)
  (forall n_r l1 l2, hydrogen_limit_3d n_r l1 == hydrogen_limit_3d n_r l2) /\
  (* No accidental: same principal n=2, different n_r → different limits *)
  ~ (hydrogen_limit_3d 1 0 == hydrogen_limit_3d 0 1).
Proof.
  split.
  - exact partial_degeneracy.
  - exact no_accidental_degeneracy.
Qed.

(** Complete 3D Coulomb theorem *)
Theorem coulomb_3d_complete :
  (* Convergence *)
  (forall n_r l eps, 0 < eps -> exists M, forall N, (M <= N)%nat ->
    Qabs (scaled_energy_3d N n_r l - hydrogen_limit_3d n_r l) < eps) /\
  (* Partial degeneracy *)
  (forall n_r l1 l2, hydrogen_limit_3d n_r l1 == hydrogen_limit_3d n_r l2) /\
  (* Ground state minimum *)
  (forall N n_r l, scaled_energy_3d N 0 0 <= scaled_energy_3d N n_r l) /\
  (* Centrifugal raises energy *)
  (forall N n_r l, (1 <= l)%nat ->
    scaled_energy_3d N n_r 0 < scaled_energy_3d N n_r l) /\
  (* Ionization *)
  (forall l eps, 0 < eps -> exists n0, forall n_r, (n0 <= n_r)%nat ->
    Qabs (hydrogen_limit_3d n_r l) < eps).
Proof.
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  - exact convergence_3d.
  - exact partial_degeneracy.
  - exact ground_state_minimum.
  - exact angular_momentum_raises.
  - exact ionization_3d.
Qed.

(** Degeneracy as a process: Cauchy, limit 0, rate O(1/K) *)
Theorem process_view_degeneracy :
  (* Cauchy *)
  (forall n_r l, is_cauchy (degeneracy_process n_r l)) /\
  (* Limit zero *)
  (forall n_r l eps, 0 < eps -> exists M, forall N, (M <= N)%nat ->
    Qabs (degeneracy_process n_r l N) < eps) /\
  (* Rate bound *)
  (forall n_r l N, Qabs (degeneracy_process n_r l N) <=
    inject_Z (Z.of_nat (l * S l)) / (2 * inject_Z (Z.of_nat (S N)))).
Proof.
  refine (conj _ (conj _ _)).
  - exact degeneracy_is_cauchy.
  - exact degeneracy_limit_zero.
  - exact splitting_rate.
Qed.

(** ★ THE MAIN THEOREM ★ *)
Theorem coulomb_3d_main_theorem :
  (* 1. P4: finite energy at every stage *)
  (forall N n_r l, exists q, scaled_energy_3d N n_r l == q) /\
  (* 2. Convergence to hydrogen limit *)
  (forall n_r l eps, 0 < eps -> exists M, forall N, (M <= N)%nat ->
    Qabs (scaled_energy_3d N n_r l - hydrogen_limit_3d n_r l) < eps) /\
  (* 3. Partial degeneracy *)
  (forall n_r l1 l2, hydrogen_limit_3d n_r l1 == hydrogen_limit_3d n_r l2) /\
  (* 4. No accidental degeneracy *)
  (~ (hydrogen_limit_3d 1 0 == hydrogen_limit_3d 0 1)) /\
  (* 5. Ground state minimum + negative *)
  (forall N n_r l, scaled_energy_3d N 0 0 <= scaled_energy_3d N n_r l) /\
  (forall N, scaled_energy_3d N 0 0 < 0) /\
  (* 6. Splitting vanishes *)
  (forall n_r l eps, 0 < eps -> exists M, forall N, (M <= N)%nat ->
    Qabs (degeneracy_process n_r l N) < eps) /\
  (* 7. Ionization *)
  (forall l eps, 0 < eps -> exists n0, forall n_r, (n0 <= n_r)%nat ->
    Qabs (hydrogen_limit_3d n_r l) < eps).
Proof.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
  - exact p4_finiteness_3d.
  - exact convergence_3d.
  - exact partial_degeneracy.
  - exact no_accidental_degeneracy.
  - exact ground_state_minimum.
  - exact ground_negative_3d.
  - exact splitting_vanishes.
  - exact ionization_3d.
Qed.
