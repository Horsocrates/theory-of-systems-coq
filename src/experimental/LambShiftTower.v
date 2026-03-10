(**
  LambShiftTower.v — 2S-2P Splitting Analysis
  =============================================

  File 8 of the Experimental Verification module (Phase 3).

  Investigates the energy splitting between 2S (n_r=1, l=0) and 2P (n_r=0, l=1)
  states in our diagonal approximation.

  KEY RESULTS:
  - Exact formula: lamb_splitting N == (1#8) - 1/K where K = S(N)
  - Limit: splitting_limit = 1/8 (artifact of diagonal approximation)
  - Convergence: O(1/K) rate, monotonically increasing
  - Splitting crosses zero at N=7 (exact cancellation)
  - HONEST: This 1/8 splitting is O(1), NOT the physical Lamb shift O(alpha^5)
    Our diagonal approximation breaks accidental degeneracy entirely.
    Textbook hydrogen has E(2S)=E(2P) at principal n=2.

  STATUS: 42 Qed, 0 Admitted
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
From ToS Require Import experimental.CoulombFull3D.

(* ========================================================================= *)
(*              DEFINITIONS                                                   *)
(* ========================================================================= *)

(** 2S state: n_r=1, l=0 (first excited radial, s-wave) *)
Definition energy_2S (N : nat) : Q := scaled_energy_3d N 1 0.

(** 2P state: n_r=0, l=1 (ground radial, p-wave) *)
Definition energy_2P (N : nat) : Q := scaled_energy_3d N 0 1.

(** 2S-2P energy splitting *)
Definition lamb_splitting (N : nat) : Q := energy_2S N - energy_2P N.

(** Limit of the splitting process *)
Definition splitting_limit : Q := hydrogen_limit_3d 1 0 - hydrogen_limit_3d 0 1.

(** Off-diagonal coupling placeholder (zero in diagonal approximation) *)
Definition off_diagonal_coupling (N n1 l1 n2 l2 : nat) : Q := 0.

(* ========================================================================= *)
(*              PART I: CONCRETE VALUES + FORMULA                            *)
(* ========================================================================= *)

(** Concrete: energy_2S at N=3 *)
Lemma energy_2S_at_3 : energy_2S 3 == -(3#32).
Proof. vm_compute. reflexivity. Qed.

(** Concrete: energy_2P at N=3 *)
Lemma energy_2P_at_3 : energy_2P 3 == (1#32).
Proof. vm_compute. reflexivity. Qed.

(** Concrete: splitting at N=1 *)
Lemma splitting_at_1 : lamb_splitting 1 == -(3#8).
Proof. vm_compute. reflexivity. Qed.

(** Concrete: splitting at N=3 *)
Lemma splitting_at_3 : lamb_splitting 3 == -(1#8).
Proof. vm_compute. reflexivity. Qed.

(** Concrete: splitting at N=9 *)
Lemma splitting_at_9 : lamb_splitting 9 == (1#40).
Proof. vm_compute. reflexivity. Qed.

(** Concrete: splitting at N=19 *)
Lemma splitting_at_19 : lamb_splitting 19 == (3#40).
Proof. vm_compute. reflexivity. Qed.

(** Concrete: splitting at N=0 *)
Lemma splitting_at_0 : lamb_splitting 0 == -(7#8).
Proof. vm_compute. reflexivity. Qed.

(** P4: splitting is computable at every stage *)
Lemma splitting_computable : forall N, exists q : Q, lamb_splitting N == q.
Proof. intros N. exists (lamb_splitting N). reflexivity. Qed.

(** The splitting limit value *)
Lemma splitting_limit_value : splitting_limit == (1#8).
Proof. vm_compute. reflexivity. Qed.

(** Helper: centrifugal for (n_r=0, l=1) equals 1/K *)
Lemma centrifugal_01 : forall N,
  centrifugal_scaled N 0 1 == 1 / inject_Z (Z.of_nat (S N)).
Proof.
  intros N. unfold centrifugal_scaled.
  simpl (1 * S 1)%nat. simpl (S 0)%nat.
  change (inject_Z (Z.of_nat 2)) with 2.
  change (Qpow (inject_Z (Z.of_nat 1)) 2) with (1 * (1 * 1)).
  set (K := inject_Z (Z.of_nat (S N))).
  field. unfold K. apply inject_Z_S_neq_0.
Qed.

(** ★ THE KEY FORMULA: lamb_splitting N = 1/8 - 1/K ★ *)
Theorem splitting_formula : forall N,
  lamb_splitting N == (1#8) - 1 / inject_Z (Z.of_nat (S N)).
Proof.
  intros N.
  unfold lamb_splitting, energy_2S, energy_2P, scaled_energy_3d.
  rewrite centrifugal_scaled_l0.
  set (K := inject_Z (Z.of_nat (S N))).
  assert (Hdev1 := deviation_formula N 1). fold K in Hdev1.
  assert (Hdev0 := deviation_formula N 0). fold K in Hdev0.
  assert (Hcent := centrifugal_01 N). fold K in Hcent.
  assert (HL1 : hydrogen_limit 1 == -(1#8)) by (vm_compute; reflexivity).
  assert (HL0 : hydrogen_limit 0 == -(1#4)) by (vm_compute; reflexivity).
  (* Use deviation_formula to express scaled_energy in terms of hydrogen_limit *)
  setoid_replace (scaled_energy N 1) with (-(1#8) + 1 / (8 * K)).
  2:{ rewrite HL1 in Hdev1. lra. }
  setoid_replace (scaled_energy N 0) with (-(1#4) + 1 / (8 * K)).
  2:{ rewrite HL0 in Hdev0. lra. }
  rewrite Hcent.
  field. unfold K. apply inject_Z_S_neq_0.
Qed.

(** Deviation from limit: exactly -1/K *)
Theorem splitting_deviation : forall N,
  lamb_splitting N - splitting_limit == -(1) / inject_Z (Z.of_nat (S N)).
Proof.
  intros N.
  rewrite splitting_formula, splitting_limit_value.
  set (K := inject_Z (Z.of_nat (S N))).
  field. unfold K. apply inject_Z_S_neq_0.
Qed.

(* ========================================================================= *)
(*              PART II: CONVERGENCE PROPERTIES                              *)
(* ========================================================================= *)

(** ★ CONVERGENCE of splitting to limit ★ *)
Theorem splitting_converges : forall (eps : Q),
  0 < eps ->
  exists M : nat, forall N, (M <= N)%nat ->
    Qabs (lamb_splitting N - splitting_limit) < eps.
Proof.
  intros eps Heps.
  destruct (nat_archimedean (1 / eps) 1 ltac:(lra)) as [K0 HK0].
  exists K0. intros N HN.
  rewrite splitting_deviation.
  set (K := inject_Z (Z.of_nat (S N))).
  assert (HK : 0 < K) by (unfold K; apply inject_Z_S_pos).
  assert (HKneq : ~ K == 0) by (unfold K; apply inject_Z_S_neq_0).
  (* |-(1)/K| = 1/K *)
  setoid_replace (-(1) / K) with (-(1 / K)) by (field; exact HKneq).
  rewrite Qabs_opp.
  assert (H1K_pos : 0 < 1 / K).
  { unfold K. unfold Qdiv, Qlt, Qmult, Qinv. simpl. nia. }
  rewrite (Qabs_pos (1 / K)) by lra.
  (* Now: 1/K < eps. Use Q_bound_over_K with bound=1 *)
  apply (Q_bound_over_K 1 eps K ltac:(lra) Heps HK).
  (* Need: 1/eps < K *)
  apply Qlt_le_trans with (inject_Z (Z.of_nat K0)).
  - lra.
  - unfold K, Qle. simpl. lia.
Qed.

(** Splitting is a Cauchy sequence *)
Theorem splitting_is_cauchy : is_cauchy lamb_splitting.
Proof.
  unfold is_cauchy. intros eps Heps.
  assert (Heps2 : 0 < eps * (1#2)).
  { unfold Qlt, Qmult. simpl. unfold Qlt in Heps. simpl in Heps. lia. }
  destruct (splitting_converges (eps * (1#2)) Heps2) as [M HM].
  exists M. intros m n Hm Hn.
  assert (H1 := HM m Hm).
  assert (H2 := HM n Hn).
  set (fm := lamb_splitting m) in *.
  set (fn := lamb_splitting n) in *.
  set (L := splitting_limit) in *.
  (* |fm - fn| = |(fm - L) - (fn - L)| ≤ |fm - L| + |fn - L| *)
  assert (Htri : Qabs (fm - fn) <= Qabs (fm - L) + Qabs (fn - L)).
  { setoid_replace (fm - fn) with ((fm - L) - (fn - L)) by ring.
    setoid_replace ((fm - L) - (fn - L)) with ((fm - L) + (-(fn - L))) by ring.
    apply Qle_trans with (Qabs (fm - L) + Qabs (-(fn - L))).
    - apply Qabs_triangle.
    - assert (Hopp : Qabs (-(fn - L)) == Qabs (fn - L)) by apply Qabs_opp.
      lra. }
  assert (Heps_eq : eps * (1 # 2) + eps * (1 # 2) == eps) by ring.
  lra.
Qed.

(** Splitting limit is nonzero *)
Theorem splitting_nonzero : ~ (splitting_limit == 0).
Proof.
  rewrite splitting_limit_value. unfold Qeq. simpl. discriminate.
Qed.

(** Splitting is monotonically increasing *)
Theorem splitting_monotone : forall N, lamb_splitting N < lamb_splitting (S N).
Proof.
  intros N.
  assert (Hdev := splitting_deviation N).
  assert (HdevS := splitting_deviation (S N)).
  set (K := inject_Z (Z.of_nat (S N))) in *.
  set (K' := inject_Z (Z.of_nat (S (S N)))) in *.
  (* -(1)/K < -(1)/K' because K < K' and both positive *)
  assert (Hlt : -(1) / K < -(1) / K').
  { unfold K, K'.
    change (Z.of_nat (S N)) with (Z.pos (Pos.of_succ_nat N)).
    change (Z.of_nat (S (S N))) with (Z.pos (Pos.of_succ_nat (S N))).
    unfold inject_Z, Qdiv, Qlt, Qmult, Qopp, Qinv. simpl. lia. }
  lra.
Qed.

(** 2S energy converges to hydrogen_limit 1 *)
Theorem energy_2S_converges : forall (eps : Q),
  0 < eps ->
  exists M : nat, forall N, (M <= N)%nat ->
    Qabs (energy_2S N - hydrogen_limit 1) < eps.
Proof.
  intros eps Heps.
  destruct (convergence_3d 1 0 eps Heps) as [M HM].
  exists M. intros N HN.
  unfold energy_2S. unfold hydrogen_limit_3d in HM.
  exact (HM N HN).
Qed.

(** 2P energy converges to hydrogen_limit 0 *)
Theorem energy_2P_converges : forall (eps : Q),
  0 < eps ->
  exists M : nat, forall N, (M <= N)%nat ->
    Qabs (energy_2P N - hydrogen_limit 0) < eps.
Proof.
  intros eps Heps.
  destruct (convergence_3d 0 1 eps Heps) as [M HM].
  exists M. intros N HN.
  unfold energy_2P. unfold hydrogen_limit_3d in HM.
  exact (HM N HN).
Qed.

(** The two limits differ: -1/8 ≠ -1/4 *)
Theorem limits_differ : ~ (hydrogen_limit 1 == hydrogen_limit 0).
Proof.
  unfold hydrogen_limit, Qeq. simpl. discriminate.
Qed.

(** 2S energy is nonpositive (equals 0 at N=0, negative for N≥1) *)
Lemma energy_2S_nonpositive : forall N, energy_2S N <= 0.
Proof.
  intros N. unfold energy_2S. rewrite scaled_energy_3d_l0.
  assert (Hdev := deviation_formula N 1).
  assert (HL1 : hydrogen_limit 1 == -(1#8)) by (vm_compute; reflexivity).
  rewrite HL1 in Hdev.
  (* Convert everything to Z arithmetic *)
  unfold Qeq, Qle, Qdiv, Qmult, Qinv, Qplus, Qopp, Qminus in *.
  simpl in *. nia.
Qed.

(** Absolute deviation equals 1/K *)
Theorem splitting_deviation_abs : forall N,
  Qabs (lamb_splitting N - splitting_limit) == 1 / inject_Z (Z.of_nat (S N)).
Proof.
  intros N. rewrite splitting_deviation.
  set (K := inject_Z (Z.of_nat (S N))).
  assert (HK : 0 < K) by (unfold K; apply inject_Z_S_pos).
  assert (HKneq : ~ K == 0) by (unfold K; apply inject_Z_S_neq_0).
  setoid_replace (-(1) / K) with (-(1 / K)) by (field; exact HKneq).
  rewrite Qabs_opp. apply Qabs_pos.
  unfold K. unfold Qdiv, Qle, Qmult, Qinv. simpl. nia.
Qed.

(** Deviation is bounded by 1 *)
Theorem splitting_rate_bound : forall N,
  Qabs (lamb_splitting N - splitting_limit) <= 1.
Proof.
  intros N. rewrite splitting_deviation_abs.
  unfold Qdiv, Qle, Qmult, Qinv. simpl. nia.
Qed.

(* ========================================================================= *)
(*              PART III: HONEST ASSESSMENT                                  *)
(* ========================================================================= *)

(** Our splitting is O(1): |splitting_limit| > 1/16 *)
Lemma our_splitting_is_order_one : (1#16) < Qabs splitting_limit.
Proof.
  rewrite splitting_limit_value.
  unfold Qabs, Qlt. simpl. lia.
Qed.

(** Textbook hydrogen: 2S and 2P SHOULD be degenerate at n=2 *)
Theorem textbook_2S_2P_degenerate :
  (* Our model does NOT achieve textbook degeneracy: *)
  ~ (hydrogen_limit_3d 1 0 == hydrogen_limit_3d 0 1) /\
  (* Our limits differ: -1/8 vs -1/4 *)
  hydrogen_limit_3d 1 0 == -(1#8) /\
  hydrogen_limit_3d 0 1 == -(1#4).
Proof.
  refine (conj _ (conj _ _)).
  - exact no_accidental_degeneracy.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

(** Reuse: diagonal breaks accidental degeneracy *)
Theorem diagonal_breaks_accidental :
  ~ (hydrogen_limit_3d 1 0 == hydrogen_limit_3d 0 1).
Proof. exact no_accidental_degeneracy. Qed.

(** Our splitting is an ARTIFACT, not the physical Lamb shift *)
Theorem splitting_artifact_not_lamb_shift :
  (* Splitting limit = 1/8, an O(1) quantity *)
  splitting_limit == (1#8) /\
  (* It's nonzero *)
  ~ (splitting_limit == 0) /\
  (* Physical Lamb shift is O(alpha^5 ≈ 10^-6), ours is O(1) *)
  (1#16) < Qabs splitting_limit.
Proof.
  refine (conj _ (conj _ _)).
  - exact splitting_limit_value.
  - exact splitting_nonzero.
  - exact our_splitting_is_order_one.
Qed.

(** Off-diagonal coupling is zero in our model *)
Lemma off_diagonal_is_zero : forall N n1 l1 n2 l2,
  off_diagonal_coupling N n1 l1 n2 l2 == 0.
Proof. intros. unfold off_diagonal_coupling. reflexivity. Qed.

(** Full Hamiltonian needed for true degeneracy *)
Theorem full_hamiltonian_needed :
  (* Off-diagonal = 0 (our limitation) *)
  (forall N n1 l1 n2 l2, off_diagonal_coupling N n1 l1 n2 l2 == 0) /\
  (* Splitting is nonzero (consequence) *)
  ~ (splitting_limit == 0) /\
  (* It's an artifact *)
  (1#16) < Qabs splitting_limit.
Proof.
  refine (conj _ (conj _ _)).
  - exact off_diagonal_is_zero.
  - exact splitting_nonzero.
  - exact our_splitting_is_order_one.
Qed.

(** P4 alias: splitting is computable *)
Lemma p4_splitting_computable : forall N, exists q : Q, lamb_splitting N == q.
Proof. exact splitting_computable. Qed.

(** Deviation shrinks at each step *)
Theorem energy_gap_shrinks : forall N,
  Qabs (lamb_splitting (S N) - splitting_limit) <
  Qabs (lamb_splitting N - splitting_limit).
Proof.
  intros N. rewrite !splitting_deviation_abs.
  (* 1/(S(S N)) < 1/(S N) *)
  unfold Qdiv, Qlt, Qmult, Qinv. simpl. nia.
Qed.

(** Splitting crosses zero at N=7 *)
Lemma splitting_crosses_zero : lamb_splitting 7 == 0.
Proof. vm_compute. reflexivity. Qed.

(** Framework established: process + Cauchy + limit + honest *)
Theorem framework_established :
  (* Process is defined and computable *)
  (forall N, exists q, lamb_splitting N == q) /\
  (* Cauchy sequence *)
  is_cauchy lamb_splitting /\
  (* Limit computed *)
  splitting_limit == (1#8) /\
  (* Honest about limitations *)
  ~ (splitting_limit == 0).
Proof.
  refine (conj _ (conj _ (conj _ _))).
  - exact splitting_computable.
  - exact splitting_is_cauchy.
  - exact splitting_limit_value.
  - exact splitting_nonzero.
Qed.

(* ========================================================================= *)
(*              PART IV: SUMMARY THEOREMS                                    *)
(* ========================================================================= *)

(** Convergence theorem *)
Theorem lamb_shift_convergence_theorem :
  (* Convergence *)
  (forall eps, 0 < eps -> exists M, forall N, (M <= N)%nat ->
    Qabs (lamb_splitting N - splitting_limit) < eps) /\
  (* Cauchy *)
  is_cauchy lamb_splitting /\
  (* Limit value *)
  splitting_limit == (1#8).
Proof.
  refine (conj _ (conj _ _)).
  - exact splitting_converges.
  - exact splitting_is_cauchy.
  - exact splitting_limit_value.
Qed.

(** Honest assessment theorem *)
Theorem lamb_shift_honest_assessment :
  (* Our splitting = 1/8 (artifact of diagonal approx) *)
  splitting_limit == (1#8) /\
  (* Textbook says E(2S) = E(2P) but we get different limits *)
  ~ (hydrogen_limit_3d 1 0 == hydrogen_limit_3d 0 1) /\
  (* Our splitting is O(1), physical Lamb shift is O(alpha^5) *)
  ~ (splitting_limit == 0).
Proof.
  refine (conj _ (conj _ _)).
  - exact splitting_limit_value.
  - exact no_accidental_degeneracy.
  - exact splitting_nonzero.
Qed.

(** Process view of splitting *)
Theorem lamb_shift_process_view :
  (* P4: finite at every stage *)
  (forall N, exists q, lamb_splitting N == q) /\
  (* Monotonically increasing *)
  (forall N, lamb_splitting N < lamb_splitting (S N)) /\
  (* Converges *)
  (forall eps, 0 < eps -> exists M, forall N, (M <= N)%nat ->
    Qabs (lamb_splitting N - splitting_limit) < eps) /\
  (* Deviation = 1/K *)
  (forall N, Qabs (lamb_splitting N - splitting_limit) ==
    1 / inject_Z (Z.of_nat (S N))).
Proof.
  refine (conj _ (conj _ (conj _ _))).
  - exact splitting_computable.
  - exact splitting_monotone.
  - exact splitting_converges.
  - exact splitting_deviation_abs.
Qed.

(** Framework theorem *)
Theorem lamb_shift_framework_theorem :
  (* Splitting defined *)
  (forall N, exists q, lamb_splitting N == q) /\
  (* Cauchy *)
  is_cauchy lamb_splitting /\
  (* Limit computed *)
  splitting_limit == (1#8) /\
  (* Needs full Hamiltonian *)
  (forall N n1 l1 n2 l2, off_diagonal_coupling N n1 l1 n2 l2 == 0).
Proof.
  refine (conj _ (conj _ (conj _ _))).
  - exact splitting_computable.
  - exact splitting_is_cauchy.
  - exact splitting_limit_value.
  - exact off_diagonal_is_zero.
Qed.

(** What Phase 3 proved *)
Theorem phase3_verified_results :
  (* Partial degeneracy: same n_r → same limit *)
  (forall n_r l1 l2, hydrogen_limit_3d n_r l1 == hydrogen_limit_3d n_r l2) /\
  (* Convergence: each (n_r,l) converges *)
  (forall n_r l eps, 0 < eps -> exists M, forall N, (M <= N)%nat ->
    Qabs (scaled_energy_3d N n_r l - hydrogen_limit_3d n_r l) < eps) /\
  (* 2S-2P splitting computed *)
  splitting_limit == (1#8).
Proof.
  refine (conj _ (conj _ _)).
  - exact partial_degeneracy.
  - exact convergence_3d.
  - exact splitting_limit_value.
Qed.

(** What needs off-diagonal coupling (open questions) *)
Theorem phase3_open_questions :
  (* Accidental degeneracy: same principal n, different n_r → currently different *)
  ~ (hydrogen_limit_3d 1 0 == hydrogen_limit_3d 0 1) /\
  (* Off-diagonal = 0 is the cause *)
  (forall N n1 l1 n2 l2, off_diagonal_coupling N n1 l1 n2 l2 == 0) /\
  (* Splitting artifact *)
  ~ (splitting_limit == 0).
Proof.
  refine (conj _ (conj _ _)).
  - exact no_accidental_degeneracy.
  - exact off_diagonal_is_zero.
  - exact splitting_nonzero.
Qed.

(** ★ MASTER THEOREM: all Lamb shift results ★ *)
Theorem lamb_shift_complete :
  (* Exact formula *)
  (forall N, lamb_splitting N == (1#8) - 1 / inject_Z (Z.of_nat (S N))) /\
  (* Convergence *)
  (forall eps, 0 < eps -> exists M, forall N, (M <= N)%nat ->
    Qabs (lamb_splitting N - splitting_limit) < eps) /\
  (* Cauchy *)
  is_cauchy lamb_splitting /\
  (* Limit = 1/8 *)
  splitting_limit == (1#8) /\
  (* Nonzero *)
  ~ (splitting_limit == 0) /\
  (* Monotone *)
  (forall N, lamb_splitting N < lamb_splitting (S N)) /\
  (* Gap shrinks *)
  (forall N, Qabs (lamb_splitting (S N) - splitting_limit) <
    Qabs (lamb_splitting N - splitting_limit)).
Proof.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  - exact splitting_formula.
  - exact splitting_converges.
  - exact splitting_is_cauchy.
  - exact splitting_limit_value.
  - exact splitting_nonzero.
  - exact splitting_monotone.
  - exact energy_gap_shrinks.
Qed.

(** ★ THE COMBINED PHASE 3 MAIN THEOREM ★ *)
Theorem experimental_phase3_main :
  (* From CoulombFull3D: partial degeneracy *)
  (forall n_r l1 l2, hydrogen_limit_3d n_r l1 == hydrogen_limit_3d n_r l2) /\
  (* From CoulombFull3D: convergence *)
  (forall n_r l eps, 0 < eps -> exists M, forall N, (M <= N)%nat ->
    Qabs (scaled_energy_3d N n_r l - hydrogen_limit_3d n_r l) < eps) /\
  (* From CoulombFull3D: no accidental degeneracy *)
  ~ (hydrogen_limit_3d 1 0 == hydrogen_limit_3d 0 1) /\
  (* From LambShift: splitting formula *)
  (forall N, lamb_splitting N == (1#8) - 1 / inject_Z (Z.of_nat (S N))) /\
  (* From LambShift: splitting converges *)
  (forall eps, 0 < eps -> exists M, forall N, (M <= N)%nat ->
    Qabs (lamb_splitting N - splitting_limit) < eps) /\
  (* From LambShift: splitting nonzero (artifact) *)
  ~ (splitting_limit == 0).
Proof.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  - exact partial_degeneracy.
  - exact convergence_3d.
  - exact no_accidental_degeneracy.
  - exact splitting_formula.
  - exact splitting_converges.
  - exact splitting_nonzero.
Qed.

(** Verification entry: partial degeneracy proved *)
Theorem verification_table_entry_partial_degeneracy :
  forall n_r l1 l2, hydrogen_limit_3d n_r l1 == hydrogen_limit_3d n_r l2.
Proof. exact partial_degeneracy. Qed.

(** Verification entry: centrifugal splitting vanishes as O(1/K) *)
Theorem verification_table_entry_centrifugal_splitting :
  forall n_r l eps, 0 < eps ->
  exists M, forall N, (M <= N)%nat ->
    Qabs (degeneracy_process n_r l N) < eps.
Proof. exact splitting_vanishes. Qed.
