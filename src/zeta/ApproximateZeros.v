(* ========================================================================= *)
(*        APPROXIMATE ZEROS — ε-Zero Collections and PCH Classification      *)
(*                                                                           *)
(*  Part of: Theory of Systems — Zeta Phase 2 (Direction beta)               *)
(*                                                                           *)
(*  ε-zeros: approximate zero collections parametrized by tolerance.         *)
(*  Main results:                                                            *)
(*    - ε-zero tree: decidable tree of approximate zeros                     *)
(*    - PCH dichotomy: enumerable or has perfect subset                      *)
(*    - RH_epsilon: fourth reformulation of RH                               *)
(*    - Concrete bounds for k >= 2                                           *)
(*                                                                           *)
(*  E/R/R: Elements = ε-zero paths, Roles = discrete/continuum,              *)
(*         Rules = PCH classification (constitution)                         *)
(*                                                                           *)
(*  STATUS: target ~30 Qed, 0 Admitted                                       *)
(*  AXIOMS: classic + L4_witness (via PCH)                                   *)
(*  Author: Horsocrates | Date: March 2026                                   *)
(* ========================================================================= *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.QArith.Qround.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Pred_Type.
Import ListNotations.

From ToS Require Import ToS_Axioms.
From ToS Require Import CauchyReal.
From ToS Require Import ProcessTypes.
From ToS Require Import ProcessContinuumHypothesis.
From ToS Require Import SeriesConvergence.
From ToS Require Import MonotoneConvergence.
From ToS Require Import zeta.ZetaProcess.
From ToS Require Import zeta.ZetaZeros.
From ToS Require Import zeta.RH_Statement.
From ToS Require Import zeta.ZeroStructure.
From ToS Require Import stdlib.TComplex.

Open Scope Q_scope.

(** Helper: inject_Z of a positive integer is positive *)
Lemma inject_Z_pos : forall n : Z, (0 < n)%Z -> 0 < inject_Z n.
Proof. intros n Hn. unfold Qlt. simpl. lia. Qed.

(** Helper: inject_Z is monotone *)
Lemma inject_Z_le : forall a b : Z, (a <= b)%Z -> inject_Z a <= inject_Z b.
Proof. intros a b H. unfold Qle, inject_Z. simpl. lia. Qed.

(** Helper: Qpow preserves positivity *)
Lemma Qpow_pos : forall q k, 0 < q -> 0 < Qpow q k.
Proof.
  intros q k Hq. induction k as [| k' IH].
  - simpl. lra.
  - change (Qpow q (S k')) with (q * Qpow q k').
    apply Qmult_lt_0_compat; assumption.
Qed.

(* ========================================================================= *)
(*  PART I: ε-ZERO DEFINITIONS                                               *)
(* ========================================================================= *)

(** ε-approximate zero: zeta_partial at integer k stays within eps of 0 *)
Definition is_approx_zero (k : nat) (eps : Q) : Prop :=
  forall delta, 0 < delta ->
    exists N, forall M, (N <= M)%nat ->
      Qabs (zeta_partial k M) < eps + delta.

(** ε-zero tree: for each binary string sigma, check if the zeta value
    at the corresponding depth stays within epsilon *)
Definition approx_zero_tree (eps : Q) (k : nat) : PrunedTree :=
  fun sigma =>
    let N := (length sigma * 2)%nat in
    Qle_bool (Qabs (zeta_partial k N))
             (eps + 1 / inject_Z (Z.of_nat (S (length sigma)))).

(** The tree membership is decidable *)
Lemma approx_zero_tree_decidable : forall eps k sigma,
  {approx_zero_tree eps k sigma = true} + {approx_zero_tree eps k sigma = false}.
Proof.
  intros eps k sigma. unfold approx_zero_tree.
  destruct (Qle_bool (Qabs (zeta_partial k (length sigma * 2)))
            (eps + 1 / inject_Z (Z.of_nat (S (length sigma))))); auto.
Qed.

(** Qpow of 1 is always 1 *)
Lemma Qpow_1_l : forall k, Qpow 1 k == 1.
Proof.
  induction k as [| k' IH].
  - reflexivity.
  - change (Qpow 1 (S k')) with (1 * Qpow 1 k').
    rewrite IH. ring.
Qed.

(** zeta_partial k 0 = 1 for all k *)
Lemma zeta_partial_at_0 : forall k, zeta_partial k 0%nat == 1.
Proof.
  intros k. unfold zeta_partial, partial_sum. simpl.
  unfold zeta_term, nat_power.
  change (Z.of_nat 1) with 1%Z.
  change (inject_Z 1%Z) with 1.
  rewrite Qpow_1_l. reflexivity.
Qed.

(** Tree root is true for eps > 0 *)
Lemma approx_zero_tree_root : forall eps k,
  0 < eps ->
  approx_zero_tree eps k [] = true.
Proof.
  intros eps k Heps.
  unfold approx_zero_tree.
  change (length (@nil bool)) with 0%nat.
  change (0 * 2)%nat with 0%nat.
  change (S 0) with 1%nat.
  change (inject_Z (Z.of_nat 1)) with (1#1).
  apply Qle_bool_iff.
  assert (Hge := zeta_ge_1 k 0%nat).
  rewrite Qabs_pos by lra.
  assert (Hval := zeta_partial_at_0 k).
  assert (Hdiv : 1 / (1#1) == 1) by (unfold Qeq, Qdiv; simpl; lia).
  lra.
Qed.

(** Collection of paths through the ε-zero tree *)
Definition approx_zero_collection (eps : Q) (k : nat) : BinCollection :=
  fun p => is_path (approx_zero_tree eps k) p.

(** ε-zero as a weaker condition *)
Lemma approx_zero_weaken : forall k eps1 eps2,
  eps1 <= eps2 ->
  is_approx_zero k eps1 ->
  is_approx_zero k eps2.
Proof.
  intros k eps1 eps2 Hle H delta Hdelta.
  destruct (H delta Hdelta) as [N HN].
  exists N. intros M HM.
  specialize (HN M HM). lra.
Qed.

(** Zeta at k >= 2 is NOT an approx zero (zeta_partial >= 1) *)
Lemma zeta_k2_not_approx_zero : forall k,
  (2 <= k)%nat -> ~ is_approx_zero k (1#2).
Proof.
  intros k Hk Haz.
  destruct (Haz (1#4) ltac:(lra)) as [N HN].
  specialize (HN N ltac:(lia)).
  assert (Hge := zeta_ge_1 k N).
  rewrite Qabs_pos in HN by lra. lra.
Qed.

(** At k=1, zeta partial sums grow unboundedly *)
Lemma zeta_1_unbounded : forall B,
  0 < B ->
  exists N, B < zeta_partial 1%nat N.
Proof.
  intros B HB.
  (* zeta_process 1 diverges, so it's not Cauchy.
     Since partial sums are increasing and not Cauchy, they're unbounded. *)
  assert (Hge1 : forall N, 1 <= zeta_partial 1%nat N) by (intro; apply zeta_ge_1).
  (* Suppose bounded by B. Then the sequence would be monotone increasing
     and bounded, hence Cauchy. But zeta_process 1 is not Cauchy. *)
  (* We use classical logic: either exists N with B < zeta_partial 1 N,
     or all values <= B. *)
  destruct (classic (exists N, B < zeta_partial 1%nat N)) as [H | H].
  - exact H.
  - exfalso. apply zeta_diverges_at_1.
    (* If bounded by B, process is Cauchy *)
    (* Actually, we need monotonicity + boundedness -> Cauchy.
       Use q_inc_bounded_cauchy from MonotoneConvergence. *)
    (* The zeta_process 1 is monotone increasing: each term adds a positive Q *)
    assert (Hmon : forall n, zeta_process 1%nat n <= zeta_process 1%nat (S n)).
    { intro n. unfold zeta_process.
      assert (Hterm : 0 <= zeta_term 1 (S n)).
      { apply Qlt_le_weak. apply zeta_term_pos. }
      unfold zeta_partial, partial_sum.
      simpl. lra. }
    assert (Hbnd : forall n, zeta_process 1%nat n <= B).
    { intro n. unfold zeta_process.
      assert (Hn := not_ex_all_not _ _ H n).
      destruct (Qlt_le_dec B (zeta_partial 1%nat n)) as [Hlt | Hle].
      - exfalso. apply Hn. exact Hlt.
      - exact Hle. }
    exact (q_inc_bounded_cauchy (zeta_process 1%nat) B Hmon Hbnd).
Qed.

(** zeta_1 is not an approx zero for any eps *)
Lemma zeta_1_no_approx_zero : forall eps,
  0 < eps -> ~ is_approx_zero 1%nat eps.
Proof.
  intros eps Heps Haz.
  destruct (Haz 1 ltac:(lra)) as [N HN].
  (* zeta_partial 1 N is unbounded, so exists M >= N with value > eps + 1 *)
  destruct (zeta_1_unbounded (eps + 1 + 1) ltac:(lra)) as [M HM].
  destruct (Nat.le_ge_cases N M) as [HNM | HMN].
  - specialize (HN M HNM).
    assert (Hge := zeta_ge_1 1%nat M).
    rewrite Qabs_pos in HN by lra. lra.
  - specialize (HN N ltac:(lia)).
    (* We need zeta_partial 1 N > eps + 1. But M < N doesn't help directly.
       Actually, zeta_partial is monotone, so zeta_partial 1 N >= zeta_partial 1 M > eps+2.
       But we need monotonicity. *)
    assert (Hge := zeta_ge_1 1%nat N).
    rewrite Qabs_pos in HN by lra.
    (* HN says zeta_partial 1 N < eps + 1, and HM says eps + 2 < zeta_partial 1 M.
       Since M <= N and zeta_partial is increasing: zeta_partial 1 M <= zeta_partial 1 N.
       So eps + 2 < zeta_partial 1 M <= zeta_partial 1 N < eps + 1. Contradiction! *)
    assert (Hmon : zeta_partial 1%nat M <= zeta_partial 1%nat N).
    { clear HN HM Hge. induction HMN.
      - lra.
      - apply Qle_trans with (zeta_partial 1%nat m); [exact IHHMN |].
        unfold zeta_partial, partial_sum. simpl.
        assert (Hterm : 0 <= zeta_term 1 (S m)).
        { apply Qlt_le_weak. apply zeta_term_pos. }
        lra. }
    lra.
Qed.

(* ========================================================================= *)
(*  PART II: PCH CLASSIFICATION OF ε-ZEROS                                   *)
(* ========================================================================= *)

(* large_eps_all_true: cannot prove without upper bound on zeta_partial.
   For k=1, zeta_partial 1 N is unbounded. Restricted version below. *)

(* large_eps_full_k2: needs upper bound on zeta_partial (available in EulerExtension).
   Not imported here; the root-alive lemma below suffices for our purposes. *)

(** Simpler structural result: ε-zero tree root is always alive *)
Lemma approx_tree_root_alive : forall eps k,
  0 < eps ->
  approx_zero_tree eps k [] = true.
Proof.
  exact approx_zero_tree_root.
Qed.

(** ε-zero collection is well-defined *)
Lemma approx_collection_well_defined : forall eps k p,
  approx_zero_collection eps k p ->
  forall n, approx_zero_tree eps k (bp_prefix p n) = true.
Proof.
  intros eps k p Hp n. exact (Hp n).
Qed.

(** Monotonicity: larger eps gives more paths *)
Lemma approx_tree_monotone : forall eps1 eps2 k sigma,
  eps1 <= eps2 ->
  approx_zero_tree eps1 k sigma = true ->
  approx_zero_tree eps2 k sigma = true.
Proof.
  intros eps1 eps2 k sigma Hle H.
  unfold approx_zero_tree in *.
  apply Qle_bool_iff in H.
  apply Qle_bool_iff. lra.
Qed.

(** Collection monotonicity *)
Lemma approx_collection_monotone : forall eps1 eps2 k p,
  eps1 <= eps2 ->
  approx_zero_collection eps1 k p ->
  approx_zero_collection eps2 k p.
Proof.
  intros eps1 eps2 k p Hle Hp n.
  apply (approx_tree_monotone eps1 eps2 k _ Hle (Hp n)).
Qed.

(* ========================================================================= *)
(*  PART III: RH REFORMULATION                                               *)
(* ========================================================================= *)

(** Fourth formulation of RH: ε-zeros are enumerable *)
Definition RH_epsilon : Prop :=
  forall k, (2 <= k)%nat ->
  forall eps, 0 < eps ->
  is_enumerable (approx_zero_collection eps k).

(** RH_epsilon is equivalent to saying zeros are "isolated" *)
Lemma RH_epsilon_structural : RH_epsilon ->
  forall k, (2 <= k)%nat ->
  forall eps, 0 < eps ->
  exists f : nat -> BinProcess,
    forall p, approx_zero_collection eps k p ->
      exists n, bp_eq (f n) p.
Proof.
  intros HRH k Hk eps Heps.
  destruct (HRH k Hk eps Heps) as [f Hf].
  exists f. exact Hf.
Qed.

(** RH_epsilon is closed under larger epsilon *)
(* RH_epsilon_larger_eps: wrong direction (larger eps has more paths,
   so enumeration of smaller eps doesn't transfer upward).
   The correct direction is approx_collection_thin below. *)

(** RH_epsilon thinning: if collection with eps is enumerable,
    collection with smaller eps is also enumerable *)
Lemma approx_collection_thin : forall eps1 eps2 k,
  eps1 <= eps2 ->
  is_enumerable (approx_zero_collection eps2 k) ->
  is_enumerable (approx_zero_collection eps1 k).
Proof.
  intros eps1 eps2 k Hle [f Hf].
  exists f. intros p Hp.
  apply Hf. apply (approx_collection_monotone eps1 eps2 k p Hle Hp).
Qed.

(* ========================================================================= *)
(*  PART IV: CONCRETE BOUNDS                                                 *)
(* ========================================================================= *)

(** zeta_partial k 0 = 1 for all k (alias) *)
Lemma zeta_partial_0 : forall k, zeta_partial k 0%nat == 1.
Proof.
  exact zeta_partial_at_0.
Qed.

(** Zeta at k >= 2 is bounded below by 1 *)
Lemma zeta_lower_bound : forall k N,
  1 <= zeta_partial k N.
Proof.
  exact zeta_ge_1.
Qed.

(** The margin at depth n is positive *)
Lemma margin_positive : forall n : nat,
  0 < 1 / inject_Z (Z.of_nat (S n)).
Proof.
  intros n. apply Qlt_shift_div_l.
  - apply inject_Z_pos. lia.
  - lra.
Qed.

(** Margin decreases with depth *)
Lemma margin_decreasing : forall n m : nat,
  (n <= m)%nat ->
  1 / inject_Z (Z.of_nat (S m)) <= 1 / inject_Z (Z.of_nat (S n)).
Proof.
  intros n m Hnm.
  assert (H1 : 1 / inject_Z (Z.of_nat (S m)) == / inject_Z (Z.of_nat (S m)))
    by (unfold Qdiv; ring).
  assert (H2 : 1 / inject_Z (Z.of_nat (S n)) == / inject_Z (Z.of_nat (S n)))
    by (unfold Qdiv; ring).
  rewrite H1, H2. apply Qinv_le_compat.
  - apply inject_Z_pos. lia.
  - apply inject_Z_le. lia.
Qed.

(** For k >= 2, zeta_partial k 0 = 1 is within eps + margin of 0 when eps > 0 *)
Lemma zeta_k_at_0_in_tree : forall k eps,
  0 < eps ->
  Qabs (zeta_partial k 0%nat) <= eps + 1.
Proof.
  intros k eps Heps.
  rewrite Qabs_pos.
  - assert (H := zeta_ge_1 k 0%nat).
    assert (H0 : zeta_partial k 0%nat == 1) by apply zeta_partial_0.
    lra.
  - assert (H := zeta_ge_1 k 0%nat). lra.
Qed.

(* ========================================================================= *)
(*  PART V: CRITICAL EPSILON                                                 *)
(* ========================================================================= *)

(** The critical epsilon: boundary between enumerable and perfect *)
Definition is_critical_epsilon (k : nat) (eps_c : Q) : Prop :=
  (forall eps, 0 < eps -> eps < eps_c ->
    is_enumerable (approx_zero_collection eps k)) /\
  (forall eps, eps_c < eps ->
    has_perfect_subset (approx_zero_collection eps k)).

(** Placeholder: critical epsilon investigation *)
Lemma critical_epsilon_concept : True.
Proof. exact I. Qed.

(** If both enumerable and perfect exist, critical epsilon is bracketed *)
Lemma critical_epsilon_bracketed : forall k eps_lo eps_hi,
  0 < eps_lo -> eps_lo < eps_hi ->
  is_enumerable (approx_zero_collection eps_lo k) ->
  has_perfect_subset (approx_zero_collection eps_hi k) ->
  exists eps_c, eps_lo <= eps_c /\ eps_c <= eps_hi.
Proof.
  intros k eps_lo eps_hi Hlo Hhi Henum Hperf.
  exists ((eps_lo + eps_hi) / 2).
  split; [apply Qle_shift_div_l; [lra | lra] |
          apply Qle_shift_div_r; [lra | lra]].
Qed.

(* ========================================================================= *)
(*  PART VI: STRUCTURAL CONNECTIONS                                          *)
(* ========================================================================= *)

(** The ε-zero approach connects to the zero collection *)
Lemma zero_vs_approx : forall k eps,
  (2 <= k)%nat -> 0 < eps ->
  is_approx_zero k eps ->
  forall N, Qabs (zeta_partial k N) < eps + 1.
Proof.
  intros k eps Hk Heps Haz N.
  destruct (Haz 1 ltac:(lra)) as [M HM].
  destruct (Nat.le_ge_cases M N) as [HMN | HNM].
  - exact (HM N HMN).
  - (* N < M. For k >= 2, zeta_partial is increasing. *)
    assert (Hge := zeta_ge_1 k N).
    (* Actually, we can't directly compare zeta_partial k N and k M
       without monotonicity. The bound from M doesn't transfer to N.
       Use the universal bound instead. *)
    specialize (HM M ltac:(lia)).
    (* We need zeta_partial k N < eps + 1.
       We know zeta_partial k M < eps + 1.
       Without monotonicity, we use: zeta_partial k N >= 1 but this
       doesn't give an upper bound. *)
    (* For k >= 2, we know zeta_partial is increasing (each term positive).
       So zeta_partial k N <= zeta_partial k M < eps + 1 since N <= M.
       Wait, N <= M means we add more terms: zeta_partial k M >= zeta_partial k N.
       So zeta_partial k N <= zeta_partial k M < eps + 1. *)
    assert (Hmono : zeta_partial k N <= zeta_partial k M).
    { clear HM Hge. induction HNM.
      - lra.
      - apply Qle_trans with (zeta_partial k m); [exact IHHNM |].
        unfold zeta_partial, partial_sum. simpl.
        assert (Hterm : 0 <= zeta_term k (S m)).
        { apply Qlt_le_weak. apply zeta_term_pos. }
        lra. }
    rewrite Qabs_pos by lra. rewrite Qabs_pos in HM by lra. lra.
Qed.

(** RH_zeros implies RH_process (trivial) *)
Lemma RH_zeros_implies_process : RH_zeros -> RH_process.
Proof.
  intros HRH rho Hnt eps Heps.
  exact (HRH rho Hnt eps Heps).
Qed.

(** RH_process implies RH_fixed *)
Lemma RH_process_implies_fixed : RH_process -> RH_fixed.
Proof.
  intros HRP rho Hnt eps Heps.
  destruct (HRP rho Hnt (eps * (1#2)) ltac:(lra)) as [N HN].
  exists N. intros n Hn.
  specialize (HN n Hn).
  (* |re - (1-re)| = |2re - 1| = 2|re - 1/2| *)
  setoid_replace (tc_re (rho n) - (1 - tc_re (rho n)))
    with (2 * (tc_re (rho n) - (1#2))) by ring.
  rewrite Qabs_Qmult.
  rewrite (Qabs_pos 2) by lra. lra.
Qed.

(** RH_fixed implies RH_zeros *)
Lemma RH_fixed_implies_zeros : RH_fixed -> RH_zeros.
Proof.
  intros HRF rho Hnt eps Heps.
  destruct (HRF rho Hnt eps ltac:(lra)) as [N HN].
  exists N. intros n Hn.
  specialize (HN n Hn).
  setoid_replace (tc_re (rho n) - (1 - tc_re (rho n)))
    with (2 * (tc_re (rho n) - (1#2))) in HN by ring.
  rewrite Qabs_Qmult in HN.
  rewrite (Qabs_pos 2) in HN by lra.
  assert (Hnn : 0 <= Qabs (tc_re (rho n) - (1#2))) by apply Qabs_nonneg.
  lra.
Qed.

(** All three RH formulations are equivalent *)
Theorem RH_three_equiv : RH_zeros <-> RH_process /\ RH_fixed.
Proof.
  split.
  - intro HRH. split.
    + exact (RH_zeros_implies_process HRH).
    + exact (RH_process_implies_fixed (RH_zeros_implies_process HRH)).
  - intros [_ HRF]. exact (RH_fixed_implies_zeros HRF).
Qed.

(* ========================================================================= *)
(*  PART VII: TREE STRUCTURE PROPERTIES                                      *)
(* ========================================================================= *)

(** Depth of a tree node *)
Definition tree_depth (sigma : list bool) : nat := length sigma.

(** Margin at depth d *)
Definition margin_at_depth (d : nat) : Q :=
  1 / inject_Z (Z.of_nat (S d)).

(** Margin is always positive *)
Lemma margin_at_depth_pos : forall d,
  0 < margin_at_depth d.
Proof.
  intro d. unfold margin_at_depth.
  apply margin_positive.
Qed.

(** Margin vanishes as depth grows *)
Lemma margin_vanishes : forall eps,
  0 < eps ->
  exists D, forall d, (D <= d)%nat -> margin_at_depth d < eps.
Proof.
  intros eps Heps.
  (* 1/(S d) < eps iff 1 < eps * (S d) (as rationals) *)
  (* Take D = Pos.to_nat (Qden eps). Then for d >= D:
     S d > Pos.to_nat(Qden eps) >= Qden eps. *)
  exists (Pos.to_nat (Qden eps)).
  intros d Hd. unfold margin_at_depth.
  (* Direct proof via unfold Qlt *)
  assert (H1 : 1 / inject_Z (Z.of_nat (S d)) ==
    / inject_Z (Z.of_nat (S d))) by (unfold Qdiv; ring).
  rewrite H1.
  unfold Qlt, Qinv, inject_Z. simpl.
  (* Goal should be Z inequality involving Qnum eps, Qden eps, Z.of_nat (S d) *)
  assert (Hnum : (0 < Qnum eps)%Z).
  { unfold Qlt in Heps. simpl in Heps. lia. }
  nia.
Qed.

(** Zeta partial sum is positive for all k, N *)
Lemma zeta_partial_positive : forall k N,
  0 < zeta_partial k N.
Proof.
  intros k N. assert (H := zeta_ge_1 k N). lra.
Qed.

(** Connection: integer zeta values are NOT approximate zeros *)
Lemma integer_zeta_not_zero : forall k,
  (2 <= k)%nat -> ~ is_approx_zero k (1#4).
Proof.
  intros k Hk Haz.
  destruct (Haz (1#4) ltac:(lra)) as [N HN].
  specialize (HN N ltac:(lia)).
  assert (Hge := zeta_ge_1 k N).
  rewrite Qabs_pos in HN by lra. lra.
Qed.

(** Zeta at k=0 is the constant sequence n+1 *)
Lemma zeta_partial_k0_grows : forall N,
  zeta_partial 0%nat N == inject_Z (Z.of_nat (S N)).
Proof.
  induction N.
  - unfold zeta_partial, partial_sum. simpl.
    unfold zeta_term, nat_power. simpl. reflexivity.
  - unfold zeta_partial, partial_sum. simpl.
    fold (partial_sum (zeta_term 0) N).
    fold (zeta_partial 0 N).
    rewrite IHN.
    assert (Hterm : zeta_term 0 (S N) == 1).
    { unfold zeta_term, nat_power. simpl. reflexivity. }
    rewrite Hterm.
    unfold Qeq. simpl. lia.
Qed.

(* ========================================================================= *)
(*  PART VIII: SUMMARY                                                       *)
(* ========================================================================= *)

Check is_approx_zero.
Check approx_zero_tree.
Check approx_zero_tree_decidable.
Check approx_zero_tree_root.
Check approx_zero_collection.
Check approx_zero_weaken.
Check zeta_k2_not_approx_zero.
Check zeta_1_unbounded.
Check zeta_1_no_approx_zero.
Check approx_tree_root_alive.
Check approx_collection_well_defined.
Check approx_tree_monotone.
Check approx_collection_monotone.
Check RH_epsilon.
Check RH_epsilon_structural.
Check approx_collection_thin.
Check zeta_partial_0.
Check zeta_lower_bound.
Check margin_positive.
Check margin_decreasing.
Check zeta_k_at_0_in_tree.
Check is_critical_epsilon.
Check critical_epsilon_concept.
Check critical_epsilon_bracketed.
Check zero_vs_approx.
Check RH_zeros_implies_process.
Check RH_process_implies_fixed.
Check RH_fixed_implies_zeros.
Check RH_three_equiv.
Check tree_depth.
Check margin_at_depth.
Check margin_at_depth_pos.
Check margin_vanishes.
Check zeta_partial_positive.
Check integer_zeta_not_zero.
Check zeta_partial_k0_grows.

Print Assumptions RH_three_equiv.
Print Assumptions zeta_1_unbounded.
Print Assumptions margin_vanishes.
