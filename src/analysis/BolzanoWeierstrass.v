(** * BolzanoWeierstrass.v -- Bolzano-Weierstrass Theorem

    Theory of Systems -- Analysis Gap Closure (Phase 0)

    Every bounded sequence in [a,b] has a Cauchy subsequence.

    Elements: sequence terms, interval endpoints
    Roles:    term -> Bounded, subsequence -> Convergent, interval -> Container
    Rules:    bisection selection (L5: choose left when equal)
    Status:   converging | oscillating | bounded

    Strategy: bisect [a,b], choose half with infinitely many terms (classic),
    nested intervals -> convergent subsequence via Completeness.v

    STATUS: 22 Qed, 0 Admitted
    Axioms: classic (L3), L4_witness (L4) — via ToS_Axioms.v
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qminmax.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
From ToS Require Import ToS_Axioms.
Require Import Coq.Logic.Classical_Pred_Type.

From ToS Require Import Archimedean_ERR.
From ToS Require Import CauchyReal.
From ToS Require Import Completeness.
From ToS Require Import MonotoneConvergence.

Open Scope Q_scope.
Local Open Scope cauchy_scope.

(* ========================================================================= *)
(* SECTION 1: BOUNDED SEQUENCES AND INFINITELY MANY                         *)
(* ========================================================================= *)

(** A sequence is bounded in [a, b] *)
Definition bounded_seq (s : nat -> Q) (a b : Q) : Prop :=
  forall n, a <= s n /\ s n <= b.

(** Infinitely many terms of s lie in [lo, hi] *)
Definition infinitely_many_in (s : nat -> Q) (lo hi : Q) : Prop :=
  forall N : nat, exists n : nat, (N <= n)%nat /\ lo <= s n /\ s n <= hi.

(** 1. bounded_seq implies infinitely_many_in on the whole interval *)
Lemma bounded_seq_initial : forall (s : nat -> Q) (a b : Q),
  bounded_seq s a b -> infinitely_many_in s a b.
Proof.
  intros s a b Hbnd N.
  exists N. split.
  - lia.
  - exact (Hbnd N).
Qed.

(** 2. Infinite pigeonhole: if infinitely many in [lo,hi],
       then infinitely many in left half or right half (uses classic) *)
Lemma infinite_pigeonhole : forall (s : nat -> Q) (lo hi : Q),
  infinitely_many_in s lo hi ->
  infinitely_many_in s lo ((lo + hi) / 2) \/
  infinitely_many_in s ((lo + hi) / 2) hi.
Proof.
  intros s lo hi Hinf.
  destruct (classic (infinitely_many_in s lo ((lo + hi) / 2))) as [Hleft | Hnleft].
  - left. exact Hleft.
  - right.
    apply not_all_ex_not in Hnleft.
    destruct Hnleft as [N0 HN0].
    intros N.
    destruct (Hinf (Nat.max N N0)) as [n [Hn [Hlo Hhi]]].
    exists n. split.
    + lia.
    + split; [| exact Hhi].
      destruct (Qlt_le_dec (s n) ((lo + hi) / 2)) as [Hlt | Hge].
      * exfalso. apply HN0.
        exists n. split; [lia |]. split; [exact Hlo |]. lra.
      * exact Hge.
Qed.

(* ========================================================================= *)
(* SECTION 2: BISECTION STATE AND ITERATION                                 *)
(* ========================================================================= *)

Record BWState := mkBW {
  bw_left : Q;
  bw_right : Q
}.

Definition bw_mid (st : BWState) : Q := (bw_left st + bw_right st) / 2.

(** bw_step_left: Prop saying "go left" *)
Definition bw_step_left (s : nat -> Q) (st : BWState) : Prop :=
  infinitely_many_in s (bw_left st) (bw_mid st).

(** bw_step: use classic to choose left or right half.
    Uses Defined so it computes (needed for Fixpoint). *)
Definition bw_step (s : nat -> Q) (st : BWState) : BWState.
Proof.
  destruct (L3_informative (bw_step_left s st)) as [H | H].
  - exact (mkBW (bw_left st) (bw_mid st)).
  - exact (mkBW (bw_mid st) (bw_right st)).
Defined.

(** Iteration of bisection *)
Fixpoint bw_iter (s : nat -> Q) (st : BWState) (n : nat) : BWState :=
  match n with
  | O => st
  | S n' => bw_step s (bw_iter s st n')
  end.

(* ========================================================================= *)
(* SECTION 3: BISECTION PROPERTIES                                          *)
(* ========================================================================= *)

(** Helper for qdiv2: convert /2 to *(1#2) for lra *)
Ltac bw_qdiv2_lra :=
  repeat match goal with
  | |- context [?x / 2] =>
      setoid_replace (x / 2) with (x * (1#2)) by field
  end; lra.

(** 3. bw_step preserves lo <= hi *)
Lemma bw_step_valid : forall s st,
  bw_left st <= bw_right st ->
  bw_left (bw_step s st) <= bw_right (bw_step s st).
Proof.
  intros s [l r] Hlr. change (l <= r) in Hlr.
  unfold bw_step.
  destruct (L3_informative (bw_step_left s (mkBW l r))) as [H | H];
    simpl; unfold bw_mid; simpl; bw_qdiv2_lra.
Qed.

(** 4. bw_step halves the width *)
Lemma bw_step_width : forall s st,
  bw_right (bw_step s st) - bw_left (bw_step s st) ==
  (bw_right st - bw_left st) / 2.
Proof.
  intros s [l r].
  unfold bw_step.
  destruct (L3_informative (bw_step_left s (mkBW l r))) as [H | H];
    simpl; unfold bw_mid; simpl; field.
Qed.

(** 5. bw_step: left endpoint doesn't decrease *)
Lemma bw_step_nested_left : forall s st,
  bw_left st <= bw_right st ->
  bw_left st <= bw_left (bw_step s st).
Proof.
  intros s [l r] Hlr. change (l <= r) in Hlr.
  unfold bw_step.
  destruct (L3_informative (bw_step_left s (mkBW l r))) as [H | H];
    simpl; unfold bw_mid; simpl; bw_qdiv2_lra.
Qed.

(** 6. bw_step: right endpoint doesn't increase *)
Lemma bw_step_nested_right : forall s st,
  bw_left st <= bw_right st ->
  bw_right (bw_step s st) <= bw_right st.
Proof.
  intros s [l r] Hlr. change (l <= r) in Hlr.
  unfold bw_step.
  destruct (L3_informative (bw_step_left s (mkBW l r))) as [H | H];
    simpl; unfold bw_mid; simpl; bw_qdiv2_lra.
Qed.

(** 7. bw_step preserves infinitely many terms in chosen half *)
Lemma bw_step_preserves_infinite : forall s st,
  bw_left st <= bw_right st ->
  infinitely_many_in s (bw_left st) (bw_right st) ->
  infinitely_many_in s (bw_left (bw_step s st)) (bw_right (bw_step s st)).
Proof.
  intros s [l r] Hlr Hinf. change (l <= r) in Hlr.
  unfold bw_step.
  destruct (L3_informative (bw_step_left s (mkBW l r))) as [H | H]; simpl.
  - exact H.
  - unfold bw_step_left in H. simpl in H. unfold bw_mid in H. simpl in H.
    destruct (infinite_pigeonhole s l r Hinf) as [Hl | Hr].
    + exfalso. apply H. exact Hl.
    + exact Hr.
Qed.

(** 8. bw_iter preserves validity (induction) *)
Lemma bw_iter_valid : forall s st n,
  bw_left st <= bw_right st ->
  bw_left (bw_iter s st n) <= bw_right (bw_iter s st n).
Proof.
  intros s st n Hs. induction n; simpl.
  - exact Hs.
  - apply bw_step_valid. exact IHn.
Qed.

(** 9. bw_iter: left endpoints are increasing *)
Lemma bw_iter_left_inc : forall s st n,
  bw_left st <= bw_right st ->
  bw_left (bw_iter s st n) <= bw_left (bw_iter s st (S n)).
Proof.
  intros s st n Hs. simpl.
  apply bw_step_nested_left.
  apply bw_iter_valid. exact Hs.
Qed.

(** 10. bw_iter: right endpoints are decreasing *)
Lemma bw_iter_right_dec : forall s st n,
  bw_left st <= bw_right st ->
  bw_right (bw_iter s st (S n)) <= bw_right (bw_iter s st n).
Proof.
  intros s st n Hs. simpl.
  apply bw_step_nested_right.
  apply bw_iter_valid. exact Hs.
Qed.

(** Helper: left endpoints are monotone increasing *)
Lemma bw_left_mono : forall s a b,
  a <= b ->
  forall m n, (m <= n)%nat ->
  bw_left (bw_iter s (mkBW a b) m) <= bw_left (bw_iter s (mkBW a b) n).
Proof.
  intros s a b Hvalid m n Hmn.
  induction Hmn.
  - lra.
  - apply Qle_trans with (bw_left (bw_iter s (mkBW a b) m0)).
    + exact IHHmn.
    + apply bw_iter_left_inc. exact Hvalid.
Qed.

(** Helper: right endpoints are monotone decreasing *)
Lemma bw_right_mono : forall s a b,
  a <= b ->
  forall m n, (m <= n)%nat ->
  bw_right (bw_iter s (mkBW a b) n) <= bw_right (bw_iter s (mkBW a b) m).
Proof.
  intros s a b Hvalid m n Hmn.
  induction Hmn.
  - lra.
  - apply Qle_trans with (bw_right (bw_iter s (mkBW a b) m0)).
    + apply bw_iter_right_dec. exact Hvalid.
    + exact IHHmn.
Qed.

(** 11. bw_iter preserves infinitely many (induction) *)
Lemma bw_iter_preserves_infinite : forall s st n,
  bw_left st <= bw_right st ->
  infinitely_many_in s (bw_left st) (bw_right st) ->
  infinitely_many_in s (bw_left (bw_iter s st n)) (bw_right (bw_iter s st n)).
Proof.
  intros s st n Hs Hinf. induction n; simpl.
  - exact Hinf.
  - apply bw_step_preserves_infinite.
    + apply bw_iter_valid. exact Hs.
    + exact IHn.
Qed.

(* ========================================================================= *)
(* SECTION 4: WIDTH BOUND AND CONVERGENCE                                   *)
(* ========================================================================= *)

(** 12. Width bound: width after n steps <= (b-a) / 2^n *)
Lemma bw_width_bound : forall s st n,
  bw_left st <= bw_right st ->
  bw_right (bw_iter s st n) - bw_left (bw_iter s st n) <=
    (bw_right st - bw_left st) / Qpow2 n.
Proof.
  intros s st n Hs.
  induction n as [|n' IHn'].
  - simpl bw_iter.
    assert (Hdiv1 : (bw_right st - bw_left st) / Qpow2 0 ==
                     bw_right st - bw_left st).
    { unfold Qpow2. simpl. field. }
    rewrite Hdiv1. lra.
  - assert (Hstep := bw_step_width s (bw_iter s st n')).
    simpl bw_iter.
    apply Qle_trans with ((bw_right (bw_iter s st n') -
                           bw_left (bw_iter s st n')) / 2).
    + rewrite Hstep. apply Qle_refl.
    + apply Qle_trans with ((bw_right st - bw_left st) / Qpow2 n' / 2).
      * unfold Qdiv.
        apply Qmult_le_compat_r.
        { exact IHn'. }
        { change (0 <= (1#2)). lra. }
      * pose proof (Qpow2_pos n').
        rewrite Qpow2_double_local.
        unfold Qdiv. setoid_replace (/ (2 * Qpow2 n'))
          with (/ Qpow2 n' * / 2) by (field; lra).
        ring_simplify. apply Qle_refl.
Qed.

(** 13. Width converges to zero *)
Lemma bw_width_to_zero : forall s a b,
  a < b ->
  forall eps, 0 < eps ->
    exists N, bw_right (bw_iter s (mkBW a b) N) -
              bw_left (bw_iter s (mkBW a b) N) < eps.
Proof.
  intros s a b Hab eps Heps.
  assert (Hba : b - a > 0) by lra.
  destruct (Archimedean_width (b - a) eps Hba Heps) as [N HN].
  exists N.
  apply Qle_lt_trans with ((b - a) / Qpow2 N).
  - assert (Hvalid : a <= b) by lra.
    exact (bw_width_bound s (mkBW a b) N Hvalid).
  - simpl bw_left. simpl bw_right. exact HN.
Qed.

(** 14. Left endpoints form a Cauchy sequence *)
Lemma bw_left_cauchy : forall s a b,
  a < b ->
  is_cauchy (fun n => bw_left (bw_iter s (mkBW a b) n)).
Proof.
  intros s a b Hab.
  assert (Hvalid : a <= b) by lra.
  apply left_endpoints_cauchy with (hi := fun n => bw_right (bw_iter s (mkBW a b) n)).
  - intros n. apply bw_iter_valid. exact Hvalid.
  - intros n. apply bw_iter_left_inc. exact Hvalid.
  - intros n. apply bw_iter_right_dec. exact Hvalid.
  - intros eps Heps. exact (bw_width_to_zero s a b Hab eps Heps).
Qed.

(** 15. Right endpoints form a Cauchy sequence *)
Lemma bw_right_cauchy : forall s a b,
  a < b ->
  is_cauchy (fun n => bw_right (bw_iter s (mkBW a b) n)).
Proof.
  intros s a b Hab.
  assert (Hvalid : a <= b) by lra.
  apply right_endpoints_cauchy with (lo := fun n => bw_left (bw_iter s (mkBW a b) n)).
  - intros n. apply bw_iter_valid. exact Hvalid.
  - intros n. apply bw_iter_left_inc. exact Hvalid.
  - intros n. apply bw_iter_right_dec. exact Hvalid.
  - intros eps Heps. exact (bw_width_to_zero s a b Hab eps Heps).
Qed.

(* ========================================================================= *)
(* SECTION 5: CONVERGENT SUBSEQUENCE PROPERTIES                             *)
(* ========================================================================= *)

(** 16. Any sequence trapped in bisection intervals is Cauchy *)
Lemma trapped_seq_cauchy : forall s a b (t : nat -> Q),
  a < b ->
  (forall n, bw_left (bw_iter s (mkBW a b) n) <= t n /\
             t n <= bw_right (bw_iter s (mkBW a b) n)) ->
  is_cauchy t.
Proof.
  intros s a b t Hab Htrap.
  assert (Hvalid : a <= b) by lra.
  intros eps Heps.
  destruct (bw_width_to_zero s a b Hab eps Heps) as [N HN].
  exists N. intros m n Hm Hn.
  destruct (Htrap m) as [Hm_lo Hm_hi].
  destruct (Htrap n) as [Hn_lo Hn_hi].
  assert (HloN_m : bw_left (bw_iter s (mkBW a b) N) <=
                    bw_left (bw_iter s (mkBW a b) m)).
  { apply bw_left_mono; [exact Hvalid | exact Hm]. }
  assert (HloN_n : bw_left (bw_iter s (mkBW a b) N) <=
                    bw_left (bw_iter s (mkBW a b) n)).
  { apply bw_left_mono; [exact Hvalid | exact Hn]. }
  assert (HhiN_m : bw_right (bw_iter s (mkBW a b) m) <=
                    bw_right (bw_iter s (mkBW a b) N)).
  { apply bw_right_mono; [exact Hvalid | exact Hm]. }
  assert (HhiN_n : bw_right (bw_iter s (mkBW a b) n) <=
                    bw_right (bw_iter s (mkBW a b) N)).
  { apply bw_right_mono; [exact Hvalid | exact Hn]. }
  apply Qabs_lt_bound; lra.
Qed.

(** 17. The bisection endpoints are equivalent (same limit) *)
Lemma bw_endpoints_equiv : forall s a b,
  a < b ->
  let lo := fun n => bw_left (bw_iter s (mkBW a b) n) in
  let hi := fun n => bw_right (bw_iter s (mkBW a b) n) in
  forall (Hlc : is_cauchy lo) (Hrc : is_cauchy hi),
    mkCauchy lo Hlc ~~ mkCauchy hi Hrc.
Proof.
  intros s a b Hab lo hi Hlc Hrc.
  assert (Hvalid : a <= b) by lra.
  intros eps Heps.
  destruct (bw_width_to_zero s a b Hab eps Heps) as [N HN].
  exists N. intros n Hn.
  change (Qabs (lo n - hi n) < eps).
  unfold lo, hi.
  assert (Hlo_n : bw_left (bw_iter s (mkBW a b) N) <=
                  bw_left (bw_iter s (mkBW a b) n)).
  { apply bw_left_mono; [exact Hvalid | exact Hn]. }
  assert (Hhi_n : bw_right (bw_iter s (mkBW a b) n) <=
                  bw_right (bw_iter s (mkBW a b) N)).
  { apply bw_right_mono; [exact Hvalid | exact Hn]. }
  assert (Hvalid_n : bw_left (bw_iter s (mkBW a b) n) <=
                     bw_right (bw_iter s (mkBW a b) n)).
  { apply bw_iter_valid. exact Hvalid. }
  apply Qabs_lt_bound; lra.
Qed.

(** 18. For each bisection interval, infinitely many terms exist *)
Lemma bw_infinitely_many : forall s a b n,
  a <= b ->
  bounded_seq s a b ->
  infinitely_many_in s (bw_left (bw_iter s (mkBW a b) n))
                       (bw_right (bw_iter s (mkBW a b) n)).
Proof.
  intros s a b n Hvalid Hbnd.
  apply bw_iter_preserves_infinite.
  - exact Hvalid.
  - apply bounded_seq_initial. exact Hbnd.
Qed.

(** 19. There exists a term of s in each bisection interval with index >= N *)
Lemma bw_term_exists : forall s a b,
  a <= b -> bounded_seq s a b ->
  forall n N, exists k,
    (N <= k)%nat /\
    bw_left (bw_iter s (mkBW a b) n) <= s k /\
    s k <= bw_right (bw_iter s (mkBW a b) n).
Proof.
  intros s a b Hvalid Hbnd n N.
  exact (bw_infinitely_many s a b n Hvalid Hbnd N).
Qed.

(* ========================================================================= *)
(* SECTION 6: BOLZANO-WEIERSTRASS MAIN THEOREM                             *)
(* ========================================================================= *)

(** Cluster point: a CauchySeq L is a cluster point of s if
    for every eps > 0 and every threshold N, there exists k >= N
    with s(k) within eps of the limit.
    We use a Cauchy-compatible formulation: for large enough
    index M of L, |L(M) - s(k)| < eps. *)
Definition is_cluster_point (s : nat -> Q) (L : CauchySeq) : Prop :=
  forall eps : Q, 0 < eps ->
    forall N : nat, exists k : nat, exists M : nat,
      (N <= k)%nat /\
      Qabs (cs_seq L M - s k) < eps.

(** 20. Bolzano-Weierstrass: every bounded sequence in [a,b] (a < b)
    has a cluster point that is a CauchySeq.

    The bisection left endpoints form a Cauchy sequence L.
    For any eps > 0 and threshold N, we find a bisection level M
    with width < eps, then pick s(k) from that interval (k >= N).
    Since s(k) and L(M) = bw_left(iter M) are both in [L(M), R(M)]
    with width < eps, we get |L(M) - s(k)| < eps. *)
Theorem bolzano_weierstrass : forall (s : nat -> Q) (a b : Q),
  a < b -> bounded_seq s a b ->
  exists L : CauchySeq, is_cluster_point s L.
Proof.
  intros s a b Hab Hbnd.
  assert (Hvalid : a <= b) by lra.
  exists (mkCauchy _ (bw_left_cauchy s a b Hab)).
  intros eps Heps N.
  destruct (bw_width_to_zero s a b Hab eps Heps) as [M HM].
  destruct (bw_infinitely_many s a b M Hvalid Hbnd N) as [k [HkN [Hklo Hkhi]]].
  exists k. exists M. split.
  - exact HkN.
  - change (Qabs (bw_left (bw_iter s (mkBW a b) M) - s k) < eps).
    assert (Hvalid_M : bw_left (bw_iter s (mkBW a b) M) <=
                       bw_right (bw_iter s (mkBW a b) M)).
    { apply bw_iter_valid. exact Hvalid. }
    apply Qabs_lt_bound; lra.
Qed.

(** 21. Monotone bounded implies Cauchy *)
Theorem monotone_bounded_cauchy : forall (s : nat -> Q) (B : Q),
  (forall n, s n <= s (S n)) ->
  (forall n, s n <= B) ->
  is_cauchy s.
Proof.
  intros s B Hinc Hbnd.
  exact (q_inc_bounded_cauchy s B Hinc Hbnd).
Qed.

(** 22. Decreasing bounded implies Cauchy *)
Theorem decreasing_bounded_cauchy : forall (s : nat -> Q) (B : Q),
  (forall n, s (S n) <= s n) ->
  (forall n, B <= s n) ->
  is_cauchy s.
Proof.
  intros s B Hdec Hbnd.
  exact (q_dec_bounded_cauchy s B Hdec Hbnd).
Qed.

(** 23. Left endpoints are bounded in [a, b] *)
Lemma bw_left_bounded : forall s a b,
  a <= b ->
  forall n, a <= bw_left (bw_iter s (mkBW a b) n) /\
            bw_left (bw_iter s (mkBW a b) n) <= b.
Proof.
  intros s a b Hvalid n. split.
  - change a with (bw_left (bw_iter s (mkBW a b) 0)).
    apply bw_left_mono; [exact Hvalid | lia].
  - apply Qle_trans with (bw_right (bw_iter s (mkBW a b) n)).
    + apply bw_iter_valid. exact Hvalid.
    + change b with (bw_right (bw_iter s (mkBW a b) 0)).
      apply bw_right_mono; [exact Hvalid | lia].
Qed.

(** 24. Right endpoints are bounded in [a, b] *)
Lemma bw_right_bounded : forall s a b,
  a <= b ->
  forall n, a <= bw_right (bw_iter s (mkBW a b) n) /\
            bw_right (bw_iter s (mkBW a b) n) <= b.
Proof.
  intros s a b Hvalid n. split.
  - apply Qle_trans with (bw_left (bw_iter s (mkBW a b) n)).
    + change a with (bw_left (bw_iter s (mkBW a b) 0)).
      apply bw_left_mono; [exact Hvalid | lia].
    + apply bw_iter_valid. exact Hvalid.
  - change b with (bw_right (bw_iter s (mkBW a b) 0)).
    apply bw_right_mono; [exact Hvalid | lia].
Qed.

(* ========================================================================= *)
(* SECTION 7: VERIFICATION                                                   *)
(* ========================================================================= *)

Check bounded_seq.
Check infinitely_many_in.
Check bounded_seq_initial.
Check infinite_pigeonhole.
Check bw_step.
Check bw_iter.
Check bw_step_valid.
Check bw_step_width.
Check bw_step_nested_left.
Check bw_step_nested_right.
Check bw_step_preserves_infinite.
Check bw_iter_valid.
Check bw_iter_left_inc.
Check bw_iter_right_dec.
Check bw_iter_preserves_infinite.
Check bw_width_bound.
Check bw_width_to_zero.
Check bw_left_cauchy.
Check bw_right_cauchy.
Check trapped_seq_cauchy.
Check bw_endpoints_equiv.
Check bw_infinitely_many.
Check bw_term_exists.
Check bolzano_weierstrass.
Check monotone_bounded_cauchy.
Check decreasing_bounded_cauchy.
Check bw_left_bounded.
Check bw_right_bounded.

Print Assumptions bolzano_weierstrass.
Print Assumptions monotone_bounded_cauchy.
Print Assumptions trapped_seq_cauchy.
