(* ========================================================================= *)
(*            COMPLETENESS OF CAUCHY REALS                                   *)
(*                                                                           *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)         *)
(*                                                                           *)
(*  PURPOSE: Prove completeness properties of the Cauchy real construction:  *)
(*    1. Nested Interval Property (NIP)                                      *)
(*    2. Constructive Sup via Bisection                                      *)
(*    3. Metric Completeness (diagonal construction)                         *)
(*                                                                           *)
(*  AXIOMS: NONE - fully constructive over Q                                 *)
(*                                                                           *)
(*  Author: Horsocrates | Date: March 2026                                   *)
(* ========================================================================= *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qminmax.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.Pnat.

From ToS Require Import Archimedean_ERR.
From ToS Require Import CauchyReal.
From ToS Require Import RealField.

Open Scope Q_scope.
Local Open Scope cauchy_scope.

(* ========================================================================= *)
(* HELPERS: Qabs bounds                                                       *)
(* ========================================================================= *)

(** Qeq implies Qle *)
Lemma Qeq_Qle : forall x y : Q, x == y -> x <= y.
Proof. intros [xn xd] [yn yd]. unfold Qeq, Qle. lia. Qed.

(** Bound Qabs from split bounds (strict) *)
Lemma Qabs_lt_bound : forall x y : Q,
  -y < x -> x < y -> Qabs x < y.
Proof.
  intros x y Hlo Hhi.
  destruct (Qlt_le_dec x 0) as [Hneg | Hpos].
  - apply Qle_lt_trans with (-x).
    + apply Qeq_Qle. apply Qabs_neg. lra.
    + lra.
  - apply Qle_lt_trans with x.
    + apply Qeq_Qle. apply Qabs_pos. exact Hpos.
    + exact Hhi.
Qed.

(** Bound Qabs from split bounds (non-strict) *)
Lemma Qabs_le_bound : forall x y : Q,
  -y <= x -> x <= y -> Qabs x <= y.
Proof.
  intros x y Hlo Hhi.
  destruct (Qlt_le_dec x 0) as [Hneg | Hpos].
  - apply Qle_trans with (-x).
    + apply Qeq_Qle. apply Qabs_neg. lra.
    + lra.
  - apply Qle_trans with x.
    + apply Qeq_Qle. apply Qabs_pos. exact Hpos.
    + exact Hhi.
Qed.

(* ========================================================================= *)
(* SECTION 1: NESTED INTERVAL PROPERTY                                       *)
(* ========================================================================= *)

(** Monotonicity of increasing nat-indexed sequences *)
Lemma increasing_mono : forall (f : nat -> Q),
  (forall n, f n <= f (S n)) ->
  forall a b, (a <= b)%nat -> f a <= f b.
Proof.
  intros f Hf a b Hab.
  induction Hab.
  - apply Qle_refl.
  - apply Qle_trans with (f m); [exact IHHab | apply Hf].
Qed.

(** Monotonicity of decreasing nat-indexed sequences *)
Lemma decreasing_mono : forall (f : nat -> Q),
  (forall n, f (S n) <= f n) ->
  forall a b, (a <= b)%nat -> f b <= f a.
Proof.
  intros f Hf a b Hab.
  induction Hab.
  - apply Qle_refl.
  - apply Qle_trans with (f m); [apply Hf | exact IHHab].
Qed.

(** Left endpoints of nested intervals form a Cauchy sequence *)
Lemma left_endpoints_cauchy : forall (lo hi : nat -> Q),
  (forall n, lo n <= hi n) ->
  (forall n, lo n <= lo (S n)) ->
  (forall n, hi (S n) <= hi n) ->
  (forall eps, 0 < eps -> exists N, hi N - lo N < eps) ->
  is_cauchy lo.
Proof.
  intros lo hi Hvalid Hlo_inc Hhi_dec Hwidth eps Heps.
  destruct (Hwidth eps Heps) as [N HN].
  exists N.
  intros m n Hm Hn.
  (* lo(m), lo(n) ∈ [lo(N), hi(N)] *)
  assert (lo N <= lo m) by (apply increasing_mono; [exact Hlo_inc | lia]).
  assert (lo N <= lo n) by (apply increasing_mono; [exact Hlo_inc | lia]).
  assert (lo m <= hi N).
  { apply Qle_trans with (hi m);
      [apply Hvalid | apply decreasing_mono; [exact Hhi_dec | lia]]. }
  assert (lo n <= hi N).
  { apply Qle_trans with (hi n);
      [apply Hvalid | apply decreasing_mono; [exact Hhi_dec | lia]]. }
  apply Qabs_lt_bound; lra.
Qed.

(** Right endpoints of nested intervals form a Cauchy sequence *)
Lemma right_endpoints_cauchy : forall (lo hi : nat -> Q),
  (forall n, lo n <= hi n) ->
  (forall n, lo n <= lo (S n)) ->
  (forall n, hi (S n) <= hi n) ->
  (forall eps, 0 < eps -> exists N, hi N - lo N < eps) ->
  is_cauchy hi.
Proof.
  intros lo hi Hvalid Hlo_inc Hhi_dec Hwidth eps Heps.
  destruct (Hwidth eps Heps) as [N HN].
  exists N.
  intros m n Hm Hn.
  assert (lo N <= hi m).
  { apply Qle_trans with (lo m);
      [apply increasing_mono; [exact Hlo_inc | lia] | apply Hvalid]. }
  assert (lo N <= hi n).
  { apply Qle_trans with (lo n);
      [apply increasing_mono; [exact Hlo_inc | lia] | apply Hvalid]. }
  assert (hi m <= hi N) by (apply decreasing_mono; [exact Hhi_dec | lia]).
  assert (hi n <= hi N) by (apply decreasing_mono; [exact Hhi_dec | lia]).
  apply Qabs_lt_bound; lra.
Qed.

(** The CauchySeqs from lo and hi are equivalent *)
Lemma endpoints_equiv : forall (lo hi : nat -> Q)
  (Hvalid : forall n, lo n <= hi n)
  (Hlo_inc : forall n, lo n <= lo (S n))
  (Hhi_dec : forall n, hi (S n) <= hi n)
  (Hwidth : forall eps, 0 < eps -> exists N, hi N - lo N < eps),
  mkCauchy lo (left_endpoints_cauchy lo hi Hvalid Hlo_inc Hhi_dec Hwidth) ~~
  mkCauchy hi (right_endpoints_cauchy lo hi Hvalid Hlo_inc Hhi_dec Hwidth).
Proof.
  intros lo hi Hvalid Hlo_inc Hhi_dec Hwidth eps Heps.
  destruct (Hwidth eps Heps) as [N HN].
  exists N.
  intros n Hn.
  change (Qabs (lo n - hi n) < eps).
  assert (lo N <= lo n) by (apply increasing_mono; [exact Hlo_inc | lia]).
  assert (hi n <= hi N) by (apply decreasing_mono; [exact Hhi_dec | lia]).
  assert (lo n <= hi n) by apply Hvalid.
  apply Qabs_lt_bound; lra.
Qed.

(** Main Nested Interval Property:
    Nested intervals with shrinking widths determine a unique CauchySeq *)
Theorem nested_interval_limit : forall (lo hi : nat -> Q)
  (Hvalid : forall n, lo n <= hi n)
  (Hlo_inc : forall n, lo n <= lo (S n))
  (Hhi_dec : forall n, hi (S n) <= hi n)
  (Hwidth : forall eps, 0 < eps -> exists N, hi N - lo N < eps),
  exists L : CauchySeq,
    (forall n, cauchy_le (cauchy_const (lo n)) L) /\
    (forall n, cauchy_le L (cauchy_const (hi n))).
Proof.
  intros.
  exists (mkCauchy lo (left_endpoints_cauchy lo hi Hvalid Hlo_inc Hhi_dec Hwidth)).
  split.
  - (* cauchy_const (lo n) ≤ L = mkCauchy lo ... *)
    intros n eps Heps.
    exists n.
    intros m Hm.
    simpl.
    assert (lo n <= lo m) by (apply increasing_mono; [exact Hlo_inc | lia]).
    lra.
  - (* L ≤ cauchy_const (hi n) *)
    intros n eps Heps.
    exists n.
    intros m Hm.
    simpl.
    assert (lo m <= hi m) by apply Hvalid.
    assert (hi m <= hi n) by (apply decreasing_mono; [exact Hhi_dec | lia]).
    lra.
Qed.

(* ========================================================================= *)
(* SECTION 2: CONSTRUCTIVE SUP VIA BISECTION                                 *)
(*                                                                           *)
(*  Given a decidable predicate P : Q -> bool with P(a)=false, P(b)=true,   *)
(*  produce a CauchySeq at the transition point of P.                        *)
(* ========================================================================= *)

(** Local bisection state (avoids importing IVT_ERR which requires Classical) *)
Record SupBisectState := mkSupBisect {
  sb_left : Q;
  sb_right : Q
}.

Definition sup_bisect_step (P : Q -> bool) (s : SupBisectState) : SupBisectState :=
  let mid := (sb_left s + sb_right s) / 2 in
  if P mid then mkSupBisect (sb_left s) mid
           else mkSupBisect mid (sb_right s).

Fixpoint sup_bisect_iter (P : Q -> bool) (s : SupBisectState) (n : nat)
  : SupBisectState :=
  match n with
  | O => s
  | S n' => sup_bisect_step P (sup_bisect_iter P s n')
  end.

(** Helper: rewrite /2 to *(1#2) for lra (lra can't handle Qdiv) *)
Ltac qdiv2_lra :=
  repeat match goal with
  | |- context [?x / 2] =>
      setoid_replace (x / 2) with (x * (1#2)) by field
  end; lra.

(** Interval validity is preserved *)
Lemma sup_bisect_step_valid : forall P s,
  sb_left s <= sb_right s ->
  sb_left (sup_bisect_step P s) <= sb_right (sup_bisect_step P s).
Proof.
  intros P [l r] Hlr. change (l <= r) in Hlr.
  unfold sup_bisect_step. cbv zeta. cbn [sb_left sb_right].
  destruct (P ((l + r) / 2)); cbn [sb_left sb_right]; qdiv2_lra.
Qed.

Lemma sup_bisect_iter_valid : forall P s n,
  sb_left s <= sb_right s ->
  sb_left (sup_bisect_iter P s n) <= sb_right (sup_bisect_iter P s n).
Proof.
  intros P s n Hs. induction n; simpl.
  - exact Hs.
  - apply sup_bisect_step_valid. exact IHn.
Qed.

(** Width halves at each step *)
Lemma sup_bisect_step_width : forall P s,
  sb_right (sup_bisect_step P s) - sb_left (sup_bisect_step P s) ==
  (sb_right s - sb_left s) / 2.
Proof.
  intros P [l r]. unfold sup_bisect_step. cbv zeta. cbn [sb_left sb_right].
  destruct (P ((l + r) / 2)); cbn [sb_left sb_right]; field.
Qed.

(** Left endpoints increase *)
Lemma sup_bisect_left_inc : forall P s,
  sb_left s <= sb_right s ->
  sb_left s <= sb_left (sup_bisect_step P s).
Proof.
  intros P [l r] Hlr. change (l <= r) in Hlr.
  unfold sup_bisect_step. cbv zeta. cbn [sb_left sb_right].
  destruct (P ((l + r) / 2)); cbn [sb_left sb_right]; qdiv2_lra.
Qed.

(** Right endpoints decrease *)
Lemma sup_bisect_right_dec : forall P s,
  sb_left s <= sb_right s ->
  sb_right (sup_bisect_step P s) <= sb_right s.
Proof.
  intros P [l r] Hlr. change (l <= r) in Hlr.
  unfold sup_bisect_step. cbv zeta. cbn [sb_left sb_right].
  destruct (P ((l + r) / 2)); cbn [sb_left sb_right]; qdiv2_lra.
Qed.

(** Iteration monotonicity *)
Lemma sup_bisect_iter_left_inc : forall P s n,
  sb_left s <= sb_right s ->
  sb_left (sup_bisect_iter P s n) <= sb_left (sup_bisect_iter P s (S n)).
Proof.
  intros P s n Hs. simpl.
  apply sup_bisect_left_inc.
  apply sup_bisect_iter_valid. exact Hs.
Qed.

Lemma sup_bisect_iter_right_dec : forall P s n,
  sb_left s <= sb_right s ->
  sb_right (sup_bisect_iter P s (S n)) <= sb_right (sup_bisect_iter P s n).
Proof.
  intros P s n Hs. simpl.
  apply sup_bisect_right_dec.
  apply sup_bisect_iter_valid. exact Hs.
Qed.

(** P-preservation: P stays false on left, true on right *)
Lemma sup_bisect_preserves_P : forall P a b n,
  P a = false -> P b = true ->
  P (sb_left (sup_bisect_iter P (mkSupBisect a b) n)) = false /\
  P (sb_right (sup_bisect_iter P (mkSupBisect a b) n)) = true.
Proof.
  intros P a b n HPa HPb.
  induction n as [|n' [IHl IHr]]; simpl.
  - split; assumption.
  - unfold sup_bisect_step.
    set (s := sup_bisect_iter P (mkSupBisect a b) n').
    set (mid := (sb_left s + sb_right s) / 2).
    destruct (P mid) eqn:Hmid; simpl; split.
    + exact IHl.
    + exact Hmid.
    + exact Hmid.
    + exact IHr.
Qed.

(** Local Qpow2 doubling lemma *)
Lemma Qpow2_double_local : forall n, Qpow2 (S n) == 2 * Qpow2 n.
Proof.
  intros n. unfold Qeq, Qpow2, Qmult. simpl.
  rewrite Pos2Z.inj_xO. lia.
Qed.

(** Width bound: width after n steps ≤ initial_width / 2^n *)
Lemma sup_bisect_width_bound : forall P s n,
  sb_left s <= sb_right s ->
  sb_right (sup_bisect_iter P s n) - sb_left (sup_bisect_iter P s n) <=
    (sb_right s - sb_left s) / Qpow2 n.
Proof.
  intros P s n Hs.
  induction n as [|n' IHn'].
  - simpl sup_bisect_iter.
    assert (Hdiv1 : (sb_right s - sb_left s) / Qpow2 0 ==
                     sb_right s - sb_left s).
    { unfold Qpow2. simpl. field. }
    rewrite Hdiv1. lra.
  - (* width(n'+1) == width(n') / 2 ≤ (initial / 2^n') / 2 = initial / 2^(S n') *)
    assert (Hstep := sup_bisect_step_width P (sup_bisect_iter P s n')).
    (* width(S n') == width(n') / 2 *)
    simpl sup_bisect_iter.
    (* Now goal: sb_right (step ...) - sb_left (step ...) ≤ (b-a) / Qpow2 (S n') *)
    apply Qle_trans with ((sb_right (sup_bisect_iter P s n') -
                           sb_left (sup_bisect_iter P s n')) / 2).
    + (* width(step s') == width(s') / 2 → width(step s') ≤ width(s') / 2 *)
      rewrite Hstep. apply Qle_refl.
    + (* width(n') / 2 ≤ (initial / 2^n') / 2 = initial / 2^(S n') *)
      apply Qle_trans with ((sb_right s - sb_left s) / Qpow2 n' / 2).
      * (* width(n') ≤ initial / 2^n' → width(n')/2 ≤ (initial/2^n')/2 *)
        unfold Qdiv.
        apply Qmult_le_compat_r.
        { exact IHn'. }
        { change (0 <= (1#2)). lra. }
      * (* (initial / 2^n') / 2 == initial / 2^(S n') *)
        pose proof (Qpow2_pos n').
        rewrite Qpow2_double_local.
        unfold Qdiv. setoid_replace (/ (2 * Qpow2 n'))
          with (/ Qpow2 n' * / 2) by (field; lra).
        ring_simplify. apply Qle_refl.
Qed.

(** Width converges to 0 *)
Lemma sup_bisect_width_to_zero : forall P a b,
  a < b ->
  forall eps, 0 < eps ->
    exists N, sb_right (sup_bisect_iter P (mkSupBisect a b) N) -
              sb_left (sup_bisect_iter P (mkSupBisect a b) N) < eps.
Proof.
  intros P a b Hab eps Heps.
  assert (Hba : b - a > 0) by lra.
  destruct (Archimedean_width (b - a) eps Hba Heps) as [N HN].
  exists N.
  apply Qle_lt_trans with ((b - a) / Qpow2 N).
  - assert (Hvalid : a <= b) by lra.
    exact (sup_bisect_width_bound P (mkSupBisect a b) N Hvalid).
  - simpl sb_left. simpl sb_right. exact HN.
Qed.

(** Main theorem: bisection produces a CauchySeq at the transition point *)
Theorem sup_bisect_cauchy : forall (P : Q -> bool) (a b : Q),
  a < b -> P a = false -> P b = true ->
  exists L : CauchySeq,
    cauchy_le (cauchy_const a) L /\
    cauchy_le L (cauchy_const b) /\
    (forall n, P (sb_left (sup_bisect_iter P (mkSupBisect a b) n)) = false) /\
    (forall n, P (sb_right (sup_bisect_iter P (mkSupBisect a b) n)) = true).
Proof.
  intros P a b Hab HPa HPb.
  set (lo := fun n => sb_left (sup_bisect_iter P (mkSupBisect a b) n)).
  set (hi := fun n => sb_right (sup_bisect_iter P (mkSupBisect a b) n)).
  assert (Hvalid : forall n, lo n <= hi n).
  { intros n. unfold lo, hi. apply sup_bisect_iter_valid.
    cbn [sb_left sb_right]. lra. }
  assert (Hab_le : a <= b) by lra.
  assert (Hlo_inc : forall n, lo n <= lo (S n)).
  { intros n. unfold lo. apply sup_bisect_iter_left_inc. exact Hab_le. }
  assert (Hhi_dec : forall n, hi (S n) <= hi n).
  { intros n. unfold hi. apply sup_bisect_iter_right_dec. exact Hab_le. }
  assert (Hwidth : forall eps, 0 < eps -> exists N, hi N - lo N < eps).
  { intros eps Heps. unfold lo, hi.
    exact (sup_bisect_width_to_zero P a b Hab eps Heps). }
  destruct (nested_interval_limit lo hi Hvalid Hlo_inc Hhi_dec Hwidth) as [L [HL_lo HL_hi]].
  exists L.
  split; [| split; [| split]].
  - (* cauchy_const a ≤ L *)
    exact (HL_lo 0%nat).
  - (* L ≤ cauchy_const b *)
    exact (HL_hi 0%nat).
  - (* P left = false *)
    intros n. exact (proj1 (sup_bisect_preserves_P P a b n HPa HPb)).
  - (* P right = true *)
    intros n. exact (proj2 (sup_bisect_preserves_P P a b n HPa HPb)).
Qed.

(* ========================================================================= *)
(* SECTION 3: METRIC COMPLETENESS                                            *)
(*                                                                           *)
(*  A sequence of CauchySeqs that is "meta-Cauchy" converges to a CauchySeq  *)
(*  via the diagonal construction: L(n) = s(n)(n).                           *)
(* ========================================================================= *)

(** Two CauchySeqs are within eps of each other *)
Definition cauchy_close (a b : CauchySeq) (eps : Q) : Prop :=
  exists N : nat, forall n : nat,
    (N <= n)%nat -> Qabs (cs_seq a n - cs_seq b n) < eps.

(** Meta-Cauchy: a sequence of CauchySeqs where N works uniformly
    for both individual Cauchy rates and cross-sequence closeness *)
Definition meta_cauchy (s : nat -> CauchySeq) : Prop :=
  forall eps : Q, 0 < eps ->
    exists N : nat,
      (* Equi-Cauchy: each s(k) with k >= N has Cauchy rate bounded by N *)
      (forall k m n : nat,
        (N <= k)%nat -> (N <= m)%nat -> (N <= n)%nat ->
        Qabs (cs_seq (s k) m - cs_seq (s k) n) < eps) /\
      (* Cross-closeness: different sequences are pointwise close *)
      (forall k l n : nat,
        (N <= k)%nat -> (N <= l)%nat -> (N <= n)%nat ->
        Qabs (cs_seq (s k) n - cs_seq (s l) n) < eps).

(** The diagonal L(n) = s(n)(n) is Cauchy when s is meta-Cauchy *)
Lemma diagonal_is_cauchy : forall (s : nat -> CauchySeq),
  meta_cauchy s -> is_cauchy (fun n => cs_seq (s n) n).
Proof.
  intros s Hmeta eps Heps.
  assert (Heps2 : 0 < eps * (1#2)) by lra.
  destruct (Hmeta (eps * (1#2)) Heps2) as [N [Hequi Hcross]].
  exists N.
  intros m n Hm Hn.
  (* |s(m)(m) - s(n)(n)| ≤ |s(m)(m) - s(m)(n)| + |s(m)(n) - s(n)(n)| *)
  assert (Hdecomp :
    cs_seq (s m) m - cs_seq (s n) n ==
    (cs_seq (s m) m - cs_seq (s m) n) + (cs_seq (s m) n - cs_seq (s n) n)) by ring.
  qabs_rw Hdecomp.
  apply Qle_lt_trans with
    (Qabs (cs_seq (s m) m - cs_seq (s m) n) +
     Qabs (cs_seq (s m) n - cs_seq (s n) n)).
  { apply Qabs_triangle. }
  assert (H1 : Qabs (cs_seq (s m) m - cs_seq (s m) n) < eps * (1#2))
    by (apply Hequi; lia).
  assert (H2 : Qabs (cs_seq (s m) n - cs_seq (s n) n) < eps * (1#2))
    by (apply Hcross; lia).
  lra.
Qed.

(** Construct the limit CauchySeq from the diagonal *)
Definition diagonal_limit (s : nat -> CauchySeq) (H : meta_cauchy s) : CauchySeq :=
  mkCauchy (fun n => cs_seq (s n) n) (diagonal_is_cauchy s H).

(** The diagonal limit is indeed the limit of the sequence:
    for large k, s(k) is cauchy_close to L *)
Theorem diagonal_converges : forall (s : nat -> CauchySeq) (H : meta_cauchy s),
  forall eps : Q, 0 < eps ->
    exists K : nat, forall k : nat,
      (K <= k)%nat -> cauchy_close (s k) (diagonal_limit s H) eps.
Proof.
  intros s H eps Heps.
  destruct (H eps Heps) as [N [Hequi Hcross]].
  exists N.
  intros k Hk.
  (* cauchy_close (s k) L eps = exists M, forall n >= M, |s(k)(n) - L(n)| < eps *)
  exists N.
  intros n Hn.
  simpl.
  (* |s(k)(n) - s(n)(n)| < eps, from cross-closeness with k, n ≥ N *)
  exact (Hcross k n n Hk Hn Hn).
Qed.

(** meta_cauchy implies the individual sequences are Cauchy
    (sanity check — follows from equi-Cauchy part) *)
Lemma meta_cauchy_each_cauchy : forall (s : nat -> CauchySeq) (k : nat),
  meta_cauchy s -> is_cauchy (cs_seq (s k)).
Proof.
  intros s k Hmeta. exact (cs_cauchy (s k)).
Qed.

(* ========================================================================= *)
(* SECTION 4: VERIFICATION                                                    *)
(* ========================================================================= *)

Check increasing_mono.
Check decreasing_mono.
Check left_endpoints_cauchy.
Check right_endpoints_cauchy.
Check endpoints_equiv.
Check nested_interval_limit.

Check sup_bisect_step.
Check sup_bisect_iter.
Check sup_bisect_step_valid.
Check sup_bisect_iter_valid.
Check sup_bisect_step_width.
Check sup_bisect_left_inc.
Check sup_bisect_right_dec.
Check sup_bisect_preserves_P.
Check sup_bisect_width_bound.
Check sup_bisect_width_to_zero.
Check sup_bisect_cauchy.

Check cauchy_close.
Check meta_cauchy.
Check diagonal_is_cauchy.
Check diagonal_limit.
Check diagonal_converges.
Check meta_cauchy_each_cauchy.

Print Assumptions left_endpoints_cauchy.
Print Assumptions nested_interval_limit.
Print Assumptions sup_bisect_cauchy.
Print Assumptions diagonal_is_cauchy.
Print Assumptions diagonal_converges.
