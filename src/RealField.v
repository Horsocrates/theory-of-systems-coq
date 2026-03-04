(* ========================================================================= *)
(*            REAL FIELD: MULTIPLICATION AND FIELD STRUCTURE                *)
(*                                                                         *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)       *)
(*                                                                         *)
(*  PURPOSE: Extend CauchyReal.v with multiplication, multiplicative       *)
(*  inverse, and ordered field laws — completing the construction of R      *)
(*  as an ordered field from Cauchy sequences of rationals.                *)
(*                                                                         *)
(*  CONTENTS:                                                              *)
(*    1. Helpers: Qabs_Qmult, Qdiv_lt_from_mul, cauchy_bounded            *)
(*    2. Multiplication: cauchy_mul + is_cauchy proof                      *)
(*    3. Multiplication respects equivalence: cauchy_mul_compat            *)
(*    4. Ring laws: mul_comm, mul_assoc, mul_one_r, distrib_l             *)
(*    5. Multiplicative inverse: cauchy_inv, cauchy_mul_inv_r             *)
(*    6. Ordered field: cauchy_pos_add, cauchy_pos_mul                    *)
(*                                                                         *)
(*  AXIOMS: NONE - fully constructive over Q                               *)
(*                                                                         *)
(*  Author: Horsocrates | Date: March 2026                                 *)
(* ========================================================================= *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qminmax.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.

From ToS Require Import CauchyReal.

Open Scope Q_scope.
Local Open Scope cauchy_scope.

(* ========================================================================= *)
(* SECTION 1: HELPERS                                                        *)
(* ========================================================================= *)

(** |x * y| == |x| * |y|  —  proved at Z level via Z.abs_mul *)
Lemma Qabs_Qmult : forall x y : Q, Qabs (x * y) == Qabs x * Qabs y.
Proof.
  intros [xn xd] [yn yd].
  unfold Qeq, Qabs, Qmult. simpl.
  rewrite Z.abs_mul. lia.
Qed.

(** If a < b * c with c > 0, then a / c < b *)
Lemma Qdiv_lt_from_mul : forall a b c : Q,
  0 < c -> a < b * c -> a * / c < b.
Proof.
  intros a b c Hc Hlt.
  assert (Hic : 0 < / c) by (apply Qinv_lt_0_compat; exact Hc).
  assert (H : a * / c < b * c * / c).
  { apply Qmult_lt_compat_r; [exact Hic | exact Hlt]. }
  setoid_replace (b * c * / c) with b in H by (field; lra).
  exact H.
Qed.

(** Every Cauchy sequence is bounded: exists B > 0, forall n, |a(n)| <= B *)
Lemma cauchy_bounded : forall a : CauchySeq,
  exists B : Q, 0 < B /\
    forall n : nat, Qabs (cs_seq a n) <= B.
Proof.
  intros a.
  destruct (cs_cauchy a 1 ltac:(lra)) as [N HN].
  (* Prefix max for 0..N by induction *)
  assert (prefix_max : forall k : nat,
    exists M : Q, 0 <= M /\
      forall i : nat, (i <= k)%nat -> Qabs (cs_seq a i) <= M).
  { induction k as [|k' [M' [HM'pos HM']]].
    - exists (Qabs (cs_seq a 0)). split.
      + apply Qabs_nonneg.
      + intros i Hi. replace i with 0%nat by lia. apply Qle_refl.
    - exists (Qmax M' (Qabs (cs_seq a (S k')))). split.
      + apply Qle_trans with M'; [exact HM'pos | apply Q.le_max_l].
      + intros i Hi. destruct (Nat.eq_dec i (S k')) as [->|Hne].
        * apply Q.le_max_r.
        * apply Qle_trans with M'; [apply HM'; lia | apply Q.le_max_l]. }
  destruct (prefix_max N) as [M [HMpos HMbound]].
  exists (Qmax M (Qabs (cs_seq a N)) + 1).
  split.
  - assert (H := Qabs_nonneg (cs_seq a N)).
    assert (HM_le := Q.le_max_l M (Qabs (cs_seq a N))). lra.
  - intros n.
    destruct (Nat.le_gt_cases N n) as [Hge|Hlt].
    + (* n >= N: |a(n)| < |a(N)| + 1 <= B *)
      assert (Hdiff := HN n N Hge (Nat.le_refl N)).
      assert (Htri : Qabs (cs_seq a n) <=
                     Qabs (cs_seq a n - cs_seq a N) + Qabs (cs_seq a N)).
      { assert (Heq : cs_seq a n == (cs_seq a n - cs_seq a N) + cs_seq a N) by ring.
        qabs_rw Heq. apply Qabs_triangle. }
      assert (H_aN_le := Q.le_max_r M (Qabs (cs_seq a N))). lra.
    + (* n < N *)
      assert (Hbn := HMbound n ltac:(lia)).
      assert (HM_le := Q.le_max_l M (Qabs (cs_seq a N))). lra.
Qed.

(* ========================================================================= *)
(* SECTION 2: MULTIPLICATION                                                 *)
(* ========================================================================= *)

Lemma cauchy_mul_is_cauchy (a b : CauchySeq) :
  is_cauchy (fun n => cs_seq a n * cs_seq b n).
Proof.
  intros eps Heps.
  destruct (cauchy_bounded a) as [Ba [HBa_pos HBa]].
  destruct (cauchy_bounded b) as [Bb [HBb_pos HBb]].
  (* eps_b = eps/(2*Ba), eps_a = eps/(2*Bb) *)
  set (eps_b := eps * (1#2) * / Ba).
  set (eps_a := eps * (1#2) * / Bb).
  assert (Heps_b : 0 < eps_b)
    by (unfold eps_b; apply Qmult_lt_0_compat; [lra | apply Qinv_lt_0_compat; lra]).
  assert (Heps_a : 0 < eps_a)
    by (unfold eps_a; apply Qmult_lt_0_compat; [lra | apply Qinv_lt_0_compat; lra]).
  destruct (cs_cauchy a eps_a Heps_a) as [Na HNa].
  destruct (cs_cauchy b eps_b Heps_b) as [Nb HNb].
  exists (Nat.max Na Nb).
  intros m n Hm Hn.
  assert (HmNa : (Na <= m)%nat) by lia.
  assert (HnNa : (Na <= n)%nat) by lia.
  assert (HmNb : (Nb <= m)%nat) by lia.
  assert (HnNb : (Nb <= n)%nat) by lia.
  assert (Hb_close := HNb m n HmNb HnNb).
  assert (Ha_close := HNa m n HmNa HnNa).
  (* a(m)*b(m) - a(n)*b(n) = a(m)*(b(m)-b(n)) + (a(m)-a(n))*b(n) *)
  assert (Hdecomp :
    cs_seq a m * cs_seq b m - cs_seq a n * cs_seq b n ==
    cs_seq a m * (cs_seq b m - cs_seq b n) +
    (cs_seq a m - cs_seq a n) * cs_seq b n) by ring.
  qabs_rw Hdecomp.
  (* Triangle inequality *)
  apply Qle_lt_trans with
    (Qabs (cs_seq a m * (cs_seq b m - cs_seq b n)) +
     Qabs ((cs_seq a m - cs_seq a n) * cs_seq b n)).
  { apply Qabs_triangle. }
  (* Bound term 1: |a(m)*(b(m)-b(n))| <= Ba * |b(m)-b(n)| *)
  assert (Hterm1 : Qabs (cs_seq a m * (cs_seq b m - cs_seq b n)) <=
                   Ba * Qabs (cs_seq b m - cs_seq b n)).
  { rewrite Qabs_Qmult.
    apply Qmult_le_compat_r; [apply HBa | apply Qabs_nonneg]. }
  (* Bound term 2: |(a(m)-a(n))*b(n)| <= |a(m)-a(n)| * Bb *)
  assert (Hterm2 : Qabs ((cs_seq a m - cs_seq a n) * cs_seq b n) <=
                   Qabs (cs_seq a m - cs_seq a n) * Bb).
  { rewrite Qabs_Qmult.
    setoid_replace (Qabs (cs_seq a m - cs_seq a n) * Qabs (cs_seq b n))
      with (Qabs (cs_seq b n) * Qabs (cs_seq a m - cs_seq a n)) by ring.
    setoid_replace (Qabs (cs_seq a m - cs_seq a n) * Bb)
      with (Bb * Qabs (cs_seq a m - cs_seq a n)) by ring.
    apply Qmult_le_compat_r; [apply HBb | apply Qabs_nonneg]. }
  (* Ba * |b(m)-b(n)| < Ba * eps_b *)
  assert (Hfirst : Ba * Qabs (cs_seq b m - cs_seq b n) < Ba * eps_b).
  { setoid_replace (Ba * Qabs (cs_seq b m - cs_seq b n))
      with (Qabs (cs_seq b m - cs_seq b n) * Ba) by ring.
    setoid_replace (Ba * eps_b) with (eps_b * Ba) by ring.
    apply Qmult_lt_compat_r; [exact HBa_pos | exact Hb_close]. }
  (* |a(m)-a(n)| * Bb < eps_a * Bb *)
  assert (Hsecond : Qabs (cs_seq a m - cs_seq a n) * Bb < eps_a * Bb).
  { apply Qmult_lt_compat_r; [exact HBb_pos | exact Ha_close]. }
  (* Ba * eps_b + eps_a * Bb == eps *)
  assert (Hsum : Ba * eps_b + eps_a * Bb == eps).
  { unfold eps_a, eps_b. field; lra. }
  lra.
Qed.

Definition cauchy_mul (a b : CauchySeq) : CauchySeq :=
  mkCauchy _ (cauchy_mul_is_cauchy a b).

Definition cauchy_one : CauchySeq := cauchy_const 1.

(* ========================================================================= *)
(* SECTION 3: MULTIPLICATION RESPECTS EQUIVALENCE                            *)
(* ========================================================================= *)

Lemma cauchy_mul_compat : forall a a' b b' : CauchySeq,
  a ~~ a' -> b ~~ b' -> cauchy_mul a b ~~ cauchy_mul a' b'.
Proof.
  intros a a' b b' Ha Hb eps Heps.
  destruct (cauchy_bounded a) as [Ba [HBa_pos HBa]].
  destruct (cauchy_bounded b') as [Bb' [HBb'_pos HBb']].
  set (eps_1 := eps * (1#2) * / Bb').
  set (eps_2 := eps * (1#2) * / Ba).
  assert (Heps1 : 0 < eps_1)
    by (unfold eps_1; apply Qmult_lt_0_compat; [lra | apply Qinv_lt_0_compat; lra]).
  assert (Heps2 : 0 < eps_2)
    by (unfold eps_2; apply Qmult_lt_0_compat; [lra | apply Qinv_lt_0_compat; lra]).
  destruct (Ha eps_1 Heps1) as [N1 HN1].
  destruct (Hb eps_2 Heps2) as [N2 HN2].
  exists (Nat.max N1 N2).
  intros n Hn.
  simpl.
  assert (HnN1 : (N1 <= n)%nat) by lia.
  assert (HnN2 : (N2 <= n)%nat) by lia.
  (* a(n)*b(n) - a'(n)*b'(n) = (a(n)-a'(n))*b'(n) + a(n)*(b(n)-b'(n)) *)
  assert (Hdecomp :
    cs_seq a n * cs_seq b n - cs_seq a' n * cs_seq b' n ==
    (cs_seq a n - cs_seq a' n) * cs_seq b' n +
    cs_seq a n * (cs_seq b n - cs_seq b' n)) by ring.
  qabs_rw Hdecomp.
  apply Qle_lt_trans with
    (Qabs ((cs_seq a n - cs_seq a' n) * cs_seq b' n) +
     Qabs (cs_seq a n * (cs_seq b n - cs_seq b' n))).
  { apply Qabs_triangle. }
  assert (Ht1 : Qabs ((cs_seq a n - cs_seq a' n) * cs_seq b' n) <=
                Qabs (cs_seq a n - cs_seq a' n) * Bb').
  { rewrite Qabs_Qmult.
    setoid_replace (Qabs (cs_seq a n - cs_seq a' n) * Qabs (cs_seq b' n))
      with (Qabs (cs_seq b' n) * Qabs (cs_seq a n - cs_seq a' n)) by ring.
    setoid_replace (Qabs (cs_seq a n - cs_seq a' n) * Bb')
      with (Bb' * Qabs (cs_seq a n - cs_seq a' n)) by ring.
    apply Qmult_le_compat_r; [apply HBb' | apply Qabs_nonneg]. }
  assert (Ht2 : Qabs (cs_seq a n * (cs_seq b n - cs_seq b' n)) <=
                Ba * Qabs (cs_seq b n - cs_seq b' n)).
  { rewrite Qabs_Qmult.
    apply Qmult_le_compat_r; [apply HBa | apply Qabs_nonneg]. }
  assert (H1 := HN1 n HnN1).
  assert (H2 := HN2 n HnN2).
  assert (Hfirst : Qabs (cs_seq a n - cs_seq a' n) * Bb' < eps_1 * Bb').
  { apply Qmult_lt_compat_r; [exact HBb'_pos | exact H1]. }
  assert (Hsecond : Ba * Qabs (cs_seq b n - cs_seq b' n) < Ba * eps_2).
  { setoid_replace (Ba * Qabs (cs_seq b n - cs_seq b' n))
      with (Qabs (cs_seq b n - cs_seq b' n) * Ba) by ring.
    setoid_replace (Ba * eps_2) with (eps_2 * Ba) by ring.
    apply Qmult_lt_compat_r; [exact HBa_pos | exact H2]. }
  assert (Hsum : eps_1 * Bb' + Ba * eps_2 == eps).
  { unfold eps_1, eps_2. field; lra. }
  lra.
Qed.

(* ========================================================================= *)
(* SECTION 4: RING LAWS                                                      *)
(* ========================================================================= *)

Lemma cauchy_mul_comm : forall a b : CauchySeq,
  cauchy_mul a b ~~ cauchy_mul b a.
Proof.
  intros a b eps Heps.
  exists 0%nat. intros n _.
  simpl.
  assert (H : cs_seq a n * cs_seq b n - cs_seq b n * cs_seq a n == 0) by ring.
  qabs_rw H. rewrite Qabs_pos; lra.
Qed.

Lemma cauchy_mul_assoc : forall a b c : CauchySeq,
  cauchy_mul (cauchy_mul a b) c ~~ cauchy_mul a (cauchy_mul b c).
Proof.
  intros a b c eps Heps.
  exists 0%nat. intros n _.
  simpl.
  assert (H : cs_seq a n * cs_seq b n * cs_seq c n -
              cs_seq a n * (cs_seq b n * cs_seq c n) == 0) by ring.
  qabs_rw H. rewrite Qabs_pos; lra.
Qed.

Lemma cauchy_mul_one_r : forall a : CauchySeq,
  cauchy_mul a cauchy_one ~~ a.
Proof.
  intros a eps Heps.
  exists 0%nat. intros n _.
  simpl.
  assert (H : cs_seq a n * 1 - cs_seq a n == 0) by ring.
  qabs_rw H. rewrite Qabs_pos; lra.
Qed.

Lemma cauchy_mul_one_l : forall a : CauchySeq,
  cauchy_mul cauchy_one a ~~ a.
Proof.
  intros a.
  apply cauchy_equiv_trans with (cauchy_mul a cauchy_one).
  - apply cauchy_mul_comm.
  - apply cauchy_mul_one_r.
Qed.

Lemma cauchy_distrib_l : forall a b c : CauchySeq,
  cauchy_mul a (cauchy_add b c) ~~ cauchy_add (cauchy_mul a b) (cauchy_mul a c).
Proof.
  intros a b c eps Heps.
  exists 0%nat. intros n _.
  simpl.
  assert (H : cs_seq a n * (cs_seq b n + cs_seq c n) -
              (cs_seq a n * cs_seq b n + cs_seq a n * cs_seq c n) == 0) by ring.
  qabs_rw H. rewrite Qabs_pos; lra.
Qed.

Lemma cauchy_distrib_r : forall a b c : CauchySeq,
  cauchy_mul (cauchy_add a b) c ~~ cauchy_add (cauchy_mul a c) (cauchy_mul b c).
Proof.
  intros a b c eps Heps.
  exists 0%nat. intros n _.
  simpl.
  assert (H : (cs_seq a n + cs_seq b n) * cs_seq c n -
              (cs_seq a n * cs_seq c n + cs_seq b n * cs_seq c n) == 0) by ring.
  qabs_rw H. rewrite Qabs_pos; lra.
Qed.

Lemma cauchy_mul_zero_r : forall a : CauchySeq,
  cauchy_mul a (cauchy_const 0) ~~ cauchy_const 0.
Proof.
  intros a eps Heps.
  exists 0%nat. intros n _.
  simpl.
  assert (H : cs_seq a n * 0 - 0 == 0) by ring.
  qabs_rw H. rewrite Qabs_pos; lra.
Qed.

Lemma cauchy_mul_neg_r : forall a b : CauchySeq,
  cauchy_mul a (cauchy_neg b) ~~ cauchy_neg (cauchy_mul a b).
Proof.
  intros a b eps Heps.
  exists 0%nat. intros n _.
  simpl.
  assert (H : cs_seq a n * - cs_seq b n - - (cs_seq a n * cs_seq b n) == 0) by ring.
  qabs_rw H. rewrite Qabs_pos; lra.
Qed.

(* ========================================================================= *)
(* SECTION 5: MULTIPLICATIVE INVERSE                                         *)
(*                                                                           *)
(*  For a CauchySeq a with cauchy_pos a (i.e., eventually > q > 0),         *)
(*  we define inv by shifting: inv(n) = 1/a(n+N) where N is the index      *)
(*  after which a stays above q.                                             *)
(* ========================================================================= *)

(** A sequence eventually bounded away from 0 has a Cauchy inverse.
    Strategy: avoid inverse-ordering lemmas by using Qdiv_lt_from_mul
    (reduce |num|/den < eps to |num| < eps * den). *)
Lemma cauchy_inv_is_cauchy (a : CauchySeq) (q : Q) (N : nat)
  (Hq : 0 < q)
  (HaN : forall n : nat, (N <= n)%nat -> q < cs_seq a n) :
  is_cauchy (fun n => / cs_seq a (n + N)%nat).
Proof.
  intros eps Heps.
  set (eps' := eps * (q * q)).
  assert (Heps' : 0 < eps')
    by (unfold eps'; apply Qmult_lt_0_compat; [lra | apply Qmult_lt_0_compat; lra]).
  destruct (cs_cauchy a eps' Heps') as [M HM].
  exists M.
  intros m n Hm Hn.
  assert (HmN : (N <= m + N)%nat) by lia.
  assert (HnN : (N <= n + N)%nat) by lia.
  assert (Ham := HaN _ HmN).
  assert (Han := HaN _ HnN).
  assert (Ham_pos : 0 < cs_seq a (m + N)) by lra.
  assert (Han_pos : 0 < cs_seq a (n + N)) by lra.
  (* Rewrite difference of inverses *)
  assert (Hinv_diff :
    / cs_seq a (m + N) - / cs_seq a (n + N) ==
    (cs_seq a (n + N) - cs_seq a (m + N)) /
    (cs_seq a (m + N) * cs_seq a (n + N)))
    by (field; lra).
  qabs_rw Hinv_diff.
  set (num := cs_seq a (n + N) - cs_seq a (m + N)).
  set (den := cs_seq a (m + N) * cs_seq a (n + N)).
  assert (Hden_pos : 0 < den)
    by (unfold den; apply Qmult_lt_0_compat; lra).
  (* |num / den| = |num| * / den *)
  assert (Habs_decomp : Qabs (num / den) == Qabs num * / den).
  { unfold Qdiv. rewrite Qabs_Qmult.
    rewrite (Qabs_pos (/ den)).
    - reflexivity.
    - apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Hden_pos. }
  setoid_rewrite Habs_decomp.
  (* Use Qdiv_lt_from_mul: suffices |num| < eps * den *)
  apply Qdiv_lt_from_mul.
  - exact Hden_pos.
  - (* |num| < eps * den *)
    assert (HMm : (M <= m + N)%nat) by lia.
    assert (HMn : (M <= n + N)%nat) by lia.
    assert (Hclose : Qabs num < eps') by (unfold num; exact (HM _ _ HMn HMm)).
    (* q * q < den *)
    assert (Hqq_lt_den : q * q < den).
    { unfold den.
      apply Qmult_lt_compat_nonneg; split; lra. }
    (* eps * (q*q) < eps * den *)
    assert (Heps_bound : eps' < eps * den).
    { unfold eps'.
      setoid_replace (eps * (q * q)) with ((q * q) * eps) by ring.
      setoid_replace (eps * den) with (den * eps) by ring.
      apply Qmult_lt_compat_r; [exact Heps | exact Hqq_lt_den]. }
    lra.
Qed.

(** Multiplicative inverse for positive Cauchy sequences *)
Definition cauchy_inv_pos (a : CauchySeq) (q : Q) (N : nat)
  (Hq : 0 < q)
  (HaN : forall n : nat, (N <= n)%nat -> q < cs_seq a n) : CauchySeq :=
  mkCauchy _ (cauchy_inv_is_cauchy a q N Hq HaN).

(** a * inv(a) ~~ 1 for positive sequences *)
Lemma cauchy_mul_inv_r_pos :
  forall (a : CauchySeq) (q : Q) (N : nat)
    (Hq : 0 < q)
    (HaN : forall n : nat, (N <= n)%nat -> q < cs_seq a n),
  cauchy_mul a (cauchy_inv_pos a q N Hq HaN) ~~ cauchy_one.
Proof.
  intros a q N Hq HaN eps Heps.
  (* (cauchy_mul a inv)(n) = a(n) * /a(n+N), need this ~~ 1 *)
  set (eps' := eps * q).
  assert (Heps' : 0 < eps')
    by (unfold eps'; apply Qmult_lt_0_compat; lra).
  destruct (cs_cauchy a eps' Heps') as [M HM].
  exists (Nat.max N M).
  intros n Hn.
  simpl.
  assert (HnN : (N <= n)%nat) by lia.
  assert (HnM : (M <= n)%nat) by lia.
  assert (HnpN : (N <= n + N)%nat) by lia.
  assert (HnpM : (M <= n + N)%nat) by lia.
  assert (Han := HaN n HnN).
  assert (HanN := HaN (n + N)%nat HnpN).
  assert (HanN_pos : 0 < cs_seq a (n + N)) by lra.
  (* a(n) * /a(n+N) - 1 = (a(n) - a(n+N)) * /a(n+N) *)
  assert (Hrw : cs_seq a n * / cs_seq a (n + N) - 1 ==
                (cs_seq a n - cs_seq a (n + N)) * / cs_seq a (n + N))
    by (field; lra).
  qabs_rw Hrw.
  (* |x * /y| = |x| * /y when y > 0 *)
  assert (Habs_decomp :
    Qabs ((cs_seq a n - cs_seq a (n + N)) * / cs_seq a (n + N)) ==
    Qabs (cs_seq a n - cs_seq a (n + N)) * / cs_seq a (n + N)).
  { rewrite Qabs_Qmult.
    rewrite (Qabs_pos (/ cs_seq a (n + N))).
    - reflexivity.
    - apply Qlt_le_weak. apply Qinv_lt_0_compat. exact HanN_pos. }
  setoid_rewrite Habs_decomp.
  (* Use Qdiv_lt_from_mul: suffices |a(n) - a(n+N)| < eps * a(n+N) *)
  apply Qdiv_lt_from_mul.
  - exact HanN_pos.
  - (* |a(n) - a(n+N)| < eps * a(n+N) *)
    assert (Hclose : Qabs (cs_seq a n - cs_seq a (n + N)) < eps')
      by exact (HM n (n + N)%nat HnM HnpM).
    (* eps' = eps * q < eps * a(n+N) *)
    assert (Hbound : eps' < eps * cs_seq a (n + N)).
    { unfold eps'.
      setoid_replace (eps * q) with (q * eps) by ring.
      setoid_replace (eps * cs_seq a (n + N))
        with (cs_seq a (n + N) * eps) by ring.
      apply Qmult_lt_compat_r; [exact Heps | exact HanN]. }
    lra.
Qed.

(* ========================================================================= *)
(* SECTION 6: ORDERED FIELD PROPERTIES                                       *)
(* ========================================================================= *)

Lemma cauchy_pos_add : forall a b : CauchySeq,
  cauchy_pos a -> cauchy_pos b -> cauchy_pos (cauchy_add a b).
Proof.
  intros a b [qa [Hqa [Na HNa]]] [qb [Hqb [Nb HNb]]].
  exists (qa + qb).
  split.
  - lra.
  - exists (Nat.max Na Nb).
    intros n Hn.
    simpl.
    assert (HnNa : (Na <= n)%nat) by lia.
    assert (HnNb : (Nb <= n)%nat) by lia.
    assert (Ha := HNa n HnNa).
    assert (Hb := HNb n HnNb).
    lra.
Qed.

Lemma cauchy_pos_mul : forall a b : CauchySeq,
  cauchy_pos a -> cauchy_pos b -> cauchy_pos (cauchy_mul a b).
Proof.
  intros a b [qa [Hqa [Na HNa]]] [qb [Hqb [Nb HNb]]].
  exists (qa * qb).
  split.
  - apply Qmult_lt_0_compat; assumption.
  - exists (Nat.max Na Nb).
    intros n Hn.
    simpl.
    assert (HnNa : (Na <= n)%nat) by lia.
    assert (HnNb : (Nb <= n)%nat) by lia.
    assert (Ha := HNa n HnNa).
    assert (Hb := HNb n HnNb).
    (* qa * qb < a(n) * b(n) *)
    apply Qmult_lt_compat_nonneg; split; lra.
Qed.

(* ========================================================================= *)
(* SECTION 7: VERIFICATION                                                    *)
(* ========================================================================= *)

Check cauchy_bounded.
Check cauchy_mul.
Check cauchy_mul_compat.
Check cauchy_mul_comm.
Check cauchy_mul_assoc.
Check cauchy_mul_one_r.
Check cauchy_mul_one_l.
Check cauchy_distrib_l.
Check cauchy_distrib_r.
Check cauchy_mul_zero_r.
Check cauchy_mul_neg_r.
Check cauchy_inv_pos.
Check cauchy_mul_inv_r_pos.
Check cauchy_pos_add.
Check cauchy_pos_mul.

Print Assumptions cauchy_bounded.
Print Assumptions cauchy_mul_is_cauchy.
Print Assumptions cauchy_mul_compat.
Print Assumptions cauchy_mul_inv_r_pos.
Print Assumptions cauchy_pos_mul.
