(* ========================================================================= *)
(*            METRIC SPACES AS ToS SYSTEMS                                 *)
(*                                                                         *)
(*  Part of: Theory of Systems - Verified Standard Library (Tier 2b)       *)
(*                                                                         *)
(*  Elements: points of the space                                          *)
(*  Roles:    distance -> MeasureOfSeparation                              *)
(*  Rules:    triangle inequality (constitution), symmetry, positivity     *)
(*  Status:   close (d < eps) | far (d >= eps) | convergent | divergent   *)
(*                                                                         *)
(*  CONTENTS:                                                              *)
(*    Section 1: Abstract metric space (section-parametric)                *)
(*    Section 2: Q as a metric space via Qdist                            *)
(*    Section 3: QVec L-infinity distance via component-max               *)
(*                                                                         *)
(*  STATUS: 18 Qed, 0 Admitted                                            *)
(*  AXIOMS: NONE                                                          *)
(*                                                                         *)
(*  Connection: CauchyReal.v, ProcessGeneral.v, FixedPoint.v              *)
(*  Author: Horsocrates | Date: March 2026                                 *)
(* ========================================================================= *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qminmax.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Close Scope Z_scope.
Open Scope Q_scope.

From ToS Require Import CauchyReal.
From ToS Require Import ProcessGeneral.
From ToS Require Import LinearAlgebra.

(* ========================================================================= *)
(* SECTION 1: ABSTRACT METRIC SPACE (Section-Parametric)                    *)
(* ========================================================================= *)

(**
  ABSTRACT METRIC SPACE
  ======================

  A metric space is a type X equipped with a distance function d : X -> X -> Q
  satisfying the four axioms: non-negativity, identity of indiscernibles
  (reflexive zero), symmetry, and triangle inequality.

  We use a Section to parameterize all definitions and theorems by the
  carrier type and distance, following the ToS convention of avoiding
  typeclasses in favour of explicit parametricity.
*)

Section MetricSpaces.

Variable X : Type.
Variable d : X -> X -> Q.

Hypothesis d_nonneg : forall x y, 0 <= d x y.
Hypothesis d_zero : forall x, d x x == 0.
Hypothesis d_sym : forall x y, d x y == d y x.
Hypothesis d_triangle : forall x y z, d x z <= d x y + d y z.

(** Cauchy sequence in a metric space *)
Definition is_cauchy_metric (f : nat -> X) : Prop :=
  forall eps : Q, 0 < eps ->
    exists N : nat, forall m n : nat,
      (N < m)%nat -> (N < n)%nat -> d (f m) (f n) < eps.

(** Convergence to a limit in a metric space *)
Definition is_limit_metric (f : nat -> X) (l : X) : Prop :=
  forall eps : Q, 0 < eps ->
    exists N : nat, forall n : nat,
      (N < n)%nat -> d (f n) l < eps.

(** Completeness: every Cauchy sequence has a limit *)
Definition is_complete_metric : Prop :=
  forall f : nat -> X, is_cauchy_metric f -> exists l : X, is_limit_metric f l.

(** Contraction mapping on an abstract metric space *)
Definition is_contraction_metric (f : X -> X) (c : Q) : Prop :=
  0 <= c /\ c < 1 /\ forall x y, d (f x) (f y) <= c * d x y.

(* ----- Theorem 1: d_nonneg_alt ----- *)
(** Non-negativity with swapped arguments *)
Lemma d_nonneg_alt : forall x y, 0 <= d y x.
Proof.
  intros x y.
  assert (Hsym := d_sym y x).
  assert (Hnn := d_nonneg x y).
  lra.
Qed.

(* ----- Theorem 2: limit_dist_zero ----- *)
(** If a sequence converges to two limits, their distance is arbitrarily small *)
Lemma limit_dist_zero : forall f l1 l2,
  is_limit_metric f l1 ->
  is_limit_metric f l2 ->
  forall eps, 0 < eps -> d l1 l2 < eps.
Proof.
  intros f l1 l2 Hl1 Hl2 eps Heps.
  assert (Heps2 : 0 < eps * (1 # 2)) by lra.
  destruct (Hl1 (eps * (1 # 2)) Heps2) as [N1 HN1].
  destruct (Hl2 (eps * (1 # 2)) Heps2) as [N2 HN2].
  set (N := Nat.max N1 N2).
  assert (HN1_lt : (N1 < S N)%nat) by (unfold N; lia).
  assert (HN2_lt : (N2 < S N)%nat) by (unfold N; lia).
  specialize (HN1 (S N) HN1_lt).
  specialize (HN2 (S N) HN2_lt).
  apply Qle_lt_trans with (d l1 (f (S N)) + d (f (S N)) l2).
  - apply d_triangle.
  - assert (Hsym : d l1 (f (S N)) == d (f (S N)) l1) by apply d_sym.
    rewrite Hsym. lra.
Qed.

(* ----- Theorem 3: cauchy_of_limit ----- *)
(** A convergent sequence is Cauchy *)
Lemma cauchy_of_limit : forall f l,
  is_limit_metric f l -> is_cauchy_metric f.
Proof.
  intros f l Hl eps Heps.
  assert (Heps2 : 0 < eps * (1 # 2)) by lra.
  destruct (Hl (eps * (1 # 2)) Heps2) as [N HN].
  exists N. intros m n Hm Hn.
  assert (HNm := HN m Hm).
  assert (HNn := HN n Hn).
  apply Qle_lt_trans with (d (f m) l + d l (f n)).
  - apply d_triangle.
  - assert (Hsym : d l (f n) == d (f n) l) by apply d_sym.
    rewrite Hsym. lra.
Qed.

(* ----- Theorem 4: contraction_fixed_bound ----- *)
(** Extract the contraction bound from the definition *)
Lemma contraction_fixed_bound : forall f c,
  is_contraction_metric f c ->
  forall x y, d (f x) (f y) <= c * d x y.
Proof.
  intros f c [_ [_ Hcontr]] x y.
  apply Hcontr.
Qed.

(* ----- Theorem 5: contraction_nonneg_factor ----- *)
(** The contraction factor is non-negative *)
Lemma contraction_nonneg_factor : forall f c,
  is_contraction_metric f c -> 0 <= c.
Proof.
  intros f c [Hnn _]. exact Hnn.
Qed.

(* ----- Theorem 6: contraction_lt_one_factor ----- *)
(** The contraction factor is strictly less than 1 *)
Lemma contraction_lt_one_factor : forall f c,
  is_contraction_metric f c -> c < 1.
Proof.
  intros f c [_ [Hlt _]]. exact Hlt.
Qed.

(* ----- Theorem 7: contraction_shrinks ----- *)
(** Applying a contraction does not increase distances *)
Lemma contraction_shrinks : forall f c,
  is_contraction_metric f c ->
  forall x y, d (f x) (f y) <= d x y.
Proof.
  intros f c [Hnn [Hlt Hcontr]] x y.
  apply Qle_trans with (c * d x y).
  - apply Hcontr.
  - assert (Hd : 0 <= d x y) by apply d_nonneg.
    assert (Hle : c * d x y <= 1 * d x y).
    { apply Qmult_le_compat_r; lra. }
    lra.
Qed.

End MetricSpaces.

(* After ending the section, the hypotheses become explicit parameters. *)
(* Usage: d_nonneg_alt X d d_nonneg d_sym x y *)

(* ========================================================================= *)
(* SECTION 2: Q AS A METRIC SPACE                                           *)
(* ========================================================================= *)

(**
  Q METRIC SPACE
  ===============

  The rationals Q form a metric space with distance d(x,y) = |x - y|.
  We define Q_dist locally (matching ProcessGeneral.v's Qdist) and verify
  the four metric axioms, then show equivalence with CauchyReal.is_cauchy.
*)

Definition Q_dist (x y : Q) : Q := Qabs (x - y).

(* ----- Theorem 8: Q_dist_nonneg ----- *)
Lemma Q_dist_nonneg : forall x y, 0 <= Q_dist x y.
Proof.
  intros x y. unfold Q_dist. apply Qabs_nonneg.
Qed.

(* ----- Theorem 9: Q_dist_zero ----- *)
Lemma Q_dist_zero : forall x, Q_dist x x == 0.
Proof.
  intro x. unfold Q_dist.
  assert (Hzero : x - x == 0) by ring.
  apply Qabs_wd in Hzero. rewrite Hzero.
  apply Qabs_pos. lra.
Qed.

(* ----- Theorem 10: Q_dist_sym ----- *)
Lemma Q_dist_sym : forall x y, Q_dist x y == Q_dist y x.
Proof.
  intros x y. unfold Q_dist.
  assert (Hopp : y - x == -(x - y)) by ring.
  apply Qabs_wd in Hopp. rewrite Hopp.
  symmetry. apply Qabs_opp.
Qed.

(* ----- Theorem 11: Q_dist_triangle ----- *)
Lemma Q_dist_triangle : forall x y z, Q_dist x z <= Q_dist x y + Q_dist y z.
Proof.
  intros x y z. unfold Q_dist.
  assert (Hdecomp : x - z == (x - y) + (y - z)) by ring.
  apply Qabs_wd in Hdecomp. rewrite Hdecomp.
  apply Qabs_triangle.
Qed.

(* ----- Theorem 12: Q_cauchy_metric_equiv ----- *)
(** Equivalence: metric-space Cauchy over Q_dist iff CauchyReal.is_cauchy *)
Lemma Q_cauchy_metric_equiv : forall f : nat -> Q,
  is_cauchy_metric Q Q_dist f <-> is_cauchy f.
Proof.
  intro f. unfold is_cauchy_metric, is_cauchy, Q_dist.
  split.
  - (* metric -> CauchyReal: N < m becomes S N <= m *)
    intros H eps Heps.
    destruct (H eps Heps) as [N HN].
    exists (S N). intros m n Hm Hn.
    apply HN; lia.
  - (* CauchyReal -> metric: N <= m follows from N < m *)
    intros H eps Heps.
    destruct (H eps Heps) as [N HN].
    exists N. intros m n Hm Hn.
    apply HN; lia.
Qed.

(* ========================================================================= *)
(* SECTION 3: QVec L-INFINITY DISTANCE                                      *)
(* ========================================================================= *)

(**
  QVEC METRIC (L-infinity)
  =========================

  For QVec n (from LinearAlgebra.v), the L-infinity distance is defined as
  the maximum of component-wise absolute differences:

    d_inf(v1, v2) = max_i |v1_i - v2_i|

  We implement this via list_max_dist on the underlying lists, then lift
  to QVec. The triangle inequality for Qmax-based distance requires
  showing that if a <= c + e and b <= d + f, then
  Qmax a b <= Qmax c d + Qmax e f.
*)

(** Component-max distance on lists *)
Fixpoint list_max_dist (l1 l2 : list Q) : Q :=
  match l1, l2 with
  | x :: xs, y :: ys => Qmax (Qabs (x - y)) (list_max_dist xs ys)
  | _, _ => 0
  end.

(** QVec L-infinity distance *)
Definition QVec_dist {n : nat} (v1 v2 : QVec n) : Q :=
  list_max_dist (qv_data v1) (qv_data v2).

(* ----- Theorem 13: list_max_dist_nonneg ----- *)
Lemma list_max_dist_nonneg : forall l1 l2, 0 <= list_max_dist l1 l2.
Proof.
  induction l1 as [| x xs IH]; intros [| y ys]; simpl; try lra.
  apply Qle_trans with (Qabs (x - y)).
  - apply Qabs_nonneg.
  - apply Q.le_max_l.
Qed.

(* ----- Theorem 14: list_max_dist_zero ----- *)
Lemma list_max_dist_zero : forall l, list_max_dist l l == 0.
Proof.
  induction l as [| x xs IH]; simpl.
  - reflexivity.
  - assert (Habs : Qabs (x - x) == 0).
    { assert (Hzz : x - x == 0) by ring.
      apply Qabs_wd in Hzz. rewrite Hzz. apply Qabs_pos. lra. }
    destruct (Q.max_dec (Qabs (x - x)) (list_max_dist xs xs)) as [Hl | Hr].
    + rewrite Hl. exact Habs.
    + rewrite Hr. exact IH.
Qed.

(* ----- Theorem 15: list_max_dist_sym ----- *)
Lemma list_max_dist_sym : forall l1 l2,
  list_max_dist l1 l2 == list_max_dist l2 l1.
Proof.
  induction l1 as [| x xs IH]; intros [| y ys]; simpl; try reflexivity.
  assert (Habs_eq : Qabs (x - y) == Qabs (y - x)).
  { assert (Hopp : y - x == -(x - y)) by ring.
    apply Qabs_wd in Hopp. rewrite Hopp. symmetry. apply Qabs_opp. }
  assert (IHtail := IH ys).
  (* Use Q.max_le_iff to show both directions *)
  apply Qle_antisym.
  - destruct (Q.max_dec (Qabs (x - y)) (list_max_dist xs ys)) as [Hl | Hr].
    + rewrite Hl.
      apply Qle_trans with (Qabs (y - x)).
      * lra.
      * apply Q.le_max_l.
    + rewrite Hr.
      apply Qle_trans with (list_max_dist ys xs).
      * lra.
      * apply Q.le_max_r.
  - destruct (Q.max_dec (Qabs (y - x)) (list_max_dist ys xs)) as [Hl | Hr].
    + rewrite Hl.
      apply Qle_trans with (Qabs (x - y)).
      * lra.
      * apply Q.le_max_l.
    + rewrite Hr.
      apply Qle_trans with (list_max_dist xs ys).
      * lra.
      * apply Q.le_max_r.
Qed.

(* ----- Theorem 16: list_max_dist_head_le ----- *)
(** The head-component distance is bounded by the total *)
Lemma list_max_dist_head_le : forall x y xs ys,
  Qabs (x - y) <= list_max_dist (x :: xs) (y :: ys).
Proof.
  intros x y xs ys. simpl. apply Q.le_max_l.
Qed.

(* ----- Theorem 17: list_max_dist_tail_le ----- *)
(** The tail distance is bounded by the total *)
Lemma list_max_dist_tail_le : forall x y xs ys,
  list_max_dist xs ys <= list_max_dist (x :: xs) (y :: ys).
Proof.
  intros x y xs ys. simpl. apply Q.le_max_r.
Qed.

(* ----- Theorem 18: list_max_dist_triangle ----- *)
(** Triangle inequality for L-infinity distance on lists *)
Lemma list_max_dist_triangle : forall l1 l2 l3,
  length l1 = length l2 ->
  length l2 = length l3 ->
  list_max_dist l1 l3 <= list_max_dist l1 l2 + list_max_dist l2 l3.
Proof.
  induction l1 as [| x xs IH]; intros [| y ys] [| z zs] Hlen12 Hlen23;
    simpl in *; try lra; try discriminate.
  (* Goal: Qmax |x-z| (lmd xs zs) <= Qmax |x-y| (lmd xs ys) + Qmax |y-z| (lmd ys zs) *)
  (* Strategy: show both arguments of the LHS Qmax are <= RHS,
     then use Q.max_lub_iff or equivalent *)
  assert (Hlen12' : length xs = length ys) by lia.
  assert (Hlen23' : length ys = length zs) by lia.
  assert (IHtail := IH ys zs Hlen12' Hlen23').
  (* Component triangle inequality *)
  assert (Hcomp : Qabs (x - z) <= Qabs (x - y) + Qabs (y - z)).
  { assert (Hdecomp : x - z == (x - y) + (y - z)) by ring.
    apply Qabs_wd in Hdecomp. rewrite Hdecomp. apply Qabs_triangle. }
  (* Both parts are <= the sum of the two maxes *)
  set (s := Qmax (Qabs (x - y)) (list_max_dist xs ys) +
            Qmax (Qabs (y - z)) (list_max_dist ys zs)).
  assert (Hcomp_le : Qabs (x - z) <= s).
  { unfold s.
    apply Qle_trans with (Qabs (x - y) + Qabs (y - z)); [exact Hcomp |].
    apply Qplus_le_compat; [apply Q.le_max_l | apply Q.le_max_l]. }
  assert (Htail_le : list_max_dist xs zs <= s).
  { unfold s.
    apply Qle_trans with (list_max_dist xs ys + list_max_dist ys zs); [exact IHtail |].
    apply Qplus_le_compat; [apply Q.le_max_r | apply Q.le_max_r]. }
  (* Now: Qmax a b <= s when a <= s and b <= s *)
  destruct (Q.max_dec (Qabs (x - z)) (list_max_dist xs zs)) as [Hl | Hr].
  - rewrite Hl. exact Hcomp_le.
  - rewrite Hr. exact Htail_le.
Qed.

(* ========================================================================= *)
(* SUMMARY                                                                   *)
(* ========================================================================= *)

(**
  THEOREM INVENTORY (18 Qed, 0 Admitted)
  ========================================

  Section 1 — Abstract Metric Space (Section MetricSpaces):
    1.  d_nonneg_alt           : 0 <= d y x
    2.  limit_dist_zero        : limits are arbitrarily close
    3.  cauchy_of_limit         : convergent => Cauchy
    4.  contraction_fixed_bound : extract contraction inequality
    5.  contraction_nonneg_factor : 0 <= c
    6.  contraction_lt_one_factor : c < 1
    7.  contraction_shrinks     : d(f x, f y) <= d(x, y)

  Section 2 — Q Metric Space:
    8.  Q_dist_nonneg          : 0 <= |x - y|
    9.  Q_dist_zero            : |x - x| == 0
    10. Q_dist_sym             : |x - y| == |y - x|
    11. Q_dist_triangle        : |x - z| <= |x - y| + |y - z|
    12. Q_cauchy_metric_equiv  : metric Cauchy <-> CauchyReal Cauchy

  Section 3 — QVec L-infinity Distance:
    13. list_max_dist_nonneg   : 0 <= list_max_dist l1 l2
    14. list_max_dist_zero     : list_max_dist l l == 0
    15. list_max_dist_sym      : list_max_dist l1 l2 == list_max_dist l2 l1
    16. list_max_dist_head_le  : |x - y| <= list_max_dist (x::xs) (y::ys)
    17. list_max_dist_tail_le  : lmd xs ys <= list_max_dist (x::xs) (y::ys)
    18. list_max_dist_triangle : triangle inequality for L-infinity
*)
