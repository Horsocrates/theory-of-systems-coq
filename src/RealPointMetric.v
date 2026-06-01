(** * RealPointMetric.v — Metric on RealPoint classes (F-5), axiom-free

    ================= E/R/R разбор: расстояние между точками =================
    Надстройка над setoid'ом F-10 (RealPointSetoid.v). Генеративный порядок:

      Rules (L5)    : аксиомы метрики — неотрицательность, симметрия,
                      d(a,a)=0 / d=0 <-> a~~b (тождество неразличимых),
                      неравенство треугольника; + Proper (расстояние УВАЖАЕТ
                      правило тождества-точки, т.е. корректно на классах).
      Roles (L4)    : «расстояние между двумя точками» = (неотрицательная)
                      ТОЧКА (сам реал!); «точка» (из F-10).
      Elements      : Коши-процессы-представители (nat->Q); рациональные
                      приближения расстояния |P n - Q n| на каждом шаге (P4).

    ДИАГНОСТИКА: расстояние двух реалов — само РЕАЛ (процесс n |-> |P n - Q n|),
    а НЕ одно рациональное число. Принять его за рациональное = смешать роль
    (значение-приближаемое) с элементом (рациональным приближением) — частный
    случай корневой ошибки P4. Метрика живёт на КЛАССАХ (режим): корректность =
    Proper относительно cauchy_equiv (носитель-представитель не важен).

    Status: F-5 — метрика rp_dist на RealPoint (= CauchySeq до cauchy_equiv),
            axiom-free; разблокирована F-10. Готовит F-6 (топология на классах).
    STATUS: 18 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: May 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
From Stdlib Require Import Setoid Morphisms.
From ToS Require Import CauchyReal.
From ToS Require Import RealPointSetoid.

Local Open Scope cauchy_scope.

(* ===================================================================== *)
(*  cs_* : how cs_seq reduces through the operations (all by reflexivity) *)
(* ===================================================================== *)

Lemma cs_const : forall q n, cs_seq (cauchy_const q) n = q.
Proof. reflexivity. Qed.

Lemma cs_add : forall a b n, cs_seq (cauchy_add a b) n = cs_seq a n + cs_seq b n.
Proof. reflexivity. Qed.

Lemma cs_neg : forall a n, cs_seq (cauchy_neg a) n = - cs_seq a n.
Proof. reflexivity. Qed.

Lemma cs_sub : forall a b n, cs_seq (cauchy_sub a b) n = cs_seq a n - cs_seq b n.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  cauchy_abs : the absolute value of a real is a real                   *)
(* ===================================================================== *)

(** Reverse triangle in absolute-value form: | |x| - |y| | <= |x - y|. *)
Lemma Qabs_abs_sub_le : forall x y : Q, Qabs (Qabs x - Qabs y) <= Qabs (x - y).
Proof.
  intros x y.
  pose proof (Qabs_triangle_reverse x y) as H1.   (* |x|-|y| <= |x-y| *)
  pose proof (Qabs_triangle_reverse y x) as H2.    (* |y|-|x| <= |y-x| *)
  rewrite (Qabs_Qminus y x) in H2.                 (* |y-x| = |x-y| *)
  apply Qabs_Qle_condition. split; lra.
Qed.

Lemma cauchy_abs_is_cauchy (a : CauchySeq) : is_cauchy (fun n => Qabs (cs_seq a n)).
Proof.
  intros eps Heps. destruct (cs_cauchy a eps Heps) as [N HN].
  exists N. intros m n Hm Hn. simpl.
  eapply Qle_lt_trans.
  - apply Qabs_abs_sub_le.
  - apply HN; assumption.
Qed.

Definition cauchy_abs (a : CauchySeq) : CauchySeq :=
  mkCauchy _ (cauchy_abs_is_cauchy a).

Lemma cs_abs : forall a n, cs_seq (cauchy_abs a) n = Qabs (cs_seq a n).
Proof. reflexivity. Qed.

Lemma cauchy_abs_compat : forall a a' : CauchySeq,
  a ~~ a' -> cauchy_abs a ~~ cauchy_abs a'.
Proof.
  intros a a' H eps Heps. destruct (H eps Heps) as [N HN].
  exists N. intros n Hn. specialize (HN n Hn).
  rewrite !cs_abs.
  eapply Qle_lt_trans; [ apply Qabs_abs_sub_le | exact HN ].
Qed.

(* ===================================================================== *)
(*  Helper: pointwise-equal processes are equivalent                      *)
(* ===================================================================== *)

Lemma cauchy_equiv_pointwise : forall x y : CauchySeq,
  (forall n, cs_seq x n == cs_seq y n) -> x ~~ y.
Proof.
  intros x y Hpt eps Heps. exists 0%nat. intros n _.
  assert (E : cs_seq x n - cs_seq y n == 0) by (rewrite (Hpt n); ring).
  qabs_rw E.
  assert (HZ : Qabs 0 == 0) by (apply Qabs_pos; lra). lra.
Qed.

Lemma cauchy_sub_compat : forall a a' b b' : CauchySeq,
  a ~~ a' -> b ~~ b' -> cauchy_sub a b ~~ cauchy_sub a' b'.
Proof.
  intros a a' b b' Ha Hb. unfold cauchy_sub.
  apply cauchy_add_compat; [ exact Ha | apply cauchy_neg_compat; exact Hb ].
Qed.

(* ===================================================================== *)
(*  rp_dist : the distance between two real points — itself a real point  *)
(* ===================================================================== *)

Definition rp_dist (a b : RealPoint) : RealPoint := cauchy_abs (cauchy_sub a b).

Lemma cs_rp_dist : forall a b n,
  cs_seq (rp_dist a b) n = Qabs (cs_seq a n - cs_seq b n).
Proof. reflexivity. Qed.

(** Well-defined on classes: rp_dist respects cauchy_equiv in both args. *)
Lemma rp_dist_compat : forall a a' b b' : RealPoint,
  a ~~ a' -> b ~~ b' -> rp_dist a b ~~ rp_dist a' b'.
Proof.
  intros a a' b b' Ha Hb. unfold rp_dist.
  apply cauchy_abs_compat. apply cauchy_sub_compat; assumption.
Qed.

#[export] Instance rp_dist_Proper :
  Proper (cauchy_equiv ==> cauchy_equiv ==> cauchy_equiv) rp_dist.
Proof. intros a a' Ha b b' Hb. apply rp_dist_compat; assumption. Qed.

(* ===================================================================== *)
(*  Metric axioms                                                         *)
(* ===================================================================== *)

(** Non-negativity (pointwise: each rational approximation is >= 0). *)
Lemma rp_dist_nonneg : forall a b n, 0 <= cs_seq (rp_dist a b) n.
Proof. intros a b n. rewrite cs_rp_dist. apply Qabs_nonneg. Qed.

(** Symmetry: d(a,b) = d(b,a). *)
Lemma rp_dist_sym : forall a b : RealPoint, rp_dist a b ~~ rp_dist b a.
Proof.
  intros a b. apply cauchy_equiv_pointwise. intros n.
  rewrite !cs_rp_dist.
  rewrite (Qabs_Qminus (cs_seq a n) (cs_seq b n)). reflexivity.
Qed.

(** d(a,a) = 0. *)
Lemma rp_dist_self_zero : forall a : RealPoint, rp_dist a a ~~ cauchy_const 0.
Proof.
  intros a. apply cauchy_equiv_pointwise. intros n.
  rewrite cs_rp_dist, cs_const.
  assert (E : cs_seq a n - cs_seq a n == 0) by ring.
  qabs_rw E. apply Qabs_pos; lra.
Qed.

(** Identity of indiscernibles: d(a,b) = 0  <->  a ~~ b. *)
Lemma rp_dist_eq_zero_iff : forall a b : RealPoint,
  rp_dist a b ~~ cauchy_const 0 <-> a ~~ b.
Proof.
  intros a b.
  assert (Hkey : forall n,
    Qabs (cs_seq (rp_dist a b) n - cs_seq (cauchy_const 0) n)
      == Qabs (cs_seq a n - cs_seq b n)).
  { intros n. rewrite cs_rp_dist, cs_const.
    assert (E : Qabs (cs_seq a n - cs_seq b n) - 0
                == Qabs (cs_seq a n - cs_seq b n)) by ring.
    qabs_rw E. apply Qabs_pos. apply Qabs_nonneg. }
  split; intros H eps Heps; destruct (H eps Heps) as [N HN];
    exists N; intros n Hn; specialize (HN n Hn).
  - rewrite (Hkey n) in HN. exact HN.
  - rewrite (Hkey n). exact HN.
Qed.

(** Triangle inequality: d(a,c) <= d(a,b) + d(b,c). *)
Lemma rp_dist_triangle : forall a b c : RealPoint,
  cauchy_le (rp_dist a c) (cauchy_add (rp_dist a b) (rp_dist b c)).
Proof.
  intros a b c eps Heps. exists 0%nat. intros n _.
  rewrite cs_add, !cs_rp_dist.
  assert (Htri : Qabs (cs_seq a n - cs_seq c n)
                 <= Qabs (cs_seq a n - cs_seq b n) + Qabs (cs_seq b n - cs_seq c n)).
  { assert (E : cs_seq a n - cs_seq c n
                == (cs_seq a n - cs_seq b n) + (cs_seq b n - cs_seq c n)) by ring.
    qabs_rw E. apply Qabs_triangle. }
  lra.
Qed.

Print Assumptions rp_dist_triangle.
