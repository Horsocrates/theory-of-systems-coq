(** * RealPointTopology.v — Topology basics on RealPoint classes (F-6)

    ================= E/R/R разбор: топология на точках =================
    Надстройка над метрикой F-5 (RealPointMetric.v) над setoid'ом F-10.

      Rules (L5)    : предикаты близости (шар, окрестность, открытость) +
                      их КОРРЕКТНОСТЬ на классах = Proper относительно
                      cauchy_equiv (топологическое свойство не зависит от
                      выбора процесса-представителя). Базовое правило —
                      cauchy_le уважает cauchy_equiv.
      Roles (L4)    : «шар / окрестность / открытое» = режимы рассмотрения
                      точек; «точка» (F-10), «расстояние» (F-5).
      Elements      : Коши-процессы-представители (nat->Q), P4.

    ДИАГНОСТИКА: топология живёт на КЛАССАХ (режим), а корректность = именно
    независимость от представителя (Proper). «Открытое множество точек» — не
    завершённый объект-множество, а предикат-режим над процессами.

    ЧЕСТНАЯ ГРАНИЦА: здесь — метрическая база топологии на классах (шар +
    корректность). ПОЛНАЯ компактность на RealPoint НЕ строится: над ℚ
    компактность урезана (см. книгу, Глава 5.2 — ℚ не компактно; доступны лишь
    uniform/Lebesgue-формы). Это направление честно оставлено открытым.

    Status: F-6 — метрическая топология на классах (Proper cauchy_le, шар,
            корректность), axiom-free; разблокирована F-5/F-10.
    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: May 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa Lia.
From Stdlib Require Import Setoid Morphisms.
From ToS Require Import CauchyReal.
From ToS Require Import RealPointSetoid.
From ToS Require Import RealPointMetric.

Local Open Scope cauchy_scope.

(* ===================================================================== *)
(*  Base rule: cauchy_le is well-defined on classes (respects ~~)         *)
(* ===================================================================== *)

Lemma cauchy_le_compat : forall a a' b b' : CauchySeq,
  a ~~ a' -> b ~~ b' -> cauchy_le a b -> cauchy_le a' b'.
Proof.
  intros a a' b b' Ha Hb Hle eps Heps.
  assert (He3 : 0 < eps * (1#3)) by lra.
  destruct (Ha _ He3) as [Na HNa].
  destruct (Hb _ He3) as [Nb HNb].
  destruct (Hle _ He3) as [Nc HNc].
  exists (Nat.max (Nat.max Na Nb) Nc). intros n Hn.
  assert (HnNa : (Na <= n)%nat) by lia.
  assert (HnNb : (Nb <= n)%nat) by lia.
  assert (HnNc : (Nc <= n)%nat) by lia.
  pose proof (HNa n HnNa) as A. apply Qabs_Qlt_condition in A. destruct A as [A1 A2].
  pose proof (HNb n HnNb) as B. apply Qabs_Qlt_condition in B. destruct B as [B1 B2].
  pose proof (HNc n HnNc) as C.
  lra.
Qed.

#[export] Instance cauchy_le_Proper :
  Proper (cauchy_equiv ==> cauchy_equiv ==> iff) cauchy_le.
Proof.
  intros a a' Ha b b' Hb. split; intro H.
  - exact (cauchy_le_compat a a' b b' Ha Hb H).
  - exact (cauchy_le_compat a' a b' b
             (cauchy_equiv_sym _ _ Ha) (cauchy_equiv_sym _ _ Hb) H).
Qed.

(* ===================================================================== *)
(*  Closed metric ball on RealPoint, well-defined on classes              *)
(* ===================================================================== *)

(** x lies within (closed) distance r of the centre c. *)
Definition rp_in_ball (c : RealPoint) (r : Q) (x : RealPoint) : Prop :=
  cauchy_le (rp_dist c x) (cauchy_const r).

(** Ball membership is a property of the POINT, not the representative. *)
Lemma rp_in_ball_well_defined : forall (c : RealPoint) (r : Q) (x x' : RealPoint),
  x ~~ x' -> (rp_in_ball c r x <-> rp_in_ball c r x').
Proof.
  intros c r x x' Hx. unfold rp_in_ball.
  rewrite (rp_dist_compat c c x x' (cauchy_equiv_refl c) Hx). reflexivity.
Qed.

(** The centre lies in its own ball of any positive radius. *)
Lemma rp_in_ball_centre : forall (c : RealPoint) (r : Q), 0 < r -> rp_in_ball c r c.
Proof.
  intros c r Hr. unfold rp_in_ball.
  rewrite (rp_dist_self_zero c).
  intros eps Heps. exists 0%nat. intros n _. rewrite !cs_const. lra.
Qed.

(* ===================================================================== *)
(*  The ball above is CLOSED; the open ball on classes (Nov 2026)          *)
(* ===================================================================== *)

From Stdlib Require Import Lia.

(** [rp_in_ball] is the closed ball: a point at distance exactly r belongs to it. *)
Lemma rp_in_ball_contains_boundary : rp_in_ball (cauchy_const 0) 1 (cauchy_const 1).
Proof.
  unfold rp_in_ball. intros eps Heps. exists 0%nat. intros n _.
  rewrite cs_rp_dist, !cs_const.
  assert (E : 0 - 1 == - (1)) by ring. rewrite (Qabs_wd _ _ E). simpl. lra.
Qed.

(** The open ball: a closed ball of a smaller radius. *)
Definition rp_in_open_ball (c : RealPoint) (r : Q) (x : RealPoint) : Prop :=
  exists q : Q, q < r /\ rp_in_ball c q x.

Lemma rp_in_open_ball_well_defined : forall (c : RealPoint) (r : Q) (x x' : RealPoint),
  x ~~ x' -> (rp_in_open_ball c r x <-> rp_in_open_ball c r x').
Proof.
  intros c r x x' Hx. unfold rp_in_open_ball.
  split; intros [q [Hq H]]; exists q; (split; [exact Hq|]).
  - apply (rp_in_ball_well_defined c q x x' Hx). exact H.
  - apply (rp_in_ball_well_defined c q x x' Hx). exact H.
Qed.

Lemma rp_in_open_ball_centre : forall (c : RealPoint) (r : Q), 0 < r -> rp_in_open_ball c r c.
Proof.
  intros c r Hr. exists (r * (1#2)). split; [lra|].
  apply rp_in_ball_centre. lra.
Qed.

(** The boundary point is not in the open ball. *)
Lemma rp_open_ball_excludes_boundary : ~ rp_in_open_ball (cauchy_const 0) 1 (cauchy_const 1).
Proof.
  intros [q [Hq H]]. unfold rp_in_ball in H.
  destruct (H ((1 - q) * (1#2)) ltac:(lra)) as [N HN].
  specialize (HN N (le_n _)).
  rewrite cs_rp_dist, !cs_const in HN.
  assert (E : 0 - 1 == - (1)) by ring. rewrite (Qabs_wd _ _ E) in HN. simpl in HN. lra.
Qed.

(** The open ball is open: with every point it contains a closed ball of a
    positive radius around that point. *)
Lemma rp_open_ball_is_open : forall (c : RealPoint) (r : Q) (x : RealPoint),
  rp_in_open_ball c r x ->
  exists e : Q, 0 < e /\ forall y : RealPoint, rp_in_ball x e y -> rp_in_open_ball c r y.
Proof.
  intros c r x [q [Hq H]].
  exists ((r - q) * (1#2)). split; [lra|].
  intros y Hy. exists (q + (r - q) * (1#2)). split; [lra|].
  unfold rp_in_ball in *. intros eps Heps.
  destruct (H (eps * (1#2)) ltac:(lra)) as [N1 HN1].
  destruct (Hy (eps * (1#2)) ltac:(lra)) as [N2 HN2].
  exists (Nat.max N1 N2). intros n Hn.
  specialize (HN1 n ltac:(lia)). specialize (HN2 n ltac:(lia)).
  rewrite cs_rp_dist, cs_const in *.
  assert (Htri : Qabs (cs_seq c n - cs_seq y n)
                 <= Qabs (cs_seq c n - cs_seq x n) + Qabs (cs_seq x n - cs_seq y n)).
  { assert (E : cs_seq c n - cs_seq y n
                == (cs_seq c n - cs_seq x n) + (cs_seq x n - cs_seq y n)) by ring.
    rewrite (Qabs_wd _ _ E). apply Qabs_triangle. }
  lra.
Qed.

Print Assumptions rp_in_ball_well_defined.
