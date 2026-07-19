(** * EthicsTrueOrder.v — Истинный порядок и мера-согласование-вверх (Р-110, Р-113)

    Деривация: Ш-40…Ш-41 сводного прохода (порядок-вообще vs истинный порядок;
    мера истинности = согласование вверх по иерархии объемлющих систем).

    Elements: башня уровней — система (уровень 0) и её объемлющие до предельной
              инстанции (уровень height); задача системы как роль на каждом уровне.
    Roles:    правильность задачи на уровне k; локальная оптимальность (внутри
              своей задачи); истинность (правильность на каждом уровне вверх).
    Rules:    истинный порядок = замыкание оси правильности по всей вертикали;
              регресс конечен (height — предельная инстанция, сама Логика).
    Status:   истинный влечёт локальную оптимальность; обратное ложно (мафия);
              мера решаема конечной проверкой; вершина входит в меру;
              единственность истинного порядка не следует (пул равно-наилучших).
    Честно:   уровни и правильность абстрактны (bool на nat); СОДЕРЖАНИЕ
              правильности на уровне — из EthicsStatus (соответствие); мера —
              структура, не вердикт о конкретных обществах.
    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: July 2026
*)

From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(* ===================================================================== *)
(*  Башня объемлющих систем                                              *)
(* ===================================================================== *)

Record Tower : Type := {
  height     : nat;          (* уровни 0..height; height = предельная инстанция *)
  correct_at : nat -> bool   (* правильность задачи как роли на уровне k        *)
}.

(* Локальная оптимальность: правильность внутри собственной задачи *)
Definition locally_optimal (t : Tower) : Prop := correct_at t 0 = true.

(* Истинный порядок: правильность на КАЖДОМ уровне вверх (согласование) *)
Definition true_order (t : Tower) : Prop :=
  forall k, k <= height t -> correct_at t k = true.

(* ===================================================================== *)
(*  Истинный порядок сильнее локальной оптимальности                     *)
(* ===================================================================== *)

Theorem true_implies_local : forall t, true_order t -> locally_optimal t.
Proof.
  intros t H. apply H. lia.
Qed.

(* Мафия: эффективна внутри своей задачи, ломает объемлющий уровень *)
Definition mafia : Tower :=
  {| height := 1;
     correct_at := fun k => match k with 0 => true | _ => false end |}.

Theorem mafia_locally_optimal : locally_optimal mafia.
Proof. reflexivity. Qed.

Theorem mafia_not_true_order : ~ true_order mafia.
Proof.
  intros H. pose proof (H 1 (le_n 1)) as Hf. simpl in Hf. discriminate.
Qed.

Theorem local_does_not_imply_true :
  exists t, locally_optimal t /\ ~ true_order t.
Proof.
  exists mafia. split.
  - apply mafia_locally_optimal.
  - apply mafia_not_true_order.
Qed.

(* ===================================================================== *)
(*  Ломающий объемлющее — не истинный                                     *)
(* ===================================================================== *)

Theorem breaks_above_not_true :
  forall t j, j <= height t -> correct_at t j = false -> ~ true_order t.
Proof.
  intros t j Hj Hf H. specialize (H j Hj). rewrite H in Hf. discriminate.
Qed.

(* ===================================================================== *)
(*  Мера решаема: регресс конечен — проверка добегает до вершины          *)
(* ===================================================================== *)

Definition true_order_b (t : Tower) : bool :=
  forallb (correct_at t) (seq 0 (S (height t))).

Lemma true_order_b_reflect :
  forall t, true_order_b t = true <-> true_order t.
Proof.
  intros t. unfold true_order_b, true_order. rewrite forallb_forall. split.
  - intros H k Hk. apply H. rewrite in_seq. lia.
  - intros H x Hx. rewrite in_seq in Hx. apply H. lia.
Qed.

(* Предельная инстанция входит в меру *)
Theorem apex_checked : forall t, true_order t -> correct_at t (height t) = true.
Proof.
  intros t H. apply H. lia.
Qed.

(* ===================================================================== *)
(*  Единственность не следует: пул равно-наилучших возможен               *)
(*  (открытый хвост Р-113 — структурно честно)                            *)
(* ===================================================================== *)

Definition all_true (h : nat) : Tower :=
  {| height := h; correct_at := fun _ => true |}.

Theorem all_true_is_true_order : forall h, true_order (all_true h).
Proof.
  intros h k _. reflexivity.
Qed.

Theorem true_order_not_unique :
  exists t1 t2, t1 <> t2 /\ true_order t1 /\ true_order t2.
Proof.
  exists (all_true 0), (all_true 1). split; [ | split ].
  - intros H.
    assert (Hh : height (all_true 0) = height (all_true 1))
      by (rewrite H; reflexivity).
    simpl in Hh. discriminate.
  - apply all_true_is_true_order.
  - apply all_true_is_true_order.
Qed.
