(** * EthicsStatus.v — «Правильно = соответствие» как ToS-система (СТРУКТУРА)

    Elements: кандидаты-элементы, моделируемые степенью соответствия (fit : nat) телосу роли;
              роль задаёт порог thr (ЗДО-гейт) и — для режима B — цель tgt.
    Roles:    fit = соответствие элемента роли; порог = ЗДО-гейт кандидатуры;
              отбор (b) = выбор лучшего из пула: A = argmax / B = мин-отклонение (анти-overqualified).
    Rules:    L4 (ЗДО-порог: подходит ⟺ соответствие ≥ порога); L5 (порядок отбора).
    Status:   формализована СТРУКТУРА статуса «правильно» — решаемый гейт (a), отбор (b),
              множественно-правильное = ничья, анти-overqualified для B. НЕ ценностное суждение.
    STATUS: 15 Qed, 0 Admitted, 0 axioms (Print Assumptions: Closed under the global context)
    Author: Horsocrates | Date: June 2026

    Прозаический грунт: Книги/Этика/00 Этика — рабочая запись.md — Р-46 (ось (a)+(b)),
      Р-50 (режимы A/B + анти-overqualified = глобальная аллокация), Р-76 (правильно = соответствие).
    ЧЕСТНОСТЬ (стена): Coq кодирует СТРУКТУРУ соответствия/отбора; «правильно есть благо» —
      не теорема Coq, а прозаический тезис (Р-40/76). 0 аксиом, всё Qed, всё конструктивно/decidable.
*)

From Stdlib Require Import Arith Lia List.
Import ListNotations.

(* ===================================================================== *)
(*  (a) ЗДО-ГЕЙТ: правильно = соответствие ≥ порога (РЕШАЕМО)             *)
(* ===================================================================== *)

(** Степень соответствия элемента телосу роли — [fit : nat].
    «Правильно» (подходит роли) ⟺ соответствие достигает порога ЗДО. *)
Definition correct (thr fit : nat) : Prop := thr <= fit.

(** Статус «правильно/неправильно» РЕШАЕМ (не интуиция-оракул). *)
Theorem correct_dec : forall thr fit, {correct thr fit} + {~ correct thr fit}.
Proof.
  intros thr fit. unfold correct. destruct (thr <=? fit) eqn:E.
  - left. exact (proj1 (Nat.leb_le thr fit) E).
  - right. intro H. apply (proj2 (Nat.leb_le thr fit)) in H.
    rewrite H in E. discriminate.
Qed.

(** L3-локально на статусе: подходит ИЛИ не подходит — без третьего. *)
Theorem correct_or_not : forall thr fit, correct thr fit \/ ~ correct thr fit.
Proof. intros thr fit. destruct (correct_dec thr fit); [left|right]; assumption. Qed.

(** Булева реализация гейта и её адекватность. *)
Definition passes (thr fit : nat) : bool := thr <=? fit.

Theorem passes_reflect : forall thr fit, passes thr fit = true <-> correct thr fit.
Proof. intros thr fit. unfold passes, correct. apply Nat.leb_le. Qed.

(* ===================================================================== *)
(*  ПУЛ КАНДИДАТОВ = элементы, прошедшие ЗДО-гейт                         *)
(* ===================================================================== *)

(** Список fit-значений; пул = прошедшие порог (Р-46 «первичный подбор»). *)
Definition pool (thr : nat) (l : list nat) : list nat := filter (passes thr) l.

Theorem in_pool_iff : forall thr l v,
  In v (pool thr l) <-> In v l /\ correct thr v.
Proof.
  intros thr l v. unfold pool. rewrite filter_In.
  split; intros [H1 H2]; split; try exact H1.
  - exact (proj1 (passes_reflect thr v) H2).
  - exact (proj2 (passes_reflect thr v) H2).
Qed.

Theorem pool_correct : forall thr l v, In v (pool thr l) -> correct thr v.
Proof. intros thr l v H. apply in_pool_iff in H. tauto. Qed.

(** Пустой пул ⟺ ни один элемент не подходит. *)
Theorem pool_nil_iff : forall thr l,
  pool thr l = [] <-> (forall v, In v l -> ~ correct thr v).
Proof.
  intros thr l. split.
  - intros H v Hin Hp.
    assert (In v (pool thr l)) as Hcon by (apply in_pool_iff; split; assumption).
    rewrite H in Hcon. inversion Hcon.
  - intros H. unfold pool. induction l as [|x xs IH]; simpl.
    + reflexivity.
    + destruct (passes thr x) eqn:E.
      * exfalso. apply (H x).
        -- left; reflexivity.
        -- exact (proj1 (passes_reflect thr x) E).
      * apply IH. intros v Hin. apply H. right; assumption.
Qed.

(* ===================================================================== *)
(*  (b) ОТБОР — РЕЖИМ A: лучший = argmax соответствия (Р-50 режим A)      *)
(* ===================================================================== *)

Definition maxfit (l : list nat) : nat := fold_right Nat.max 0 l.

(** Лучший доминирует: maxfit — верхняя грань всех соответствий пула. *)
Theorem maxfit_upper : forall l v, In v l -> v <= maxfit l.
Proof.
  induction l as [|x xs IH]; intros v Hin; simpl in *.
  - contradiction.
  - destruct Hin as [->|Hin].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (maxfit xs).
      * apply IH; exact Hin.
      * apply Nat.le_max_r.
Qed.

(** Непустой список содержит лучшего (максимум ДОСТИГАЕТСЯ — отбор не пуст). *)
Theorem maxfit_attained : forall l, l <> [] -> In (maxfit l) l.
Proof.
  induction l as [|x xs IH]; intros Hne.
  - exfalso; apply Hne; reflexivity.
  - destruct xs as [|y ys].
    + unfold maxfit; simpl. rewrite Nat.max_0_r. left; reflexivity.
    + assert (Hne' : (y :: ys) <> []) by discriminate.
      specialize (IH Hne').
      replace (maxfit (x :: y :: ys)) with (Nat.max x (maxfit (y :: ys)))
        by reflexivity.
      destruct (Nat.max_dec x (maxfit (y :: ys))) as [E|E].
      * rewrite E. left; reflexivity.
      * rewrite E. right; exact IH.
Qed.

(* ===================================================================== *)
(*  МНОЖЕСТВЕННО-ПРАВИЛЬНОЕ = ничья в отборе (Р-42/46): ≥2 равно-лучших   *)
(* ===================================================================== *)

Definition tie_at (l : list nat) (best : nat) : Prop :=
  exists i j, i <> j /\ nth_error l i = Some best /\ nth_error l j = Some best.

(** Конкретная ничья: два кандидата с одинаковым лучшим соответствием 5. *)
Example mult_correct_example : tie_at [5; 5; 3] 5.
Proof.
  exists 0, 1. split; [discriminate | split; reflexivity].
Qed.

(** Ничья ⇒ свобода выбора (P4): оба варианта правильны при пороге ≤ best. *)
Theorem tie_both_correct : forall l best thr,
  correct thr best -> tie_at l best ->
  correct thr best /\ correct thr best.
Proof. intros l best thr Hp _. split; exact Hp. Qed.

(* ===================================================================== *)
(*  (b) ОТБОР — РЕЖИМ B: «впору» = мин-отклонение; АНТИ-OVERQUALIFIED    *)
(*      (Р-50: глобальная аллокация — перебор сверх цели расточителен)    *)
(* ===================================================================== *)

Definition dist (a b : nat) : nat := (a - b) + (b - a).

Theorem dist_sym : forall a b, dist a b = dist b a.
Proof. intros a b. unfold dist. lia. Qed.

Theorem dist_refl : forall a, dist a a = 0.
Proof. intro a. unfold dist. lia. Qed.

(** АНТИ-OVERQUALIFIED: при цели tgt, среди соответствий ≥ tgt
    меньшее (ближе к мерке) отклоняется НЕ БОЛЬШЕ, чем большее (overqualified). *)
Theorem anti_overqualified : forall tgt f1 f2,
  tgt <= f1 -> f1 <= f2 -> dist f1 tgt <= dist f2 tgt.
Proof. intros tgt f1 f2 H1 H2. unfold dist. lia. Qed.

(** Точная мерка (f = tgt) отклоняется на 0 — идеально впору. *)
Theorem exact_fit_zero : forall tgt, dist tgt tgt = 0.
Proof. intro tgt. apply dist_refl. Qed.

(* ===================================================================== *)
(*  СВЯЗКА (a)+(b): резкий порог + градуальная высота на стороне правильно *)
(* ===================================================================== *)

(** Над порогом всё «правильно», но (b) даёт ПОРЯДОК-высоту: лучший доминирует. *)
Theorem threshold_then_height : forall thr l v,
  In v (pool thr l) -> correct thr v /\ v <= maxfit (pool thr l).
Proof.
  intros thr l v H. split.
  - exact (pool_correct thr l v H).
  - apply maxfit_upper; exact H.
Qed.
