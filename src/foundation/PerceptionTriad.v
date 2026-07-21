(** * PerceptionTriad.v — Три проявления Логики как ToS System (E/R/R)

    Формализация-подтверждение деривации (справочник «Метафизика», правка раздела IX,
    2026-06-15): акт восприятия по ЗДО раскладывается РОВНО на три конституирующих
    момента, каждый из них необходим, а направленность (воля/внимание) — ОТДЕЛЬНАЯ ось,
    не четвёртый момент (самадхи: направленность -> минимум, восприятие сохраняется).

    Соответствие справочнику: Свидетель (§II) — кто; потенциал->актуализация (§IV–V);
    нирвикальпа-самадхи (§XII) — отделимость направленности; принцип познаваемости (§IX).

    Elements: Свидетель (носитель = запись акта), потенция, акт, среда, направленность.
    Roles:    Сознание = потенция (возможность, градуальна: nat);
              Разум    = акт (действующая способность);
              Ментал   = среда (медиум восприятия);
              Воля/внимание = направленность (отдельная ось, не момент);
              Свидетель = кто (носитель трёх моментов).
    Rules:    R1 познаваемость; R2 ЗДО => акт со всеми моментами; R3 потенциал->актуализация;
              R4 необходимость каждого момента; R5 направленность логически после конституции.
    Status:   акт восприятия = присутствие всех трёх моментов; ровно три; воля отделима.
    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* ===================================================================== *)
(*  Три конституирующих момента акта восприятия (субъектная сторона)      *)
(* ===================================================================== *)

Inductive Moment : Type :=
  | Potency    (* Сознание — возможность воспринимать (потенция)        *)
  | Actuality  (* Разум    — что воспринимает (актуализация потенции)   *)
  | Medium.    (* Ментал   — чем воспринимает (среда/медиум)            *)

Definition all_moments : list Moment := [Potency; Actuality; Medium].

(* ---- «Ровно три»: перечисление полно, длина 3, без повторов ---- *)

Theorem moments_exhaustive : forall m : Moment, In m all_moments.
Proof.
  intros m; unfold all_moments; destruct m; simpl.
  - left; reflexivity.
  - right; left; reflexivity.
  - right; right; left; reflexivity.
Qed.

Theorem moments_count_three : length all_moments = 3.
Proof. reflexivity. Qed.

Theorem moments_nodup : NoDup all_moments.
Proof.
  unfold all_moments.
  apply NoDup_cons.
  - simpl. intros [H | [H | H]]; try discriminate; contradiction.
  - apply NoDup_cons.
    + simpl. intros [H | H]; try discriminate; contradiction.
    + apply NoDup_cons.
      * simpl. intros H; contradiction.
      * apply NoDup_nil.
Qed.

(* ===================================================================== *)
(*  Акт восприятия как запись (Свидетель — носитель)                      *)
(* ===================================================================== *)

Record PerceptAct : Type := {
  potency : nat;    (* Сознание: степень возможности; 0 = наблюдателя нет     *)
  acting  : bool;   (* Разум:    идёт ли актуализация (восприятие)            *)
  medium  : bool;   (* Ментал:   присутствует ли среда восприятия             *)
  aim     : nat     (* Воля/внимание: степень направленности; 0 = расплылось  *)
}.

(* Восприятие СОВЕРШАЕТСЯ <=> присутствуют все три момента.
   Заметьте: aim (направленность) НЕ входит в условие. *)
Definition perceives (a : PerceptAct) : Prop :=
  potency a > 0 /\ acting a = true /\ medium a = true.

(* Присутствие конкретного момента (Prop-значное) *)
Definition moment_present (a : PerceptAct) (m : Moment) : Prop :=
  match m with
  | Potency   => potency a > 0
  | Actuality => acting a = true
  | Medium    => medium a = true
  end.

(* ---- Восприятие = присутствие ВСЕХ трёх (и только трёх) моментов ---- *)
Theorem perceives_iff_all_moments :
  forall a, perceives a <-> (forall m, moment_present a m).
Proof.
  intros a. unfold perceives. split.
  - intros (Hp & Ha & Hm) m. destruct m; simpl; assumption.
  - intros H. split; [ | split ].
    + exact (H Potency).
    + exact (H Actuality).
    + exact (H Medium).
Qed.

(* ===================================================================== *)
(*  R4: необходимость каждого момента (убери любой — акта нет)            *)
(* ===================================================================== *)

Theorem act_requires_potency : forall a, perceives a -> potency a > 0.
Proof. intros a [Hp _]. exact Hp. Qed.

Theorem perception_requires_act : forall a, perceives a -> acting a = true.
Proof. intros a (_ & Ha & _). exact Ha. Qed.

Theorem perception_requires_medium : forall a, perceives a -> medium a = true.
Proof. intros a (_ & _ & Hm). exact Hm. Qed.

Theorem no_potency_no_perception : forall a, potency a = 0 -> ~ perceives a.
Proof. intros a H0 [Hp _]. rewrite H0 in Hp. lia. Qed.

Theorem no_act_no_perception : forall a, acting a = false -> ~ perceives a.
Proof. intros a Ha (_ & Ha' & _). rewrite Ha in Ha'. discriminate. Qed.

Theorem no_medium_no_perception : forall a, medium a = false -> ~ perceives a.
Proof. intros a Hm (_ & _ & Hm'). rewrite Hm in Hm'. discriminate. Qed.

(* ===================================================================== *)
(*  Направленность (воля/внимание) — отдельная ось, не момент            *)
(* ===================================================================== *)

(* Перенастройка направленности не трогает три конституирующих момента *)
Definition set_aim (a : PerceptAct) (n : nat) : PerceptAct :=
  {| potency := potency a; acting := acting a; medium := medium a; aim := n |}.

(* Восприятие не зависит от направленности: aim не конституирует акт *)
Theorem perception_independent_of_aim :
  forall a n, perceives a <-> perceives (set_aim a n).
Proof.
  intros a n. unfold perceives, set_aim; simpl. tauto.
Qed.

(* Самадхи: восприятие сохраняется при направленности = 0 *)
Theorem samadhi_perception_without_aim :
  exists a, perceives a /\ aim a = 0.
Proof.
  exists {| potency := 1; acting := true; medium := true; aim := 0 |}.
  split.
  - unfold perceives; simpl. split; [ lia | split; reflexivity ].
  - reflexivity.
Qed.

(* Нижняя точка градуальной шкалы: восприятие при сознании = 1 (минимум > 0) *)
Theorem samadhi_minimum :
  exists a, potency a = 1 /\ perceives a.
Proof.
  exists {| potency := 1; acting := true; medium := true; aim := 0 |}.
  split.
  - reflexivity.
  - unfold perceives; simpl. split; [ lia | split; reflexivity ].
Qed.

(* Сфокусированность = восприятие + направленность *)
Definition focused (a : PerceptAct) : Prop := perceives a /\ aim a > 0.

(* R5: направленность ПРЕДПОЛАГАЕТ уже-конституированное восприятие *)
Theorem focus_presupposes_perception : forall a, focused a -> perceives a.
Proof. intros a [Hperc _]. exact Hperc. Qed.

(* Восприятие без фокуса существует (самадхи): фокус — строго добавочный слой *)
Theorem unfocused_perception_exists :
  exists a, perceives a /\ ~ focused a.
Proof.
  exists {| potency := 1; acting := true; medium := true; aim := 0 |}.
  split.
  - unfold perceives; simpl. split; [ lia | split; reflexivity ].
  - unfold focused; simpl. intros [_ Haim]. simpl in Haim. lia.
Qed.
