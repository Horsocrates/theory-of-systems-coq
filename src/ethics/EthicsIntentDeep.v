(** * EthicsIntentDeep.v — Углублённая полярность умысла (Р-106…Р-114) как ToS System

    Деривация: Ш-58…Ш-64 сводного прохода (критерий зла; зеркало добра; механика
    притяжение/отталкивание; матрица «воля Другого × чей интерес»; внеполярные
    клетки; вид-удовольствие только у зла; проверка по адресату и времени).

    Elements: акты с признаками — умысел; отношение к воле Другого; чей интерес;
              притяжение/отталкивание собственной воли; мотив-удовольствие;
              защита-заявление (адресат и время действия).
    Roles:    полюса зло/добро — классификация актов; внеполярные клетки
              (патернализм, обмен); «просто правильный поступок» в клетке согласия.
    Rules:    зло = умысел + против воли Другого + ради своих целей;
              добро = согласно воле + ради его целей + без притяжения, из отталкивания;
              мотив-удовольствие есть вид притяжения (wf);
              заявленная цель обязана совпасть с адресатом действия.
    Status:   полюса на диагонали и исключают друг друга; патернализм и обмен вне
              полярности; клетка добра расщеплена притяжением; вид-удовольствие
              только у зла; без умысла нет зла; зло не проходит тест получателя (L2);
              рационализация «иду против беды» вскрывается адресатом.
    Честно:   формализована булева СТРУКТУРА критериев; «добрая натура»,
              градуальность сознания наблюдателя и нормативность — вне модели (проза).
    STATUS: 16 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: July 2026
*)

From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(* ===================================================================== *)
(*  Акт: субъектная сторона полярности умысла                            *)
(* ===================================================================== *)

Inductive WillRel := AgainstWill | AccordingWill.
Inductive Beneficiary := OwnGoals | OtherGoals.

Record Act : Type := {
  has_intent      : bool;        (* умысел присутствует (без умысла — вред/ошибка) *)
  will_rel        : WillRel;     (* отношение к воле Другого                       *)
  benef           : Beneficiary; (* чей интерес движет актом                       *)
  attraction      : bool;        (* притяжение собственной воли к акту             *)
  repulsion       : bool;        (* из отталкивания от неправильности не-делания   *)
  pleasure_motive : bool         (* мотив: собственное удовольствие                *)
}.

(* Дисциплина модели: мотив-удовольствие есть вид притяжения *)
Definition wf (a : Act) : Prop := pleasure_motive a = true -> attraction a = true.

(* ===================================================================== *)
(*  Полюса и клетки матрицы (воля Другого × чей интерес)                  *)
(* ===================================================================== *)

Definition evil (a : Act) : Prop :=
  has_intent a = true /\ will_rel a = AgainstWill /\ benef a = OwnGoals.

Definition good (a : Act) : Prop :=
  will_rel a = AccordingWill /\ benef a = OtherGoals /\
  attraction a = false /\ repulsion a = true.

Definition paternalism (a : Act) : Prop :=
  will_rel a = AgainstWill /\ benef a = OtherGoals.

Definition exchange (a : Act) : Prop :=
  will_rel a = AccordingWill /\ benef a = OwnGoals.

(* Клетка согласия при собственном притяжении: просто правильный поступок *)
Definition merely_correct (a : Act) : Prop :=
  will_rel a = AccordingWill /\ benef a = OtherGoals /\ attraction a = true.

(* ===================================================================== *)
(*  Без умысла нет зла (лев-пример: запер без умысла — вред, не зло)      *)
(* ===================================================================== *)

Theorem no_intent_no_evil : forall a, has_intent a = false -> ~ evil a.
Proof.
  intros a H (Hi & _ & _). rewrite H in Hi. discriminate.
Qed.

(* ===================================================================== *)
(*  Полюса на диагонали: исключают друг друга                            *)
(* ===================================================================== *)

Theorem evil_good_exclusive : forall a, evil a -> good a -> False.
Proof.
  intros a (_ & Hw & _) (Hw' & _). rewrite Hw in Hw'. discriminate.
Qed.

(* ===================================================================== *)
(*  Внедиагональные клетки — вне полярности                               *)
(* ===================================================================== *)

Theorem paternalism_not_evil : forall a, paternalism a -> ~ evil a.
Proof.
  intros a (_ & Hb) (_ & _ & Hb'). rewrite Hb in Hb'. discriminate.
Qed.

Theorem paternalism_not_good : forall a, paternalism a -> ~ good a.
Proof.
  intros a (Hw & _) (Hw' & _). rewrite Hw in Hw'. discriminate.
Qed.

Theorem exchange_not_evil : forall a, exchange a -> ~ evil a.
Proof.
  intros a (Hw & _) (_ & Hw' & _). rewrite Hw in Hw'. discriminate.
Qed.

Theorem exchange_not_good : forall a, exchange a -> ~ good a.
Proof.
  intros a (_ & Hb) (_ & Hb' & _). rewrite Hb in Hb'. discriminate.
Qed.

(* ===================================================================== *)
(*  Расщепление клетки добра: притяжение блокирует добро                  *)
(* ===================================================================== *)

Theorem attraction_blocks_good : forall a, attraction a = true -> ~ good a.
Proof.
  intros a Ha (_ & _ & Ha' & _). rewrite Ha in Ha'. discriminate.
Qed.

Theorem merely_correct_not_good : forall a, merely_correct a -> ~ good a.
Proof.
  intros a (_ & _ & Ha). apply attraction_blocks_good. exact Ha.
Qed.

(* ===================================================================== *)
(*  Вид-удовольствие — только у зла (асимметрия полюсов, Р-112)           *)
(* ===================================================================== *)

Theorem good_no_pleasure_motive :
  forall a, wf a -> good a -> pleasure_motive a = false.
Proof.
  intros a Hwf Hg. destruct (pleasure_motive a) eqn:Hp; [ | reflexivity ].
  apply Hwf in Hp. destruct Hg as (_ & _ & Hattr & _).
  rewrite Hp in Hattr. discriminate.
Qed.

Theorem sadistic_evil_exists :
  exists a, wf a /\ evil a /\ pleasure_motive a = true.
Proof.
  exists {| has_intent := true; will_rel := AgainstWill; benef := OwnGoals;
            attraction := true; repulsion := false; pleasure_motive := true |}.
  split; [ | split ].
  - intros _. reflexivity.
  - unfold evil; simpl. repeat split.
  - reflexivity.
Qed.

Theorem good_act_exists : exists a, wf a /\ good a.
Proof.
  exists {| has_intent := true; will_rel := AccordingWill; benef := OtherGoals;
            attraction := false; repulsion := true; pleasure_motive := false |}.
  split.
  - intros H. discriminate.
  - unfold good; simpl. repeat split.
Qed.

(* ===================================================================== *)
(*  Тест получателя (L2, неуниверсализуемость исключения-для-себя):       *)
(*  получатель злого акта его не волит — по построению                    *)
(* ===================================================================== *)

Definition endorsed_by_receiver (a : Act) : Prop := will_rel a = AccordingWill.

Theorem evil_fails_receiver_test :
  forall a, evil a -> ~ endorsed_by_receiver a.
Proof.
  intros a (_ & Hw & _) Hw'. unfold endorsed_by_receiver in Hw'.
  rewrite Hw in Hw'. discriminate.
Qed.

(* ===================================================================== *)
(*  Решаемость полюсов (эхо correct_dec: статус вычислим над актом)       *)
(* ===================================================================== *)

Definition evil_b (a : Act) : bool :=
  has_intent a
  && (match will_rel a with AgainstWill => true | AccordingWill => false end)
  && (match benef a with OwnGoals => true | OtherGoals => false end).

Definition good_b (a : Act) : bool :=
  (match will_rel a with AccordingWill => true | AgainstWill => false end)
  && (match benef a with OtherGoals => true | OwnGoals => false end)
  && negb (attraction a) && repulsion a.

Lemma evil_b_reflect : forall a, evil_b a = true <-> evil a.
Proof.
  intros a. unfold evil_b, evil.
  destruct (has_intent a), (will_rel a), (benef a); simpl; intuition congruence.
Qed.

Lemma good_b_reflect : forall a, good_b a = true <-> good a.
Proof.
  intros a. unfold good_b, good.
  destruct (will_rel a), (benef a), (attraction a), (repulsion a); simpl;
    intuition congruence.
Qed.

(* ===================================================================== *)
(*  Проверка по адресату и времени (Р-108): след скрытого умысла          *)
(* ===================================================================== *)

Inductive Target := TheTrouble | TheChoice.

Record Defense : Type := {
  claimed : Target;   (* заявленная цель («иду против беды»)        *)
  address : Target;   (* фактический адресат действия               *)
  early   : bool      (* пришло ли действие раньше момента выбора   *)
}.

Definition honest_defense (d : Defense) : Prop := claimed d = address d.

(* Рационализация патернализма: заявлена беда, адресован чужой выбор *)
Definition rationalization (d : Defense) : Prop :=
  claimed d = TheTrouble /\ address d = TheChoice.

Theorem rationalization_dishonest :
  forall d, rationalization d -> ~ honest_defense d.
Proof.
  intros d (Hc & Ha) He. unfold honest_defense in He.
  rewrite Hc, Ha in He. discriminate.
Qed.

(* Подлинное действие против беды: адресовано беде и приходит раньше *)
Theorem genuine_anti_trouble_exists :
  exists d, honest_defense d /\ address d = TheTrouble /\ early d = true.
Proof.
  exists {| claimed := TheTrouble; address := TheTrouble; early := true |}.
  repeat split.
Qed.
