(** * EthicsEvil.v — Зло как статус ¬правильного (Н-8, СТРУКТУРА)

    Elements: «неправое» (вид намерения + магнитуда); акт (деятель/затронутый);
              содержание (заполнено? соответствует?); мотив.
    Roles:    зло = НЕправый исход С не-правда-ВИДОМ (намерение); наказуемость = реляционна;
              статус зла = заполнено-но-несоответственно; мотив = инструментальный.
    Rules:    критерий (искажение НАМЕРЕНИЯ); L2 (зло движется к A≠A — не достигает);
              реляционность (Р-32/59); правильно = соответствие (Р-76).
    Status:   формализована СТРУКТУРА зла — критерий (вид, не магнитуда), реляционность
              наказуемости, положительно-реально-но-несоответственно (НЕ privatio-как-ничто),
              инструментальность (нет радикального). НЕ ценностное суждение.
    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026

    Прозаический грунт: Книги/Этика/00 Этика — рабочая запись.md — Р-53 (вид⊥магнитуда),
      Р-59 (реляционность; зло-к-себе), Р-79/80 (критерий; положительно-реально-но-несоответственно;
      инструментально, нет радикального).
    ЧЕСТНОСТЬ (стена): кодируется СТРУКТУРА. «Нет радикального зла» формализовано как МОДЕЛЬНЫЙ выбор —
      тип Motive по построению несёт лишь инструментальные конструкторы (отражает тезис Р-79, не
      доказывает невозможность вообще). «Зло есть плохо» — не теорема (проза).
*)

From Stdlib Require Import Arith.
From ToS Require Import ethics.EthicsStatus ethics.EthicsModality.

(* ===================================================================== *)
(*  I. КРИТЕРИЙ: зло привязано к ВИДУ (намерение=не-правда), не к магнитуде *)
(* ===================================================================== *)

(** вид w = false (не-правда) ⇒ зло; вид w = true (правда) ⇒ (честная) ошибка. *)
Definition is_evil  (w : Wrong) : Prop := vid w = false.
Definition is_error (w : Wrong) : Prop := vid w = true.

Theorem evil_xor_error : forall w, is_evil w \/ is_error w.
Proof. intro w. unfold is_evil, is_error. destruct (vid w); [right|left]; reflexivity. Qed.

Theorem evil_not_error : forall w, is_evil w -> ~ is_error w.
Proof. intros w He Hr. unfold is_evil, is_error in *. rewrite He in Hr. discriminate. Qed.

(** Глубокая ЧЕСТНАЯ ошибка (любой магнитуды) — НЕ зло (Р-53). *)
Theorem deep_error_not_evil : forall m, is_error (mkWrong true m).
Proof. intro m. unfold is_error. reflexivity. Qed.

(** Мелкая ЛОЖЬ — зло. *)
Theorem shallow_lie_is_evil : is_evil (mkWrong false 1).
Proof. unfold is_evil. reflexivity. Qed.

(** Зло НЕ зависит от магнитуды (тот же вид при любой глубине). *)
Theorem evil_independent_of_magn : forall m1 m2,
  is_evil (mkWrong false m1) /\ is_evil (mkWrong false m2).
Proof. intros m1 m2. split; reflexivity. Qed.

(* ===================================================================== *)
(*  II. РЕЛЯЦИОННОСТЬ: вина/наказание ⟺ ВТОРОЙ затронутый (Р-59)          *)
(* ===================================================================== *)

Record EvilAct := mkEvilAct { actor : nat ; affected : nat ; w : Wrong }.

Definition internal (a : EvilAct) : Prop := affected a = actor a.
Definition external (a : EvilAct) : Prop := affected a <> actor a.

(** Наказуемо ⟺ зло-вид ∧ внешний затронутый (нужен ВТОРОЙ пострадавший). *)
Definition punishable (a : EvilAct) : Prop := is_evil (w a) /\ external a.

(** Внутреннее не-правда = зло-СЕБЕ, НЕ наказуемо (нет второго затронутого, Р-59). *)
Theorem internal_not_punishable : forall a, internal a -> ~ punishable a.
Proof.
  intros a Hi [_ Hext]. unfold internal in Hi. unfold external in Hext.
  apply Hext; exact Hi.
Qed.

(** Внешняя ЧЕСТНАЯ ошибка (вред другому, но намерение-правда) — НЕ наказуема
    (остаётся лишь возмещение — см. EthicsResponsibility). *)
Theorem external_error_not_punishable : forall a,
  external a -> is_error (w a) -> ~ punishable a.
Proof.
  intros a Hext Her [Hev _]. apply (evil_not_error (w a) Hev). exact Her.
Qed.

(* ===================================================================== *)
(*  III. СТАТУС: положительно реально, но НЕсоответственно (Р-79)         *)
(*      (НЕ privatio-как-ничто: заполнено ∧ ¬соответствует)               *)
(* ===================================================================== *)

Record Content := mkContent { filled : bool ; corresponds : bool }.

Definition pravda_content (c : Content) : Prop := filled c = true /\ corresponds c = true.
Definition illusion      (c : Content) : Prop := filled c = true /\ corresponds c = false.
Definition empty_content (c : Content) : Prop := filled c = false.

(** Иллюзия (зло-контент) НЕ пуста — имеет субстанцию (заполнено). *)
Theorem illusion_not_empty : forall c, illusion c -> ~ empty_content c.
Proof. intros c [Hf _] He. unfold empty_content in He. rewrite Hf in He. discriminate. Qed.

(** ...но и НЕ соответствует (ложно): дефицит в СООТВЕТСТВИИ, не в бытии. *)
Theorem illusion_not_corresponds : forall c, illusion c -> corresponds c = false.
Proof. intros c [_ Hc]. exact Hc. Qed.

(** Отличие иллюзии от правды-контента — ТОЛЬКО в соответствии (заполнены оба). *)
Theorem illusion_vs_pravda_same_filled : forall c1 c2,
  illusion c1 -> pravda_content c2 -> filled c1 = filled c2.
Proof. intros c1 c2 [H1 _] [H2 _]. rewrite H1, H2. reflexivity. Qed.

(* ===================================================================== *)
(*  IV. ИНСТРУМЕНТАЛЬНОСТЬ: всё зло за собственной выгодой; РАДИКАЛЬНОГО НЕТ *)
(* ===================================================================== *)

(** Мотивы — по построению лишь инструментальные (виды собственной выгоды);
    конструктора «беспорядок/A≠A-как-цель» НЕТ (модельный тезис Р-79, Сократ). *)
Inductive Motive := OwnBenefit | AvoidPain.

Theorem no_radical_motive : forall m : Motive, m = OwnBenefit \/ m = AvoidPain.
Proof. intros [|]; [left|right]; reflexivity. Qed.
