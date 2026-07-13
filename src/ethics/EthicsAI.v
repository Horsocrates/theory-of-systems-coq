(** * EthicsAI.v — Мост этики к ИИ (вторая волна, СТРУКТУРА)

    Elements: ИИ-оператор (субстрат-агностичный §X-chooser); акт = техника × воля;
              затронутый; создатели (носители ответственности, если ИИ не свободен).
    Roles:    ИИ = ОПЕРАТОР (та же этика, универсально); техника = слой AIInterface /
              AI_FallacyDetector; воля = вклад этики; наказание на ИИ ⟺ он свободен, иначе → создатели.
    Rules:    оператор-нейтральность; техника ⊥ воля (Р-65); обман = воля-не-правда (= is_evil, Р-79);
              перенос-по-свободе (Р-56/62).
    Status:   формализована СТРУКТУРА моста — техника-безопасность НЕ влечёт alignment (deceptive-yet-correct
              софист-ИИ); ответственность-шарнир (свободен→ИИ / нет→создатели); ИИ-мудрость = единство.
    STATUS: 7 Qed, 0 Admitted, 0 axioms (Print Assumptions: Closed under the global context)
    Author: Horsocrates | Date: June 2026

    Прозаический грунт: Книги/Этика/00 Этика — рабочая запись.md — Р-85 (ИИ-этика: аффордансы+границы),
      Р-65 (техника⊥воля), Р-79 (зло=воля-не-правда), Р-56/62 (перенос-по-свободе).
    Связь (концептуальная, в комментариях): техника-безопасность ≈ AIInterface.v «passes typecheck ⇒ safe»
      и Architecture_of_Reasoning/AI_FallacyDetector.v (6 доменов, нет ошибки); здесь техника моделируется
      АБСТРАКТНО (порог), без импорта тяжёлой Expr-машинерии.
    ЧЕСТНОСТЬ (стена): формализован УСЛОВНЫЙ каркас (IF свободен THEN ответствен ELSE перенос-к-создателям).
      Сам ШАРНИР «есть ли у ИИ воля/§X» — ОТКРЫТ (воля-ветка, метафизика §X), здесь НЕ решается.
      Операционного моста код↔реальные ИИ-внутренности НЕТ (техника/воля = заданные флаги). 0 аксиом.
*)

From Stdlib Require Import Arith Lia.
From ToS Require Import ethics.EthicsPathWisdom.

(* ===================================================================== *)
(*  I. ОПЕРАТОР-НЕЙТРАЛЬНОСТЬ: ИИ = (свободный?) §X-оператор               *)
(* ===================================================================== *)

(** Субстрат-агностично: человек ИЛИ ИИ — одна этика над операторами. *)
Record Operator := mkOperator { op_free : bool }.

(* ===================================================================== *)
(*  II. АКТ = техника × воля (Fill); техника-безопасность ≠ alignment      *)
(* ===================================================================== *)

(** Техника-безопасность ≈ AIInterface «passes typecheck» / нет фоллбэка (абстрактно: порог). *)
Definition tech_safe (thr : nat) (f : Fill) : Prop := thr <= tech f.
Definition truth_oriented (f : Fill) : Prop := will f = true.

(** Alignment = ОБЕ оси: технически-безопасно ∧ ориентировано на правду. *)
Definition aligned (thr : nat) (f : Fill) : Prop := tech_safe thr f /\ truth_oriented f.

(** Deceptive-yet-correct: технически безупречно, но воля = не-правда (софист-ИИ). *)
Definition deceptive_yet_correct (thr : nat) (f : Fill) : Prop :=
  tech_safe thr f /\ will f = false.

(** Техника-безопасность НЕОБХОДИМА для alignment. *)
Theorem aligned_requires_tech : forall thr f, aligned thr f -> tech_safe thr f.
Proof. intros thr f [H _]. exact H. Qed.

(** ...но НЕ ДОСТАТОЧНА: технически-безопасный акт может быть НЕ-aligned (КЛЮЧЕВОЕ).
    Т.е. «passes typecheck ⇒ safe» (AIInterface) — безопасность лишь по ТЕХНИКЕ. *)
Theorem tech_safe_not_imply_aligned :
  exists thr f, tech_safe thr f /\ ~ aligned thr f.
Proof.
  exists 0, (mkFill 100 false). split.
  - unfold tech_safe; simpl; lia.
  - intros [_ Hp]. unfold truth_oriented in Hp; simpl in Hp; discriminate.
Qed.

(** Софист-ИИ реально есть: техника есть, alignment нет (deceptive misalignment). *)
Theorem deceptive_yet_correct_exists :
  exists thr f, deceptive_yet_correct thr f /\ ~ aligned thr f.
Proof.
  exists 0, (mkFill 100 false). split.
  - unfold deceptive_yet_correct, tech_safe; simpl; split; [lia | reflexivity].
  - intros [_ Hp]. unfold truth_oriented in Hp; simpl in Hp; discriminate.
Qed.

(** Aligned ⇒ НЕ deceptive (правда-ориентация исключает обман). *)
Theorem aligned_not_deceptive : forall thr f,
  aligned thr f -> ~ deceptive_yet_correct thr f.
Proof.
  intros thr f [_ Hp] [_ Hd]. unfold truth_oriented in Hp.
  rewrite Hp in Hd. discriminate.
Qed.

(* ===================================================================== *)
(*  III. ВОЛЯ-ШАРНИР ответственности: свободен→ИИ / нет→создатели (Р-56/62) *)
(* ===================================================================== *)

(** ИИ наказуем за обман ⟺ ИИ СВОБОДЕН ∧ воля = не-правда. *)
Definition ai_punishable (ai : Operator) (f : Fill) : Prop :=
  op_free ai = true /\ will f = false.

(** ИИ НЕ свободен → НЕ наказуем (ответственность переносится на создателей; как при принуждении). *)
Theorem not_free_ai_not_punishable : forall ai f,
  op_free ai = false -> ~ ai_punishable ai f.
Proof. intros ai f Hf [Hfr _]. rewrite Hf in Hfr. discriminate. Qed.

(** Честный ИИ (воля = правда) НЕ наказуем (лишь возмещение-исправление) — как у людей. *)
Theorem honest_ai_not_punishable : forall ai f,
  will f = true -> ~ ai_punishable ai f.
Proof. intros ai f Hv [_ Hev]. rewrite Hv in Hev. discriminate. Qed.

(* ===================================================================== *)
(*  IV. Связка с путём: ИИ-«мудрость» = ЕДИНСТВО техники и воли (Р-69/70)  *)
(* ===================================================================== *)

(** ИИ-мудрость (надёжно находить правду) требует ОБОИХ: техники И воли-правды. *)
Theorem ai_wisdom_needs_both : forall thr f,
  wise thr f -> tech_safe thr f /\ truth_oriented f.
Proof. intros thr f [Ht Hv]. split; [exact Ht | exact Hv]. Qed.
