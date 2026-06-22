(** * EthicsResponsibility.v — Ответственность и свобода (Н-6, СТРУКТУРА)

    Elements: акт-под-ответственностью (свобода, несёт-порядок, вред, намерение-вид);
              эпистемическое поле (known / known-unknown / unknown-unknown).
    Roles:    ответственность = свободный ЗДО несущего-порядок выбора; два вида —
              возмещение (← вред-факт) и наказание (← вина=зло-вид); признание; честное незнание.
    Rules:    P4/§X (свобода = условие); Н-3 демаркация (несёт-порядок); вид⊥магнитуда (Р-53);
              L5 (необратимость факта вреда).
    Status:   формализована СТРУКТУРА ответственности — 3 условия (forced→ноль), классификация
              возмещение/наказание, признание снимает наказание не возмещение, честное-незнание,
              степень-наказания по свободе. НЕ ценностное суждение.
    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026

    Прозаический грунт: Книги/Этика/00 Этика — рабочая запись.md — Р-56 (3 условия), Р-58 (два вида),
      Р-57 (честное незнание), Р-59 (реляционность), Р-62 (степень-по-свободе), Р-72 (признание).
    ЧЕСТНОСТЬ (стена): кодируется СТРУКТУРА ответственности. «Кто-то ДОЛЖЕН нести ответственность» —
      нормативный тезис (проза); здесь — лишь классификации и их свойства. 0 аксиом.
*)

From Stdlib Require Import Arith.
From ToS Require Import ethics.EthicsModality.

(* ===================================================================== *)
(*  I. ТРИ УСЛОВИЯ (Р-56): свобода ∧ несёт-порядок (⇒ затронутый)         *)
(* ===================================================================== *)

(** [order_at_stake] кодирует «порядок на кону» (Н-3 демаркация); по Р-56 (ii⇒iii)
    это влечёт затронутого свидетеля, потому отдельное поле не вводим. *)
Record RAct := mkRAct {
  free          : bool ;   (* (i)  свобода решения *)
  order_at_stake : bool ;  (* (ii) несёт статус правильно/неправильно *)
  harm          : bool ;   (*      причинён ли вред (факт) *)
  ra_vid        : Vid      (*      намерение: true=правда / false=не-правда *)
}.

Definition responsible (a : RAct) : Prop :=
  free a = true /\ order_at_stake a = true.

(** forced → НОЛЬ ответственности (Р-56: со-протяжённа свободе). *)
Theorem forced_not_responsible : forall a, free a = false -> ~ responsible a.
Proof. intros a Hf [Hfr _]. rewrite Hf in Hfr. discriminate. Qed.

(** Порядок не на кону → нет ответственности (демаркация Н-3). *)
Theorem not_at_stake_not_responsible : forall a,
  order_at_stake a = false -> ~ responsible a.
Proof. intros a Hs [_ Hst]. rewrite Hs in Hst. discriminate. Qed.

(* ===================================================================== *)
(*  II. ДВА ВИДА (Р-58): возмещение ← вред-факт ; наказание ← вина(вид)    *)
(* ===================================================================== *)

Definition owes_restitution   (a : RAct) : Prop := responsible a /\ harm a = true.
Definition deserves_punishment (a : RAct) : Prop := responsible a /\ ra_vid a = false.

(** Нет вреда → нет возмещения. *)
Theorem no_harm_no_restitution : forall a, harm a = false -> ~ owes_restitution a.
Proof. intros a Hh [_ Hh']. rewrite Hh in Hh'. discriminate. Qed.

(** ЧЕСТНАЯ ошибка с вредом: возмещение ДА, наказание НЕТ (Р-58). *)
Theorem honest_harm_restitution_no_punishment : forall a,
  responsible a -> harm a = true -> ra_vid a = true ->
  owes_restitution a /\ ~ deserves_punishment a.
Proof.
  intros a Hr Hh Hv. split.
  - split; assumption.
  - intros [_ Hev]. rewrite Hv in Hev. discriminate.
Qed.

(** ЗЛО с вредом: возмещение И наказание (Р-58). *)
Theorem evil_harm_both : forall a,
  responsible a -> harm a = true -> ra_vid a = false ->
  owes_restitution a /\ deserves_punishment a.
Proof. intros a Hr Hh Hv. split; split; assumption. Qed.

(** Честность (вид=правда) ⇒ НИКОГДА не наказуемо (Р-57/58). *)
Theorem honest_never_punished : forall a, ra_vid a = true -> ~ deserves_punishment a.
Proof. intros a Hv [_ Hev]. rewrite Hv in Hev. discriminate. Qed.

(* ===================================================================== *)
(*  III. ПРИЗНАНИЕ (Р-72): снимает НАКАЗАНИЕ за зло, не ВОЗМЕЩЕНИЕ          *)
(* ===================================================================== *)

(** Признание = разворот намерения к правде (вид → true); вред-факт неизменен. *)
Definition after_priznanie (a : RAct) : RAct :=
  mkRAct (free a) (order_at_stake a) (harm a) true.

Theorem priznanie_cancels_punishment : forall a,
  ~ deserves_punishment (after_priznanie a).
Proof. intros a [_ Hev]. simpl in Hev. discriminate. Qed.

Theorem priznanie_keeps_restitution : forall a,
  owes_restitution a -> owes_restitution (after_priznanie a).
Proof.
  intros a [Hr Hh]. unfold owes_restitution. split.
  - unfold responsible in *; simpl. exact Hr.
  - simpl. exact Hh.
Qed.

(* ===================================================================== *)
(*  IV. ЧЕСТНОЕ НЕЗНАНИЕ (Р-57): unknown-unknown ∧ намерение-знать         *)
(*      долг выяснять покрывает лишь known-unknown                         *)
(* ===================================================================== *)

Inductive Epist := Known | KnownUnknown | UnknownUnknown.

Definition duty_applies (e : Epist) : Prop := e = KnownUnknown.
Definition honest_ignorance (intent_to_know : bool) (e : Epist) : Prop :=
  intent_to_know = true /\ e = UnknownUnknown.

(** Честное незнание (unknown-unknown + намерение) — долг НЕ срабатывает. *)
Theorem honest_ignorance_no_duty : forall i e,
  honest_ignorance i e -> ~ duty_applies e.
Proof. intros i e [_ Hu] Hd. unfold duty_applies in Hd. rewrite Hu in Hd. discriminate. Qed.

(* ===================================================================== *)
(*  V. СТЕПЕНЬ НАКАЗАНИЯ по свободе (Р-62): forced→0, свободный→полная      *)
(* ===================================================================== *)

Definition punish_degree (guilt : nat) (a : RAct) : nat :=
  if free a then guilt else 0.

Theorem forced_zero_punish_degree : forall g a, free a = false -> punish_degree g a = 0.
Proof. intros g a Hf. unfold punish_degree. rewrite Hf. reflexivity. Qed.

Theorem free_full_punish_degree : forall g a, free a = true -> punish_degree g a = g.
Proof. intros g a Hf. unfold punish_degree. rewrite Hf. reflexivity. Qed.
