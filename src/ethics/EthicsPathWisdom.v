(** * EthicsPathWisdom.v — Путь и мудрость (Н-9, СТРУКТУРА)

    Elements: заполнение (техника + воля-ориентация); состояние пути (ориентация + глубина).
    Roles:    путь = заполнение структуры правдой/не-правдой по ДВУМ ортогональным осям
              (техника ⊥ воля); мудрость = ЕДИНСТВО обеих вокруг правды; спираль + выход-признание.
    Rules:    Р-65 (две оси, не верх/низ); Р-69 (единство, не две мудрости); Р-70 (находить правду
              правильно); Р-53/62 (спираль, признание-выход всегда); L5 (необратимость истории).
    Status:   формализована СТРУКТУРА — ортогональность техника⊥воля, мудрость=оба-аспекта
              (софист/простак = вне-углы), спираль-углубление + признание-выход, восстановление
              всегда возможно (глубина-история сохраняется). НЕ ценностное суждение.
    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026

    Прозаический грунт: Книги/Этика/00 Этика — рабочая запись.md — Р-65/69/70 (путь/мудрость),
      Р-53/62/68 (спираль, признание, восстановление). Связь: RoleLimitSpecies (regular=сходящийся /
      singular=спираль) — здесь не импортируется (модель спирали самодостаточна).
    ЧЕСТНОСТЬ (стена): кодируется структура заполнения/мудрости/спирали; «мудрость есть благо» —
      не теорема (проза). 0 аксиом.
*)

From Stdlib Require Import Arith Lia.

(* ===================================================================== *)
(*  I. ПУТЬ = ЗАПОЛНЕНИЕ; техника ⊥ воля (Р-65, не верх/низ)              *)
(* ===================================================================== *)

(** Заполнение: tech = качество работы с данными; will = ориентация
    (true = правда / false = не-правда). Механизм один — разнится содержание. *)
Record Fill := mkFill { tech : nat ; will : bool }.

(** ОРТОГОНАЛЬНОСТЬ: любая комбинация (техника, воля) реализуема. *)
Theorem tech_will_independent : forall (t : nat) (v : bool),
  exists f : Fill, tech f = t /\ will f = v.
Proof. intros t v. exists (mkFill t v). split; reflexivity. Qed.

Definition sophist (f : Fill) : Prop := will f = false.            (* техника есть, воля=не-правда *)
Definition simpleton_truthful (f : Fill) : Prop := will f = true.  (* воля=правда, техника любая *)

(** Софист: умело заполняет ИЛЛЮЗИЕЙ (высокая техника + воля не-правда). *)
Theorem sophist_example : exists f, sophist f /\ tech f = 100.
Proof. exists (mkFill 100 false). split; reflexivity. Qed.

(** Техника НЕ определяет волю (⊥). *)
Theorem tech_does_not_fix_will :
  exists f1 f2, tech f1 = tech f2 /\ will f1 <> will f2.
Proof. exists (mkFill 5 true), (mkFill 5 false). split; [reflexivity | discriminate]. Qed.

(* ===================================================================== *)
(*  II. МУДРОСТЬ = ЕДИНСТВО обоих вокруг правды (Р-69/70)                 *)
(* ===================================================================== *)

(** Мудрость = «находить правду правильно» = техника ≥ порога ∧ воля-правда. *)
Definition wise (thr : nat) (f : Fill) : Prop := thr <= tech f /\ will f = true.

(** Софист (воля не-правда) НЕ мудр — сколь угодно умел. *)
Theorem sophist_not_wise : forall thr f, sophist f -> ~ wise thr f.
Proof. intros thr f Hs [_ Hv]. unfold sophist in Hs. rewrite Hs in Hv. discriminate. Qed.

(** Простак (техника ниже порога) НЕ (полно-)мудр — сколь угодно правдив. *)
Theorem low_tech_not_wise : forall thr f, tech f < thr -> ~ wise thr f.
Proof. intros thr f Hlt [Hge _]. lia. Qed.

(** Мудрость требует ОБОИХ — ни один аспект в отдельности не достаточен. *)
Theorem wise_needs_both : forall thr f,
  wise thr f -> thr <= tech f /\ will f = true.
Proof. intros thr f H. exact H. Qed.

(** «Находить правду правильно» ⟺ мудрость (единство, не две мудрости). *)
Definition finds_truth (thr : nat) (f : Fill) : Prop := thr <= tech f /\ will f = true.
Theorem wise_iff_finds_truth : forall thr f, wise thr f <-> finds_truth thr f.
Proof. intros thr f. unfold wise, finds_truth. split; intro H; exact H. Qed.

(* ===================================================================== *)
(*  III. СПИРАЛЬ + ВЫХОД-ПРИЗНАНИЕ; восстановление всегда (Р-53/62/68)     *)
(* ===================================================================== *)

(** Состояние пути: ориентация (st_will) + глубина искажения (depth). *)
Record PState := mkPState { st_will : bool ; depth : nat }.

(** Шаг без признания: не-правда УГЛУБЛЯЕТСЯ (depth+1); правда стабильна. *)
Definition step (s : PState) : PState :=
  if st_will s then s else mkPState false (S (depth s)).

(** Признание: разворот к правде (волю → true); глубина-история сохраняется. *)
Definition acknowledgment (s : PState) : PState := mkPState true (depth s).

(** Признание ВЫХОДИТ из спирали (воля → правда). *)
Theorem acknowledgment_exits : forall s, st_will (acknowledgment s) = true.
Proof. intro s. reflexivity. Qed.

(** Без признания не-правда углубляется (спираль = расходящийся процесс). *)
Theorem spiral_deepens : forall s, st_will s = false -> depth (step s) = S (depth s).
Proof. intros s H. unfold step. rewrite H. reflexivity. Qed.

(** Правда-ориентация стабильна (в спираль не входит). *)
Theorem truth_stable : forall s, st_will s = true -> step s = s.
Proof. intros s H. unfold step. rewrite H. reflexivity. Qed.

(** ВОССТАНОВЛЕНИЕ всегда возможно: из ЛЮБОГО состояния есть выход к правде. *)
Theorem recovery_always_possible : forall s : PState, exists s', st_will s' = true.
Proof. intro s. exists (acknowledgment s). apply acknowledgment_exits. Qed.

(** История (глубина) НЕ стирается признанием (L5: необратимость; «шрам»). *)
Theorem acknowledgment_keeps_depth : forall s, depth (acknowledgment s) = depth s.
Proof. intro s. reflexivity. Qed.
