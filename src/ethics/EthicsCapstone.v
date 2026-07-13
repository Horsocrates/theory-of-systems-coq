(** * EthicsCapstone.v — Сборка ветки Этики: 7 несущих осей (Р-83, СТРУКТУРА)

    Roles:    собрать структурные результаты пяти файлов в семь несущих осей капстоуна Р-83.
    Status:   интегративные леммы (re-export + связки); подтверждение 0 аксиом по всей ветке.
    STATUS: 8 Qed, 0 Admitted, 0 axioms (Print Assumptions: Closed; вся ветка 0 аксиом)
    Author: Horsocrates | Date: June 2026

    Прозаический грунт: Книги/Этика/00 Этика — рабочая запись.md — Р-83 (капстоун ветки, 7 осей).
    ЧЕСТНОСТЬ (стена): формализуемы оси 1,2,3,4,6,7 (структура). Ось 5 «логика ПОКАЗЫВАЕТ, не
      навязывает» = реляционная стойка (демонстрация vs принуждение) — вне текущей решаемой модели,
      остаётся ПРОЗОЙ (Р-35/40). «Этика истинна/обязательна» — не теорема (нормативность в прозе).
*)

From ToS Require Import ethics.EthicsStatus.
From ToS Require Import ethics.EthicsModality.
From ToS Require Import ethics.EthicsEvil.
From ToS Require Import ethics.EthicsResponsibility.
From ToS Require Import ethics.EthicsPathWisdom.

(* ===================================================================== *)
(*  ОСЬ 1 — одно ОСНОВАНИЕ: статус «правильно = соответствие» РЕШАЕМ      *)
(* ===================================================================== *)
Theorem axis1_foundation : forall thr fit, {correct thr fit} + {~ correct thr fit}.
Proof. exact correct_dec. Qed.

(* ===================================================================== *)
(*  ОСЬ 2 — одна ОСЬ: полярность резка, нет нейтрального ТРЕТЬЕГО         *)
(* ===================================================================== *)
Theorem axis2_one_axis_no_third :
  forall (P : Status -> Prop),
    (forall s, P s -> s <> Correct) ->
    (forall s, P s -> s <> Incorrect) ->
    forall s, ~ P s.
Proof. exact no_neutral_third. Qed.

(* ===================================================================== *)
(*  ОСЬ 3 — одна СВОБОДА: намерение(вид)=шарнир добро/зло; неотчуждаема   *)
(* ===================================================================== *)
Theorem axis3_intent_hinge : forall w, is_evil w \/ is_error w.
Proof. exact evil_xor_error. Qed.

Theorem axis3_freedom_inalienable : forall s : PState, exists s', st_will s' = true.
Proof. exact recovery_always_possible. Qed.

(* ===================================================================== *)
(*  ОСЬ 4 — одно ОТНОШЕНИЕ: реляционность (внутреннее = к себе, не наказ.) *)
(* ===================================================================== *)
Theorem axis4_relational : forall a, internal a -> ~ punishable a.
Proof. exact internal_not_punishable. Qed.

(* ===================================================================== *)
(*  ОСЬ 5 — один СПОСОБ: логика ПОКАЗЫВАЕТ, не навязывает — ПРОЗА          *)
(*  (демонстрация vs принуждение = реляционная стойка вне решаемой модели; *)
(*   Р-35/40. Здесь честно НЕ формализуется.)                             *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  ОСЬ 6 — одна ДИСЦИПЛИНА: техника ⊥ воля                               *)
(* ===================================================================== *)
Theorem axis6_discipline_orthogonality :
  exists f1 f2, tech f1 = tech f2 /\ will f1 <> will f2.
Proof. exact tech_does_not_fix_will. Qed.

(* ===================================================================== *)
(*  ОСЬ 7 — один ПУТЬ: мудрость = единство; восстановление всегда         *)
(* ===================================================================== *)
Theorem axis7_wisdom_unity : forall thr f,
  wise thr f -> thr <= tech f /\ will f = true.
Proof. exact wise_needs_both. Qed.

(* ===================================================================== *)
(*  КАПСТОУН-СВЯЗКА: зло определяется НАМЕРЕНИЕМ (не магнитудой) И          *)
(*  наказуемость РЕЛЯЦИОННА (нужен второй затронутый)                      *)
(* ===================================================================== *)
Theorem capstone_spine :
  (forall m, is_error (mkWrong true m)) /\
  (forall a, internal a -> ~ punishable a).
Proof. split; [exact deep_error_not_evil | exact internal_not_punishable]. Qed.

(* Print Assumptions любой теоремы выше = «Closed under the global context»
   (0 аксиом по всем 6 файлам ветки; проверено отдельно). *)
