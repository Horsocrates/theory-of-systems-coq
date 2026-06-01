(** * RealPointSetoid.v — "Point = class" as a SETOID (F-10), axiom-free

    ================= E/R/R разбор: действительное-как-точка =================
    Система — НЕ «множество ℝ», а ИМЕНОВАНИЕ значений процессами.
    Генеративный порядок Rules -> Roles -> Elements:

      Rules (L5)    : is_Cauchy      — правило допустимости процесса;
                      cauchy_equiv   — КОГДА два процесса именуют ОДНУ точку
                                       (конституция тождества-как-точки);
                      Proper-совместимость — роль «точка» сохраняется под +,*,-.
      Roles (L4)    : «точка / действительное» = позиция «приближаемое
                      значение», занимаемая процессом ДО эквивалентности;
                      «представитель»; «класс» = роль-группировка (НЕ Element).
      Elements      : Коши-процессы (nat -> Q), конечно-актуализуемы (L1+P4);
                      их рациональные значения R n (уровнем ниже).

    Хорошая сформированность: однозначно (процесс = Element, точка = Role,
    эквивалентность = Rule); P1 — уровни не схлопываются (значение < процесс
    < роль-точка), правило связывает Элементы, не роль с собой.

    ДИАГНОСТИКА (что растворяем): реифицировать класс в один терм-ОБЪЕКТ
    (фактортип) = сплавить Role+Rule в мнимый Element => смешение категорий,
    корневая ошибка P4 (процесс/роль приняты за завершённый объект). К тому же
    конструктивно невозможно (нет вычислимой канонформы; равенство реалов
    неразрешимо) и потребовало бы НОВЫХ аксиом. Поэтому «точка = класс»
    формализуется как SETOID: Роль, порождённая Правилом (Equivalence) над
    Элементами (процессами) — без реифицированного объекта, 0 новых аксиом.

    НОСИТЕЛЬ НЕСЁТ ПРАВИЛО: операции суть морфизмы (Proper) на CauchySeq, где
    свойство Коши УПАКОВАНО в носитель, а НЕ на сыром nat->Q (там произведение
    эквивалентность не уважает — нужна ограниченность сомножителей). Значит
    правильный носитель Роли — CauchySeq (процесс + свидетель Коши).
    =========================================================================

    Status: F-10 — setoid-слой (Equivalence + Proper-морфизмы), axiom-free.
            Разблокирует F-5 (метрика на классах) и F-6 (топология на классах).
    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: May 2026
*)

From Stdlib Require Import QArith.
From Stdlib Require Import Setoid Morphisms.
From ToS Require Import process.ProcessCore.
From ToS Require Import CauchyReal.
From ToS Require Import RealField.

(* ===================================================================== *)
(*  Rule registered: the equivalences are genuine equivalence relations  *)
(* ===================================================================== *)

(** CauchyReal line: cauchy_equiv is an Equivalence. *)
#[export] Instance cauchy_equiv_Equivalence : Equivalence cauchy_equiv.
Proof.
  split.
  - intros x. exact (cauchy_equiv_refl x).
  - intros x y H. exact (cauchy_equiv_sym x y H).
  - intros x y z Hxy Hyz. exact (cauchy_equiv_trans x y z Hxy Hyz).
Qed.

(** ProcessCore line: process_equiv is an Equivalence (same relation, F-8). *)
#[export] Instance process_equiv_Equivalence : Equivalence process_equiv.
Proof.
  split.
  - intros x. exact (process_equiv_refl x).
  - intros x y H. exact (process_equiv_sym x y H).
  - intros x y z Hxy Hyz. exact (process_equiv_trans x y z Hxy Hyz).
Qed.

(* ===================================================================== *)
(*  RealPoint: the carrier of the Role "point" — a Cauchy process        *)
(*  regarded UP TO cauchy_equiv. NOT a reified quotient object (P4).      *)
(* ===================================================================== *)

Definition RealPoint := CauchySeq.

(* ===================================================================== *)
(*  Roles preserved: the field operations are morphisms (Proper),        *)
(*  so they descend to RealPoint (i.e. are well-defined on "points").    *)
(* ===================================================================== *)

#[export] Instance cauchy_add_Proper :
  Proper (cauchy_equiv ==> cauchy_equiv ==> cauchy_equiv) cauchy_add.
Proof. intros a a' Ha b b' Hb. apply cauchy_add_compat; assumption. Qed.

#[export] Instance cauchy_mul_Proper :
  Proper (cauchy_equiv ==> cauchy_equiv ==> cauchy_equiv) cauchy_mul.
Proof. intros a a' Ha b b' Hb. apply cauchy_mul_compat; assumption. Qed.

#[export] Instance cauchy_neg_Proper :
  Proper (cauchy_equiv ==> cauchy_equiv) cauchy_neg.
Proof. intros a a' Ha. apply cauchy_neg_compat; assumption. Qed.

(* ===================================================================== *)
(*  Demonstrations: setoid rewriting now works on RealPoint —            *)
(*  "equal points give equal results", i.e. operations are well-defined  *)
(*  on the Role, exactly the infrastructure F-5/F-6 need.                *)
(* ===================================================================== *)

Example realpoint_add_well_defined : forall a b c : RealPoint,
  cauchy_equiv a b ->
  cauchy_equiv (cauchy_add a c) (cauchy_add b c).
Proof. intros a b c H. rewrite H. reflexivity. Qed.

Example realpoint_mul_well_defined : forall a a' b : RealPoint,
  cauchy_equiv a a' ->
  cauchy_equiv (cauchy_mul a b) (cauchy_mul a' b).
Proof. intros a a' b H. rewrite H. reflexivity. Qed.

Print Assumptions cauchy_mul_Proper.
