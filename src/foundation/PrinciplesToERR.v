(** * PrinciplesToERR.v — Architecture: principles <-> E/R/R, E/R/R self-well-formedness,
      Distinction typed by E/R/R at its own level  (F-2, F-3, F-4)

    Только СВЯЗУЮЩИЕ теоремы поверх уже доказанного; ЯДРО НЕ ТРОГАЕТСЯ.

    ===== F-3: E/R/R, применённая к себе — само-ПРИМЕНЕНИЕ, не само-ЧЛЕНСТВО =====
    Граница: само-ЧЛЕНСТВО (x e x; level(S) < level(S)) запрещено P1 (Рассел/лжец);
    само-ПРИМЕНЕНИЕ (критерий E/R/R применён к описанию СВОЕЙ триады) — благое, ибо
    СТРАТИФИЦИРОВАНО: схема (мета) организует своё-описание (объект уровнем ниже),
    уровни сохранены. E/R/R само-применима И P1-СОВМЕСТИМА (не исключение, а соблюдение).
    Различитель — no_self_reference: у Рассела ребро i->i (членство) -> ill-formed;
    у E/R/R его нет -> well-formed. err_self_well_formed = позитивное подтверждение:
    само-применение E/R/R благого, уровне-сохраняющего рода.

    ===== F-2: P1-P4 <-> E/R/R — СООТВЕТСТВИЕ, не вывод =====
    E/R/R выводится ПРЯМО из законов (ERRFromDistinction), не через принципы; принципы
    ТОЖЕ из законов. Значит «принципы -> E/R/R» = СООТВЕТСТВИЕ двух параллельных следствий
    законов (P1 <-> no_self_reference; L5-иерархия <-> rules_above_elements), а НЕ строгий
    вывод E/R/R из принципов. Не подделываем энтейлмент, которого нет.

    ===== F-4: Distinction типизируется E/R/R на СВОЁМ уровне (вариант B) =====
    Distinction (генеративный АКТ границы; positive/negative=Roles, exclusive/exhaustive=
    Rules, стороны=Elements) ПЕРВИЧНЕЕ, чем System L (организованный ПРОДУКТ, параметризован
    Level, который derived). Втиснуть Distinction в System L (вариант A) = ИНВЕРСИЯ уровней
    (основание как продукт) — категориальная ошибка семейства P4. Поэтому B: типизируем
    Distinction его РОДНЫМ E/R/R на его уровне (well-formed), НЕ embed как System L.

    STATUS: 7 Qed, 0 Admitted, 0 axioms (Print Assumptions: Closed under the global context)
    Author: Horsocrates | Date: May 2026
*)

From Stdlib Require Import Bool PeanoNat.
From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.Distinction.
From ToS Require Import foundation.PrinciplesFromLaws.
From ToS Require Import foundation.ERRWellFormedness.

(* ===================================================================== *)
(*  F-3: E/R/R as a system passes its OWN well-formedness criterion       *)
(* ===================================================================== *)

(** E/R/R's own triad, as an ERRSystem: three components — the Element-, Role-,
    Rule-category themselves — with the generative order Rule -> Role -> Element
    (strictly downward, NO self-reference). *)
Definition err_meta_system : ERRSystem := mkERRSys 3
  (fun i => match i with
            | 0%nat => Cat_Element
            | 1%nat => Cat_Role
            | _     => Cat_Rule
            end)
  (fun i j => (Nat.eqb i 2 && Nat.eqb j 1) || (Nat.eqb i 1 && Nat.eqb j 0)).

Theorem err_self_well_formed : is_well_formed err_meta_system = true.
Proof. vm_compute. reflexivity. Qed.

(** The crux: E/R/R's self-APPLICATION is well-formed, while self-MEMBERSHIP
    (Russell: a component that IS its own member) is NOT — the criterion is
    precisely the discriminator. *)
Theorem self_application_not_self_membership :
  is_well_formed err_meta_system = true /\ is_well_formed russell_system = false.
Proof. split; [ exact err_self_well_formed | exact russell_ill_formed ]. Qed.

(** E/R/R's own triad really carries all three categories. *)
Theorem err_meta_has_all_three : exists i j k,
  errs_category err_meta_system i = Cat_Element /\
  errs_category err_meta_system j = Cat_Role /\
  errs_category err_meta_system k = Cat_Rule.
Proof. exists 0%nat, 1%nat, 2%nat. vm_compute. auto. Qed.

(* ===================================================================== *)
(*  F-2: principles <-> E/R/R  (correspondence, not derivation)           *)
(* ===================================================================== *)

(** P1 in the LEVEL register (no self-membership) and the SAME constraint in the
    E/R/R register (no_self_reference), both proven; hence E/R/R is well-formed.
    This is the correspondence that closes the architectural picture — NOT a
    derivation of E/R/R from the principles (E/R/R comes straight from the laws). *)
Theorem principles_err_correspondence :
  (forall l : Level, ~ (l << l)) /\
  no_self_reference err_meta_system = true /\
  is_well_formed err_meta_system = true.
Proof.
  split; [| split].
  - exact P1_no_self_membership.
  - vm_compute. reflexivity.
  - exact err_self_well_formed.
Qed.

(* ===================================================================== *)
(*  F-4 (variant B): Distinction typed by E/R/R at its OWN level           *)
(*  (NOT embedded as System L — that would invert levels)                 *)
(* ===================================================================== *)

(** The native E/R/R triad of a Distinction: two actualized sides (Elements),
    positive/negative (Roles), exclusive/exhaustive (Rules), generative order
    Rule -> Role -> Element. Structural — uniform over all Distinctions. *)
Definition distinction_meta_system : ERRSystem := mkERRSys 6
  (fun i => match i with
            | 0%nat | 1%nat => Cat_Element   (* the two sides, actualized *)
            | 2%nat | 3%nat => Cat_Role      (* positive / negative *)
            | _             => Cat_Rule      (* exclusive (L2) / exhaustive (L3) *)
            end)
  (fun i j =>
     ((Nat.eqb i 4 || Nat.eqb i 5) && (Nat.eqb j 2 || Nat.eqb j 3))
     || ((Nat.eqb i 2 || Nat.eqb i 3) && (Nat.eqb j 0 || Nat.eqb j 1))).

Theorem distinction_err_well_formed : is_well_formed distinction_meta_system = true.
Proof. vm_compute. reflexivity. Qed.

(** The typing applies to EVERY distinction (the E/R/R type is structural). *)
Theorem every_distinction_err_well_formed :
  forall _ : Distinction, is_well_formed distinction_meta_system = true.
Proof. intros _. exact distinction_err_well_formed. Qed.

Theorem distinction_has_all_three : exists i j k,
  errs_category distinction_meta_system i = Cat_Element /\
  errs_category distinction_meta_system j = Cat_Role /\
  errs_category distinction_meta_system k = Cat_Rule.
Proof. exists 0%nat, 2%nat, 4%nat. vm_compute. auto. Qed.

Print Assumptions principles_err_correspondence.
Print Assumptions distinction_err_well_formed.
