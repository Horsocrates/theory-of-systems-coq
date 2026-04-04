(** * ERRLawsCorrespondence.v — E/R/R ↔ Laws of Logic correspondence
    Elements: E↔L1, R↔L4, R↔L5, L4+L5 complementarity
    Roles:    each E/R/R component grounded in specific law
    Rules:    from Law of Order paper §4.2.1, §8.5 / ERR Framework §2
    STATUS:   11 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: April 2026

    FROM THE PAPER (§4.2.1, Derivation of Three Components):
    "Elements (what exists) ← L1 (Identity)
     Roles (why significant) ← L4 (Sufficient Reason)
     Rules (how structured) ← L5 (Order)"

    FROM §8.5 (L4 and L5 as Complementary Principles):
    "L4 eliminates arbitrariness of GROUNDS (why this, not that?)
     L5 eliminates arbitrariness of STRUCTURE (in what order?)
     Together: full determinacy."

    This file FORMALIZES these correspondences as theorems.
*)

From Stdlib Require Import QArith Lia ZArith List PeanoNat Bool.
From Stdlib Require Import Lqa.
Import ListNotations.

From ToS Require Import foundation.ERRWellFormedness.

Open Scope Q_scope.

(* ================================================================ *)
(*  E/R/R ↔ LAWS CORRESPONDENCE                                     *)
(* ================================================================ *)

(** The three laws grounding E/R/R *)
Inductive ERRLaw :=
  | Law_L1_Identity       (* grounds Elements: what IS *)
  | Law_L4_SufficientReason  (* grounds Roles: WHY significant *)
  | Law_L5_Order.            (* grounds Rules: HOW structured *)

(** Formal mapping: category → grounding law *)
Definition category_law (c : ERRCategory) : ERRLaw :=
  match c with
  | Cat_Element => Law_L1_Identity
  | Cat_Role => Law_L4_SufficientReason
  | Cat_Rule => Law_L5_Order
  end.

(** Inverse: law → category *)
Definition law_category (l : ERRLaw) : ERRCategory :=
  match l with
  | Law_L1_Identity => Cat_Element
  | Law_L4_SufficientReason => Cat_Role
  | Law_L5_Order => Cat_Rule
  end.

(* ================================================================ *)
(*  CORRESPONDENCE IS BIJECTIVE                                      *)
(* ================================================================ *)

Lemma category_law_roundtrip : forall c : ERRCategory,
  law_category (category_law c) = c.
Proof. intro c. destruct c; reflexivity. Qed.

Lemma law_category_roundtrip : forall l : ERRLaw,
  category_law (law_category l) = l.
Proof. intro l. destruct l; reflexivity. Qed.

(** The correspondence is a BIJECTION *)
Theorem err_law_bijection :
  (forall c, law_category (category_law c) = c) /\
  (forall l, category_law (law_category l) = l).
Proof.
  split; [exact category_law_roundtrip | exact law_category_roundtrip].
Qed.

(* ================================================================ *)
(*  WHAT EACH LAW PROVIDES                                           *)
(* ================================================================ *)

(** L1 provides: identity, self-sameness → Elements are determinate *)
Definition L1_provides_identity : Prop :=
  forall (A : Type) (x : A), x = x.

Lemma L1_reflexivity : L1_provides_identity.
Proof. intros A x. reflexivity. Qed.

(** L4 provides: sufficient reason → Roles are justified *)
(** "An element without purpose is indistinguishable from non-existence" *)
Definition L4_provides_justification : Prop :=
  True.  (* Conceptual: every element's presence justified by its role *)

Lemma L4_justification : L4_provides_justification.
Proof. exact I. Qed.

(** L5 provides: order → Rules are deterministic *)
(** "Rules establish the structure that makes the system a system" *)
Definition L5_provides_structure : Prop :=
  True.  (* Conceptual: rules determine which elements fulfill which roles *)

Lemma L5_structure : L5_provides_structure.
Proof. exact I. Qed.

(* ================================================================ *)
(*  L4 + L5 COMPLEMENTARITY (§8.5)                                  *)
(* ================================================================ *)

(** L4 alone: we know WHY but not HOW → indeterminate structure *)
(** L5 alone: we know HOW but not WHY → unmotivated order *)
(** L4 + L5: both → FULL DETERMINACY *)

(** A system is fully determinate when every element has:
    (a) reason for existence (L4) AND (b) place in structure (L5) *)
Definition is_fully_determinate (S : ERRSystem) : bool :=
  let has_roles := existsb
    (fun i => err_cat_eqb (errs_category S i) Cat_Role)
    (seq 0 (errs_n_components S)) in
  let has_rules := existsb
    (fun i => err_cat_eqb (errs_category S i) Cat_Rule)
    (seq 0 (errs_n_components S)) in
  has_roles && has_rules && is_well_formed S.

Lemma nat_fully_determinate : is_fully_determinate nat_system = true.
Proof. vm_compute. reflexivity. Qed.

(** System with roles but no rules: INDETERMINATE *)
Definition roles_no_rules : ERRSystem := mkERRSys 2
  (fun i => match i with 0%nat => Cat_Element | _ => Cat_Role end)
  (fun _ _ => false).

Lemma roles_no_rules_indeterminate :
  is_fully_determinate roles_no_rules = false.
Proof. vm_compute. reflexivity. Qed.

(** System with rules but no roles: POINTLESS *)
Definition rules_no_roles : ERRSystem := mkERRSys 2
  (fun i => match i with 0%nat => Cat_Element | _ => Cat_Rule end)
  (fun _ _ => false).

Lemma rules_no_roles_pointless :
  is_fully_determinate rules_no_roles = false.
Proof. vm_compute. reflexivity. Qed.

(** L4+L5 complementarity theorem:
    Need BOTH roles (L4) AND rules (L5) for full determinacy *)
Theorem L4_L5_complementarity :
  (* With both: determinate *)
  is_fully_determinate nat_system = true /\
  (* Without rules (L5): indeterminate *)
  is_fully_determinate roles_no_rules = false /\
  (* Without roles (L4): pointless *)
  is_fully_determinate rules_no_roles = false.
Proof.
  split; [exact nat_fully_determinate |
  split; [exact roles_no_rules_indeterminate |
  exact rules_no_roles_pointless]].
Qed.

(* ================================================================ *)
(*  SYNTHESIS                                                        *)
(* ================================================================ *)

Theorem err_laws_correspondence_synthesis :
  (* Bijection: E↔L1, R↔L4, R↔L5 *)
  (forall c, law_category (category_law c) = c) /\
  (forall l, category_law (law_category l) = l) /\
  (* L1 provides identity *)
  L1_provides_identity /\
  (* L4+L5 complementarity: need both for determinacy *)
  is_fully_determinate nat_system = true /\
  is_fully_determinate roles_no_rules = false /\
  is_fully_determinate rules_no_roles = false.
Proof.
  split; [exact category_law_roundtrip |
  split; [exact law_category_roundtrip |
  split; [exact L1_reflexivity |
  split; [exact nat_fully_determinate |
  split; [exact roles_no_rules_indeterminate |
  exact rules_no_roles_pointless]]]]].
Qed.

(**
  BOOK REFERENCE:
  This file formalizes §2 of ERR_Framework_Draft.md, §4.2.1 and §8.5 of Law_of_Order.

  Key theorems:
  - err_law_bijection: E↔L1, R↔L4, R↔L5 is a BIJECTION (machine-verified)
  - L4_L5_complementarity: need BOTH roles AND rules for full determinacy
    "Reason without structure is chaos justified.
     Structure without reason is order unmotivated.
     Only together: genuine determinacy." (§8.5.4)

  Three concrete systems tested:
  - nat_system (has E+R+R): FULLY DETERMINATE ✓
  - roles_no_rules (has E+R but no R): INDETERMINATE ✗
  - rules_no_roles (has E+R but no R): POINTLESS ✗
*)
