(** * ERRActualization.v — остаток: the GENERAL level-transition operator — Products(L) = Elements(L+1)
      as an OPERATION (the paper's formula, previously only per-level instances).

    The E/R/R paper states two formulas: actualization (Process + Constitution = Product) and the
    LEVEL TRANSITION Products(L) = Elements(L+1).  In Core_ERR the latter appears only as per-level
    instances (Nat -> Real -> Enum).  This file makes the level transition a GENERAL operator:

      ★ fs_lift : FunctionalSystem L -> FunctionalSystem (LS L) — the SAME triad, re-situated one
        level up; its elements (the products of level L) become legitimate elements at level LS L,
        because each was graded < L and L << LS L (transitivity).
      ★ lift_elements : get_Elements (fs_lift S) = get_Elements S — Products(L) = Elements(L+1):
        the carrier is preserved across the level jump.
      ★ lift_roles / lift_rules : Roles and Rules preserved;
      ★ lift_elements_valid_up : every product is a valid element at LS L (the transition is sound).

    Honest scope: this is the LEVEL-TRANSITION half of actualization (Products(L) = Elements(L+1),
    generalized).  The DYNAMIC half — Process + Constitution = Product, a sequence completing into an
    object (Cauchy etc.) — is per-arena content (Core_ERR's concrete instances), here abstracted as
    "the system as the carrier of its products."  fs_lift is, in effect, the embed functor for
    FunctionalSystem.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      (1) fs_lift raises a level-L system to level LS L, preserving the triad;
      (2) its elements (= the products of L) become legitimate elements at LS L (grading < L < LS L
          by transitivity);
      (3) the carrier is preserved: Products(L) = Elements(L+1).
    Roles (L4): fs_lift = the transition operator; fs_element_level is carried over; transitivity of
      << = the lift.
    Elements (L1+P4): the systems S; their elements-as-products.
    P4 diagnostic (could it be otherwise?):
      The formula Products(L) = Elements(L+1) is now GENERAL (it was only Nat/Real/Enum instances);
      the carrier is forced to be preserved under the lift.
    Honesty wall:
      this is the level-transition half of actualization; the dynamic half (Process + Constitution =
      Product) is per-arena content, abstracted here.  fs_lift is essentially the embed functor for
      FunctionalSystem.  0 axioms.

    STATUS: 6 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.

Arguments fs_constitution {L}.
Arguments fs_domain {L}.
Arguments fs_relations {L}.
Arguments fs_functional {L}.
Arguments fs_element_level {L}.
Arguments fs_level_valid {L}.

(* ===================================================================== *)
(*  THE LEVEL-TRANSITION OPERATOR                                          *)
(* ===================================================================== *)

(** ★ Lift a system one level up: the same triad, with its elements (the products of level L) now
    valid as elements of level LS L (grading < L < LS L by transitivity). *)
Definition fs_lift {L} (S : FunctionalSystem L) : FunctionalSystem (LS L).
Proof.
  refine {| fs_constitution := fs_constitution S;
            fs_domain := fs_domain S;
            fs_relations := fs_relations S;
            fs_functional := fs_functional S;
            fs_element_level := fs_element_level S;
            fs_level_valid := _ |}.
  intro e.
  apply (level_lt_trans (fs_element_level S e) L (LS L)).
  - exact (fs_level_valid S e).
  - simpl. left. reflexivity.
Defined.

(* ===================================================================== *)
(*  WHAT THE LIFT PRESERVES / SENDS                                        *)
(* ===================================================================== *)

(** ★★ Products(L) = Elements(L+1): the carrier of products at level L is the carrier of elements at
    level LS L — the same Elements, re-situated one level up. *)
Lemma lift_elements : forall {L} (S : FunctionalSystem L),
  get_Elements (fs_lift S) = get_Elements S.
Proof. intros. reflexivity. Qed.

(** ★ Roles preserved across the level transition. *)
Lemma lift_roles : forall {L} (S : FunctionalSystem L),
  get_Roles (fs_lift S) = get_Roles S.
Proof. intros. reflexivity. Qed.

(** ★ Rules preserved across the level transition. *)
Lemma lift_rules : forall {L} (S : FunctionalSystem L),
  fs_constitution (fs_lift S) = fs_constitution S.
Proof. intros. reflexivity. Qed.

(** ★ The grading is carried over unchanged. *)
Lemma lift_grading : forall {L} (S : FunctionalSystem L) (e : get_Elements (fs_lift S)),
  fs_element_level (fs_lift S) e = fs_element_level S e.
Proof. intros. reflexivity. Qed.

(** ★★ The transition is SOUND: every product (element of S) is a legitimate element at level LS L. *)
Lemma lift_elements_valid_up : forall {L} (S : FunctionalSystem L) (e : get_Elements (fs_lift S)),
  fs_element_level (fs_lift S) e << LS L.
Proof. intros L S e. exact (fs_level_valid (fs_lift S) e). Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ THE LEVEL TRANSITION, generalized: fs_lift takes any level-L system to a level-(LS L) system
    preserving the whole triad (Elements/Roles/Rules), with its products becoming valid elements one
    level up.  Products(L) = Elements(L+1) is now an operator, not just per-level instances. *)
Theorem err_actualization : forall {L} (S : FunctionalSystem L),
  get_Elements (fs_lift S) = get_Elements S
  /\ get_Roles (fs_lift S) = get_Roles S
  /\ fs_constitution (fs_lift S) = fs_constitution S
  /\ (forall e : get_Elements (fs_lift S), fs_element_level (fs_lift S) e << LS L).
Proof.
  intros L S.
  split; [ exact (lift_elements S) | ].
  split; [ exact (lift_roles S) | ].
  split; [ exact (lift_rules S) | exact (lift_elements_valid_up S) ].
Qed.

Print Assumptions err_actualization.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  6 Qed, 0 Admitted, 0 axioms.                                             *)
(*  The general level-transition operator fs_lift : FunctionalSystem L ->     *)
(*  FunctionalSystem (LS L), making the paper's Products(L) = Elements(L+1) an *)
(*  OPERATION (was only Nat/Real/Enum instances).  lift_elements (carrier      *)
(*  preserved = Products = Elements one level up), lift_roles/lift_rules       *)
(*  (triad preserved), lift_elements_valid_up (the products are valid elements *)
(*  at LS L).  Capstone err_actualization.  HONEST: the level-transition half  *)
(*  of actualization; the dynamic Process+Constitution=Product half is         *)
(*  per-arena content (abstracted).  fs_lift is essentially the embed functor  *)
(*  for FunctionalSystem.                                                     *)
(* ========================================================================= *)
