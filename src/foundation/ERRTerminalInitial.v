(** * ERRTerminalInitial.v — completing the categorical inventory: the TERMINAL object (one-element
      system) and the INITIAL object (empty system) of the category of FunctionalSystems, and the fact
      that they are DISTINCT — so the category has NO zero object (it is Set-like, not Ab-like).

    With product (ERRComposition), coproduct (ERRCoproduct), sub-system (ERRDynamicsInvariant.restrict),
    quotient (ERRQuotient), and iso (ERRIso) already in place, the nullary cases close the inventory:

      ★ fs_terminal — the one-element (unit) system.  Every system has a UNIQUE morphism INTO it
        (fs_to_terminal + fs_terminal_unique): collapse everything to the single element.  This is the
        nullary PRODUCT.
      ★ fs_initial — the empty system.  Every system has a UNIQUE morphism OUT of it (fs_from_initial +
        fs_initial_unique): the vacuous map.  This is the nullary COPRODUCT.
      ★ NO ZERO OBJECT: fs_initial is NOT isomorphic to fs_terminal (0 elements vs 1) — no_zero_object.
        So the category is SET-LIKE (initial ≠ terminal), not Ab-like (where a zero object exists).

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      the category has a TERMINAL object (unique map IN — maximal collapse) and an INITIAL object
      (unique map OUT — the void); they are DISTINCT (1 element vs 0), so there is NO zero object — the
      category is Set-like.
    Roles (L4): fs_terminal / fs_initial; fs_to_terminal / fs_from_initial (the unique morphisms);
      no_zero_object.
    Elements (L1+P4): one actual element (tt) for the terminal; none (Empty_set) for the initial — both
      P4-finite (1 and 0).
    P4 diagnostic (could it be otherwise?):
      the terminal collapses every system to a single actuality; the initial is the void; they are
      genuinely different finite cardinalities (1 ≠ 0), so they cannot be identified — no zero object.
    Honesty wall:
      built in the specific category FunctionalSystem L2 (the level where our systems live; at L1 the
      grading-validity has nothing below L1, so the construction targets L2 as everywhere in this
      thread).  These are DISTINCT from SystemCategory.v's empty_system / unit_system, which live in the
      OTHER (indexed-System) category — here they are objects of the ERRMorphism category.  No zero
      object = Set-like.  Reuses ERRComposition + ERRIso.  0 axioms.

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.ERRComposition.   (* ERRMorphism, mkERRMorphism, err_map, err_morph_eq *)
From ToS Require Import foundation.ERRIso.            (* SystemIso, iso *)

Arguments fs_constitution {L}.
Arguments fs_domain {L}.
Arguments fs_relations {L}.
Arguments fs_functional {L}.
Arguments fs_element_level {L}.
Arguments fs_level_valid {L}.

(* ===================================================================== *)
(*  THE TERMINAL OBJECT — the one-element system                           *)
(* ===================================================================== *)

(** The one-element system: carrier unit, full Roles, equivalence constitution. *)
Definition fs_terminal : FunctionalSystem L2.
Proof.
  refine {| fs_constitution := EquivalenceConstitution; fs_domain := unit;
            fs_relations := (fun _ _ => True); fs_functional := _;
            fs_element_level := fun _ => L1; fs_level_valid := fun _ => L1_lt_L2 |}.
  unfold EquivalenceConstitution. split; [ | split ]; intros; exact I.
Defined.

Lemma fs_terminal_carrier : get_Elements fs_terminal = unit.
Proof. reflexivity. Qed.

(** The unique morphism INTO the terminal: collapse everything to the single element. *)
Definition fs_to_terminal (S : FunctionalSystem L2) : ERRMorphism S fs_terminal :=
  @mkERRMorphism L2 S fs_terminal (fun _ => tt) (fun x y _ => I).

(** ★★ Any two morphisms into the terminal agree (unit has one element). *)
Lemma fs_terminal_unique : forall (S : FunctionalSystem L2) (m1 m2 : ERRMorphism S fs_terminal),
  err_morph_eq m1 m2.
Proof.
  intros S m1 m2 x. destruct (err_map m1 x); destruct (err_map m2 x); reflexivity.
Qed.

(** ★★ TERMINAL: a unique morphism into fs_terminal from every system. *)
Lemma terminal_universal : forall (S : FunctionalSystem L2),
  exists m : ERRMorphism S fs_terminal, forall m', err_morph_eq m' m.
Proof. intro S. exists (fs_to_terminal S). intro m'. apply fs_terminal_unique. Qed.

(* ===================================================================== *)
(*  THE INITIAL OBJECT — the empty system                                  *)
(* ===================================================================== *)

(** The empty system: carrier Empty_set, empty Roles, equivalence constitution (vacuous). *)
Definition fs_initial : FunctionalSystem L2.
Proof.
  refine {| fs_constitution := EquivalenceConstitution; fs_domain := Empty_set;
            fs_relations := (fun _ _ => False); fs_functional := _;
            fs_element_level := fun e => match e with end;
            fs_level_valid := fun e => match e with end |}.
  unfold EquivalenceConstitution. split; [ | split ].
  - intro x. destruct x.
  - intros x y H. destruct x.
  - intros x y z Hxy Hyz. destruct x.
Defined.

Lemma fs_initial_carrier : get_Elements fs_initial = Empty_set.
Proof. reflexivity. Qed.

(** The unique morphism OUT of the initial: the vacuous map. *)
Definition fs_from_initial (S : FunctionalSystem L2) : ERRMorphism fs_initial S :=
  @mkERRMorphism L2 fs_initial S (fun e => match e with end) (fun x y H => match x with end).

(** ★★ Any two morphisms out of the initial agree (no elements). *)
Lemma fs_initial_unique : forall (S : FunctionalSystem L2) (m1 m2 : ERRMorphism fs_initial S),
  err_morph_eq m1 m2.
Proof. intros S m1 m2 x. destruct x. Qed.

(** ★★ INITIAL: a unique morphism out of fs_initial into every system. *)
Lemma initial_universal : forall (S : FunctionalSystem L2),
  exists m : ERRMorphism fs_initial S, forall m', err_morph_eq m' m.
Proof. intro S. exists (fs_from_initial S). intro m'. apply fs_initial_unique. Qed.

(* ===================================================================== *)
(*  NO ZERO OBJECT — initial and terminal are distinct                     *)
(* ===================================================================== *)

(** ★★ The initial is NOT isomorphic to the terminal (an iso would yield an element of the empty
    carrier from the terminal's element).  So the category has NO zero object — it is Set-like. *)
Lemma no_zero_object : ~ SystemIso fs_initial fs_terminal.
Proof. intros [m [m' _]]. destruct (err_map m' tt). Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ TERMINAL & INITIAL objects:
      (terminal)   a unique morphism INTO the one-element system from every system (nullary product);
      (initial)    a unique morphism OUT of the empty system into every system (nullary coproduct);
      (no zero)    initial and terminal are not isomorphic — the category is Set-like, no zero object.
    The category of systems has both a terminal and an initial object, and they are distinct (1 element
    vs 0) — so it is Set-like, completing the (co)product / (sub,quotient) / iso inventory. *)
Theorem err_terminal_initial :
  (forall (S : FunctionalSystem L2),
     exists m : ERRMorphism S fs_terminal, forall m', err_morph_eq m' m)
  /\ (forall (S : FunctionalSystem L2),
     exists m : ERRMorphism fs_initial S, forall m', err_morph_eq m' m)
  /\ ~ SystemIso fs_initial fs_terminal.
Proof.
  split; [ exact terminal_universal | ].
  split; [ exact initial_universal | exact no_zero_object ].
Qed.

Print Assumptions err_terminal_initial.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  8 Qed, 0 Admitted, 0 axioms.                                             *)
(*  Completes the categorical inventory of FunctionalSystems.  fs_terminal     *)
(*  (one-element/unit system) with fs_to_terminal + fs_terminal_unique +       *)
(*  terminal_universal (unique map IN = nullary product).  fs_initial (empty   *)
(*  system) with fs_from_initial + fs_initial_unique + initial_universal       *)
(*  (unique map OUT = nullary coproduct).  no_zero_object (initial is NOT iso   *)
(*  to terminal -- 1 element vs 0 -- so the category is SET-like, no zero       *)
(*  object).  Capstone err_terminal_initial.  HONEST: in the specific category  *)
(*  FunctionalSystem L2; distinct from SystemCategory.v's empty_system/         *)
(*  unit_system (the other, indexed-System category).                          *)
(* ========================================================================= *)
