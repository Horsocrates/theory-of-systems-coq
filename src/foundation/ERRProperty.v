(** * ERRProperty.v — Task #128 (program capstone): the first-class PROPERTY / OBSERVABLE of a system,
      and the PART -> WHOLE map — with EMERGENCE defined as a whole-property OUTSIDE the image of the
      part->whole map.  Closes the gap "no first-class property/observable + no part->whole map + no
      general emergence taxonomy".

    Author's derivation: what EXISTS has an essence (суть) and is KNOWABLE — so property/observable are
    derivable, as is the part->whole map.  Realized in the core:

      ★ a system EXISTS (a FunctionalSystem) and HAS AN ESSENCE — it satisfies its own constitution
        (system_has_essence : get_Rules S, witnessed by fs_functional — non-trivially);
      ★ a PROPERTY = a predicate on systems (Property L); an OBSERVABLE = a value it yields
        (Observable L V) — both first-class, derived from the triad (rules_observable, carrier_
        observable).  Knowability: the essence-property is CONSTRUCTIVELY known (the witness
        fs_functional) — познаваемость (the Knowledge branch) realized 0-axiom for the essence.

      ★ the PART -> WHOLE map combines the parts' Roles into the whole's Roles (prod_rel, ERRComposition);
        a whole-Roles is PART-REDUCIBLE iff it is in the image of this map (separable, ERREntanglement);
      ★ EMERGENT = a whole-property NOT in the image (non-separable).  Witnesses: every product-Roles is
        reducible (product_is_reducible); the parity (Bell/GHZ) correlation is EMERGENT
        (parity_is_emergent), and parity_system is a SYSTEM carrying a first-class emergent property
        (parity_system_emergent).

    This UNIFIES the three: a property/observable is first-class; the part->whole map is prod_rel; and
    EMERGENCE = whole-property outside that map's image — the general emergence taxonomy, of which
    entanglement (ERREntanglement) is the concrete instance.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      (1) what EXISTS has an ESSENCE (satisfies its own constitution) and is KNOWABLE => a PROPERTY =
          a knowable predicate on systems, an OBSERVABLE = a value it yields (first-class, from the
          triad);
      (2) the PART -> WHOLE map combines the parts' Roles into the whole's (prod_rel);
      (3) a whole-property is REDUCIBLE if in the image (separable), EMERGENT if outside (non-separable).
    Roles (L4): Property (predicate on systems); Observable (value-map); system_has_essence
      (get_Rules / fs_functional); the part->whole map = prod_rel; part_reducible = separable; emergent
      = ~ separable; the parity witnesses.
    Elements (L1+P4): the systems; their constitutions / carriers / Roles; the composite.
    P4 diagnostic (could it be otherwise?):
      property/observable is FORCED by existence (a system satisfies its rules — has an essence,
      non-trivially via fs_functional) and is knowable (a constructive witness of the essence).  The
      part->whole map is prod_rel; whether a whole-property is in its image is a real question
      (reducible vs emergent), decided at the Roles tier — emergence is genuine (parity is outside the
      image).
    Honesty wall:
      Property / Observable here are the CORE structural notions (predicate / value-map on systems);
      the познаваемость bridge to the Knowledge branch is cited (the essence-property is constructively
      known, 0-axiom).  The part->whole map and emergence REUSE ERREntanglement (separable / non-
      separable) — this CLOSES the gap by UNIFYING the three: emergence = whole-property outside the
      part->whole image.  Physics-grade observables (amplitudes) = QObservable, a different tier.
      0 axioms.

    STATUS: 5 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.ERRComposition.   (* prod_rel *)
From ToS Require Import foundation.ERREntanglement.  (* separable, prod_rel_separable, parity_roles, parity_not_separable, parity_system, parity_system_entangled *)

(* Restore the section-local implicit {L} on the record projections (see ERRRankAsymmetry.v). *)
Arguments fs_constitution {L}.
Arguments fs_domain {L}.
Arguments fs_relations {L}.
Arguments fs_functional {L}.
Arguments fs_element_level {L}.
Arguments fs_level_valid {L}.

(* ===================================================================== *)
(*  PROPERTY / OBSERVABLE AS FIRST-CLASS (derived from existence)          *)
(* ===================================================================== *)

(** A PROPERTY of systems: a predicate on systems. *)
Definition Property (L : Level) : Type := FunctionalSystem L -> Prop.

(** An OBSERVABLE of systems: a value it yields. *)
Definition Observable (L : Level) (V : Type) : Type := FunctionalSystem L -> V.

(** ★★ EXISTENCE -> ESSENCE: every system HAS AN ESSENCE — it satisfies its own constitution.  This is
    the constructive witness that makes the essence KNOWABLE (познаваемость, 0-axiom). *)
Lemma system_has_essence : forall {L} (S : FunctionalSystem L), get_Rules S.
Proof. intros L S. exact (fs_functional S). Qed.

(** The constitution is an OBSERVABLE (the essence-as-value); the carrier is an OBSERVABLE (the
    element-set).  Properties/observables are first-class, read off the triad. *)
Definition rules_observable {L} : Observable L Constitution := fun S => fs_constitution S.
Definition carrier_observable {L} : Observable L Type := fun S => get_Elements S.

(* ===================================================================== *)
(*  THE PART -> WHOLE MAP, AND EMERGENCE AS ITS COKERNEL                   *)
(* ===================================================================== *)

(** The PART -> WHOLE map for Roles = prod_rel (ERRComposition): the parts' Roles combine into the
    whole's Roles.  A whole-Roles is PART-REDUCIBLE iff it lies in the image of this map — i.e., it is
    separable (ERREntanglement). *)
Definition part_reducible {D1 D2 : Type} (R : (D1 * D2) -> (D1 * D2) -> Prop) : Prop :=
  separable R.

(** EMERGENT = a whole-property NOT in the image of the part -> whole map (non-separable). *)
Definition emergent {D1 D2 : Type} (R : (D1 * D2) -> (D1 * D2) -> Prop) : Prop :=
  ~ separable R.

(** ★ Every product-Roles is PART-REDUCIBLE: the image of the part -> whole map. *)
Lemma product_is_reducible : forall {D1 D2 : Type} (R1 : D1 -> D1 -> Prop) (R2 : D2 -> D2 -> Prop),
  part_reducible (prod_rel R1 R2).
Proof. intros D1 D2 R1 R2. exact (prod_rel_separable R1 R2). Qed.

(** ★★ The parity (Bell/GHZ) correlation is EMERGENT: a whole-property outside the part -> whole image. *)
Lemma parity_is_emergent : emergent parity_roles.
Proof. exact parity_not_separable. Qed.

(** ★★ A SYSTEM carrying a first-class EMERGENT property: parity_system's Roles are emergent. *)
Lemma parity_system_emergent : emergent (get_Roles parity_system).
Proof. exact parity_system_entangled. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ PROPERTY / OBSERVABLE + PART -> WHOLE + EMERGENCE:
      (essence)     every system has an essence (satisfies its own constitution) — property is derived;
      (image)       every product-Roles is part-reducible (the part -> whole map's image);
      (cokernel)    the parity correlation is emergent (a whole-property outside the image);
      (a system)    parity_system carries a first-class emergent property.
    Emergence = whole-property outside the part -> whole map — the general taxonomy, instantiated by
    entanglement.  Closes the "no first-class property/observable + no part -> whole + no emergence
    taxonomy" gap. *)
Theorem err_property :
  (forall (L : Level) (S : FunctionalSystem L), get_Rules S)
  /\ (forall (D1 D2 : Type) (R1 : D1 -> D1 -> Prop) (R2 : D2 -> D2 -> Prop),
        part_reducible (prod_rel R1 R2))
  /\ emergent parity_roles
  /\ emergent (get_Roles parity_system).
Proof.
  split; [ exact @system_has_essence | ].
  split; [ exact @product_is_reducible | ].
  split; [ exact parity_is_emergent | exact parity_system_emergent ].
Qed.

Print Assumptions err_property.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  5 Qed, 0 Admitted, 0 axioms.                                             *)
(*  Task #128 (program capstone): first-class PROPERTY / OBSERVABLE + the      *)
(*  PART -> WHOLE map + EMERGENCE.  Property L (predicate on systems),         *)
(*  Observable L V (value-map); system_has_essence (existence -> essence: a    *)
(*  system satisfies its own constitution, fs_functional — knowable 0-ax);     *)
(*  rules_observable / carrier_observable (observables off the triad).  Part-> *)
(*  whole map = prod_rel; part_reducible = separable (in the image); emergent  *)
(*  = ~ separable (outside).  product_is_reducible (the image), parity_is_      *)
(*  emergent (a whole-property outside it), parity_system_emergent (a system    *)
(*  with a first-class emergent property).  Capstone err_property.  UNIFIES:    *)
(*  emergence = whole-property outside the part -> whole image — the general    *)
(*  taxonomy, of which entanglement (ERREntanglement) is the instance.  HONEST: *)
(*  core structural property/observable (познаваемость bridge cited);          *)
(*  physics-grade observables = QObservable, a different tier.                 *)
(* ========================================================================= *)
