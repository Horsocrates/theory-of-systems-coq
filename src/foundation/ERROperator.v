(** * ERROperator.v — Task #125: the OPERATOR in the E/R/R core, two kinds — INSIDE a system
      (an endomorphism: the system transforms its own state) and OUTSIDE (an operator inside ANOTHER
      system that, through a coupling, acts on this one — the interaction).

    An operator acts on a system.  ToS distinguishes two kinds by the SOURCE of the action:

      ★ InsideOperator S  := ERRMorphism S S — an ENDO-action: a Roles-preserving map of S's own
        Elements onto themselves.  Inside-operators form a MONOID (identity err_id, associative
        composition err_comp) — the endomorphism monoid of S.  (Conceptual sibling: Core_ERR's
        system_update, an inside change of a StructuredSystem's own state.)

      ★ OutsideOperator S := { S' : FunctionalSystem L & ERRMorphism S' S } — an action on S coming
        from ANOTHER system S' (the interacting one) via a coupling S' -> S.  The operator that lives
        INSIDE S' (an InsideOperator S' = g), pushed through the coupling c : S' -> S, yields the
        outside action err_comp g c : S' -> S (outside_via).  This is exactly "оператор внутри другой
        системы, которая производит взаимодействие".

    The two are related: INSIDE = the SELF-SOURCED special case of OUTSIDE (embed_inside: an endo is
    an outside-operator with source S itself).  Genuine interaction = the source is a DIFFERENT system,
    with possibly a DIFFERENT carrier (outside_source_can_differ: unit-sourced into a bool-target).

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      (1) an operator acts on a system; two kinds by the SOURCE of the action;
      (2) INSIDE = endo S -> S (the system transforms its own state, preserving Roles) — a monoid;
      (3) OUTSIDE = the action comes from another system S' via a coupling S' -> S (an operator inside
          S' pushed through the interaction); INSIDE = the self-sourced special case; genuine
          interaction injects from a different carrier.
    Roles (L4): InsideOperator = ERRMorphism S S (endo); OutsideOperator = source system + morphism
      into S; embed_inside (inside = self-outside); outside_via (g inside S' through coupling c); the
      monoid laws (err_id / err_comp from ERRComposition).
    Elements (L1+P4): the systems S, S'; their Elements; the morphisms.
    P4 diagnostic (could it be otherwise?):
      an inside-operator is FORCED to map S into itself (endo); an outside-operator is NOT — its source
      can be a different system with a different carrier (witness unit /= bool).  So "inside vs outside"
      = "self-sourced vs other-sourced": inside is one source among many (inside ⊂ outside), and a
      genuine interaction has source /= target.
    Honesty wall:
      operators here = E/R/R-morphisms (Roles-preserving Element-maps); inside = endo (monoid), outside
      = a morphism from another system (the interaction).  This is the STRUCTURAL operator of the E/R/R
      triad — distinct from the ANALYTIC operators (ProcessOperator / CompactOperator / transfer
      matrices) that act on the amplitude/process-Hilbert tier; do not conflate.  Built on
      ERRComposition (the morphism category, Кирпич 2).  0 axioms.

    STATUS: 5 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.ERRComposition.   (* ERRMorphism, err_id, err_comp, err_morph_eq, laws *)

(* Restore the section-local implicit {L} on the record projections (see ERRRankAsymmetry.v). *)
Arguments fs_constitution {L}.
Arguments fs_domain {L}.
Arguments fs_relations {L}.
Arguments fs_functional {L}.
Arguments fs_element_level {L}.
Arguments fs_level_valid {L}.

(* ===================================================================== *)
(*  THE TWO KINDS OF OPERATOR                                              *)
(* ===================================================================== *)

(** An INSIDE operator: an endo-action on the system's own Elements, preserving Roles. *)
Definition InsideOperator {L : Level} (S : FunctionalSystem L) : Type := ERRMorphism S S.

(** An OUTSIDE operator on S: a source system S' (the interacting one) and a coupling S' -> S. *)
Definition OutsideOperator {L : Level} (S : FunctionalSystem L) : Type :=
  { S' : FunctionalSystem L & ERRMorphism S' S }.

(** The source system of an outside operator (the system the action comes from). *)
Definition oo_source {L} {S : FunctionalSystem L} (oo : OutsideOperator S) : FunctionalSystem L :=
  projT1 oo.

(** The coupling: how the source acts on S. *)
Definition oo_action {L} {S : FunctionalSystem L} (oo : OutsideOperator S)
  : ERRMorphism (oo_source oo) S := projT2 oo.

(** INSIDE as the SELF-SOURCED special case of OUTSIDE. *)
Definition embed_inside {L} {S : FunctionalSystem L} (op : InsideOperator S) : OutsideOperator S :=
  existT (fun S' : FunctionalSystem L => ERRMorphism S' S) S op.

(** The OUTSIDE operator produced by an operator g INSIDE another system S', through a coupling c:
    "оператор внутри другой системы, которая производит взаимодействие" = err_comp g c. *)
Definition outside_via {L} {S : FunctionalSystem L} (S' : FunctionalSystem L)
  (c : ERRMorphism S' S) (g : InsideOperator S') : OutsideOperator S :=
  existT (fun S'0 : FunctionalSystem L => ERRMorphism S'0 S) S' (err_comp g c).

(* ===================================================================== *)
(*  INSIDE OPERATORS FORM A MONOID                                         *)
(* ===================================================================== *)

(** ★★ The inside-operators of S form a MONOID: identity is a two-sided unit, composition is
    associative (the endomorphism monoid). *)
Lemma inside_operators_monoid : forall {L} (S : FunctionalSystem L) (f g h : InsideOperator S),
  err_morph_eq (err_comp (err_id S) f) f
  /\ err_morph_eq (err_comp f (err_id S)) f
  /\ err_morph_eq (err_comp (err_comp f g) h) (err_comp f (err_comp g h)).
Proof.
  intros L S f g h.
  split; [ apply err_id_left | ].
  split; [ apply err_id_right | apply err_comp_assoc ].
Qed.

(* ===================================================================== *)
(*  INSIDE = SELF-OUTSIDE; OUTSIDE = OPERATOR IN ANOTHER SYSTEM           *)
(* ===================================================================== *)

(** ★ Every inside-operator IS an outside-operator with source S itself (self-interaction). *)
Lemma inside_is_self_outside : forall {L} (S : FunctionalSystem L) (op : InsideOperator S),
  oo_source (embed_inside op) = S.
Proof. intros L S op. reflexivity. Qed.

(** ★ An operator g inside another system S', through a coupling c, is the outside action err_comp g c
    on S — the interaction realized. *)
Lemma outside_via_action : forall {L} (S S' : FunctionalSystem L)
  (c : ERRMorphism S' S) (g : InsideOperator S'),
  oo_action (outside_via S' c g) = err_comp g c.
Proof. intros. reflexivity. Qed.

(* ===================================================================== *)
(*  GENUINE INTERACTION: SOURCE CAN DIFFER FROM TARGET                     *)
(* ===================================================================== *)

(** A unit-carrier system and a bool-carrier system (both trivial), and a coupling unit -> bool. *)
Definition SysU : FunctionalSystem L2.
Proof.
  refine {| fs_constitution := TrivialConstitution; fs_domain := unit;
            fs_relations := (fun _ _ => True); fs_functional := I;
            fs_element_level := fun _ => L1; fs_level_valid := fun _ => _ |}.
  exact L1_lt_L2.
Defined.

Definition SysB : FunctionalSystem L2.
Proof.
  refine {| fs_constitution := TrivialConstitution; fs_domain := bool;
            fs_relations := (fun _ _ => True); fs_functional := I;
            fs_element_level := fun _ => L1; fs_level_valid := fun _ => _ |}.
  exact L1_lt_L2.
Defined.

(** A coupling SysU -> SysB (the unit system acts on the bool system). *)
Definition morUB : ERRMorphism SysU SysB :=
  @mkERRMorphism L2 SysU SysB (fun _ => true) (fun x y _ => I).

(** ★★ GENUINE INTERACTION: an outside-operator whose SOURCE has a different carrier than the TARGET
    (unit /= bool) — the action genuinely comes from elsewhere, not an endo. *)
Lemma outside_source_can_differ :
  exists oo : OutsideOperator SysB, get_Elements (oo_source oo) <> get_Elements SysB.
Proof.
  exists (existT (fun S' : FunctionalSystem L2 => ERRMorphism S' SysB) SysU morUB).
  intro H.
  assert (Hb : exists a b : get_Elements SysB, a <> b) by (exists true, false; discriminate).
  rewrite <- H in Hb. destruct Hb as [a [b Hab]]. destruct a, b. apply Hab. reflexivity.
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ THE OPERATOR, two kinds:
      (inside monoid)  inside-operators (endo S -> S) form a monoid;
      (inside⊂outside) every inside-operator is an outside-operator sourced at S itself;
      (interaction)    an operator inside another system, through a coupling, is an outside action;
      (genuine)        an outside-operator's source can have a different carrier than the target.
    INSIDE = self-sourced (endo), OUTSIDE = other-sourced (interaction); inside is one source among
    many.  Built on the E/R/R morphism category. *)
Theorem err_operator :
  (forall (L : Level) (S : FunctionalSystem L) (f g h : InsideOperator S),
     err_morph_eq (err_comp (err_id S) f) f
     /\ err_morph_eq (err_comp f (err_id S)) f
     /\ err_morph_eq (err_comp (err_comp f g) h) (err_comp f (err_comp g h)))
  /\ (forall (L : Level) (S : FunctionalSystem L) (op : InsideOperator S),
        oo_source (embed_inside op) = S)
  /\ (forall (L : Level) (S S' : FunctionalSystem L) (c : ERRMorphism S' S) (g : InsideOperator S'),
        oo_action (outside_via S' c g) = err_comp g c)
  /\ (exists oo : OutsideOperator SysB, get_Elements (oo_source oo) <> get_Elements SysB).
Proof.
  split; [ intros L S f g h; apply inside_operators_monoid | ].
  split; [ intros L S op; apply inside_is_self_outside | ].
  split; [ intros L S S' c g; apply outside_via_action | exact outside_source_can_differ ].
Qed.

Print Assumptions err_operator.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  5 Qed, 0 Admitted, 0 axioms.                                             *)
(*  Task #125: the OPERATOR in the E/R/R core, two kinds.  InsideOperator S =  *)
(*  ERRMorphism S S (endo, the system transforms its own state) —             *)
(*  inside_operators_monoid (identity + associative = the endomorphism monoid).*)
(*  OutsideOperator S = a source system S' + a coupling S' -> S; oo_source /    *)
(*  oo_action.  embed_inside / inside_is_self_outside (INSIDE = self-sourced    *)
(*  OUTSIDE); outside_via / outside_via_action (an operator g INSIDE another    *)
(*  system, through coupling c, = the outside action err_comp g c — the         *)
(*  interaction).  outside_source_can_differ (genuine interaction: source       *)
(*  carrier unit /= target carrier bool).  Capstone err_operator.  HONEST:      *)
(*  structural operator = E/R/R-morphism (inside = endo, outside = morphism     *)
(*  from another system); distinct from analytic operators (ProcessOperator/    *)
(*  CompactOperator/transfer) on the process-Hilbert tier.  Built on            *)
(*  ERRComposition (Кирпич 2).                                                 *)
(* ========================================================================= *)
