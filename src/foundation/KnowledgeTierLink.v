(** * KnowledgeTierLink.v — F-39 branch «Связь ярусов»: inter-tier relations = the level
      adjunction forget ⊣ embed; ascent carries, descent constrains, both preserve the neighbor

    Formalizes the structural core of the derivation "Связь ярусов" (Книги/Теория Знания/
    Связь ярусов.md), which closes two open nodes (inter-tier rules from «Взаимодействие», the
    co-presence mechanism from «Усмотрение»).  Its stated formal anchor is the level-functor
    adjunction forget ⊣ embed (LevelFunctors.v / LevelAdjunction.v) — a REAL anchor about abstract
    ToS systems that the derivation says to CITE, not appropriate ("ссылаемся не присваивая").
    Here that citation is made formal: the inter-tier claims are bridged to the existing
    LevelFunctors facts (verified 0-axiom).

    THE STRUCTURE:
      §2  the BINDING — tiers of one hierarchy are bound by a FOUNDED grounding relation (no tier
          stands on itself, no cycle, no infinite regress): the meta-pair demand
          (GroundedOrderedStructure / F-38).  The concrete ToS instance is the Level hierarchy
          (level_lt, well-founded — MetaPairStrength.level_lt_wf).
      §3  ASCENT carries — the lower carries the upper (its support / condition of possibility),
          but NOT its rules.  Formally: embed (LevelFunctors), which carries losslessly
          (forget ∘ embed = id, forget_embed_roundtrip — "вложение вполне верно"), preserves the
          elements (embed_obj_elem_eq), and goes strictly up a level (level_lt_LS).
      §4  DESCENT constrains — the upper constrains the lower: SELECTION FROM THE ALLOWED, not
          violation of the lower's laws.  Formally: forget (LevelFunctors) is PARTIAL — not every
          upper system descends (P1_obstructs_total_forget), and which descend is decidable
          (is_forgettable_dec).  An abstract selection model (actualized := allowed /\ context)
          proves downward action is real (it selects) but lawful (never outside the allowed).
      §5  DOUBLE HONESTY — both relations preserve the neighbor's rules.  Against reductionism: the
          upper is genuinely above (descent is partial — the upper has irreducible members).
          Against holism-magic: downward causation is selection within the allowed, never a
          miracle.  Emergence real but not miraculous; downward causation real but not lawless.
      §6  CO-PRESENCE — being an element is being conditioned by the encompassing, and that
          conditioning is a datum present from within (no external channel).  Resolved structurally
          here in prose; the full mechanism is the derivation «Усмотрение».

    ============================== E/R/R разбор ==============================
    Elements: tiers; the grounding relation (the carrying edge); embedding (up); forgetting (down);
              the role of an element; the presentation boundary.
    Roles:    upward conditioning = the "carrier" role (lower = condition of the upper); downward
              constraint = the "context" role (upper selects from the possible lower); role of an
              element = being conditioned by the encompassing; foundedness = the binding of the
              hierarchy (the chain of grounds neither loops nor hangs).
    Rules:    (1) tiers of one hierarchy are bound by a FOUNDED grounding relation; (2) ascent: the
              lower carries the upper but not its rules; (3) descent: the upper constrains the lower
              — selection from the allowed, NOT violation; (4) both relations preserve the neighbor
              tier's rules (neither reductionism nor holism-magic); (5) being an element = being
              conditioned by the encompassing = having data about the whole from within.
    P4 diagnostic: downward causation = selection from the possible, NOT violation of lower laws
              (honestly separated from magical holism).  The level functors (embed/forget
              adjunction) are the real anchor about abstract ToS systems — cited, not appropriated.
              The physical tiers (chemistry, life) are the intended interpretation, not proved here
              as physics.  The hierarchy's "bottom" inherits openness from «Глубина».

    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import Relations.
From ToS Require Import TheoryOfSystems_Core_ERR.            (* Level, System, level_lt (<<), LS *)
From ToS Require Import UniversePolymorphism.                (* level_lt_LS : l << LS l *)
From ToS Require Import LevelFunctors.                       (* embed_obj/forget_obj, forget_embed_roundtrip,
                                                                P1_obstructs_total_forget, is_forgettable_dec *)
From ToS Require Import foundation.GroundedOrderedStructure. (* meta_pair_demands — the founded binding (§2, F-38) *)

(* ===================================================================== *)
(*  §2 — the BINDING: tiers are a FOUNDED grounding order                 *)
(* ===================================================================== *)

(** ★ What makes two tiers tiers of ONE hierarchy (not two separate systems) is a FOUNDED
    grounding relation: nothing grounds itself, no cycle through any mediation, no infinite
    regress of grounds.  This is the meta-pair demand (GroundedOrderedStructure / F-38).  The
    concrete ToS instance is the Level hierarchy (level_lt, well-founded by
    MetaPairStrength.level_lt_wf). *)
Theorem tier_binding_founded :
  forall (T : Type) (grounds : T -> T -> Prop), well_founded grounds ->
    (forall t, ~ grounds t t)
    /\ (forall t, ~ clos_trans T grounds t t)
    /\ (forall f : nat -> T, ~ (forall n, grounds (f (S n)) (f n))).
Proof.
  intros T grounds WF.
  destruct (meta_pair_demands T grounds WF) as [H1 [_ [_ [H4 H5]]]].
  split; [ exact H1 | split; [ exact H4 | exact H5 ] ].
Qed.

(* ===================================================================== *)
(*  §3 — ASCENT carries: embed (lower into upper), losslessly             *)
(* ===================================================================== *)

(** ★ Ascent CARRIES the lower into the upper LOSSLESSLY: descending again recovers it exactly
    (forget ∘ embed = id).  "Вложение вполне верно — ничего не теряет."  (= forget_embed_roundtrip.) *)
Theorem ascent_carries_losslessly : forall (L : Level) (S : System L),
  forget_obj L (embed_obj L S) (embed_is_forgettable L S) = S.
Proof. exact forget_embed_roundtrip. Qed.

(** ★ Ascent goes strictly UP a tier — the upper is genuinely higher (восхождение). *)
Theorem ascent_goes_up : forall (L : Level), L << LS L.
Proof. exact level_lt_LS. Qed.

(* ===================================================================== *)
(*  §4 — DESCENT constrains: forget is PARTIAL (selection), not violation *)
(* ===================================================================== *)

(** ★ Descent is PARTIAL — a selection, not a total reduction: there are upper systems that do
    NOT descend (the P1 obstruction).  The upper tier has IRREDUCIBLE members.
    (= P1_obstructs_total_forget.) *)
Theorem descent_partial : forall (L : Level),
  exists S : System (LS L), ~ is_forgettable L S.
Proof. exact P1_obstructs_total_forget. Qed.

(** ★ Which upper systems descend (the selection) is DECIDABLE. *)
Theorem descent_eligibility_decidable : forall (L : Level) (S : System (LS L)),
  {is_forgettable L S} + {~ is_forgettable L S}.
Proof. exact is_forgettable_dec. Qed.

(** The abstract selection model (§4): the upper context picks the ACTUALIZED out of the lower's
    ALLOWED — downward action is selection from the allowed, never violation of it. *)
Section DownwardSelection.

  Variable State : Type.
  Variable allowed : State -> Prop.   (* the lower tier's rules permit this state *)
  Variable context : State -> Prop.    (* the upper tier's context selects (the role) *)

  Definition actualized (s : State) : Prop := allowed s /\ context s.

  (** ★ Downward action does NOT violate the lower's law: every actualized state is lower-permitted. *)
  Theorem descent_no_violation : forall s, actualized s -> allowed s.
  Proof. intros s [Ha _]. exact Ha. Qed.

  (** Against magic-holism: nothing FORBIDDEN by the lower becomes actual. *)
  Theorem no_magic_holism : forall s, ~ allowed s -> ~ actualized s.
  Proof. intros s Hna [Ha _]. exact (Hna Ha). Qed.

  (** ★ Downward causation is REAL (the upper context genuinely selects) but LAWFUL (within the
      lower's allowance): selection from the allowed, never violation of it. *)
  Theorem downward_real_but_lawful :
    (forall s, actualized s -> context s) /\ (forall s, actualized s -> allowed s).
  Proof. split; [ intros s [_ Hc]; exact Hc | exact descent_no_violation ]. Qed.

End DownwardSelection.

(* ===================================================================== *)
(*  §5 — DOUBLE HONESTY: against reductionism AND against holism-magic    *)
(* ===================================================================== *)

(** ★★★ The two-sided honesty of inter-tier connection.  BINDING: ascent carries losslessly and
    descent recovers it (the adjoint round-trip).  AGAINST REDUCTIONISM: the upper is genuinely
    above — descent is PARTIAL, the upper has irreducible members, so the lower carries but does
    not explain the upper.  AGAINST HOLISM-MAGIC: downward action is selection WITHIN the allowed,
    never a violation.  Emergence real but not miraculous; downward causation real but not lawless. *)
Theorem tier_link_double_honesty :
  (* binding: ascent carries losslessly, descent recovers it (forget ∘ embed = id) *)
  (forall (L : Level) (S : System L),
     forget_obj L (embed_obj L S) (embed_is_forgettable L S) = S)
  /\ (* against reductionism: the upper tier is genuinely above — descent is PARTIAL *)
  (forall (L : Level), exists S : System (LS L), ~ is_forgettable L S)
  /\ (* against holism-magic: downward action is selection WITHIN the allowed, never violation *)
  (forall (State : Type) (allowed context : State -> Prop) (s : State),
     (allowed s /\ context s) -> allowed s).
Proof.
  split; [ exact forget_embed_roundtrip | split ].
  - exact P1_obstructs_total_forget.
  - intros State allowed context s [Ha _]. exact Ha.
Qed.

Print Assumptions tier_link_double_honesty.
Print Assumptions ascent_carries_losslessly.
Print Assumptions descent_partial.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  9 Qed, 0 Admitted, 0 axioms.                                             *)
(*  Inter-tier connection = the level adjunction forget ⊣ embed (cited, not   *)
(*  appropriated).  §2 the binding = a FOUNDED grounding order                *)
(*  (tier_binding_founded, via GroundedOrderedStructure/F-38).  §3 ASCENT     *)
(*  carries losslessly (ascent_carries_losslessly = forget∘embed=id),        *)
(*  preserves elements, goes up a tier.  §4 DESCENT is PARTIAL — selection    *)
(*  from the allowed, not violation (descent_partial = P1 obstruction;        *)
(*  descent_no_violation / no_magic_holism / downward_real_but_lawful).       *)
(*  §5 double honesty: against reductionism (upper irreducible) AND against   *)
(*  holism-magic (downward stays within the allowed).  Closes the inter-tier  *)
(*  node of «Взаимодействие»; the physical tiers are the intended            *)
(*  interpretation, not proved here as physics. *)
(* ========================================================================= *)
