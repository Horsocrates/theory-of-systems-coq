(** * ChoicePriceMap.v — the axiom-price audit of Part X: what each result costs
    Elements: result names, axiom-price tiers
    Roles:    price = the role each result plays on the axiom-cost scale
    Rules:    a tier records WHICH axiom declarations a proof depends on (Print
              Assumptions); it is not a strength scale below the Axiom of Choice:
                PZero     — closed under the global context;
                PL3       — classic only;
                PL4       — L4_witness only;
                PL3_L4    — classic + L4_witness;
                PHorizon  — not built: a result the formalization does not have yet;
                PBoundary — forbidden: the completed actual-infinite OBJECT, which the
                            theory does not build and P4 excludes.
              PZero lies below PL3 and PL4; PL3 and PL4 are incomparable; both lie below
              PL3_L4 (price_le).  Every PROVEN result stays below PHorizon and PBoundary.
    STATUS:   20 Qed, 0 Admitted, 0 axioms
    Author:   Horsocrates | Date: June 2026 (tiers corrected October 2026; registry
              brought to the compiler November 2026)

    An AUDIT layer — a CLASSIFICATION, not a theorem about the results: the table below
    is a decidable function written by hand, and each entry is cross-checked against
    Print Assumptions in the result's own file.  A lemma about [price] is a lemma about
    this TABLE.  What this file DOES prove (machine-checked, 0 axioms) is how strong
    the L4 tier is:
      * the statement of L4_witness (ToS_Axioms.v) is exactly the constructive
        indefinite description of the standard library; applied to each index of a
        family it yields FUNCTIONAL CHOICE over an arbitrary family
        (l4_statement_gives_functional_choice);
      * together with classic it yields Hilbert's epsilon
        (l3_l4_statements_give_epsilon);
      * «AC on nat» in the formulation of foundation/P4ProhibitsAC.v is provable with
        no axioms at all (ac_on_nat_free).
    So PL4 and PL3_L4 are NOT «below full AC»: whatever rests on L4_witness rests on a
    principle from which choice over families follows.

    WHERE CHOICE ACTUALLY ENTERS (Nov 2026).  L4_witness is used in two ways: for a
    UNIQUE witness (the statement fixes it — no choice) and for ONE witness AMONG MANY
    (a choice).  Schroeder–Bernstein and cardinal antisymmetry need only the first:
    Schroeder_Bernstein_definite derives them from excluded middle and extraction of the
    unique witness taken as PREMISES and is closed (row RSchroederBernsteinDefinite,
    PZero); the rows RSchroederBernstein / RCardinalAntisym price the same theorems
    written on the two axioms.  The second way is what the rows RSurjectionBridge,
    RIntervalAnyCauchy (PL4) and RContinuumHypothesis, RZermeloDeterminacy (PL3_L4) pay.

    CORRECTION (2026-10-17), from Print Assumptions on a mirror build (Rocq 9.0.1):
      RShrinkingIntervals  PL3 -> PZero;  RKruskalFamilies  PL3 -> PZero;
      RFullAC (was PBoundary, «refused») replaced by entries backed in this file.
    CORRECTION (2026-11-13), after the audit of Part X against the compiler:
      RHigman              PL3 -> PZero (Dickson's lemma for pairs is now constructive;
                           higman_synthesis is closed);
      RFiniteDeterminacy   split into RGameTreeDeterminacy (PZero), RWeakDeterminacy
                           (PL3) and RZermeloDeterminacy (PL3_L4);
      RFunctionalChoice    removed: its backing lemma takes L4 as a premise and is
                           closed; the PL4 tier is now backed by theorems proved FROM
                           the axiom (RSurjectionBridge, RIntervalAnyCauchy);
      new rows             RSchroederBernsteinDefinite, RIntervalGivenRate,
                           ROrdinalInduction, RP4Reinterpretations, RPi11Codes (PZero);
      PBoundary            split: PBoundary (forbidden object) and PHorizon (not built);
                           new rows RCompletedChoiceGraph, RHigmanGeneralAlphabet;
      proven_results_below_boundary used to be a conjunction of ten [True]; it now says
                           which rows of the table are NOT below the boundary.
*)

From Stdlib Require Import List.
Import ListNotations.

(* ===================== Price tiers ===================== *)

Inductive AxiomPrice : Set := PZero | PL3 | PL4 | PL3_L4 | PHorizon | PBoundary.

(** p ≼ q: every axiom declaration under p is also under q (for the proven tiers;
    PHorizon and PBoundary sit above them and are not comparable to each other). *)
Definition price_le (p q : AxiomPrice) : bool :=
  match p, q with
  | PZero, _ => true
  | PL3, (PL3 | PL3_L4 | PHorizon | PBoundary) => true
  | PL4, (PL4 | PL3_L4 | PHorizon | PBoundary) => true
  | PL3_L4, (PL3_L4 | PHorizon | PBoundary) => true
  | PHorizon, PHorizon => true
  | PBoundary, PBoundary => true
  | _, _ => false
  end.

Lemma pl3_pl4_incomparable : price_le PL3 PL4 = false /\ price_le PL4 PL3 = false.
Proof. split; reflexivity. Qed.

Lemma pl3_pl4_below_pl3_l4 : price_le PL3 PL3_L4 = true /\ price_le PL4 PL3_L4 = true.
Proof. split; reflexivity. Qed.

(* ===================== Results and their prices ===================== *)

Inductive ResultName : Set :=
  (* closed under the global context *)
  | RCountabilityQ | RDiagonal | RCantorGeneral
  | RShrinkingIntervals | RIntervalGivenRate
  | RSchroederBernsteinDefinite
  | RCantorBendixson | RKruskalFamilies | RHigman
  | RGameTreeDeterminacy
  | ROrdinalInduction | RTransfiniteLevel
  | RFiniteChoice | RACOnNat | RP4Reinterpretations | RPi11Codes
  (* classic *)
  | RWeakDeterminacy
  (* L4_witness *)
  | RSurjectionBridge | RIntervalAnyCauchy
  (* classic + L4_witness *)
  | RSchroederBernstein | RCardinalAntisym | RContinuumHypothesis | RZermeloDeterminacy
  (* not built *)
  | RFullKruskal | RBorelDeterminacy | RHigmanGeneralAlphabet
  (* forbidden object *)
  | RPowerSetObject | RCompletedChoiceGraph.

(** Backing theorems (Print Assumptions in their own files):
    RCountabilityQ      — Countability_Q.Q_countable, Q_bijection: closed
    RDiagonal           — ProcessDiagonal.binary_processes_not_enumerable: closed
    RCantorGeneral      — CantorTheoremGeneral.cantor_no_surjection;
                          CardinalityWithoutChoice.no_maximal_cardinality: closed
    RShrinkingIntervals — ShrinkingIntervals_ERR.unit_interval_uncountable_trisect_v2
                          (regular enumerations): closed
    RIntervalGivenRate  — UnitIntervalUncountableGeneral.unit_interval_uncountable_modulated
                          (any GIVEN rate of convergence): closed
    RSchroederBernsteinDefinite
                        — SchroederBernstein_ERR.Schroeder_Bernstein_definite,
                          CardinalityWithoutChoice.cardinal_antisym_definite (excluded
                          middle and extraction of the unique witness as premises): closed
    RCantorBendixson    — CantorBendixsonFull.perfect_kernel_in_omega,
                          stable_stage_is_perfect_kernel, finite_set_scattered: closed.
                          The perfect-set DICHOTOMY for closed sets is
                          RContinuumHypothesis, not this entry.
    RKruskalFamilies    — KruskalTree.kruskal_chains, kruskal_forks;
                          KruskalFull.depth1_wqo, depth_le1_wqo: closed
    RHigman             — HigmanLemma.higman_unit (one-letter alphabet), dickson_pair,
                          higman_synthesis: closed
    RGameTreeDeterminacy— FiniteGameDeterminacy.finite_game_strategically_determined
                          (every position of a finite tree is won by exactly one side;
                          backward induction computes which): closed
    ROrdinalInduction   — OrdinalOrders.wf_ord_below, structural_transfinite_ind,
                          ord_rec_eq, wf_olt: closed
    RTransfiniteLevel   — TransfiniteInductionLevel.no_universal_level,
                          level_strong_induction: closed
    RFiniteChoice       — P4_Eliminates_AC.finite_choice, AC_is_L5;
                          P4ProhibitsAC.finite_choice_works: closed
    RACOnNat            — ac_on_nat_free (this file): closed
    RP4Reinterpretations— P4ProhibitsAC.P4_cuts_completed_keeps_rule;
                          P4_Eliminates_ATR.P4_eliminates_ATR0;
                          P4_Eliminates_Infinity.P4_eliminates_Infinity;
                          P4ProhibitsImpredicative.russell_requires_completed_totality:
                          closed
    RPi11Codes          — P4_Eliminates_Pi11.P4_eliminates_Pi11 (for ANY table of codes;
                          a section variable, not a Parameter): closed
    RWeakDeterminacy    — BorelDeterminacy.weak_determinacy: classic.  This is excluded
                          middle applied to «player I has a winning strategy», not
                          determinacy proper.
    RSurjectionBridge   — CardinalityWithoutChoice.surjects_injects_back,
                          surjection_has_section: L4_witness (one witness among many in
                          every fibre)
    RIntervalAnyCauchy  — UnitIntervalUncountableGeneral.unit_interval_uncountable_general
                          (arbitrary Cauchy enumerations, an arbitrary rate extracted):
                          L4_witness.  With excluded middle the LEAST rate is a unique
                          witness: unit_interval_uncountable_general_definite is closed.
    RSchroederBernstein — SchroederBernstein_ERR.Schroeder_Bernstein: classic + L4_witness
    RCardinalAntisym    — CardinalityWithoutChoice.cardinal_antisym: classic + L4_witness
    RContinuumHypothesis— ProcessContinuumHypothesis.process_continuum_hypothesis:
                          classic + L4_witness (L4 applied to a countable family)
    RZermeloDeterminacy — ZermeloDeterminacy.zermelo_determinacy (K rounds, moves in nat,
                          arbitrary winning condition): classic + L4_witness
    PHorizon            — not built: Kruskal in full generality, Borel / Martin
                          determinacy, Higman's lemma for an alphabet of two or more
                          letters.
    PBoundary           — forbidden: the completed power-set object; the choice function
                          read as a completed graph (P4ProhibitsAC.
                          completed_graph_contradicts_P4, under the bridge). *)
Definition price (r : ResultName) : AxiomPrice :=
  match r with
  | RCountabilityQ | RDiagonal | RCantorGeneral
  | RShrinkingIntervals | RIntervalGivenRate
  | RSchroederBernsteinDefinite
  | RCantorBendixson | RKruskalFamilies | RHigman
  | RGameTreeDeterminacy
  | ROrdinalInduction | RTransfiniteLevel
  | RFiniteChoice | RACOnNat | RP4Reinterpretations | RPi11Codes => PZero
  | RWeakDeterminacy => PL3
  | RSurjectionBridge | RIntervalAnyCauchy => PL4
  | RSchroederBernstein | RCardinalAntisym | RContinuumHypothesis
  | RZermeloDeterminacy => PL3_L4
  | RFullKruskal | RBorelDeterminacy | RHigmanGeneralAlphabet => PHorizon
  | RPowerSetObject | RCompletedChoiceGraph => PBoundary
  end.

(* ===== Concrete prices (each cross-checked by Print Assumptions elsewhere) == *)

Lemma cantor_general_zero : price RCantorGeneral = PZero.
Proof. reflexivity. Qed.

Lemma countability_q_zero : price RCountabilityQ = PZero.
Proof. reflexivity. Qed.

Lemma transfinite_level_zero : price RTransfiniteLevel = PZero.
Proof. reflexivity. Qed.

Lemma shrinking_intervals_zero : price RShrinkingIntervals = PZero.
Proof. reflexivity. Qed.

Lemma kruskal_families_zero : price RKruskalFamilies = PZero.
Proof. reflexivity. Qed.

Lemma higman_costs_nothing : price RHigman = PZero.
Proof. reflexivity. Qed.

Lemma sb_definite_costs_nothing : price RSchroederBernsteinDefinite = PZero.
Proof. reflexivity. Qed.

Lemma sb_uses_L3_L4 : price RSchroederBernstein = PL3_L4.
Proof. reflexivity. Qed.

Lemma cardinal_antisym_uses_L3_L4 : price RCardinalAntisym = PL3_L4.
Proof. reflexivity. Qed.

Lemma surjection_bridge_costs_L4 : price RSurjectionBridge = PL4.
Proof. reflexivity. Qed.

Lemma ac_on_nat_costs_nothing : price RACOnNat = PZero.
Proof. reflexivity. Qed.

(* ===================== How strong the L4 tier is (0 axioms) ===================== *)

(** The statement of L4_witness (ToS_Axioms.v:105), taken as a hypothesis.  It is
    letter for letter the standard library's constructive indefinite description. *)
Definition L4_statement : Type :=
  forall (A : Type) (P : A -> Prop), (exists x, P x) -> {x : A | P x}.

(** The statement of classic, taken as a hypothesis. *)
Definition L3_statement : Prop := forall P : Prop, P \/ ~ P.

(** Witness extraction applied to every index of a family is a choice function. *)
Lemma l4_statement_gives_functional_choice :
  L4_statement ->
  forall (I X : Type) (R : I -> X -> Prop),
    (forall i, exists x, R i x) -> exists f : I -> X, forall i, R i (f i).
Proof.
  intros L4 I X R H.
  exists (fun i => proj1_sig (L4 X (R i) (H i))).
  intro i. exact (proj2_sig (L4 X (R i) (H i))).
Qed.

(** With classic, witness extraction yields Hilbert's epsilon. *)
Lemma l3_l4_statements_give_epsilon :
  L3_statement -> L4_statement ->
  forall (A : Type) (P : A -> Prop), inhabited A -> {x : A | (exists y, P y) -> P x}.
Proof.
  intros L3 L4 A P Hinh.
  assert (Hb : exists b : bool, if b then (exists y, P y) else ~ (exists y, P y)).
  { destruct (L3 (exists y, P y)) as [Hy | Hn].
    - exists true. exact Hy.
    - exists false. exact Hn. }
  destruct (L4 bool _ Hb) as [[|] Hsel].
  - destruct (L4 A P Hsel) as [x Hx]. exists x. intros _. exact Hx.
  - assert (Ha : exists a : A, True) by (destruct Hinh as [a]; exists a; exact I).
    destruct (L4 A (fun _ => True) Ha) as [a _]. exists a. intro Hex. contradiction.
Qed.

(* Replicated from foundation/P4ProhibitsAC.v:28–31 (no import: the audit stays
   stdlib-only). *)
Definition AC_on_nat : Prop :=
  forall (F : nat -> list nat),
    (forall n, F n <> nil) ->
    exists f : nat -> nat, forall n, In (f n) (F n).

(** «Full AC on nat» in that formulation needs nothing: take the head of each list. *)
Lemma ac_on_nat_free : AC_on_nat.
Proof.
  intros F HF. exists (fun n => hd 0 (F n)).
  intro n. destruct (F n) as [| x xs] eqn:E.
  - exfalso. exact (HF n E).
  - simpl. left. reflexivity.
Qed.

(* ===================== What the table says about its own top ===================== *)

(** Below the boundary: a tier under which something is PROVEN. *)
Definition below_boundary (p : AxiomPrice) : Prop :=
  match p with PHorizon | PBoundary => False | _ => True end.

(** The forbidden rows are exactly two: the completed power-set object and the choice
    function read as a completed graph. *)
Lemma boundary_rows_exactly : forall r,
  price r = PBoundary <-> r = RPowerSetObject \/ r = RCompletedChoiceGraph.
Proof.
  intro r. split.
  - destruct r; simpl; intro H; try discriminate H; [left | right]; reflexivity.
  - intros [H | H]; subst r; reflexivity.
Qed.

(** The rows not built yet are exactly three. *)
Lemma horizon_rows_exactly : forall r,
  price r = PHorizon <->
  r = RFullKruskal \/ r = RBorelDeterminacy \/ r = RHigmanGeneralAlphabet.
Proof.
  intro r. split.
  - destruct r; simpl; intro H; try discriminate H;
      [left | right; left | right; right]; reflexivity.
  - intros [H | [H | H]]; subst r; reflexivity.
Qed.

(** The completed power-set object is the boundary. *)
Lemma power_set_object_is_boundary : price RPowerSetObject = PBoundary.
Proof. reflexivity. Qed.

(** Every row of the table other than those five sits below the boundary.  This is a
    property of the TABLE; it says nothing about strength relative to choice — see the
    section above. *)
Lemma proven_results_below_boundary : forall r,
  below_boundary (price r) <->
  ~ In r [RFullKruskal; RBorelDeterminacy; RHigmanGeneralAlphabet;
          RPowerSetObject; RCompletedChoiceGraph].
Proof.
  intro r. split.
  - intros Hb Hin. simpl in Hin.
    destruct Hin as [H | [H | [H | [H | [H | []]]]]]; subst r; exact Hb.
  - intro Hn. destruct r; simpl; try exact I; exfalso; apply Hn; simpl; tauto.
Qed.

(* Axiom audit: every lemma of this file is closed under the global context. *)
Print Assumptions l4_statement_gives_functional_choice.
Print Assumptions l3_l4_statements_give_epsilon.
Print Assumptions ac_on_nat_free.
Print Assumptions boundary_rows_exactly.
Print Assumptions horizon_rows_exactly.
Print Assumptions proven_results_below_boundary.
