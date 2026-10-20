(** * ChoicePriceMap.v — the axiom-price audit of Part X: what each result costs
    Elements: result names, axiom-price tiers
    Roles:    price = the role each result plays on the axiom-cost scale
    Rules:    a tier records WHICH axiom declarations a proof depends on (Print
              Assumptions); it is not a strength scale below the Axiom of Choice:
                PZero     — closed under the global context;
                PL3       — classic only;
                PL4       — L4_witness only;
                PL3_L4    — classic + L4_witness;
                PBoundary — not constructed: objects the theory does not build.
              PZero lies below PL3 and PL4; PL3 and PL4 are incomparable; both lie below
              PL3_L4 (price_le).  Every PROVEN result stays below PBoundary.
    STATUS:   17 Qed, 0 Admitted, 0 axioms
    Author:   Horsocrates | Date: June 2026 (tiers corrected October 2026)

    An AUDIT layer — a CLASSIFICATION, not a theorem about the results: the table below
    is a decidable function written by hand, and each entry is cross-checked against
    Print Assumptions in the result's own file.  What this file DOES prove
    (machine-checked, 0 axioms) is how strong the L4 tier is:
      * the statement of L4_witness (ToS_Axioms.v) is exactly the constructive
        indefinite description of the standard library; applied to each index of a
        family it yields FUNCTIONAL CHOICE over an arbitrary family
        (l4_statement_gives_functional_choice);
      * together with classic it yields Hilbert's epsilon
        (l3_l4_statements_give_epsilon);
      * «AC on nat» in the formulation of foundation/P4ProhibitsAC.v is provable with
        no axioms at all (ac_on_nat_free).
    So PL4 and PL3_L4 are NOT «below full AC»: whatever rests on L4_witness rests on a
    principle from which choice over families follows.  The honest content of «without
    the Axiom of Choice» is narrower: the results priced PZero or PL3 use neither
    L4_witness nor any choice schema.

    CORRECTION (2026-10-17), from Print Assumptions on a mirror build (Rocq 9.0.1):
      RShrinkingIntervals  PL3 -> PZero (unit_interval_uncountable_trisect_v2: closed);
      RKruskalFamilies     PL3 -> PZero (kruskal_chains, kruskal_forks, depth1_wqo,
                                         L5_from_kruskal: closed);
      RHigman              PL3, now actually backed: HigmanLemma.v compiles again (its
                           proofs were repaired); Nat.le and one-letter Higman are closed,
                           Dickson's lemma for pairs uses classic;
      RFullAC              (was PBoundary, «refused») replaced by two entries backed in
                           this file: RFunctionalChoice — PL4; RACOnNat — PZero.
    The old thesis «no PROVEN result reaches PBoundary — nothing in Part X uses the full
    Axiom of Choice» is withdrawn in its second half: Schroeder–Bernstein, cardinal
    antisymmetry and the closed-set dichotomy rest on L4_witness.
*)

From Stdlib Require Import List.
Import ListNotations.

(* ===================== Price tiers ===================== *)

Inductive AxiomPrice : Set := PZero | PL3 | PL4 | PL3_L4 | PBoundary.

(** p ≼ q: every axiom declaration under p is also under q. *)
Definition price_le (p q : AxiomPrice) : bool :=
  match p, q with
  | PZero, _ => true
  | PL3, (PL3 | PL3_L4 | PBoundary) => true
  | PL4, (PL4 | PL3_L4 | PBoundary) => true
  | PL3_L4, (PL3_L4 | PBoundary) => true
  | PBoundary, PBoundary => true
  | _, _ => false
  end.

Lemma pl3_pl4_incomparable : price_le PL3 PL4 = false /\ price_le PL4 PL3 = false.
Proof. split; reflexivity. Qed.

Lemma pl3_pl4_below_pl3_l4 : price_le PL3 PL3_L4 = true /\ price_le PL4 PL3_L4 = true.
Proof. split; reflexivity. Qed.

(* ===================== Results and their prices ===================== *)

Inductive ResultName : Set :=
  | RCantorGeneral | RCountabilityQ | RDiagonal | RCantorBendixson
  | RTransfiniteLevel | RFiniteChoice
  | RHigman | RKruskalFamilies | RFiniteDeterminacy | RShrinkingIntervals
  | RSchroederBernstein | RCardinalAntisym | RContinuumHypothesis
  | RFunctionalChoice | RACOnNat
  | RPowerSetObject | RFullKruskal | RBorelDeterminacy.

(** Backing theorems (Print Assumptions in their own files):
    RCantorGeneral      — CantorTheoremGeneral.cantor_no_surjection, no_maximal_bool_power;
                          CardinalityWithoutChoice.no_maximal_cardinality: closed
    RCountabilityQ      — Countability_Q.Q_countable, Q_bijection: closed
    RDiagonal           — ProcessDiagonal.binary_processes_not_enumerable: closed
    RCantorBendixson    — CantorBendixsonFull (derivative facts, e.g. S_finite_scattered,
                          CB_omega_accumulation_in_parent): closed.  The perfect-set
                          DICHOTOMY for closed sets is RContinuumHypothesis, not this entry.
    RTransfiniteLevel   — TransfiniteInductionLevel.no_universal_level: closed
    RShrinkingIntervals — ShrinkingIntervals_ERR.unit_interval_uncountable_trisect_v2: closed
    RKruskalFamilies    — KruskalTree.kruskal_chains, kruskal_forks; KruskalFull.depth1_wqo,
                          L5_from_kruskal: closed
    RACOnNat            — ac_on_nat_free (this file): closed
    RHigman             — HigmanLemma.higman_synthesis: classic (only through dickson_pair)
    RFiniteDeterminacy  — BorelDeterminacy.weak_determinacy (arbitrary win condition W):
                          classic.  NB: this is excluded middle applied to «player I has
                          a winning strategy», not determinacy proper; full `determined`
                          is proved only for trivial games and for K = 0, and
                          FiniteGameDeterminacy.finite_game_determined is just the boolean
                          dichotomy of the backward-induction value (no link to winning
                          strategies is proved)
    RFunctionalChoice   — l4_statement_gives_functional_choice (this file): needs the
                          statement of L4_witness only
    RSchroederBernstein — SchroederBernstein_ERR.Schroeder_Bernstein: classic + L4_witness
    RCardinalAntisym    — CardinalityWithoutChoice.cardinal_antisym: classic + L4_witness
    RContinuumHypothesis— ProcessContinuumHypothesis.process_continuum_hypothesis:
                          classic + L4_witness (L4 applied to a countable family, 70–80)
    PBoundary           — not constructed: the completed power-set object, Kruskal in full
                          generality, Borel / Martin determinacy. *)
Definition price (r : ResultName) : AxiomPrice :=
  match r with
  | RCantorGeneral | RCountabilityQ | RDiagonal | RCantorBendixson
  | RTransfiniteLevel | RFiniteChoice
  | RShrinkingIntervals | RKruskalFamilies | RACOnNat => PZero
  | RHigman | RFiniteDeterminacy => PL3
  | RFunctionalChoice => PL4
  | RSchroederBernstein | RCardinalAntisym | RContinuumHypothesis => PL3_L4
  | RPowerSetObject | RFullKruskal | RBorelDeterminacy => PBoundary
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

Lemma higman_uses_L3_not_AC : price RHigman = PL3.
Proof. reflexivity. Qed.

Lemma sb_uses_L3_L4 : price RSchroederBernstein = PL3_L4.
Proof. reflexivity. Qed.

Lemma cardinal_antisym_uses_L3_L4 : price RCardinalAntisym = PL3_L4.
Proof. reflexivity. Qed.

Lemma functional_choice_costs_L4 : price RFunctionalChoice = PL4.
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

(* ===================== The audited thesis ===================== *)

Definition below_boundary (p : AxiomPrice) : Prop :=
  match p with PBoundary => False | _ => True end.

(** The completed power-set object is the boundary: not constructed. *)
Lemma power_set_object_is_boundary : price RPowerSetObject = PBoundary.
Proof. reflexivity. Qed.

(** Every PROVEN result listed here sits below the boundary.  This says nothing
    about strength relative to choice: see the section above. *)
Lemma proven_results_below_boundary :
  below_boundary (price RCantorGeneral) /\
  below_boundary (price RSchroederBernstein) /\
  below_boundary (price RHigman) /\
  below_boundary (price RCardinalAntisym) /\
  below_boundary (price RCantorBendixson) /\
  below_boundary (price RTransfiniteLevel) /\
  below_boundary (price RShrinkingIntervals) /\
  below_boundary (price RKruskalFamilies) /\
  below_boundary (price RFunctionalChoice) /\
  below_boundary (price RACOnNat).
Proof. repeat split; exact I. Qed.

(* Axiom audit: every lemma of this file is closed under the global context. *)
Print Assumptions l4_statement_gives_functional_choice.
Print Assumptions l3_l4_statements_give_epsilon.
Print Assumptions ac_on_nat_free.
Print Assumptions proven_results_below_boundary.
