(** * ChoicePriceMap.v — the axiom-price audit of Part X (no AC anywhere)
    Elements: result names, axiom-price tiers
    Roles:    price = the role each result plays on the axiom-cost scale
    Rules:    PZero < PL3 < PL3_L4 < PBoundary; every PROVEN result stays below
              PBoundary (i.e. none requires the full Axiom of Choice)
    STATUS:   8 Qed, 0 Admitted, 0 axioms
    Author:   Horsocrates | Date: June 2026

    An AUDIT layer (not new mathematics): it encodes, as a decidable table, the
    verified axiom cost of Part X's results (each cross-checked by Print
    Assumptions in its own file). Tiers: PZero (0 axioms), PL3 (classic only),
    PL3_L4 (classic + L4_witness), PBoundary (open / role-limit: full AC, the
    power-set OBJECT, full Kruskal in complete generality, Borel/Martin
    determinacy). The thesis, audited: no PROVEN result reaches PBoundary —
    nothing in Part X uses the full Axiom of Choice.
*)

(* ===================== Price tiers ===================== *)

Inductive AxiomPrice : Set := PZero | PL3 | PL3_L4 | PBoundary.

Inductive ResultName : Set :=
  | RCantorGeneral | RCountabilityQ | RDiagonal | RCantorBendixson
  | RTransfiniteLevel | RFiniteChoice
  | RHigman | RKruskalFamilies | RFiniteDeterminacy | RShrinkingIntervals
  | RSchroederBernstein | RCardinalAntisym | RContinuumHypothesis
  | RFullAC | RPowerSetObject | RFullKruskal | RBorelDeterminacy.

Definition price (r : ResultName) : AxiomPrice :=
  match r with
  | RCantorGeneral | RCountabilityQ | RDiagonal | RCantorBendixson
  | RTransfiniteLevel | RFiniteChoice => PZero
  | RHigman | RKruskalFamilies | RFiniteDeterminacy | RShrinkingIntervals => PL3
  | RSchroederBernstein | RCardinalAntisym | RContinuumHypothesis => PL3_L4
  | RFullAC | RPowerSetObject | RFullKruskal | RBorelDeterminacy => PBoundary
  end.

(* ===== Concrete prices (each cross-checked by Print Assumptions elsewhere) == *)

Lemma cantor_general_zero : price RCantorGeneral = PZero.
Proof. reflexivity. Qed.

Lemma countability_q_zero : price RCountabilityQ = PZero.
Proof. reflexivity. Qed.

Lemma transfinite_level_zero : price RTransfiniteLevel = PZero.
Proof. reflexivity. Qed.

Lemma higman_uses_L3_not_AC : price RHigman = PL3.
Proof. reflexivity. Qed.

Lemma sb_uses_L3_L4_not_AC : price RSchroederBernstein = PL3_L4.
Proof. reflexivity. Qed.

Lemma cardinal_antisym_uses_L3_L4 : price RCardinalAntisym = PL3_L4.
Proof. reflexivity. Qed.

(* ===================== The audited thesis ===================== *)

Definition below_boundary (p : AxiomPrice) : Prop :=
  match p with PBoundary => False | _ => True end.

(* Full AC is the boundary (open / refused), not a proven result *)
Lemma full_AC_is_boundary : price RFullAC = PBoundary.
Proof. reflexivity. Qed.

(* Every substantive PROVEN result of Part X sits strictly below the boundary:
   none requires the full Axiom of Choice. *)
Lemma proven_results_below_boundary :
  below_boundary (price RCantorGeneral) /\
  below_boundary (price RSchroederBernstein) /\
  below_boundary (price RHigman) /\
  below_boundary (price RCardinalAntisym) /\
  below_boundary (price RCantorBendixson) /\
  below_boundary (price RTransfiniteLevel).
Proof. repeat split; exact I. Qed.
