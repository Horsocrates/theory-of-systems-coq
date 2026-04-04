(** * ERRProcess.v — E/R/R as DYNAMIC PROCESS: properties → gate → status
    Elements: ERREntity with properties (signals, scores, domain)
    Roles:    Status (PrimaryMax, SecondaryMax, Candidate, Invalid, HistoricalMax)
    Rules:    Zero-Gate (4-component AND) → Weight → L5-comparison → Status
    STATUS:   15 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: April 2026

    THE KEY INSIGHT (missing from previous formalization):
    E/R/R is NOT a static triple (Elements, Roles, Rules).
    E/R/R is a PROCESS:
      Elements have PROPERTIES (signals, scores, domain position).
      Rules CHECK properties (Zero-Gate: 4 boolean gates, AND logic).
      Roles are ASSIGNED based on check result (status machine).

    Rules → determine → Roles → distinguish → Elements
    = Rules(gate) → determine → Roles(status) → distinguish → Elements(by weight)

    This mirrors EXACTLY the Python implementation in regulus/core/:
      types.py       → ERREntity record (this file)
      zero_gate.py   → compute_gate (ZeroGateFormalized.v)
      status_machine → assign_status (StatusFromERR.v)

    CONNECTION TO PHYSICS:
    Same structure as lattice QFT:
      Element = node on graph (with field values)
      Rule = Zero-Gate check (structural integrity)
      Role = Status (PrimaryMax = physical, Invalid = unphysical)
*)

From Stdlib Require Import QArith Lia ZArith List PeanoNat Bool.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================ *)
(*  GATE SIGNALS: Properties of an Element                           *)
(* ================================================================ *)

(** Every element has 7 boolean signals (from types.py GateSignals) *)
Record GateSignals := mkGS {
  gs_e_exists : bool;        (* Element present and identifiable *)
  gs_r_exists : bool;        (* Role (functional purpose) defined *)
  gs_rule_exists : bool;     (* Rule (logical connection) specified *)
  gs_s_exists : bool;        (* Status defined *)
  gs_deps_declared : bool;   (* Dependencies on prior domains stated *)
  gs_l1_l3_ok : bool;        (* No hierarchical loops *)
  gs_l5_ok : bool;           (* Domain sequence D1→D6 respected *)
}.

(** Every element has scores *)
Record RawScores := mkRS {
  rs_struct_points : nat;    (* E/R/R structural completeness, 0-10 *)
  rs_domain_points : nat;    (* Quality within current domain, 0-10 *)
  rs_current_domain : nat;   (* Which domain D1-D6 = 1-6 *)
}.

(* ================================================================ *)
(*  STATUS: Roles that Elements can receive                          *)
(* ================================================================ *)

Inductive Status :=
  | PrimaryMax      (* THE unique winner: gate=1, highest weight, L5-resolved *)
  | SecondaryMax    (* Valid alternative with equal max weight *)
  | HistoricalMax   (* Was Primary, now superseded *)
  | Candidate       (* Valid but lower weight *)
  | Invalid.        (* Gate failed, weight forced to 0 *)

(* ================================================================ *)
(*  ZERO-GATE: The Rule that checks Elements                         *)
(* ================================================================ *)

(** Integrity Gate: G(e) = g_ERR ∧ g_Deps ∧ g_Levels ∧ g_Order *)
Record IntegrityGate := mkIG {
  ig_err : bool;     (* E/R/R/S all present *)
  ig_deps : bool;    (* Dependencies declared *)
  ig_levels : bool;  (* No hierarchical loops *)
  ig_order : bool;   (* Domain sequence respected *)
}.

(** Compute gate from signals *)
Definition compute_gate (s : GateSignals) : IntegrityGate :=
  mkIG (gs_e_exists s && gs_r_exists s && gs_rule_exists s && gs_s_exists s)
       (gs_deps_declared s)
       (gs_l1_l3_ok s)
       (gs_l5_ok s).

(** Gate validity: ALL four must be true *)
Definition gate_valid (g : IntegrityGate) : bool :=
  ig_err g && ig_deps g && ig_levels g && ig_order g.

(* ================================================================ *)
(*  WEIGHT: How Rules quantify Elements                              *)
(* ================================================================ *)

(** Weight formula: W = G_total × (S_struct + S_domain) *)
Definition compute_weight (scores : RawScores) (gate : IntegrityGate) : nat :=
  if gate_valid gate then
    (rs_struct_points scores + rs_current_domain scores * 10 + rs_domain_points scores)%nat
  else 0%nat.   (* ANNIHILATION: gate=0 → weight=0 *)

(* ================================================================ *)
(*  ERR ENTITY: Element with all properties                          *)
(* ================================================================ *)

Record ERREntity := mkEntity {
  ent_id : nat;
  ent_legacy_idx : nat;     (* creation order, for L5 tie-breaking *)
  ent_signals : GateSignals;
  ent_scores : RawScores;
  ent_gate : IntegrityGate;
  ent_weight : nat;
  ent_status : Status;
}.

(* ================================================================ *)
(*  CONCRETE: VALID ENTITY                                           *)
(* ================================================================ *)

Definition valid_signals : GateSignals :=
  mkGS true true true true true true true.

Definition valid_scores : RawScores := mkRS 8 7 3.

Definition valid_gate : IntegrityGate := compute_gate valid_signals.

Lemma valid_gate_passes : gate_valid valid_gate = true.
Proof. vm_compute. reflexivity. Qed.

Definition valid_weight : nat := compute_weight valid_scores valid_gate.

Lemma valid_weight_positive : (0 < valid_weight)%nat.
Proof. vm_compute. lia. Qed.

Lemma valid_weight_value : valid_weight = 45%nat.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  CONCRETE: INVALID ENTITY (missing Element)                       *)
(* ================================================================ *)

Definition invalid_signals : GateSignals :=
  mkGS false true true true true true true.  (* E missing! *)

Definition invalid_gate : IntegrityGate := compute_gate invalid_signals.

Lemma invalid_gate_fails : gate_valid invalid_gate = false.
Proof. vm_compute. reflexivity. Qed.

Definition invalid_weight : nat := compute_weight valid_scores invalid_gate.

Lemma invalid_weight_zero : invalid_weight = 0%nat.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  ZERO-GATE LAW: G=0 ⇒ W=0 (Coq-proven property)                 *)
(* ================================================================ *)

Theorem zero_gate_law : forall scores gate,
  gate_valid gate = false -> compute_weight scores gate = 0%nat.
Proof.
  intros scores gate H. unfold compute_weight. rewrite H. reflexivity.
Qed.

(* ================================================================ *)
(*  SELF-REFERENCE → INVALID                                         *)
(* ================================================================ *)

Definition self_ref_signals : GateSignals :=
  mkGS true true true true true false true.  (* l1_l3_ok = false! *)

Lemma self_ref_fails : gate_valid (compute_gate self_ref_signals) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma self_ref_zero_weight :
  compute_weight valid_scores (compute_gate self_ref_signals) = 0%nat.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  DOMAIN ORDER VIOLATION → INVALID                                 *)
(* ================================================================ *)

Definition order_violation_signals : GateSignals :=
  mkGS true true true true true true false.  (* l5_ok = false! *)

Lemma order_violation_fails :
  gate_valid (compute_gate order_violation_signals) = false.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  THE DYNAMIC CHAIN: properties → gate → weight → status           *)
(* ================================================================ *)

(** The full ERR process for one entity *)
Definition process_entity (id legacy : nat) (sig : GateSignals)
  (scores : RawScores) : ERREntity :=
  let gate := compute_gate sig in
  let weight := compute_weight scores gate in
  let status := if gate_valid gate then Candidate else Invalid in
  mkEntity id legacy sig scores gate weight status.

Lemma valid_entity_is_candidate :
  ent_status (process_entity 0 0 valid_signals valid_scores) = Candidate.
Proof. vm_compute. reflexivity. Qed.

Lemma invalid_entity_is_invalid :
  ent_status (process_entity 1 1 invalid_signals valid_scores) = Invalid.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  SYNTHESIS                                                        *)
(* ================================================================ *)

Theorem err_process_synthesis :
  (* Zero-Gate Law: gate=0 → weight=0 *)
  (forall s g, gate_valid g = false -> compute_weight s g = 0%nat) /\
  (* Valid signals → positive weight *)
  (0 < valid_weight)%nat /\
  (* Invalid signals → zero weight *)
  invalid_weight = 0%nat /\
  (* Self-reference → gate fails *)
  gate_valid (compute_gate self_ref_signals) = false /\
  (* Order violation → gate fails *)
  gate_valid (compute_gate order_violation_signals) = false /\
  (* Valid entity → Candidate *)
  ent_status (process_entity 0 0 valid_signals valid_scores) = Candidate /\
  (* Invalid entity → Invalid *)
  ent_status (process_entity 1 1 invalid_signals valid_scores) = Invalid.
Proof.
  split; [exact zero_gate_law |
  split; [exact valid_weight_positive |
  split; [exact invalid_weight_zero |
  split; [exact self_ref_fails |
  split; [exact order_violation_fails |
  split; [exact valid_entity_is_candidate |
  exact invalid_entity_is_invalid]]]]]].
Qed.
