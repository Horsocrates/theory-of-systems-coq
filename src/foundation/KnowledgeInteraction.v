(** * KnowledgeInteraction.v — F-39 branch «Взаимодействие»: the trace (след), the presentation
      boundary, and classical/quantum as two tiers of one hierarchy (STRUCTURAL reading, not QM)

    Formalizes the structural core of the derivation "Взаимодействие" (Книги/Теория Знания/
    Взаимодействие.md).  It develops the d_source hook of KnowledgeInformation.v: data are borne by
    their SOURCE because the presented difference leaves a TRACE (след) in a system — a record
    WITHOUT a witness.  The knowledge ladder EXTENDS DOWNWARD:
        предъявление -> СЛЕД (in a system) -> считывание (by a witness) -> информация -> знание.
    A measuring device knows nothing — it holds a trace; the witness reads the device's trace
    (dinosaurs: no one witnessed them, but their meetings left traces that waited for a witness).

    WHAT IS PROVED (the STRUCTURAL frame — NOT quantum mechanics):
      - the trace is APPEND-ONLY: once presented it is never erased or edited (Rule 2,5),
        irreversibility — the same arrow as L5_Arrow.cannot_unmake_distinction (the named anchor);
      - classical tier = TRACES: a presented distinction is DETERMINATE (true or false; excluded
        middle in full force); quantum tier = POTENTIAL: not-yet-presented = "ещё ни то ни другое"
        (None) — NOT "both at once" (that would break non-contradiction);
      - NON-CONTRADICTION holds at EVERY tier (the status is function-valued: never both);
      - the presentation boundary potential->trace goes ONE way (irreversible);
      - the five laws are UNIVERSAL (determinacy holds at every tier) while interaction rules are
        TIERED (vary) — so determinacy does NOT fix the rules (emergence demystified; limit of
        reductionism).

    HONEST FRAME (the derivation is emphatic): we do NOT derive QM.  We read the classical/quantum
    CONNECTION as tieredness of rules — a structural skeleton (potential/trace tiers + an
    irreversible presentation boundary), with NO amplitudes, NO Born rule, NO Hilbert space.  The
    machine-checked physics pieces — measurement-as-process (physics/MeasurementProcess.v), the
    Born rule (BornRule.v), Bell–Tsirelson (stdlib/BellTsirelson.v), recording-from-P4
    (foundation/RecordingFromP4.v) — are CITED repository anchors, not appropriated here.  "Each
    tier has its own laws" does NOT relativize logic: the five laws are universal as the determinacy
    conditions of ANY tier.

    ============================== E/R/R разбор ==============================
    Elements: systems of any tier; data (presented differences); СЛЕД/trace (data retained by a
              system — a record without a witness); tiers; interaction rules; potential (not-yet-
              presented differences).
    Roles:    interaction = mutual presentation; trace = the objective memory of the interaction
              (the d_source side); interaction rules = the TIERED role of Rules; the five laws =
              the UNIVERSAL frame of determinacy (not tiered); presentation = the boundary between
              the tiers of potential and traces.
    Rules:    (1) presentation is mutual, on the common meeting tier; (2) the presented leaves a
              trace, not erased (strong append-only P4) — irreversibility; (3) interaction rules
              are tiered; only determinacy conditions are universal; (4) below traces is potential,
              determinacy questions to the un-presented are categorially inapplicable; (5) the tier
              boundary is presentation, irreversible by (2).
    P4 diagnostic: we do NOT derive QM — only the structural connection (tieredness; potential/trace
              boundary).  The physics is cited, not appropriated.  Logic is not relativized.

    STATUS: 13 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List PeanoNat Lia.
From ToS Require Import foundation.L5_Arrow.   (* cannot_unmake_distinction — the irreversibility arrow (anchor) *)

(* ===================================================================== *)
(*  PART I — the trace, and classical/quantum as presented/potential       *)
(* ===================================================================== *)

Section ClassicalQuantum.

  Variable D : Type.                              (* distinctions (presentable differences) *)
  (** The world's status of each distinction at each step: None = potential (quantum tier, not yet
      presented), Some b = presented with a definite value (a TRACE, the classical tier). *)
  Variable status : nat -> D -> option bool.

  (** Rule 2 + 5: the trace is APPEND-ONLY — once presented (traced), never un-presented or altered.
      (Strong, append-only reading of finite actuality; cf. foundation/RecordingFromP4.v.) *)
  Hypothesis trace_append_only :
    forall n d b, status n d = Some b -> status (S n) d = Some b.

  Definition presented (n : nat) (d : D) : Prop := exists b, status n d = Some b.  (* classical: traced *)
  Definition potential (n : nat) (d : D) : Prop := status n d = None.              (* quantum: not yet presented *)

  Lemma presented_or_potential : forall n d, presented n d \/ potential n d.
  Proof.
    intros n d. unfold presented, potential. destruct (status n d) as [b|].
    - left. exists b. reflexivity.
    - right. reflexivity.
  Qed.

  (** ★ The trace VALUE is stable: once set, it is never edited (the record is not rewritten). *)
  Theorem trace_value_stable : forall n m d b,
    (n <= m)%nat -> status n d = Some b -> status m d = Some b.
  Proof.
    intros n m d b Hle Hb. induction Hle as [|m Hle IH].
    - exact Hb.
    - apply trace_append_only. exact IH.
  Qed.

  (** ★ Presentation is IRREVERSIBLE: once presented, presented at every later step.  The
      quantum->classical boundary goes ONE way — the same arrow as L5/time/records (Rule 2,5). *)
  Theorem presentation_irreversible : forall n m d,
    (n <= m)%nat -> presented n d -> presented m d.
  Proof. intros n m d Hle [b Hb]. exists b. exact (trace_value_stable n m d b Hle Hb). Qed.

  (** ★ The dinosaur point (§3): a trace, once left, persists to EVERY later step — it AWAITS a
      witness.  The objective rung (trace, witness-free) is read by a witness who may arrive much
      later; the data of a dinosaur and the data of an instrument are one mechanism. *)
  Corollary trace_awaits_witness : forall n d b,
    status n d = Some b -> forall later, (n <= later)%nat -> status later d = Some b.
  Proof. intros n d b Hb later Hle. exact (trace_value_stable n later d b Hle Hb). Qed.

  (** ★ CLASSICAL tier = traces: a presented distinction is DETERMINATE — its value is true or
      false (предъявленное либо есть, либо нет; excluded middle in full force). *)
  Theorem classical_value_determinate : forall n d, presented n d ->
    status n d = Some true \/ status n d = Some false.
  Proof. intros n d [b Hb]. destruct b; [ left | right ]; exact Hb. Qed.

  (** ★ NON-CONTRADICTION holds at EVERY tier (status is function-valued): never both true and
      false.  Superposition does NOT break this — it is not "both at once". *)
  Theorem non_contradiction : forall n d,
    ~ (status n d = Some true /\ status n d = Some false).
  Proof. intros n d [H1 H2]. rewrite H1 in H2. discriminate. Qed.

  (** ★ QUANTUM tier = potential: a not-yet-presented distinction is NEITHER traced-true NOR
      traced-false — "ещё ни то ни другое" (potential before distinction), NOT "both at once".
      The determinacy question is inapplicable to the un-presented; no contradiction arises. *)
  Theorem potential_not_both : forall n d, potential n d ->
    status n d <> Some true /\ status n d <> Some false.
  Proof. intros n d Hp. unfold potential in Hp. split; rewrite Hp; discriminate. Qed.

  (** ★★ The presentation BOUNDARY: a distinction goes potential -> presented (None -> Some) and
      never back.  Classical and quantum are TWO TIERS of one hierarchy (traces / potential), with
      the irreversible presentation boundary between them. *)
  Definition presents (n : nat) (d : D) : Prop := potential n d /\ presented (S n) d.

  Theorem boundary_one_way : forall n d,
    presents n d -> forall m, (S n <= m)%nat -> presented m d.
  Proof. intros n d [_ Hpres] m Hle. exact (presentation_irreversible (S n) m d Hle Hpres). Qed.

End ClassicalQuantum.

(* ===================================================================== *)
(*  PART II — the trace-net is the L5 arrow (bridge to L5_Arrow, the anchor)*)
(* ===================================================================== *)

Section TraceArrow.

  (** P4: at each moment the trace-net is a FINITE set of presented distinctions (ids). *)
  Variable traced : nat -> DistSet'.
  Hypothesis trace_grows : L5_pres traced.   (* append-only: each step's trace <= the next *)

  (** ★ The trace-net only grows: once a distinction is traced, it stays traced — exactly
      L5_Arrow.cannot_unmake_distinction, the project's irreversibility arrow.  The world remembers
      structurally; decoherence is this net spreading. *)
  Theorem trace_net_irreversible : forall K d,
    has_dist' (traced K) d = true -> forall K', (K <= K')%nat -> has_dist' (traced K') d = true.
  Proof. intros K d Hd K' Hle. exact (cannot_unmake_distinction traced K d trace_grows Hd K' Hle). Qed.

End TraceArrow.

(* ===================================================================== *)
(*  PART III — universal frame (five laws) vs tiered rules (§4)             *)
(* ===================================================================== *)

Section UniversalVsTiered.

  Variable Tier : Type.
  Variable rules : Tier -> (nat -> nat -> nat).   (* each tier's interaction rule (a combination op) *)
  Variable determinate : Tier -> Prop.             (* the five-laws determinacy condition at a tier *)

  Hypothesis determinacy_universal : forall t, determinate t.   (* UNIVERSAL: every tier is determinate *)
  Hypothesis emergence : exists t1 t2, rules t1 <> rules t2.    (* TIERED: rules genuinely differ *)

  (** ★ The five laws are UNIVERSAL — tier-invariant: every tier is determinate (the determinacy
      conditions are more fundamental than any physics law). *)
  Theorem laws_universal : forall t, determinate t.
  Proof. exact determinacy_universal. Qed.

  (** ★ Interaction rules are TIERED — they differ across tiers: emergence is not mysticism, just
      a new tier = a new system = new rules. *)
  Theorem rules_tiered : exists t1 t2, rules t1 <> rules t2.
  Proof. exact emergence. Qed.

  (** ★★ Anti-reductionism / emergence demystified: two tiers BOTH satisfy the universal
      determinacy laws yet have DIFFERENT interaction rules — so the universal frame does NOT fix
      the tiered rules.  Reduction explains what a tier stands on, not its rules. *)
  Theorem determinacy_underdetermines_rules :
    exists t1 t2, determinate t1 /\ determinate t2 /\ rules t1 <> rules t2.
  Proof.
    destruct emergence as [t1 [t2 Hne]]. exists t1, t2.
    split; [ apply determinacy_universal | split; [ apply determinacy_universal | exact Hne ] ].
  Qed.

End UniversalVsTiered.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ The structural frame of interaction: the trace is irreversible (the arrow);
    non-contradiction holds at every tier; and the universal determinacy frame does not fix the
    tiered (emergent) rules. *)
Theorem interaction_capstone :
  (* the trace / presentation is irreversible (append-only) — the arrow *)
  (forall (D : Type) (status : nat -> D -> option bool),
     (forall n d b, status n d = Some b -> status (S n) d = Some b) ->
     forall n m d, (n <= m)%nat ->
       (exists b, status n d = Some b) -> (exists b, status m d = Some b))
  /\ (* non-contradiction holds at every tier (function-valued status) *)
  (forall (D : Type) (status : nat -> D -> option bool) n d,
     ~ (status n d = Some true /\ status n d = Some false))
  /\ (* the universal frame does not fix the tiered rules (emergence / anti-reductionism) *)
  (forall (Tier : Type) (rules : Tier -> (nat -> nat -> nat)) (determinate : Tier -> Prop),
     (forall t, determinate t) -> (exists t1 t2, rules t1 <> rules t2) ->
     exists t1 t2, determinate t1 /\ determinate t2 /\ rules t1 <> rules t2).
Proof.
  split; [ | split ].
  - intros D status Hao n m d Hle [b Hb]. exists b.
    induction Hle as [|m Hle IH]; [ exact Hb | apply Hao; exact IH ].
  - intros D status n d [H1 H2]. rewrite H1 in H2. discriminate.
  - intros Tier rules determinate Huniv [t1 [t2 Hne]]. exists t1, t2.
    split; [ apply Huniv | split; [ apply Huniv | exact Hne ] ].
Qed.

Print Assumptions interaction_capstone.
Print Assumptions trace_net_irreversible.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  13 Qed, 0 Admitted, 0 axioms.                                            *)
(*  The structural core of «Взаимодействие»: the trace (след) is append-only  *)
(*  / irreversible (trace_value_stable, presentation_irreversible,           *)
(*  trace_awaits_witness = the dinosaur point; trace_net_irreversible bridges *)
(*  to L5_Arrow.cannot_unmake_distinction).  Classical = traces = determinate *)
(*  (Some true/false); quantum = potential = None = "not yet either"          *)
(*  (potential_not_both), NOT "both at once" (non_contradiction); the         *)
(*  presentation boundary is one-way (boundary_one_way).  The five laws are   *)
(*  universal while interaction rules are tiered, so determinacy does not fix *)
(*  the rules (determinacy_underdetermines_rules — emergence demystified).    *)
(*  STRUCTURAL reading only — NOT a derivation of QM; physics pieces (Born,   *)
(*  Bell–Tsirelson, measurement-as-process, recording-from-P4) are cited.     *)
(*  Develops the d_source hook of KnowledgeInformation.v (data = a trace).    *)
(* ========================================================================= *)
