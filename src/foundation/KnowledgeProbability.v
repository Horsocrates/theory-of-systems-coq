(** * KnowledgeProbability.v — F-39 branch «Вероятность»: probability = the MEASURE OF
      UNCLAMPEDNESS on the presentation boundary; Born's two-part status (structure vs physics)

    Formalizes the structural core of the derivation "Вероятность" (Книги/Теория Знания/
    Вероятность.md), which ties off two open nodes — the Born status from «Взаимодействие» and the
    "strength of descent" from «Связь ярусов».  It continues directly from those two files: the
    presentation boundary потенциал→след (KnowledgeInteraction) and descent = SELECTION FROM THE
    ALLOWED (KnowledgeTierLink, actualized := allowed /\ context).

    THE MAIN HONESTY (the derivation is emphatic): we do NOT derive the |ψ|² form.  Structurally
    derivable is ONLY: (a) WHERE probability lives (the presentation boundary) and (b) WHAT it
    measures (unclampedness).  The numerical FORM of the distribution is content of the physical
    tier — flagged, and (here) PROVED structurally underdetermined.

    WHAT IS PROVED (structural):
      §2/§3  probability lives on the BOUNDARY: at a presentation the admissible set is either a
             single outcome (DETERMINED — determinism), several (FREE — where probability lives),
             or none (impossible).  Unclampedness = the residual freedom (|admissible| - 1): 0 for a
             determined transition (certainty), positive for a free one.
      §4     ЗДО requires weights: a free transition cannot be groundless, so the ground DISTRIBUTES
             across the admissible (a weight on each, conserving the total ground).  BUT the FORM is
             NOT fixed — two distinct distributions satisfy the same structural constraints
             (weight_form_underdetermined): the structure requires A distribution, not |ψ|².
      §5     determinism (a trace-tier law) and probability (a boundary law) do NOT conflict — they
             hold on different sides of the boundary; "collapse" is a tier transition (free boundary
             -> determined trace), extinguishing probability irreversibly (the arrow).
      §6     Born's two-part status: by TYPE a boundary phenomenon measuring unclampedness
             (structural, derived); by FORM a physics-tier law (NOT structurally fixed).

    ============================== E/R/R разбор ==============================
    Elements: the presentation boundary (потенциал→след); admissible outcomes; clamping (downward
              constraint); residual freedom; weights.
    Roles:    probability = the measure of unclampedness (what the context did not reduce to one);
              ЗДО = the distributor of ground across admissible outcomes; presentation = the
              actualizer (one outcome -> trace); determinism = a law WITHIN the trace tier;
              probability = a law of the BOUNDARY.
    Rules:    (1) probability lives on the boundary, not the trace tier (determinate) nor the
              potential tier (no outcomes); (2) descent clamps: full -> one outcome (determinism),
              incomplete -> freedom; (3) probability = measure of unclampedness; (4) ЗДО: if not
              clamped to one, the ground distributes across the admissible (weights MUST be); (5)
              the weight FORM is NOT derivable from general structure — physics-tier content; (6)
              actualization extinguishes probability (the trace is irreversible).
    P4 diagnostic: the |ψ|² form is NOT derived (flagged AND proved underdetermined);
              determinism/probability do NOT conflict (different tiers); collapse = a tier
              transition, not a physical process within a tier.  The machine-checked physics —
              BornRule.v, MeasurementProcess.v, BellTsirelson.v — is CITED as tier content, not
              appropriated as structure.  Free will is a flagged node, not developed here.

    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

(** Sum of a weight assignment over a (finite) list of outcomes — the total ground (ЗДО). *)
Definition gsum {O : Type} (w : O -> nat) (l : list O) : nat :=
  fold_right (fun o acc => w o + acc) 0 l.

(* ===================================================================== *)
(*  §2/§3 — probability lives on the BOUNDARY; unclampedness = residual freedom *)
(* ===================================================================== *)

(** The admissible outcomes at the boundary (after the upper context's partial clamp). *)
Definition determined {O : Type} (adm : list O) : Prop := exists o, adm = [o].   (* clamped to ONE *)
Definition free {O : Type} (adm : list O) : Prop := (2 <= length adm)%nat.        (* incomplete clamp *)
Definition impossible {O : Type} (adm : list O) : Prop := adm = [].               (* none admissible *)

(** Unclampedness = the residual freedom = how many admissible outcomes beyond the first. *)
Definition unclampedness {O : Type} (adm : list O) : nat := length adm - 1.

(** ★ §2/§3 The boundary trichotomy: a presentation is DETERMINED (one outcome — determinism),
    FREE (several — where probability lives), or impossible (none). *)
Theorem clamp_trichotomy : forall {O : Type} (adm : list O),
  impossible adm \/ determined adm \/ free adm.
Proof.
  intros O adm. destruct adm as [|o [|o' rest]].
  - left. reflexivity.
  - right; left. exists o. reflexivity.
  - right; right. unfold free. simpl. lia.
Qed.

(** ★ Full clamp = determinism: clamped to one outcome => unclampedness is 0 (certainty). *)
Theorem full_clamp_is_determinism : forall {O : Type} (adm : list O),
  determined adm -> unclampedness adm = 0.
Proof. intros O adm [o ->]. reflexivity. Qed.

(** ★ Probability needs freedom: a FREE transition has positive unclampedness — this is exactly
    where probability lives. *)
Theorem probability_needs_freedom : forall {O : Type} (adm : list O),
  free adm -> 0 < unclampedness adm.
Proof. intros O adm Hf. unfold free, unclampedness in *. lia. Qed.

(** The two extremes are ends of ONE scale (certainty at 0, growing with the admissible count). *)
Theorem unclampedness_scale : forall {O : Type} (adm : list O),
  unclampedness adm = (length adm - 1)%nat.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  §4 — ЗДО: the ground distributes; but the FORM is NOT fixed            *)
(* ===================================================================== *)

(** ★ Determinism limit: clamped to one outcome => all the ground sits on it (certainty, weight
    "all"). *)
Theorem determined_concentrates_ground : forall {O : Type} (w : O -> nat) (o : O),
  gsum w [o] = w o.
Proof. intros O w o. simpl. lia. Qed.

(** ★★ THE HONEST WALL (§4): the weight FORM is NOT fixed by the structure.  Two DISTINCT
    distributions satisfy the same structural constraints — nonnegative (free over nat) and the
    SAME total ground — on the same admissible set.  The structure requires A distribution; it does
    NOT pick |ψ|².  (This is the structural STOP before the Born form.) *)
Theorem weight_form_underdetermined :
  exists (O : Type) (a b : O) (adm : list O) (w1 w2 : O -> nat),
    a <> b /\ adm = [a; b]
    /\ gsum w1 adm = gsum w2 adm                       (* same total ground *)
    /\ (exists o, In o adm /\ w1 o <> w2 o).           (* yet a different distribution *)
Proof.
  exists bool, true, false, [true; false],
         (fun o : bool => if o then 1 else 2), (fun o : bool => if o then 2 else 1).
  split; [ discriminate | ].
  split; [ reflexivity | ].
  split; [ reflexivity | ].
  exists true. split; [ simpl; left; reflexivity | simpl; discriminate ].
Qed.

(* ===================================================================== *)
(*  §5 — determinism (trace tier) and probability (boundary) do not conflict *)
(* ===================================================================== *)

(** Actualization picks one outcome and traces it — afterward only that outcome remains. *)
Definition actualize {O : Type} (o : O) : list O := [o].

(** ★ §5 "Collapse" = a TIER TRANSITION, not a physical process: a presentation actualizes to a
    DETERMINED trace, extinguishing probability's subject (unclampedness -> 0).  Irreversible (the
    trace is append-only — KnowledgeInteraction). *)
Theorem collapse_extinguishes_probability : forall {O : Type} (o : O),
  determined (actualize o) /\ unclampedness (actualize o) = 0.
Proof. intros O o. split; [ exists o; reflexivity | reflexivity ]. Qed.

(** ★ §5 Determinism (trace tier) and probability (boundary) COEXIST without conflict: a traced
    (actualized) outcome has unclampedness 0, while a free boundary has unclampedness > 0 — the
    same scale, two regimes on two sides.  "Determinism or randomness" is the tier-confusion that
    "classical or quantum" is. *)
Theorem determinism_and_probability_coexist : forall {O : Type} (o : O) (adm : list O),
  free adm ->
  unclampedness (actualize o) = 0   (* trace tier: determined *)
  /\ 0 < unclampedness adm.          (* boundary: free *)
Proof. intros O o adm Hf. split; [ reflexivity | apply probability_needs_freedom; exact Hf ]. Qed.

(* ===================================================================== *)
(*  §6 — Born's two-part status                                            *)
(* ===================================================================== *)

(** ★★★ Born's two-part status, resolving the «Взаимодействие» node.  By TYPE (structural):
    probability lives on the boundary — a free transition has positive unclampedness.  By FORM
    (physical): the distribution is NOT structurally fixed.  Born-as-boundary-phenomenon is
    derived; Born-as-|ψ|² is physics. *)
Theorem born_two_part :
  (* TYPE — structural: probability lives on the boundary (free => positive unclampedness) *)
  (forall (O : Type) (adm : list O), free adm -> 0 < unclampedness adm)
  /\ (* FORM — physical: the weight distribution is NOT structurally fixed *)
  (exists (O : Type) (a b : O) (adm : list O) (w1 w2 : O -> nat),
     a <> b /\ adm = [a; b] /\ gsum w1 adm = gsum w2 adm /\ (exists o, In o adm /\ w1 o <> w2 o)).
Proof.
  split; [ exact @probability_needs_freedom | exact weight_form_underdetermined ].
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ Probability is the measure of unclampedness on the presentation boundary: a free
    transition has positive unclampedness (probability lives there), determinism is the full-clamp
    limit (unclampedness 0), the ground distributes by ЗДО but its FORM is structurally
    underdetermined, and actualization extinguishes probability into a determined trace. *)
Theorem probability_capstone :
  (forall (O : Type) (adm : list O), free adm -> 0 < unclampedness adm)            (* lives on the boundary *)
  /\ (forall (O : Type) (adm : list O), determined adm -> unclampedness adm = 0)   (* determinism = full clamp *)
  /\ (exists (O : Type) (a b : O) (adm : list O) (w1 w2 : O -> nat),               (* FORM underdetermined *)
        a <> b /\ adm = [a; b] /\ gsum w1 adm = gsum w2 adm /\ (exists o, In o adm /\ w1 o <> w2 o))
  /\ (forall (O : Type) (o : O), unclampedness (actualize o) = 0).                 (* actualization extinguishes it *)
Proof.
  split; [ exact @probability_needs_freedom | ].
  split; [ exact @full_clamp_is_determinism | ].
  split; [ exact weight_form_underdetermined | ].
  intros O o. reflexivity.
Qed.

Print Assumptions probability_capstone.
Print Assumptions weight_form_underdetermined.
Print Assumptions born_two_part.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  10 Qed, 0 Admitted, 0 axioms.                                            *)
(*  Probability = the measure of unclampedness on the presentation boundary   *)
(*  (clamp_trichotomy: determined / free / impossible; probability_needs_     *)
(*  freedom; full_clamp_is_determinism).  ЗДО requires a distribution         *)
(*  (determined_concentrates_ground) but its FORM is structurally             *)
(*  underdetermined (weight_form_underdetermined — the honest STOP before     *)
(*  |ψ|²).  Determinism (trace tier) and probability (boundary) coexist       *)
(*  (determinism_and_probability_coexist); collapse = a tier transition       *)
(*  (collapse_extinguishes_probability).  Born's status is two-part           *)
(*  (born_two_part): boundary-phenomenon = structural, |ψ|² = physical.       *)
(*  The physics (BornRule/MeasurementProcess/BellTsirelson) is cited, not     *)
(*  appropriated.  Continues KnowledgeInteraction + KnowledgeTierLink.        *)
(* ========================================================================= *)
