(** * DistinctionCoDefinition.v — What the Distinction record yields BY DERIVATION

    E/R/R reading (done before coding; audit of Part I of the Mathematics
    volume, 2026-11-13):

    Elements: a completed act [D : Distinction] with its two sides
              [positive D], [negative D]; a pending act
              [PendingDistinction] (sides fixed, no assignment yet);
              a bare pair of propositions [(p, n)].
    Roles:    [exclusive] and [exhaustive] — the two rules GIVEN as fields
              of the record; co-definition [n <-> ~ p] — the single rule
              from which non-overlap, grounding and "no third" FOLLOW.
    Rules:    (1) for every D each side is exactly the negation of the
                  other (uses BOTH fields); the two sides are distinct;
              (2) the two fields are independent: neither follows from the
                  other, and with either one alone co-definition fails;
              (3) from co-definition alone, L2, L4 and L3-as-binarity are
                  theorems with no axiom;
              (4) L3-as-totality for co-defined sides is EXACTLY excluded
                  middle — an equivalence in both directions, no axiom;
              (5) a distinction with a given positive side exists iff that
                  proposition is decided;
              (6) for a pair of sides there are three cases and no fourth:
                  the distinction IS; it IS NOT — exactly when the sides
                  are not co-defined, and then there is no potential for
                  it either; there is a POTENTIAL — sides co-defined, no
                  side assigned — and a potential cannot be absent. A
                  "partial" distinction is contradictory (author's word,
                  2026-11-13: a limit of logic itself, not of the theory).
    P4 diagnostic ("could it be otherwise?"): nothing infinite is used.
              Forced: (1)-(6). NOT forced: the assignment of a side — that,
              and only that, is the content of `classic`.

    Given / derived (the ledger behind the prose of Part I):
      given by the record              : exclusive (L2 for the sides),
                                         exhaustive (L3 for the sides);
      given by the calculus            : L1 as [x = x];
      derived from the two fields      : L4, co-determination and
                                         distinctness of the sides;
      derived from co-definition alone : L2, L4, binarity;
      equivalent to excluded middle    : totality for every co-definition;
                                         "every proposition is a side of
                                         some distinction".

    STATUS: 40 Qed, 0 Admitted
    AXIOMS: none — except Section 6 (four statements), which rests on
            Classical_Prop.classic and says so.
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import ClassicalFacts.
From ToS Require Import foundation.Distinction.
From ToS Require Import foundation.BinarityVsTotality.

(* ========================================================================= *)
(*  1. CO-DETERMINATION OF THE SIDES — for every Distinction, no axiom       *)
(* ========================================================================= *)

(** The negative side of ANY distinction is exactly the negation of the
    positive one. Left-to-right uses [exclusive], right-to-left uses
    [exhaustive]: both rules of the record are needed. *)
Theorem negative_iff_not_positive : forall D : Distinction,
  negative D <-> ~ positive D.
Proof.
  intro D. split.
  - intros n p. exact (exclusive D (conj p n)).
  - intro np. destruct (exhaustive D) as [p | n].
    + exfalso. exact (np p).
    + exact n.
Qed.

(** Symmetrically: the positive side is exactly the negation of the
    negative one. *)
Theorem positive_iff_not_negative : forall D : Distinction,
  positive D <-> ~ negative D.
Proof.
  intro D. split.
  - intros p n. exact (exclusive D (conj p n)).
  - intro nn. destruct (exhaustive D) as [p | n].
    + exact p.
    + exfalso. exact (nn n).
Qed.

(** Co-definition, both directions at once. *)
Theorem sides_codetermined : forall D : Distinction,
  (negative D <-> ~ positive D) /\ (positive D <-> ~ negative D).
Proof.
  intro D. split.
  - exact (negative_iff_not_positive D).
  - exact (positive_iff_not_negative D).
Qed.

(** One side fixes the other: distinctions with equivalent positive sides
    have equivalent negative sides. *)
Theorem negative_determined_by_positive : forall D1 D2 : Distinction,
  (positive D1 <-> positive D2) -> (negative D1 <-> negative D2).
Proof.
  intros D1 D2 H. split.
  - intro n1. apply (proj2 (negative_iff_not_positive D2)). intro p2.
    exact (proj1 (negative_iff_not_positive D1) n1 (proj2 H p2)).
  - intro n2. apply (proj2 (negative_iff_not_positive D1)). intro p1.
    exact (proj1 (negative_iff_not_positive D2) n2 (proj1 H p1)).
Qed.

Theorem positive_determined_by_negative : forall D1 D2 : Distinction,
  (negative D1 <-> negative D2) -> (positive D1 <-> positive D2).
Proof.
  intros D1 D2 H. split.
  - intro p1. apply (proj2 (positive_iff_not_negative D2)). intro n2.
    exact (proj1 (positive_iff_not_negative D1) p1 (proj2 H n2)).
  - intro p2. apply (proj2 (positive_iff_not_negative D1)). intro n1.
    exact (proj1 (positive_iff_not_negative D2) p2 (proj1 H n1)).
Qed.

(** The two sides are never equivalent — and hence never the same
    proposition. "Two" is a theorem here, and it uses both rules. *)
Theorem sides_not_equivalent : forall D : Distinction,
  ~ (positive D <-> negative D).
Proof.
  intros D [H1 H2]. destruct (exhaustive D) as [p | n].
  - exact (exclusive D (conj p (H1 p))).
  - exact (exclusive D (conj (H2 n) n)).
Qed.

Theorem sides_distinct : forall D : Distinction,
  positive D <> negative D.
Proof.
  intros D Heq. apply (sides_not_equivalent D). rewrite Heq.
  split; intro H; exact H.
Qed.

(* ========================================================================= *)
(*  2. THE TWO RULES ARE INDEPENDENT, AND BOTH ARE NEEDED                    *)
(* ========================================================================= *)

(** Neither field of the record follows from the other. *)
Theorem exclusive_not_from_exhaustive :
  ~ (forall p n : Prop, p \/ n -> ~ (p /\ n)).
Proof. intro H. exact (H True True (or_introl I) (conj I I)). Qed.

Theorem exhaustive_not_from_exclusive :
  ~ (forall p n : Prop, ~ (p /\ n) -> p \/ n).
Proof.
  intro H.
  destruct (H False False (fun X => match X with conj h _ => h end))
    as [h | h]; exact h.
Qed.

(** With exhaustiveness alone, co-definition can fail (both sides hold). *)
Theorem codefinition_needs_exclusive :
  exists p n : Prop, (p \/ n) /\ ~ (n <-> ~ p).
Proof.
  exists True, True. split.
  - left. exact I.
  - intros [H _]. exact (H I I).
Qed.

(** With exclusiveness alone, co-definition can fail (neither side holds:
    the "third way"). *)
Theorem codefinition_needs_exhaustive :
  exists p n : Prop, ~ (p /\ n) /\ ~ (n <-> ~ p).
Proof.
  exists False, False. split.
  - intros [h _]. exact h.
  - intros [_ H]. exact (H (fun h => h)).
Qed.

Theorem third_way_without_exhaustive :
  exists p n : Prop, ~ (p /\ n) /\ ~ p /\ ~ n.
Proof.
  exists False, False. split; [| split].
  - intros [h _]. exact h.
  - intro h. exact h.
  - intro h. exact h.
Qed.

(* ========================================================================= *)
(*  3. ONE RULE — CO-DEFINITION — YIELDS L2, L4 AND BINARITY                 *)
(* ========================================================================= *)

(** Let the two sides be bound by the single rule [n <-> ~ p]. Then
    non-overlap (L2), grounding (L4) and "no third" (L3 as binarity) are
    THEOREMS — not fields — and need no axiom. *)

Theorem L2_from_codefinition : forall p n : Prop,
  (n <-> ~ p) -> ~ (p /\ n).
Proof. intros p n c [hp hn]. exact (proj1 c hn hp). Qed.

Theorem L4_from_codefinition : forall p n : Prop,
  (n <-> ~ p) -> p -> ~ n.
Proof. intros p n c hp hn. exact (proj1 c hn hp). Qed.

Theorem binarity_from_codefinition : forall p n : Prop,
  (n <-> ~ p) -> ~ ~ (p \/ n).
Proof.
  intros p n c H. apply H. right. apply (proj2 c). intro hp.
  apply H. left. exact hp.
Qed.

(** L4 in the form "one side grounds the denial of the other" and L2 in the
    form "the sides do not overlap" are one and the same statement. *)
Theorem L4_form_iff_L2_form : forall p n : Prop,
  (p -> ~ n) <-> ~ (p /\ n).
Proof.
  intros p n. split.
  - intros H [hp hn]. exact (H hp hn).
  - intros H hp hn. exact (H (conj hp hn)).
Qed.

(** A pending act can be built from co-definition ALONE: its exclusivity
    field is computed, not supplied. (In `PendingDistinction` the field
    [p_exclusive] is therefore redundant.) *)
Definition pending_from_codefinition (p n : Prop) (c : n <-> ~ p)
  : PendingDistinction :=
  mkPending p n c (L2_from_codefinition p n c).

(** The two fields of the completed record say exactly: co-definition plus
    an assignment of a side. *)
Theorem fields_iff_codefinition_and_assignment : forall p n : Prop,
  (~ (p /\ n) /\ (p \/ n)) <-> ((n <-> ~ p) /\ (p \/ n)).
Proof.
  intros p n. split.
  - intros [He Hx]. split; [| exact Hx]. split.
    + intros hn hp. exact (He (conj hp hn)).
    + intro hnp. destruct Hx as [hp | hn]; [exfalso; exact (hnp hp) | exact hn].
  - intros [Hc Hx]. split; [| exact Hx]. exact (L2_from_codefinition p n Hc).
Qed.

(* ========================================================================= *)
(*  4. TOTALITY IS EXACTLY EXCLUDED MIDDLE — both directions, no axiom       *)
(* ========================================================================= *)

(** "Every pair of co-defined sides has one side assigned" is the same
    statement as "every proposition is decided". *)
Theorem totality_from_codefinition_iff_EM :
  (forall p n : Prop, (n <-> ~ p) -> p \/ n) <->
  (forall P : Prop, P \/ ~ P).
Proof.
  split.
  - intros H P. exact (H P (~ P) (iff_refl (~ P))).
  - intros EM p n c. destruct (EM p) as [yes | no].
    + left. exact yes.
    + right. exact (proj2 c no).
Qed.

(** Pointwise: where the positive side is decided, co-definition and the
    two record fields coincide. *)
Theorem codefinition_iff_fields_when_decided : forall p n : Prop,
  (p \/ ~ p) -> ((n <-> ~ p) <-> (~ (p /\ n) /\ (p \/ n))).
Proof.
  intros p n d. split.
  - intro c. split.
    + exact (L2_from_codefinition p n c).
    + destruct d as [yes | no]; [left; exact yes | right; exact (proj2 c no)].
  - intro F. exact (proj1 (proj1 (fields_iff_codefinition_and_assignment p n) F)).
Qed.

(** A distinction with positive side P exists exactly when P is decided. *)
Theorem distinction_on_P_iff_decided : forall P : Prop,
  (exists D : Distinction, positive D = P) <-> (P \/ ~ P).
Proof.
  intro P. split.
  - intros [D E]. destruct (exhaustive D) as [p | n].
    + left. rewrite <- E. exact p.
    + right. intro p. rewrite <- E in p. exact (exclusive D (conj p n)).
  - intro d.
    exists (mkDistinction P (~ P)
              (fun X => match X with conj p np => np p end) d).
    reflexivity.
Qed.

(** Hence: "every proposition is the positive side of some distinction" is
    excluded middle — neither weaker nor stronger. This is the honest
    internal form of "L3 = classic". *)
Theorem every_prop_distinguishes_iff_EM :
  (forall P : Prop, exists D : Distinction, positive D = P) <->
  (forall P : Prop, P \/ ~ P).
Proof.
  split.
  - intros H P. exact (proj1 (distinction_on_P_iff_decided P) (H P)).
  - intros EM P. exact (proj2 (distinction_on_P_iff_decided P) (EM P)).
Qed.

(** A pending act can be completed exactly when its positive side is
    decided. *)
Theorem pending_completes_iff_decided : forall D : PendingDistinction,
  (exists C : Distinction, positive C = p_pos D /\ negative C = p_neg D) <->
  (p_pos D \/ ~ p_pos D).
Proof.
  intro D. split.
  - intros [C [Ep En]]. destruct (exhaustive C) as [p | n].
    + left. rewrite <- Ep. exact p.
    + right. intro p. rewrite <- Ep in p. exact (exclusive C (conj p n)).
  - intros [yes | no].
    + exists (actualize D (or_introl yes)). split; reflexivity.
    + exists (actualize D (or_intror (proj2 (p_codef D) no))).
      split; reflexivity.
Qed.

(* ========================================================================= *)
(*  5. AXIOM-FREE INSTANCES                                                  *)
(* ========================================================================= *)

(** Where P is decided, its canonical distinction needs no axiom. *)
Definition distinction_of_decided (P : Prop) (d : P \/ ~ P) : Distinction :=
  mkDistinction P (~ P) (fun X => match X with conj p np => np p end) d.

Theorem distinction_of_decided_sides : forall (P : Prop) (d : P \/ ~ P),
  positive (distinction_of_decided P d) = P /\
  negative (distinction_of_decided P d) = ~ P.
Proof. intros P d. split; reflexivity. Qed.

(** A distinction whose negative side is written WITHOUT a negation sign. *)
Definition distinction_true_false : Distinction :=
  mkDistinction True False
    (fun X => match X with conj _ f => f end)
    (or_introl I).

(** The record is inhabited, and its laws are jointly satisfiable, with no
    axiom at all. *)
Theorem distinction_exists_without_axiom :
  exists D : Distinction, positive D /\ ~ negative D.
Proof.
  exists distinction_true_false. split.
  - exact I.
  - intro f. exact f.
Qed.

(* ========================================================================= *)
(*  6. AT THE PRICE OF `classic`: A DISTINCTION IS ITS TWO SIDES             *)
(* ========================================================================= *)

(** Once excluded middle is accepted, the proofs stored in the fields
    [exclusive] and [exhaustive] carry no information of their own: two
    distinctions with the same sides are the same record. (Excluded middle
    gives proof irrelevance — ClassicalFacts.proof_irrelevance_cci.)
    Print Assumptions: Classical_Prop.classic. *)
Lemma distinction_proof_fields_irrelevant :
  forall (p n : Prop) (e1 e2 : ~ (p /\ n)) (h1 h2 : p \/ n),
    mkDistinction p n e1 h1 = mkDistinction p n e2 h2.
Proof.
  intros p n e1 e2 h1 h2.
  rewrite (proof_irrelevance_cci classic _ e1 e2).
  rewrite (proof_irrelevance_cci classic _ h1 h2).
  reflexivity.
Qed.

Theorem distinction_determined_by_sides : forall D1 D2 : Distinction,
  positive D1 = positive D2 -> negative D1 = negative D2 -> D1 = D2.
Proof.
  intros [p1 n1 e1 h1] [p2 n2 e2 h2]. simpl. intros Hp Hn. subst.
  apply distinction_proof_fields_irrelevant.
Qed.

(** Every distinction coincides with the canonical one on its positive side
    up to equivalence of the sides: the general record is wider than the
    canonical construction in FORM only (chapter I.2 of the volume).
    Print Assumptions: Classical_Prop.classic (through [distinction_of]). *)
Theorem every_distinction_canonical_up_to_iff : forall D : Distinction,
  (positive D <-> positive (distinction_of (positive D))) /\
  (negative D <-> negative (distinction_of (positive D))).
Proof.
  intro D. split.
  - apply iff_refl.
  - exact (negative_iff_not_positive D).
Qed.

(** The step-by-step script of chapter I.2 of the volume (constructor
    applied to the two sides, then the two proof obligations) builds the
    same object as the one-term definition in Distinction.v: equality by
    computation. Print Assumptions: Classical_Prop.classic. *)
Definition distinction_of_by_steps (P : Prop) : Distinction.
Proof.
  apply (mkDistinction P (~ P)).
  - (* exclusive : ~(P /\ ~ P) *)
    intros [p np]. exact (np p).
  - (* exhaustive : P \/ ~ P *)
    apply classic.
Defined.

Theorem distinction_of_by_steps_eq : forall P : Prop,
  distinction_of_by_steps P = distinction_of P.
Proof. reflexivity. Qed.

(* ========================================================================= *)
(*  7. IS / IS NOT / POTENTIAL — AND NO FOURTH                               *)
(*     (author's word, 2026-11-13: a distinction either is or is not; a      *)
(*     potential for a distinction is possible too; by construction there    *)
(*     are no other cases — a limit of logic itself, not of the theory)      *)
(* ========================================================================= *)

(** A distinction with the given two sides IS. *)
Definition actual_on (p n : Prop) : Prop :=
  exists D : Distinction, positive D = p /\ negative D = n.

(** There is a POTENTIAL for a distinction with the given two sides: the
    pending act — sides co-defined, no side assigned yet. *)
Definition potential_on (p n : Prop) : Prop :=
  exists D : PendingDistinction, p_pos D = p /\ p_neg D = n.

(** The potential is exactly co-definition of the sides. *)
Theorem potential_iff_codefinition : forall p n : Prop,
  potential_on p n <-> (n <-> ~ p).
Proof.
  intros p n. split.
  - intros [D [Hp Hn]]. subst. exact (p_codef D).
  - intro c. exists (pending_from_codefinition p n c). split; reflexivity.
Qed.

(** What separates the potential from the distinction is ONE thing: the
    assignment of a side. *)
Theorem actual_iff_potential_and_assignment : forall p n : Prop,
  actual_on p n <-> (potential_on p n /\ (p \/ n)).
Proof.
  intros p n. split.
  - intros [D [Hp Hn]]. subst. split.
    + exists (mkPending (positive D) (negative D)
                (negative_iff_not_positive D) (exclusive D)).
      split; reflexivity.
    + exact (exhaustive D).
  - intros [[D [Hp Hn]] a]. subst.
    exists (actualize D a). split; reflexivity.
Qed.

(** Where a distinction is, its potential is. *)
Theorem actual_is_potential : forall p n : Prop,
  actual_on p n -> potential_on p n.
Proof.
  intros p n H. exact (proj1 (proj1 (actual_iff_potential_and_assignment p n) H)).
Qed.

(** A potential cannot be closed for good: where the sides are co-defined,
    the absence of the distinction is contradictory. *)
Theorem potential_cannot_be_absent : forall p n : Prop,
  potential_on p n -> ~ ~ actual_on p n.
Proof.
  intros p n Hpot Habs.
  apply (binarity_from_codefinition p n (proj1 (potential_iff_codefinition p n) Hpot)).
  intro a. apply Habs.
  apply (proj2 (actual_iff_potential_and_assignment p n)). split; assumption.
Qed.

(** "IS NOT" has one meaning: the distinction is absent exactly when there
    is no potential for it. *)
Theorem absent_iff_no_potential : forall p n : Prop,
  ~ actual_on p n <-> ~ potential_on p n.
Proof.
  intros p n. split.
  - intros Habs Hpot. exact (potential_cannot_be_absent p n Hpot Habs).
  - intros Hno Hact. exact (Hno (actual_is_potential p n Hact)).
Qed.

(** ... that is: exactly when the two sides are not co-defined. *)
Theorem absent_iff_not_codefined : forall p n : Prop,
  ~ actual_on p n <-> ~ (n <-> ~ p).
Proof.
  intros p n. split.
  - intros Habs c.
    exact (proj1 (absent_iff_no_potential p n) Habs
             (proj2 (potential_iff_codefinition p n) c)).
  - intros Hnc Hact.
    exact (Hnc (proj1 (potential_iff_codefinition p n) (actual_is_potential p n Hact))).
Qed.

(** NO FOURTH: a "partial" distinction — a potential that is nevertheless
    absent — does not exist. *)
Theorem no_partial_distinction : forall p n : Prop,
  ~ (potential_on p n /\ ~ actual_on p n).
Proof.
  intros p n [Hpot Habs]. exact (potential_cannot_be_absent p n Hpot Habs).
Qed.

(** A part of the structure is no distinction at all: a pair that lacks
    co-definition carries neither a distinction nor a potential for one —
    whichever single rule of the record it happens to satisfy. *)
Theorem part_of_structure_is_no_distinction : forall p n : Prop,
  ~ (n <-> ~ p) -> ~ potential_on p n /\ ~ actual_on p n.
Proof.
  intros p n Hnc. split.
  - intro Hpot. exact (Hnc (proj1 (potential_iff_codefinition p n) Hpot)).
  - exact (proj2 (absent_iff_not_codefined p n) Hnc).
Qed.

(** Both single-rule cases occur: non-overlap alone, and coverage alone —
    and neither carries a distinction or a potential. *)
Theorem exclusive_alone_is_no_distinction :
  exists p n : Prop, ~ (p /\ n) /\ ~ potential_on p n /\ ~ actual_on p n.
Proof.
  exists False, False. split.
  - intros [f _]. exact f.
  - apply part_of_structure_is_no_distinction.
    intros [_ back]. exact (back (fun f => f)).
Qed.

Theorem exhaustive_alone_is_no_distinction :
  exists p n : Prop, (p \/ n) /\ ~ potential_on p n /\ ~ actual_on p n.
Proof.
  exists True, True. split.
  - left. exact I.
  - apply part_of_structure_is_no_distinction.
    intros [fwd _]. exact (fwd I I).
Qed.

(** The potential becomes the distinction exactly where the positive side
    is decided; so "every potential is completed" is excluded middle. *)
Theorem potential_is_actual_iff_decided : forall p n : Prop,
  potential_on p n -> (actual_on p n <-> (p \/ ~ p)).
Proof.
  intros p n Hpot.
  pose proof (proj1 (potential_iff_codefinition p n) Hpot) as c. split.
  - intro Hact.
    destruct (proj2 (proj1 (actual_iff_potential_and_assignment p n) Hact)) as [yes | no].
    + left. exact yes.
    + right. exact (proj1 c no).
  - intros [yes | no]; apply (proj2 (actual_iff_potential_and_assignment p n)); split.
    + exact Hpot.
    + left. exact yes.
    + exact Hpot.
    + right. exact (proj2 c no).
Qed.

Theorem every_potential_completes_iff_EM :
  (forall p n : Prop, potential_on p n -> actual_on p n) <->
  (forall P : Prop, P \/ ~ P).
Proof.
  split.
  - intros H P.
    assert (Hpot : potential_on P (~ P)).
    { apply (proj2 (potential_iff_codefinition P (~ P))). apply iff_refl. }
    exact (proj1 (potential_is_actual_iff_decided P (~ P) Hpot) (H P (~ P) Hpot)).
  - intros em p n Hpot.
    exact (proj2 (potential_is_actual_iff_decided p n Hpot) (em p)).
Qed.
