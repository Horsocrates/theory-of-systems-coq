(** * KnowledgeTruthLie.v — untruth vs lie: the double root, the modal
      substitution, the overlay that does not stand by itself
      (formalization of VL-5/VL-6 adjudications V-7..V-15, the will working
       record, Knigi/Volya/00; the ethics <-> question-branch bridge;
       sibling of KnowledgeQuestionPath.v / KnowledgeWillStatus.v and of
       the src/ethics/ layer)

    Elements: content statuses (true / untrue); intents of the asserting
              act; the two kinds of root (of the act / of the content);
              presentations (what is shown, what is hidden); declarations
              of modal layer; the overlay held by effort.
    Roles:    UNTRUTH is a status of content ("is not the truth", no
              intent — an honest error is possible); a LIE is a status of
              the ACT: the will intentionally aimed at untruth; the lie
              always has its own root — the ground of the act — while the
              root of the CONTENT (the chain of grounds from what-is) it
              never has; the lie is addressed: its direction is the other
              witness.
    Rules:    the projection itself is legal — a thought-form of the layer
              "can be, but is not"; the lie is committed at the assignment
              of status: the possible declared as being, without grounds;
              the objective field is not damaged (what is — is; nothing is
              destroyed) — damaged is the other witness's record; the
              constatation belongs to the witness, not to the will: the
              refusal of truth turns the vector away, it does not erase
              the record; the overlay structure stands only while actively
              held — the truth stands by itself.
    Status:   intention = goal + direction of the act of will; the sophist
              hides BOTH: the root of his act (the motive) and the absence
              of the content root.
    STATUS: 21 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: July 2026

    ============================== E/R/R razbor ==============================
    Rules: the double root separates what my earlier reading merged: every
      act is grounded (its motivating sufficient ground), but only the true
      content carries a chain of grounds from what-is; recoverability of the
      content root is the criterion of an answer.
    Roles: the lie is a full act — goal (the untruth as projection),
      direction (the other witness), ground (the concealed motive), path
      (the maintenance of the projection).
    Elements: finite decidable enumerations; the overlay model is a boolean
      effort-trace over finite time (P4).
    P4 diagnostic (could it be otherwise?): an act without an act-root does
      not fire (L4); a true content without a content root would be a truth
      underivable from what-is — excluded by the connectivity of the field;
      an overlay standing without effort would be a projection with roots
      in what-is, i.e. not an overlay but the truth. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* ---------- untruth is a status of content; the lie is a status of the act ---------- *)

Inductive ContentStatus := CsTrue | CsUntrue.

Inductive AssertIntent := IntToTruth | IntToUntruth.

Record Assertion := mkAssert {
  asserted_status : ContentStatus;
  assert_intent   : AssertIntent
}.

Definition is_lie (a : Assertion) : bool :=
  match assert_intent a with IntToUntruth => true | _ => false end.

Definition is_honest_error (a : Assertion) : bool :=
  match asserted_status a, assert_intent a with
  | CsUntrue, IntToTruth => true
  | _, _ => false
  end.

(* untruth without intent is not a lie: the honest error *)
Theorem untruth_without_intent_not_lie :
  forall a, is_honest_error a = true -> is_lie a = false.
Proof.
  intros [c i] H; destruct c, i; simpl in *; try discriminate H; reflexivity.
Qed.

(* the same content, two different act-statuses: the lie lives in the act *)
Theorem same_content_two_acts :
  exists a b, asserted_status a = asserted_status b /\
    is_lie a = true /\ is_lie b = false.
Proof.
  exists (mkAssert CsUntrue IntToUntruth), (mkAssert CsUntrue IntToTruth).
  split; [reflexivity | split; reflexivity].
Qed.

Theorem lie_by_intent :
  forall a, is_lie a = true <-> assert_intent a = IntToUntruth.
Proof.
  intros [c i]; destruct i; simpl; split; intro H;
  first [ reflexivity | discriminate H ].
Qed.

(* ---------- the double root: of the act and of the content ---------- *)

Inductive RootKind := RAct | RContent.

Definition has_root (a : Assertion) (r : RootKind) : bool :=
  match r with
  | RAct => true
      (* every performed act carries its motivating ground (L4) *)
  | RContent =>
      match asserted_status a with CsTrue => true | CsUntrue => false end
      (* only the truth has a chain of grounds from what-is *)
  end.

Theorem every_act_rooted : forall a, has_root a RAct = true.
Proof. intro a; reflexivity. Qed.

Theorem truth_double_rooted :
  forall a, asserted_status a = CsTrue -> forall r, has_root a r = true.
Proof.
  intros a H r; destruct r; simpl; [reflexivity | rewrite H; reflexivity].
Qed.

Theorem untruth_no_content_root :
  forall a, asserted_status a = CsUntrue -> has_root a RContent = false.
Proof. intros a H; simpl; rewrite H; reflexivity. Qed.

(* the lie has its own root — as an act; and none — as a truth-claim *)
Theorem lie_rooted_only_as_act :
  forall a, asserted_status a = CsUntrue -> is_lie a = true ->
    has_root a RAct = true /\ has_root a RContent = false.
Proof.
  intros a H _; split; [reflexivity | simpl; rewrite H; reflexivity].
Qed.

Theorem roots_independent :
  exists a, has_root a RAct = true /\ has_root a RContent = false.
Proof. exists (mkAssert CsUntrue IntToUntruth); split; reflexivity. Qed.

(* ---------- the sophist: the double concealment ---------- *)

Inductive Showing := Shown | Hidden.

Record Presentation := mkP {
  motive_shown      : Showing;  (* the root of the act *)
  content_gap_shown : Showing   (* the absence of the content root *)
}.

Definition verifiable_pres (p : Presentation) : bool :=
  match motive_shown p, content_gap_shown p with
  | Shown, Shown => true | _, _ => false
  end.

Definition sophistic (p : Presentation) : bool :=
  match motive_shown p, content_gap_shown p with
  | Hidden, Hidden => true | _, _ => false
  end.

Theorem sophistry_double_concealment :
  forall p, sophistic p = true ->
    motive_shown p = Hidden /\ content_gap_shown p = Hidden.
Proof.
  intros [m c] H; destruct m, c; simpl in *; try discriminate H;
  split; reflexivity.
Qed.

Theorem sophistic_never_verifiable :
  forall p, sophistic p = true -> verifiable_pres p = false.
Proof.
  intros [m c] H; destruct m, c; simpl in *; try discriminate H; reflexivity.
Qed.

(* ---------- the modal substitution: the possible declared as being ---------- *)

Inductive Layer := LActual | LPotential.

Record Declaration := mkD {
  built_in    : Layer;  (* where the construction really lives *)
  declared_as : Layer   (* the status assigned to it for the other *)
}.

Definition honest_declaration (d : Declaration) : bool :=
  match built_in d, declared_as d with
  | LActual, LActual | LPotential, LPotential => true
  | _, _ => false
  end.

Definition modal_substitution (d : Declaration) : bool :=
  match built_in d, declared_as d with
  | LPotential, LActual => true | _, _ => false
  end.

(* the projection itself is legal: a thought-form declared as possible *)
Theorem projection_itself_legal :
  honest_declaration (mkD LPotential LPotential) = true.
Proof. reflexivity. Qed.

Theorem substitution_dishonest :
  forall d, modal_substitution d = true -> honest_declaration d = false.
Proof.
  intros [b dc] H; destruct b, dc; simpl in *; try discriminate H; reflexivity.
Qed.

Theorem honest_iff_status_matches :
  forall d, honest_declaration d = true <-> built_in d = declared_as d.
Proof.
  intros [b dc]; destruct b, dc; simpl; split; intro H;
  first [ reflexivity | discriminate H ].
Qed.

(* ---------- the lie is addressed; the objective field is not damaged ---------- *)

Inductive LieTarget := TObjectiveField | TOtherRecord.

Definition damaged (t : LieTarget) : bool :=
  match t with TObjectiveField => false | TOtherRecord => true end.

(* what is — is: nothing is destroyed in the common field *)
Theorem objective_field_undamaged : damaged TObjectiveField = false.
Proof. reflexivity. Qed.

(* damaged is the other witness's record of status *)
Theorem lie_damages_the_other_record : damaged TOtherRecord = true.
Proof. reflexivity. Qed.

(* ---------- the refusal turns the vector away; it does not erase ---------- *)

Inductive CloserActor := ByWitnessActor | ByWillActor.

Definition closes_constatation : CloserActor := ByWitnessActor.

(* the constatation is the witness's act: the will cannot un-see *)
Theorem constatation_not_wills : closes_constatation <> ByWillActor.
Proof. discriminate. Qed.

Inductive RefusalChange := ChangesVector | ChangesRecord.

Definition refusal : RefusalChange := ChangesVector.

Theorem refusal_turns_away_not_erases :
  refusal = ChangesVector /\ ChangesVector <> ChangesRecord.
Proof. split; [reflexivity | discriminate]. Qed.

(* ---------- the overlay stands only while held; the truth stands by itself ---------- *)

Definition overlay_stands (effort : nat -> bool) (t : nat) : bool :=
  forallb effort (seq 0 (S t)).

(* the overlay needs the effort at EVERY moment *)
Theorem overlay_needs_every_moment :
  forall eff t k, overlay_stands eff t = true -> k <= t -> eff k = true.
Proof.
  intros eff t k H Hk; unfold overlay_stands in H;
  rewrite forallb_forall in H; apply H; apply in_seq; lia.
Qed.

(* one gap — and the overlay falls *)
Theorem overlay_falls_at_first_gap :
  forall eff t k, k <= t -> eff k = false -> overlay_stands eff t = false.
Proof.
  intros eff t k Hk Hf; destruct (overlay_stands eff t) eqn:E;
  [ exfalso | reflexivity ].
  assert (eff k = true) by (eapply overlay_needs_every_moment; eauto).
  congruence.
Qed.

Definition truth_stands (t : nat) : bool := true.

(* the truth is self-supporting: its roots are held by the field *)
Theorem truth_needs_no_effort : forall t, truth_stands t = true.
Proof. intro t; reflexivity. Qed.

(* every new lie widens the area that must be held: the spiral as cost *)
Definition maintenance (lies : nat) : nat := lies.

Theorem maintenance_grows :
  forall n, maintenance n < maintenance (S n).
Proof. intro n; unfold maintenance; lia. Qed.
