(** * KnowledgeEgoZone.v — The Ego Zone and the Registry of Impossible Constructions as ToS System

    Formalizes the adjudicated ego thread (working journal MP-37..MP-41,
    2026-07-21): ego = the ZONE of self-records in the witness's mental
    field (not a thing, not an agency), with two independent axes
    (correspondence x size); the triple witness (role) / "I" (pointer) /
    ego (zone of records) making reification and identification errors
    unbuildable; "ego death" as a doubly impossible construction
    (records are not organisms; dis-identification and potentialization
    preserve the zone); labels without a meeting as projections; and the
    registry seed: every impossible construction is built by a category
    substitution, with root/derivative structure (nothing-as-thing ->
    view-from-nowhere).

    Elements: self-records in the mental field (ego zone); witness
              states (zone, identification stance, attention); labels
              about another's zone; categories and substitutions.
    Roles:    witness = the only willing agent (records and zones do
              not will); correctness = correspondence status of a
              record; identification and attention = droppable stances;
              legality of a construction = category preservation.
    Rules:    axes of the zone are independent (any size, either
              status); dis-identification and the peak experience
              preserve the zone and its size (return guaranteed);
              death applies to organisms only — a zone cannot die;
              a label without a meeting projects; a substitution is
              never legal; derivatives share the root's category.
    Status:   all proved; self-contained (no ToS imports).
    STATUS: 21 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: July 2026
*)

From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

(* ================================================================ *)
(** ** 1. The ego zone: records about self, two independent axes     *)
(* ================================================================ *)

(** A self-record either corresponds to what is (correct) or not
    (an illusory construction). *)
Record SelfRecord : Type := mkSR { sr_matches : bool }.

(** The ego is a ZONE: a region of records about self in the mental
    field — content, not an agent. *)
Definition EgoZone : Type := list SelfRecord.

Definition zone_size (z : EgoZone) : nat := length z.

Definition all_correct (z : EgoZone) : bool := forallb sr_matches z.

Definition has_illusion (z : EgoZone) : bool :=
  existsb (fun r => negb (sr_matches r)) z.

Definition correct_zone (n : nat) : EgoZone :=
  repeat (mkSR true) n.

Definition illusory_zone (n : nat) : EgoZone :=
  repeat (mkSR false) n.

Lemma repeat_len : forall (A : Type) (x : A) n, length (repeat x n) = n.
Proof.
  intros A x n. induction n; simpl; [reflexivity | rewrite IHn; reflexivity].
Qed.

Lemma correct_zone_all : forall n, all_correct (correct_zone n) = true.
Proof. induction n; simpl; [reflexivity | exact IHn]. Qed.

Lemma illusory_zone_has : forall n, has_illusion (illusory_zone (S n)) = true.
Proof. intros n. reflexivity. Qed.

(** The two axes are independent: a zone of ANY size can be all-correct
    and can carry illusion. Size is neutral; the flaw is illusoriness. *)
Theorem axes_independent : forall n,
  zone_size (correct_zone n) = n /\
  all_correct (correct_zone n) = true /\
  zone_size (illusory_zone (S n)) = S n /\
  has_illusion (illusory_zone (S n)) = true.
Proof.
  intros n. split; [apply repeat_len | split;
    [apply correct_zone_all | split;
      [apply repeat_len | apply illusory_zone_has]]].
Qed.

(* ================================================================ *)
(** ** 2. The triple: witness (role) / "I" (pointer) / ego (zone)    *)
(* ================================================================ *)

(** Who can will? Records and zones are content; the witness is the
    only doer. "The ego wants" attributes will to content — the model
    makes it false, not just wrong. *)
Inductive Entity : Type :=
  | EWitness
  | ERecord (r : SelfRecord)
  | EZone   (z : EgoZone).

Definition can_will (e : Entity) : bool :=
  match e with
  | EWitness => true
  | _        => false
  end.

Theorem records_do_not_will : forall r, can_will (ERecord r) = false.
Proof. intros r. reflexivity. Qed.

Theorem zone_does_not_will : forall z, can_will (EZone z) = false.
Proof. intros z. reflexivity. Qed.

(** Reification (element passed off as role) is unbuildable: whatever
    wills IS the witness. *)
Theorem only_witness_wills : forall e, can_will e = true -> e = EWitness.
Proof. intros e H. destruct e; [reflexivity | discriminate H | discriminate H]. Qed.

(* ================================================================ *)
(** ** 3. Identification is a stance; "ego death" is ill-built       *)
(* ================================================================ *)

(** The witness state: his zone, whether he takes the records for
    himself (identification), whether attention dwells in the zone. *)
Record WitnessState : Type := mkWS {
  ws_zone       : EgoZone;
  ws_identified : bool;
  ws_attending  : bool
}.

(** Dis-identification: dropping the stance — the zone persists. *)
Definition drop_identification (w : WitnessState) : WitnessState :=
  mkWS (ws_zone w) false (ws_attending w).

Theorem disidentification_keeps_zone : forall w,
  ws_zone (drop_identification w) = ws_zone w.
Proof. intros w. reflexivity. Qed.

Theorem disidentification_not_annihilation : forall w,
  zone_size (ws_zone (drop_identification w)) = zone_size (ws_zone w).
Proof. intros w. reflexivity. Qed.

(** The peak experience ("ego death"): identification dropped AND
    attention withdrawn (potentialization). Records untouched. *)
Definition peak (w : WitnessState) : WitnessState :=
  mkWS (ws_zone w) false false.

Definition come_back (w : WitnessState) : WitnessState :=
  mkWS (ws_zone w) (ws_identified w) true.

Theorem peak_preserves_records : forall w, ws_zone (peak w) = ws_zone w.
Proof. intros w. reflexivity. Qed.

(** Return guaranteed: after the peak the same zone is there to read —
    the person still knows his name. *)
Theorem return_with_zone_intact : forall w,
  ws_zone (come_back (peak w)) = ws_zone w.
Proof. intros w. reflexivity. Qed.

(** Death is a predicate of organisms. A zone of records is not an
    organism: "ego death" applies a predicate outside its kind. *)
Inductive Kind : Type := KOrganism | KRecord | KZone | KRole | KPointer.

Definition can_die (k : Kind) : bool :=
  match k with KOrganism => true | _ => false end.

Theorem zone_cannot_die : can_die KZone = false.
Proof. reflexivity. Qed.

Theorem death_only_for_organisms : forall k,
  can_die k = true -> k = KOrganism.
Proof.
  intros k H. destruct k; [reflexivity | discriminate H | discriminate H |
    discriminate H | discriminate H].
Qed.

(* ================================================================ *)
(** ** 4. Labels without a meeting are projections                   *)
(* ================================================================ *)

(** A label about ANOTHER's zone ("big ego"): without a meeting with
    that zone it is written from the labeler's own zone — a projection.
    Even a large CORRECT zone can be so labeled. *)
Record ZoneLabel : Type := mkZL {
  zl_met_other  : bool;  (** did the labeler meet the other's zone *)
  zl_says_inflated : bool
}.

Definition label_projects (l : ZoneLabel) : bool := negb (zl_met_other l).

Theorem no_meeting_label_projects : forall l,
  zl_met_other l = false -> label_projects l = true.
Proof. intros l H. unfold label_projects. rewrite H. reflexivity. Qed.

Theorem big_correct_can_be_mislabeled :
  exists (z : EgoZone) (l : ZoneLabel),
    all_correct z = true /\ zl_says_inflated l = true /\
    label_projects l = true.
Proof.
  exists (correct_zone 5), (mkZL false true).
  split; [apply correct_zone_all | split; reflexivity].
Qed.

(* ================================================================ *)
(** ** 5. Registry seed: impossibles built by category substitution  *)
(* ================================================================ *)

Inductive Category : Type :=
  | CProcess | CObject | CRole | CThing | CElement
  | CStatus  | CSystem | CPosition | CPole | CAbsence.

Definition cat_eqb (a b : Category) : bool :=
  match a, b with
  | CProcess, CProcess | CObject, CObject | CRole, CRole
  | CThing, CThing | CElement, CElement | CStatus, CStatus
  | CSystem, CSystem | CPosition, CPosition | CPole, CPole
  | CAbsence, CAbsence => true
  | _, _ => false
  end.

Lemma cat_eqb_spec : forall a b, cat_eqb a b = true <-> a = b.
Proof.
  intros a b. destruct a, b; split; intros H;
    try reflexivity; try discriminate H.
Qed.

(** A construction moves content of one category into another; it is
    legal only when the category is preserved. *)
Record Construction : Type := mkCn {
  built_from : Category;
  passed_as  : Category
}.

Definition legal (c : Construction) : bool :=
  cat_eqb (built_from c) (passed_as c).

Theorem legal_iff_same : forall c,
  legal c = true <-> built_from c = passed_as c.
Proof. intros c. unfold legal. apply cat_eqb_spec. Qed.

(** The registry seed (adjudicated entries; names in comments). *)
Definition nothing_as_thing  := mkCn CAbsence CThing.    (* nichto kak vesch *)
Definition view_from_nowhere := mkCn CAbsence CPosition. (* vzglyad-niotkuda *)
Definition ego_as_agent      := mkCn CElement CRole.     (* "ego khochet" *)
Definition ego_death         := mkCn CElement CThing.    (* smert' ego *)
Definition completed_corpus  := mkCn CProcess CObject.   (* zavershyonny svod *)
Definition actual_infinity   := mkCn CProcess CObject.   (* aktualnaya beskonechnost *)
Definition status_as_system  := mkCn CStatus  CSystem.   (* Sushchestvovanie = sistema *)
Definition position_as_pole  := mkCn CPosition CPole.    (* naivny obyektivizm *)

Definition registry : list Construction :=
  [ nothing_as_thing; view_from_nowhere; ego_as_agent; ego_death;
    completed_corpus; actual_infinity; status_as_system; position_as_pole ].

(** Every registry entry is a substitution — none is legal. *)
Theorem all_registry_illegal :
  forallb (fun c => negb (legal c)) registry = true.
Proof. reflexivity. Qed.

(** Root/derivative structure: a derivative misuses the same root
    category as its root entry. View-from-nowhere derives from
    nothing-as-thing: both build on reified absence. *)
Definition derives_from (child parent : Construction) : bool :=
  cat_eqb (built_from child) (built_from parent).

Theorem nowhere_derives_from_nothing :
  derives_from view_from_nowhere nothing_as_thing = true.
Proof. reflexivity. Qed.

(** Ego death derives from ego-as-agent: both build on the records. *)
Theorem ego_death_derives_from_reification :
  derives_from ego_death ego_as_agent = true.
Proof. reflexivity. Qed.

(** The impossible does not exist — it is only built: an illegal
    construction stays a construction; legality would require the
    categories to coincide. *)
Theorem impossible_never_becomes_legal : forall c,
  built_from c <> passed_as c -> legal c = false.
Proof.
  intros c H. destruct (legal c) eqn:E; [ | reflexivity].
  exfalso. apply H. apply legal_iff_same. exact E.
Qed.
