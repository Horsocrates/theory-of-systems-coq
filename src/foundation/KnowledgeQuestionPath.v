(** * KnowledgeQuestionPath.v — the LADDER of questions, the root, the duality,
      the connected hierarchy, and the ethics of the entrance
      (formalization of MP-20..MP-29 adjudications, the mental-field working
       record, Knigi/Volya/01; sibling of KnowledgeQuestion.v /
       KnowledgeAnswerExists.v / KnowledgeMentalField.v)

    Elements: three tiers of questioning (target / process / domain); the
              hierarchy of systems with Logic at the top; provenances of
              utterances; walks along the root; fields and cycles.
    Roles:    the target question holds the whole action (its goal = the
              essence); the ROOT question advances along the root — and the
              motion along the root IS the motion along logic; the CONTEXT
              question surveys the influencing systems (outward / inward /
              sideways) and prepares the next root step; domain questions
              live inside the cycle of every step.
    Rules:    every system stands inside Logic — the system of rules is the
              top, self-grounded (the FIRST ground is the law of sufficient
              ground itself); the outward path is finite for every system,
              the inward chain is open — the completed svod of systems is
              impossible (there lives the impossible goal, 1.A.7); an answer
              exists only to a question: whatever is an answer carries its
              root question; the sophist conceals an existing root; every
              question bounds its own field and runs its own cycle; walking
              the root goes rung by rung, without a skip.
    Status:   the ethics of the entrance (V31/V32): the five defects of 1.A
              are volitional distortions of the intent, split against-other /
              against-self; honest questioning moves ON the root — and since
              good = logic = order, the honest entrance is good and the
              sophistic one is evil at the entrance of reasoning.
    STATUS: 26 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: July 2026

    ============================== E/R/R razbor ==============================
    Rules: connectivity is grounded VERTICALLY (MP-29): everything that can
      be is inside the system of rules; the top is self-grounded and unique;
      hence between any two systems a logical chain exists — the root of a
      question is FOUND, not invented.  Inward the hierarchy is open (P4):
      no list of systems is complete.
    Roles: root/context/domain questions are functions in the process, not
      forms: the same goal/category may serve either.
    Elements: finite decidable models; the open chain SNest n is potential,
      never a completed totality.
    P4 diagnostic: the svod theorem is the formal face of "impossible goal";
      pointwise-finite ascent with no uniform bound is honest finitism. *)

From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.

(* ---------- three tiers of questioning (MP-22) ---------- *)

Inductive Tier := TTarget | TProcess | TDomain.
(* the question of the whole action | the questions of the process |
   the leading questions of the domains inside the cycle *)

Inductive ProcessMove := MRoot | MContext | MAside.
(* a root step (into the depth, along the root) | a context step (breadth:
   the influencing systems) | an aside serving neither — the red herring *)

Definition legal_move (m : ProcessMove) : bool :=
  match m with MAside => false | _ => true end.

Theorem aside_illegal : legal_move MAside = false.
Proof. reflexivity. Qed.

Theorem legal_two :
  forall m, legal_move m = true -> m = MRoot \/ m = MContext.
Proof.
  intro m; destruct m; intro H;
  [ left; reflexivity | right; reflexivity | discriminate H ].
Qed.

(* ---------- the hierarchy: Logic on top, Source inside, nesting open ---------- *)

Inductive Sys :=
  | SLogic            (* the system of rules — the top (MP-29) *)
  | SSource           (* the filling inside the structure *)
  | SLight            (* the first generated system — the act of Logic *)
  | SNest (n : nat).  (* the open chain of generated nested systems *)

Definition parent (s : Sys) : Sys :=
  match s with
  | SLogic => SLogic          (* self-grounded: the FIRST ground *)
  | SSource => SLogic
  | SLight => SSource
  | SNest 0 => SLight
  | SNest (S n) => SNest n
  end.

Fixpoint up (k : nat) (s : Sys) : Sys :=
  match k with 0 => s | S k' => up k' (parent s) end.

Definition depth (s : Sys) : nat :=
  match s with SLogic => 0 | SSource => 1 | SLight => 2 | SNest n => 3 + n end.

(* the Source is inside Logic: the filling inside the structure (MP-29) *)
Theorem source_inside_logic : parent SSource = SLogic.
Proof. reflexivity. Qed.

(* the top grounds itself: the first ground is the law of ground itself *)
Theorem logic_self_grounded : parent SLogic = SLogic.
Proof. reflexivity. Qed.

(* and nothing else does: the first ground is unique *)
Theorem self_grounded_unique : forall s, parent s = s -> s = SLogic.
Proof.
  intros s H; destruct s as [ | | | n]; try reflexivity; try discriminate H.
  destruct n as [ | m]; simpl in H.
  - discriminate H.
  - injection H as E; exfalso; apply (Nat.neq_succ_diag_l m); symmetry; exact E.
Qed.

(* the outward path of every system reaches the top in finitely many steps *)
Theorem chain_to_root : forall s, up (depth s) s = SLogic.
Proof.
  intro s; destruct s as [ | | | n]; [reflexivity | reflexivity | reflexivity | ].
  induction n as [ | n IH].
  - reflexivity.
  - simpl in *; exact IH.
Qed.

Theorem inside_logic : forall s, exists k, up k s = SLogic.
Proof. intro s; exists (depth s); apply chain_to_root. Qed.

(* any two systems are connected through the common meta-system:
   the path between any two points exists — the logical chain (MP-25/26) *)
Theorem path_via_common_meta :
  forall a b, exists c ka kb, up ka a = c /\ up kb b = c.
Proof.
  intros a b; exists SLogic, (depth a), (depth b);
  split; apply chain_to_root.
Qed.

(* INWARD the hierarchy is open: under every nested system lies a further one *)
Definition child_of (s t : Sys) : Prop := parent t = s.

Theorem inward_open : forall n, child_of (SNest n) (SNest (S n)).
Proof. intro n; unfold child_of; reflexivity. Qed.

(* the completed svod of systems is impossible: no list holds them all —
   the formal face of the impossible goal (1.A.7) on the hierarchy itself *)
Definition idx (s : Sys) : nat := match s with SNest n => n | _ => 0 end.

Fixpoint maxidx (l : list Sys) : nat :=
  match l with [] => 0 | s :: r => Nat.max (idx s) (maxidx r) end.

Lemma in_le_maxidx : forall l s, In s l -> idx s <= maxidx l.
Proof.
  induction l as [ | a l IH]; simpl; intros s H.
  - contradiction.
  - destruct H as [-> | H].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact H | apply Nat.le_max_r].
Qed.

Theorem no_svod_of_systems :
  forall l : list Sys, ~ In (SNest (S (maxidx l))) l.
Proof.
  intros l H; apply in_le_maxidx in H; simpl in H.
  exact (Nat.nle_succ_diag_l _ H).
Qed.

(* ---------- duality: the answer and its root (MP-23, V30) ---------- *)

Inductive Provenance := ShownRoot | HiddenRoot | NoRoot.
(* honest answer: root shown | sophistry: the root EXISTS but is concealed
   behind the wording | a rootless utterance: not an answer at all *)

Definition is_answer (p : Provenance) : bool :=
  match p with NoRoot => false | _ => true end.

Definition root_shown (p : Provenance) : bool :=
  match p with ShownRoot => true | _ => false end.

(* whatever is an answer carries its root question (V30) *)
Theorem answer_has_root :
  forall p, is_answer p = true -> p = ShownRoot \/ p = HiddenRoot.
Proof.
  intro p; destruct p; intro H;
  [ left; reflexivity | right; reflexivity | discriminate H ].
Qed.

Theorem rootless_not_answer : is_answer NoRoot = false.
Proof. reflexivity. Qed.

(* the sophist's mark: an answer whose existing root is not shown *)
Theorem sophistry_conceals :
  is_answer HiddenRoot = true /\ root_shown HiddenRoot = false.
Proof. split; reflexivity. Qed.

Theorem verifiable_shows_root :
  forall p, root_shown p = true -> is_answer p = true /\ p = ShownRoot.
Proof.
  intro p; destruct p; intro H; try discriminate H;
  split; reflexivity.
Qed.

(* ---------- the ethics of the entrance (V31/V32) ---------- *)

Inductive Intent := ToTruth | ToOther.
(* the intent of the CHOICE of a question: truth, or something else *)

Inductive Target := AgainstOther | AgainstSelf.

Inductive Defect1A :=
  | DLoaded | DMerged | DTabooImposed | DTabooSelf | DContextDodge | DImpossible.
(* loaded question | merged questions | taboo imposed on others |
   self-imposed taboo | context dodge | the impossible goal as a weapon *)

(* every defect of the entrance distorts the intent away from truth (V31) *)
Definition intent_of (d : Defect1A) : Intent := ToOther.

Theorem all_defects_distort : forall d, intent_of d = ToOther.
Proof. intro d; destruct d; reflexivity. Qed.

Definition target_of (d : Defect1A) : Target :=
  match d with
  | DLoaded | DMerged | DTabooImposed => AgainstOther
  | DTabooSelf | DContextDodge | DImpossible => AgainstSelf
  end.

Theorem targets_covered : forall t, exists d, target_of d = t.
Proof.
  intro t; destruct t; [exists DLoaded | exists DTabooSelf]; reflexivity.
Qed.

(* the lock (V32): truth-intent moves ON the root — and the motion along the
   root is the motion along logic; distorted intent leaves the root *)
Inductive Motion := OnRoot | OffRoot.

Definition motion_of (i : Intent) : Motion :=
  match i with ToTruth => OnRoot | ToOther => OffRoot end.

Theorem truth_moves_on_root : motion_of ToTruth = OnRoot.
Proof. reflexivity. Qed.

Theorem defect_leaves_root : forall d, motion_of (intent_of d) = OffRoot.
Proof. intro d; destruct d; reflexivity. Qed.

(* ---------- depth as distance; walking without a skip (V24/V27) ---------- *)

Fixpoint walk (n : nat) : list nat :=
  match n with 0 => [0] | S k => walk k ++ [S k] end.
(* the rungs 0..n of the root, passed one by one *)

Theorem walk_length : forall n, length (walk n) = S n.
Proof.
  induction n as [ | n IH]; simpl.
  - reflexivity.
  - rewrite last_length, IH; reflexivity.
Qed.

(* no skip: every rung up to the goal is actually passed *)
Theorem no_skip : forall n k, k <= n -> In k (walk n).
Proof.
  induction n as [ | n IH]; intros k H.
  - apply Nat.le_0_r in H; subst; simpl; left; reflexivity.
  - apply Nat.le_succ_r in H; destruct H as [H | ->]; simpl.
    + apply in_or_app; left; apply IH; exact H.
    + apply in_or_app; right; left; reflexivity.
Qed.

(* a deep question is legal beyond any current slice: distance is unbounded,
   the walk merely gets longer (the slice grows along the way) *)
Theorem deep_beyond_slice :
  forall slice, exists n, slice < n /\ length (walk n) = S n.
Proof.
  intro slice; exists (S slice); split; [lia | apply walk_length].
Qed.

(* ---------- the field and the cycle of every question (V29) ---------- *)

Record QField := mkF { f_lo : nat; f_hi : nat }.

Definition within (a b : QField) : bool :=
  (f_lo b <=? f_lo a) && (f_hi a <=? f_hi b).

Theorem within_refl : forall f, within f f = true.
Proof.
  intro f; unfold within; rewrite !Nat.leb_refl; reflexivity.
Qed.

(* questions in questions = fields in fields: nesting composes *)
Theorem within_trans :
  forall a b c, within a b = true -> within b c = true -> within a c = true.
Proof.
  unfold within; intros a b c H1 H2.
  apply andb_true_iff in H1 as [H1a H1b].
  apply andb_true_iff in H2 as [H2a H2b].
  apply andb_true_iff; split; apply Nat.leb_le.
  - apply Nat.le_trans with (f_lo b); apply Nat.leb_le; assumption.
  - apply Nat.le_trans with (f_hi b); apply Nat.leb_le; assumption.
Qed.

(* the cycle: the process of the path from the asking to its closure *)
Inductive CyclePhase := CAsk | CWork | CClose.

Definition cycle : list CyclePhase := [CAsk; CWork; CClose].

Theorem cycle_opens_with_ask : exists post, cycle = CAsk :: post.
Proof. exists [CWork; CClose]; reflexivity. Qed.

Theorem cycle_closes : exists pre, cycle = pre ++ [CClose].
Proof. exists [CAsk; CWork]; reflexivity. Qed.
