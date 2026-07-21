(** * KnowledgeDomainCycle.v — the domain cycle realizes the path: questions x domains
      (formalization of MP-35, the second step of MP-2.2: leading questions of
       the six domains laid out on the axes of the question anatomy;
       sibling of KnowledgeQuestion.v / KnowledgeQuestionPath.v)

    Elements: the six domains D1..D6; the steps of the path (build, select,
              verify — replicated from KnowledgeQuestionPath.v); the goal
              kinds and closers (replicated from KnowledgeQuestion.v); the
              subject of a domain (the world / the path itself).
    Roles:    D1 recognition and D2 clarification BUILD (material and
              categories; the goals of questions are formed in D2); D3 frame,
              D4 comparison and D5 conclusion SELECT (criterion -> candidates
              -> choice); D6 reflection VERIFIES — the polar closure.
    Rules:    the cycle is monotone over the path (it never steps back);
              compressed, it IS the full path exactly; the decision enters
              reasoning exactly once — at the frame (the unique selective
              leading question, closed by the will); the verification is
              unique and last (the invariant of polar closure); the goals
              are formed strictly before every choosing domain; reflection
              is the unique change of subject — the path itself watched.
    Status:   ties the three files of the question branch into one system:
              the same steps, kinds and closers, now indexed by the domains.
    STATUS: 16 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: July 2026

    ============================== E/R/R razbor ==============================
    Rules: the correspondence is FORCED by the adjudicated canon (MP-6z: the
      cores of the domains drive the steps; V26: service questions are domain
      questions; V30: the root step is the motion along the grounds), not
      chosen: permuting any cell breaks a theorem below.
    Roles: stage_of, leading_kind, subject_of are total decidable maps —
      every domain carries exactly one stage, one leading kind, one subject.
    Elements: finite enumerations only (P4).
    P4 diagnostic (could it be otherwise?): a cycle stepping back over the
      stages would contradict the order of dependence; two selective leading
      questions would let the decision enter twice — the frame would lose
      its office; a verifier before the end would close an unwalked path. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* ---------- the six domains ---------- *)

Inductive Domain := D1 | D2 | D3 | D4 | D5 | D6.

Definition dom_index (d : Domain) : nat :=
  match d with D1 => 1 | D2 => 2 | D3 => 3 | D4 => 4 | D5 => 5 | D6 => 6 end.

Definition all_domains : list Domain := [D1; D2; D3; D4; D5; D6].

(* ---------- the steps of the path (replicated from KnowledgeQuestionPath.v) ---------- *)

Inductive Step := SBuild | SSelect | SVerify.

Definition step_eqb (a b : Step) : bool :=
  match a, b with
  | SBuild, SBuild | SSelect, SSelect | SVerify, SVerify => true
  | _, _ => false
  end.

Definition full_path : list Step := [SBuild; SSelect; SVerify].

Definition stage_of (d : Domain) : Step :=
  match d with
  | D1 | D2 => SBuild
  | D3 | D4 | D5 => SSelect
  | D6 => SVerify
  end.

Definition stage_rank (s : Step) : nat :=
  match s with SBuild => 0 | SSelect => 1 | SVerify => 2 end.

(* the cycle never steps back over the path *)
Theorem cycle_monotone :
  forall a b, dom_index a <= dom_index b ->
    stage_rank (stage_of a) <= stage_rank (stage_of b).
Proof. intros a b H; destruct a, b; simpl in *; lia. Qed.

(* every step of the path is carried by some domain *)
Theorem stages_covered : forall s, exists d, stage_of d = s.
Proof.
  intro s; destruct s; [exists D1 | exists D3 | exists D6]; reflexivity.
Qed.

(* compressed, the domain cycle IS the full path — no gap, no return *)
Fixpoint dedup (l : list Step) : list Step :=
  match l with
  | [] => []
  | s :: r =>
      match r with
      | [] => [s]
      | s' :: _ => if step_eqb s s' then dedup r else s :: dedup r
      end
  end.

Theorem cycle_is_full_path :
  dedup (map stage_of all_domains) = full_path.
Proof. reflexivity. Qed.

(* the build phase precedes every choice, the choice precedes the check *)
Theorem build_before_select :
  forall a b, stage_of a = SBuild -> stage_of b = SSelect ->
    dom_index a < dom_index b.
Proof.
  intros a b Ha Hb; destruct a; try discriminate Ha;
  destruct b; try discriminate Hb; simpl; lia.
Qed.

Theorem select_before_verify :
  forall a b, stage_of a = SSelect -> stage_of b = SVerify ->
    dom_index a < dom_index b.
Proof.
  intros a b Ha Hb; destruct a; try discriminate Ha;
  destruct b; try discriminate Hb; simpl; lia.
Qed.

(* ---------- leading questions on the goal axis (replicated kinds) ---------- *)

Inductive GoalKind := CPolar | CSelective | CFilling.

Definition leading_kind (d : Domain) : GoalKind :=
  match d with
  | D3 => CSelective   (* through what to look? — the question of DECISION *)
  | D6 => CPolar       (* was it right? — the polar check of the path *)
  | _ => CFilling
  end.

(* the decision enters reasoning exactly once — at the frame *)
Theorem unique_decision_domain :
  forall d, leading_kind d = CSelective <-> d = D3.
Proof.
  intro d; destruct d; split; intro H;
  first [ reflexivity | discriminate H ].
Qed.

(* the polar leading question belongs to reflection alone *)
Theorem polar_only_reflection :
  forall d, leading_kind d = CPolar <-> d = D6.
Proof.
  intro d; destruct d; split; intro H;
  first [ reflexivity | discriminate H ].
Qed.

(* all three kinds of goal are present among the leading questions *)
Theorem leading_kinds_covered : forall k, exists d, leading_kind d = k.
Proof.
  intro k; destruct k; [exists D6 | exists D3 | exists D1]; reflexivity.
Qed.

(* ---------- closers (replicated from KnowledgeQuestion.v) ---------- *)

Inductive Closer := ByWitness | ByWill | ByActualization.

Definition closes (k : GoalKind) : Closer :=
  match k with
  | CPolar => ByWitness | CSelective => ByWill | CFilling => ByActualization
  end.

(* the frame is closed by the will: the first question of decision *)
Theorem will_closes_frame : closes (leading_kind D3) = ByWill.
Proof. reflexivity. Qed.

(* the reflection is closed by the witness: the constatation of the path *)
Theorem witness_closes_reflection : closes (leading_kind D6) = ByWitness.
Proof. reflexivity. Qed.

(* ---------- the verification is unique and last ---------- *)

Theorem unique_verifier : forall d, stage_of d = SVerify <-> d = D6.
Proof.
  intro d; destruct d; split; intro H;
  first [ reflexivity | discriminate H ].
Qed.

Theorem verifier_is_last : forall d, dom_index d <= dom_index D6.
Proof. intro d; destruct d; simpl; lia. Qed.

(* ---------- the goals are formed before the choice (D2 before D3..D5) ---------- *)

Theorem goals_before_choice : dom_index D2 < dom_index D3.
Proof. simpl; lia. Qed.

Theorem goals_before_every_choice :
  forall d, stage_of d = SSelect -> dom_index D2 < dom_index d.
Proof.
  intro d; destruct d; intro H; try discriminate H; simpl; lia.
Qed.

(* ---------- reflection: the unique change of subject ---------- *)

Inductive Subject := SubjWorld | SubjPath.

Definition subject_of (d : Domain) : Subject :=
  match d with D6 => SubjPath | _ => SubjWorld end.

Theorem unique_reflexive : forall d, subject_of d = SubjPath <-> d = D6.
Proof.
  intro d; destruct d; split; intro H;
  first [ reflexivity | discriminate H ].
Qed.

(* the world is watched before the path is *)
Theorem world_before_path :
  forall a b, subject_of a = SubjPath -> subject_of b = SubjWorld ->
    dom_index b < dom_index a.
Proof.
  intros a b Ha Hb; destruct a; try discriminate Ha;
  destruct b; try discriminate Hb; simpl; lia.
Qed.
