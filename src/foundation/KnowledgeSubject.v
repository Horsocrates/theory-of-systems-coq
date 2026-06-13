(** * KnowledgeSubject.v — the knowing SUBJECT: the witness-ROLE a system occupies relative to a
      knowable, its constitutive core (E/R/R + P4), and the inside-limit on self-knowing

    Built on the AUTHOR'S theory of the subject (2026-06-13):

      (1) The subject is the ROLE of observer = the knower: the POSITION of a knowing-system relative
          to a known-system.  When the knower knows ITSELF it is INSIDE the system, which structurally
          limits knowing-oneself-as-a-system-from-outside.
      (3) Knower--knowable is a RELATION between two systems.  Knowability is given as a POSSIBILITY
          (the existing is knowable) for knowing by a witness; actual knowing ACTUALIZES it.
      (4) The subject's boundary IS the boundary of the subject-system: core = critical roles/elements
          (for existence), extended = optional roles/elements, all belonging to ONE system.
          Instruments are OTHER systems.
      (5) The essence is what makes A = A and stays unchanged in any form of A.
      Honesty: keep the theory STRUCTURAL (it will develop with the metaphysics).

    Forks (4) and (5) are EXACTLY KnowledgeMutability applied to the subject-as-a-system A (core =
    critical = the invariant; extended = optional = the variant; identity = the essence) — cited, not
    re-proved.  This file proves what is NEW: the subject is a positional ROLE; its constitutive core
    is the E/R/R + P4 of a knower; self-knowing has no external (outside) view by itself; and
    knowability (possibility) is not being-known (actuality).

    ============================== E/R/R разбор (the constitutive core) ==============================
    Rules (the generative rule first):
      R-relation (fork 3): knowing is a RELATION between two systems; knowability is the standing
                 POSSIBILITY of the existing, actual knowing is its ACTUALIZATION by a witness — the
                 subject is the actualizer-pole.
      R-finitude (P4): the knower is a FINITE actuality => finite attention (R3, one focus per step)
                 is constitutive.
      R-inside (fork 1): in self-knowing knower = known => the knower is INSIDE => no external view of
                 itself by itself (the outside view needs another system).
    Roles (L4): the subject = the witness-POSITION relative to a knowable (positional, NOT a kind);
      the knowable = the source-pole (a possibility).
    Elements (L1+P4): the resolved distinction (the unit held) — needs distinction-resolution and a
      threshold >= 1.
    The constitutive core = E/R/R + P4 of the knower:
      Element: resolve and hold a distinction (resolves + threshold >= 1);
      Role:    at least one channel (the witness-meeting that instantiates the relation);
      Rule:    finite attention (the P4 finitude of the knower).
      Contingent (a richer subject, NOT constitutive): reflection, the ЗДО-grading faculty,
      accumulation-record beyond the hold, specific channels / instruments.
    P4 diagnostic (could it be otherwise?):
      The core is FORCED — no knower lacks distinction-resolution, a channel, a hold, or finite
      attention; the extras are not (a minimal subject neither reflects nor grades ground).
      Self-knowing is bounded (inside => no outside self-view).  Knowability (possibility, with
      existence) is not being-known (actuality, needs a witness).
    Honesty wall:
      STRUCTURAL only — the formal subject = the witness-pole with capacities; the phenomenal
      "for-whom" / qualia is OUT of scope (to develop with the metaphysics).  Forks (4) boundary and
      (5) identity = KnowledgeMutability applied to the subject (cited).

    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import PeanoNat Lia.

(* ===================================================================== *)
(*  PART I — the subject as a positional ROLE; the constitutive core       *)
(* ===================================================================== *)

Section Subject.
Context {Sys : Type}.
Variable knows     : Sys -> Sys -> Prop.   (* S (as witness) knows O *)
Variable resolves  : Sys -> Prop.           (* can resolve a distinction (the act of knowing) *)
Variable channels  : Sys -> nat.            (* number of channels to meet a knowable *)
Variable threshold : Sys -> nat.            (* capacity to hold a read *)

(** The CONSTITUTIVE core of the knower-role (E/R/R + P4): resolve a distinction (Element), at least
    one channel (Role: the witness-meeting), a threshold >= 1 (hold the read).  Finite attention is
    automatic (the limiter is a nat = the P4 finitude). *)
Definition is_subject (S : Sys) : Prop :=
  resolves S /\ 1 <= channels S /\ 1 <= threshold S.

(** Positions in the knowing relation. *)
Definition is_knower (S : Sys) : Prop := exists O, knows S O.   (* the witness-position *)
Definition is_known  (O : Sys) : Prop := exists S, knows S O.   (* the known-position *)

(** ★ Each core capacity is NECESSARY to be a subject. *)
Theorem subject_needs_resolution : forall S, is_subject S -> resolves S.
Proof. intros S [H _]. exact H. Qed.

Theorem subject_needs_channel : forall S, is_subject S -> 1 <= channels S.
Proof. intros S [_ [H _]]. exact H. Qed.

Theorem subject_needs_threshold : forall S, is_subject S -> 1 <= threshold S.
Proof. intros S [_ [_ H]]. exact H. Qed.

(** ★ Subjecthood is POSITIONAL (fork 1): to be a subject is to occupy the knower-position in some
    relation — not to be a special kind. *)
Theorem subject_is_positional : forall S, is_knower S <-> exists O, knows S O.
Proof. intros S. unfold is_knower. tauto. Qed.

(** ★ The SAME system can occupy BOTH positions — e.g. in self-knowing it is knower and known of
    itself.  Subject/object is a position, interchangeable. *)
Theorem same_system_both_positions : forall S, knows S S -> is_knower S /\ is_known S.
Proof. intros S H. split; exists S; exact H. Qed.

(* ===================================================================== *)
(*  PART II — the inside-limit on self-knowing (fork 1)                    *)
(* ===================================================================== *)

(** The EXTERNAL (outside) view of O is a knowing of O by a DIFFERENT system. *)
Definition external_view (S O : Sys) : Prop := knows S O /\ S <> O.

(** ★★ Self-knowing has NO external view by itself: when the knower IS the known (S knows S) it is
    INSIDE the system, so the outside view of itself is structurally unavailable.  (fork 1: the
    knower is inside.)  Cf. KnowledgeReflection.no_complete_self_model. *)
Theorem no_external_self_view : forall S, ~ external_view S S.
Proof. intros S [_ Hne]. apply Hne. reflexivity. Qed.

(** ★ The outside view of S requires ANOTHER system (a knower distinct from the known). *)
Theorem external_view_needs_other : forall S O, external_view O S -> O <> S.
Proof. intros S O [_ H]. exact H. Qed.

(* ===================================================================== *)
(*  CAPSTONE (abstract)                                                    *)
(* ===================================================================== *)

(** ★★★ The subject: a positional witness-role whose constitutive core is resolve+channel+threshold;
    the same system can be knower and known (self-knowing); but self-knowing has no external view. *)
Theorem subject_capstone : forall S,
  (is_subject S -> resolves S /\ 1 <= channels S /\ 1 <= threshold S)
  /\ (knows S S -> is_knower S /\ is_known S)
  /\ (~ external_view S S).
Proof.
  intros S. split; [ | split ].
  - intro H. exact H.
  - apply same_system_both_positions.
  - apply no_external_self_view.
Qed.

End Subject.

(* ===================================================================== *)
(*  PART III — a concrete world: a minimal subject (no reflection), and    *)
(*  knowability (possibility) =/= being-known (actuality) (fork 3)         *)
(*  system 0 = a minimal subject; system 1 = an existing knowable nobody    *)
(*  knows                                                                   *)
(* ===================================================================== *)

Definition c_resolves  (n : nat) : Prop := n = 0.
Definition c_channels  (n : nat) : nat  := match n with O => 1 | _ => 0 end.
Definition c_threshold (n : nat) : nat  := match n with O => 1 | _ => 0 end.
Definition c_reflects  (n : nat) : Prop := False.                 (* nobody reflects *)
Definition c_existing  (n : nat) : Prop := n = 0 \/ n = 1.
Definition c_knowable  (n : nat) : Prop := c_existing n.          (* the existing is knowable *)
Definition c_knows     (a b : nat) : Prop := a = 0 /\ b = 0.      (* 0 knows itself; nobody knows 1 *)

(** ★★ A MINIMAL subject (system 0) has the constitutive core but does NOT reflect — reflection is
    contingent, not constitutive. *)
Theorem minimal_subject_without_reflection :
  is_subject c_resolves c_channels c_threshold 0 /\ ~ c_reflects 0.
Proof.
  split.
  - unfold is_subject, c_resolves, c_channels, c_threshold.
    split; [ reflexivity | ]. split; simpl; lia.
  - unfold c_reflects. intro H. exact H.
Qed.

(** ★ Self-knowing instance (system 0 knows itself) — the positional witness: 0 is both knower and
    known of itself. *)
Theorem self_knowing_witness : c_knows 0 0.
Proof. unfold c_knows. split; reflexivity. Qed.

(** ★★ KNOWABILITY (possibility) is NOT being-known (actuality), fork 3: system 1 EXISTS and is
    KNOWABLE, yet NO subject knows it.  Knowability is given with existence; being-known needs a
    witness. *)
Theorem knowable_not_known_witness :
  c_existing 1 /\ c_knowable 1 /\ ~ (exists S, c_knows S 1).
Proof.
  split; [ right; reflexivity | ].
  split.
  - unfold c_knowable, c_existing. right; reflexivity.
  - intros [S [_ Hb]]. discriminate Hb.
Qed.

Print Assumptions subject_capstone.
Print Assumptions minimal_subject_without_reflection.
Print Assumptions knowable_not_known_witness.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  11 Qed, 0 Admitted, 0 axioms.                                            *)
(*  The knowing SUBJECT = the witness-ROLE a system occupies relative to a    *)
(*  knowable (subject_is_positional; same_system_both_positions — positional, *)
(*  not a kind).  Its CONSTITUTIVE core is the E/R/R + P4 of a knower:        *)
(*  resolve a distinction + threshold >= 1 (Element), >= 1 channel (Role),    *)
(*  finite attention (Rule/P4) - each necessary (the subject_needs lemmas).   *)
(*  Reflection is CONTINGENT (minimal_subject_without_reflection).  Self-     *)
(*  knowing has NO external view by itself (no_external_self_view — the       *)
(*  inside-limit, fork 1).  Knowability (possibility, with existence) is NOT  *)
(*  being-known (actuality, needs a witness): knowable_not_known_witness      *)
(*  (fork 3).  Forks 4 (boundary = system; core/extended) and 5 (identity =   *)
(*  essence) = KnowledgeMutability applied to the subject (cited).  Structural *)
(*  only; the phenomenal "for-whom" is out of scope.  Direction (3).         *)
(* ========================================================================= *)
