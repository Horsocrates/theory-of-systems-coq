(** * KnowledgeFinitization.v — the LEARNABILITY boundary of the Theory of Knowledge IS the
      FINITIZATION boundary (H1) the project marks across math / physics / CS / information

    The project flag H1: the finitization boundary (Element = finite / terminating / dyadic) vs the
    role-limit (a K->infinity process, never completed) = the constructivity boundary.  This file
    makes EXPLICIT that the Theory-of-Knowledge branch has lived on the SAME boundary throughout:

      * KnowledgeGap: Species I (bounded field -> completes) vs Species II (g>r -> diverges).
      * KnowledgeProcess: forall-exists holds (along the way) / exists-forall fails (completed object).
      * KnowledgeMutability: essence (fixed, a completed object) vs variant (a moving target).
      * KnowledgeShannon: the trit (log2 3 not in Q) is off the dyadic Element skeleton.

    Here they are identified: the LEARNABLE = the Element side (bounded / finite field -> knowledge
    completes); the UNLEARNABLE-AS-TOTALITY = the role-limit side (unbounded / outrunning field ->
    knowledge never completes as an object).  The trit is the concrete role-limit anchor shared with
    the information and mathematics threads.  So: learnability = finitization = constructivity, in
    the EPISTEMIC arena.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      R-finitization (H1): every knowable is either Element-side (bounded/finite field => knowledge
                 COMPLETES) or role-limit-side (unbounded, outrunning => never completes as totality).
      R3/R4 (the race, KnowledgeGap): acquisition rate vs field growth decides the side.
      R-diagonal: the completed totality of an unbounded process is barred (as_object_fails).
    Roles (L4): element_side = the learnable (finite, terminating, dyadic); role_limit_side = the
      unlearnable-as-totality (a K->infinity process); the trit = the concrete role-limit anchor.
    Elements (L1+P4): field, known : nat -> nat; the rates r, g; the process p; the trit (3 configs).
    P4 diagnostic (could it be otherwise?):
      This is the SAME boundary the project marks everywhere (surds, halting, Tsirelson, the trit
      log2 3 not in Q) — here in the epistemic arena.  Element = the completed OBJECT of knowledge
      (knowable as a whole); role-limit = PROCESS knowledge (only along the way) = the essence/variant
      split (KnowledgeMutability).  Bounded => completes; outrunning => diverges (counted,
      KnowledgeGap); the completed totality of an unbounded process is barred by the diagonal.
    Honesty wall:
      This is a SYNTHESIS / observation of H1 class, NOT a new theorem (as H1 is tagged in HIGHLIGHTS).
      The load-bearing results (knowledge_completes_when_bounded, deficit_diverges, as_object_fails,
      log2_3_irrational) are CITED; the contribution is the connective identity
      learnability = finitization = constructivity.  No claim beyond the proven implications — a full
      Element-XOR-role-limit dichotomy would need L3 and is NOT asserted (only the two implications
      and the disjointness sides_exclusive).

    STATUS: 6 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import PeanoNat Lia.
From ToS Require Import foundation.KnowledgeGap.       (* knowledge_completes_when_bounded, deficit_diverges, field_ge_linear *)
From ToS Require Import foundation.KnowledgeProcess.   (* GenProcess, known_as_object, as_object_fails *)
From ToS Require Import stdlib.DyadicBits.             (* log2_3_irrational — the role-limit anchor *)

(* ===================================================================== *)
(*  The two sides of H1, in the epistemic arena                            *)
(* ===================================================================== *)

(** Element side: the knowable field is BOUNDED (finite). *)
Definition element_side (field : nat -> nat) : Prop := exists Fcap, forall n, field n <= Fcap.

(** Role-limit side: the field OUTRUNS acquisition (grows >= g/step, acquired <= r/step, r < g). *)
Definition role_limit_side (field known : nat -> nat) (r g : nat) : Prop :=
  (forall n, known (S n) <= known n + r) /\ (forall n, field n + g <= field (S n)) /\ r < g.

(** Learnable: knowledge completes (catches the field). *)
Definition learnable (field known : nat -> nat) : Prop := exists N, field N <= known N.

(** Unlearnable as a totality: the deficit diverges (never a completed object). *)
Definition unlearnable_as_totality (field known : nat -> nat) : Prop :=
  forall B, exists n, known n + B < field n.

(* ===================================================================== *)
(*  The identification: learnability boundary = finitization boundary      *)
(* ===================================================================== *)

(** ★ ELEMENT side => LEARNABLE: a bounded (finite) knowable with steady acquisition COMPLETES.
    (= KnowledgeGap.knowledge_completes_when_bounded, Species I.) *)
Theorem element_side_learnable : forall field known,
  element_side field -> (forall n, n <= known n) -> learnable field known.
Proof.
  intros field known [Fcap Hb] Hs. unfold learnable.
  apply (knowledge_completes_when_bounded field known Fcap Hb Hs).
Qed.

(** ★ ROLE-LIMIT side => UNLEARNABLE as a totality: an outrunning field DIVERGES.
    (= KnowledgeGap.deficit_diverges, Species II.) *)
Theorem role_limit_unlearnable : forall field known r g,
  role_limit_side field known r g -> known 0 <= field 0 -> unlearnable_as_totality field known.
Proof.
  intros field known r g [Hacq [Hfg Hrg]] H0. unfold unlearnable_as_totality.
  apply (deficit_diverges field known r g Hacq Hfg Hrg H0).
Qed.

(** ★ The two sides are DISJOINT: a bounded field cannot also outrun acquisition unboundedly. *)
Theorem sides_exclusive : forall field known r g,
  element_side field -> role_limit_side field known r g -> False.
Proof.
  intros field known r g [Fcap Hb] [_ [Hfg Hrg]].
  pose proof (field_ge_linear field g Hfg (S Fcap)) as Hf.
  pose proof (Hb (S Fcap)) as Hbn.
  assert (Hg1 : 1 <= g) by lia.
  nia.
Qed.

(** ★ The completed TOTALITY of knowledge of an unbounded process is a role-limit — it never exists
    as an object (= KnowledgeProcess.as_object_fails, the diagonal). *)
Theorem totality_is_role_limit : forall (A : Type) (p : GenProcess A), ~ known_as_object p.
Proof. intros A p. apply as_object_fails. Qed.

(** ★ The concrete role-limit anchor shared with the information and mathematics threads: a TRIT
    (3 equally-likely configurations) is off the dyadic Element skeleton — no whole number of binary
    distinctions yields it (= DyadicBits.log2_3_irrational). *)
Theorem trit_is_role_limit : ~ (exists n, (2 ^ n)%nat = 3%nat).
Proof.
  intros [n H]. apply log2_3_irrational. exists n, 1%nat. split; [ lia | ].
  simpl. exact H.
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ The learnability boundary IS the finitization boundary (H1), in the epistemic arena:
    Element-side (bounded) knowledge COMPLETES; role-limit-side (outrunning) knowledge DIVERGES; the
    completed totality of an unbounded process never exists (the diagonal); and the trit is the
    concrete role-limit anchor.  Learnability = finitization = constructivity. *)
Theorem learnability_is_finitization :
  (forall field known, element_side field -> (forall n, n <= known n) -> learnable field known)
  /\ (forall field known r g, role_limit_side field known r g -> known 0 <= field 0 ->
        unlearnable_as_totality field known)
  /\ (forall (A : Type) (p : GenProcess A), ~ known_as_object p)
  /\ (~ exists n, (2 ^ n)%nat = 3%nat).
Proof.
  split; [ exact element_side_learnable | ].
  split; [ exact role_limit_unlearnable | ].
  split; [ exact totality_is_role_limit | exact trit_is_role_limit ].
Qed.

Print Assumptions learnability_is_finitization.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  6 Qed, 0 Admitted, 0 axioms.                                             *)
(*  The Theory-of-Knowledge LEARNABILITY boundary = the project's H1          *)
(*  FINITIZATION boundary, in the epistemic arena: Element-side / bounded     *)
(*  field => knowledge COMPLETES (element_side_learnable, Species I);         *)
(*  role-limit-side / outrunning field => DIVERGES (role_limit_unlearnable,   *)
(*  Species II); the two sides are disjoint (sides_exclusive); the completed  *)
(*  totality of an unbounded process never exists (totality_is_role_limit =   *)
(*  as_object_fails, the diagonal); the trit is the concrete role-limit       *)
(*  anchor (trit_is_role_limit = log2_3_irrational).  Synthesis (H1 class),   *)
(*  not a new theorem; machinery cited from KnowledgeGap / KnowledgeProcess / *)
(*  DyadicBits.  Learnability = finitization = constructivity.               *)
(* ========================================================================= *)
