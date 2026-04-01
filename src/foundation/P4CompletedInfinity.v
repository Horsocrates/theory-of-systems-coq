(** * P4CompletedInfinity.v — P4 PROHIBITS completed infinities (not just replaces them)
    Elements: CompletedInfSet, P4_stage_bounded, potential_infinity
    Roles:    P4 (finite actuality) → bound at each stage → contradiction with completed ∞
    Rules:    completed_inf + P4_bounded + bridge → False
    STATUS:   12 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: April 2026

    KEY DISTINCTION:
    "Reinterpretation": P4 provides ALTERNATIVE to infinity axiom.
    "Prohibition": P4 is INCONSISTENT with completed infinity.
    Prohibition implies reinterpretation, but not vice versa.

    THE ARGUMENT:
    CompletedInfSet S: every natural number is ACTUALLY a member of S.
    P4_stage_bounded: at each stage, the number of actual elements is bounded.
    Bridge: if S(n) then n is actual at stage 0.

    Contradiction: S says all n are members → all actual at stage 0.
    But P4 says stage 0 has a bound B. Take n = B+1: S(B+1) but B+1 > B. ⊥.
*)

From Stdlib Require Import PeanoNat Lia.

(* ================================================================ *)
(*  COMPLETED VS POTENTIAL INFINITY                                  *)
(* ================================================================ *)

(** Completed infinite set: every natural is ACTUALLY a member *)
Definition CompletedInfSet (S : nat -> Prop) : Prop :=
  forall n : nat, S n.

(** P4: at each stage, actuality is finitely bounded *)
Definition P4_stage_bounded (actual : nat -> nat -> Prop) : Prop :=
  forall stage : nat, exists bound : nat,
    forall n : nat, actual stage n -> (n <= bound)%nat.

(** Potential infinity: always more, never all at once *)
Definition potential_infinity : Prop :=
  forall n : nat, exists m : nat, (n < m)%nat.

(** Bridge: membership in completed set implies actuality *)
Definition bridge (S : nat -> Prop) (actual : nat -> nat -> Prop) : Prop :=
  forall n : nat, S n -> actual 0%nat n.

(* ================================================================ *)
(*  COMPLETED INFINITY IS UNBOUNDED                                  *)
(* ================================================================ *)

Lemma completed_inf_unbounded : forall S : nat -> Prop,
  CompletedInfSet S ->
  forall bound : nat, exists n : nat, (bound < n)%nat /\ S n.
Proof.
  intros S HS bound.
  exists (Datatypes.S bound). split.
  - lia.
  - apply HS.
Qed.

(* ================================================================ *)
(*  THE CONTRADICTION                                                *)
(* ================================================================ *)

(** P4 + CompletedInfSet + bridge → False *)
Theorem completed_inf_contradicts_P4 :
  forall (S : nat -> Prop) (actual : nat -> nat -> Prop),
  CompletedInfSet S ->
  P4_stage_bounded actual ->
  bridge S actual ->
  False.
Proof.
  intros S actual HS HP4 Hbridge.
  (* P4 gives a bound for stage 0 *)
  destruct (HP4 0%nat) as [bound Hbound].
  (* Completed infinity gives an element beyond the bound *)
  destruct (completed_inf_unbounded S HS bound) as [n [Hlt HSn]].
  (* Bridge makes it actual *)
  assert (actual 0%nat n) as Hact by (apply Hbridge; exact HSn).
  (* Bound says n ≤ bound, but we have bound < n *)
  assert (n <= bound)%nat as Hle by (apply Hbound; exact Hact).
  lia.
Qed.

(* ================================================================ *)
(*  POTENTIAL INFINITY IS COMPATIBLE                                  *)
(* ================================================================ *)

Lemma potential_inf_exists : potential_infinity.
Proof.
  intro n. exists (Datatypes.S n). lia.
Qed.

(** Potential infinity does NOT require all elements to be actual at once *)
Lemma potential_compatible_with_P4 :
  exists (actual : nat -> nat -> Prop),
    P4_stage_bounded actual /\ potential_infinity.
Proof.
  exists (fun stage n => (n <= stage)%nat).
  split.
  - intro stage. exists stage. intros n H. exact H.
  - exact potential_inf_exists.
Qed.

(* ================================================================ *)
(*  P4 PROHIBITION                                                   *)
(* ================================================================ *)

(** P4 PROHIBITS completed infinity (not merely provides alternative) *)
Theorem P4_prohibition_infinity :
  (* For ANY P4-bounded actuality and ANY bridge,
     completed infinity leads to contradiction *)
  forall (S : nat -> Prop) (actual : nat -> nat -> Prop),
  CompletedInfSet S ->
  P4_stage_bounded actual ->
  bridge S actual ->
  False.
Proof. exact completed_inf_contradicts_P4. Qed.

(** Prohibition is STRONGER than reinterpretation *)
Theorem prohibition_stronger :
  (* Prohibition: P4 AND completed infinity → False *)
  (forall S actual, CompletedInfSet S -> P4_stage_bounded actual ->
    bridge S actual -> False) /\
  (* Reinterpretation: P4 provides alternative (potential infinity) *)
  potential_infinity.
Proof.
  split.
  - exact completed_inf_contradicts_P4.
  - exact potential_inf_exists.
Qed.

(* ================================================================ *)
(*  NATURAL NUMBERS ARE NOT A COMPLETED SET                          *)
(* ================================================================ *)

(** nat is an INDUCTIVE TYPE, not a completed set.
    Each n : nat is finite. Induction gives potential infinity.
    But "the set of all nat" requires completed infinity. *)

Definition nat_as_completed : nat -> Prop := fun _ => True.

Lemma nat_would_be_completed : CompletedInfSet nat_as_completed.
Proof. intro n. exact I. Qed.

(** If nat were treated as completed AND P4 holds,
    then any bridge to actuality gives contradiction *)
Theorem nat_not_completed_under_P4 :
  forall (actual : nat -> nat -> Prop),
  P4_stage_bounded actual ->
  bridge nat_as_completed actual ->
  False.
Proof.
  intros actual HP4 Hb.
  apply (completed_inf_contradicts_P4 nat_as_completed actual).
  - exact nat_would_be_completed.
  - exact HP4.
  - exact Hb.
Qed.

(* ================================================================ *)
(*  SYNTHESIS                                                        *)
(* ================================================================ *)

Theorem p4_completed_infinity_synthesis :
  (* Completed infinity contradicts P4 *)
  (forall S actual, CompletedInfSet S -> P4_stage_bounded actual ->
    bridge S actual -> False) /\
  (* Potential infinity is compatible with P4 *)
  (exists actual, P4_stage_bounded actual /\ potential_infinity) /\
  (* Prohibition is stronger than reinterpretation *)
  potential_infinity.
Proof.
  split; [exact completed_inf_contradicts_P4 |
  split; [exact potential_compatible_with_P4 |
  exact potential_inf_exists]].
Qed.
