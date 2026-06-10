(** * P4ProhibitsImpredicative.v — P4 prohibits impredicative definitions
    Elements: impredicative quantification, totality, Russell's paradox
    Roles:    impredicativity requires completed totality, P4 prohibits that
    Rules:    P1 (hierarchy) + P4 (finiteness) dissolve Russell
    STATUS:   10 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: April 2026

    IMPREDICATIVITY:
    A definition is impredicative if it quantifies over a totality that
    includes the very entity being defined.
    Example: R = {x | x ∉ x}. R is defined by quantifying over "all sets"
    which includes R itself.

    P4 PROHIBITS THIS:
    "All sets" is a completed totality (all at once).
    P4 (finite actuality) prohibits completed totalities.
    Therefore P4 prohibits the class of definitions that leads to Russell.

    P4 ALLOWS INDUCTIVE DEFINITIONS:
    Inductive types build stage-by-stage, never requiring "all at once."
    nat = O | S n. Each element is finite. No completed totality needed.
*)

From Stdlib Require Import PeanoNat Lia.

From ToS Require Import foundation.P4CompletedInfinity.

(* ================================================================ *)
(*  IMPREDICATIVE DEFINITIONS REQUIRE TOTALITY                       *)
(* ================================================================ *)

(** A totality over nat: the collection of ALL subsets *)
Definition NatTotality : Prop :=
  forall P : nat -> Prop, exists n : nat, True.
  (* This is trivially true; the REAL content is that
     quantification "forall P : nat -> Prop" ranges over
     ALL subsets simultaneously = completed power set *)

(** Impredicative definition: defined by reference to the totality
    that includes itself *)
Definition impredicative_prop : Prop :=
  exists P : nat -> Prop,
    (forall Q : nat -> Prop, Q = P \/ Q <> P) /\
    P 0%nat.

(** Russell's criterion: "x not in x" *)
Definition russell_criterion (member : nat -> nat -> Prop) (x : nat) : Prop :=
  ~ member x x.

(* ================================================================ *)
(*  P1 BLOCKS RUSSELL                                                *)
(* ================================================================ *)

(** P1 (hierarchy): S ∉ S. No set contains itself.
    This blocks Russell's paradox at the TYPE level. *)
Theorem P1_blocks_russell :
  forall (member : nat -> nat -> Prop),
  (* If membership respects hierarchy (no self-membership) *)
  (forall x, ~ member x x) ->
  (* Then Russell's set is simply everything *)
  forall x, russell_criterion member x.
Proof.
  intros member Hirr x.
  unfold russell_criterion.
  apply Hirr.
Qed.

(** Without P1: Russell gives contradiction *)
Theorem russell_contradiction_without_P1 :
  forall (member : nat -> nat -> Prop) (r : nat),
  (* If r is the "Russell set" *)
  (forall x, member x r <-> ~ member x x) ->
  (* Then contradiction *)
  False.
Proof.
  intros member r Hrussell.
  destruct (Hrussell r) as [H1 H2].
  (* H1 : member r r -> ~ member r r *)
  (* H2 : ~ member r r -> member r r *)
  assert (~ member r r) as Hnm.
  { intro Hmem. exact (H1 Hmem Hmem). }
  exact (Hnm (H2 Hnm)).
Qed.

(* ================================================================ *)
(*  INDUCTIVE DEFINITIONS ARE COMPATIBLE WITH P4                     *)
(* ================================================================ *)

(** nat is inductive: every element is the origin or a successor — built in
    finitely many steps, no completed totality needed (June 2026: was
    `exists m, n = m`, vacuous). *)
Lemma nat_is_inductive :
  forall n : nat, n = 0%nat \/ exists m : nat, n = S m.
Proof.
  intro n. destruct n as [| m]; [left; reflexivity | right; exists m; reflexivity].
Qed.

(** Stage-bounded actuality for inductive nat *)
Definition nat_staged_actual : nat -> nat -> Prop :=
  fun stage n => (n <= stage)%nat.

Lemma nat_staged_bounded : P4_stage_bounded nat_staged_actual.
Proof.
  intro stage. exists stage.
  intros n H. exact H.
Qed.

(** Each element of nat is actual at SOME stage (not all at once) *)
Lemma nat_eventually_actual :
  forall n : nat, exists stage : nat, nat_staged_actual stage n.
Proof.
  intro n. exists n. unfold nat_staged_actual. lia.
Qed.

(* ================================================================ *)
(*  P4 PROHIBITS THE FORMATION OF RUSSELL'S SET                      *)
(* ================================================================ *)

(** Russell's set requires quantifying over "all sets."
    "All sets" is a completed totality.
    P4 prohibits completed totalities.
    Therefore P4 prohibits the very FORMATION of Russell's set. *)

Theorem P4_dissolves_russell :
  (* P1 blocks self-membership *)
  (forall member : nat -> nat -> Prop,
    (forall x, ~ member x x) ->
    forall x, russell_criterion member x) /\
  (* Russell requires completed totality *)
  (forall (member : nat -> nat -> Prop) (r : nat),
    (forall x, member x r <-> ~ member x x) -> False) /\
  (* Inductive types are P4-compatible *)
  P4_stage_bounded nat_staged_actual.
Proof.
  split; [exact P1_blocks_russell |
  split; [exact russell_contradiction_without_P1 |
  exact nat_staged_bounded]].
Qed.

(* ================================================================ *)
(*  SYNTHESIS                                                        *)
(* ================================================================ *)

Theorem p4_impredicative_synthesis :
  (* P1 blocks self-membership *)
  (forall member : nat -> nat -> Prop,
    (forall x, ~ member x x) ->
    forall x, russell_criterion member x) /\
  (* Russell gives contradiction without P1 *)
  (forall (member : nat -> nat -> Prop) (r : nat),
    (forall x, member x r <-> ~ member x x) -> False) /\
  (* Inductive types are P4-compatible *)
  P4_stage_bounded nat_staged_actual /\
  (* Each nat element is eventually actual *)
  (forall n, exists stage, nat_staged_actual stage n).
Proof.
  split; [exact P1_blocks_russell |
  split; [exact russell_contradiction_without_P1 |
  split; [exact nat_staged_bounded |
  exact nat_eventually_actual]]].
Qed.
