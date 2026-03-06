(* ========================================================================= *)
(*                  GENERAL PROCESS THEORY                                 *)
(*                                                                          *)
(*  Part of: Theory of Systems — Coq Formalization                         *)
(*                                                                          *)
(*  A Process in ToS is a step-indexed computation (P4: always finite).    *)
(*  Core_ERR.v instantiates Process for specific systems.                  *)
(*  CauchyReal.v instantiates it for Q.                                    *)
(*  This file provides the GENERAL theory over arbitrary types.            *)
(*                                                                          *)
(*  GenProcess A := nat -> A                                               *)
(*    - Observation, prefix, map                                           *)
(*    - Equivalence, monotonicity, Cauchy property                         *)
(*    - Connection to CauchySeq                                            *)
(*                                                                          *)
(*  STATUS: 16 Qed, 0 Admitted, 0 axioms                                  *)
(*  Author: Horsocrates | Date: March 2026                                  *)
(* ========================================================================= *)

Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lqa.
Import ListNotations.

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import CauchyReal.

Open Scope Q_scope.

(* ========================================================================= *)
(*                   PART I: GENERAL PROCESS DEFINITION                    *)
(* ========================================================================= *)

(**
  GENERAL PROCESS
  =================

  A process over type A is a step-indexed computation: nat -> A.
  This is the most general form — no constraints on steps.

  Core_ERR.v's Process record adds system context and finite depth (P4).
  Here we work with the raw computation.
*)

(** General process: step-indexed computation over any type *)
Definition GenProcess (A : Type) := nat -> A.

(** Observation: read the value at step n *)
Definition observe {A : Type} (p : GenProcess A) (n : nat) : A := p n.

(** Prefix: collect the first n values into a list *)
Fixpoint prefix {A : Type} (p : GenProcess A) (n : nat) : list A :=
  match n with
  | O => []
  | S k => prefix p k ++ [p k]
  end.

(** Process map: apply a function to every step *)
Definition process_map {A B : Type} (f : A -> B) (p : GenProcess A) : GenProcess B :=
  fun n => f (p n).

(** Constant process: same value at every step *)
Definition const_process {A : Type} (a : A) : GenProcess A :=
  fun _ => a.

(* ========================================================================= *)
(*                   PART II: PREFIX PROPERTIES                            *)
(* ========================================================================= *)

(**
  PREFIX THEOREMS
  =================

  The prefix function collects the first n values of a process.
  Key properties: length = n, and nth access.
*)

(** Prefix has the expected length *)
Lemma prefix_length :
  forall (A : Type) (p : GenProcess A) (n : nat),
    length (prefix p n) = n.
Proof.
  intros A p n. induction n as [|k IH].
  - simpl. reflexivity.
  - simpl. rewrite app_length. simpl. rewrite IH. lia.
Qed.

(** Prefix preserves order: the k-th element of prefix is p(k) *)
Lemma prefix_nth :
  forall (A : Type) (p : GenProcess A) (n k : nat) (d : A),
    (k < n)%nat ->
    nth k (prefix p n) d = p k.
Proof.
  intros A p n. induction n as [|n' IH]; intros k d Hk.
  - lia.
  - simpl. destruct (Nat.lt_ge_cases k n') as [Hlt | Hge].
    + rewrite app_nth1 by (rewrite prefix_length; lia).
      apply IH. exact Hlt.
    + assert (Heq : k = n') by lia. subst k.
      rewrite app_nth2 by (rewrite prefix_length; lia).
      rewrite prefix_length. replace (n' - n')%nat with 0%nat by lia.
      simpl. reflexivity.
Qed.

(* ========================================================================= *)
(*                   PART III: PROCESS EQUIVALENCE                         *)
(* ========================================================================= *)

(**
  PROCESS EQUIVALENCE
  =====================

  Two processes are equivalent when they agree at every step,
  according to a given equivalence relation on A.
*)

(** Process equivalence: pointwise agreement *)
Definition process_equiv {A : Type} (eq_A : A -> A -> Prop)
    (p1 p2 : GenProcess A) : Prop :=
  forall n : nat, eq_A (p1 n) (p2 n).

(** Reflexivity (given reflexive eq_A) *)
Lemma process_equiv_refl :
  forall (A : Type) (eq_A : A -> A -> Prop),
    (forall a, eq_A a a) ->
    forall (p : GenProcess A), process_equiv eq_A p p.
Proof.
  intros A eq_A Hrefl p n. apply Hrefl.
Qed.

(** Symmetry (given symmetric eq_A) *)
Lemma process_equiv_sym :
  forall (A : Type) (eq_A : A -> A -> Prop),
    (forall a b, eq_A a b -> eq_A b a) ->
    forall (p1 p2 : GenProcess A),
      process_equiv eq_A p1 p2 -> process_equiv eq_A p2 p1.
Proof.
  intros A eq_A Hsym p1 p2 H n. apply Hsym. apply H.
Qed.

(** Transitivity (given transitive eq_A) *)
Lemma process_equiv_trans :
  forall (A : Type) (eq_A : A -> A -> Prop),
    (forall a b c, eq_A a b -> eq_A b c -> eq_A a c) ->
    forall (p1 p2 p3 : GenProcess A),
      process_equiv eq_A p1 p2 ->
      process_equiv eq_A p2 p3 ->
      process_equiv eq_A p1 p3.
Proof.
  intros A eq_A Htrans p1 p2 p3 H12 H23 n.
  apply (Htrans _ (p2 n)).
  - apply H12.
  - apply H23.
Qed.

(** Map preserves equivalence *)
Lemma process_map_equiv :
  forall (A B : Type) (eq_A : A -> A -> Prop) (eq_B : B -> B -> Prop)
         (f : A -> B),
    (forall a1 a2, eq_A a1 a2 -> eq_B (f a1) (f a2)) ->
    forall (p1 p2 : GenProcess A),
      process_equiv eq_A p1 p2 ->
      process_equiv eq_B (process_map f p1) (process_map f p2).
Proof.
  intros A B eq_A eq_B f Hf p1 p2 Heq n.
  unfold process_map. apply Hf. apply Heq.
Qed.

(* ========================================================================= *)
(*                   PART IV: CAUCHY PROPERTY                              *)
(* ========================================================================= *)

(**
  GENERAL CAUCHY PROPERTY
  ========================

  A process is Cauchy when its values eventually stabilize:
  for any ε > 0, there exists N such that for all m, n > N,
  dist(p(m), p(n)) < ε.

  This generalizes CauchyReal.v's is_cauchy from Q to any type
  equipped with a distance function.
*)

(** General Cauchy property with respect to a distance function *)
Definition is_cauchy_gen {A : Type} (dist : A -> A -> Q)
    (p : GenProcess A) : Prop :=
  forall eps : Q, 0 < eps ->
    exists N : nat, forall m n : nat,
      (N <= m)%nat -> (N <= n)%nat -> dist (p m) (p n) < eps.

(** Monotone process *)
Definition gen_monotone {A : Type} (le : A -> A -> Prop)
    (p : GenProcess A) : Prop :=
  forall n : nat, le (p n) (p (S n)).

(* ========================================================================= *)
(*                   PART V: CONNECTION TO CAUCHYREAL                      *)
(* ========================================================================= *)

(**
  CAUCHYSEQ AS SPECIAL CASE
  ===========================

  CauchyReal.v defines:
    is_cauchy (a : nat -> Q) :=
      forall eps > 0, exists N, forall m n >= N, |a(m) - a(n)| < eps

  This is exactly is_cauchy_gen with dist = fun x y => Qabs (x - y).
*)

(** The standard Q distance: |x - y| *)
Definition Qdist (x y : Q) : Q := Qabs (x - y).

(** CauchyReal.is_cauchy ↔ is_cauchy_gen Qdist *)
Lemma cauchy_Q_equiv :
  forall (a : nat -> Q),
    is_cauchy a <-> is_cauchy_gen Qdist a.
Proof.
  intro a. unfold is_cauchy, is_cauchy_gen, Qdist. reflexivity.
Qed.

(** A CauchySeq is a GenProcess Q that satisfies the Cauchy property *)
Lemma cauchy_seq_is_gen_process :
  forall (cs : CauchySeq),
    is_cauchy_gen Qdist (cs_seq cs).
Proof.
  intro cs. apply cauchy_Q_equiv. exact (cs_cauchy cs).
Qed.

(** Constant processes are trivially Cauchy *)
Lemma const_process_cauchy :
  forall {A : Type} (dist : A -> A -> Q) (a : A),
    dist a a == 0 ->
    is_cauchy_gen dist (const_process a).
Proof.
  intros A dist a Hzero eps Heps.
  exists 0%nat. intros m n _ _.
  unfold const_process. lra.
Qed.

(** Map preserves Cauchy under non-expansive condition *)
Lemma process_map_cauchy :
  forall (A B : Type) (distA : A -> A -> Q) (distB : B -> B -> Q)
         (f : A -> B),
    (forall a1 a2, distB (f a1) (f a2) <= distA a1 a2) ->
    forall (p : GenProcess A),
      is_cauchy_gen distA p ->
      is_cauchy_gen distB (process_map f p).
Proof.
  intros A B distA distB f Hne p Hcauchy eps Heps.
  destruct (Hcauchy eps Heps) as [N HN].
  exists N. intros m n Hm Hn.
  unfold process_map.
  apply Qle_lt_trans with (distA (p m) (p n)).
  - apply Hne.
  - apply HN; assumption.
Qed.

(* ========================================================================= *)
(*                   PART VI: ADDITIONAL PROPERTIES                        *)
(* ========================================================================= *)

(**
  COMPOSITION, IDENTITY, AND STRUCTURAL THEOREMS
  =================================================

  Further properties of general processes.
*)

(** Process map composition: map f (map g p) = map (f ∘ g) p *)
Lemma process_map_compose :
  forall (A B C : Type) (f : B -> C) (g : A -> B) (p : GenProcess A) (n : nat),
    process_map f (process_map g p) n = process_map (fun x => f (g x)) p n.
Proof.
  intros. unfold process_map. reflexivity.
Qed.

(** Process map identity: map id p = p *)
Lemma process_map_id :
  forall (A : Type) (p : GenProcess A) (n : nat),
    process_map (fun x => x) p n = p n.
Proof.
  intros. unfold process_map. reflexivity.
Qed.

(** Observation agrees with prefix *)
Lemma observe_in_prefix :
  forall (A : Type) (p : GenProcess A) (k n : nat) (d : A),
    (k < n)%nat ->
    observe p k = nth k (prefix p n) d.
Proof.
  intros A p k n d Hk. unfold observe.
  symmetry. apply prefix_nth. exact Hk.
Qed.

(** Monotone: direct accessor *)
Lemma monotone_shift :
  forall (A : Type) (le : A -> A -> Prop) (p : GenProcess A),
    gen_monotone le p ->
    forall n : nat, le (p n) (p (S n)).
Proof.
  intros A le p Hmon n. exact (Hmon n).
Qed.

(** Constant process equivalence *)
Lemma const_process_equiv :
  forall (A : Type) (eq_A : A -> A -> Prop) (a : A),
    (forall x, eq_A x x) ->
    process_equiv eq_A (const_process a) (const_process a).
Proof.
  intros A eq_A a Hrefl n. unfold const_process. apply Hrefl.
Qed.

(** Prefix of constant process *)
Lemma prefix_const :
  forall (A : Type) (a : A) (n : nat) (k : nat) (d : A),
    (k < n)%nat ->
    nth k (prefix (const_process a) n) d = a.
Proof.
  intros A a n k d Hk.
  rewrite prefix_nth by exact Hk.
  unfold const_process. reflexivity.
Qed.

(* ========================================================================= *)
(*                   SUMMARY                                                *)
(* ========================================================================= *)

(**
  PROVEN (16 Qed):

  Part II  — Prefix properties:
    prefix_length, prefix_nth

  Part III — Process equivalence:
    process_equiv_refl, process_equiv_sym, process_equiv_trans,
    process_map_equiv

  Part V   — Connection to CauchyReal:
    cauchy_Q_equiv, cauchy_seq_is_gen_process,
    const_process_cauchy, process_map_cauchy

  Part VI  — Additional properties:
    process_map_compose, process_map_id, observe_in_prefix,
    monotone_shift, const_process_equiv, prefix_const

  KEY INSIGHTS:
  1. GenProcess A = nat -> A is the universal process type
  2. All specific processes (Process, CauchySeq) are special cases
  3. prefix collects finite observations (P4 compatibility)
  4. is_cauchy_gen abstracts CauchyReal's is_cauchy to any metric
  5. Map preserves equivalence and Cauchy under appropriate conditions

  AXIOMS: 0 (all proofs constructive)
*)

Print Assumptions prefix_nth.
Print Assumptions process_map_equiv.
Print Assumptions process_map_cauchy.
