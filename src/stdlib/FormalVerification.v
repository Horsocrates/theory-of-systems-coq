(** * FormalVerification.v -- Formal Verification Concepts as ToS Systems

    Theory of Systems -- Verified Standard Library (Batch 6)

    Elements: formulas (inductive type), valuations (nat -> bool)
    Roles:    formula -> Specification, valuation -> Model, checker -> Verifier
    Rules:    satisfaction relation (constitution), model checking
    Status:   verified | counterexample | timeout | unknown

    Connection: Automata.v -- model checking via state exploration

    STATUS: 20 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* ================================================================= *)
(** ** Formulas: propositional logic AST *)
(* ================================================================= *)

Inductive Formula : Set :=
  | FVar   : nat -> Formula
  | FNot   : Formula -> Formula
  | FAnd   : Formula -> Formula -> Formula
  | FOr    : Formula -> Formula -> Formula
  | FImpl  : Formula -> Formula -> Formula
  | FTrue  : Formula
  | FFalse : Formula.

(** A valuation maps variable indices to booleans. *)
Definition Valuation := nat -> bool.

(* ================================================================= *)
(** ** Evaluation *)
(* ================================================================= *)

Fixpoint eval_formula (v : Valuation) (f : Formula) : bool :=
  match f with
  | FVar n      => v n
  | FNot f1     => negb (eval_formula v f1)
  | FAnd f1 f2  => (eval_formula v f1 && eval_formula v f2)%bool
  | FOr f1 f2   => (eval_formula v f1 || eval_formula v f2)%bool
  | FImpl f1 f2 => (negb (eval_formula v f1) || eval_formula v f2)%bool
  | FTrue       => true
  | FFalse      => false
  end.

(* ================================================================= *)
(** ** Semantic notions *)
(* ================================================================= *)

Definition satisfiable (f : Formula) : Prop :=
  exists v, eval_formula v f = true.

Definition valid (f : Formula) : Prop :=
  forall v, eval_formula v f = true.

Definition unsatisfiable (f : Formula) : Prop :=
  forall v, eval_formula v f = false.

Definition equiv_formula (f1 f2 : Formula) : Prop :=
  forall v, eval_formula v f1 = eval_formula v f2.

Definition entails (f1 f2 : Formula) : Prop :=
  forall v, eval_formula v f1 = true -> eval_formula v f2 = true.

(* ================================================================= *)
(** ** Formula size *)
(* ================================================================= *)

Fixpoint formula_size (f : Formula) : nat :=
  match f with
  | FVar _      => 1
  | FNot f1     => 1 + formula_size f1
  | FAnd f1 f2  => 1 + formula_size f1 + formula_size f2
  | FOr f1 f2   => 1 + formula_size f1 + formula_size f2
  | FImpl f1 f2 => 1 + formula_size f1 + formula_size f2
  | FTrue       => 1
  | FFalse      => 1
  end.

(* ================================================================= *)
(** ** Evaluation lemmas (1-5) *)
(* ================================================================= *)

Lemma eval_true : forall v, eval_formula v FTrue = true.
Proof. intros. reflexivity. Qed.

Lemma eval_false : forall v, eval_formula v FFalse = false.
Proof. intros. reflexivity. Qed.

Lemma eval_var : forall v n, eval_formula v (FVar n) = v n.
Proof. intros. reflexivity. Qed.

Lemma eval_not : forall v f,
  eval_formula v (FNot f) = negb (eval_formula v f).
Proof. intros. reflexivity. Qed.

Lemma eval_and : forall v f1 f2,
  eval_formula v (FAnd f1 f2) = (eval_formula v f1 && eval_formula v f2)%bool.
Proof. intros. reflexivity. Qed.

(* ================================================================= *)
(** ** Validity / satisfiability / unsatisfiability (6-9) *)
(* ================================================================= *)

Lemma true_is_valid : valid FTrue.
Proof. unfold valid. intros. reflexivity. Qed.

Lemma false_is_unsat : unsatisfiable FFalse.
Proof. unfold unsatisfiable. intros. reflexivity. Qed.

Lemma valid_implies_sat : forall f, valid f -> satisfiable f.
Proof.
  unfold valid, satisfiable. intros f H.
  exists (fun _ => true). apply H.
Qed.

Lemma unsat_not_sat : forall f, unsatisfiable f -> ~ satisfiable f.
Proof.
  unfold unsatisfiable, satisfiable. intros f Hu [v Hv].
  rewrite Hu in Hv. discriminate.
Qed.

(* ================================================================= *)
(** ** Equivalences (10-13) *)
(* ================================================================= *)

Lemma double_neg : forall f, equiv_formula (FNot (FNot f)) f.
Proof.
  unfold equiv_formula. intros f v. simpl.
  rewrite negb_involutive. reflexivity.
Qed.

Lemma impl_as_or : forall f1 f2,
  equiv_formula (FImpl f1 f2) (FOr (FNot f1) f2).
Proof.
  unfold equiv_formula. intros f1 f2 v. simpl. reflexivity.
Qed.

Lemma and_comm : forall f1 f2,
  equiv_formula (FAnd f1 f2) (FAnd f2 f1).
Proof.
  unfold equiv_formula. intros f1 f2 v. simpl.
  rewrite andb_comm. reflexivity.
Qed.

Lemma or_comm : forall f1 f2,
  equiv_formula (FOr f1 f2) (FOr f2 f1).
Proof.
  unfold equiv_formula. intros f1 f2 v. simpl.
  rewrite orb_comm. reflexivity.
Qed.

(* ================================================================= *)
(** ** Entailment (14-20) *)
(* ================================================================= *)

Lemma entails_refl : forall f, entails f f.
Proof. unfold entails. auto. Qed.

Lemma entails_trans : forall f1 f2 f3,
  entails f1 f2 -> entails f2 f3 -> entails f1 f3.
Proof. unfold entails. auto. Qed.

Lemma and_entails_left : forall f1 f2, entails (FAnd f1 f2) f1.
Proof.
  unfold entails. intros f1 f2 v H. simpl in H.
  apply andb_prop in H. destruct H as [H _]. exact H.
Qed.

Lemma or_entails_left : forall f1 f2, entails f1 (FOr f1 f2).
Proof.
  unfold entails. intros f1 f2 v H. simpl.
  rewrite H. reflexivity.
Qed.

Lemma and_entails_right : forall f1 f2, entails (FAnd f1 f2) f2.
Proof.
  unfold entails. intros f1 f2 v H. simpl in H.
  apply andb_prop in H. destruct H as [_ H]. exact H.
Qed.

Lemma false_entails_any : forall f, entails FFalse f.
Proof. unfold entails. intros f v H. simpl in H. discriminate. Qed.

Lemma any_entails_true : forall f, entails f FTrue.
Proof. unfold entails. intros f v _. reflexivity. Qed.
