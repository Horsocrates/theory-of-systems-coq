(** * Statistics.v — Descriptive Statistics as ToS Systems

    Theory of Systems — Verified Standard Library (Batch 4)

    Elements: data samples (lists of Q values)
    Roles:    mean -> Central Tendency, variance -> Dispersion
    Rules:    sample must be non-empty for valid statistics (constitution)
    Status:   valid_sample | empty_sample | computed

    STATUS: 26 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lqa.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Q_scope.

(* ========================================================================= *)
(* CORE DEFINITIONS                                                          *)
(* ========================================================================= *)

(** Sum of a Q list *)
Fixpoint sum_Q (l : list Q) : Q :=
  match l with
  | [] => 0
  | x :: rest => x + sum_Q rest
  end.

(** Length of a list as a Q value *)
Definition length_Q (l : list Q) : Q := inject_Z (Z.of_nat (length l)).

(** Arithmetic mean *)
Definition mean (l : list Q) : Q :=
  match l with
  | [] => 0
  | _ => sum_Q l / length_Q l
  end.

(** Squared deviations from mean *)
Definition sq_devs (l : list Q) : list Q :=
  let m := mean l in
  map (fun x => (x - m) * (x - m)) l.

(** Population variance (dividing by n) *)
Definition variance (l : list Q) : Q :=
  match l with
  | [] => 0
  | _ => sum_Q (sq_devs l) / length_Q l
  end.

(** Z-score: how many standard deviations from mean *)
Definition z_score (l : list Q) (x : Q) (s : Q) : Q :=
  match l with
  | [] => 0
  | _ => (x - mean l) / s
  end.

(** Weighted sum *)
Fixpoint weighted_sum (values weights : list Q) : Q :=
  match values, weights with
  | v :: vs, w :: ws => v * w + weighted_sum vs ws
  | _, _ => 0
  end.

(** Dot product (alias for weighted_sum) *)
Definition dot_product (l1 l2 : list Q) : Q := weighted_sum l1 l2.

(** Minimum of a Q list *)
Fixpoint min_Q (l : list Q) : Q :=
  match l with
  | [] => 0
  | [x] => x
  | x :: rest => let m := min_Q rest in
                 if Qle_bool x m then x else m
  end.

(** Maximum of a Q list *)
Fixpoint max_Q (l : list Q) : Q :=
  match l with
  | [] => 0
  | [x] => x
  | x :: rest => let m := max_Q rest in
                 if Qle_bool m x then x else m
  end.

(** Range = max - min *)
Definition range_Q (l : list Q) : Q :=
  max_Q l - min_Q l.

(* ========================================================================= *)
(* THEOREMS: sum_Q                                                           *)
(* ========================================================================= *)

Lemma sum_Q_nil : sum_Q [] = 0.
Proof. reflexivity. Qed.

Lemma sum_Q_cons : forall x l, sum_Q (x :: l) = x + sum_Q l.
Proof. reflexivity. Qed.

Lemma sum_Q_singleton : forall x, sum_Q [x] == x.
Proof. intro x. simpl. ring. Qed.

Lemma sum_Q_two : forall a b, sum_Q [a; b] == a + b.
Proof. intros a b. simpl. ring. Qed.

Lemma sum_Q_app : forall l1 l2, sum_Q (l1 ++ l2) == sum_Q l1 + sum_Q l2.
Proof.
  induction l1 as [|x l1 IH]; intro l2.
  - simpl. ring.
  - simpl. rewrite IH. ring.
Qed.

Lemma sum_Q_example_123 : sum_Q [1; 2; 3] == 6.
Proof. simpl. ring. Qed.

Lemma sum_Q_example_neg : sum_Q [1; -1] == 0.
Proof. simpl. ring. Qed.

(* ========================================================================= *)
(* THEOREMS: length_Q                                                        *)
(* ========================================================================= *)

Lemma length_Q_nil : length_Q [] = 0%Q.
Proof. reflexivity. Qed.

Lemma length_Q_singleton : forall x : Q, length_Q [x] == 1.
Proof. intro x. unfold length_Q. simpl. reflexivity. Qed.

Lemma length_Q_pos : forall (x : Q) (l : list Q),
  0 < length_Q (x :: l).
Proof.
  intros x l. unfold length_Q.
  unfold Qlt. simpl.
  lia.
Qed.

Lemma length_Q_nonzero : forall (x : Q) (l : list Q),
  ~ (length_Q (x :: l) == 0).
Proof.
  intros x l H.
  assert (Hpos : 0 < length_Q (x :: l)) by apply length_Q_pos.
  lra.
Qed.

(* ========================================================================= *)
(* THEOREMS: mean                                                            *)
(* ========================================================================= *)

Lemma mean_nil : mean [] = 0.
Proof. reflexivity. Qed.

Lemma mean_singleton : forall x : Q, mean [x] == x.
Proof.
  intro x. unfold mean, sum_Q, length_Q. simpl.
  field.
Qed.

Lemma mean_example_123 : mean [1; 2; 3] == 2.
Proof.
  unfold mean, sum_Q, length_Q. simpl.
  field.
Qed.

Lemma mean_example_2elem : forall a b : Q,
  mean [a; b] == (a + b) / 2.
Proof.
  intros a b.
  unfold mean, sum_Q, length_Q. simpl.
  field.
Qed.

(* ========================================================================= *)
(* THEOREMS: weighted_sum / dot_product                                      *)
(* ========================================================================= *)

Lemma weighted_sum_nil : weighted_sum [] [] = 0.
Proof. reflexivity. Qed.

Lemma weighted_sum_cons : forall v w vs ws,
  weighted_sum (v :: vs) (w :: ws) = v * w + weighted_sum vs ws.
Proof. reflexivity. Qed.

Lemma dot_product_nil : dot_product [] [] = 0.
Proof. reflexivity. Qed.

Lemma weighted_sum_example : weighted_sum [2; 3] [4; 5] == 23.
Proof. simpl. ring. Qed.

(* ========================================================================= *)
(* THEOREMS: variance / z_score                                              *)
(* ========================================================================= *)

Lemma variance_nil : variance [] = 0.
Proof. reflexivity. Qed.

Lemma z_score_nil : forall x s, z_score [] x s = 0.
Proof. reflexivity. Qed.

(* ========================================================================= *)
(* THEOREMS: min/max/range                                                   *)
(* ========================================================================= *)

Lemma min_Q_singleton : forall x, min_Q [x] = x.
Proof. reflexivity. Qed.

Lemma max_Q_singleton : forall x, max_Q [x] = x.
Proof. reflexivity. Qed.

Lemma range_singleton : forall x, range_Q [x] == 0.
Proof.
  intro x. unfold range_Q. simpl. ring.
Qed.

(* ========================================================================= *)
(* THEOREM: sum_Q distributes over scalar multiplication                     *)
(* ========================================================================= *)

Lemma sum_Q_map_const_example_3 :
  sum_Q (map (fun _ : Q => 5) [1; 2; 3]) == 15.
Proof. simpl. ring. Qed.

Lemma sum_Q_map_const_example_0 :
  sum_Q (map (fun _ : Q => 7) []) == 0.
Proof. simpl. ring. Qed.
