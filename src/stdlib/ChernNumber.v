(** * ChernNumber.v — Chern Number from Lattice Berry Phase
    Elements: Sign flips at plaquettes, count_negatives, topological invariant
    Roles:    Classify phases by parity of negative overlaps
    Rules:    Odd negatives → topological, Even → trivial
    Status:   Stdlib
    STATUS: 13 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
Open Scope Q_scope.

(* ================================================================== *)
(*  SIGN DETECTION                                                     *)
(*  is_neg x = 1 if x < 0, 0 otherwise                                *)
(*  Uses Qnum to check sign — fully computable                        *)
(* ================================================================== *)

Definition is_neg (x : Q) : nat :=
  match Qnum x with
  | Zneg _ => 1%nat
  | _ => 0%nat
  end.

Lemma is_neg_positive : is_neg (3#4) = 0%nat.
Proof. reflexivity. Qed.

Lemma is_neg_negative : is_neg (-(1#2)) = 1%nat.
Proof. reflexivity. Qed.

Lemma is_neg_zero : is_neg 0 = 0%nat.
Proof. reflexivity. Qed.

(* ================================================================== *)
(*  PHASE DIAGRAM                                                      *)
(*  Model: 4 plaquettes with overlap signs depending on mass m        *)
(*  overlap_sign(m, k) models the sign of Berry plaquette at k        *)
(* ================================================================== *)

(* Plaquette overlaps for mass parameter m *)
(* Model: overlap at k_i = m - threshold_i *)
(* Thresholds: 0, 2, 2, 4 (from 2-band Chern insulator) *)

Definition plaquette_overlap (m : Q) (i : nat) : Q :=
  match i with
  | O => m                 (* threshold 0 *)
  | S O => m - 2           (* threshold 2 *)
  | S (S O) => m - 2       (* threshold 2 *)
  | _ => m - 4             (* threshold 4 *)
  end.

Definition count_negatives (m : Q) : nat :=
  (is_neg (plaquette_overlap m O) +
   is_neg (plaquette_overlap m (S O)) +
   is_neg (plaquette_overlap m (S (S O))) +
   is_neg (plaquette_overlap m (S (S (S O)))))%nat.

(* ================================================================== *)
(*  PHASE CLASSIFICATION                                               *)
(* ================================================================== *)

(* m = 1: overlaps = 1, -1, -1, -3 → 3 negatives *)
Lemma count_neg_m1 : count_negatives 1 = 3%nat.
Proof. reflexivity. Qed.

(* m = 3: overlaps = 3, 1, 1, -1 → 1 negative *)
Lemma count_neg_m3 : count_negatives 3 = 1%nat.
Proof. reflexivity. Qed.

(* m = -1: overlaps = -1, -3, -3, -5 → 4 negatives *)
Lemma count_neg_mn1 : count_negatives (-(1)) = 4%nat.
Proof. reflexivity. Qed.

(* m = 5: overlaps = 5, 3, 3, 1 → 0 negatives *)
Lemma count_neg_m5 : count_negatives 5 = 0%nat.
Proof. reflexivity. Qed.

(* ================================================================== *)
(*  TOPOLOGICAL CLASSIFICATION                                         *)
(*  Topological iff count_negatives is odd                              *)
(* ================================================================== *)

Definition is_topological (m : Q) : bool :=
  Nat.odd (count_negatives m).

Lemma topological_m1 : is_topological 1 = true.
Proof. reflexivity. Qed.

Lemma topological_m3 : is_topological 3 = true.
Proof. reflexivity. Qed.

Lemma trivial_mn1 : is_topological (-(1)) = false.
Proof. reflexivity. Qed.

Lemma trivial_m5 : is_topological 5 = false.
Proof. reflexivity. Qed.

(* ================================================================== *)
(*  PHASE TRANSITIONS AT THRESHOLD CROSSINGS                          *)
(* ================================================================== *)

Lemma phase_transition_at_m0 :
  count_negatives (-(1#2)) = 4%nat /\ count_negatives (1#2) = 3%nat.
Proof. split; reflexivity. Qed.

Theorem chern_number_synthesis :
  is_topological 1 = true /\
  is_topological 3 = true /\
  count_negatives 5 = 0%nat /\
  count_negatives (-(1)) = 4%nat.
Proof.
  split; [exact topological_m1|].
  split; [exact topological_m3|].
  split; [exact count_neg_m5|exact count_neg_mn1].
Qed.
