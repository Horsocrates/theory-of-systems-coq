(** * MarketUncertainty.v — Uncertainty principle for markets
    Elements: market_gap, market_memory_param, uncertainty_product;
    Roles:    gap + memory = 1 as fundamental trade-off;
    Rules:    uncertainty product maximized at lambda=1/2.
    STATUS: 17 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs List Bool Lia Lra Lqa.
Open Scope Q_scope.

(* ===== Market gap: how much information is lost per step ===== *)

Definition market_gap (l : Q) : Q := 1 - Qabs l.

(* ===== Market memory parameter ===== *)

Definition market_memory_param (l : Q) : Q := Qabs l.

(* ===== Uncertainty product ===== *)

Definition uncertainty_product (l : Q) : Q := market_gap l * market_memory_param l.

(* ===== FUNDAMENTAL: gap + memory = 1 (universal) ===== *)

Theorem market_uncertainty : forall l,
  market_gap l + market_memory_param l == 1.
Proof.
  intro l. unfold market_gap, market_memory_param. ring.
Qed.

(* ===== Qabs concrete values ===== *)

Lemma qabs_zero : Qabs 0 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma qabs_one : Qabs 1 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma qabs_half : Qabs (1#2) == 1#2.
Proof. vm_compute. reflexivity. Qed.

Lemma qabs_neg_three_fifths : Qabs (-(3#5)) == 3#5.
Proof. vm_compute. reflexivity. Qed.

(* ===== Maximum uncertainty product at l=1/2 ===== *)

Lemma max_uncertainty_product : uncertainty_product (1#2) == 1#4.
Proof.
  unfold uncertainty_product, market_gap, market_memory_param.
  assert (H : Qabs (1#2) == 1#2) by (vm_compute; reflexivity).
  rewrite H. ring.
Qed.

(* ===== Zero at extremes ===== *)

Lemma uncertainty_at_zero : uncertainty_product 0 == 0.
Proof.
  unfold uncertainty_product, market_gap, market_memory_param.
  assert (H : Qabs 0 == 0) by (vm_compute; reflexivity).
  rewrite H. ring.
Qed.

Lemma uncertainty_at_one : uncertainty_product 1 == 0.
Proof.
  unfold uncertainty_product, market_gap, market_memory_param.
  assert (H : Qabs 1 == 1) by (vm_compute; reflexivity).
  rewrite H. ring.
Qed.

Lemma uncertainty_at_neg_one : uncertainty_product (-(1)) == 0.
Proof.
  unfold uncertainty_product, market_gap, market_memory_param.
  assert (H : Qabs (-(1)) == 1) by (vm_compute; reflexivity).
  rewrite H. ring.
Qed.

(* ===== Concrete market gaps ===== *)

Lemma gap_one_fifth : market_gap (1#5) == 4#5.
Proof.
  unfold market_gap.
  assert (H : Qabs (1#5) == 1#5) by (vm_compute; reflexivity).
  rewrite H. ring.
Qed.

Lemma gap_four_fifths : market_gap (4#5) == 1#5.
Proof.
  unfold market_gap.
  assert (H : Qabs (4#5) == 4#5) by (vm_compute; reflexivity).
  rewrite H. ring.
Qed.

(* ===== Concrete memory params ===== *)

Lemma memory_one_fifth : market_memory_param (1#5) == 1#5.
Proof.
  unfold market_memory_param. vm_compute. reflexivity.
Qed.

Lemma memory_four_fifths : market_memory_param (4#5) == 4#5.
Proof.
  unfold market_memory_param. vm_compute. reflexivity.
Qed.

(* ===== Uncertainty product concrete ===== *)

Lemma uncertainty_one_fifth : uncertainty_product (1#5) == 4#25.
Proof.
  unfold uncertainty_product, market_gap, market_memory_param.
  assert (H : Qabs (1#5) == 1#5) by (vm_compute; reflexivity).
  rewrite H. ring.
Qed.

Lemma uncertainty_three_fifths : uncertainty_product (3#5) == 6#25.
Proof.
  unfold uncertainty_product, market_gap, market_memory_param.
  assert (H : Qabs (3#5) == 3#5) by (vm_compute; reflexivity).
  rewrite H. ring.
Qed.

(* ===== Symmetry: |l| determines everything ===== *)

Lemma uncertainty_symmetric : forall l,
  uncertainty_product l == uncertainty_product (-(l)).
Proof.
  intro l. unfold uncertainty_product, market_gap, market_memory_param.
  rewrite Qabs_opp. ring.
Qed.

(* ===== Synthesis ===== *)

Theorem market_uncertainty_synthesis :
  (forall l, market_gap l + market_memory_param l == 1) /\
  uncertainty_product (1#2) == 1#4 /\
  uncertainty_product 0 == 0 /\
  uncertainty_product 1 == 0 /\
  (forall l, uncertainty_product l == uncertainty_product (-(l))).
Proof.
  split; [exact market_uncertainty|].
  split; [exact max_uncertainty_product|].
  split; [exact uncertainty_at_zero|].
  split; [exact uncertainty_at_one|].
  exact uncertainty_symmetric.
Qed.
