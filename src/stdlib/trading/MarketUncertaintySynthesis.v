(** * MarketUncertaintySynthesis.v — Synthesis of market uncertainty principle
    Elements: uncertainty product, Heisenberg analogy, bounds;
    Roles:    unify uncertainty theory with Heisenberg connection;
    Rules:    combined theorems for Direction 3.
    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs List Bool Lia Lra Lqa.
From ToS Require Import stdlib.trading.MarketUncertainty.
From ToS Require Import stdlib.trading.MarketHeisenberg.
Open Scope Q_scope.

(* ===== Core trade-off ===== *)

Lemma fundamental_trade_off :
  forall l, market_gap l + market_memory_param l == 1.
Proof. exact market_uncertainty. Qed.

(* ===== Bound and maximum ===== *)

Lemma bound_and_max :
  uncertainty_product (1#2) == 1#4 /\
  (forall l, 0 <= Qabs l -> Qabs l <= 1 ->
    uncertainty_product l <= 1#4).
Proof.
  split; [exact max_uncertainty_product | exact uncertainty_bounded].
Qed.

(* ===== Concrete examples span the range ===== *)

Lemma concrete_range :
  uncertainty_product 0 == 0 /\
  uncertainty_product (1#5) == 4#25 /\
  uncertainty_product (1#2) == 1#4 /\
  uncertainty_product (3#5) == 6#25 /\
  uncertainty_product 1 == 0.
Proof.
  split; [exact uncertainty_at_zero|].
  split; [exact uncertainty_one_fifth|].
  split; [exact max_uncertainty_product|].
  split; [exact uncertainty_three_fifths|].
  exact uncertainty_at_one.
Qed.

(* ===== Gap-memory duality ===== *)

Lemma gap_memory_duality :
  market_gap 0 == 1 /\ market_memory_param 0 == 0 /\
  market_gap 1 == 0 /\ market_memory_param 1 == 1.
Proof.
  split; [exact no_memory_full_gap|].
  split; [vm_compute; reflexivity|].
  split; [exact perfect_memory_no_gap|].
  vm_compute. reflexivity.
Qed.

(* ===== Symmetry principle ===== *)

Lemma direction3_symmetry :
  forall l, uncertainty_product l == uncertainty_product (-(l)).
Proof. exact uncertainty_symmetric. Qed.

(* ===== Sub-maximum examples ===== *)

Lemma sub_maximum_examples :
  uncertainty_product (1#5) < 1#4 /\
  uncertainty_product (3#5) < 1#4.
Proof.
  split; [exact one_fifth_below_max | exact three_fifths_below_max].
Qed.

(* ===== Grand synthesis ===== *)

Theorem uncertainty_grand_synthesis :
  (* Fundamental: gap + memory = 1 *)
  (forall l, market_gap l + market_memory_param l == 1) /\
  (* Maximum product = 1/4 *)
  uncertainty_product (1#2) == 1#4 /\
  (* Extremes are zero *)
  (uncertainty_product 0 == 0 /\ uncertainty_product 1 == 0) /\
  (* Symmetry *)
  (forall l, uncertainty_product l == uncertainty_product (-(l))).
Proof.
  split; [exact market_uncertainty|].
  split; [exact max_uncertainty_product|].
  split; [split; [exact uncertainty_at_zero | exact uncertainty_at_one]|].
  exact uncertainty_symmetric.
Qed.
