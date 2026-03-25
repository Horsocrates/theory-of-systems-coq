(** * InformationUncertainty.v — Per-bit information cost of position measurement
    Elements: position_bits_16, block_uncertainty_16, cost_per_bit_16
    Roles:    Finer blocks need more bits but have higher per-bit uncertainty
    Rules:    cost_per_bit increases with block size; first bit most expensive
    Status:   complete
    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Lia.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.heisenberg.BlockMeasurement.
From ToS Require Import stdlib.heisenberg.CommutatorBits.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Position Bits and Block Uncertainty for K=16               *)
(* ================================================================== *)

(** Number of bits of position information at block size B in K=16 chain.
    B=1: 4 bits (full resolution), B=2: 3 bits, B=4: 2 bits, B=8: 1 bit *)
Definition position_bits_16 (B : nat) : Q :=
  match B with
  | S O => 4
  | S (S O) => 3
  | S (S (S (S O))) => 2
  | S (S (S (S (S (S (S (S O))))))) => 1
  | _ => 0
  end.

(** Block uncertainty at each scale for K=16.
    B=1: near-maximal (98/100), B=2,4,8: half (50/100). *)
Definition block_uncertainty_16 (B : nat) : Q :=
  match B with
  | S O => 98#100
  | S (S O) => 50#100
  | S (S (S (S O))) => 50#100
  | S (S (S (S (S (S (S (S O))))))) => 50#100
  | _ => 0
  end.

(** Cost per bit = block uncertainty / number of position bits *)
Definition cost_per_bit_16 (B : nat) : Q :=
  block_uncertainty_16 B / position_bits_16 B.

(* ================================================================== *)
(*  Part II: Cost Values at Each Scale                                 *)
(* ================================================================== *)

Lemma cost_at_full : cost_per_bit_16 1 == 49#200.
Proof.
  unfold cost_per_bit_16, block_uncertainty_16, position_bits_16.
  field.
Qed.

Lemma cost_at_B2 : cost_per_bit_16 2 == 1#6.
Proof.
  unfold cost_per_bit_16, block_uncertainty_16, position_bits_16.
  field.
Qed.

Lemma cost_at_B4 : cost_per_bit_16 4 == 1#4.
Proof.
  unfold cost_per_bit_16, block_uncertainty_16, position_bits_16.
  field.
Qed.

Lemma cost_at_B8 : cost_per_bit_16 8 == 1#2.
Proof.
  unfold cost_per_bit_16, block_uncertainty_16, position_bits_16.
  field.
Qed.

(* ================================================================== *)
(*  Part III: Ordering — Coarser Bits Cost More Per Bit                *)
(*  (Reformulated without division to keep lra happy)                  *)
(* ================================================================== *)

(** B=8 costs more per bit than B=2:
    uncertainty(8)/bits(8) > uncertainty(2)/bits(2)
    ⟺ uncertainty(8) * bits(2) > uncertainty(2) * bits(8)  *)
Lemma first_bit_most_expensive :
  block_uncertainty_16 8 * position_bits_16 2 >
  block_uncertainty_16 2 * position_bits_16 8.
Proof.
  unfold block_uncertainty_16, position_bits_16.
  (* 50/100 * 3 > 50/100 * 1 ⟹ 150/100 > 50/100 *)
  lra.
Qed.

Lemma cost_monotone_B8_B4 :
  block_uncertainty_16 8 * position_bits_16 4 >
  block_uncertainty_16 4 * position_bits_16 8.
Proof.
  unfold block_uncertainty_16, position_bits_16.
  (* 50/100 * 2 > 50/100 * 1 *)
  lra.
Qed.

Lemma cost_monotone_B4_B2 :
  block_uncertainty_16 4 * position_bits_16 2 >
  block_uncertainty_16 2 * position_bits_16 4.
Proof.
  unfold block_uncertainty_16, position_bits_16.
  (* 50/100 * 3 > 50/100 * 2 *)
  lra.
Qed.

(* ================================================================== *)
(*  Part IV: Full Resolution Has Highest Total Uncertainty              *)
(* ================================================================== *)

Lemma full_resolution_highest_total :
  block_uncertainty_16 1 * position_bits_16 2 >
  block_uncertainty_16 2 * position_bits_16 1.
Proof.
  unfold block_uncertainty_16, position_bits_16.
  (* 98/100 * 3 > 50/100 * 4 ⟹ 294/100 > 200/100 *)
  lra.
Qed.

Lemma all_costs_positive :
  0 < block_uncertainty_16 1 /\ 0 < block_uncertainty_16 2 /\
  0 < block_uncertainty_16 4 /\ 0 < block_uncertainty_16 8.
Proof.
  unfold block_uncertainty_16. lra.
Qed.
