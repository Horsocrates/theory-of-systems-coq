(** * DistinctionCost.v — Cost of distinguishing positions at each bit level
    Elements: distinction_cost, total_cost, per-bit average, fine vs coarse
    Roles:    Wraps commutator bounds as "distinction cost" — measuring costs information
    Rules:    Fine (LSB) costs ~2× coarse (MSB); average cost < 2
    Status:   complete
    STATUS: 13 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Lia.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.heisenberg.CommutatorBits.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Distinction Cost = Commutator Bound                        *)
(* ================================================================== *)

(** The cost of distinguishing position at bit level k equals
    the commutator bound for that bit. *)
Definition distinction_cost (n_bits k : nat) : Q :=
  bit_comm_max n_bits k.

(* ================================================================== *)
(*  Part II: Individual Bit Costs                                      *)
(* ================================================================== *)

Lemma msb_cost : distinction_cost 4 3 == 1#2.
Proof. unfold distinction_cost. apply msb_is_half. Qed.

Lemma lsb_cost : distinction_cost 4 0 == 983#1000.
Proof. unfold distinction_cost. apply lsb_value. Qed.

Lemma cost_ratio : distinction_cost 4 0 / distinction_cost 4 3 == 983#500.
Proof. unfold distinction_cost. apply lsb_ratio. Qed.

Lemma cost_ratio_gt_3_2 : 2 * distinction_cost 4 0 > 3 * distinction_cost 4 3.
Proof.
  unfold distinction_cost, bit_comm_max.
  (* 2 * 983/1000 = 1966/1000 > 3 * 1/2 = 1500/1000 *)
  lra.
Qed.

(* ================================================================== *)
(*  Part III: Total and Average Cost                                   *)
(* ================================================================== *)

Definition total_cost : Q := total_bound_16.

Lemma total_cost_value : total_cost == 7983#1000.
Proof. unfold total_cost. apply total_bound_value. Qed.

Lemma per_bit_average : total_cost / 4 == 7983#4000.
Proof. unfold total_cost, total_bound_16, bit_comm_max. field. Qed.

Lemma per_bit_average_approx : total_cost < 8.
Proof. unfold total_cost, total_bound_16, bit_comm_max. lra. Qed.

(* ================================================================== *)
(*  Part IV: Fine vs Coarse Ordering                                   *)
(* ================================================================== *)

Lemma fine_vs_coarse : distinction_cost 4 0 > distinction_cost 4 1.
Proof. unfold distinction_cost. apply lsb_expensive. Qed.

Lemma all_coarse_same : distinction_cost 4 1 == distinction_cost 4 2.
Proof.
  unfold distinction_cost, bit_comm_max. lra.
Qed.

(* ================================================================== *)
(*  Part V: 3-bit System (K=8)                                        *)
(* ================================================================== *)

Lemma distinction_cost_3bit_lsb : bit_comm_max 3 0 == 983#1000.
Proof. unfold bit_comm_max. lra. Qed.

Lemma distinction_cost_3bit_msb : bit_comm_max 3 2 == 1#2.
Proof. unfold bit_comm_max. lra. Qed.

(* ================================================================== *)
(*  Part VI: Cost Monotonicity                                         *)
(* ================================================================== *)

Lemma cost_lsb_gt_all_others :
  distinction_cost 4 0 > distinction_cost 4 1 /\
  distinction_cost 4 0 > distinction_cost 4 2 /\
  distinction_cost 4 0 > distinction_cost 4 3.
Proof.
  unfold distinction_cost, bit_comm_max. lra.
Qed.

Lemma cost_always_positive :
  0 < distinction_cost 4 0 /\ 0 < distinction_cost 4 1 /\
  0 < distinction_cost 4 2 /\ 0 < distinction_cost 4 3.
Proof.
  unfold distinction_cost, bit_comm_max. lra.
Qed.
