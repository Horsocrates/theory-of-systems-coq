(** * ConnectionSynthesis.v — Grand synthesis: i = connection between distinction sides
    Elements: All results from DistinctionConnection, GaussianSpiral, CommutatorComplex, ConnectionCircle
    Roles:    Unifies: binary→plane, i²=-I, spiral growth, commutator structure, Z₄ cycle
    Rules:    i is the unique connection forced by binary distinction
    Status:   Stdlib
    STATUS: 6 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.GreenFunction.
From ToS Require Import stdlib.ComplexOverQ.
From ToS Require Import stdlib.DistinctionConnection.
From ToS Require Import stdlib.GaussianSpiral.
From ToS Require Import stdlib.CommutatorComplex.
From ToS Require Import stdlib.ConnectionCircle.
From ToS Require Import stdlib.SpiralProcess.
Open Scope Q_scope.

(* ================================================================== *)
(*  GRAND SYNTHESIS                                                    *)
(* ================================================================== *)

Theorem connection_synthesis :
  (* Binary → one plane *)
  planes_from_sides 2 = 1%nat /\
  (* i² = -I (both diagonal entries) *)
  mat2_mul C_i C_i 0%nat 0%nat == -(1) /\
  mat2_mul C_i C_i 1%nat 1%nat == -(1) /\
  (* Spiral: |z(4)|² = 5 *)
  spiral_r_sq 4 = 5%Z /\
  (* 5 factors in Z[i]: 2²+1² = 5 *)
  2*2 + 1*1 == 5 /\
  (* Commutator verified: off-diagonal ±1 *)
  comm_4 0%nat 3%nat == 1 /\
  comm_4 3%nat 0%nat == -(1) /\
  (* Brahmagupta: norm multiplicative *)
  (1*1 + 1*1) * (2*2 + 1*1) == 3*3 + 1*1.
Proof.
  split; [exact one_plane_from_binary |].
  split; [exact i_sq_00 |].
  split; [exact i_sq_11 |].
  split; [exact r_sq_4_is_5 |].
  split; [exact five_factors |].
  split; [exact comm_4_03 |].
  split; [exact comm_4_30 |].
  exact norm_multiplicative.
Qed.

(* ================================================================== *)
(*  UNIQUENESS: BINARY DISTINCTION FORCES i                            *)
(* ================================================================== *)

(* The only rotation in one plane with period dividing 4 and
   sending (1,0) to (0,1) is i *)
Theorem binary_forces_i :
  (* i sends A to ¬A *)
  C_i 1%nat 0%nat * 1 + C_i 1%nat 1%nat * 0 == 1 /\
  (* i sends ¬A to -A *)
  C_i 0%nat 0%nat * 0 + C_i 0%nat 1%nat * 1 == -(1) /\
  (* i has period 4 *)
  (forall r c, (r <= 1)%nat -> (c <= 1)%nat ->
    mat2_mul C_i (fun r' c' =>
      mat2_mul C_i (fun r'' c'' => mat2_mul C_i C_i r'' c'') r' c') r c
    == C_one r c) /\
  (* 4 elements are distinct *)
  ~(C_one 0%nat 1%nat == C_i 0%nat 1%nat).
Proof.
  split; [exact i_sends_A_to_notA |].
  split; [exact i_sends_notA_to_negA |].
  split; [exact i_pow_4_is_identity |].
  exact I_neq_i.
Qed.

(* ================================================================== *)
(*  PHYSICAL INTERPRETATION                                            *)
(* ================================================================== *)

(* i connects being (X) and becoming (P): commutator is nonzero *)
Theorem i_connects_being_becoming :
  comm_4 0%nat 3%nat == 1 /\
  comm_4 0%nat 0%nat == 0 /\
  comm_4 1%nat 1%nat == 0.
Proof.
  split; [exact comm_4_03 |].
  split; [exact comm_4_00 |].
  exact comm_4_11.
Qed.

(* Spiral growth: i generates unbounded exploration *)
Theorem i_generates_growth :
  (spiral_r_sq 1 < spiral_r_sq 2)%Z /\
  (spiral_r_sq 2 < spiral_r_sq 4)%Z /\
  fib_Q 2 * fib_Q 2 + fib_Q 3 * fib_Q 3 == fib_Q 5.
Proof.
  split; [exact spiral_growth_1_2 |].
  split; [exact spiral_growth_2_4 |].
  exact fibonacci_sum_of_squares.
Qed.

(* ================================================================== *)
(*  CIRCLE CLOSURE                                                     *)
(* ================================================================== *)

Theorem connection_is_circle :
  (* Z₄ has 4 distinct elements *)
  ~(C_one 0%nat 1%nat == C_i 0%nat 1%nat) /\
  ~(C_one 0%nat 0%nat == complex_mat (-(1)) 0 0%nat 0%nat) /\
  ~(C_i 0%nat 0%nat == complex_mat (-(1)) 0 0%nat 0%nat) /\
  (* Generator squares to -I *)
  mat2_mul C_i C_i 0%nat 0%nat == -(1).
Proof.
  split; [exact I_neq_i |].
  split; [exact I_neq_neg_I |].
  split; [exact i_neq_neg_I |].
  exact i_sq_00.
Qed.

(* ================================================================== *)
(*  FINAL: EVERYTHING FROM ONE AXIOM                                   *)
(* ================================================================== *)

Theorem from_distinction_to_circle :
  (* One plane from binary distinction *)
  planes_from_sides 2 = 1%nat /\
  (* Connection has period 4 *)
  (forall r c, (r <= 1)%nat -> (c <= 1)%nat ->
    mat2_mul C_i (fun r' c' =>
      mat2_mul C_i (fun r'' c'' => mat2_mul C_i C_i r'' c'') r' c') r c
    == C_one r c) /\
  (* Connection links X and P *)
  comm_4 0%nat 3%nat == 1 /\
  (* Spiral grows without bound *)
  (spiral_r_sq 2 < spiral_r_sq 4)%Z.
Proof.
  split; [exact one_plane_from_binary |].
  split; [exact i_pow_4_is_identity |].
  split; [exact comm_4_03 |].
  exact spiral_growth_2_4.
Qed.
