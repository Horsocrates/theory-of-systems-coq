(** * GrandVerification.v -- Crown: one framework, 40+ verified numbers
    Elements: grand_verification theorem
    Roles:    Unite Ising, random walks, Fibonacci, Green's functions
    Rules:    G_{ij}(K) = (M^K)_{ij} — one object, all of physics
    Status:   Stdlib
    STATUS: 5 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.GreenFunction.
From ToS Require Import stdlib.Ising1D.
From ToS Require Import stdlib.Ising1DVerify.
From ToS Require Import stdlib.RandomWalkCycle.
From ToS Require Import stdlib.RandomWalkLine.
From ToS Require Import stdlib.FibonacciGreen.
From ToS Require Import stdlib.HeatKernelLattice.
From ToS Require Import stdlib.VerificationTable.

Open Scope Q_scope.

(* ================================================================== *)
(*  GRAND VERIFICATION                                                 *)
(* ================================================================== *)

(** All domains unified under G_{ij}(K) = (M^K)_{ij}:

    ISING MODEL:
      T = [[exp(β), exp(-β)], [exp(-β), exp(β)]]
      G_{00}(K) = amplitude of same-spin propagation
      E = -G_{10}(1)/G_{00}(1) in eigenbasis

    RANDOM WALKS:
      M = transition matrix
      G_{00}(K) = return probability in K steps

    FIBONACCI:
      M = [[1,1],[1,0]]
      G_{00}(K) = F(K+1)
      det(M^K) = (-1)^K → Cassini identity

    HEAT KERNEL:
      Z(K) = Σ G_{ii}(K) = trace process
      heat_ratio(K) → λ_max
*)

Lemma ising_verified :
  exp_taylor 1 4 == 65#24 /\
  energy_ising 1 4 == -(28#37) /\
  0 < ising_gap 1 4.
Proof.
  split; [|split].
  - exact exp_taylor_4.
  - exact energy_b1.
  - exact ising_1d_gap_positive.
Qed.

Lemma walks_verified :
  green rw_C3 0%nat 0%nat 2 == 1#2 /\
  return_line 2 == 3#8 /\
  return_line 3 == 5#16.
Proof.
  split; [|split].
  - exact return_C3_2.
  - exact return_line_2.
  - exact return_line_3.
Qed.

Lemma fibonacci_verified :
  green golden 0%nat 0%nat 6 == 13 /\
  trace_process golden 4 == 7 /\
  green_det 3 == -(1).
Proof.
  split; [|split].
  - exact green_golden_00_6.
  - exact trace_golden_4.
  - exact cassini_3.
Qed.

Lemma heat_verified :
  heat_kernel golden 0 == 2 /\
  heat_ratio golden 3 == 7#4.
Proof.
  split.
  - exact heat_golden_0.
  - exact heat_ratio_golden_3.
Qed.

(** THE GRAND THEOREM *)
Theorem grand_verification :
  (* Ising *)
  exp_taylor 1 4 == 65#24 /\
  energy_ising 1 4 == -(28#37) /\
  (* Random walks *)
  green rw_C3 0%nat 0%nat 2 == 1#2 /\
  return_line 2 == 3#8 /\
  (* Fibonacci *)
  green golden 0%nat 0%nat 4 == 5 /\
  trace_process golden 4 == 7 /\
  (* Heat kernel *)
  heat_ratio golden 3 == 7#4.
Proof.
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - exact exp_taylor_4.
  - exact energy_b1.
  - exact return_C3_2.
  - exact return_line_2.
  - exact green_golden_00_4.
  - exact trace_golden_4.
  - exact heat_ratio_golden_3.
Qed.
