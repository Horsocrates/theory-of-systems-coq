(** * TransitionConcrete.v -- Concrete Green's function values across the transition
    Elements: G_{00}(K) at ε=0, ε=1/2, ε=1 for small K
    Roles:    Demonstrates how propagator behavior changes across phases
    Rules:    ε=0 gives 2^K (doubling), ε=1/2 gives Fibonacci, ε=1 oscillates
    Status:   Stdlib
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.GreenFunction.
From ToS Require Import stdlib.TransitionFamily.

Open Scope Q_scope.

(* ================================================================== *)
(*  CLASSICAL PHASE: ε=0 (full shift, G_{00} = 2^K)                    *)
(* ================================================================== *)

Lemma green_eps0_1 : green (M_eps 0) 0%nat 0%nat 1 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma green_eps0_2 : green (M_eps 0) 0%nat 0%nat 2 == 2.
Proof. vm_compute. reflexivity. Qed.

Lemma green_eps0_3 : green (M_eps 0) 0%nat 0%nat 3 == 4.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  MAXIMAL PHASE: ε=1 (det=-2, oscillating)                           *)
(* ================================================================== *)

Lemma green_eps1_1 : green (M_eps 1) 0%nat 0%nat 1 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma green_eps1_2 : green (M_eps 1) 0%nat 0%nat 2 == 2.
Proof. vm_compute. reflexivity. Qed.

Lemma green_eps1_3 : green (M_eps 1) 0%nat 0%nat 3 == 2.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  GROWTH COMPARISON AT K=4                                            *)
(* ================================================================== *)

(** Golden (ε=1/2): G_{00}(4) = 5 *)
Lemma green_golden_K4 : green (M_eps (1#2)) 0%nat 0%nat 4 == 5.
Proof. vm_compute. reflexivity. Qed.

(** Classical (ε=0): G_{00}(4) = 8 *)
Lemma green_classical_K4 : green (M_eps 0) 0%nat 0%nat 4 == 8.
Proof. vm_compute. reflexivity. Qed.

(** Golden grows slower than classical at K=4 *)
Lemma golden_slower_than_classical :
  green (M_eps (1#2)) 0%nat 0%nat 4 < green (M_eps 0) 0%nat 0%nat 4.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  COMPARISON AT K=3: three phases diverge                             *)
(* ================================================================== *)

(** At K=3: classical=4 > golden=3 > maximal=2 *)
Lemma three_phase_ordering :
  green (M_eps 1) 0%nat 0%nat 3 < green (M_eps (1#2)) 0%nat 0%nat 3 /\
  green (M_eps (1#2)) 0%nat 0%nat 3 < green (M_eps 0) 0%nat 0%nat 3.
Proof.
  split; vm_compute; reflexivity.
Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                           *)
(* ================================================================== *)

Theorem transition_concrete_synthesis :
  (* Classical doubling: 1, 2, 4, 8 *)
  green (M_eps 0) 0%nat 0%nat 3 == 4 /\
  green (M_eps 0) 0%nat 0%nat 4 == 8 /\
  (* Maximal oscillation: 1, 2, 2 *)
  green (M_eps 1) 0%nat 0%nat 3 == 2 /\
  (* Golden slower than classical *)
  green (M_eps (1#2)) 0%nat 0%nat 4 < green (M_eps 0) 0%nat 0%nat 4 /\
  (* Three-phase ordering at K=3 *)
  green (M_eps 1) 0%nat 0%nat 3 < green (M_eps (1#2)) 0%nat 0%nat 3.
Proof.
  split; [exact green_eps0_3|].
  split; [exact green_classical_K4|].
  split; [exact green_eps1_3|].
  split; [exact golden_slower_than_classical|].
  exact (proj1 three_phase_ordering).
Qed.
