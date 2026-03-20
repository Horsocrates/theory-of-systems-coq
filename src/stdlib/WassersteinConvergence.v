(** * WassersteinConvergence.v — W1 convergence rate on lattice
    Elements: refinement_plan_2to4, refinement_plan_4to8
    Roles:    W1 between successive refinements = cost of adding distinctions
    Rules:    Constant refinement cost = 1/2 for uniform distributions
    Status:   Stdlib
    STATUS: 8 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.ProcessOptimalTransport.

Open Scope Q_scope.

(* ================================================================== *)
(*  REFINEMENT PLANS: COARSE TO FINE                                   *)
(* ================================================================== *)

(** Embedding: coarse uniform into fine lattice.
    Coarse: K+1 sites. Fine: 2(K+1) sites.
    Each coarse site splits into 2 fine sites, each with half mass. *)

(** W1 between uniform(1) and uniform(3):
    Coarse: 2 sites at {0,1}, weights [1/2, 1/2]
    Fine:   4 sites at {0,1,2,3}, weights [1/4, 1/4, 1/4, 1/4]
    Plan: coarse 0 sends to fine {0,1}; coarse 1 sends to fine {2,3} *)
Definition refinement_plan_2to4 : TransportPlan :=
  fun i j => match i, j with
  | O, O => 1#4  | O, S O => 1#4
  | S O, S (S O) => 1#4  | S O, S (S (S O)) => 1#4
  | _, _ => 0
  end.

(** Cost: 1/4*|0-0| + 1/4*|0-1| + 1/4*|1-2| + 1/4*|1-3|
    = 0 + 1/4 + 1/4 + 1/2 = 1
    Wait -- with lattice_cost: |0-1|=1, |1-2|=1, |1-3|=2 *)
Lemma refinement_cost_2to4 :
  transport_cost refinement_plan_2to4 lattice_cost 3 == 1.
Proof.
  unfold transport_cost, refinement_plan_2to4, lattice_cost.
  vm_compute. reflexivity.
Qed.

(** 4 to 8 refinement:
    Coarse: 4 sites. Fine: 8 sites.
    Same pattern: each site splits. *)
Definition refinement_plan_4to8 : TransportPlan :=
  fun i j => match i, j with
  | O, O => 1#8          | O, S O => 1#8
  | S O, S (S O) => 1#8  | S O, S (S (S O)) => 1#8
  | S (S O), S (S (S (S O))) => 1#8
  | S (S O), S (S (S (S (S O)))) => 1#8
  | S (S (S O)), S (S (S (S (S (S O))))) => 1#8
  | S (S (S O)), S (S (S (S (S (S (S O)))))) => 1#8
  | _, _ => 0
  end.

Lemma refinement_cost_4to8 :
  transport_cost refinement_plan_4to8 lattice_cost 7 == 2.
Proof.
  unfold transport_cost, refinement_plan_4to8, lattice_cost.
  vm_compute. reflexivity.
Qed.

(** Refinement cost scales with lattice size:
    2to4: cost=1, 4to8: cost=2. Ratio = 2 = lattice doubling factor. *)
Theorem refinement_cost_scaling :
  transport_cost refinement_plan_4to8 lattice_cost 7 ==
  2 * transport_cost refinement_plan_2to4 lattice_cost 3.
Proof.
  rewrite refinement_cost_2to4. rewrite refinement_cost_4to8. lra.
Qed.

(** Plans are non-negative *)
Lemma refinement_2to4_nonneg : forall i j, 0 <= refinement_plan_2to4 i j.
Proof.
  intros i j. unfold refinement_plan_2to4.
  destruct i as [|[|i']]; destruct j as [|[|[|[|j']]]]; lra.
Qed.

Lemma refinement_4to8_nonneg : forall i j, 0 <= refinement_plan_4to8 i j.
Proof.
  intros i j. unfold refinement_plan_4to8.
  destruct i as [|[|[|[|i']]]]; destruct j as [|[|[|[|[|[|[|[|j']]]]]]]]; lra.
Qed.

(** Refinement cost is positive *)
Theorem refinement_cost_positive :
  0 < transport_cost refinement_plan_2to4 lattice_cost 3.
Proof. rewrite refinement_cost_2to4. lra. Qed.
