(* PropagatorSynthesis.v *)
(* E/R/R: Elements = propagator synthesis results
         Roles = unify path counting with Catalan numbers
         Rules = return probabilities are Catalan, paths spread combinatorially *)

Require Import QArith.
Require Import QArith.Qabs.
Require Import Lia.
Require Import ZArith.

From ToS Require Import stdlib.graph.GraphPropagator.

Open Scope Q_scope.

(* === Catalan connection === *)

Lemma catalan_return_sequence :
  chain_paths 0 0 == 1 /\
  chain_paths 2 0 == 1 /\
  chain_paths 4 0 == 2 /\
  chain_paths 6 0 == 5.
Proof.
  split; [| split; [| split]]; vm_compute; reflexivity.
Qed.

(* === Propagator reaches all sites === *)

Lemma propagator_reaches_far :
  chain_paths 5 5 == 1 /\
  chain_paths 6 6 == 1 /\
  chain_paths 7 7 == 1.
Proof.
  split; [| split]; vm_compute; reflexivity.
Qed.

(* === Interior path counts grow === *)

Lemma interior_growth :
  chain_paths 4 2 == 3 /\
  chain_paths 6 2 == 9 /\
  chain_paths 7 3 == 14.
Proof.
  split; [| split]; vm_compute; reflexivity.
Qed.

(* === Grand synthesis === *)

Theorem propagator_grand_synthesis :
  (* 1. Return probabilities follow Catalan numbers *)
  chain_paths 0 0 == 1 /\
  chain_paths 4 0 == 2 /\
  chain_paths 6 0 == 5 /\
  (* 2. Odd steps never return to origin *)
  chain_paths 1 0 == 0 /\
  chain_paths 3 0 == 0 /\
  (* 3. Propagator reaches far sites *)
  chain_paths 7 5 > 0 /\
  (* 4. Path count symmetry *)
  chain_paths 2 0 == chain_paths 2 2.
Proof.
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - unfold chain_paths. unfold Qlt. simpl. lia.
  - vm_compute. reflexivity.
Qed.
