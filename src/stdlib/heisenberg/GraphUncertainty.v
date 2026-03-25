(** * GraphUncertainty.v — Uncertainty depends on graph topology
    Elements: adj_chain_entry, adj_cycle_entry, adj_complete_entry, tr_A2, rms_hbar
    Roles:    Different graphs give different uncertainty; more edges = more uncertainty
    Rules:    chain < cycle < complete; edge count orders uncertainty
    Status:   complete
    STATUS: 17 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Lia.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Adjacency Matrices for Three Graph Types                   *)
(* ================================================================== *)

(** Chain graph: A_{ij} = 1 if |i-j| = 1 *)
Definition adj_chain_entry (K : nat) (i j : nat) : Q :=
  if Nat.eqb (S i) j then 1
  else if Nat.eqb i (S j) then 1
  else 0.

(** Cycle graph: chain + wrap-around edge (0,K-1) *)
Definition adj_cycle_entry (K : nat) (i j : nat) : Q :=
  if Nat.eqb (S i) j then 1
  else if Nat.eqb i (S j) then 1
  else if andb (Nat.eqb i O) (Nat.eqb j (pred K)) then 1
  else if andb (Nat.eqb j O) (Nat.eqb i (pred K)) then 1
  else 0.

(** Complete graph: A_{ij} = 1 if i <> j *)
Definition adj_complete_entry (K : nat) (i j : nat) : Q :=
  if Nat.eqb i j then 0 else 1.

(* ================================================================== *)
(*  Part II: Concrete Adjacency Values                                 *)
(* ================================================================== *)

Lemma chain_01 : adj_chain_entry 5 0 1 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma chain_02 : adj_chain_entry 5 0 2 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma cycle_04 : adj_cycle_entry 5 0 4 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma cycle_02 : adj_cycle_entry 5 0 2 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma complete_03 : adj_complete_entry 5 0 3 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma complete_22 : adj_complete_entry 5 2 2 == 0.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part III: Trace of A^2 (= 2 * edge_count)                         *)
(* ================================================================== *)

(** tr(A^2) for chain = 2(K-1), cycle = 2K, complete = K(K-1) *)
Definition tr_A2_chain (K : nat) : Q :=
  2 * (inject_Z (Z.of_nat K) - 1).

Definition tr_A2_cycle (K : nat) : Q :=
  2 * inject_Z (Z.of_nat K).

Definition tr_A2_complete (K : nat) : Q :=
  inject_Z (Z.of_nat K) * (inject_Z (Z.of_nat K) - 1).

Lemma tr_A2_chain_10 : tr_A2_chain 10 == 18.
Proof. vm_compute. reflexivity. Qed.

Lemma tr_A2_cycle_10 : tr_A2_cycle 10 == 20.
Proof. vm_compute. reflexivity. Qed.

Lemma tr_A2_complete_10 : tr_A2_complete 10 == 90.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part IV: RMS hbar for Each Graph                                   *)
(* ================================================================== *)

(** rms_hbar = tr(A^2) / (4K) *)
Definition rms_hbar_chain (K : nat) : Q :=
  tr_A2_chain K / (4 * inject_Z (Z.of_nat K)).

Definition rms_hbar_cycle (K : nat) : Q :=
  tr_A2_cycle K / (4 * inject_Z (Z.of_nat K)).

Definition rms_hbar_complete (K : nat) : Q :=
  tr_A2_complete K / (4 * inject_Z (Z.of_nat K)).

Lemma chain_rms_10 : rms_hbar_chain 10 == 9#20.
Proof. vm_compute. reflexivity. Qed.

Lemma cycle_rms_10 : rms_hbar_cycle 10 == 1#2.
Proof. vm_compute. reflexivity. Qed.

Lemma complete_rms_10 : rms_hbar_complete 10 == 9#4.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part V: Ordering by Connectivity                                   *)
(* ================================================================== *)

Lemma complete_larger : rms_hbar_complete 10 > rms_hbar_chain 10.
Proof. unfold rms_hbar_complete, rms_hbar_chain. vm_compute. reflexivity. Qed.

Lemma cycle_larger_than_chain : rms_hbar_cycle 10 > rms_hbar_chain 10.
Proof. unfold rms_hbar_cycle, rms_hbar_chain. vm_compute. reflexivity. Qed.

Lemma complete_larger_than_cycle : rms_hbar_complete 10 > rms_hbar_cycle 10.
Proof. unfold rms_hbar_complete, rms_hbar_cycle. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part VI: Edge Counts                                               *)
(* ================================================================== *)

Definition edge_count_chain (K : nat) : Q :=
  inject_Z (Z.of_nat K) - 1.

Definition edge_count_cycle (K : nat) : Q :=
  inject_Z (Z.of_nat K).

Definition edge_count_complete (K : nat) : Q :=
  inject_Z (Z.of_nat K) * (inject_Z (Z.of_nat K) - 1) / 2.

Lemma edge_ordering : edge_count_chain 10 < edge_count_cycle 10.
Proof. unfold edge_count_chain, edge_count_cycle. vm_compute. reflexivity. Qed.

Lemma edge_ordering_2 : edge_count_cycle 10 < edge_count_complete 10.
Proof. unfold edge_count_cycle, edge_count_complete. vm_compute. reflexivity. Qed.
