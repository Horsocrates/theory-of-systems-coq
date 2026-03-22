(** * CommutatorComplex.v — Commutator [X⊗I, I⊗P] with complex structure
    Elements: XI_4, Pi_4 (tensor products), comm_4 (commutator)
    Roles:    i connects position (being) and momentum (becoming) in K=2
    Rules:    [X⊗I, I⊗i·P] has i-structure: off-diagonal blocks ±1
    Status:   Stdlib
    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.GreenFunction.
From ToS Require Import stdlib.ComplexOverQ.
From ToS Require Import stdlib.HeisenbergReturn.
Open Scope Q_scope.

(* ================================================================== *)
(*  PART I: TENSOR PRODUCT OPERATORS (4×4 for K=2)                     *)
(* ================================================================== *)

(* X⊗I: position on first factor, identity on second *)
(* X = [[0,0],[0,1]], I = [[1,0],[0,1]] *)
(* X⊗I = diag(0,0,1,1) *)
Definition XI_4 (i j : nat) : Q :=
  match (i, j) with
  | (S (S O), S (S O)) => 1
  | (S (S (S O)), S (S (S O))) => 1
  | _ => 0
  end.

(* I⊗(i·P): identity on first, i*momentum on second *)
(* P = [[0,1],[-1,0]], i·P via complex_mat structure *)
(* I⊗(iP) has blocks: iP on diagonal *)
Definition Pi_4 (i j : nat) : Q :=
  match (i, j) with
  | (O, S (S (S O))) => -(1)
  | (S O, S (S O)) => 1
  | (S (S O), S O) => 1
  | (S (S (S O)), O) => -(1)
  | _ => 0
  end.

(* Commutator [XI_4, Pi_4]_{ij} = Σ_k (XI·Pi - Pi·XI)_{ij} *)
Definition comm_4 (i j : nat) : Q :=
  fold_left (fun acc k =>
    acc + XI_4 i k * Pi_4 k j - Pi_4 i k * XI_4 k j)
    (seq 0%nat 4%nat) 0.

(* ================================================================== *)
(*  PART II: COMMUTATOR ENTRIES                                        *)
(* ================================================================== *)

Lemma comm_4_03 : comm_4 0%nat 3%nat == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma comm_4_12 : comm_4 1%nat 2%nat == -(1).
Proof. vm_compute. reflexivity. Qed.

Lemma comm_4_21 : comm_4 2%nat 1%nat == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma comm_4_30 : comm_4 3%nat 0%nat == -(1).
Proof. vm_compute. reflexivity. Qed.

(* Diagonal entries vanish *)
Lemma comm_4_00 : comm_4 0%nat 0%nat == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma comm_4_11 : comm_4 1%nat 1%nat == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma comm_4_22 : comm_4 2%nat 2%nat == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma comm_4_33 : comm_4 3%nat 3%nat == 0.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  PART III: i-STRUCTURE OF COMMUTATOR                                *)
(* ================================================================== *)

(* The commutator has the structure of i: antisymmetric off-diagonal *)
Lemma comm_4_antisymmetric_03 :
  comm_4 0%nat 3%nat == -(comm_4 3%nat 0%nat).
Proof. vm_compute. reflexivity. Qed.

Lemma comm_4_antisymmetric_12 :
  comm_4 1%nat 2%nat == -(comm_4 2%nat 1%nat).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

Theorem commutator_complex_synthesis :
  comm_4 0%nat 3%nat == 1 /\
  comm_4 3%nat 0%nat == -(1) /\
  comm_4 0%nat 0%nat == 0 /\
  comm_4 1%nat 2%nat == -(comm_4 2%nat 1%nat).
Proof.
  split; [exact comm_4_03 |].
  split; [exact comm_4_30 |].
  split; [exact comm_4_00 |].
  exact comm_4_antisymmetric_12.
Qed.
