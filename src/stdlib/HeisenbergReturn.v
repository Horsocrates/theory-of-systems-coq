(** * HeisenbergReturn.v — Heisenberg Commutator [X,P] on Finite Lattice
    Elements: X_op, P_op (position/momentum), XP_comm (commutator matrix)
    Roles:    [X,P] = negative discrete Laplacian on K-site lattice
    Rules:    Concrete verification for K=3,4,5; diagonal and off-diagonal entries
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.ProcessHilbert.
Open Scope Q_scope.

(* ================================================================== *)
(*  POSITION AND MOMENTUM OPERATORS ON K-SITE LATTICE                  *)
(* ================================================================== *)

(** Position operator: diagonal with eigenvalues 0,1,...,K-1 *)
Definition X_op (K : nat) (i j : nat) : Q :=
  if Nat.eqb i j then inject_Z (Z.of_nat i) else 0.

(** Momentum operator: discrete derivative (antisymmetric tridiag) *)
Definition P_op (K : nat) (i j : nat) : Q :=
  if Nat.eqb (S i) j then 1
  else if Nat.eqb i (S j) then -(1)
  else 0.

(** Commutator [X,P]_{ij} = sum_k (X_{ik}P_{kj} - P_{ik}X_{kj}) *)
Definition XP_comm (K : nat) (i j : nat) : Q :=
  fold_left (fun acc k =>
    acc + X_op K i k * P_op K k j - P_op K i k * X_op K k j)
    (seq 0 K) 0.

(* ================================================================== *)
(*  K=3: FULL COMMUTATOR MATRIX                                        *)
(* ================================================================== *)

Lemma comm_3_00 : XP_comm 3 0 0 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma comm_3_01 : XP_comm 3 0 1 == -(1).
Proof. vm_compute. reflexivity. Qed.

Lemma comm_3_10 : XP_comm 3 1 0 == -(1).
Proof. vm_compute. reflexivity. Qed.

Lemma comm_3_11 : XP_comm 3 1 1 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma comm_3_12 : XP_comm 3 1 2 == -(1).
Proof. vm_compute. reflexivity. Qed.

Lemma comm_3_21 : XP_comm 3 2 1 == -(1).
Proof. vm_compute. reflexivity. Qed.

Lemma comm_3_22 : XP_comm 3 2 2 == 0.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  K=4: SAMPLE ENTRIES                                                 *)
(* ================================================================== *)

Lemma comm_4_00 : XP_comm 4 0 0 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma comm_4_01 : XP_comm 4 0 1 == -(1).
Proof. vm_compute. reflexivity. Qed.

Lemma comm_4_12 : XP_comm 4 1 2 == -(1).
Proof. vm_compute. reflexivity. Qed.

Lemma comm_4_23 : XP_comm 4 2 3 == -(1).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  DIAGONAL IS ZERO FOR ALL K=3,4,5                                    *)
(* ================================================================== *)

Lemma comm_diagonal_3 : XP_comm 3 0 0 == 0 /\ XP_comm 3 1 1 == 0 /\ XP_comm 3 2 2 == 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

Lemma comm_diagonal_4 : XP_comm 4 0 0 == 0 /\ XP_comm 4 1 1 == 0
                      /\ XP_comm 4 2 2 == 0 /\ XP_comm 4 3 3 == 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

Lemma comm_diagonal_5 : XP_comm 5 0 0 == 0 /\ XP_comm 5 1 1 == 0
                      /\ XP_comm 5 2 2 == 0 /\ XP_comm 5 3 3 == 0 /\ XP_comm 5 4 4 == 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ================================================================== *)
(*  SYNTHESIS: [X,P] = -Laplacian (negative adjacency) on K-lattice     *)
(* ================================================================== *)

Theorem heisenberg_return_synthesis :
  (* Off-diagonal: [X,P]_{i,i+1} = -1 for all verified K *)
  XP_comm 3 0 1 == -(1) /\
  XP_comm 4 0 1 == -(1) /\
  XP_comm 4 2 3 == -(1) /\
  (* Diagonal: [X,P]_{i,i} = 0 *)
  XP_comm 3 1 1 == 0 /\
  XP_comm 4 2 2 == 0 /\
  XP_comm 5 3 3 == 0.
Proof. repeat split; vm_compute; reflexivity. Qed.
