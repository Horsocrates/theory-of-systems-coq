(* DivisibilityGraph.v *)
(* Arithmetic Heisenberg: Divisibility graph structure *)
(* E/R/R: Elements = natural numbers, Roles = divisibility/successor,
   Rules = adjacency in multiplicative and additive graphs *)

From Coq Require Import QArith.
From Coq Require Import Lia.
From Coq Require Import Lra.
From Coq Require Import Arith.

(* === Definitions (before Q_scope) === *)

Definition divides (a b : nat) : bool := Nat.eqb (b mod a) 0.

Definition mult_adj (i j : nat) : Q :=
  let n := S i in let m := S j in
  if Nat.eqb n m then 0
  else if orb (divides n m) (divides m n) then 1
  else 0.

Definition add_adj (i j : nat) : Q :=
  if Nat.eqb (S i) j then 1
  else if Nat.eqb i (S j) then 1
  else 0.

Open Scope Q_scope.

(* === Hub property: 1 divides everything === *)

Lemma one_hub_1 : mult_adj 0 1 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma one_hub_4 : mult_adj 0 4 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma one_hub_9 : mult_adj 0 9 == 1.
Proof. vm_compute. reflexivity. Qed.

(* === Divisibility examples === *)

Lemma prime_div : mult_adj 1 3 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma no_div : mult_adj 1 2 == 0.
Proof. vm_compute. reflexivity. Qed.

(* === Additive chain === *)

Lemma chain_01 : add_adj 0 1 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma chain_12 : add_adj 1 2 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma chain_not : add_adj 0 2 == 0.
Proof. vm_compute. reflexivity. Qed.

(* === Symmetry === *)

Lemma mult_symmetric_2_4 : mult_adj 1 3 == mult_adj 3 1.
Proof. vm_compute. reflexivity. Qed.

(* === Degree counting === *)

(* Degree of node 1 in K_5 subgraph (nodes 1..5): 1 connects to 2,3,4,5 *)
Lemma degree_one_5 :
  mult_adj 0 1 + mult_adj 0 2 + mult_adj 0 3 + mult_adj 0 4 == 4.
Proof. vm_compute. reflexivity. Qed.

(* Degree of node 2 in K_6 subgraph (nodes 1..6):
   2 connects to 1 (1|2), 4 (2|4), 6 (2|6) = degree 3 *)
Lemma degree_two_6 :
  mult_adj 1 0 + mult_adj 1 2 + mult_adj 1 3 + mult_adj 1 4 + mult_adj 1 5 == 3.
Proof. vm_compute. reflexivity. Qed.

(* === Additional structural lemmas === *)

Lemma one_hub_2 : mult_adj 0 2 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma one_hub_3 : mult_adj 0 3 == 1.
Proof. vm_compute. reflexivity. Qed.

(* 3 divides 6: mult_adj 2 5 == 1 (i=2→n=3, j=5→m=6) *)
Lemma three_divides_six : mult_adj 2 5 == 1.
Proof. vm_compute. reflexivity. Qed.

(* 5 and 7 are coprime: mult_adj 4 6 == 0 *)
Lemma coprime_5_7 : mult_adj 4 6 == 0.
Proof. vm_compute. reflexivity. Qed.

(* Additive chain is path: consecutive nodes connected *)
Lemma chain_23 : add_adj 2 3 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma chain_34 : add_adj 3 4 == 1.
Proof. vm_compute. reflexivity. Qed.

(* Self-adjacency is 0 in both graphs *)
Lemma mult_no_self : mult_adj 0 0 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma add_no_self : add_adj 0 0 == 0.
Proof. vm_compute. reflexivity. Qed.
