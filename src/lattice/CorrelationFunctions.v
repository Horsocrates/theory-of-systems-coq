(* ========================================================================= *)
(*                     CORRELATION FUNCTIONS                                 *)
(*           Wick's theorem and cluster decomposition on lattice             *)
(*                                                                          *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)        *)
(*                                                                          *)
(*  Author:  Horsocrates | Version: 1.0 (E/R/R) | Date: March 2026         *)
(*                                                                          *)
(*  STATUS: 10 Qed, 0 Admitted, 0 axioms                                   *)
(*                                                                          *)
(* ========================================================================= *)
(*                                                                          *)
(*  E/R/R INTERPRETATION:                                                   *)
(*  =====================                                                   *)
(*                                                                          *)
(*  Correlation functions encode multi-point relationships:                 *)
(*                                                                          *)
(*    Elements = n-point correlators <φ(x1)...φ(xn)>                       *)
(*    Roles    = Wick contractions (pairings), connected parts              *)
(*    Rules    = Wick theorem (sum over pairings), cluster decomposition    *)
(*                                                                          *)
(*  PHYSICAL NOTE (P4):                                                     *)
(*    For a free (Gaussian) field, ALL correlators reduce to products       *)
(*    of 2-point functions via Wick's theorem.                              *)
(*    The connected 4-point function vanishes — this IS the definition     *)
(*    of a free field (no interactions).                                    *)
(*                                                                          *)
(* ========================================================================= *)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* === Wick's theorem for 4-point function === *)

(* 4-point Wick contraction: sum over 3 pairings
   <φ1 φ2 φ3 φ4> = G(1,2)G(3,4) + G(1,3)G(2,4) + G(1,4)G(2,3) *)
Definition wick_4pt (G : nat -> nat -> Q) (x1 x2 x3 x4 : nat) : Q :=
  G x1 x2 * G x3 x4 + G x1 x3 * G x2 x4 + G x1 x4 * G x2 x3.

(* === Combinatorics of pairings === *)

(* Double factorial: (2n-1)!! = number of perfect matchings of 2n points *)
Fixpoint double_factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S O => 1
  | S (S n') => (n * double_factorial n')%nat
  end.

(* Number of pairings of 2n objects = (2n-1)!! *)
Definition num_pairings (n : nat) : nat := double_factorial (2*n - 1).

(* === Propagator for chain-2, m²=1 === *)

(* G(x,y) = 2/3 if x=y, 1/3 if x≠y (from Propagator.v) *)
Definition G_chain2 (x y : nat) : Q :=
  if Nat.eqb x y then 2#3 else 1#3.

(* === Theorems === *)

(* <φ(0)φ(0)φ(1)φ(1)> = G00·G11 + G01·G01 + G01·G01
   = (2/3)(2/3) + (1/3)(1/3) + (1/3)(1/3) = 4/9 + 1/9 + 1/9 = 6/9 = 2/3 *)
Lemma wick_0011 :
  wick_4pt G_chain2 0 0 1 1 == 2#3.
Proof. vm_compute. reflexivity. Qed.

(* <φ(0)φ(1)φ(0)φ(1)> = G01·G01 + G00·G11 + G01·G01
   = (1/3)(1/3) + (2/3)(2/3) + (1/3)(1/3) = 1/9 + 4/9 + 1/9 = 6/9 = 2/3 *)
Lemma wick_0101 :
  wick_4pt G_chain2 0 1 0 1 == 2#3.
Proof. vm_compute. reflexivity. Qed.

(* <φ(0)φ(0)φ(0)φ(0)> = G00·G00 + G00·G00 + G00·G00
   = 3 × (2/3)² = 3 × 4/9 = 12/9 = 4/3 *)
Lemma wick_0000 :
  wick_4pt G_chain2 0 0 0 0 == 4#3.
Proof. vm_compute. reflexivity. Qed.

(* Number of pairings of 4 objects = (4-1)!! = 3!! = 3 *)
Lemma num_pairings_2 :
  num_pairings 2 = 3%nat.
Proof. vm_compute. reflexivity. Qed.

(* Number of pairings of 6 objects = 5!! = 15 *)
Lemma num_pairings_3 :
  num_pairings 3 = 15%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma double_factorial_5 :
  double_factorial 5 = 15%nat.
Proof. vm_compute. reflexivity. Qed.

(* Connected 4-point function vanishes for free field:
   <φ0 φ0 φ1 φ1>_conn = <φ0 φ0 φ1 φ1> - (<φ0 φ0><φ1 φ1> + 2<φ0 φ1>²)
   = 2/3 - (4/9 + 2/9) = 2/3 - 6/9 = 2/3 - 2/3 = 0 *)
Lemma connected_4pt_free_field :
  wick_4pt G_chain2 0 0 1 1 -
  (G_chain2 0 0 * G_chain2 1 1 + 2 * G_chain2 0 1 * G_chain2 0 1) == 0.
Proof. vm_compute. reflexivity. Qed.

(* The cluster decomposition property: Wick = disconnected + connected,
   and for a free field the connected part is zero *)
Lemma wick_is_cluster :
  wick_4pt G_chain2 0 0 1 1 ==
  G_chain2 0 0 * G_chain2 1 1 + 2 * G_chain2 0 1 * G_chain2 0 1.
Proof. vm_compute. reflexivity. Qed.

(* Symmetry: wick is invariant under relabeling 0↔1 *)
Lemma wick_symmetry_01 :
  wick_4pt G_chain2 0 0 1 1 == wick_4pt G_chain2 1 1 0 0.
Proof. vm_compute. reflexivity. Qed.

Lemma correlation_synthesis :
  wick_4pt G_chain2 0 0 1 1 == 2#3 /\
  wick_4pt G_chain2 0 0 0 0 == 4#3 /\
  num_pairings 2 = 3%nat /\
  num_pairings 3 = 15%nat /\
  wick_4pt G_chain2 0 0 1 1 -
    (G_chain2 0 0 * G_chain2 1 1 + 2 * G_chain2 0 1 * G_chain2 0 1) == 0.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.
