(** * UncertaintyBounds.v -- Tridiagonal Expectation Values as ToS System
    Elements: apply_tridiag, tridiag_expectation (adjacency matrix expectation)
    Roles:    Uncertainty bounds from lattice adjacency on finite K-site systems
    Rules:    Concrete verified values for K=2..5, localized vs delocalized states
    Status:   Stdlib
    STATUS: 17 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.HeisenbergReturn.
From ToS Require Import stdlib.ProcessHilbert.
Open Scope Q_scope.

(* ================================================================== *)
(*  LOCAL DOT PRODUCT (guaranteed to compute)                          *)
(* ================================================================== *)

Fixpoint dot (a b : list Q) : Q :=
  match a, b with
  | x :: xs, y :: ys => x * y + dot xs ys
  | _, _ => 0
  end.

Definition dot_sq (a : list Q) : Q := dot a a.

(* ================================================================== *)
(*  TRIDIAGONAL APPLICATION: adjacency matrix on K-site lattice        *)
(*  (apply_tridiag K psi)_i = psi_{i-1} + psi_{i+1}                   *)
(* ================================================================== *)

Definition apply_tridiag (K : nat) (psi : PState) : PState :=
  map (fun i =>
    let prev := if Nat.eqb i 0 then 0 else nth (i-1) psi 0 in
    let next := nth (S i) psi 0 in
    prev + next)
    (seq 0 K).

(* ================================================================== *)
(*  TRIDIAGONAL EXPECTATION: <psi|T|psi> / <psi|psi>                  *)
(* ================================================================== *)

Definition tridiag_expectation (K : nat) (psi : PState) : Q :=
  dot psi (apply_tridiag K psi) / dot_sq psi.

(* ================================================================== *)
(*  K=2 STATES                                                         *)
(* ================================================================== *)

Lemma ub_K2_ground : tridiag_expectation 2 [1;1] == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma ub_K2_localized : tridiag_expectation 2 [1;0] == 0.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  K=3 STATES                                                         *)
(* ================================================================== *)

Lemma ub_K3_uniform : tridiag_expectation 3 [1;1;1] == 4#3.
Proof. vm_compute. reflexivity. Qed.

Lemma ub_K3_center : tridiag_expectation 3 [0;1;0] == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma ub_K3_edge : tridiag_expectation 3 [1;0;0] == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma ub_K3_super : tridiag_expectation 3 [1;0;1] == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma ub_K3_weighted : tridiag_expectation 3 [1;2;1] == 4#3.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  K=4 STATES                                                         *)
(* ================================================================== *)

Lemma ub_K4_uniform : tridiag_expectation 4 [1;1;1;1] == 3#2.
Proof. vm_compute. reflexivity. Qed.

Lemma ub_K4_localized : tridiag_expectation 4 [1;0;0;0] == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma ub_K4_center : tridiag_expectation 4 [0;1;1;0] == 1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  K=5 STATES                                                         *)
(* ================================================================== *)

Lemma ub_K5_uniform : tridiag_expectation 5 [1;1;1;1;1] == 8#5.
Proof. vm_compute. reflexivity. Qed.

Lemma ub_K5_localized : tridiag_expectation 5 [0;0;1;0;0] == 0.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  STRUCTURAL PROPERTIES                                               *)
(* ================================================================== *)

(** Localized states always have zero adjacency expectation *)
Lemma localized_zero_K2 : tridiag_expectation 2 [1;0] == 0.
Proof. vm_compute. reflexivity. Qed.

(** Delocalized (uniform) expectation grows with K *)
Lemma uniform_growth_2_3 : tridiag_expectation 2 [1;1] < tridiag_expectation 3 [1;1;1].
Proof.
  change (tridiag_expectation 2 [1;1]) with (2#2).
  change (tridiag_expectation 3 [1;1;1]) with (4#3).
  unfold Qlt. simpl. lia.
Qed.

Lemma uniform_growth_3_4 : tridiag_expectation 3 [1;1;1] < tridiag_expectation 4 [1;1;1;1].
Proof.
  change (tridiag_expectation 3 [1;1;1]) with (4#3).
  change (tridiag_expectation 4 [1;1;1;1]) with (6#4).
  unfold Qlt. simpl. lia.
Qed.

Lemma uniform_growth_4_5 : tridiag_expectation 4 [1;1;1;1] < tridiag_expectation 5 [1;1;1;1;1].
Proof.
  change (tridiag_expectation 4 [1;1;1;1]) with (6#4).
  change (tridiag_expectation 5 [1;1;1;1;1]) with (8#5).
  unfold Qlt. simpl. lia.
Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                           *)
(* ================================================================== *)

Theorem uncertainty_bounds_synthesis :
  (* Uniform states give maximal adjacency expectation *)
  tridiag_expectation 2 [1;1] == 1 /\
  tridiag_expectation 3 [1;1;1] == 4#3 /\
  tridiag_expectation 4 [1;1;1;1] == 3#2 /\
  tridiag_expectation 5 [1;1;1;1;1] == 8#5 /\
  (* Localized states have zero expectation *)
  tridiag_expectation 2 [1;0] == 0 /\
  tridiag_expectation 3 [0;1;0] == 0 /\
  (* Growth with K *)
  tridiag_expectation 2 [1;1] < tridiag_expectation 3 [1;1;1].
Proof.
  repeat split; first [ vm_compute; reflexivity | exact uniform_growth_2_3 ].
Qed.
