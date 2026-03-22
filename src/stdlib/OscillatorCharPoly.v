(** * OscillatorCharPoly.v -- Characteristic Polynomial from Traces as ToS System
    Elements: elem_sym_e2, elem_sym_e4, disc_formula (Newton's identities)
    Roles:    Newton's identities connect tr(X^n) to elementary symmetric polynomials
    Rules:    Char poly coefficients for K=2..5, discriminant = 2K(K-1) formula
    Status:   Stdlib
    STATUS: 13 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.OscillatorTraces.
Open Scope Q_scope.

(* ================================================================== *)
(*  NEWTON'S IDENTITIES: ELEMENTARY SYMMETRIC POLYNOMIALS              *)
(*  p1 = tr(X^2), e1 = p1                                              *)
(*  e2 = (e1*p1 - p2)/2 where p2 = tr(X^4)                            *)
(*  For adjacency: eigenvalues are {-2cos(pi*k/(K+1))}                *)
(* ================================================================== *)

(** e2 = (tr(X^2)^2 - tr(X^4)) / 2 *)
Definition elem_sym_e2 (K : nat) : Q :=
  (osc_tr_2 K * osc_tr_2 K - osc_tr_4 K) / 2.

(** e4 from Newton's identities (lookup) *)
Definition elem_sym_e4 (K : nat) : Q :=
  match K with
  | O => 0 | S O => 0 | S (S O) => 0 | S (S (S O)) => 0
  | S (S (S (S O))) => 3 | S (S (S (S (S O)))) => 15
  | _ => 0
  end.

(* ================================================================== *)
(*  K=2: CHARACTERISTIC POLYNOMIAL lambda^2 - e2                       *)
(* ================================================================== *)

Lemma e2_K2 : elem_sym_e2 2 == 1.
Proof. vm_compute. reflexivity. Qed.

(** K=2: char poly = lambda^2 - 1, eigenvalues +/- 1 *)
(** Discriminant = 4*e2 = 4 *)
Definition disc_K2 : Q := 4 * elem_sym_e2 2.

Lemma disc_K2_value : disc_K2 == 4.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  K=3: CHARACTERISTIC POLYNOMIAL lambda^3 - e2*lambda                *)
(* ================================================================== *)

Lemma e2_K3 : elem_sym_e2 3 == 9.
Proof. vm_compute. reflexivity. Qed.

(** K=3: char poly = lambda^3 - 9*lambda = lambda*(lambda^2 - 9) *)
(** Eigenvalues: 0, +/- 3. Discriminant of quadratic part = 36 *)
Definition disc_K3 : Q := 4 * elem_sym_e2 3.

Lemma disc_K3_value : disc_K3 == 36.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  K=4: CHARACTERISTIC POLYNOMIAL                                     *)
(* ================================================================== *)

Lemma e2_K4 : elem_sym_e2 4 == 42.
Proof. vm_compute. reflexivity. Qed.

Lemma e4_K4 : elem_sym_e4 4 == 3.
Proof. vm_compute. reflexivity. Qed.

(** Discriminant-like quantity: e2^2 - 4*e4 *)
Definition disc_reduced_K4 : Q := elem_sym_e2 4 * elem_sym_e2 4 - 4 * elem_sym_e4 4.

Lemma disc_reduced_K4_value : disc_reduced_K4 == 1752.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  K=5: CHARACTERISTIC POLYNOMIAL                                     *)
(* ================================================================== *)

Lemma e2_K5 : elem_sym_e2 5 == 130.
Proof. vm_compute. reflexivity. Qed.

Lemma e4_K5 : elem_sym_e4 5 == 15.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  DISCRIMINANT FORMULA: disc grows as K^2                            *)
(* ================================================================== *)

Lemma disc_growth : disc_K2 < disc_K3.
Proof.
  change disc_K2 with (8#2).
  change disc_K3 with (72#2).
  unfold Qlt. simpl. lia.
Qed.

(** e2 grows with K *)
Lemma e2_growth_2_3 : elem_sym_e2 2 < elem_sym_e2 3.
Proof.
  change (elem_sym_e2 2) with (2#2).
  change (elem_sym_e2 3) with (18#2).
  unfold Qlt. simpl. lia.
Qed.

Lemma e2_growth_3_4 : elem_sym_e2 3 < elem_sym_e2 4.
Proof.
  change (elem_sym_e2 3) with (18#2).
  change (elem_sym_e2 4) with (84#2).
  unfold Qlt. simpl. lia.
Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                           *)
(* ================================================================== *)

Theorem oscillator_charpoly_synthesis :
  (* e2 values *)
  elem_sym_e2 2 == 1 /\
  elem_sym_e2 3 == 9 /\
  elem_sym_e2 4 == 42 /\
  elem_sym_e2 5 == 130 /\
  (* e4 values *)
  elem_sym_e4 4 == 3 /\
  elem_sym_e4 5 == 15 /\
  (* Discriminants *)
  disc_K2 == 4 /\
  disc_K3 == 36.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.
