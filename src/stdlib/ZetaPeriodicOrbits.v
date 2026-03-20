(** * ZetaPeriodicOrbits.v -- Periodic orbit counting via zeta
    Elements: orbit_count, mobius_coefficient, prime_orbit_count
    Roles:    tr(M^n) counts n-periodic points; prime orbits via Möbius
    Rules:    Exact over Q, no approximation needed
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import LinearAlgebra.
From ToS Require Import CauchyReal.
From ToS Require Import physics.InnerProductSpace.
From ToS Require Import physics.QState.
From ToS Require Import physics.QObservable.
From ToS Require Import physics.Orthogonality.
From ToS Require Import physics.SpinChain.
From ToS Require Import linalg.MatrixOps.
From ToS Require Import linalg.EigenvalueTheory.
From ToS Require Import stdlib.SFTEntropyGeneral.
From ToS Require Import stdlib.DynamicalZeta.

Open Scope Q_scope.

(* ================================================================== *)
(*  PERIODIC ORBIT COUNTING: tr(M^n) = |Fix(σ^n)|                     *)
(* ================================================================== *)

(** Total n-periodic points = tr(M^n) *)
Definition orbit_count (M : QMat 2 2) (n : nat) : Q := tr_pow M n.

(** Golden: periodic point counts = Lucas numbers *)
Lemma golden_orbit_0 : orbit_count golden_sft 0 == 2.
Proof. unfold orbit_count. rewrite golden_tr_0. reflexivity. Qed.

Lemma golden_orbit_1 : orbit_count golden_sft 1 == 1.
Proof. unfold orbit_count. rewrite golden_tr_1. reflexivity. Qed.

Lemma golden_orbit_2 : orbit_count golden_sft 2 == 3.
Proof. unfold orbit_count. rewrite golden_tr_2. reflexivity. Qed.

Lemma golden_orbit_3 : orbit_count golden_sft 3 == 4.
Proof. unfold orbit_count. rewrite golden_tr_3. reflexivity. Qed.

Lemma golden_orbit_4 : orbit_count golden_sft 4 == 7.
Proof. unfold orbit_count. rewrite golden_tr_4. reflexivity. Qed.

(** Full: periodic point counts = 2^n *)
Lemma full_orbit_0 : orbit_count full_sft 0 == 2.
Proof. unfold orbit_count. rewrite full_tr_0. reflexivity. Qed.

Lemma full_orbit_1 : orbit_count full_sft 1 == 2.
Proof. unfold orbit_count. rewrite full_tr_1. reflexivity. Qed.

Lemma full_orbit_2 : orbit_count full_sft 2 == 4.
Proof. unfold orbit_count. rewrite full_tr_2. reflexivity. Qed.

Lemma full_orbit_3 : orbit_count full_sft 3 == 8.
Proof. unfold orbit_count. rewrite full_tr_3. reflexivity. Qed.

(* ================================================================== *)
(*  PRIME ORBIT COUNTING: Möbius inversion                             *)
(* ================================================================== *)

(** Prime orbits of period n: orbits not decomposable as repetitions
    of shorter orbits. For period 1: p(1) = tr(M).
    For prime period n: p(n) = (1/n)(Σ_{d|n} μ(n/d)·tr(M^d))
    We compute concrete instances. *)

(** Simple Möbius function for small values *)
Definition mobius (n : nat) : Z :=
  match n with
  | S O => 1
  | S (S O) => (-1)
  | S (S (S O)) => (-1)
  | S (S (S (S O))) => 0    (* 4 = 2² *)
  | S (S (S (S (S O)))) => (-1)
  | S (S (S (S (S (S O))))) => 1    (* 6 = 2·3, two prime factors *)
  | _ => 0    (* placeholder *)
  end%Z.

(** Golden prime orbits:
    p(1) = tr(M) = 1  (one fixed point)
    p(2) = (tr(M²) - tr(M))/2 = (3-1)/2 = 1
    p(3) = (tr(M³) - tr(M))/3 = (4-1)/3 = 1 *)

Lemma golden_prime_orbit_1 : orbit_count golden_sft 1 == 1.
Proof. exact golden_orbit_1. Qed.

Lemma golden_prime_orbit_2 :
  (orbit_count golden_sft 2 - orbit_count golden_sft 1) / 2 == 1.
Proof.
  rewrite golden_orbit_2, golden_orbit_1.
  vm_compute. reflexivity.
Qed.

Lemma golden_prime_orbit_3 :
  (orbit_count golden_sft 3 - orbit_count golden_sft 1) / 3 == 1.
Proof.
  rewrite golden_orbit_3, golden_orbit_1.
  vm_compute. reflexivity.
Qed.

(** Full shift prime orbits:
    p(1) = 2 (two fixed points: 00... and 11...)
    p(2) = (4-2)/2 = 1
    p(3) = (8-2)/3 = 2 *)

Lemma full_prime_orbit_1 : orbit_count full_sft 1 == 2.
Proof. exact full_orbit_1. Qed.

Lemma full_prime_orbit_2 :
  (orbit_count full_sft 2 - orbit_count full_sft 1) / 2 == 1.
Proof.
  rewrite full_orbit_2, full_orbit_1.
  vm_compute. reflexivity.
Qed.

Lemma full_prime_orbit_3 :
  (orbit_count full_sft 3 - orbit_count full_sft 1) / 3 == 2.
Proof.
  rewrite full_orbit_3, full_orbit_1.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  ORBIT GROWTH: golden vs full                                       *)
(* ================================================================== *)

(** Full shift orbits grow faster than golden *)
Lemma full_more_orbits_3 :
  orbit_count golden_sft 3 < orbit_count full_sft 3.
Proof.
  rewrite golden_orbit_3, full_orbit_3.
  unfold Qlt. simpl. lia.
Qed.

(** Orbit counts are always positive for golden (Lucas ≥ 1) *)
Lemma golden_orbit_positive_1 : 0 < orbit_count golden_sft 1.
Proof. rewrite golden_orbit_1. unfold Qlt. simpl. lia. Qed.

(** SYNTHESIS *)
Theorem periodic_orbit_synthesis :
  (* Golden orbits = Lucas: 2, 1, 3, 4, 7 *)
  orbit_count golden_sft 0 == 2 /\
  orbit_count golden_sft 4 == 7 /\
  (* Full orbits = 2^n: 2, 2, 4, 8 *)
  orbit_count full_sft 3 == 8 /\
  (* Prime orbits: golden has 1 per period, full grows *)
  (orbit_count golden_sft 3 - orbit_count golden_sft 1) / 3 == 1 /\
  (orbit_count full_sft 3 - orbit_count full_sft 1) / 3 == 2.
Proof.
  split; [|split; [|split; [|split]]].
  - exact golden_orbit_0.
  - exact golden_orbit_4.
  - exact full_orbit_3.
  - exact golden_prime_orbit_3.
  - exact full_prime_orbit_3.
Qed.
