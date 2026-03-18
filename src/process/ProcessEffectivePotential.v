(** * ProcessEffectivePotential.v — Effective Potential on Regge Lattice

    Theory of Systems — Step 6: Unrealized Potential (File 2)

    Elements: V_eff, effective potential at several radii
    Roles:    Schwarzschild effective potential V_eff(r) = -M/r + L^2/(2r^2) - ML^2/r^3
    Rules:    All computations over Q, concrete values at r=15,20,30,50
    Status:   complete

    STATUS: 10 Qed, 0 Admitted
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessSchwarzschildRegge.

(* ================================================================== *)
(*  Part I: Effective potential definition  (~3 lemmas)               *)
(* ================================================================== *)

(** V_eff(r) = -M/r + L^2/(2r^2) - M*L^2/r^3
    With M=1 (mass), L=5 (angular momentum), r as Q *)

Definition V_eff (r : Q) : Q :=
  -(1) / r + (25#1) / (2 * r * r) - (25#1) / (r * r * r).

(** V_eff is well-defined for positive r (just a Q expression) *)

Lemma V_eff_at_15 : V_eff 15 == -((1#54)).
Proof.
  unfold V_eff. field.
Qed.

Lemma V_eff_at_20 : V_eff 20 == -((7#320)).
Proof.
  unfold V_eff. field.
Qed.

Lemma V_eff_at_30 : V_eff 30 == -((11#540)).
Proof.
  unfold V_eff. field.
Qed.

(* ================================================================== *)
(*  Part II: Potential values and ordering  (~4 lemmas)               *)
(* ================================================================== *)

Lemma V_eff_at_50 : V_eff 50 == -((19#1250)).
Proof.
  unfold V_eff. field.
Qed.

Lemma V_eff_neg_at_15 : V_eff 15 < 0.
Proof.
  rewrite V_eff_at_15. unfold Qlt; simpl; lia.
Qed.

Lemma V_eff_neg_at_20 : V_eff 20 < 0.
Proof.
  rewrite V_eff_at_20. unfold Qlt; simpl; lia.
Qed.

(** V_eff(20) < V_eff(15): the potential deepens from r=15 to r=20 *)
Lemma V_eff_deeper_at_20 : V_eff 20 < V_eff 15.
Proof.
  rewrite V_eff_at_20. rewrite V_eff_at_15.
  unfold Qlt; simpl. lia.
Qed.

(* ================================================================== *)
(*  Part III: Minimum and summary  (~3 lemmas)                        *)
(* ================================================================== *)

(** V_eff(50) > V_eff(30): potential rises at large r *)
Lemma V_eff_rises_far : V_eff 30 < V_eff 50.
Proof.
  rewrite V_eff_at_30. rewrite V_eff_at_50.
  unfold Qlt; simpl. lia.
Qed.

(** All values are negative and bounded *)
Lemma V_eff_bounded : V_eff 15 > -(1#1) /\ V_eff 50 > -(1#1).
Proof.
  rewrite V_eff_at_15. rewrite V_eff_at_50.
  split; unfold Qlt; simpl; lia.
Qed.

Theorem effective_potential_summary :
  V_eff 20 < V_eff 15 /\
  V_eff 30 < V_eff 50 /\
  V_eff 15 < 0 /\ V_eff 50 < 0.
Proof.
  split; [| split; [| split]].
  - apply V_eff_deeper_at_20.
  - apply V_eff_rises_far.
  - apply V_eff_neg_at_15.
  - rewrite V_eff_at_50. unfold Qlt; simpl; lia.
Qed.

Definition v1_theorem_count := 10%nat.
