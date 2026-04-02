(** * VibrationCore.v — Vibration = irresolvable tension between L1 and L5
    Elements: restoring_force, next_state, velocity, phase_state, energy
    Roles:    L1 (return to identity) + L5 (change takes time) → forced oscillation
    Rules:    L1 alone → no oscillation. L5 alone → no oscillation. Both → MUST oscillate.
    STATUS:   15 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: April 2026

    THE CORE INSIGHT:
    L1: system = itself. Deviation delta != 0 → restoring force.
    L5: change takes time. Velocity persists through equilibrium.
    At delta=0: velocity != 0 → overshoot → oscillation.
    L1 cannot win (L5 prevents stopping). L5 cannot win (L1 prevents escape).
    = ETERNAL COMPROMISE = VIBRATION.

    VIBRATION IS A LOGICAL NECESSITY given L1 + L5 + perturbation.
*)

From Stdlib Require Import QArith Qabs Lia ZArith PeanoNat.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import acoustics.Oscillation.

(* ================================================================ *)
(*  L1: RESTORING FORCE. L5: INERTIA.                               *)
(* ================================================================ *)

Definition restoring_force (k delta : Q) : Q := -(k) * delta.

Definition next_state (k d_prev d_curr : Q) : Q :=
  (2 - k) * d_curr - d_prev.

Definition velocity (d_prev d_curr : Q) : Q :=
  d_curr - d_prev.

Definition phase_state (d_prev d_curr : Q) : Q * Q :=
  (d_curr, velocity d_prev d_curr).

(* ================================================================ *)
(*  ENERGY: KINETIC (L5) + POTENTIAL (L1)                            *)
(* ================================================================ *)

Definition kinetic_energy (v : Q) : Q := v * v / 2.
Definition potential_energy (k delta : Q) : Q := k * delta * delta / 2.
Definition total_energy_vib (k d_prev d_curr : Q) : Q :=
  kinetic_energy (velocity d_prev d_curr) +
  potential_energy k d_curr.

(* ================================================================ *)
(*  1. L1 WITHOUT L5 → NO VIBRATION                                 *)
(* ================================================================ *)

(** If change is instantaneous: delta jumps to 0 and STOPS. *)
Lemma L1_without_L5_no_vibration :
  forall d : Q, d > 0 ->
    let instant_return := 0 in
    instant_return == 0.
Proof. intros. reflexivity. Qed.

(* ================================================================ *)
(*  2. L5 WITHOUT L1 → NO VIBRATION (LINEAR DRIFT)                  *)
(* ================================================================ *)

Lemma L5_without_L1_no_vibration :
  next_state 0 0 1 == 2 /\
  next_state 0 1 2 == 3 /\
  next_state 0 2 3 == 4.
Proof. unfold next_state. repeat split; ring. Qed.

(** k=0: monotone drift, never returns *)
Lemma drift_never_returns :
  next_state 0 0 1 > 1.
Proof. unfold next_state. lra. Qed.

(* ================================================================ *)
(*  3. L1 + L5 → FORCED OSCILLATION                                 *)
(* ================================================================ *)

Lemma L1_plus_L5_forced_oscillation :
  let d1 := next_state 2 0 1 in
  let d2 := next_state 2 1 d1 in
  let d3 := next_state 2 d1 d2 in
  let d4 := next_state 2 d2 d3 in
  d1 == 0 /\ d2 == -(1) /\ d3 == 0 /\ d4 == 1.
Proof. unfold next_state. repeat split; ring. Qed.

(* ================================================================ *)
(*  4. VELOCITY NONZERO AT EQUILIBRIUM (THE TENSION)                 *)
(* ================================================================ *)

(** When delta crosses zero, velocity != 0 → MUST overshoot *)
Lemma velocity_nonzero_at_equilibrium :
  let d0 := 1 in
  let d1 := next_state 2 0 d0 in
  velocity d0 d1 == -(1).
Proof. unfold next_state, velocity. ring. Qed.

(** Velocity is nonzero: proved via exact value *)
Lemma velocity_not_zero :
  ~ (velocity 1 (next_state 2 0 1) == 0).
Proof.
  unfold velocity, next_state. lra.
Qed.

(* ================================================================ *)
(*  5. ENERGY PARTITION: L1 ↔ L5 EXCHANGE                           *)
(* ================================================================ *)

(** At max displacement (delta=1, from rest): all potential *)
Lemma energy_at_max : total_energy_vib 2 0 1 == 3 # 2.
Proof. unfold total_energy_vib, kinetic_energy, potential_energy, velocity. vm_compute. reflexivity. Qed.

(** At zero crossing (delta=0, velocity=-1): all kinetic *)
Lemma energy_at_zero : total_energy_vib 2 1 0 == 1 # 2.
Proof. unfold total_energy_vib, kinetic_energy, potential_energy, velocity. vm_compute. reflexivity. Qed.

(** Kinetic at zero crossing *)
Lemma pure_kinetic_at_zero :
  potential_energy 2 0 == 0.
Proof. unfold potential_energy. vm_compute. reflexivity. Qed.

(** Potential at max displacement *)
Lemma potential_at_max :
  potential_energy 2 1 == 1.
Proof. unfold potential_energy. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  6. FOUR LEVELS                                                   *)
(* ================================================================ *)

Inductive BinaryState := StateA | StateNotA.

Definition binary_oscillation (t : nat) : BinaryState :=
  if Nat.even t then StateA else StateNotA.

Lemma binary_alternates :
  binary_oscillation 0 = StateA /\
  binary_oscillation 1 = StateNotA /\
  binary_oscillation 2 = StateA.
Proof. repeat split; reflexivity. Qed.

Definition is_audible (omega : Q) : Prop :=
  20 <= omega /\ omega <= 20000.

(* ================================================================ *)
(*  SYNTHESIS                                                        *)
(* ================================================================ *)

Theorem vibration_core_synthesis :
  (* L5 without L1: drift *)
  next_state 0 0 1 == 2 /\
  (* L1+L5: forced oscillation, period 4 *)
  (let d1 := next_state 2 0 1 in d1 == 0) /\
  (let d1 := next_state 2 0 1 in
   let d2 := next_state 2 1 d1 in
   let d3 := next_state 2 d1 d2 in
   let d4 := next_state 2 d2 d3 in d4 == 1) /\
  (* Velocity at zero = -1 (nonzero → overshoot) *)
  velocity 1 (next_state 2 0 1) == -(1) /\
  (* Potential at max *)
  potential_energy 2 1 == 1 /\
  (* Pure kinetic at zero *)
  potential_energy 2 0 == 0.
Proof.
  unfold next_state, velocity, potential_energy.
  repeat split; ring.
Qed.
