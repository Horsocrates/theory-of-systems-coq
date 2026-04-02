(** * WavePropagation.v — Wave propagation from oscillation + coupling
    Elements: wave_step, impulse response, wavefront
    Roles:    oscillation (File 1) + graph coupling → traveling wave
    Rules:    delta(v,t+1) = (2-2c^2)*delta(v,t) + c^2*(delta(v-1)+delta(v+1)) - delta(v,t-1)
    STATUS:   12 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: April 2026

    OSCILLATION + COUPLING = PROPAGATION = SOUND.
    One oscillator alone → vibration (not sound).
    Coupled oscillators on graph → wave that travels.

    The discrete wave equation = Klein-Gordon with m=0.
    Same as LatticeFieldEquations.v but derived here as SOUND.
*)

From Stdlib Require Import QArith Lia ZArith PeanoNat.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ================================================================ *)
(*  WAVE EQUATION ON CHAIN                                           *)
(* ================================================================ *)

(** Wave step: delta(v,t+1) from current and previous *)
Definition wave_step (c_sq : Q) (N : nat)
  (prev curr : nat -> Q) (v : nat) : Q :=
  let left := if (0 <? v)%nat then curr (v - 1)%nat else 0 in
  let right := if (v <? N - 1)%nat then curr (v + 1)%nat else 0 in
  (2 - 2 * c_sq) * curr v + c_sq * (left + right) - prev v.

(** Initial condition: impulse at v=0 *)
Definition impulse (v : nat) : Q :=
  if (v =? 0)%nat then 1 else 0.

Definition zero_field (_ : nat) : Q := 0.

(* ================================================================ *)
(*  IMPULSE PROPAGATES                                               *)
(* ================================================================ *)

(** After 1 step: disturbance reaches v=1 *)
(** Compute wave_step at each vertex *)
Lemma wave_v0 : wave_step (1 # 4) 4 zero_field impulse 0 == 3 # 2.
Proof. unfold wave_step, zero_field, impulse. vm_compute. reflexivity. Qed.

Lemma wave_v1 : wave_step (1 # 4) 4 zero_field impulse 1 == 1 # 4.
Proof. unfold wave_step, zero_field, impulse. vm_compute. reflexivity. Qed.

(** After 1 step: disturbance reaches v=1 (positive displacement) *)
Lemma impulse_propagates : 0 < wave_step (1 # 4) 4 zero_field impulse 1.
Proof. rewrite wave_v1. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  WAVEFRONT IS CAUSAL                                              *)
(* ================================================================ *)

(** After 1 step: v=2 still at rest *)
Lemma wavefront_causal :
  wave_step (1 # 4) 4 zero_field impulse 2 == 0.
Proof.
  unfold wave_step, zero_field, impulse. vm_compute. reflexivity.
Qed.

(** v=3 also at rest *)
Lemma wavefront_causal_3 :
  wave_step (1 # 4) 4 zero_field impulse 3 == 0.
Proof.
  unfold wave_step, zero_field, impulse. vm_compute. reflexivity.
Qed.

(* ================================================================ *)
(*  NO COUPLING = NO PROPAGATION                                     *)
(* ================================================================ *)

(** c^2=0: vertices oscillate independently, no energy transfer *)
Lemma no_coupling_no_propagation :
  wave_step 0 4 zero_field impulse 1 == 0.
Proof.
  unfold wave_step, zero_field, impulse. vm_compute. reflexivity.
Qed.

(** With zero coupling, source stays put *)
Lemma no_coupling_source_stays :
  wave_step 0 4 zero_field impulse 0 == 2.
  (* = (2-0)*1 + 0 - 0 = 2. Source amplified (no damping). *)
Proof.
  unfold wave_step, zero_field, impulse. vm_compute. reflexivity.
Qed.

(* ================================================================ *)
(*  ENERGY DENSITY                                                   *)
(* ================================================================ *)

Definition energy_density (c_sq : Q) (prev curr : nat -> Q) (v : nat) : Q :=
  (curr v - prev v) * (curr v - prev v) / 2 +
  c_sq * (curr v) * (curr v) / 2.

(** Energy at source after impulse *)
Lemma energy_at_source :
  energy_density (1 # 4) zero_field impulse 0 == 5 # 8.
Proof.
  unfold energy_density, zero_field, impulse.
  simpl (0 =? 0)%nat. vm_compute. reflexivity.
Qed.

(** Energy at neighbor before wave arrives *)
Lemma energy_zero_ahead :
  energy_density (1 # 4) zero_field impulse 2 == 0.
Proof.
  unfold energy_density, zero_field, impulse. vm_compute. reflexivity.
Qed.

(* ================================================================ *)
(*  CONCRETE: c^2 = 1/2 (faster propagation)                        *)
(* ================================================================ *)

Lemma wave_v1_fast : wave_step (1 # 2) 4 zero_field impulse 1 == 1 # 2.
Proof. unfold wave_step, zero_field, impulse. vm_compute. reflexivity. Qed.

Lemma fast_propagation : 0 < wave_step (1 # 2) 4 zero_field impulse 1.
Proof. rewrite wave_v1_fast. vm_compute. reflexivity. Qed.

(** Faster coupling → more energy transferred to neighbor *)
Lemma faster_coupling_more_transfer :
  wave_step (1 # 4) 4 zero_field impulse 1 <
  wave_step (1 # 2) 4 zero_field impulse 1.
Proof. rewrite wave_v1, wave_v1_fast. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  SYNTHESIS                                                        *)
(* ================================================================ *)

Theorem wave_propagation_synthesis :
  (* Impulse propagates to neighbor *)
  0 < wave_step (1 # 4) 4 zero_field impulse 1 /\
  (* Wavefront is causal: v=2 still at rest *)
  wave_step (1 # 4) 4 zero_field impulse 2 == 0 /\
  (* No coupling → no propagation *)
  wave_step 0 4 zero_field impulse 1 == 0 /\
  (* Energy at source *)
  energy_density (1 # 4) zero_field impulse 0 == 5 # 8 /\
  (* Faster coupling -> more transfer *)
  wave_step (1 # 4) 4 zero_field impulse 1 <
    wave_step (1 # 2) 4 zero_field impulse 1.
Proof.
  split; [exact impulse_propagates |
  split; [exact wavefront_causal |
  split; [exact no_coupling_no_propagation |
  split; [exact energy_at_source |
  exact faster_coupling_more_transfer]]]].
Qed.
