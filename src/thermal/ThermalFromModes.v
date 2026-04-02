(** * ThermalFromModes.v — Temperature and entropy from vibration mode distribution
    Elements: ModeState, mode_energy, temperature, energy_variance, active_modes
    Roles:    ONE mode excited = pure tone = low entropy; ALL = noise = high entropy
    Rules:    Temperature = energy/modes. Entropy ~ #active modes. Derived from L1-L5.
    STATUS:   12 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: April 2026

    THERMAL = DISTRIBUTED L1-L5 TENSION.
    Pure tone: tension concentrated in one mode → structured, ordered.
    Noise: tension distributed across all modes → unstructured, disordered.
    Temperature = average tension per mode.
    Entropy = "how evenly is tension distributed?"
*)

From Stdlib Require Import QArith Qabs Lia ZArith List PeanoNat.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================ *)
(*  MODE ENERGY                                                      *)
(* ================================================================ *)

Fixpoint total_energy_modes (omegas amplitudes : list Q) : Q :=
  match omegas, amplitudes with
  | w :: ws, a :: as_ => a * a * w + total_energy_modes ws as_
  | _, _ => 0
  end.

Definition temperature (total_E : Q) (N : nat) : Q :=
  total_E / inject_Z (Z.of_nat N).

(* ================================================================ *)
(*  PURE TONE vs THERMAL STATE                                       *)
(* ================================================================ *)

Definition pure_tone_4 : list Q := [2; 0; 0; 0].
Definition thermal_4 : list Q := [1; 1; 1; 1].
Definition omega_4 : list Q := [1; 1; 1; 1].

(** Active modes: count amplitudes above threshold *)
Fixpoint active_modes_aux (amps : list Q) (thr : Q) : nat :=
  match amps with
  | nil => 0%nat
  | a :: rest =>
    let cnt := active_modes_aux rest thr in
    if Qlt_le_dec thr (Qabs a) then (1 + cnt)%nat else cnt
  end.

Definition active_modes (amps : list Q) (thr : Q) : nat :=
  active_modes_aux amps thr.

(* ================================================================ *)
(*  ENTROPY: PURE TONE LOW, THERMAL HIGH                             *)
(* ================================================================ *)

Lemma pure_tone_one_active :
  active_modes pure_tone_4 (1 # 10) = 1%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma thermal_all_active :
  active_modes thermal_4 (1 # 10) = 4%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma more_active_more_entropy :
  (active_modes pure_tone_4 (1 # 10) < active_modes thermal_4 (1 # 10))%nat.
Proof. vm_compute. lia. Qed.

(* ================================================================ *)
(*  ENERGY VARIANCE                                                  *)
(* ================================================================ *)

Fixpoint sum_sq (l : list Q) : Q :=
  match l with nil => 0 | x :: xs => x * x + sum_sq xs end.

Fixpoint sum_list (l : list Q) : Q :=
  match l with nil => 0 | x :: xs => x + sum_list xs end.

Definition energy_variance_simple (amps : list Q) : Q :=
  let N := inject_Z (Z.of_nat (length amps)) in
  let mean_sq := sum_sq amps / N in
  let mean := sum_list amps / N in
  mean_sq - mean * mean.

Lemma thermal_low_variance :
  energy_variance_simple thermal_4 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma pure_tone_high_variance :
  energy_variance_simple pure_tone_4 == 3 # 4.
Proof. vm_compute. reflexivity. Qed.

Lemma variance_ordering :
  energy_variance_simple thermal_4 < energy_variance_simple pure_tone_4.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  TEMPERATURE                                                      *)
(* ================================================================ *)

Lemma temperature_from_energy :
  temperature 8 4 == 2.
Proof. unfold temperature. vm_compute. reflexivity. Qed.

Lemma temperature_zero :
  temperature 0 4 == 0.
Proof. unfold temperature. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  TOTAL ENERGY                                                     *)
(* ================================================================ *)

Lemma pure_tone_energy :
  total_energy_modes omega_4 pure_tone_4 == 4.
Proof. vm_compute. reflexivity. Qed.

Lemma thermal_energy :
  total_energy_modes omega_4 thermal_4 == 4.
Proof. vm_compute. reflexivity. Qed.

(** Same total energy, different distribution *)
Lemma same_energy_different_distribution :
  total_energy_modes omega_4 pure_tone_4 ==
  total_energy_modes omega_4 thermal_4.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  SYNTHESIS                                                        *)
(* ================================================================ *)

Theorem thermal_from_modes_synthesis :
  (* Pure tone: 1 active mode, high variance *)
  active_modes pure_tone_4 (1#10) = 1%nat /\
  energy_variance_simple pure_tone_4 == 3 # 4 /\
  (* Thermal: all active, zero variance *)
  active_modes thermal_4 (1#10) = 4%nat /\
  energy_variance_simple thermal_4 == 0 /\
  (* Same total energy *)
  total_energy_modes omega_4 pure_tone_4 ==
    total_energy_modes omega_4 thermal_4 /\
  (* Temperature = energy/modes *)
  temperature 8 4 == 2.
Proof.
  split; [exact pure_tone_one_active |
  split; [exact pure_tone_high_variance |
  split; [exact thermal_all_active |
  split; [exact thermal_low_variance |
  split; [exact same_energy_different_distribution |
  exact temperature_from_energy]]]]].
Qed.
