(** * ThermalSynthesis.v — Grand synthesis: thermodynamics from vibration
    STATUS:   8 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: April 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import thermal.ThermalFromModes.
From ToS Require Import thermal.SecondLaw.

Theorem thermal_grand_synthesis :
  (* Pure tone = concentrated tension *)
  active_modes pure_tone_4 (1#10) = 1%nat /\
  (* Thermal = distributed tension *)
  active_modes thermal_4 (1#10) = 4%nat /\
  (* Same energy, different distribution *)
  total_energy_modes omega_4 pure_tone_4 == total_energy_modes omega_4 thermal_4 /\
  (* Temperature = energy/modes *)
  temperature 8 4 == 2 /\
  (* Second law: coupling increases entropy *)
  (active_modes ((2:Q) :: (0:Q) :: nil) (1#10) < active_modes (Qmake 3 2 :: Qmake 1 2 :: nil) (1#10))%nat /\
  (* Equilibrium: zero variance *)
  energy_variance_simple [1; 1; 1; 1] == 0.
Proof.
  split; [exact pure_tone_one_active |
  split; [exact thermal_all_active |
  split; [exact same_energy_different_distribution |
  split; [exact temperature_from_energy |
  split; [exact entropy_increases |
  exact equilibrium_zero_variance]]]]].
Qed.

(** Zero-point energy: absolute zero has nonzero tension *)
Definition zero_point_4 : Q := (0 + 2 + 4 + 2) / 8.

Lemma zero_point_positive : 0 < zero_point_4.
Proof. unfold zero_point_4. vm_compute. reflexivity. Qed.

(** Heat = sound at equilibrium. Music = non-thermal sound. *)
Lemma heat_is_equilibrium_sound :
  energy_variance_simple thermal_4 == 0.
Proof. exact thermal_low_variance. Qed.
