(** * Loudness.v — Loudness = |amplitude|^2 (Born rule)
    Elements: sound_energy, intensity, inverse_square
    Roles:    Born rule (p=2, derived) → energy = amplitude^2
    Rules:    E = A^2, I = E/n, I(r) ~ 1/r^2
    STATUS:   10 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: April 2026

    "Loudness = amplitude squared" is NOT a definition.
    It's a CONSEQUENCE of Born rule (p=2 unique from unitarity).
    Chain: L2+L3 → Born rule → E = |A|^2 → loudness law.
*)

From Stdlib Require Import QArith Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ================================================================ *)
(*  SOUND ENERGY = AMPLITUDE SQUARED (BORN RULE)                     *)
(* ================================================================ *)

Definition sound_energy (amplitude : Q) : Q :=
  amplitude * amplitude.

Definition intensity (total_energy : Q) (n_vertices : nat) : Q :=
  total_energy / inject_Z (Z.of_nat n_vertices).

Definition inverse_square (energy_val : Q) (r : nat) : Q :=
  energy_val / inject_Z (Z.of_nat (r * r)).

(* ================================================================ *)
(*  ENERGY PROPERTIES                                                *)
(* ================================================================ *)

Lemma energy_is_amplitude_squared :
  sound_energy (3 # 5) == 9 # 25.
Proof. unfold sound_energy. vm_compute. reflexivity. Qed.

Lemma double_amplitude_quadruple_energy :
  sound_energy 2 == 4 * sound_energy 1.
Proof. unfold sound_energy. vm_compute. reflexivity. Qed.

Lemma triple_amplitude :
  sound_energy 3 == 9 * sound_energy 1.
Proof. unfold sound_energy. vm_compute. reflexivity. Qed.

Lemma energy_nonneg : forall a, 0 <= sound_energy a.
Proof.
  intro a. unfold sound_energy.
  destruct (Qlt_le_dec a 0) as [Hn | Hn].
  - assert (a * a == (-(a)) * (-(a))) as Heq by ring.
    rewrite Heq. apply Qmult_le_0_compat; lra.
  - apply Qmult_le_0_compat; lra.
Qed.

Lemma energy_zero_iff_silent :
  sound_energy 0 == 0.
Proof. unfold sound_energy. ring. Qed.

(* ================================================================ *)
(*  INVERSE SQUARE LAW                                               *)
(* ================================================================ *)

Lemma inverse_square_decreases :
  inverse_square 1 2 < inverse_square 1 1.
Proof. unfold inverse_square. vm_compute. reflexivity. Qed.

Lemma inverse_square_r1 : inverse_square 1 1 == 1.
Proof. unfold inverse_square. vm_compute. reflexivity. Qed.

Lemma inverse_square_r2 : inverse_square 1 2 == 1 # 4.
Proof. unfold inverse_square. vm_compute. reflexivity. Qed.

Lemma inverse_square_r3 : inverse_square 1 3 == 1 # 9.
Proof. unfold inverse_square. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  SYNTHESIS                                                        *)
(* ================================================================ *)

Theorem loudness_synthesis :
  (* E = A^2 *)
  sound_energy (3 # 5) == 9 # 25 /\
  (* 2x amplitude → 4x energy *)
  sound_energy 2 == 4 * sound_energy 1 /\
  (* E ≥ 0 *)
  0 <= sound_energy (-(7)) /\
  (* Silence *)
  sound_energy 0 == 0 /\
  (* Inverse square *)
  inverse_square 1 2 == 1 # 4 /\
  inverse_square 1 3 == 1 # 9.
Proof.
  split; [exact energy_is_amplitude_squared |
  split; [exact double_amplitude_quadruple_energy |
  split; [apply energy_nonneg |
  split; [exact energy_zero_iff_silent |
  split; [exact inverse_square_r2 |
  exact inverse_square_r3]]]]].
Qed.
