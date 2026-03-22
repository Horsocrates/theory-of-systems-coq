(** * OscillatorCorrection.v -- Correct Harmonic Oscillator Energy Levels as ToS System
    Elements: E_oscillator (exact energy levels E_n = n + 1/2)
    Roles:    Ground state E0 = 1/2 for ALL K (lattice size irrelevant for exact spectrum)
    Rules:    Uniform spacing, positivity of zero-point energy
    Status:   Stdlib (corrects OscillatorFiniteSize interpretation)
    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

(* ================================================================== *)
(*  EXACT OSCILLATOR SPECTRUM: E_n = n + 1/2                           *)
(* ================================================================== *)

Definition E_oscillator (n : nat) : Q := inject_Z (Z.of_nat n) + (1#2).

(** Ground state: E0 = 1/2 always *)
Lemma E0_always_half : E_oscillator 0 == 1#2.
Proof. vm_compute. reflexivity. Qed.

(** First excited state *)
Lemma E1_always : E_oscillator 1 == 3#2.
Proof. vm_compute. reflexivity. Qed.

(** Second excited state *)
Lemma E2_always : E_oscillator 2 == 5#2.
Proof. vm_compute. reflexivity. Qed.

(** Third excited state *)
Lemma E3_always : E_oscillator 3 == 7#2.
Proof. vm_compute. reflexivity. Qed.

(** Zero-point energy is strictly positive *)
Lemma E_positive : 0 < E_oscillator 0.
Proof. unfold E_oscillator, Qlt. simpl. lia. Qed.

(** Uniform energy spacing: E1 - E0 = 1 *)
Lemma energy_spacing : E_oscillator 1 - E_oscillator 0 == 1.
Proof. vm_compute. reflexivity. Qed.

(** Uniform energy spacing: E2 - E1 = 1 *)
Lemma energy_spacing_2 : E_oscillator 2 - E_oscillator 1 == 1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                           *)
(* ================================================================== *)

Theorem oscillator_correction_synthesis :
  E_oscillator 0 == 1#2 /\
  0 < E_oscillator 0 /\
  E_oscillator 1 - E_oscillator 0 == 1 /\
  E_oscillator 2 - E_oscillator 1 == 1.
Proof.
  split; [exact E0_always_half |].
  split; [exact E_positive |].
  split; [exact energy_spacing |].
  exact energy_spacing_2.
Qed.
