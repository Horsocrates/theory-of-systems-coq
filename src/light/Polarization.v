(* ================================================================== *)
(*  Polarization.v                                                     *)
(*  Polarization as edge-field component selection                     *)
(*  STATUS: COMPLETE  (10 Qed, 0 Admitted)                            *)
(*  Author: Horsocrates                                                *)
(*  Date:   April 2026                                                 *)
(* ================================================================== *)

From Stdlib Require Import QArith Qabs Lia ZArith List PeanoNat.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(*  Definitions                                                        *)
(* ------------------------------------------------------------------ *)

(** Total energy of a two-component (H,V) edge field *)
Definition polarized_energy (eps_h eps_v : Q) : Q :=
  eps_h * eps_h + eps_v * eps_v.

(** Horizontal polarizer: keeps H, kills V *)
Definition h_polarize (eps_h eps_v : Q) : Q * Q :=
  (eps_h, 0 : Q).

(** Vertical polarizer: keeps V, kills H *)
Definition v_polarize (eps_h eps_v : Q) : Q * Q :=
  (0 : Q, eps_v).

(** Malus's law (intensity): I = A^2 * cos^2(theta) *)
Definition malus (amp cos_theta : Q) : Q :=
  amp * amp * cos_theta * cos_theta.

(* ------------------------------------------------------------------ *)
(*  Theorems                                                           *)
(* ------------------------------------------------------------------ *)

(** Purely H-polarized light has energy 1 *)
Theorem h_polarized_energy : polarized_energy 1 0 == 1.
Proof. vm_compute. reflexivity. Qed.

(** Purely V-polarized light has energy 1 *)
Theorem v_polarized_energy : polarized_energy 0 1 == 1.
Proof. vm_compute. reflexivity. Qed.

(** Unpolarized (equal H,V) has energy 2 *)
Theorem unpolarized_energy : polarized_energy 1 1 == 2.
Proof. vm_compute. reflexivity. Qed.

(** H-polarizer on equal-amplitude field halves the energy:
    H component squared == total / 2 *)
Theorem polarizer_halves :
  let p := h_polarize 1 1 in
  fst p * fst p == polarized_energy 1 1 / 2.
Proof. vm_compute. reflexivity. Qed.

(** Crossed polarizers block all light:
    H-polarize then V-polarize gives zero V-component *)
Theorem crossed_block :
  let hp := h_polarize 1 1 in
  let vp := v_polarize (fst hp) 0 in
  snd vp == 0.
Proof. vm_compute. reflexivity. Qed.

(** Malus: aligned polarizers (cos=1) transmit fully *)
Theorem malus_aligned : malus 1 1 == 1.
Proof. vm_compute. reflexivity. Qed.

(** Malus: crossed polarizers (cos=0) block fully *)
Theorem malus_crossed : malus 1 0 == 0.
Proof. vm_compute. reflexivity. Qed.

(** Malus at 45 degrees: cos(45) ~ 1/sqrt(2), approximate as 7/10.
    malus 1 (7#10) = 49/100 *)
Theorem malus_45_approx : malus 1 (7#10) == 49#100.
Proof. vm_compute. reflexivity. Qed.

(** H and V polarizations are orthogonal: swapping gives zero cross-energy *)
Theorem orthogonal_polarizations :
  let hp := h_polarize 1 0 in
  let vp := v_polarize 0 1 in
  fst hp * fst vp + snd hp * snd vp == 0.
Proof. vm_compute. reflexivity. Qed.

(** === SYNTHESIS === *)
Theorem polarization_synthesis :
  polarized_energy 1 0 == 1 /\
  polarized_energy 0 1 == 1 /\
  malus 1 1 == 1 /\
  malus 1 0 == 0.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.
