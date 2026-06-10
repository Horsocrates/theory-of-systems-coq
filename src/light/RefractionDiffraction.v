(* ================================================================== *)
(*  RefractionDiffraction.v                                            *)
(*  Reflection/transmission from impedance mismatch — June 2026        *)
(*  honesty rollback: 2 True-stubs removed (total_internal_reflection  *)
(*  — needs angles/Snell; diffraction — needs an aperture layer; both  *)
(*  RETIRED).  Real general layer: energy_conserved_general (R+T=1 ∀), *)
(*  reflection_symmetric_general, reflection_below_one (no perfect     *)
(*  mirror at positive speeds).                                         *)
(*  STATUS: 11 Qed, 0 Admitted, 0 axioms                               *)
(*  Author: Horsocrates | Date: April 2026 (rollback: June 2026)       *)
(* ================================================================== *)

From Stdlib Require Import QArith Qabs Lia ZArith List PeanoNat.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(*  Definitions                                                        *)
(* ------------------------------------------------------------------ *)

(** Reflection coefficient (intensity): R = ((c2-c1)/(c2+c1))^2
    c1, c2 are wave speeds in the two regions *)
Definition reflection_coeff (c1 c2 : Q) : Q :=
  (c2 - c1) * (c2 - c1) / ((c2 + c1) * (c2 + c1)).

(** Transmission coefficient: T = 1 - R *)
Definition transmission_coeff (c1 c2 : Q) : Q :=
  1 - reflection_coeff c1 c2.

(* ------------------------------------------------------------------ *)
(*  Theorems                                                           *)
(* ------------------------------------------------------------------ *)

(** No reflection when media match *)
Theorem no_reflection_matched : reflection_coeff 1 1 == 0.
Proof. vm_compute. reflexivity. Qed.

(** Reflection at c1=1, c2=2 gives R = 1/9 *)
Theorem reflection_1_2 : reflection_coeff 1 2 == 1#9.
Proof. vm_compute. reflexivity. Qed.

(** Reflection at c1=1, c2=3 gives R = 1/4 *)
Theorem reflection_1_3 : reflection_coeff 1 3 == 1#4.
Proof. vm_compute. reflexivity. Qed.

(** Larger mismatch => larger reflection *)
Theorem full_reflection_large_mismatch :
  reflection_coeff 1 2 < reflection_coeff 1 3.
Proof. vm_compute. reflexivity. Qed.

(** Transmission at c1=1, c2=2 is 8/9 *)
Theorem transmission_complement : transmission_coeff 1 2 == 8#9.
Proof. vm_compute. reflexivity. Qed.

(** Energy conservation: R + T = 1 (concrete case) *)
Theorem energy_conserved :
  reflection_coeff 1 2 + transmission_coeff 1 2 == 1.
Proof. vm_compute. reflexivity. Qed.

(** Reflection is symmetric: swapping c1 and c2 gives same R *)
Theorem reflection_symmetric :
  reflection_coeff 1 3 == reflection_coeff 3 1.
Proof. vm_compute. reflexivity. Qed.

(* June 2026 honesty rollback: two True-stubs REMOVED.  diffraction needed an
   aperture/wave layer absent here — RETIRED.  total_internal_reflection needed
   angles/Snell — RETIRED; its honest neighbour is reflection_below_one (no
   perfect reflection at positive speeds).  Real general layer added below. *)

(** ★ Energy conservation R + T = 1 — GENERAL, for all speeds (was an instance). *)
Theorem energy_conserved_general : forall c1 c2 : Q,
  reflection_coeff c1 c2 + transmission_coeff c1 c2 == 1.
Proof. intros c1 c2. unfold transmission_coeff. ring. Qed.

(** Reflection is symmetric in the two media — GENERAL. *)
Theorem reflection_symmetric_general : forall c1 c2 : Q,
  reflection_coeff c1 c2 == reflection_coeff c2 c1.
Proof.
  intros c1 c2. unfold reflection_coeff.
  assert (Hn : (c2 - c1) * (c2 - c1) == (c1 - c2) * (c1 - c2)) by ring.
  assert (Hd : (c2 + c1) * (c2 + c1) == (c1 + c2) * (c1 + c2)) by ring.
  rewrite Hn, Hd. reflexivity.
Qed.

(** ★ No perfect mirror at positive speeds: R < 1 whenever both speeds are positive. *)
Theorem reflection_below_one : forall c1 c2 : Q,
  0 < c1 -> 0 < c2 -> reflection_coeff c1 c2 < 1.
Proof.
  intros c1 c2 H1 H2. unfold reflection_coeff.
  apply Qlt_shift_div_r.
  - nra.
  - nra.
Qed.

(** === SYNTHESIS === *)
Theorem refraction_diffraction_synthesis :
  reflection_coeff 1 1 == 0 /\
  reflection_coeff 1 2 < reflection_coeff 1 3 /\
  reflection_coeff 1 2 + transmission_coeff 1 2 == 1 /\
  (forall c1 c2 : Q,
     reflection_coeff c1 c2 + transmission_coeff c1 c2 == 1).
Proof.
  split. { vm_compute. reflexivity. }
  split. { vm_compute. reflexivity. }
  split. { vm_compute. reflexivity. }
  exact energy_conserved_general.
Qed.
