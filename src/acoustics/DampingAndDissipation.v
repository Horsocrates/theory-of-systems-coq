(** * DampingAndDissipation.v — Damping = vibration energy → waves
    Elements: damped_next, energy_radiated, damping_from_coupling
    Roles:    coupling to environment → energy leaks → amplitude decays
    Rules:    damping = wave emission. Silence = fully distributed tension.
    STATUS:   12 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: April 2026

    DAMPING = VIBRATION BECOMING WAVE:
    Undamped: L1-L5 tension stays LOCAL (eternal vibration).
    Damped: energy flows OUT to coupled neighbors → wave.
    The "louder" the sound, the faster the vibration dies.
    Silence = L1-L5 tension distributed across all DOF.
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import acoustics.VibrationCore.

(* ================================================================ *)
(*  DAMPED OSCILLATOR                                                *)
(* ================================================================ *)

Definition damped_next (k gamma d_prev d_curr : Q) : Q :=
  (2 - k - gamma) * d_curr - (1 - gamma) * d_prev.

Definition energy_radiated (E_initial E_remaining : Q) : Q :=
  E_initial - E_remaining.

Definition damping_from_coupling (k_internal k_env : Q) : Q :=
  k_env / (k_internal + k_env).

(* ================================================================ *)
(*  UNDAMPED = ETERNAL                                               *)
(* ================================================================ *)

(** gamma=0 reduces to standard oscillator *)
Lemma undamped_is_standard : forall k d0 d1,
  damped_next k 0 d0 d1 == next_state k d0 d1.
Proof. intros. unfold damped_next, next_state. ring. Qed.

Lemma undamped_k2_period :
  damped_next 2 0 0 1 == 0 /\
  damped_next 2 0 1 0 == -(1).
Proof. unfold damped_next. split; ring. Qed.

(* ================================================================ *)
(*  DAMPED = AMPLITUDE DECREASES                                     *)
(* ================================================================ *)

(** Small damping: amplitude after first step < initial *)
Lemma damped_decreasing :
  let g := 1 # 10 in
  let d1 := damped_next 2 g 0 1 in
  Qabs d1 < 1.
Proof.
  unfold damped_next. vm_compute. reflexivity.
Qed.

(** Concrete damped values for gamma=1/4 *)
Lemma damped_g14_d1 : damped_next 2 (1#4) 0 1 == -(1#4).
Proof. unfold damped_next. vm_compute. reflexivity. Qed.

Lemma damped_g14_d2 : damped_next 2 (1#4) 1 (-(1#4)) == -(11#16).
Proof. unfold damped_next. vm_compute. reflexivity. Qed.

(** Heavy damping gamma=1/2 *)
Lemma damped_g12_d1 : damped_next 2 (1#2) 0 1 == -(1#2).
Proof. unfold damped_next. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  DAMPING FROM COUPLING                                            *)
(* ================================================================ *)

Lemma damping_weak_coupling :
  damping_from_coupling 2 (1 # 10) == 1 # 21.
Proof. unfold damping_from_coupling. vm_compute. reflexivity. Qed.

Lemma damping_equal_coupling :
  damping_from_coupling 1 1 == 1 # 2.
Proof. unfold damping_from_coupling. vm_compute. reflexivity. Qed.

Lemma damping_strong_coupling :
  damping_from_coupling 1 9 == 9 # 10.
Proof. unfold damping_from_coupling. vm_compute. reflexivity. Qed.

(** Stronger coupling → more damping (faster sound emission) *)
Lemma stronger_coupling_more_damping :
  damping_from_coupling 1 1 < damping_from_coupling 1 9.
Proof. unfold damping_from_coupling. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  ENERGY ACCOUNTING                                                *)
(* ================================================================ *)

(** Radiated energy = initial - remaining *)
Lemma energy_accounting :
  energy_radiated 10 3 == 7.
Proof. unfold energy_radiated. ring. Qed.

Lemma no_damping_no_radiation :
  energy_radiated 10 10 == 0.
Proof. unfold energy_radiated. ring. Qed.

(* ================================================================ *)
(*  SYNTHESIS                                                        *)
(* ================================================================ *)

Theorem damping_synthesis :
  (* Undamped = standard oscillator *)
  (forall k d0 d1, damped_next k 0 d0 d1 == next_state k d0 d1) /\
  (* Damped amplitude decreases *)
  Qabs (damped_next 2 (1#10) 0 1) < 1 /\
  (* Stronger coupling → more damping *)
  damping_from_coupling 1 1 < damping_from_coupling 1 9 /\
  (* No damping → no radiation *)
  energy_radiated 10 10 == 0.
Proof.
  split; [exact undamped_is_standard |
  split; [exact damped_decreasing |
  split; [exact stronger_coupling_more_damping |
  exact no_damping_no_radiation]]].
Qed.
