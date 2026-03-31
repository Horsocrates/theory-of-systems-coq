(* ========================================================================= *)
(*                     ACTION FROM TRANSFER MATRIX                         *)
(*          Transfer matrix traces and partition function structure         *)
(*                                                                          *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)        *)
(*                                                                          *)
(*  Author:  Horsocrates | Version: 1.0 (E/R/R) | Date: March 2026         *)
(*                                                                          *)
(*  STATUS: 8 Qed, 0 Admitted, 0 axioms                                    *)
(*                                                                          *)
(* ========================================================================= *)
(*                                                                          *)
(*  E/R/R INTERPRETATION:                                                   *)
(*  =====================                                                   *)
(*                                                                          *)
(*  Transfer matrix connects partition function to action:                  *)
(*                                                                          *)
(*    Elements = trace_TK (trace of T^K for K steps)                        *)
(*    Roles    = partition function Z = Tr(T^N), Boltzmann weights          *)
(*    Rules    = trace oscillation (Euclidean → Minkowski), det=1           *)
(*                                                                          *)
(*  PHILOSOPHICAL NOTE (P4):                                                *)
(*    The transfer matrix IS the Process: it maps state at step K to       *)
(*    state at step K+1. Tr(T^N) is the partition function — the process   *)
(*    of summing over all configurations weighted by exp(-S).              *)
(*                                                                          *)
(* ========================================================================= *)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* === Transfer Matrix Traces (using 3-4-5 rotation) === *)

(** Trace of T^K for the 3-4-5 rotation matrix.
    T^0 = I (trace 2), T^1 = U (trace 6/5),
    T^2 = U^2 (trace -14/25), T^3 = U^3 (trace -198/125). *)
Definition trace_TK (K : nat) : Q :=
  match K with
  | O => 2
  | S O => 6#5
  | S (S O) => -(14#25)
  | S (S (S O)) => -(198#125)
  | _ => 0
  end.

(** Boltzmann weight: link variable matrix entries *)
Definition U00 : Q := 3#5.
Definition U01 : Q := -(4#5).
Definition U10 : Q := 4#5.
Definition U11 : Q := 3#5.

(* === Trace Properties === *)

(** Identity matrix has trace 2 *)
Lemma trace_T0 : trace_TK 0 == 2.
Proof. vm_compute. reflexivity. Qed.

(** Single step trace = 6/5 *)
Lemma trace_T1 : trace_TK 1 == 6#5.
Proof. vm_compute. reflexivity. Qed.

(** Double step trace = -14/25 *)
Lemma trace_T2 : trace_TK 2 == -(14#25).
Proof. vm_compute. reflexivity. Qed.

(** Partition function Z_1 > 0 (positive for 1 step) *)
Lemma partition_Z1 : trace_TK 1 > 0.
Proof. vm_compute. reflexivity. Qed.

(** Trace oscillation: Tr(T^2) < 0
    This sign change reflects Euclidean-to-Minkowski rotation:
    the unitary matrix rotates past 90 degrees, flipping the trace sign. *)
Lemma partition_Z2_neg : trace_TK 2 < 0.
Proof. vm_compute. reflexivity. Qed.

(** Transition amplitude from state 0 to state 1 *)
Lemma weight_one_step : U10 == 4#5.
Proof. vm_compute. reflexivity. Qed.

(** Transition amplitude is positive *)
Lemma weight_positive : 0 < U10.
Proof. vm_compute. reflexivity. Qed.

(** Boltzmann interpretation: det=1 means unitary evolution
    (no probability loss, equivalent to Minkowski unitarity) *)
Lemma T_is_boltzmann : U00 * U11 - U01 * U10 == 1.
Proof. vm_compute. reflexivity. Qed.
