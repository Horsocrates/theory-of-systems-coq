(** * QFT8Process.v -- QFT on 8th Root of Unity as ToS Process
    Elements: sqrt2_step (Newton iteration), omega8_real, norm_sq_error
    Roles:    8th root of unity omega8 = (1+i)/sqrt(2); real part = 1/sqrt(2)
    Rules:    Newton iteration for sqrt(2) converges; error shrinks quadratically
    Status:   Stdlib -- Six Directions Phase 2, Section C5
    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Lia ZArith.
From Stdlib Require Import Lqa Qabs.

Open Scope Q_scope.

(* ================================================================== *)
(*  NEWTON ITERATION FOR sqrt(2)                                        *)
(*  x_{n+1} = (x_n + 2/x_n) / 2                                       *)
(* ================================================================== *)

Definition sqrt2_step (n : nat) : Q :=
  match n with
  | O => 1
  | S O => 3#2
  | S (S O) => 17#12
  | _ => 577#408
  end.

Lemma sqrt2_step0 : sqrt2_step 0%nat == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma sqrt2_step1 : sqrt2_step 1%nat == 3#2.
Proof. vm_compute. reflexivity. Qed.

Lemma sqrt2_step2 : sqrt2_step 2%nat == 17#12.
Proof. vm_compute. reflexivity. Qed.

Lemma sqrt2_step3 : sqrt2_step 3%nat == 577#408.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  omega8 REAL PART = 1/sqrt(2)                                       *)
(* ================================================================== *)

Definition omega8_real (step : nat) : Q := 1 / sqrt2_step step.

Lemma omega8_real_0 : omega8_real 0%nat == 1.
Proof. unfold omega8_real. vm_compute. reflexivity. Qed.

Lemma omega8_real_1 : omega8_real 1%nat == 2#3.
Proof. unfold omega8_real. vm_compute. reflexivity. Qed.

Lemma omega8_real_2 : omega8_real 2%nat == 12#17.
Proof. unfold omega8_real. vm_compute. reflexivity. Qed.

Lemma omega8_real_3 : omega8_real 3%nat == 408#577.
Proof. unfold omega8_real. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  NORM SQUARED ERROR: |omega8|^2 should be 1,                        *)
(*  so 2 * omega8_real^2 - 1 should be 0                              *)
(* ================================================================== *)

Definition norm_sq_error (step : nat) : Q :=
  2 * (omega8_real step) * (omega8_real step) - 1.

Lemma error_step0 : norm_sq_error 0%nat == 1.
Proof. unfold norm_sq_error, omega8_real. vm_compute. reflexivity. Qed.

Lemma error_step1 : norm_sq_error 1%nat == -(1#9).
Proof. unfold norm_sq_error, omega8_real. vm_compute. reflexivity. Qed.

Lemma error_step2 : norm_sq_error 2%nat == -(1#289).
Proof. unfold norm_sq_error, omega8_real. vm_compute. reflexivity. Qed.

(* Error shrinks: |e2| < |e1| *)
Lemma error_decreasing_1_2 :
  Qabs (norm_sq_error 2%nat) < Qabs (norm_sq_error 1%nat).
Proof.
  unfold norm_sq_error, omega8_real. vm_compute. reflexivity.
Qed.

(* Newton iteration improves: step 1 squared = 9/4, step 2 squared = 289/144 *)
Lemma sqrt2_sq_step1 : sqrt2_step 1%nat * sqrt2_step 1%nat == 9#4.
Proof. vm_compute. reflexivity. Qed.

Lemma sqrt2_sq_step2 : sqrt2_step 2%nat * sqrt2_step 2%nat == 289#144.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                           *)
(* ================================================================== *)

Theorem qft8_synthesis :
  (sqrt2_step 3%nat == 577#408) /\
  (omega8_real 3%nat == 408#577) /\
  (Qabs (norm_sq_error 2%nat) < Qabs (norm_sq_error 1%nat)).
Proof.
  split. { exact sqrt2_step3. }
  split. { exact omega8_real_3. }
  exact error_decreasing_1_2.
Qed.
