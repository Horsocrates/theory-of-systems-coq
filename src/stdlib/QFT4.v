(** * QFT4.v — Quantum Fourier Transform for N=4
    Elements: qft4 power table, roots of unity mod 4, QFT matrix
    Roles:    Connect modular arithmetic to quantum phase structure
    Rules:    omega^{jk mod 4} encodes QFT; power table verified
    Status:   Stdlib
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
From Stdlib Require Import PeanoNat.
Open Scope Q_scope.

(* ================================================================== *)
(*  QFT POWER TABLE                                                    *)
(*  For N=4, QFT matrix element (j,k) uses omega^{jk mod 4}          *)
(*  where omega = i (4th root of unity)                                *)
(*  Power table: p(j,k) = (j*k) mod 4                                 *)
(* ================================================================== *)

Definition qft4_power (j k : nat) : nat :=
  Nat.modulo (j * k)%nat 4%nat.

(* Verify power table entries *)
Lemma power_00 : qft4_power O O = O.
Proof. reflexivity. Qed.

Lemma power_01 : qft4_power O (S O) = O.
Proof. reflexivity. Qed.

Lemma power_11 : qft4_power (S O) (S O) = (S O).
Proof. reflexivity. Qed.

Lemma power_12 : qft4_power (S O) (S (S O)) = (S (S O)).
Proof. reflexivity. Qed.

Lemma power_13 : qft4_power (S O) (S (S (S O))) = (S (S (S O))).
Proof. reflexivity. Qed.

Lemma power_22 : qft4_power (S (S O)) (S (S O)) = O.
Proof. reflexivity. Qed.

Lemma power_23 : qft4_power (S (S O)) (S (S (S O))) = (S (S O)).
Proof. reflexivity. Qed.

Lemma power_33 : qft4_power (S (S (S O))) (S (S (S O))) = (S O).
Proof. reflexivity. Qed.

(* ================================================================== *)
(*  SYMMETRY OF POWER TABLE                                            *)
(*  p(j,k) = p(k,j) because multiplication is commutative             *)
(* ================================================================== *)

Lemma qft4_power_symmetric : forall j k,
  qft4_power j k = qft4_power k j.
Proof.
  intros j k. unfold qft4_power.
  f_equal. apply Nat.mul_comm.
Qed.

(* ================================================================== *)
(*  PHASE STRUCTURE                                                    *)
(*  Powers 0,1,2,3 correspond to phases 1, i, -1, -i                 *)
(*  Row sums encode interference                                       *)
(* ================================================================== *)

(* Phase value: omega^p where omega = i *)
Definition phase_val (p : nat) : Q :=
  match Nat.modulo p 4%nat with
  | O => 1           (* omega^0 = 1 *)
  | S O => 0         (* omega^1 = i, real part = 0 *)
  | S (S O) => -(1)  (* omega^2 = -1 *)
  | _ => 0           (* omega^3 = -i, real part = 0 *)
  end.

(* QFT row sum (real parts): for j=0, all phases = 1 *)
Definition qft4_row_sum_real (j : nat) : Q :=
  phase_val (qft4_power j O) + phase_val (qft4_power j (S O)) +
  phase_val (qft4_power j (S (S O))) + phase_val (qft4_power j (S (S (S O)))).

Lemma row0_sum : qft4_row_sum_real O == 4.
Proof. vm_compute. reflexivity. Qed.

(* Non-zero row: interference cancellation *)
Lemma row1_sum : qft4_row_sum_real (S O) == 0.
Proof. vm_compute. reflexivity. Qed.

Theorem qft4_synthesis :
  qft4_power (S O) (S (S O)) = qft4_power (S (S O)) (S O) /\
  qft4_row_sum_real O == 4 /\
  qft4_row_sum_real (S O) == 0.
Proof.
  split; [reflexivity|].
  split; [exact row0_sum|exact row1_sum].
Qed.
