(** * MatN.v -- Generic N×N matrix operations over Q
    Elements: MatN, matN_mul, matN_pow, traceN, greenN, exp_QN
    Roles:    Unified matrix framework for arbitrary-size transfer matrices
    Rules:    All exact Q arithmetic, verified against 2×2 golden mean
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.

Open Scope Q_scope.

(* ================================================================== *)
(*  N×N MATRIX OVER Q                                                  *)
(* ================================================================== *)

Definition MatN := nat -> nat -> Q.

Definition matN_mul (N : nat) (A B : MatN) : MatN :=
  fun i j => fold_left (fun acc k => acc + A i k * B k j) (seq 0 N) 0.

Definition matN_id (N : nat) : MatN := fun i j =>
  if Nat.eqb i j then 1 else 0.

Fixpoint matN_pow (N : nat) (M : MatN) (K : nat) : MatN :=
  match K with
  | O => matN_id N
  | S k => matN_mul N M (matN_pow N M k)
  end.

Definition traceN (N : nat) (M : MatN) : Q :=
  fold_left (fun acc i => acc + M i i) (seq 0 N) 0.

Definition greenN (N : nat) (M : MatN) (i j K : nat) : Q :=
  matN_pow N M K i j.

(* ================================================================== *)
(*  EXPONENTIAL OVER Q (base utility)                                  *)
(* ================================================================== *)

Fixpoint factorial (n : nat) : nat :=
  match n with O => 1 | S k => (S k * factorial k)%nat end.

Fixpoint qpow_nat (q : Q) (n : nat) : Q :=
  match n with O => 1 | S k => q * qpow_nat q k end.

Fixpoint exp_QN (x : Q) (M : nat) : Q :=
  match M with
  | O => 1
  | S m => exp_QN x m +
            qpow_nat x (S m) / inject_Z (Z.of_nat (factorial (S m)))
  end.

(* ================================================================== *)
(*  VERIFICATION: N=2 matches GreenFunction.v golden mean              *)
(* ================================================================== *)

Definition golden_N : MatN := fun i j =>
  match i, j with
  | O, O => 1 | O, S O => 1
  | S O, O => 1 | _, _ => 0
  end.

Lemma matN_golden_trace_1 : traceN 2 (matN_pow 2 golden_N 1) == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma matN_golden_trace_2 : traceN 2 (matN_pow 2 golden_N 2) == 3.
Proof. vm_compute. reflexivity. Qed.

Lemma matN_golden_trace_3 : traceN 2 (matN_pow 2 golden_N 3) == 4.
Proof. vm_compute. reflexivity. Qed.

Lemma matN_golden_trace_4 : traceN 2 (matN_pow 2 golden_N 4) == 7.
Proof. vm_compute. reflexivity. Qed.

Lemma matN_golden_G00_4 : greenN 2 golden_N 0%nat 0%nat 4 == 5.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  VERIFICATION: N=3 for Potts/Clock matrices                        *)
(* ================================================================== *)

(** 3×3 identity trace *)
Lemma traceN_id_3 : traceN 3 (matN_id 3) == 3.
Proof. vm_compute. reflexivity. Qed.

(** 3×3 all-ones matrix: trace(M^1) = 3, trace(M^2) = 9 *)
Definition all_ones_3 : MatN := fun _ _ => 1.

Lemma traceN_ones_1 : traceN 3 all_ones_3 == 3.
Proof. vm_compute. reflexivity. Qed.

Lemma traceN_ones_2 : traceN 3 (matN_pow 3 all_ones_3 2) == 9.
Proof. vm_compute. reflexivity. Qed.

(** N×N identity: trace = N *)
Lemma traceN_id_2 : traceN 2 (matN_id 2) == 2.
Proof. vm_compute. reflexivity. Qed.

(** Rayleigh quotient from trace ratio *)
Definition rayleigh_trace (N : nat) (M : MatN) (K : nat) : Q :=
  traceN N (matN_pow N M (S K)) / traceN N (matN_pow N M K).

Lemma rayleigh_golden_3 : rayleigh_trace 2 golden_N 3 == 7#4.
Proof. vm_compute. reflexivity. Qed.

(** SYNTHESIS *)
Theorem matN_synthesis :
  traceN 2 (matN_pow 2 golden_N 4) == 7 /\
  greenN 2 golden_N 0%nat 0%nat 4 == 5 /\
  traceN 3 (matN_pow 3 all_ones_3 2) == 9 /\
  rayleigh_trace 2 golden_N 3 == 7#4.
Proof.
  split; [|split; [|split]].
  - exact matN_golden_trace_4.
  - exact matN_golden_G00_4.
  - exact traceN_ones_2.
  - exact rayleigh_golden_3.
Qed.
