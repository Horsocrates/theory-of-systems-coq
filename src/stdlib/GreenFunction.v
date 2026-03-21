(** * GreenFunction.v -- Propagator G_{ij}(K) = (M^K)_{ij} as process
    Elements: Mat2, mat2_pow, green, trace_process
    Roles:    G_{ij}(K) = amplitude to go from i to j in K steps
    Rules:    All of physics = Green's functions over Q
    Status:   Stdlib
    STATUS: 20 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

(* ================================================================== *)
(*  MATRIX POWER OVER Q (function-based 2×2)                           *)
(* ================================================================== *)

Definition Mat2 := nat -> nat -> Q.

Definition mat2_mul (A B : Mat2) : Mat2 :=
  fun i j => A i 0%nat * B 0%nat j + A i 1%nat * B 1%nat j.

Definition mat2_id : Mat2 := fun i j =>
  if Nat.eqb i j then 1 else 0.

Fixpoint mat2_pow (M : Mat2) (K : nat) : Mat2 :=
  match K with
  | O => mat2_id
  | S k => mat2_mul M (mat2_pow M k)
  end.

(** THE GREEN'S FUNCTION *)
Definition green (M : Mat2) (i j : nat) (K : nat) : Q :=
  mat2_pow M K i j.

(* ================================================================== *)
(*  CONCRETE: GOLDEN MEAN MATRIX                                       *)
(* ================================================================== *)

Definition golden : Mat2 := fun i j =>
  match i, j with
  | O, O => 1 | O, S O => 1
  | S O, O => 1 | _, _ => 0
  end.

(** G_{00}(K) = return probability = Fibonacci *)
Lemma green_golden_00_0 : green golden 0%nat 0%nat 0 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma green_golden_00_1 : green golden 0%nat 0%nat 1 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma green_golden_00_2 : green golden 0%nat 0%nat 2 == 2.
Proof. vm_compute. reflexivity. Qed.

Lemma green_golden_00_3 : green golden 0%nat 0%nat 3 == 3.
Proof. vm_compute. reflexivity. Qed.

Lemma green_golden_00_4 : green golden 0%nat 0%nat 4 == 5.
Proof. vm_compute. reflexivity. Qed.

(** G_{01}(K) = propagator 0→1 *)
Lemma green_golden_01_1 : green golden 0%nat 1%nat 1 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma green_golden_01_2 : green golden 0%nat 1%nat 2 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma green_golden_01_3 : green golden 0%nat 1%nat 3 == 2.
Proof. vm_compute. reflexivity. Qed.

Lemma green_golden_01_4 : green golden 0%nat 1%nat 4 == 3.
Proof. vm_compute. reflexivity. Qed.

(** TRACE = sum of diagonal Green's functions *)
Definition trace_process (M : Mat2) (K : nat) : Q :=
  green M 0%nat 0%nat K + green M 1%nat 1%nat K.

Lemma trace_golden_0 : trace_process golden 0 == 2.
Proof. vm_compute. reflexivity. Qed.

Lemma trace_golden_1 : trace_process golden 1 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma trace_golden_2 : trace_process golden 2 == 3.
Proof. vm_compute. reflexivity. Qed.

Lemma trace_golden_3 : trace_process golden 3 == 4.
Proof. vm_compute. reflexivity. Qed.

Lemma trace_golden_4 : trace_process golden 4 == 7.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  FULL SHIFT MATRIX (for comparison)                                  *)
(* ================================================================== *)

Definition full_mat2 : Mat2 := fun i j =>
  match i, j with
  | O, O => 1 | O, S O => 1
  | S O, O => 1 | S O, S O => 1
  | _, _ => 0
  end.

Lemma green_full_00_2 : green full_mat2 0%nat 0%nat 2 == 2.
Proof. vm_compute. reflexivity. Qed.

Lemma trace_full_1 : trace_process full_mat2 1 == 2.
Proof. vm_compute. reflexivity. Qed.

Lemma trace_full_2 : trace_process full_mat2 2 == 4.
Proof. vm_compute. reflexivity. Qed.

(** Full G_{00}(3) = 4 (vs golden G_{00}(3) = 3) *)
Lemma green_full_00_3 : green full_mat2 0%nat 0%nat 3 == 4.
Proof. vm_compute. reflexivity. Qed.

(** Golden and full have different G_{00} at K=3 *)
Lemma golden_full_green_diff :
  ~ (green golden 0%nat 0%nat 3 == green full_mat2 0%nat 0%nat 3).
Proof.
  rewrite green_golden_00_3, green_full_00_3.
  unfold Qeq. simpl. lia.
Qed.

(** SYNTHESIS *)
Theorem green_function_synthesis :
  (* G_{00} = Fibonacci: 1, 1, 2, 3, 5 *)
  green golden 0%nat 0%nat 4 == 5 /\
  (* Trace = Lucas: 2, 1, 3, 4, 7 *)
  trace_process golden 4 == 7 /\
  (* Full trace = 2^n: 2, 2, 4 *)
  trace_process full_mat2 2 == 4 /\
  (* Different propagators at K=3 *)
  ~ (green golden 0%nat 0%nat 3 == green full_mat2 0%nat 0%nat 3).
Proof.
  split; [|split; [|split]].
  - exact green_golden_00_4.
  - exact trace_golden_4.
  - exact trace_full_2.
  - exact golden_full_green_diff.
Qed.
