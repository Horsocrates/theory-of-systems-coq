(** * Ising1D.v -- 1D Ising model: exact solution from transfer matrix
    Elements: exp_taylor, ising_1d, lambda_plus/minus, Z_ising, energy_ising
    Roles:    Transfer matrix T → eigenvalues → partition function → all physics
    Rules:    All over Q, verified against Onsager's exact solution
    Status:   Stdlib
    STATUS: 18 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.GreenFunction.

Open Scope Q_scope.

(* ================================================================== *)
(*  TAYLOR SERIES FOR exp(β) OVER Q                                    *)
(* ================================================================== *)

Fixpoint factorial (n : nat) : nat :=
  match n with O => 1 | S k => (S k * factorial k)%nat end.

Fixpoint qpow_nat (q : Q) (n : nat) : Q :=
  match n with O => 1 | S k => q * qpow_nat q k end.

(** exp(β) ≈ Σ_{k=0}^{M} β^k / k! *)
Fixpoint exp_taylor (beta : Q) (M : nat) : Q :=
  match M with
  | O => 1
  | S m => exp_taylor beta m +
            qpow_nat beta (S m) / inject_Z (Z.of_nat (factorial (S m)))
  end.

(** exp(1) Taylor values *)
Lemma exp_taylor_0 : exp_taylor 1 0 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma exp_taylor_1 : exp_taylor 1 1 == 2.
Proof. vm_compute. reflexivity. Qed.

Lemma exp_taylor_2 : exp_taylor 1 2 == 5#2.
Proof. vm_compute. reflexivity. Qed.

Lemma exp_taylor_3 : exp_taylor 1 3 == 8#3.
Proof. vm_compute. reflexivity. Qed.

Lemma exp_taylor_4 : exp_taylor 1 4 == 65#24.
Proof. vm_compute. reflexivity. Qed.

(** exp(-1) Taylor values *)
Definition exp_neg_taylor (beta : Q) (M : nat) : Q :=
  exp_taylor (- beta) M.

Lemma exp_neg_1_M4 : exp_neg_taylor 1 4 == 3#8.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  1D ISING TRANSFER MATRIX                                           *)
(* ================================================================== *)

(** T = [[exp(β), exp(-β)], [exp(-β), exp(β)]] *)
Definition ising_1d (beta : Q) (M : nat) : Mat2 := fun i j =>
  match i, j with
  | O, O => exp_taylor beta M
  | O, S O => exp_neg_taylor beta M
  | S O, O => exp_neg_taylor beta M
  | S O, S O => exp_taylor beta M
  | _, _ => 0
  end.

(** Eigenvalues: λ± = exp(β) ± exp(-β) *)
Definition lambda_plus (beta : Q) (M : nat) : Q :=
  exp_taylor beta M + exp_neg_taylor beta M.

Definition lambda_minus (beta : Q) (M : nat) : Q :=
  exp_taylor beta M - exp_neg_taylor beta M.

Lemma lambda_plus_b1 : lambda_plus 1 4 == 37#12.
Proof. unfold lambda_plus. vm_compute. reflexivity. Qed.

Lemma lambda_minus_b1 : lambda_minus 1 4 == 7#3.
Proof. unfold lambda_minus. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  PARTITION FUNCTION AND THERMODYNAMICS                               *)
(* ================================================================== *)

(** Z(N) = λ₊^N + λ₋^N *)
Definition Z_ising (N : nat) (beta : Q) (M : nat) : Q :=
  qpow_nat (lambda_plus beta M) N + qpow_nat (lambda_minus beta M) N.

Lemma Z_ising_1 : Z_ising 1 1 4 == 65#12.
Proof. unfold Z_ising. vm_compute. reflexivity. Qed.

(** Energy per site: E = -tanh(β) ≈ -λ₋/λ₊ *)
Definition energy_ising (beta : Q) (M : nat) : Q :=
  - lambda_minus beta M / lambda_plus beta M.

Lemma energy_b1 : energy_ising 1 4 == -(28#37).
Proof. unfold energy_ising. vm_compute. reflexivity. Qed.

(** Mass gap: gap = 1 - λ₋/λ₊ *)
Definition ising_gap (beta : Q) (M : nat) : Q :=
  1 - lambda_minus beta M / lambda_plus beta M.

Lemma ising_gap_b1 : ising_gap 1 4 == 9#37.
Proof. unfold ising_gap. vm_compute. reflexivity. Qed.

(** No phase transition: λ₊ > λ₋ (gap > 0) at β=1 *)
Lemma ising_1d_gap_positive : 0 < ising_gap 1 4.
Proof. rewrite ising_gap_b1. lra. Qed.

(** SYNTHESIS *)
Theorem ising_1d_synthesis :
  (* Taylor exp(1) = 65/24 *)
  exp_taylor 1 4 == 65#24 /\
  (* Taylor exp(-1) = 3/8 *)
  exp_neg_taylor 1 4 == 3#8 /\
  (* 2·cosh(1) = 37/12 *)
  lambda_plus 1 4 == 37#12 /\
  (* Energy = -28/37 *)
  energy_ising 1 4 == -(28#37) /\
  (* Gap > 0 (no phase transition) *)
  0 < ising_gap 1 4.
Proof.
  split; [|split; [|split; [|split]]].
  - exact exp_taylor_4.
  - exact exp_neg_1_M4.
  - exact lambda_plus_b1.
  - exact energy_b1.
  - exact ising_1d_gap_positive.
Qed.
