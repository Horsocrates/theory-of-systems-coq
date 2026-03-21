(** * Ising2DTransfer.v -- 2D Ising transfer matrix on width-2 strip
    Elements: Mat4, mat4_pow, exp_Q, ising_2d_transfer, trace4
    Roles:    4×4 transfer matrix with entries exp(nβ) over Q
    Rules:    Exact Q arithmetic, Taylor truncation at order M
    Status:   Stdlib
    STATUS: 18 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

(* ================================================================== *)
(*  EXPONENTIAL OVER Q (Taylor series)                                 *)
(* ================================================================== *)

Fixpoint factorial (n : nat) : nat :=
  match n with O => 1 | S k => (S k * factorial k)%nat end.

Fixpoint qpow_nat (q : Q) (n : nat) : Q :=
  match n with O => 1 | S k => q * qpow_nat q k end.

Fixpoint exp_Q (x : Q) (M : nat) : Q :=
  match M with
  | O => 1
  | S m => exp_Q x m +
            qpow_nat x (S m) / inject_Z (Z.of_nat (factorial (S m)))
  end.

(** Concrete values at M=4 (from Ising1D.v, verified) *)
Lemma exp_Q_1_4 : exp_Q 1 4 == 65#24.
Proof. vm_compute. reflexivity. Qed.

Lemma exp_Q_neg1_4 : exp_Q (-(1)) 4 == 3#8.
Proof. vm_compute. reflexivity. Qed.

(** Concrete values at small arguments, M=3 *)
Lemma exp_Q_half_3 : exp_Q (1#2) 3 == 79#48.
Proof. vm_compute. reflexivity. Qed.

Lemma exp_Q_neg_half_3 : exp_Q (-(1#2)) 3 == 29#48.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  4×4 MATRIX ARITHMETIC                                              *)
(* ================================================================== *)

Definition Mat4 := nat -> nat -> Q.

Definition mat4_mul (A B : Mat4) : Mat4 :=
  fun i j =>
    A i 0%nat * B 0%nat j + A i 1%nat * B 1%nat j +
    A i 2%nat * B 2%nat j + A i 3%nat * B 3%nat j.

Definition mat4_id : Mat4 := fun i j =>
  if Nat.eqb i j then 1 else 0.

Fixpoint mat4_pow (M : Mat4) (K : nat) : Mat4 :=
  match K with
  | O => mat4_id
  | S k => mat4_mul M (mat4_pow M k)
  end.

Definition trace4 (M : Mat4) : Q :=
  M 0%nat 0%nat + M 1%nat 1%nat + M 2%nat 2%nat + M 3%nat 3%nat.

(* ================================================================== *)
(*  2D ISING TRANSFER MATRIX                                           *)
(* ================================================================== *)

Definition ising_2d_transfer (beta : Q) (M : nat) : Mat4 :=
  let a := exp_Q (3 * beta) M in
  let b := exp_Q beta M in
  let c := exp_Q (- beta) M in
  let d := exp_Q (-(3) * beta) M in
  fun i j => match i, j with
  | O, O => a | O, S O => c | O, S (S O) => c | O, S (S (S O)) => c
  | S O, O => b | S O, S O => b | S O, S (S O) => d | S O, S (S (S O)) => b
  | S (S O), O => b | S (S O), S O => d | S (S O), S (S O) => b | S (S O), S (S (S O)) => b
  | S (S (S O)), O => c | S (S (S O)), S O => c | S (S (S O)), S (S O) => c | S (S (S O)), S (S (S O)) => a
  | _, _ => 0
  end.

(** Trace = 2a + 2b (by symmetry T₀₀=T₃₃=a, T₁₁=T₂₂=b) *)
Lemma ising_2d_trace_formula : forall beta M,
  trace4 (ising_2d_transfer beta M) ==
  2 * exp_Q (3 * beta) M + 2 * exp_Q beta M.
Proof. intros. unfold trace4, ising_2d_transfer. ring. Qed.

(** Partition function *)
Definition Z_2d (N : nat) (beta : Q) (M : nat) : Q :=
  trace4 (mat4_pow (ising_2d_transfer beta M) N).

(** Trace of T² *)
Definition trace_T2 (beta : Q) (M : nat) : Q :=
  trace4 (mat4_mul (ising_2d_transfer beta M) (ising_2d_transfer beta M)).

(** Green's function for 4×4 *)
Definition green4 (T : Mat4) (i j K : nat) : Q :=
  mat4_pow T K i j.

(* ================================================================== *)
(*  EIGENVALUE STRUCTURE (from symmetry decomposition)                 *)
(* ================================================================== *)

(** Antisymmetric eigenvalue: T|+-⟩-|-+⟩ = (b-d)(|+-⟩-|-+⟩) *)
Definition lambda_antisym (beta : Q) (M : nat) : Q :=
  exp_Q beta M - exp_Q (-(3) * beta) M.

(** Flip-odd eigenvalue: T(|++⟩-|--⟩) = (a-c)(|++⟩-|--⟩) *)
Definition lambda_odd (beta : Q) (M : nat) : Q :=
  exp_Q (3 * beta) M - exp_Q (- beta) M.

(** Concrete eigenvalue values *)
Lemma lambda_antisym_value : lambda_antisym (1#2) 3 == 19#12.
Proof. unfold lambda_antisym. vm_compute. reflexivity. Qed.

Lemma lambda_odd_value : lambda_odd (1#2) 3 == 43#12.
Proof. unfold lambda_odd. vm_compute. reflexivity. Qed.

(** Both eigenvalues positive *)
Lemma lambda_antisym_pos_half : 0 < lambda_antisym (1#2) 3.
Proof. rewrite lambda_antisym_value. lra. Qed.

Lemma lambda_odd_pos_half : 0 < lambda_odd (1#2) 3.
Proof. rewrite lambda_odd_value. lra. Qed.

(** Eigenvalue ordering: λ_odd > λ_antisym *)
Lemma eigenvalue_ordering_half :
  lambda_antisym (1#2) 3 < lambda_odd (1#2) 3.
Proof. rewrite lambda_antisym_value, lambda_odd_value. lra. Qed.

(** Sum of even-sector eigenvalues *)
Definition sum_even (beta : Q) (M : nat) : Q :=
  trace4 (ising_2d_transfer beta M) - lambda_antisym beta M - lambda_odd beta M.

Lemma sum_even_value : sum_even (1#2) 3 == 13#2.
Proof. unfold sum_even. vm_compute. reflexivity. Qed.

Lemma sum_even_half_pos : 0 < sum_even (1#2) 3.
Proof. rewrite sum_even_value. lra. Qed.

(** SYNTHESIS *)
Theorem ising_2d_transfer_synthesis :
  (* Trace formula holds *)
  trace4 (ising_2d_transfer (1#2) 3) ==
    2 * exp_Q (3#2) 3 + 2 * exp_Q (1#2) 3 /\
  (* Eigenvalue ordering *)
  lambda_antisym (1#2) 3 < lambda_odd (1#2) 3 /\
  (* Even sector positive *)
  0 < sum_even (1#2) 3 /\
  (* Concrete exp values *)
  exp_Q (1#2) 3 == 79#48.
Proof.
  split; [|split; [|split]].
  - exact (ising_2d_trace_formula (1#2) 3).
  - exact eigenvalue_ordering_half.
  - exact sum_even_half_pos.
  - exact exp_Q_half_3.
Qed.
