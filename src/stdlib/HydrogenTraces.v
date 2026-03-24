(** * HydrogenTraces.v -- Trace identities for hydrogen Hamiltonian
    Elements: trace_H, trace_H2, Newton identity coefficients
    Roles:    tr(H) and tr(H²) → symmetric polynomial identities
    Rules:    Concrete verification for M=2, K=3 over Q
    Status:   Stdlib
    STATUS: 11 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.

(* ================================================================== *)
(*  HYDROGEN HAMILTONIAN (replicated for standalone compilation)       *)
(* ================================================================== *)

Definition H_hydrogen (M K i j : nat) : Q :=
  let Mq := inject_Z (Z.of_nat M) in
  let ip1 := inject_Z (Z.of_nat (S i)) in
  if Nat.eqb i j then
    2 * Mq * Mq - 2 * Mq / ip1
  else if orb (Nat.eqb (S i) j) (Nat.eqb i (S j)) then
    - (Mq * Mq)
  else
    0.

Open Scope Q_scope.

(* ================================================================== *)
(*  TRACE: tr(H) = Σ H(i,i)                                           *)
(* ================================================================== *)

Definition trace3 (M K : nat) : Q :=
  H_hydrogen M K 0 0 + H_hydrogen M K 1 1 + H_hydrogen M K 2 2.

Lemma trace3_M2 : trace3 2 3 == 50#3.
Proof. vm_compute. reflexivity. Qed.

(** Individual diagonal entries sum *)
Lemma trace3_decomp : trace3 2 3 == 4 + 6 + (20#3).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  TRACE OF H²: tr(H²) = Σ_k H(i,k)*H(k,j) summed on diagonal      *)
(* ================================================================== *)

(** (H²)_{ij} = Σ_k H(i,k)*H(k,j) for K=3 *)
Definition H2_entry (M K i j : nat) : Q :=
  H_hydrogen M K i 0 * H_hydrogen M K 0 j +
  H_hydrogen M K i 1 * H_hydrogen M K 1 j +
  H_hydrogen M K i 2 * H_hydrogen M K 2 j.

(** (H²)_{00} = H(0,0)² + H(0,1)² + H(0,2)² = 16 + 16 + 0 = 32 *)
Lemma H2_diag0 : H2_entry 2 3 0 0 == 32.
Proof. vm_compute. reflexivity. Qed.

(** (H²)_{11} = H(1,0)² + H(1,1)² + H(1,2)² = 16 + 36 + 16 = 68 *)
Lemma H2_diag1 : H2_entry 2 3 1 1 == 68.
Proof. vm_compute. reflexivity. Qed.

(** (H²)_{22} = H(2,0)² + H(2,1)² + H(2,2)² = 0 + 16 + 400/9 *)
Lemma H2_diag2 : H2_entry 2 3 2 2 == 544#9.
Proof. vm_compute. reflexivity. Qed.

(** tr(H²) = 32 + 68 + 544/9 = 1444/9 *)
Definition trace_H2 (M K : nat) : Q :=
  H2_entry M K 0 0 + H2_entry M K 1 1 + H2_entry M K 2 2.

Lemma trace_H2_M2_K3 : trace_H2 2 3 == 1444#9.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  NEWTON'S IDENTITIES                                                *)
(* ================================================================== *)

(** Newton's identity: p₁ = e₁ = tr(H)
    p₂ = tr(H²)
    e₂ = (p₁² - p₂) / 2                                              *)

Definition newton_e1 (M K : nat) : Q := trace3 M K.

Definition newton_e2 (M K : nat) : Q :=
  (trace3 M K * trace3 M K - trace_H2 M K) / 2.

Lemma newton_e1_M2_K3 : newton_e1 2 3 == 50#3.
Proof. vm_compute. reflexivity. Qed.

(** e₂ = ((50/3)² - 1444/9) / 2 = (2500/9 - 1444/9) / 2 = 1056/18 = 176/3 *)
Lemma newton_e2_M2_K3 : newton_e2 2 3 == 176#3.
Proof. vm_compute. reflexivity. Qed.

(** e₂ is positive (sum of products of eigenvalue pairs) *)
Lemma newton_e2_positive : 0 < newton_e2 2 3.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  TRACE RATIO                                                        *)
(* ================================================================== *)

(** tr(H²)/tr(H)² measures spectral spread *)
Definition trace_ratio (M K : nat) : Q :=
  trace_H2 M K / (trace3 M K * trace3 M K).

(** tr(H²)/tr(H)² = 1444/9 / (2500/9) = 1444/2500 = 361/625 *)
Lemma trace_ratio_M2_K3 : trace_ratio 2 3 == 361#625.
Proof. vm_compute. reflexivity. Qed.

(** Ratio < 1 means eigenvalues are spread (not concentrated at one value) *)
Lemma trace_ratio_less_one : trace_ratio 2 3 < 1.
Proof. vm_compute. reflexivity. Qed.
