(** * NonLocalSpectrum.v -- Full (mean-field) matrix: non-local spectrum
    Elements: mean_field, trace_mf, trace_sq_mf, locality_comparison
    Roles:    Mean-field matrix (all 1 except diagonal 0) as non-local extreme
    Rules:    All Q arithmetic, no Admitted. Nat functions before Q_scope.
    Status:   Stdlib
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs ZArith.
From Stdlib Require Import Lqa.

(** Mean-field (fully connected) matrix: F(i,j) = 1 if i != j, 0 if i = j.
    Defined BEFORE Open Scope Q_scope. *)
Definition mean_field (i j : nat) : Q :=
  if Nat.eqb i j then 0 else 1.

Open Scope Q_scope.

(* ================================================================== *)
(*  CONCRETE VALUES                                                     *)
(* ================================================================== *)

Lemma mf_diag : mean_field O O == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma mf_offdiag : mean_field O (S O) == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma mf_offdiag2 : mean_field O (S (S O)) == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma mf_sym : mean_field (S O) O == 1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  TRACE FOR K=3                                                       *)
(* ================================================================== *)

(** tr(F) = F(0,0) + F(1,1) + F(2,2) = 0 + 0 + 0 = 0 *)
Definition trace_mf_3 : Q :=
  mean_field O O + mean_field (S O) (S O) + mean_field (S (S O)) (S (S O)).

Lemma trace_mf_3_val : trace_mf_3 == 0.
Proof. unfold trace_mf_3. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  TRACE OF F^2 FOR K=3                                                *)
(* ================================================================== *)

(** tr(F^2) = sum_i sum_j F(i,j)*F(j,i) = K*(K-1) = 3*2 = 6 *)
Definition trace_sq_mf_3 : Q :=
  mean_field O O * mean_field O O +
  mean_field O (S O) * mean_field (S O) O +
  mean_field O (S (S O)) * mean_field (S (S O)) O +
  mean_field (S O) O * mean_field O (S O) +
  mean_field (S O) (S O) * mean_field (S O) (S O) +
  mean_field (S O) (S (S O)) * mean_field (S (S O)) (S O) +
  mean_field (S (S O)) O * mean_field O (S (S O)) +
  mean_field (S (S O)) (S O) * mean_field (S O) (S (S O)) +
  mean_field (S (S O)) (S (S O)) * mean_field (S (S O)) (S (S O)).

Lemma trace_sq_mf_3_val : trace_sq_mf_3 == 6.
Proof. unfold trace_sq_mf_3. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SPECTRAL PROPERTIES                                                 *)
(* ================================================================== *)

(** For K=3 mean-field: eigenvalues are 2 (multiplicity 1) and -1 (multiplicity 2).
    Verification: tr(F) = 2 + (-1) + (-1) = 0 ✓
                  tr(F²) = 4 + 1 + 1 = 6 ✓ *)
Lemma eigenvalue_check_trace : (2) + (-(1)) + (-(1)) == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma eigenvalue_check_trace_sq : (2) * (2) + (-(1)) * (-(1)) + (-(1)) * (-(1)) == 6.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  COMPARISON WITH TRIDIAG                                             *)
(* ================================================================== *)

(** Tridiag trace_sq for K=3: only nearest-neighbor terms contribute.
    For the 3x3 Laplacian (normalized to unit entries):
    diagonal: 3, off-diag pairs: 2 * 1 = 2 each, total = 3*1 + 2*2*1 = ...
    Actually use simple model: T(i,j) = 1 if |i-j|=1, 0 otherwise.
    tr(T^2) for K=3: T has 2 pairs of 1s. tr(T^2) = 0 + 1 + 0 + 1 + 0 + 1 + 0 + 1 + 0 = 4 *)

Definition simple_tridiag (i j : nat) : Q :=
  if Nat.eqb (S i) j then 1
  else if Nat.eqb i (S j) then 1
  else 0.

Definition trace_sq_tri_3 : Q :=
  simple_tridiag O O * simple_tridiag O O +
  simple_tridiag O (S O) * simple_tridiag (S O) O +
  simple_tridiag O (S (S O)) * simple_tridiag (S (S O)) O +
  simple_tridiag (S O) O * simple_tridiag O (S O) +
  simple_tridiag (S O) (S O) * simple_tridiag (S O) (S O) +
  simple_tridiag (S O) (S (S O)) * simple_tridiag (S (S O)) (S O) +
  simple_tridiag (S (S O)) O * simple_tridiag O (S (S O)) +
  simple_tridiag (S (S O)) (S O) * simple_tridiag (S O) (S (S O)) +
  simple_tridiag (S (S O)) (S (S O)) * simple_tridiag (S (S O)) (S (S O)).

Lemma trace_sq_tri_3_val : trace_sq_tri_3 == 4.
Proof. unfold trace_sq_tri_3. vm_compute. reflexivity. Qed.

(** Full > tridiag in trace_sq: non-locality increases correlations *)
Lemma full_exceeds_tridiag : trace_sq_mf_3 > trace_sq_tri_3.
Proof. rewrite trace_sq_mf_3_val, trace_sq_tri_3_val. lra. Qed.

(* ================================================================== *)
(*  SUMMARY                                                             *)
(* ================================================================== *)

Theorem nonlocal_spectrum_summary :
  trace_mf_3 == 0 /\
  trace_sq_mf_3 == 6 /\
  trace_sq_tri_3 == 4 /\
  trace_sq_mf_3 > trace_sq_tri_3.
Proof.
  split; [| split; [| split]].
  - exact trace_mf_3_val.
  - exact trace_sq_mf_3_val.
  - exact trace_sq_tri_3_val.
  - exact full_exceeds_tridiag.
Qed.
