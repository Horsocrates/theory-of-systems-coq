(** * SlaterOverlap.v — Overlap Integrals for Slater Basis
    Elements: Overlap matrix S_ab, self-overlap S_11, cross-overlap S_12
    Roles:    Compute ⟨φ_a|φ_b⟩ on discrete lattice for generalized eigenvalue problem
    Rules:    S_ab = (1/M) Σ_i φ_a(i)·φ_b(i); S_11 > 0; S_12 ≠ S_11
    Status:   Stdlib
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.

From ToS Require Import stdlib.SlaterBasis.

(* ================================================================== *)
(*  OVERLAP INTEGRAL: S_ab = (1/M) Σ_{i=0}^{M-1} φ_a(i) · φ_b(i)    *)
(* ================================================================== *)

Fixpoint sum_Q (f : nat -> Q) (n : nat) : Q :=
  match n with
  | O => 0
  | S k => sum_Q f k + f k
  end.

Definition overlap (phi_a phi_b : nat -> Q) (M : nat) : Q :=
  sum_Q (fun i => phi_a i * phi_b i) M / inject_Z (Z.of_nat M).

(* ================================================================== *)
(*  CONCRETE: Self-overlap S_11 for ζ=1, M=3                          *)
(*  S_11 = (φ₀² + φ₁² + φ₂²) / 3                                     *)
(* ================================================================== *)

Definition S_11_raw : Q :=
  sto_1s 1 3 O * sto_1s 1 3 O +
  sto_1s 1 3 (S O) * sto_1s 1 3 (S O) +
  sto_1s 1 3 (S (S O)) * sto_1s 1 3 (S (S O)).

Lemma S_11_raw_eq : S_11_raw ==
  (91#127) * (91#127) + (19#37) * (19#37) + (7#19) * (7#19).
Proof.
  unfold S_11_raw, sto_1s, pade22_local. vm_compute. reflexivity.
Qed.

Lemma S_11_raw_pos : 0 < S_11_raw.
Proof. unfold S_11_raw, sto_1s, pade22_local. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  OVERLAP FUNCTION MATCHES MANUAL COMPUTATION                        *)
(* ================================================================== *)

Lemma overlap_1s_1s_eq : overlap (sto_1s 1 3) (sto_1s 1 3) 3 == S_11_raw / 3.
Proof.
  unfold overlap, sum_Q, S_11_raw, sto_1s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  Self-overlap is positive                                            *)
(* ================================================================== *)

Lemma overlap_1s_1s_pos : 0 < overlap (sto_1s 1 3) (sto_1s 1 3) 3.
Proof.
  unfold overlap, sum_Q, sto_1s, pade22_local. vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  CROSS-OVERLAP: S_12 for ζ=1, M=3                                  *)
(* ================================================================== *)

Definition S_12_raw : Q :=
  sto_1s 1 3 O * sto_2s 1 3 O +
  sto_1s 1 3 (S O) * sto_2s 1 3 (S O) +
  sto_1s 1 3 (S (S O)) * sto_2s 1 3 (S (S O)).

Lemma S_12_raw_pos : 0 < S_12_raw.
Proof. unfold S_12_raw, sto_1s, sto_2s, pade22_local. vm_compute. reflexivity. Qed.

Lemma overlap_1s_2s_eq : overlap (sto_1s 1 3) (sto_2s 1 3) 3 == S_12_raw / 3.
Proof.
  unfold overlap, sum_Q, S_12_raw, sto_1s, sto_2s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  S_12 < S_11 (cross-overlap smaller than self-overlap)              *)
(* ================================================================== *)

Lemma cross_lt_self : S_12_raw < S_11_raw.
Proof.
  unfold S_12_raw, S_11_raw, sto_1s, sto_2s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  Self-overlap of 2s basis                                            *)
(* ================================================================== *)

Definition S_22_raw : Q :=
  sto_2s 1 3 O * sto_2s 1 3 O +
  sto_2s 1 3 (S O) * sto_2s 1 3 (S O) +
  sto_2s 1 3 (S (S O)) * sto_2s 1 3 (S (S O)).

Lemma S_22_raw_pos : 0 < S_22_raw.
Proof. unfold S_22_raw, sto_2s, sto_1s, pade22_local. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  ORDERING: S_22 < S_11 (2s more diffuse than 1s)                    *)
(* ================================================================== *)

Lemma S_22_lt_S_11 : S_22_raw < S_11_raw.
Proof.
  unfold S_22_raw, S_11_raw, sto_2s, sto_1s, pade22_local.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  SYMMETRY: overlap(a,b) = overlap(b,a)                              *)
(* ================================================================== *)

Lemma overlap_symmetric : forall phi_a phi_b M,
  overlap phi_a phi_b M == overlap phi_b phi_a M.
Proof.
  intros. unfold overlap.
  apply Qdiv_comp; [|reflexivity].
  induction M as [|k IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. ring.
Qed.

(* ================================================================== *)
(*  OVERLAP AT ZERO: overlap of constant-1 basis = 1                   *)
(* ================================================================== *)

Lemma overlap_const1_M1 : overlap (fun _ => 1) (fun _ => 1) (S O) == 1.
Proof. unfold overlap, sum_Q. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  CAUCHY-SCHWARZ indicator: S_12² < S_11·S_22                        *)
(* ================================================================== *)

Lemma cauchy_schwarz_indicator : S_12_raw * S_12_raw < S_11_raw * S_22_raw.
Proof.
  unfold S_12_raw, S_11_raw, S_22_raw, sto_1s, sto_2s, pade22_local.
  vm_compute. reflexivity.
Qed.
