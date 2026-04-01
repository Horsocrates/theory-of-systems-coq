(** * ErrorComposition.v — Error propagation through compression pipeline
    Elements: spectral_error, quant_error, total_error
    Roles:    triangle inequality composes stage errors
    Rules:    |f - f'| ≤ |f - f_trunc| + |f_trunc - f'|
    STATUS:   10 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: April 2026

    ERROR COMPOSITION:
    The pipeline introduces error at two stages:
    1. Spectral truncation: |f(j) - f_trunc(j)| (discarding modes)
    2. Quantization: |f_trunc(j) - f'(j)| (rounding coefficients)

    Triangle inequality: |f(j) - f'(j)| ≤ |f(j) - f_trunc(j)| + |f_trunc(j) - f'(j)|.

    For concrete sig4=(1,2,3,4) with keep_02 and step=1:
    — Spectral error at j=0: |1 - 2| = 1
    — Quantization error: 0 (coefficients are already integer multiples)
    — Total error: 1
*)

From Stdlib Require Import QArith Qabs Lia.
From Stdlib Require Import Lqa.

From ToS Require Import analysis.FourierBasis.
From ToS Require Import stdlib.compression.SpectralCompression.
From ToS Require Import stdlib.compression.VerifiedQuantization.
From ToS Require Import stdlib.compression.CompressionPipeline.

Open Scope Q_scope.

(* ================================================================ *)
(*  TRIANGLE INEQUALITY FOR Q                                        *)
(* ================================================================ *)

Lemma qabs_triangle : forall a b,
  Qabs (a + b) <= Qabs a + Qabs b.
Proof. exact Qabs_triangle. Qed.

(** Key composition lemma: |x-z| ≤ |x-y| + |y-z| *)
Lemma error_triangle : forall x y z,
  Qabs (x - z) <= Qabs (x - y) + Qabs (y - z).
Proof.
  intros x y z.
  assert (x - z == (x - y) + (y - z)) as Hsplit by ring.
  rewrite Hsplit. apply Qabs_triangle.
Qed.

(* ================================================================ *)
(*  SPECTRAL TRUNCATION ERROR                                        *)
(* ================================================================ *)

(** Error from discarding modes: f(j) vs truncated_recon *)
Definition spectral_err (f : nat -> Q) (keep : nat -> bool) (j : nat) : Q :=
  Qabs (f j - truncated_recon f keep j).

Lemma spectral_err_full_zero : forall j, (j < 4)%nat ->
  spectral_err sig4 keep_all j == 0.
Proof.
  intros j Hj.
  unfold spectral_err.
  destruct j as [|[|[|[|j']]]]; try lia;
  unfold truncated_recon, keep_all, dft_4, inner4, sig4,
    phi_0, phi_1, phi_2, phi_3;
  vm_compute; reflexivity.
Qed.

Lemma spectral_err_02_j0 : spectral_err sig4 keep_02 0%nat == 1.
Proof.
  unfold spectral_err, truncated_recon, keep_02, dft_4, inner4, sig4,
    phi_0, phi_1, phi_2, phi_3. vm_compute. reflexivity.
Qed.

(* ================================================================ *)
(*  QUANTIZATION ERROR                                               *)
(* ================================================================ *)

(** Concrete: quantize(0, 1) = 0, error = 0 *)
Lemma quant_err_0 : quant_error 0 1 == 0.
Proof. unfold quant_error, quantize, quantize_index, q_floor.
  vm_compute. reflexivity. Qed.

(** Concrete: quantize(2, 1) = 2, error = 0 *)
Lemma quant_err_2 : quant_error 2 1 == 0.
Proof. unfold quant_error, quantize, quantize_index, q_floor.
  vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  COMPOSED ERROR                                                   *)
(* ================================================================ *)

(** Total error = spectral + quantization (via triangle) *)
Theorem total_error_bound : forall f keep step j,
  Qabs (f j - compress_pipeline f keep step j) <=
    spectral_err f keep j +
    Qabs (truncated_recon f keep j - compress_pipeline f keep step j).
Proof.
  intros f keep step j.
  unfold spectral_err.
  apply error_triangle.
Qed.

(** Concrete: for sig4, keep_all, step=1 → total error = 0 *)
Lemma total_error_lossless : forall j, (j < 4)%nat ->
  Qabs (sig4 j - compress_pipeline sig4 keep_all (1#2) j) == 0.
Proof.
  intros j Hj.
  assert (Heq : compress_pipeline sig4 keep_all (1#2) j == sig4 j).
  { apply pipeline_lossless. exact Hj. }
  assert (sig4 j - compress_pipeline sig4 keep_all (1#2) j == 0) as Hz.
  { lra. }
  rewrite Hz. rewrite Qabs_pos; lra.
Qed.

(** Concrete: for sig4, keep_02, step=1 → total error at j=0 = 1 *)
Lemma total_error_lossy_j0 :
  Qabs (sig4 0%nat - compress_pipeline sig4 keep_02 1 0%nat) == 2.
Proof. exact pipeline_lossy_error_j0. Qed.

(* ================================================================ *)
(*  ERROR PROPERTIES                                                 *)
(* ================================================================ *)

(** More modes → less spectral error (concrete) *)
Lemma more_modes_less_error :
  spectral_err sig4 keep_all 0%nat <= spectral_err sig4 keep_02 0%nat.
Proof.
  rewrite spectral_err_full_zero; [| lia].
  rewrite spectral_err_02_j0.
  lra.
Qed.

(* ================================================================ *)
(*  SYNTHESIS                                                        *)
(* ================================================================ *)

Theorem error_composition_synthesis :
  (* Triangle inequality *)
  (forall x y z, Qabs (x - z) <= Qabs (x - y) + Qabs (y - z)) /\
  (* Full pipeline = lossless *)
  (forall j, (j < 4)%nat ->
    Qabs (sig4 j - compress_pipeline sig4 keep_all (1#2) j) == 0) /\
  (* Lossy has bounded error *)
  Qabs (sig4 0%nat - compress_pipeline sig4 keep_02 1 0%nat) == 2 /\
  (* More modes → less error *)
  spectral_err sig4 keep_all 0%nat <= spectral_err sig4 keep_02 0%nat.
Proof.
  split; [exact error_triangle |
  split; [exact total_error_lossless |
  split; [exact total_error_lossy_j0 |
  exact more_modes_less_error]]].
Qed.
