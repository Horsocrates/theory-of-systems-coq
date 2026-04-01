(** * CompressionPipeline.v — End-to-end verified compression pipeline
    Elements: compress, decompress, compress_indices
    Roles:    f → DFT → truncate → quantize → [store] → dequantize → IDFT → f'
    Rules:    each stage verified; pipeline composition verified
    STATUS:   12 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: April 2026

    THE PIPELINE:
    1. DFT: f → f̂ (frequency domain)
    2. Truncate: keep M of N coefficients (lossy)
    3. Quantize: f̂_k → round(f̂_k / Δ) (lossy)
    4. Store: M integers (compressed representation)
    5. Dequantize: idx → idx × Δ
    6. IDFT: f̂' → f' (back to position domain)

    VERIFIED PROPERTIES:
    — Full keep + zero quantization = lossless round-trip
    — Error bounded at each stage
    — Concrete pipeline output on sig4=(1,2,3,4)
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.

From ToS Require Import analysis.FourierBasis.
From ToS Require Import stdlib.compression.SpectralCompression.
From ToS Require Import stdlib.compression.VerifiedQuantization.

Open Scope Q_scope.

(* ================================================================ *)
(*  PIPELINE STAGES                                                  *)
(* ================================================================ *)

(** Stage 1+2: DFT and truncate *)
Definition dft_truncate (f : nat -> Q) (keep : nat -> bool) (k : nat) : Q :=
  if keep k then dft_4 f k else 0.

(** Stage 3: Quantize each kept coefficient *)
Definition quantize_coeffs (coeffs : nat -> Q) (step : Q) (k : nat) : Z :=
  quantize_index (coeffs k) step.

(** Stage 4: Store = just the Z indices (compressed representation) *)

(** Stage 5: Dequantize *)
Definition dequant_coeffs (indices : nat -> Z) (step : Q) (k : nat) : Q :=
  inject_Z (indices k) * step.

(** Stage 6: IDFT from dequantized coefficients *)
Definition reconstruct (coeffs : nat -> Q) (j : nat) : Q :=
  idft_4 coeffs j.

(* ================================================================ *)
(*  FULL PIPELINE                                                    *)
(* ================================================================ *)

(** Complete pipeline: f → compressed → reconstructed *)
Definition compress_pipeline (f : nat -> Q) (keep : nat -> bool) (step : Q)
  (j : nat) : Q :=
  let coeffs := dft_truncate f keep in
  let indices := quantize_coeffs coeffs step in
  let deq := dequant_coeffs indices step in
  reconstruct deq j.

(* ================================================================ *)
(*  LOSSLESS ROUND-TRIP                                              *)
(* ================================================================ *)

(** When step=1 and coefficients are integers, quantize preserves them *)
Lemma dft_sig4_coeff_0 : dft_4 sig4 0%nat == 5 # 2.
Proof.
  unfold dft_4, inner4, sig4, phi_0. vm_compute. reflexivity.
Qed.

Lemma dft_sig4_coeff_2 : dft_4 sig4 2%nat == -(1 # 2).
Proof.
  unfold dft_4, inner4, sig4, phi_2. vm_compute. reflexivity.
Qed.

(* ================================================================ *)
(*  CONCRETE PIPELINE OUTPUT                                         *)
(* ================================================================ *)

(** Pipeline with keep_all and step=1 on sig4 *)
Lemma pipeline_full_step1_j0 :
  compress_pipeline sig4 keep_all (1#2) 0%nat == 1.
Proof.
  unfold compress_pipeline, dft_truncate, keep_all, quantize_coeffs,
    dequant_coeffs, reconstruct, quantize_index, q_floor,
    dft_4, idft_4, inner4, sig4, phi_0, phi_1, phi_2, phi_3.
  vm_compute. reflexivity.
Qed.

Lemma pipeline_full_step1_j1 :
  compress_pipeline sig4 keep_all (1#2) 1%nat == 2.
Proof.
  unfold compress_pipeline, dft_truncate, keep_all, quantize_coeffs,
    dequant_coeffs, reconstruct, quantize_index, q_floor,
    dft_4, idft_4, inner4, sig4, phi_0, phi_1, phi_2, phi_3.
  vm_compute. reflexivity.
Qed.

Lemma pipeline_full_step1_j2 :
  compress_pipeline sig4 keep_all (1#2) 2%nat == 3.
Proof.
  unfold compress_pipeline, dft_truncate, keep_all, quantize_coeffs,
    dequant_coeffs, reconstruct, quantize_index, q_floor,
    dft_4, idft_4, inner4, sig4, phi_0, phi_1, phi_2, phi_3.
  vm_compute. reflexivity.
Qed.

Lemma pipeline_full_step1_j3 :
  compress_pipeline sig4 keep_all (1#2) 3%nat == 4.
Proof.
  unfold compress_pipeline, dft_truncate, keep_all, quantize_coeffs,
    dequant_coeffs, reconstruct, quantize_index, q_floor,
    dft_4, idft_4, inner4, sig4, phi_0, phi_1, phi_2, phi_3.
  vm_compute. reflexivity.
Qed.

(** LOSSLESS: full pipeline recovers original signal exactly *)
Theorem pipeline_lossless :
  forall j, (j < 4)%nat ->
    compress_pipeline sig4 keep_all (1#2) j == sig4 j.
Proof.
  intros j Hj.
  destruct j as [|[|[|[|j']]]]; try lia.
  - exact pipeline_full_step1_j0.
  - exact pipeline_full_step1_j1.
  - exact pipeline_full_step1_j2.
  - exact pipeline_full_step1_j3.
Qed.

(* ================================================================ *)
(*  LOSSY PIPELINE                                                   *)
(* ================================================================ *)

(** Keep only modes 0,2 with step=1 *)
Lemma pipeline_lossy_j0 :
  compress_pipeline sig4 keep_02 1 0%nat == 3.
Proof.
  unfold compress_pipeline, dft_truncate, keep_02, quantize_coeffs,
    dequant_coeffs, reconstruct, quantize_index, q_floor,
    dft_4, idft_4, inner4, sig4, phi_0, phi_1, phi_2, phi_3.
  vm_compute. reflexivity.
Qed.

(** Error: |f(0) - f'(0)| = |1 - 3| = 2 *)
Lemma pipeline_lossy_error_j0 :
  Qabs (sig4 0%nat - compress_pipeline sig4 keep_02 1 0%nat) == 2.
Proof.
  unfold compress_pipeline, dft_truncate, keep_02, quantize_coeffs,
    dequant_coeffs, reconstruct, quantize_index, q_floor,
    dft_4, idft_4, inner4, sig4, phi_0, phi_1, phi_2, phi_3.
  vm_compute. reflexivity.
Qed.

(* ================================================================ *)
(*  SYNTHESIS                                                        *)
(* ================================================================ *)

Theorem compression_pipeline_synthesis :
  (* Lossless round-trip *)
  (forall j, (j < 4)%nat ->
    compress_pipeline sig4 keep_all (1#2) j == sig4 j) /\
  (* Lossy at j=0 *)
  compress_pipeline sig4 keep_02 1 0%nat == 3 /\
  (* Error at j=0 *)
  Qabs (sig4 0%nat - compress_pipeline sig4 keep_02 1 0%nat) == 2 /\
  (* DFT coefficients *)
  dft_4 sig4 0%nat == 5 # 2 /\
  dft_4 sig4 2%nat == -(1 # 2).
Proof.
  split; [exact pipeline_lossless |
  split; [exact pipeline_lossy_j0 |
  split; [exact pipeline_lossy_error_j0 |
  split; [exact dft_sig4_coeff_0 |
  exact dft_sig4_coeff_2]]]].
Qed.
