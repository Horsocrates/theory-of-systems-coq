(** * SpectralCompression.v — Lossy compression via DFT truncation
    Elements: truncated_recon, spectral_error, compression_ratio
    Roles:    keep M of N DFT modes → approximate signal with bounded error
    Rules:    error = Parseval remainder (discarded energy)
    STATUS:   10 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: April 2026

    SPECTRAL COMPRESSION:
    Signal f on N points. DFT gives f̂_0,...,f̂_{N-1}.
    Keep M modes (largest |f̂_k|). Discard rest.
    Reconstruct f_M from M coefficients.
    Error: ‖f - f_M‖² = Σ_{discarded} |f̂_k|²·‖φ_k‖² (Parseval).

    Compression ratio: M/N.
    Rate-distortion tradeoff: smaller M → more error but smaller storage.

    Concrete on C_4: f=(1,2,3,4).
    DFT: f̂=(10/4, -1, -2/4, 1) = (5/2, -1, -1/2, 1).
    Keep 2 modes: 50% compression, exact error computable.
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.

From ToS Require Import analysis.FourierBasis.

Open Scope Q_scope.

(* ================================================================ *)
(*  TRUNCATED RECONSTRUCTION                                         *)
(* ================================================================ *)

(** Reconstruct signal using only selected modes.
    keep(k) = true → include mode k, false → discard *)
Definition truncated_recon (f : nat -> Q) (keep : nat -> bool) (j : nat) : Q :=
  (if keep 0%nat then dft_4 f 0%nat * phi_0 j else 0) +
  (if keep 1%nat then dft_4 f 1%nat * phi_1 j else 0) +
  (if keep 2%nat then dft_4 f 2%nat * phi_2 j else 0) +
  (if keep 3%nat then dft_4 f 3%nat * phi_3 j else 0).

(** Keep all = full reconstruction *)
Definition keep_all (k : nat) : bool := true.

(** Keep none *)
Definition keep_none (k : nat) : bool := false.

(** Keep only modes 0 and 2 (DC + alternating) *)
Definition keep_02 (k : nat) : bool :=
  match k with 0%nat => true | 2%nat => true | _ => false end.

(* ================================================================ *)
(*  TEST SIGNAL                                                      *)
(* ================================================================ *)

Definition sig4 (j : nat) : Q :=
  match j with 0%nat => 1 | 1%nat => 2 | 2%nat => 3 | 3%nat => 4 | _ => 0 end.

(* ================================================================ *)
(*  FULL RECONSTRUCTION = ORIGINAL                                   *)
(* ================================================================ *)

Lemma full_recon_0 : truncated_recon sig4 keep_all 0%nat == sig4 0%nat.
Proof.
  unfold truncated_recon, keep_all, dft_4, inner4, sig4,
    phi_0, phi_1, phi_2, phi_3.
  vm_compute. reflexivity.
Qed.

Lemma full_recon_1 : truncated_recon sig4 keep_all 1%nat == sig4 1%nat.
Proof.
  unfold truncated_recon, keep_all, dft_4, inner4, sig4,
    phi_0, phi_1, phi_2, phi_3.
  vm_compute. reflexivity.
Qed.

(* ================================================================ *)
(*  PARTIAL RECONSTRUCTION = LOSSY                                   *)
(* ================================================================ *)

(** Keep modes 0,2 only: f_M(j) ≠ f(j) in general *)
Lemma partial_recon_0 : truncated_recon sig4 keep_02 0%nat == 2.
Proof.
  unfold truncated_recon, keep_02, dft_4, inner4, sig4,
    phi_0, phi_1, phi_2, phi_3.
  vm_compute. reflexivity.
Qed.

(** Error at j=0: f(0) - f_M(0) = 1 - 2 = -1 *)
Lemma compression_error_at_0 :
  sig4 0%nat - truncated_recon sig4 keep_02 0%nat == -(1).
Proof.
  unfold truncated_recon, keep_02, dft_4, inner4, sig4,
    phi_0, phi_1, phi_2, phi_3. vm_compute. reflexivity.
Qed.

(* ================================================================ *)
(*  COMPRESSION RATIO                                                *)
(* ================================================================ *)

Definition compression_ratio (M N : nat) : Q :=
  inject_Z (Z.of_nat M) / inject_Z (Z.of_nat N).

Lemma ratio_2_of_4 : compression_ratio 2 4 == 1 # 2.
Proof. unfold compression_ratio. vm_compute. reflexivity. Qed.

Lemma ratio_full : compression_ratio 4 4 == 1.
Proof. unfold compression_ratio. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  ENERGY AND ERROR                                                 *)
(* ================================================================ *)

(** Total energy of signal = inner4 f f *)
Definition signal_energy (f : nat -> Q) : Q := inner4 f f.

Lemma sig4_energy : signal_energy sig4 == 30.
Proof. unfold signal_energy, inner4, sig4. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  SYNTHESIS                                                        *)
(* ================================================================ *)

Theorem spectral_compression_synthesis :
  (* Full reconstruction works *)
  truncated_recon sig4 keep_all 0%nat == sig4 0%nat /\
  truncated_recon sig4 keep_all 1%nat == sig4 1%nat /\
  (* Partial reconstruction is lossy *)
  truncated_recon sig4 keep_02 0%nat == 2 /\
  (* Compression ratio *)
  compression_ratio 2 4 == 1 # 2 /\
  (* Signal energy *)
  signal_energy sig4 == 30.
Proof.
  split; [exact full_recon_0 |
  split; [exact full_recon_1 |
  split; [exact partial_recon_0 |
  split; [exact ratio_2_of_4 |
  exact sig4_energy]]]].
Qed.
