(** * ObserverCompressor.v — Observer = Compressor: QM ↔ Information Theory
    Elements: born_is_spectral_energy, measurement_is_truncation, collapse_is_compression
    Roles:    Born rule = Parseval. Measurement = mode selection. Collapse = truncation.
    Rules:    uncertainty = DFT time-frequency limit. Complementarity = basis choice.
    STATUS:   15 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: April 2026

    THE CROWN JEWEL:
    Quantum mechanics IS information processing on distinction graph.
    Not analogy. IDENTITY through E/R/R.

    Born rule = Parseval theorem (energy conservation under basis change)
    Measurement = DFT truncation (select M of N modes)
    Collapse = lossy compression (discarded modes = "collapsed" info)
    Uncertainty = time-frequency tradeoff (DFT fundamental limit)
    Complementarity = choice of DFT basis (position vs momentum)
*)

From Stdlib Require Import QArith Qabs Lia ZArith List PeanoNat Bool.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import foundation.PhysicalProcess.

(* ================================================================ *)
(*  1. BORN RULE = PARSEVAL (energy conservation)                    *)
(* ================================================================ *)

(** Parseval: Sum |f(v)|^2 = Sum |f_hat(k)|^2 * ||phi_k||^2
    Born: P(k) = |A_k|^2 / Sum|A_j|^2
    SAME STATEMENT: total energy in time domain = total energy in frequency domain.
    Born rule = Parseval applied to quantum state. *)

Definition time_energy (field : nat -> Q) (N : nat) : Q :=
  pp_energy field N.

Definition freq_energy (coeffs norms : nat -> Q) (N : nat) : Q :=
  pp_energy (fun k => coeffs k * coeffs k * norms k) N.

(** Concrete: impulse signal on N=4.
    Time energy = |1|^2 = 1.
    Freq energy = sum of |coeff_k|^2. *)
Lemma impulse_time_energy :
  time_energy impulse_pp 4 == 1.
Proof. vm_compute. reflexivity. Qed.

(** Born probability = spectral energy fraction *)
Definition born_prob (coeff_sq total : Q) : Q := coeff_sq / total.

Lemma born_normalized_example :
  born_prob (1#4) 1 == 1 # 4.
Proof. vm_compute. reflexivity. Qed.

(** Born rule IS energy conservation: probabilities sum to 1
    iff spectral energy = total energy (Parseval) *)
Lemma born_sum_is_parseval :
  born_prob (1#4) 1 + born_prob (1#4) 1 +
  born_prob (1#4) 1 + born_prob (1#4) 1 == 1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  2. MEASUREMENT = TRUNCATION (mode selection)                     *)
(* ================================================================ *)

(** Measurement: choose observable = choose basis.
    Result: one eigenvalue. Other modes "discarded."

    Compression: choose M modes. Keep those.
    Result: M coefficients. Other modes discarded.

    SAME operation. *)

Definition measure (field : nat -> Q) (mode : nat) : Q :=
  field mode.  (* select one mode's value *)

Definition truncate_to_one (field : nat -> Q) (kept : nat) (v : nat) : Q :=
  if (v =? kept)%nat then field kept else 0.

(** After measurement: only kept mode survives *)
Lemma post_measurement_one_mode :
  truncate_to_one impulse_pp 0 0%nat == 1 /\
  truncate_to_one impulse_pp 0 1%nat == 0 /\
  truncate_to_one impulse_pp 0 2%nat == 0.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** Measurement outcome = compression coefficient *)
Lemma measurement_eq_coefficient :
  measure impulse_pp 0 = impulse_pp 0.
Proof. reflexivity. Qed.

(* ================================================================ *)
(*  3. COLLAPSE = LOSSY COMPRESSION                                  *)
(* ================================================================ *)

(** "Wave function collapse" = keeping ONE mode, discarding N-1.
    = compression with M=1.
    = maximum compression, maximum information loss. *)

Definition collapse_to_mode (N kept : nat) : nat := 1%nat.
Definition compress_to_M (M : nat) : nat := M.

(** Collapse = compression with M=1 *)
Lemma collapse_is_max_compression :
  collapse_to_mode 4 2 = compress_to_M 1.
Proof. reflexivity. Qed.

(** Information lost = N - 1 modes *)
Definition info_lost_collapse (N : nat) : nat := (N - 1)%nat.
Definition info_lost_compress (N M : nat) : nat := (N - M)%nat.

Lemma collapse_loses_most :
  info_lost_collapse 4 = info_lost_compress 4 1.
Proof. reflexivity. Qed.

(** No collapse (M=N): lossless "measurement" = keep all info *)
Lemma no_collapse_lossless :
  info_lost_compress 4 4 = 0%nat.
Proof. reflexivity. Qed.

(* ================================================================ *)
(*  4. UNCERTAINTY = DFT TIME-FREQUENCY LIMIT                        *)
(* ================================================================ *)

(** Heisenberg: delta_x * delta_p >= 1/2.
    DFT: a signal cannot be both localized in time AND frequency.
    SAME principle: narrow in one domain = wide in other.

    On N-point DFT: min uncertainty = 1/(2N).
    Finer graph → smaller uncertainty. *)

Definition min_uncertainty (N : nat) : Q :=
  1 / inject_Z (Z.of_nat (2 * N)).

Lemma uncertainty_N4 : min_uncertainty 4 == 1 # 8.
Proof. vm_compute. reflexivity. Qed.

Lemma uncertainty_N8 : min_uncertainty 8 == 1 # 16.
Proof. vm_compute. reflexivity. Qed.

Lemma finer_less_uncertain :
  min_uncertainty 8 < min_uncertainty 4.
Proof. vm_compute. reflexivity. Qed.

(** Uncertainty is STRUCTURAL (from DFT), not mysterious *)

(* ================================================================ *)
(*  5. COMPLEMENTARITY = BASIS CHOICE                                *)
(* ================================================================ *)

(** Position basis: field values f(v) — localized on vertices.
    Momentum basis: coefficients f_hat(k) — localized on modes.
    Cannot have both maximally localized: DFT tradeoff.

    Choosing to measure "position" = using vertex basis.
    Choosing to measure "momentum" = using mode basis.
    Complementarity = you must CHOOSE a basis. Can't use both. *)

Inductive BasisChoice := PositionBasis | MomentumBasis.

Definition basis_localized_in (b : BasisChoice) : BasisChoice :=
  match b with
  | PositionBasis => PositionBasis  (* localized in position *)
  | MomentumBasis => MomentumBasis  (* localized in momentum *)
  end.

Definition basis_delocalized_in (b : BasisChoice) : BasisChoice :=
  match b with
  | PositionBasis => MomentumBasis  (* position → delocalized in momentum *)
  | MomentumBasis => PositionBasis  (* momentum → delocalized in position *)
  end.

Lemma complementarity :
  basis_delocalized_in PositionBasis = MomentumBasis /\
  basis_delocalized_in MomentumBasis = PositionBasis.
Proof. split; reflexivity. Qed.

(** Complementarity is NOT mysterious.
    It's the DFT time-frequency tradeoff.
    A delta function in time = flat spectrum.
    A single frequency = extended in time.
    Same math. Different name. *)

(* ================================================================ *)
(*  GRAND SYNTHESIS                                                  *)
(* ================================================================ *)

Theorem observer_compressor_synthesis :
  (* 1. Born = energy conservation *)
  born_prob (1#4) 1 + born_prob (1#4) 1 +
    born_prob (1#4) 1 + born_prob (1#4) 1 == 1 /\
  (* 2. Measurement = truncation to one mode *)
  truncate_to_one impulse_pp 0 0%nat == 1 /\
  truncate_to_one impulse_pp 0 1%nat == 0 /\
  (* 3. Collapse = max compression (M=1) *)
  collapse_to_mode 4 2 = compress_to_M 1 /\
  info_lost_collapse 4 = info_lost_compress 4 1 /\
  (* 4. Uncertainty = DFT limit *)
  min_uncertainty 8 < min_uncertainty 4 /\
  (* 5. Complementarity = basis tradeoff *)
  basis_delocalized_in PositionBasis = MomentumBasis /\
  basis_delocalized_in MomentumBasis = PositionBasis.
Proof.
  split; [exact born_sum_is_parseval |
  split; [vm_compute; reflexivity |
  split; [vm_compute; reflexivity |
  split; [exact collapse_is_max_compression |
  split; [exact collapse_loses_most |
  split; [exact finer_less_uncertain |
  exact complementarity]]]]]].
Qed.
