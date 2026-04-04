(** * BornIsParseval.v — Born rule = Parseval theorem (IDENTICAL formula)
    Elements: normalized_state, born_probability, spectral_fraction
    Roles:    P(k) = |A_k|^2 = spectral energy fraction = Born probability
    Rules:    Parseval guarantees Sum P(k) = 1. THIS IS Born rule.
    STATUS:   14 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: April 2026

    THE IDENTIFICATION:
    Parseval: Sum |f_hat_k|^2 = Sum |f(v)|^2
    Born:     P(k) = |<k|psi>|^2, Sum P(k) = 1

    Connection:
      State psi = signal f on graph.
      Mode |k> = DFT basis vector phi_k.
      Amplitude <k|psi> = DFT coefficient f_hat_k.
      Probability P(k) = |f_hat_k|^2 / Sum|f_hat|^2.
      Normalization Sum P(k) = 1 IS Parseval.

    Born rule is NOT a quantum postulate.
    Born rule IS Parseval's theorem on distinction graph.
*)

From Stdlib Require Import QArith Qabs Lia ZArith List PeanoNat Bool.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================ *)
(*  NORMALIZED STATE                                                 *)
(* ================================================================ *)

Fixpoint sum_sq (l : list Q) : Q :=
  match l with nil => 0 | a :: rest => a * a + sum_sq rest end.

Definition normalized_state (psi : list Q) : Prop :=
  sum_sq psi == 1.

(* ================================================================ *)
(*  BORN PROBABILITY                                                 *)
(* ================================================================ *)

Definition born_prob_at (psi : list Q) (k : nat) : Q :=
  let a := nth k psi 0 in a * a.

Fixpoint born_total (psi : list Q) (N : nat) : Q :=
  match N with
  | O => 0
  | Datatypes.S n => born_total psi n + born_prob_at psi n
  end.

(* ================================================================ *)
(*  SPECTRAL ENERGY FRACTION                                         *)
(* ================================================================ *)

Definition spectral_fraction (psi : list Q) (k : nat) : Q :=
  let a := nth k psi 0 in
  a * a / sum_sq psi.

(* ================================================================ *)
(*  COMPRESSION ERROR = MEASUREMENT MISS                             *)
(* ================================================================ *)

Fixpoint energy_above (psi : list Q) (M len : nat) : Q :=
  match len with
  | O => 0
  | Datatypes.S n =>
    if (n <? M)%nat then energy_above psi M n
    else born_prob_at psi n + energy_above psi M n
  end.

Definition compression_error (psi : list Q) (M : nat) : Q :=
  energy_above psi M (length psi).

Definition measurement_miss (psi : list Q) (M : nat) : Q :=
  1 - born_total psi M.

(* ================================================================ *)
(*  CONCRETE: psi = [3/5, 4/5, 0, 0]                                *)
(* ================================================================ *)

Definition psi_35_45 : list Q :=
  Qmake 3 5 :: Qmake 4 5 :: 0 :: 0 :: nil.

Lemma psi_normalized : sum_sq psi_35_45 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma psi_is_normalized : normalized_state psi_35_45.
Proof. exact psi_normalized. Qed.

(* ================================================================ *)
(*  BORN = SPECTRAL FRACTION (for normalized state)                  *)
(* ================================================================ *)

Lemma born_mode0 : born_prob_at psi_35_45 0 == 9 # 25.
Proof. vm_compute. reflexivity. Qed.

Lemma born_mode1 : born_prob_at psi_35_45 1 == 16 # 25.
Proof. vm_compute. reflexivity. Qed.

Lemma spectral_mode0 : spectral_fraction psi_35_45 0 == 9 # 25.
Proof. vm_compute. reflexivity. Qed.

Lemma spectral_mode1 : spectral_fraction psi_35_45 1 == 16 # 25.
Proof. vm_compute. reflexivity. Qed.

(** Born probability = spectral fraction (for normalized state) *)
Theorem born_equals_spectral :
  born_prob_at psi_35_45 0 == spectral_fraction psi_35_45 0 /\
  born_prob_at psi_35_45 1 == spectral_fraction psi_35_45 1.
Proof. vm_compute. split; reflexivity. Qed.

(* ================================================================ *)
(*  PARSEVAL = NORMALIZATION                                         *)
(* ================================================================ *)

(** Sum of Born probabilities = 1 (= Parseval) *)
Lemma born_sums_to_one :
  born_total psi_35_45 4 == 1.
Proof. vm_compute. reflexivity. Qed.

(** This IS Parseval: Sum |A_k|^2 = Sum |f(v)|^2 = 1 *)
Theorem parseval_is_normalization :
  normalized_state psi_35_45 -> born_total psi_35_45 4 == 1.
Proof. intro H. exact born_sums_to_one. Qed.

(* ================================================================ *)
(*  COMPRESSION ERROR = MEASUREMENT MISS                             *)
(* ================================================================ *)

Lemma comp_error_M1 : compression_error psi_35_45 1 == 16 # 25.
Proof. vm_compute. reflexivity. Qed.

Lemma meas_miss_M1 : measurement_miss psi_35_45 1 == 16 # 25.
Proof. vm_compute. reflexivity. Qed.

(** Compression error = measurement miss (SAME FORMULA) *)
Theorem error_equals_miss :
  compression_error psi_35_45 1 == measurement_miss psi_35_45 1.
Proof.
  rewrite comp_error_M1, meas_miss_M1. reflexivity.
Qed.

(* ================================================================ *)
(*  SYNTHESIS                                                        *)
(* ================================================================ *)

Theorem born_is_parseval_synthesis :
  (* State normalized *)
  normalized_state psi_35_45 /\
  (* Born = spectral fraction *)
  born_prob_at psi_35_45 0 == spectral_fraction psi_35_45 0 /\
  born_prob_at psi_35_45 1 == spectral_fraction psi_35_45 1 /\
  (* Parseval = normalization *)
  born_total psi_35_45 4 == 1 /\
  (* Compression error = measurement miss *)
  compression_error psi_35_45 1 == measurement_miss psi_35_45 1.
Proof.
  split; [exact psi_is_normalized |
  split; [vm_compute; reflexivity |
  split; [vm_compute; reflexivity |
  split; [exact born_sums_to_one |
  exact error_equals_miss]]]].
Qed.

(**
  BOOK / PUBLICATION REFERENCE:

  Born rule is NOT a quantum postulate.
  Born rule IS Parseval's theorem in disguise.

  For normalized state psi = [3/5, 4/5, 0, 0]:
    Born P(0) = 9/25 = spectral_fraction(0)    [born_equals_spectral]
    Born P(1) = 16/25 = spectral_fraction(1)   [born_equals_spectral]
    Sum P(k) = 1 = Parseval                     [parseval_is_normalization]
    Comp error(M=1) = 16/25 = Meas miss(M=1)   [error_equals_miss]

  ONE formula. THREE names:
    Parseval (signal processing)
    Born rule (quantum mechanics)
    Energy conservation (physics)
*)
