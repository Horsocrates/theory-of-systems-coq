(* ProcessHilbertSynthesis.v *)
(* Grand Synthesis: Process Hilbert Space *)
(* E: All results from 7 files unified *)
(* R: Structural role — complete quantum process framework *)
(* R: Inner products, Born rule, operators, uncertainty, measurement, entanglement *)

From Stdlib Require Import QArith Qabs List.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import stdlib.ProcessHilbert.
From ToS Require Import stdlib.ProcessOperatorH.
From ToS Require Import stdlib.ProcessUncertainty.
From ToS Require Import stdlib.SpectralFlow.
From ToS Require Import stdlib.ProcessMeasurementH.
From ToS Require Import stdlib.ProcessEntanglementH.
From ToS Require Import stdlib.ProcessQMConcrete.

(** ---- Foundation: Inner product and orthogonality ---- *)

Theorem hilbert_foundation :
  inner ket_0 ket_1 == 0 /\
  inner ket_0 ket_0 == 1 /\
  inner ket_1 ket_1 == 1.
Proof.
  split. exact inner_01.
  split. exact inner_00.
  exact inner_11.
Qed.

(** ---- Born rule completeness ---- *)

Theorem born_rule_complete :
  born_prob ket_0 ket_plus == (1#2) /\
  born_prob ket_1 ket_plus == (1#2) /\
  born_prob ket_0 ket_plus + born_prob ket_1 ket_plus == 1.
Proof.
  split. exact born_plus_0.
  split. exact born_plus_1.
  exact born_total.
Qed.

(** ---- Operator algebra ---- *)

Theorem operator_algebra :
  apply_op sigma_x 2 ket_0 = ket_1 /\
  apply_op hadamard_op 2 ket_0 = ket_plus /\
  apply_op sigma_x 2 (apply_op sigma_x 2 ket_0) = ket_0.
Proof.
  split. exact sigma_x_ket0.
  split. exact hadamard_ket0.
  exact sigma_x_involution_ket0.
Qed.

(** ---- Noncommutativity and uncertainty ---- *)

Theorem noncommutativity_and_uncertainty :
  commutator sigma_x sigma_z 2 O (S O) <> 0 /\
  expectation sigma_x 2 ket_plus == 1 /\
  variance sigma_z 2 ket_plus == 1.
Proof.
  split. exact noncommutative_xz.
  split. exact sx_expectation_plus.
  exact sz_variance_plus.
Qed.

(** ---- Measurement collapse ---- *)

Theorem measurement_collapse :
  measure ket_plus 0 2 = ket_0 /\
  born_prob (measure ket_plus 0 2) ket_plus == (1#2) /\
  born_prob ket_0 (measure ket_plus 0 2) == 1.
Proof.
  split. exact measure_plus_0.
  split. exact born_then_measure_0.
  exact post_measure_certain.
Qed.

(** ---- Entanglement detection ---- *)

Theorem entanglement_detection :
  ~ is_separable bell_plus /\
  is_separable separable_state /\
  norm_sq bell_plus == 2.
Proof.
  split. exact bell_entangled.
  split. exact product_separable.
  exact bell_norm.
Qed.

(** ---- Embedding preservation ---- *)

Theorem embedding_preservation :
  (forall psi phi, inner (embed psi) (embed phi) == inner psi phi) /\
  (forall psi, norm_sq (embed psi) == norm_sq psi).
Proof.
  split. exact embed_preserves_inner.
  exact embed_preserves_norm.
Qed.

(** ---- Spectral invariants ---- *)

Theorem spectral_invariants :
  trace_tridiag 5 == 0 /\
  trace_sq_tridiag 5 == 8 /\
  trace_sq_tridiag 5 - trace_sq_tridiag 4 == 2.
Proof.
  split. exact trace_tridiag_5.
  split. exact trace_sq_tridiag_5.
  exact spectral_flow_step_4_5.
Qed.

(** ---- Grand theorem ---- *)

Theorem process_hilbert_grand_synthesis :
  (* Orthogonality *)
  inner ket_0 ket_1 == 0 /\
  (* Born rule sums to 1 *)
  born_prob ket_0 ket_plus + born_prob ket_1 ket_plus == 1 /\
  (* Operators don't commute *)
  commutator sigma_x sigma_z 2 O (S O) <> 0 /\
  (* Entanglement exists *)
  ~ is_separable bell_plus /\
  (* Product states are separable *)
  is_separable separable_state /\
  (* Embedding preserves inner products *)
  (forall psi phi, inner (embed psi) (embed phi) == inner psi phi).
Proof.
  split. exact inner_01.
  split. exact born_total.
  split. exact sigma_xz_noncommute.
  split. exact bell_entangled.
  split. exact product_separable.
  exact embed_preserves_inner.
Qed.
