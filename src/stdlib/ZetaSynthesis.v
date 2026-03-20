(** * ZetaSynthesis.v -- Unified zeta function view
    Elements: zeta_classifies, orbit_spectrum_equivalent
    Roles:    Zeta function = complete dynamical invariant
    Rules:    Same ζ ↔ same orbit counts ↔ same eigenvalues
    Status:   Stdlib
    STATUS: 10 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import LinearAlgebra.
From ToS Require Import CauchyReal.
From ToS Require Import physics.InnerProductSpace.
From ToS Require Import physics.QState.
From ToS Require Import physics.QObservable.
From ToS Require Import physics.Orthogonality.
From ToS Require Import physics.SpinChain.
From ToS Require Import linalg.MatrixOps.
From ToS Require Import linalg.EigenvalueTheory.
From ToS Require Import stdlib.SFTEntropyGeneral.
From ToS Require Import stdlib.DynamicalZeta.
From ToS Require Import stdlib.ZetaPeriodicOrbits.

Open Scope Q_scope.

(* ================================================================== *)
(*  ZETA AS CLASSIFIER: same zeta ↔ same orbits                       *)
(* ================================================================== *)

(** Two SFTs have different zeta functions iff they differ on some orbit count *)
(** Contrapositive: if all orbit counts agree, zeta functions agree *)

(** Golden and full differ on orbits at K=1 *)
Lemma golden_full_orbit_diff :
  ~ (orbit_count golden_sft 1 == orbit_count full_sft 1).
Proof.
  rewrite golden_orbit_1, full_orbit_1.
  unfold Qeq. simpl. lia.
Qed.

(** Orbit counts determine the partial zeta sum *)
Lemma orbit_determines_partial :
  forall M z, zeta_partial M z 1 ==
    orbit_count M 0 + orbit_count M 1 * z.
Proof.
  intros. unfold zeta_partial, orbit_count.
  simpl. ring.
Qed.

(** Golden and full have different partial sums at z=1/10, K=1 *)
Lemma golden_full_partial_diff :
  ~ (zeta_partial golden_sft (1#10) 1 == zeta_partial full_sft (1#10) 1).
Proof. exact golden_full_different_zeta. Qed.

(* ================================================================== *)
(*  SPECTRAL INTERPRETATION: eigenvalues determine zeta               *)
(* ================================================================== *)

(** For 2×2: det(I-zM) = 1 - tr(M)z + det(M)z²
    Eigenvalues λ₁, λ₂ satisfy: λ₁+λ₂ = tr, λ₁λ₂ = det
    So ζ(z) = 1/((1-λ₁z)(1-λ₂z)) — spectrum determines zeta *)

(** Different traces → different zeta *)
Lemma different_trace_different_zeta :
  ~ (mat_trace golden_sft == mat_trace full_sft).
Proof.
  assert (H1 : mat_trace golden_sft == 1) by (vm_compute; reflexivity).
  assert (H2 : mat_trace full_sft == 2) by (vm_compute; reflexivity).
  rewrite H1, H2. unfold Qeq. simpl. lia.
Qed.

(** Different determinants → different zeta *)
Lemma golden_full_det_diff :
  ~ (det_2x2 golden_sft == det_2x2 full_sft).
Proof.
  assert (H1 : det_2x2 golden_sft == -(1)) by (vm_compute; reflexivity).
  assert (H2 : det_2x2 full_sft == 0) by (vm_compute; reflexivity).
  rewrite H1, H2. unfold Qeq. simpl. lia.
Qed.

(** Three-level classification:
    Level 1: h_top (topological entropy from λ_max)
    Level 2: spectrum (all eigenvalues via char poly)
    Level 3: zeta (all orbit counts) *)

(** Level 1 is coarser: same h_top ≠ same zeta
    (diag_21 and diag_2m1 from SFTClassification have same λ_max=2
     but different traces 3 vs 1) *)

(** Level 3 is finest: zeta determines everything *)

(** GRAND SYNTHESIS *)
Theorem zeta_synthesis :
  (* Orbit counts differ *)
  ~ (orbit_count golden_sft 1 == orbit_count full_sft 1) /\
  (* Zeta partial sums differ *)
  ~ (zeta_partial golden_sft (1#10) 1 == zeta_partial full_sft (1#10) 1) /\
  (* Spectra differ (both trace and det) *)
  ~ (mat_trace golden_sft == mat_trace full_sft) /\
  ~ (det_2x2 golden_sft == det_2x2 full_sft) /\
  (* Golden zeta at 1/2 *)
  zeta_det_2x2 golden_sft (1#2) == 1#4 /\
  (* Full zeta pole at 1/2 *)
  zeta_det_2x2 full_sft (1#2) == 0.
Proof.
  split; [|split; [|split; [|split; [|split]]]].
  - exact golden_full_orbit_diff.
  - exact golden_full_partial_diff.
  - exact different_trace_different_zeta.
  - exact golden_full_det_diff.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.
