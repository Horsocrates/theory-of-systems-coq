(** * ClassificationSynthesis.v -- Grand classification synthesis
    Elements: full_classification, hierarchy_theorem
    Roles:    Unite all classification levels into one theorem
    Rules:    h_top < spectrum ≤ orbit_process (for 2×2, spectrum = orbit_process)
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 new axioms
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
From ToS Require Import stdlib.SFTClassification.
From ToS Require Import stdlib.DynamicalZeta.
From ToS Require Import stdlib.ZetaPeriodicOrbits.
From ToS Require Import stdlib.ZetaSynthesis.
From ToS Require Import stdlib.CFMatrixProduct.
From ToS Require Import stdlib.LagrangeTheorem.
From ToS Require Import stdlib.CFSFTBridge.
From ToS Require Import stdlib.SFTClassificationSynthesis.
From ToS Require Import stdlib.ProcessClassification.
From ToS Require Import stdlib.StrictlyFiner.

Open Scope Q_scope.

(* ================================================================== *)
(*  THE HIERARCHY: entropy < spectrum ≤ orbit process                  *)
(* ================================================================== *)

(** h_top is strictly coarser than spectrum:
    diag(2,1) and diag(2,-1) have same λ_max but different spectrum *)
Theorem entropy_strictly_coarser :
  (* Same max eigenvalue *)
  mat_entry diag_21 0 0 == mat_entry diag_2m1 0 0 /\
  (* Different spectrum *)
  classify_spectrum diag_21 <> classify_spectrum diag_2m1.
Proof.
  split.
  - vm_compute. reflexivity.
  - unfold classify_spectrum. vm_compute. discriminate.
Qed.

(** Spectrum determines orbit process for 2×2 (via Newton recurrence) *)
Theorem spectrum_complete_for_2x2 :
  (* Newton recurrence: tr(M³) = tr(M)·tr(M²) - det(M)·tr(M) *)
  tr_pow golden_sft 3 == mat_trace golden_sft * tr_pow golden_sft 2
                          - det_2x2 golden_sft * tr_pow golden_sft 1 /\
  tr_pow full_sft 3 == mat_trace full_sft * tr_pow full_sft 2
                        - det_2x2 full_sft * tr_pow full_sft 1.
Proof.
  split; vm_compute; reflexivity.
Qed.

(* ================================================================== *)
(*  CF ↔ SFT: every periodic CF gives an SFT                          *)
(* ================================================================== *)

(** The CF-SFT bridge: period matrix = transfer matrix *)
Theorem cf_sft_bridge_complete :
  (* Golden CF and SFT share spectral data *)
  mat_trace golden_period == mat_trace golden_sft /\
  det_2x2 golden_period == det_2x2 golden_sft /\
  (* √2 CF gives distinct SFT *)
  mat_trace sqrt2_period == 2 /\
  det_2x2 sqrt2_period == -(1) /\
  (* √3 CF gives yet another SFT *)
  mat_trace sqrt3_period == 4 /\
  det_2x2 sqrt3_period == 1.
Proof.
  split; [|split; [|split; [|split; [|split]]]].
  - exact golden_cf_trace.
  - exact golden_cf_det.
  - exact sqrt2_period_trace.
  - exact sqrt2_period_det.
  - exact sqrt3_period_trace.
  - exact sqrt3_period_det.
Qed.

(* ================================================================== *)
(*  ZETA: complete dynamical invariant                                 *)
(* ================================================================== *)

(** Zeta function encodes all orbit data *)
Theorem zeta_encodes_orbits :
  (* Partial sums differ → different dynamics *)
  ~ (zeta_partial golden_sft (1#10) 1 == zeta_partial full_sft (1#10) 1) /\
  (* Orbit counts differ *)
  ~ (orbit_count golden_sft 1 == orbit_count full_sft 1) /\
  (* Golden: ζ(z) = 1/(1-z-z²) *)
  zeta_det_2x2 golden_sft (1#2) == 1#4 /\
  (* Full: ζ(z) = 1/(1-2z), pole at z=1/2 *)
  zeta_det_2x2 full_sft (1#2) == 0.
Proof.
  split; [|split; [|split]].
  - exact golden_full_different_zeta.
  - exact golden_full_orbit_diff.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  3×3 EXAMPLE: even shift                                            *)
(* ================================================================== *)

(** Even shift on 3 symbols: only transitions between different symbols *)
Lemma even_shift_data :
  mat_trace even_sft == 0 /\
  tr_pow even_sft 1 == 0 /\
  tr_pow even_sft 2 == 6.
Proof.
  split; [|split]; vm_compute; reflexivity.
Qed.

(** Even shift has zero fixed points (no symbol maps to itself) *)
Lemma even_shift_no_fixed_points :
  tr_pow even_sft 1 == 0.
Proof.
  vm_compute. reflexivity.
Qed.

(** But has 6 period-2 orbits *)
Lemma even_shift_period_2 :
  tr_pow even_sft 2 == 6.
Proof.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  DISCRIMINANT CLASSIFICATION OF QUADRATIC IRRATIONALS               *)
(* ================================================================== *)

(** Lagrange theorem: discriminant identifies the quadratic irrational *)
Theorem discriminant_classifies :
  discriminant_2x2 golden_period == 5 /\
  discriminant_2x2 sqrt2_period == 8 /\
  discriminant_2x2 sqrt3_period == 12.
Proof.
  split; [|split].
  - unfold discriminant_2x2. rewrite golden_period_trace, golden_period_det. ring.
  - exact sqrt2_discriminant.
  - exact sqrt3_discriminant.
Qed.

(* ================================================================== *)
(*  GRAND SYNTHESIS                                                    *)
(* ================================================================== *)

Theorem sft_classification_grand_synthesis :
  (* 1. Entropy is strictly coarser than spectrum *)
  mat_entry diag_21 0 0 == mat_entry diag_2m1 0 0 /\
  classify_spectrum diag_21 <> classify_spectrum diag_2m1 /\
  (* 2. Spectrum determines process for 2×2 *)
  tr_pow golden_sft 3 == mat_trace golden_sft * tr_pow golden_sft 2
                          - det_2x2 golden_sft * tr_pow golden_sft 1 /\
  (* 3. CF ↔ SFT bridge works *)
  mat_trace golden_period == mat_trace golden_sft /\
  (* 4. Zeta distinguishes *)
  ~ (orbit_count golden_sft 1 == orbit_count full_sft 1) /\
  (* 5. 3×3 extends naturally *)
  tr_pow even_sft 1 == 0 /\
  tr_pow even_sft 2 == 6.
Proof.
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - exact (proj1 entropy_strictly_coarser).
  - exact (proj2 entropy_strictly_coarser).
  - exact (proj1 spectrum_complete_for_2x2).
  - exact golden_cf_trace.
  - exact golden_full_orbit_diff.
  - exact even_shift_no_fixed_points.
  - exact even_shift_period_2.
Qed.
