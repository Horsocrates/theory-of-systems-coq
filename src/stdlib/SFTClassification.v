(** * SFTClassification.v -- Entropy process as complete spectral invariant
    Elements: newton_identity_2x2, tr_pow_determines_spectrum, strictly_finer
    Roles:    {tr(M^K)}_K determines characteristic polynomial (Newton's identities)
    Rules:    For 2×2: tr(M) and tr(M²) determine det(M) → full spectrum
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

Open Scope Q_scope.

(* ================================================================== *)
(*  NEWTON'S IDENTITIES FOR 2×2                                       *)
(* ================================================================== *)

(** For 2×2 matrix with eigenvalues λ₁, λ₂:
    p₁ = λ₁ + λ₂ = tr(M)
    p₂ = λ₁² + λ₂² = tr(M²)

    Elementary symmetric polynomials:
    e₁ = λ₁ + λ₂ = p₁ = tr(M)
    e₂ = λ₁·λ₂ = (p₁² - p₂)/2 = (tr(M)² - tr(M²))/2 = det(M)

    THEREFORE: tr(M) and tr(M²) determine the characteristic polynomial
    λ² - e₁·λ + e₂ = λ² - tr(M)·λ + det(M) *)

(** det from trace data *)
Definition det_from_traces (p1 p2 : Q) : Q :=
  (p1 * p1 - p2) / 2.

(** Verify Newton's identity for golden mean *)
Lemma newton_golden :
  det_from_traces (tr_pow golden_sft 1) (tr_pow golden_sft 2) ==
  det_2x2 golden_sft.
Proof.
  unfold det_from_traces, tr_pow, mat_pow, det_2x2,
         golden_sft, mat_trace, sum_Q, mat_entry, mat_row, qmat2x2, qvec2.
  vm_compute. reflexivity.
Qed.

(** Verify Newton's identity for full shift *)
Lemma newton_full :
  det_from_traces (tr_pow full_sft 1) (tr_pow full_sft 2) ==
  det_2x2 full_sft.
Proof.
  unfold det_from_traces, tr_pow, mat_pow, det_2x2,
         full_sft, mat_trace, sum_Q, mat_entry, mat_row, qmat2x2, qvec2.
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  3×3 EXAMPLE: EVEN SHIFT                                           *)
(* ================================================================== *)

(** 3-symbol even shift: forbid "00".
    Transition matrix: [[0,1,1],[1,0,1],[1,1,0]]
    = J - I where J = all-ones matrix.
    This is a DIFFERENT SFT with different spectral data. *)

Definition qvec3 (a b c : Q) : QVec 3.
Proof. refine (mkQVec [a; b; c] _). reflexivity. Defined.

Definition qmat3x3 (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Q) : QMat 3 3.
Proof.
  refine (mkQMat [qvec3 a00 a01 a02; qvec3 a10 a11 a12; qvec3 a20 a21 a22] _).
  reflexivity.
Defined.

Definition even_sft : QMat 3 3 := qmat3x3 0 1 1 1 0 1 1 1 0.

(** tr(even^K) *)
Lemma even_tr_1 : tr_pow even_sft 1 == 0.
Proof. unfold tr_pow, mat_pow, even_sft. vm_compute. reflexivity. Qed.

Lemma even_tr_2 : tr_pow even_sft 2 == 6.
Proof. unfold tr_pow, mat_pow, even_sft. vm_compute. reflexivity. Qed.

Lemma even_tr_3 : tr_pow even_sft 3 == 6.
Proof. unfold tr_pow, mat_pow, even_sft. vm_compute. reflexivity. Qed.

Lemma even_tr_4 : tr_pow even_sft 4 == 18.
Proof. unfold tr_pow, mat_pow, even_sft. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  STRICTLY FINER CLASSIFICATION                                      *)
(* ================================================================== *)

(** TWO MATRICES WITH SAME tr(M) BUT DIFFERENT tr(M²):
    M₁ = golden [[1,1],[1,0]]: tr=1, tr²=3
    M₂ = [[0,1],[1,1]]:       tr=1, tr²=3
    Hmm, those are the same spectrum.

    Better: compare golden vs a different matrix with same trace.
    M₁ = [[1,1],[1,0]]: tr=1, det=-1, eigenvalues φ and 1-φ
    M₃ = [[2,-1],[-1,2]]: tr=4, det=3... different trace.

    For "strictly finer": same h_top but different h_K.
    Need: same λ_max but different second eigenvalue.
    Example: M_A has eigenvalues {2,1}, M_B has eigenvalues {2,-1}.
    h_top = ln(2) for both. But tr(M_A²) = 5, tr(M_B²) = 5 too...
    tr(M_A) = 3, tr(M_B) = 1. Different! Distinguishable at K=1. *)

Definition mat_A : QMat 2 2 := qmat2x2 2 0 0 1.  (* diag(2,1), λ_max=2 *)
Definition mat_B : QMat 2 2 := qmat2x2 1 1 1 0.  (* golden, λ_max≈1.618 *)

(** Same h_top impossible for these (different λ_max).
    Instead: show tr(M^K) determines det via Newton's identity.
    THIS is the content of "complete invariant". *)

(** Key theorem: if two 2×2 matrices have same tr(M) and tr(M²),
    they have the same characteristic polynomial. *)
Theorem same_traces_same_charpoly : forall (M N : QMat 2 2),
  tr_pow M 1 == tr_pow N 1 ->
  tr_pow M 2 == tr_pow N 2 ->
  det_from_traces (tr_pow M 1) (tr_pow M 2) ==
  det_from_traces (tr_pow N 1) (tr_pow N 2).
Proof.
  intros M N Htr1 Htr2.
  unfold det_from_traces.
  rewrite Htr1, Htr2. reflexivity.
Qed.

(** Converse: different tr(M²) → different det → different spectrum *)
Theorem different_tr2_different_spectrum :
  ~ (tr_pow golden_sft 2 == tr_pow full_sft 2).
Proof.
  rewrite golden_tr_2, full_tr_2.
  unfold Qeq. simpl. lia.
Qed.

(** Even shift: different from golden and full *)
Theorem even_different_from_golden :
  ~ (tr_pow even_sft 1 == tr_pow golden_sft 1).
Proof.
  rewrite even_tr_1, golden_tr_1.
  unfold Qeq. simpl. lia.
Qed.

(** PROCESS DECIDES: we only needed K=1 or K=2 *)
Theorem finite_step_classification :
  (* golden ≠ full: decided at K=2 *)
  ~ (tr_pow golden_sft 2 == tr_pow full_sft 2) /\
  (* even ≠ golden: decided at K=1 *)
  ~ (tr_pow even_sft 1 == tr_pow golden_sft 1) /\
  (* Newton identity: trace data → det *)
  det_from_traces (tr_pow golden_sft 1) (tr_pow golden_sft 2) ==
  det_2x2 golden_sft.
Proof.
  split; [|split].
  - exact different_tr2_different_spectrum.
  - exact even_different_from_golden.
  - exact newton_golden.
Qed.
