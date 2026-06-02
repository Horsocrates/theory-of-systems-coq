(** * ProcessL2HilbertSynthesis.v — Synthesis of the process-L²-Hilbert + QM-dynamics
      cluster (Part VI → physics): the bricks compose into one constructive picture

    Elements: the shared substrate — vectors nat→Q, the inner product seq_inner,
              operators as matrices via op_apply, all over ℚ
    Roles:    each file is a role in the unified L²-Hilbert / QM picture; this file is
              the role-composition — it verifies the bricks co-compile and the bridges hold
    Rules:    the laws compose: inner-product geometry (Cauchy–Schwarz → Bessel →
              Parseval) → completeness (Riesz–Fischer) → spectral structure (self-adjoint,
              compact) → dynamics (no finite CCR → q̂/p̂ → Schrödinger → conservation)

    THE CLUSTER (Part VI → physics; 14 files, 0 axioms throughout):
      Ярус 0 — foundation
        ProcessL2CauchySchwarz   : general Cauchy–Schwarz, inner product, polarization
        ProcessFubiniGeneral     : discrete Fubini (q_sum_swap), q_sum toolkit
      Ярус 1 — L²-Hilbert
        ProcessL2Triangle        : L² metric, sqrt-free triangle inequality
        ProcessCompactSpectral   : diagonal self-adjoint model, discrete spectrum λₙ→0
        ProcessL2Bessel          : one-direction Pythagoras + Bessel
        ProcessL2BesselGeneral   : GENERAL Bessel Σ⟨eₖ,f⟩² ≤ ‖f‖² (any ON system)
        ProcessL2Parseval        : Parseval equality ⟺ completeness criterion
        ProcessL2RieszFischer    : L² completeness BY CONSTRUCTION (constructed limit)
        ProcessSelfAdjointSpectral : ⟨Tv,w⟩=⟨v,Tw⟩, Rayleigh, eigenvector orthogonality
        ProcessHarmonicLadder    : [a,a†]=1, Eₙ=n+½ (not imported here — local `energy` clash)
      Ярус 2 — QM dynamics
        ProcessCanonicalCommutator : trace[A,B]=0 ⟹ NO finite-dimensional CCR
        ProcessPositionMomentum  : lattice q̂/p̂, commutator defect, q̂ eigenpairs
        ProcessSchrodingerEvolution : discrete unitary evolution conserves probability
        ProcessEnergyConservation : energy conserved under an energy-preserving step

    THREE SYNTHESIS BRIDGES (each composes ≥2 files):
      (1) signflip_conserves_norm_and_energy   — Schrödinger evolution conserves BOTH
                                                   probability and energy (E3 ∧ E4).
      (2) orthonormal_expansion_synthesis       — the ON expansion theorem: Bessel
                                                   inequality ∧ Parseval-completeness (Bessel ∧ Parseval).
      (3) position_selfadjoint_and_no_ccr       — q̂ is self-adjoint ∧ its canonical
                                                   commutator is not realisable finitely (PositionMomentum ∧ SelfAdjoint ∧ CCR).

    HONEST FRONTIER (shared P4 boundary of the cluster): the exact propagator e^{−iĤt},
    the existence of an eigenvector of an arbitrary compact operator ("sup attained"),
    the completed infinite-dimensional ℓ²/L² (N→∞), a non-separable basis (Zorn), and the
    continuous spectrum as a built object — all role-limits.

    ============ E/R/R разбор ============
      Rules (L5): законы кластера компонуются (геометрия→полнота→спектр→динамика); три моста.
      Roles (L4): каждый файл = роль; синтез = роль-композиция + проверка co-compile.
      Elements  : общий субстрат nat→Q, seq_inner, op_apply над ℚ (L1+P4).
    ДИАГНОСТИКА: весь кластер процессно-конечен, 0 акс; синтез верифицирует композицию и
    мосты; общие P4-границы (e^{−iĤt}, завершённый ℓ², sup-достигается) — единый фронтир.

    STATUS: 3 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.   (* q_sum *)
(* Ярус 0 *)
From ToS Require Import process.ProcessL2CauchySchwarz.
From ToS Require Import process.ProcessFubiniGeneral.
(* Ярус 1 *)
From ToS Require Import process.ProcessL2Triangle.
From ToS Require Import process.ProcessCompactSpectral.
From ToS Require Import process.ProcessL2Bessel.
From ToS Require Import process.ProcessL2BesselGeneral.
From ToS Require Import process.ProcessL2Parseval.
From ToS Require Import process.ProcessL2RieszFischer.
From ToS Require Import process.ProcessSelfAdjointSpectral.
(* Ярус 2 *)
From ToS Require Import process.ProcessCanonicalCommutator.
From ToS Require Import process.ProcessPositionMomentum.
From ToS Require Import process.ProcessSchrodingerEvolution.
From ToS Require Import process.ProcessEnergyConservation.

Open Scope Q_scope.

(* ===================================================================== *)
(*  Bridge 1 (E3 ∧ E4): the sign-flip evolution conserves BOTH probability *)
(*  (norm) and energy, for all time steps.                                 *)
(* ===================================================================== *)

Theorem signflip_conserves_norm_and_energy :
  forall (e0 e1 : Q) (v : nat -> Q) (n : nat),
  seq_inner (evolve signflip 2 v n) (evolve signflip 2 v n) 2 == seq_inner v v 2
  /\ energy (Hdiag e0 e1) (evolve signflip 2 v n) 2 == energy (Hdiag e0 e1) v 2.
Proof.
  intros e0 e1 v n. split.
  - apply evolution_conserves_norm. apply signflip_isometry.
  - apply evolution_signflip_conserves_energy.
Qed.

(* ===================================================================== *)
(*  Bridge 2 (Bessel ∧ Parseval): the orthonormal-expansion theorem.       *)
(*  For an ON system, Bessel's inequality holds, and equality (Parseval)   *)
(*  characterises completeness.                                            *)
(* ===================================================================== *)

Theorem orthonormal_expansion_synthesis :
  forall (e : nat -> nat -> Q) (N : nat),
  (forall i j, seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0)) ->
  forall (f : nat -> Q) (K : nat),
  q_sum (fun k => seq_inner (e k) f N * seq_inner (e k) f N) K <= seq_inner f f N
  /\ ((q_sum (fun k => seq_inner (e k) f N * seq_inner (e k) f N) K == seq_inner f f N)
      <-> (forall m, (m < N)%nat ->
             q_sum (fun k => seq_inner (e k) f N * e k m) K == f m)).
Proof.
  intros e N Hon f K. split.
  - apply (bessel_general e N Hon f K).
  - apply (parseval_iff_complete e N Hon f K).
Qed.

(* ===================================================================== *)
(*  Bridge 3 (PositionMomentum ∧ SelfAdjoint ∧ CCR): the position operator *)
(*  is self-adjoint, yet its canonical commutator cannot be c·I (c≠0) in    *)
(*  finite dimension — the structural reason q̂,p̂ are unbounded.            *)
(* ===================================================================== *)

Theorem position_selfadjoint_and_no_ccr :
  forall (x : nat -> Q) (N : nat),
  op_symmetric (qhat x) N
  /\ (forall (B : nat -> nat -> Q) (c : Q),
        (1 <= N)%nat ->
        (forall i j, (i < N)%nat -> (j < N)%nat ->
           mat_sub (mat_mul (qhat x) B N) (mat_mul B (qhat x) N) i j
           == mat_scal c mat_id i j) ->
        c == 0).
Proof.
  intros x N. split.
  - apply position_symmetric.
  - intros B c HN Hcomm. exact (no_finite_ccr (qhat x) B c N HN Hcomm).
Qed.

Print Assumptions signflip_conserves_norm_and_energy.
Print Assumptions orthonormal_expansion_synthesis.
Print Assumptions position_selfadjoint_and_no_ccr.
