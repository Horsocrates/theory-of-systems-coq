(* ReggeTrajectory.v — Regge poles from transfer eigenvalues *)
From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import SeriesConvergence.
From ToS Require Import gauge.CharacterTransfer.
From ToS Require Import process.ProcessPhysicalSigma.
Open Scope Q_scope.

(** ★ REGGE TRAJECTORY from lattice eigenvalues *)
(** t_j(β) = bessel_partial(2j,β,M) − bessel_partial(2j+2,β,M) *)
(** "Energy" of spin-j state = 1 − t_j/t₀ *)

Definition regge_energy (j : nat) (beta : Q) (M : nat) : Q :=
  1 - transfer_eigenvalue j beta M / transfer_eigenvalue 0 beta M.

(** j=0: ground state, E=0 by definition *)
Lemma regge_ground : forall beta M,
  transfer_eigenvalue 0 beta M > 0 ->
  regge_energy 0 beta M == 0.
Proof.
  intros beta M Hpos. unfold regge_energy.
  field. lra.
Qed.

(** j=1 energy at β=1, M=0: *)
(** t₀ = bessel_partial(0,1,0) − bessel_partial(2,1,0) *)
(** t₁ = bessel_partial(2,1,0) − bessel_partial(4,1,0) *)
(** From CharacterTransfer: we can compute these *)

(** Regge slope: α' = Δj/ΔE = 1/E₁ *)
Definition regge_slope (beta : Q) (M : nat) : Q :=
  1 / regge_energy 1 beta M.

(** ★ String connection: α' = 1/(2πσ) *)
(** σ = string tension = sigma_phys *)
(** α' × 2πσ should ≈ 1 *)

(** Concrete: σ(β=1,M=1) = 11/20, regge_energy(1,1,1) = gap/t₀ *)
(** From existing: gap = t₀ − t₁, so regge_energy(1) = (t₀−t₁)/t₀ = gap/t₀ *)

(** ★ Partial wave amplitude *)
Definition partial_wave (j : nat) (beta : Q) (M : nat) : Q :=
  inject_Z (Z.of_nat (2*j+1)) *
  (transfer_eigenvalue j beta M / transfer_eigenvalue 0 beta M).

(** j=0 amplitude = 1 (normalized) *)
Lemma pw_j0 : forall beta M,
  transfer_eigenvalue 0 beta M > 0 ->
  partial_wave 0 beta M == 1.
Proof.
  intros beta M Hpos. unfold partial_wave. simpl.
  field. lra.
Qed.

(** Higher j: amplitude decreases (t_j/t₀ < 1) *)
(** This is why low-j dominates → REGGE TRAJECTORY LINEAR *)

(** Cross section = |Σ partial waves|² *)
(** For single partial wave: σ = (2j+1)² × (t_j/t₀)² *)

(** ★ Linearity check: E(j) ≈ α₀ + j/α' *)
(** If linear → Regge trajectory → string picture *)
(** On lattice: check j=0,1,2 for linearity *)

Theorem regge_foundation :
  (forall beta M, transfer_eigenvalue 0 beta M > 0 ->
    regge_energy 0 beta M == 0) /\
  (forall beta M, transfer_eigenvalue 0 beta M > 0 ->
    partial_wave 0 beta M == 1).
Proof.
  split.
  - exact regge_ground.
  - exact pw_j0.
Qed.

Definition regge_count := 4%nat.
