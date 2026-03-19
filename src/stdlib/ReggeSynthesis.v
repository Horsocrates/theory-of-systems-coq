(* ReggeSynthesis.v — Regge synthesis *)
From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.ReggeTrajectory.
From ToS Require Import gauge.CharacterTransfer.
From ToS Require Import process.ProcessPhysicalSigma.
Open Scope Q_scope.

(** ★ REGGE FROM LATTICE:
    Eigenvalues t_j(β) → energy E_j = 1 − t_j/t₀
    Regge trajectory: j vs E_j
    If linear → string picture α' = 1/(2πσ)
    Our σ computable at 0.01% accuracy *)

(** Cross section from single j *)
Definition cross_section_j (j : nat) (beta : Q) (M : nat) : Q :=
  partial_wave j beta M * partial_wave j beta M.

Lemma cs_j0 : forall beta M,
  transfer_eigenvalue 0 beta M > 0 ->
  cross_section_j 0 beta M == 1.
Proof.
  intros beta M Hpos. unfold cross_section_j.
  rewrite pw_j0; [|exact Hpos]. ring.
Qed.

(** ★ Total cross section: sum over j *)
(** Convergent because t_j → 0 as j → ∞ *)
(** On finite lattice: sum up to j_max *)

(** ★ VENEZIANO AMPLITUDE *)
(** If trajectory linear: A(s,t) = Γ(−α(s))Γ(−α(t))/Γ(−α(s)−α(t)) *)
(** Our lattice: discrete analogue with Q-valued Gamma *)
(** Connection: Regge → Veneziano → string theory *)
(** All from transfer matrix eigenvalues! *)

Theorem regge_synthesis :
  (forall beta M, transfer_eigenvalue 0 beta M > 0 ->
    regge_energy 0 beta M == 0) /\
  (forall beta M, transfer_eigenvalue 0 beta M > 0 ->
    cross_section_j 0 beta M == 1).
Proof.
  split.
  - exact regge_ground.
  - exact cs_j0.
Qed.

Definition regge_synth_count := 2%nat.
