(* ProcessQMCrossValidation.v — QM cross-checks *)
From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import physics.HarmonicOscillator.
From ToS Require Import LinearAlgebra.
From ToS Require Import physics.SpinChain.

Open Scope Q_scope.

(** Harmonic oscillator: E_n = (2n+1)/2 *)
Theorem ho_spectrum :
  ho_energy 0 == 1 # 2 /\
  ho_energy 1 == 3 # 2 /\
  ho_energy 2 == 5 # 2 /\
  ho_energy 3 == 7 # 2.
Proof.
  unfold ho_energy, inject_Z. split; [|split; [|split]];
  unfold Qeq; simpl; lia.
Qed.

Lemma ho_gap : ho_energy 1 - ho_energy 0 == 1.
Proof. unfold ho_energy, inject_Z. unfold Qeq; simpl; lia. Qed.

Lemma ho_spacing_01 : ho_energy 1 - ho_energy 0 == 1.
Proof. unfold ho_energy, inject_Z. unfold Qeq; simpl; lia. Qed.

Lemma ho_spacing_12 : ho_energy 2 - ho_energy 1 == 1.
Proof. unfold ho_energy, inject_Z. unfold Qeq; simpl; lia. Qed.

Lemma ho_spacing_23 : ho_energy 3 - ho_energy 2 == 1.
Proof. unfold ho_energy, inject_Z. unfold Qeq; simpl; lia. Qed.

(** Ising eigenvalues: {+J, -J, -J, +J} *)
Theorem ising_ground :
  qv_nth (ising_eigenvals 1) 0 == 1.
Proof.
  unfold ising_eigenvals, qv_nth. simpl. ring.
Qed.

Lemma ising_gap :
  qv_nth (ising_eigenvals 1) 0 - qv_nth (ising_eigenvals 1) 1 == 2.
Proof.
  unfold ising_eigenvals, qv_nth. simpl. ring.
Qed.

Theorem qm_cross_validated :
  ho_energy 0 == 1 # 2 /\
  ho_energy 1 - ho_energy 0 == 1 /\
  qv_nth (ising_eigenvals 1) 0 == 1.
Proof.
  split; [|split].
  - unfold ho_energy, inject_Z. unfold Qeq; simpl; lia.
  - exact ho_gap.
  - exact ising_ground.
Qed.

Definition qm_xv_count := 7%nat.
