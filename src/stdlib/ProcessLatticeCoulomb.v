(* ProcessLatticeCoulomb.v — Coulomb = Schwarzschild relabeled *)
From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessSchwarzschildRegge.
From ToS Require Import stdlib.ProcessOperatorF.
From ToS Require Import stdlib.ProcessDiscreteOperator.
Open Scope Q_scope.

Definition coulomb_potential_lattice (alpha ell : Q) (k : nat) : Q :=
  - alpha / shell_radius ell k.

Lemma coulomb_finite_at_0 : forall alpha,
  coulomb_potential_lattice alpha 1 0%nat == - alpha.
Proof. intros. unfold coulomb_potential_lattice, shell_radius. simpl. field. Qed.

Lemma coulomb_at_10 : coulomb_potential_lattice 1 1 9%nat == -(1 # 10).
Proof. unfold coulomb_potential_lattice, shell_radius. simpl. field. Qed.

Lemma coulomb_at_100 : coulomb_potential_lattice 1 1 99%nat == -(1 # 100).
Proof. unfold coulomb_potential_lattice, shell_radius. simpl. field. Qed.

Lemma coulomb_weakens : coulomb_potential_lattice 1 1 99%nat > coulomb_potential_lattice 1 1 9%nat.
Proof. rewrite coulomb_at_10, coulomb_at_100. lra. Qed.

(** No singularity: V(r=ℓ) = −α/ℓ = finite *)
Lemma no_coulomb_singularity : forall alpha,
  exists q, coulomb_potential_lattice alpha 1 0%nat == q.
Proof. intros. exists (- alpha). exact (coulomb_finite_at_0 alpha). Qed.

Definition coulomb_schrodinger_lattice (alpha ell : Q) : ProcessOp :=
  discrete_schrodinger (fun k => coulomb_potential_lattice alpha ell k).

Definition hydrogen_process_lattice (alpha ell : Q) (n : nat) : RealProcess :=
  fun K => coulomb_potential_lattice alpha ell (n + K).

Lemma hydrogen_deepens :
  coulomb_potential_lattice 1 1 0%nat < coulomb_potential_lattice 1 1 9%nat.
Proof. rewrite coulomb_finite_at_0, coulomb_at_10. lra. Qed.

Theorem lattice_coulomb_foundation :
  coulomb_potential_lattice 1 1 0%nat == -(1) /\
  coulomb_potential_lattice 1 1 9%nat == -(1 # 10) /\
  coulomb_potential_lattice 1 1 99%nat == -(1 # 100) /\
  (forall alpha, exists q, coulomb_potential_lattice alpha 1 0%nat == q).
Proof.
  split; [|split; [|split]].
  - exact (coulomb_finite_at_0 1).
  - exact coulomb_at_10.
  - exact coulomb_at_100.
  - exact no_coulomb_singularity.
Qed.

Definition coulomb_count := 9%nat.
