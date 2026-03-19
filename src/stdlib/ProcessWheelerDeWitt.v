(* ProcessWheelerDeWitt.v — QG as eigenvalue problem *)
From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import stdlib.ProcessOperatorF.
From ToS Require Import stdlib.ProcessDiscreteOperator.
From ToS Require Import process.ProcessRegge.
Open Scope Q_scope.

(** ★ WHEELER-DEWITT: H_grav |Ψ> = 0 *)
(** On Regge lattice: state = edge lengths, H = kinetic + Regge action *)

Definition gravity_potential (valence : nat) (ell : Q) : Q :=
  deficit_angle valence * triangle_area ell.

Lemma gravity_potential_flat : forall ell,
  gravity_potential 6 ell == 0.
Proof. intros. unfold gravity_potential. rewrite deficit_flat. ring. Qed.

Lemma gravity_potential_curved :
  gravity_potential 5 1 == (22#21) * (433#1000).
Proof. unfold gravity_potential. rewrite deficit_5. reflexivity. Qed.

Definition wdw_hamiltonian (valence : nat) : ProcessOp :=
  fun psi => fun k =>
    - (second_diff psi k) + gravity_potential valence 1 * psi k.

(** WDW equation: H_grav · Ψ = 0 *)
Definition satisfies_WDW (psi : RealProcess) (valence : nat) : Prop :=
  forall k, wdw_hamiltonian valence psi k == 0.

(** Flat space (valence=6): potential = 0 → -Δ²ψ = 0 → ψ = const *)
Theorem flat_satisfies_WDW :
  satisfies_WDW (const_process 1) 6.
Proof.
  intros k. unfold wdw_hamiltonian. rewrite gravity_potential_flat.
  rewrite second_diff_formula. unfold const_process. ring.
Qed.

(** Zero state satisfies any WDW *)
Lemma zero_satisfies_WDW : forall v,
  satisfies_WDW (const_process 0) v.
Proof.
  intros v k. unfold wdw_hamiltonian. rewrite second_diff_formula.
  unfold const_process. ring.
Qed.

(** WDW eigenvalue: kinetic_n - potential *)
Definition wdw_eigenvalue (valence : nat) (n : nat) : Q :=
  inject_Z (Z.of_nat (n * n)) - gravity_potential valence 1.

Lemma wdw_eigenvalue_flat : forall n, wdw_eigenvalue 6 n == inject_Z (Z.of_nat (n * n)).
Proof. intros. unfold wdw_eigenvalue. rewrite gravity_potential_flat. ring. Qed.

(** WDW constraint: E = 0 → n_physical where kinetic = potential *)

Theorem wheeler_dewitt_foundation :
  satisfies_WDW (const_process 1) 6 /\
  gravity_potential 6 1 == 0 /\
  gravity_potential 5 1 == (22#21) * (433#1000).
Proof.
  split; [|split].
  - exact flat_satisfies_WDW.
  - exact (gravity_potential_flat 1).
  - exact gravity_potential_curved.
Qed.

Definition wdw_count := 8%nat.
