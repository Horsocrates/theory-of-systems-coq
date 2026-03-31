(** * LevelStructure.v — L5 → levels → why metric (Level 0), not Riemann
    Elements: GeometricLevel, DOF_at_level, U1_level
    Roles:    U(1)_Y = pointwise = Level 0. Riemann = Level 2.
    Rules:    Local symmetry acts at Level 0. n_metric = 10 is DERIVED.
    STATUS:   5 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: March 2026
*)

From Stdlib Require Import Lia PeanoNat.

Inductive GeometricLevel :=
  | Level0_Pointwise
  | Level1_FirstDeriv
  | Level2_SecondDeriv.

Definition DOF_at_level (D : nat) (l : GeometricLevel) : nat :=
  match l with
  | Level0_Pointwise  => (D * (D + 1) / 2)%nat
  | Level1_FirstDeriv  => (D * D * (D + 1) / 2)%nat
  | Level2_SecondDeriv => (D * D * (D * D - 1) / 12)%nat
  end.

Definition U1_level : GeometricLevel := Level0_Pointwise.
Definition n_ambient : nat := DOF_at_level 4 U1_level.

Lemma level0_D4 : DOF_at_level 4 Level0_Pointwise = 10%nat.
Proof. reflexivity. Qed.

Lemma level2_D4 : DOF_at_level 4 Level2_SecondDeriv = 20%nat.
Proof. reflexivity. Qed.

Lemma U1_is_level0 : U1_level = Level0_Pointwise.
Proof. reflexivity. Qed.

Lemma n_ambient_is_10 : n_ambient = 10%nat.
Proof. reflexivity. Qed.

Theorem level_structure_synthesis :
  DOF_at_level 4 Level0_Pointwise = 10%nat /\
  DOF_at_level 4 Level2_SecondDeriv = 20%nat /\
  n_ambient = 10%nat.
Proof.
  split; [exact level0_D4 |
  split; [exact level2_D4 |
  exact n_ambient_is_10]].
Qed.
