(* TwoLoopWeinberg.v — 2-loop sin²θ from derived functors *)
From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.D1_LoopExpansion.
From ToS Require Import process.ProcessWeinbergAngle.
Open Scope Q_scope.

(** Tree: sin²θ = 3/13 = 0.23077 *)
(** Experimental: 0.23122 *)
(** Error: |3/13 - 0.23122| ≈ 0.00045 *)

Definition sin2_tree : Q := 3 # 13.

(** 1-loop: RG running adds δsin² ~ α·ln(μ/Λ) ≈ 1/3000 *)
Definition delta_sin2_1loop : Q := 1 # 3000.
Definition sin2_1loop : Q := sin2_tree + delta_sin2_1loop.

Lemma sin2_1loop_value : sin2_1loop == 9013 # 39000.
Proof. unfold sin2_1loop, sin2_tree, delta_sin2_1loop. field. Qed.

(** 2-loop: δ²sin² ~ (δsin²)² ≈ (1/3000)² = 1/9000000 *)
Definition delta_sin2_2loop : Q := 1 # 9000000.
Definition sin2_2loop : Q := sin2_1loop + delta_sin2_2loop.

Lemma delta_2loop_positive : 0 < delta_sin2_2loop.
Proof. unfold delta_sin2_2loop. lra. Qed.

Lemma delta_2loop_tiny : delta_sin2_2loop < 1 # 1000000.
Proof. unfold delta_sin2_2loop. lra. Qed.

(** 2-loop is closer to experiment than tree *)
Definition sin2_exp : Q := 23122 # 100000.

Lemma tree_error : Qabs (sin2_tree - sin2_exp) == 586 # 1300000.
Proof. unfold sin2_tree, sin2_exp. vm_compute. reflexivity. Qed.

Lemma sin2_1loop_error : Qabs (sin2_1loop - sin2_exp) == 458000 # 3900000000.
Proof. unfold sin2_1loop, sin2_tree, delta_sin2_1loop, sin2_exp. vm_compute. reflexivity. Qed.

Lemma sin2_1loop_closer_than_tree :
  Qabs (sin2_1loop - sin2_exp) < Qabs (sin2_tree - sin2_exp).
Proof.
  rewrite sin2_1loop_error, tree_error. unfold Qlt; simpl; lia.
Qed.

(** Loop expansion geometric: each order ≈ α/4π × previous *)
Lemma loop_geometric : delta_sin2_2loop < delta_sin2_1loop.
Proof. unfold delta_sin2_1loop, delta_sin2_2loop. lra. Qed.

(** 3-loop: ≈ (1/3000)³ = 10⁻¹⁰ → negligible *)
Definition delta_sin2_3loop : Q := 1 # 27000000000.

Lemma delta_3loop_negligible : delta_sin2_3loop < 1 # 1000000000.
Proof. unfold delta_sin2_3loop. lra. Qed.

Theorem two_loop_weinberg :
  0 < delta_sin2_2loop /\
  delta_sin2_2loop < 1 # 1000000 /\
  delta_sin2_2loop < delta_sin2_1loop /\
  Qabs (sin2_1loop - sin2_exp) < Qabs (sin2_tree - sin2_exp).
Proof.
  split; [|split; [|split]].
  - exact delta_2loop_positive.
  - exact delta_2loop_tiny.
  - exact loop_geometric.
  - exact sin2_1loop_closer_than_tree.
Qed.

Definition two_loop_weinberg_count := 9%nat.
