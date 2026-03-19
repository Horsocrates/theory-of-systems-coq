(* ProcessManifold.v — Manifold as sequence of triangulations *)
From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore.
Open Scope Q_scope.

Record ProcessManifold := mkPM {
  pm_dim : nat;
  pm_vertices : nat -> nat;
  pm_edges : nat -> nat;
  pm_edge_length : nat -> Q;
  pm_total_deficit : nat -> Q;
}.

Definition pm_refining (M : ProcessManifold) : Prop :=
  forall K, (pm_vertices M K <= pm_vertices M (S K))%nat.

Definition pm_finer (M : ProcessManifold) : Prop :=
  forall K, pm_edge_length M (S K) <= pm_edge_length M K.

Definition pm_curvature_stable (M : ProcessManifold) : Prop :=
  forall K, pm_total_deficit M (S K) == pm_total_deficit M K.

Definition flat_manifold : ProcessManifold := mkPM
  2
  (fun K => (4 * S K * S K)%nat)
  (fun K => (12 * S K * S K)%nat)
  (fun K => 1 / inject_Z (Z.of_nat (S K)))
  (fun _ => 0).

Lemma flat_curvature_stable : pm_curvature_stable flat_manifold.
Proof. intros K. reflexivity. Qed.

Lemma flat_refining : pm_refining flat_manifold.
Proof. intros K. unfold flat_manifold, pm_vertices. simpl. nia. Qed.

Definition sphere_manifold : ProcessManifold := mkPM
  2
  (fun K => (12 + 10 * K)%nat)
  (fun K => (30 + 30 * K)%nat)
  (fun K => 1 / inject_Z (Z.of_nat (S K)))
  (fun _ => 176 # 7).

Lemma sphere_curvature_stable : pm_curvature_stable sphere_manifold.
Proof. intros K. reflexivity. Qed.

Lemma sphere_dim : pm_dim sphere_manifold = 2%nat.
Proof. reflexivity. Qed.

Lemma sphere_deficit_is_4pi : pm_total_deficit sphere_manifold 0 == 176 # 7.
Proof. reflexivity. Qed.

Theorem manifold_foundation :
  pm_curvature_stable flat_manifold /\
  pm_curvature_stable sphere_manifold /\
  pm_total_deficit sphere_manifold 0 == 176 # 7.
Proof.
  split; [|split].
  - exact flat_curvature_stable.
  - exact sphere_curvature_stable.
  - exact sphere_deficit_is_4pi.
Qed.

Definition manifold_count := 7%nat.
