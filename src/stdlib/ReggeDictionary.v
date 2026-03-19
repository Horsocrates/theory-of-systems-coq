(* ReggeDictionary.v — Regge <-> Riemannian dictionary *)
From Stdlib Require Import QArith QArith_base Lia.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.
From ToS Require Import process.ProcessRegge.
Open Scope Q_scope.

Definition curvature_density (deficit area : Q) : Q := deficit / area.

Lemma curvature_density_flat :
  curvature_density 0 (433#1000) == 0.
Proof. unfold curvature_density. field. Qed.

Lemma curvature_density_val5 :
  curvature_density (22#21) (433#1000) == 22000 # 9093.
Proof. unfold curvature_density. field. Qed.

Lemma curvature_density_val7 :
  curvature_density (-(22#21)) (433#1000) == -(22000 # 9093).
Proof. unfold curvature_density. field. Qed.

Definition loop_holonomy (deficits : list Q) : Q :=
  fold_left Qplus deficits 0.

Lemma holonomy_nil : loop_holonomy nil == 0.
Proof. reflexivity. Qed.

Definition geodesic_deviation (R_curv dist : Q) : Q := R_curv * dist * dist.

Lemma deviation_flat : forall d, geodesic_deviation 0 d == 0.
Proof. intros. unfold geodesic_deviation. ring. Qed.

Lemma deviation_concrete : geodesic_deviation (22#21) 1 == 22 # 21.
Proof. unfold geodesic_deviation. ring. Qed.

Theorem regge_dictionary :
  curvature_density 0 (433#1000) == 0 /\
  curvature_density (22#21) (433#1000) == 22000 # 9093 /\
  deficit_angle 6 == 0.
Proof.
  split; [|split].
  - exact curvature_density_flat.
  - exact curvature_density_val5.
  - exact deficit_flat.
Qed.

Definition regge_dict_count := 8%nat.
