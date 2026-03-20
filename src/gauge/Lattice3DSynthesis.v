(** * Lattice3DSynthesis.v -- 3D lattice synthesis
    Elements: su3_3d_complete
    Roles:    Unify lattice geometry with SU(3) gap
    Rules:    64-site lattice, gap > 0, Z > 0
    Status:   Gauge
    STATUS: 5 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import gauge.Lattice3D.
From ToS Require Import gauge.SU3Transfer.
From ToS Require Import gauge.SU3Lattice3D.

Open Scope Q_scope.

Lemma lattice_is_3d :
  num_sites_3d 4 = 64%nat /\ num_links_3d 4 = 192%nat.
Proof. split; reflexivity. Qed.

Lemma gap_and_Z :
  gap_su3 1 == 5#6 /\ 0 < Z_su3_approx 1.
Proof.
  split; [exact gap_su3_at_1 | exact Z_su3_positive_1].
Qed.

Lemma spatial_enhances_gap :
  gap_su3_3d 1 (1#100) > gap_su3_3d 1 0.
Proof. exact gap_3d_gt_1d. Qed.

Theorem su3_3d_complete :
  num_sites_3d 4 = 64%nat /\
  gap_su3 1 == 5#6 /\
  0 < Z_su3_approx 1 /\
  0 < gap_su3_3d 1 0.
Proof.
  split; [|split; [|split]].
  - exact lattice_4cube_sites.
  - exact gap_su3_at_1.
  - exact Z_su3_positive_1.
  - exact gap_su3_3d_positive_1_0.
Qed.

Theorem phase2_complete :
  num_sites_3d 2 = 8%nat /\
  wilson_action_3d 1 1 3 == 0 /\
  gap_su3_3d 1 0 == 5#6.
Proof.
  split; [|split].
  - exact lattice_2cube_sites.
  - exact action_at_zero_field.
  - exact gap_su3_3d_at_1_0.
Qed.
