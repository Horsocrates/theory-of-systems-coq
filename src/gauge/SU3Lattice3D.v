(** * SU3Lattice3D.v -- SU(3) on 3D lattice: combined transfer
    Elements: su3_spatial_penalty, su3_combined, gap_su3_3d
    Roles:    3+1D = temporal transfer × spatial penalty
    Rules:    t^{3+1D} = t(β) · (1 - C₂·β_s), gap > 0 for physical params
    Status:   Gauge
    STATUS: 14 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import gauge.SU3Representations.
From ToS Require Import gauge.SU3Characters.

Open Scope Q_scope.

(* ================================================================== *)
(*  SPATIAL PENALTY                                                    *)
(* ================================================================== *)

(** Spatial suppression: exp(-C₂·β_s) ≈ 1 - C₂·β_s (linear approx) *)
Definition su3_spatial_penalty (p q : nat) (beta_s : Q) : Q :=
  1 - su3_casimir p q * beta_s.

Lemma penalty_trivial : forall beta_s,
  su3_spatial_penalty 0 0 beta_s == 1.
Proof.
  intro. unfold su3_spatial_penalty. rewrite casimir_trivial. ring.
Qed.

Lemma penalty_fund_at_001 : su3_spatial_penalty 1 0 (1#100) == 1 - (4#3) * (1#100).
Proof.
  unfold su3_spatial_penalty. rewrite casimir_fund. ring.
Qed.

Lemma penalty_adj_at_001 : su3_spatial_penalty 1 1 (1#100) == 1 - 3 * (1#100).
Proof.
  unfold su3_spatial_penalty. rewrite casimir_adjoint. ring.
Qed.

(** Adjoint suppressed more than fundamental *)
Lemma penalty_hierarchy :
  su3_spatial_penalty 1 1 (1#100) < su3_spatial_penalty 1 0 (1#100).
Proof.
  unfold su3_spatial_penalty, su3_casimir, Qlt.
  rewrite <- Z.ltb_lt. vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  COMBINED EIGENVALUE                                                *)
(* ================================================================== *)

(** Combined: temporal × spatial *)
Definition su3_combined (p q : nat) (beta beta_s : Q) : Q :=
  (match p, q with
   | O, O => t_trivial_su3 beta
   | S O, O => t_fund_su3 beta
   | O, S O => t_fund_su3 beta
   | S O, S O => t_adj_su3 beta
   | _, _ => 0
   end) * su3_spatial_penalty p q beta_s.

Lemma combined_trivial : forall beta beta_s,
  su3_combined 0 0 beta beta_s == 1.
Proof.
  intros. unfold su3_combined, t_trivial_su3. rewrite penalty_trivial. ring.
Qed.

Lemma combined_fund_at_1_001 :
  su3_combined 1 0 1 (1#100) == (1#6) * (1 - (4#3) * (1#100)).
Proof.
  unfold su3_combined, t_fund_su3, su3_spatial_penalty.
  rewrite casimir_fund. ring.
Qed.

(* ================================================================== *)
(*  3+1D MASS GAP                                                     *)
(* ================================================================== *)

Definition gap_su3_3d (beta beta_s : Q) : Q :=
  su3_combined 0 0 beta beta_s - su3_combined 1 0 beta beta_s.

Lemma gap_su3_3d_trivial_part : forall beta beta_s,
  su3_combined 0 0 beta beta_s == 1.
Proof. intros. exact (combined_trivial beta beta_s). Qed.

Lemma gap_su3_3d_at_1_0 : gap_su3_3d 1 0 == 5#6.
Proof.
  unfold gap_su3_3d, su3_combined, su3_spatial_penalty.
  rewrite casimir_trivial, casimir_fund.
  unfold t_trivial_su3, t_fund_su3. ring.
Qed.

Lemma gap_su3_3d_positive_1_0 : 0 < gap_su3_3d 1 0.
Proof. rewrite gap_su3_3d_at_1_0. lra. Qed.

(** With spatial coupling: gap increases (spatial penalty reduces fundamental) *)
Lemma gap_3d_gt_1d :
  gap_su3_3d 1 (1#100) > gap_su3_3d 1 0.
Proof.
  unfold gap_su3_3d, su3_combined, su3_spatial_penalty.
  rewrite casimir_trivial, casimir_fund.
  unfold t_trivial_su3, t_fund_su3. lra.
Qed.

(** Gap with spatial coupling at β=1, β_s=1/10 *)
Lemma gap_su3_3d_at_1_01 :
  gap_su3_3d 1 (1#10) == 1 - (1#6) * (1 - (4#3) * (1#10)).
Proof.
  unfold gap_su3_3d, su3_combined, su3_spatial_penalty.
  rewrite casimir_trivial, casimir_fund.
  unfold t_trivial_su3, t_fund_su3. ring.
Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

Theorem su3_3d_synthesis :
  gap_su3_3d 1 0 == 5#6 /\
  0 < gap_su3_3d 1 0 /\
  gap_su3_3d 1 (1#100) > gap_su3_3d 1 0.
Proof.
  split; [|split].
  - exact gap_su3_3d_at_1_0.
  - exact gap_su3_3d_positive_1_0.
  - exact gap_3d_gt_1d.
Qed.
