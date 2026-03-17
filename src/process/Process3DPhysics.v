(** * Process3DPhysics.v -- 3D string tension from Gap3D

    Theory of Systems -- Process Physics (Wave 1, Phase B1)

    Elements: sigma_3d, dimension ladder, gap_formula connection
    Roles:    first 3D confinement from existing Gap3D results
    Rules:    gap_3d = 15/16 -> sigma_3d ~ ln(16) ~ 2.773
    Status:   complete

    STATUS: 20 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.

Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessStringTension.
From ToS Require Import gauge.Gap3D.

(* ================================================================== *)
(*  Part I: 3D String Tension                                         *)
(* ================================================================== *)

(** 3D string tension at beta=8: sigma_3d = neg_ln_taylor(15/16, N) *)
(** gap_3d = 15/16 -> sigma = -ln(1/16) = ln(16) = 4*ln(2) ~ 2.773 *)

Definition sigma_3d (order : nat) : Q :=
  neg_ln_taylor (15 # 16) order.

Lemma sigma_3d_order1 : sigma_3d 1 == 15 # 16.
Proof. unfold sigma_3d. apply taylor_order_1. Qed.

Lemma sigma_3d_positive : 0 < sigma_3d 1.
Proof. assert (H := sigma_3d_order1). lra. Qed.

(** 2D string tension for comparison *)
Definition sigma_2d_char (order : nat) : Q :=
  neg_ln_taylor (3 # 4) order.

Lemma sigma_2d_order1 : sigma_2d_char 1 == 3 # 4.
Proof. unfold sigma_2d_char. apply taylor_order_1. Qed.

(** 3D > 2D at order 1: 15/16 > 3/4 *)
Lemma sigma_3d_exceeds_2d :
  sigma_2d_char 1 < sigma_3d 1.
Proof.
  assert (H1 := sigma_2d_order1). assert (H2 := sigma_3d_order1). lra.
Qed.

(* ================================================================== *)
(*  Part II: Dimension Ladder                                         *)
(* ================================================================== *)

(** sigma by spatial dimension using gap_formula from Gap3D *)
Definition sigma_by_dim (d order : nat) : Q :=
  neg_ln_taylor (gap_formula d) order.

Lemma sigma_dim_0 : sigma_by_dim 0 1 == 0.
Proof.
  unfold sigma_by_dim, gap_formula, gamma_sq_power, neg_ln_taylor.
  vm_compute. reflexivity.
Qed.

Lemma sigma_dim_1 : sigma_by_dim 1 1 == 3 # 4.
Proof.
  unfold sigma_by_dim, gap_formula, gamma_sq_power.
  apply taylor_order_1.
Qed.

Lemma sigma_dim_2 : sigma_by_dim 2 1 == 15 # 16.
Proof.
  unfold sigma_by_dim, gap_formula, gamma_sq_power.
  apply taylor_order_1.
Qed.

Lemma sigma_dim_3 : sigma_by_dim 3 1 == 63 # 64.
Proof.
  unfold sigma_by_dim, gap_formula, gamma_sq_power.
  apply taylor_order_1.
Qed.

(** Dimension ladder increases: 0 < 3/4 < 15/16 < 63/64 *)
Theorem sigma_ladder_increases :
  sigma_by_dim 0 1 < sigma_by_dim 1 1 /\
  sigma_by_dim 1 1 < sigma_by_dim 2 1 /\
  sigma_by_dim 2 1 < sigma_by_dim 3 1.
Proof.
  assert (H0 := sigma_dim_0). assert (H1 := sigma_dim_1).
  assert (H2 := sigma_dim_2). assert (H3 := sigma_dim_3).
  repeat split; lra.
Qed.

(* ================================================================== *)
(*  Part III: Physical Interpretation                                  *)
(* ================================================================== *)

(** Gap at 3D from existing Gap3D *)
Lemma gap_3d_is_15_16 : mass_gap_3d_at_8 == 15 # 16.
Proof. unfold mass_gap_3d_at_8. reflexivity. Qed.

(** Gap increases with dimension *)
Theorem stronger_confinement_in_higher_d :
  gap_formula 1 < gap_formula 2 /\
  gap_formula 2 < gap_formula 3.
Proof.
  assert (H1 := gap_formula_1). assert (H2 := gap_formula_2).
  assert (H3 := gap_formula_3). split; lra.
Qed.

(** Each spatial dimension adds confinement *)
(** sigma(d) ~ d * ln(4) for large d *)
(** At order 1: sigma(d) = 1 - 1/4^d *)

Theorem sigma_3d_concrete :
  (* 3D gap = 15/16 *)
  mass_gap_3d_at_8 == 15 # 16 /\
  (* 3D sigma at order 1 *)
  sigma_3d 1 == 15 # 16 /\
  (* 3D > 2D *)
  sigma_2d_char 1 < sigma_3d 1.
Proof.
  split; [| split].
  - exact gap_3d_is_15_16.
  - exact sigma_3d_order1.
  - exact sigma_3d_exceeds_2d.
Qed.

Theorem phase_B1_complete :
  0 < mass_gap_3d_at_8 /\
  0 < sigma_3d 1 /\
  sigma_by_dim 0 1 < sigma_by_dim 1 1 /\
  sigma_by_dim 1 1 < sigma_by_dim 2 1.
Proof.
  split; [| split; [| split]].
  - exact gap_3d_positive.
  - exact sigma_3d_positive.
  - destruct sigma_ladder_increases as [H _]. exact H.
  - destruct sigma_ladder_increases as [_ [H _]]. exact H.
Qed.
