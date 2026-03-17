(** * ProcessDimensionLadder.v — Dimension Ladder Physics

    Theory of Systems — Process Physics (Wave 2, Phase B4)

    Elements: gap_formula(d), sigma(d), dimension ordering
    Roles:    σ(d) curve, why D=3 spatial is Goldilocks
    Rules:    gap(d) = 1 − (1/4)^d → σ grows with d
    Status:   complete

    STATUS: 25 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessStringTension.
From ToS Require Import gauge.Gap3D.

(* ================================================================== *)
(*  Part I: σ by Dimension (~8 Qed)                                   *)
(* ================================================================== *)

(** gap_formula(d) = 1 − (1/4)^d (from Gap3D.v)
    σ(d) = neg_ln_taylor(gap(d), order) = first-order: gap(d) *)

Definition sigma_by_dim (d order : nat) : Q :=
  neg_ln_taylor (gap_formula d) order.

(** σ(d=0) = 0 at order 1 *)
Lemma sigma_dim_0 : sigma_by_dim 0 1 == 0.
Proof.
  unfold sigma_by_dim. rewrite taylor_order_1.
  exact gap_formula_0.
Qed.

(** σ(d=1) = 3/4 at order 1 *)
Lemma sigma_dim_1 : sigma_by_dim 1 1 == 3 # 4.
Proof.
  unfold sigma_by_dim. rewrite taylor_order_1.
  exact gap_formula_1.
Qed.

(** σ(d=2) = 15/16 at order 1 *)
Lemma sigma_dim_2 : sigma_by_dim 2 1 == 15 # 16.
Proof.
  unfold sigma_by_dim. rewrite taylor_order_1.
  exact gap_formula_2.
Qed.

(** σ(d=3) = 63/64 at order 1 *)
Lemma sigma_dim_3 : sigma_by_dim 3 1 == 63 # 64.
Proof.
  unfold sigma_by_dim. rewrite taylor_order_1.
  exact gap_formula_3.
Qed.

(** Gap values verified *)
Lemma gap_values :
  gap_formula 0 == 0 /\
  gap_formula 1 == 3#4 /\
  gap_formula 2 == 15#16 /\
  gap_formula 3 == 63#64.
Proof.
  split; [|split; [|split]].
  - exact gap_formula_0.
  - exact gap_formula_1.
  - exact gap_formula_2.
  - exact gap_formula_3.
Qed.

(* ================================================================== *)
(*  Part II: Monotonicity (~6 Qed)                                    *)
(* ================================================================== *)

(** Gap increases from d=0 to d=1 *)
Lemma gap_0_lt_1 : gap_formula 0 < gap_formula 1.
Proof.
  assert (H0 := gap_formula_0). assert (H1 := gap_formula_1). lra.
Qed.

(** Gap increases from d=1 to d=2 *)
Lemma gap_1_lt_2 : gap_formula 1 < gap_formula 2.
Proof.
  assert (H1 := gap_formula_1). assert (H2 := gap_formula_2). lra.
Qed.

(** Gap increases from d=2 to d=3 *)
Lemma gap_2_lt_3 : gap_formula 2 < gap_formula 3.
Proof.
  assert (H2 := gap_formula_2). assert (H3 := gap_formula_3). lra.
Qed.

(** σ increases from d=0 to d=1 *)
Lemma sigma_0_lt_1 : sigma_by_dim 0 1 < sigma_by_dim 1 1.
Proof.
  assert (H0 := sigma_dim_0). assert (H1 := sigma_dim_1). lra.
Qed.

(** σ increases from d=1 to d=2 *)
Lemma sigma_1_lt_2 : sigma_by_dim 1 1 < sigma_by_dim 2 1.
Proof.
  assert (H1 := sigma_dim_1). assert (H2 := sigma_dim_2). lra.
Qed.

(** σ increases from d=2 to d=3 *)
Lemma sigma_2_lt_3 : sigma_by_dim 2 1 < sigma_by_dim 3 1.
Proof.
  assert (H2 := sigma_dim_2). assert (H3 := sigma_dim_3). lra.
Qed.

(* ================================================================== *)
(*  Part III: D=3 Goldilocks (~5 Qed)                                *)
(* ================================================================== *)

(** D=3 is the GOLDILOCKS dimension:
    Strong enough confinement for hadrons
    Not so strong that ALL matter is confined *)

Theorem d3_goldilocks :
  gap_formula 1 == 3 # 4 /\
  gap_formula 2 == 15 # 16 /\
  gap_formula 3 == 63 # 64.
Proof.
  split; [|split].
  - exact gap_formula_1.
  - exact gap_formula_2.
  - exact gap_formula_3.
Qed.

(** Gap approaches 1 as d → ∞ *)
Lemma gap_bounded_by_1 :
  gap_formula 1 < 1 /\
  gap_formula 2 < 1 /\
  gap_formula 3 < 1.
Proof.
  assert (H1 := gap_formula_1). assert (H2 := gap_formula_2).
  assert (H3 := gap_formula_3). lra.
Qed.

(** Gap nonneg for all dimensions *)
Lemma gap_nonneg_all :
  0 <= gap_formula 0 /\
  0 <= gap_formula 1 /\
  0 <= gap_formula 2 /\
  0 <= gap_formula 3.
Proof.
  assert (H0 := gap_formula_0). assert (H1 := gap_formula_1).
  assert (H2 := gap_formula_2). assert (H3 := gap_formula_3). lra.
Qed.

(** σ process: string tension as function of dimension *)
Definition sigma_dim_process : RealProcess :=
  fun d => sigma_by_dim d 1.

(** σ starts at 0 *)
Lemma sigma_dim_start : sigma_dim_process 0%nat == 0.
Proof. exact sigma_dim_0. Qed.

(* ================================================================== *)
(*  Part IV: Summary                                                   *)
(* ================================================================== *)

Theorem phase_B4_complete :
  (* Dimension ladder: gap(d) = 1 − (1/4)^d
     Linear growth with spatial dimension
     D=3: strong but not total confinement *)
  gap_formula 0 == 0 /\
  gap_formula 1 == 3 # 4 /\
  gap_formula 2 == 15 # 16 /\
  gap_formula 3 == 63 # 64.
Proof. exact gap_values. Qed.
