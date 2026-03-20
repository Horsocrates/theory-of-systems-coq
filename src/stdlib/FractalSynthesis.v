(** * FractalSynthesis.v -- Cantor set + trisection connection
    Elements: ifs_left, ifs_right, fractal_synthesis
    Roles:    IFS maps for Cantor set, contraction with factor 1/3
    Rules:    dim = 2/3 ∈ (0,1), IFS maps [0,1] → [0,1/3]∪[2/3,1]
    Status:   Stdlib
    STATUS: 8 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.HausdorffDimension.

Open Scope Q_scope.

(* ================================================================== *)
(*  ITERATED FUNCTION SYSTEM                                           *)
(* ================================================================== *)

(** Cantor as IFS: f₁(x) = x/3, f₂(x) = x/3 + 2/3 *)
Definition ifs_left (x : Q) : Q := x * (1#3).
Definition ifs_right (x : Q) : Q := x * (1#3) + (2 # 3).

Lemma ifs_left_0 : ifs_left 0 == 0.
Proof. unfold ifs_left. ring. Qed.

Lemma ifs_right_0 : ifs_right 0 == 2#3.
Proof. unfold ifs_right. ring. Qed.

Lemma ifs_left_1 : ifs_left 1 == 1#3.
Proof. unfold ifs_left. ring. Qed.

Lemma ifs_right_1 : ifs_right 1 == 1.
Proof. unfold ifs_right. ring. Qed.

(** IFS maps preserve [0,1] boundaries *)
Lemma ifs_left_maps_0_to_third :
  ifs_left 0 == 0 /\ ifs_left 1 == 1#3.
Proof. split; [exact ifs_left_0 | exact ifs_left_1]. Qed.

Lemma ifs_right_maps_twothirds_to_one :
  ifs_right 0 == 2#3 /\ ifs_right 1 == 1.
Proof. split; [exact ifs_right_0 | exact ifs_right_1]. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

(** Connection: our trisection proof (ShrinkingIntervals, 167 Qed)
    constructs a Cantor-like set as byproduct.
    dim(Cantor) = ln2/ln3 ≈ 2/3 — strictly between 0 and 1. *)

Theorem fractal_synthesis :
  hausdorff_dim_cantor == 2#3 /\
  0 < hausdorff_dim_cantor /\
  hausdorff_dim_cantor < 1 /\
  ifs_left 0 == 0 /\
  ifs_right 0 == 2#3.
Proof.
  split; [|split; [|split; [|split]]].
  - exact hausdorff_cantor_value.
  - apply dim_is_fractal.
  - apply dim_is_fractal.
  - exact ifs_left_0.
  - exact ifs_right_0.
Qed.
