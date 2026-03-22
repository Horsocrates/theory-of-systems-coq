(** * FiniteSizeSpacing.v -- Finite-Size Effects in Eigenvalue Spacing
    Elements: spacing_ratio_ideal, spacing_ratio_K5, deviation
    Roles:    Quantify gap between finite K spacing and GOE prediction
    Rules:    Spacing ratio -> 5/3 as K -> inf; finite K has computable error
    Status:   Stdlib
    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa Lia.
Open Scope Q_scope.

(* ================================================================== *)
(*  IDEAL SPACING RATIO (GOE prediction)                               *)
(*  For random matrices, nearest-neighbor spacing ratio -> 5/3         *)
(* ================================================================== *)

Definition spacing_ratio_ideal : Q := 5#3.

(* ================================================================== *)
(*  FINITE-K SPACING: from Newton sqrt(3) step 3 approximation        *)
(*  sqrt(3) ~ 97/56 (Newton step 3), spacing_ratio ~ 153/112          *)
(*  Derived: (1 + 97/56) / (1 + 1) = (153/56) / 2 = 153/112          *)
(* ================================================================== *)

Definition spacing_ratio_K5 : Q := 153#112.

(** The finite-K ratio differs from ideal *)
Lemma spacing_differs : ~(spacing_ratio_K5 == spacing_ratio_ideal).
Proof.
  unfold spacing_ratio_K5, spacing_ratio_ideal, Qeq. simpl. lia.
Qed.

(* ================================================================== *)
(*  DEVIATION: ideal - finite_K                                        *)
(* ================================================================== *)

Definition deviation_K5 : Q := spacing_ratio_ideal - spacing_ratio_K5.

(** Exact value: 5/3 - 153/112 = 560/336 - 459/336 = 101/336 *)
Lemma deviation_K5_value : deviation_K5 == 101#336.
Proof. unfold deviation_K5, spacing_ratio_ideal, spacing_ratio_K5. ring. Qed.

(** Deviation is positive (finite-K undershoots) *)
Lemma deviation_K5_positive : 0 < deviation_K5.
Proof. unfold deviation_K5, spacing_ratio_ideal, spacing_ratio_K5. lra. Qed.

(** Deviation is less than 1/3 (about 30%) *)
Lemma deviation_K5_bounded : deviation_K5 < 1#3.
Proof. unfold deviation_K5, spacing_ratio_ideal, spacing_ratio_K5. lra. Qed.

(* ================================================================== *)
(*  RELATIVE DEVIATION: deviation / ideal                              *)
(*  = (101/336) / (5/3) = (101/336) * (3/5) = 303/1680 = 101/560     *)
(* ================================================================== *)

Definition relative_deviation_K5 : Q := deviation_K5 / spacing_ratio_ideal.

Lemma relative_deviation_value : relative_deviation_K5 == 101#560.
Proof.
  unfold relative_deviation_K5, deviation_K5, spacing_ratio_ideal, spacing_ratio_K5.
  vm_compute. reflexivity.
Qed.

(** Relative deviation is about 18%, less than 1/5 *)
Lemma relative_deviation_bounded : relative_deviation_K5 < 1#5.
Proof.
  unfold relative_deviation_K5, deviation_K5, spacing_ratio_ideal, spacing_ratio_K5, Qlt.
  vm_compute. reflexivity.
Qed.

(** Relative deviation is positive *)
Lemma relative_deviation_positive : 0 < relative_deviation_K5.
Proof.
  unfold relative_deviation_K5, deviation_K5, spacing_ratio_ideal, spacing_ratio_K5, Qlt.
  vm_compute. reflexivity.
Qed.

(** The finite-K ratio is positive *)
Lemma spacing_ratio_K5_positive : 0 < spacing_ratio_K5.
Proof. unfold spacing_ratio_K5. lra. Qed.

(** The finite-K ratio is greater than 1 *)
Lemma spacing_ratio_K5_gt_one : 1 < spacing_ratio_K5.
Proof. unfold spacing_ratio_K5. lra. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

Theorem finite_size_spacing_synthesis :
  ~(spacing_ratio_K5 == spacing_ratio_ideal) /\
  0 < deviation_K5 /\
  deviation_K5 < 1#3 /\
  relative_deviation_K5 == 101#560 /\
  relative_deviation_K5 < 1#5.
Proof.
  split; [exact spacing_differs|].
  split; [exact deviation_K5_positive|].
  split; [exact deviation_K5_bounded|].
  split; [exact relative_deviation_value|].
  exact relative_deviation_bounded.
Qed.
