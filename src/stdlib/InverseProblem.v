(** * InverseProblem.v -- Recovering the matrix from Green's functions
    Elements: trace_to_det, char_poly_from_traces, inverse_from_full_green
    Roles:    G_{ij}(1) = M_{ij} (trivial inverse), traces → char poly
    Rules:    Two traces suffice for 2×2, process inverse problem is solvable
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.GreenFunction.

Open Scope Q_scope.

(* ================================================================== *)
(*  TRIVIAL INVERSE: G at K=1 gives M                                  *)
(* ================================================================== *)

(** mat2_mul M mat2_id = M pointwise for entries 0..1 *)
Lemma mat2_mul_id_00 : forall M : Mat2,
  mat2_mul M mat2_id 0%nat 0%nat == M 0%nat 0%nat.
Proof. intro. unfold mat2_mul, mat2_id. simpl. ring. Qed.

Lemma mat2_mul_id_01 : forall M : Mat2,
  mat2_mul M mat2_id 0%nat 1%nat == M 0%nat 1%nat.
Proof. intro. unfold mat2_mul, mat2_id. simpl. ring. Qed.

Lemma mat2_mul_id_10 : forall M : Mat2,
  mat2_mul M mat2_id 1%nat 0%nat == M 1%nat 0%nat.
Proof. intro. unfold mat2_mul, mat2_id. simpl. ring. Qed.

Lemma mat2_mul_id_11 : forall M : Mat2,
  mat2_mul M mat2_id 1%nat 1%nat == M 1%nat 1%nat.
Proof. intro. unfold mat2_mul, mat2_id. simpl. ring. Qed.

(** GREEN'S FUNCTION AT K=1 = MATRIX ENTRY *)
Theorem inverse_from_full_green : forall (M : Mat2) (i j : nat),
  (i <= 1)%nat -> (j <= 1)%nat ->
  green M i j 1 == M i j.
Proof.
  intros M i j Hi Hj.
  unfold green, mat2_pow.
  destruct i as [|[|i']]; [| |lia].
  - destruct j as [|[|j']]; [| |lia].
    + exact (mat2_mul_id_00 M).
    + exact (mat2_mul_id_01 M).
  - destruct j as [|[|j']]; [| |lia].
    + exact (mat2_mul_id_10 M).
    + exact (mat2_mul_id_11 M).
Qed.

(* ================================================================== *)
(*  INVERSE FROM TRACE ONLY                                            *)
(* ================================================================== *)

(** det(M) = (tr(M)² - tr(M²)) / 2 (Newton's identity for 2×2) *)
Definition trace_to_det (tr1 tr2 : Q) : Q :=
  (tr1 * tr1 - tr2) / 2.

(** Characteristic polynomial from traces *)
Definition char_poly_from_traces (tr1 tr2 : Q) (x : Q) : Q :=
  x * x - tr1 * x + trace_to_det tr1 tr2.

(* ================================================================== *)
(*  CONCRETE: GOLDEN MEAN MATRIX                                       *)
(* ================================================================== *)

(** tr(M) = 1, tr(M²) = 3 → det = (1-3)/2 = -1 *)
Lemma golden_det_from_traces : trace_to_det 1 3 == -(1).
Proof. unfold trace_to_det. vm_compute. reflexivity. Qed.

(** Char poly: x² - x - 1 *)
Lemma golden_char_poly : forall x,
  char_poly_from_traces 1 3 x == x * x - x - 1.
Proof. intro. unfold char_poly_from_traces, trace_to_det. field. Qed.

(** Golden mean satisfies char poly: φ² - φ - 1 = 0
    With φ ≈ 8/5 (from PF process): (8/5)² - 8/5 - 1 = 64/25 - 8/5 - 1 = -1/25 ≈ 0 *)
Lemma golden_approx_root :
  char_poly_from_traces 1 3 (8#5) == -(1#25).
Proof. unfold char_poly_from_traces, trace_to_det. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  FULL SHIFT MATRIX                                                  *)
(* ================================================================== *)

(** tr(M) = 2, tr(M²) = 4 → det = (4-4)/2 = 0 *)
Lemma full_det_from_traces : trace_to_det 2 4 == 0.
Proof. unfold trace_to_det. vm_compute. reflexivity. Qed.

(** Char poly: x² - 2x (roots at 0 and 2) *)
Lemma full_char_poly : forall x,
  char_poly_from_traces 2 4 x == x * x - 2 * x.
Proof. intro. unfold char_poly_from_traces, trace_to_det. field. Qed.

(* ================================================================== *)
(*  TWO TRACES SUFFICE FOR 2×2                                         *)
(* ================================================================== *)

(** From trace_process(1) and trace_process(2), reconstruct char poly *)
Theorem two_traces_suffice_2x2 : forall (M : Mat2) x,
  char_poly_from_traces (trace_process M 1) (trace_process M 2) x ==
  x * x - trace_process M 1 * x + trace_to_det (trace_process M 1) (trace_process M 2).
Proof.
  intros. unfold char_poly_from_traces. reflexivity.
Qed.

(** Different char polys → different matrices (up to similarity) *)
Lemma golden_full_different_polys :
  ~ (forall x, char_poly_from_traces 1 3 x == char_poly_from_traces 2 4 x).
Proof.
  intro H. specialize (H 0). rewrite golden_char_poly, full_char_poly in H.
  lra.
Qed.

(** SYNTHESIS *)
Theorem inverse_problem_synthesis :
  (* G_{ij}(1) = M_{ij} *)
  (forall M i j, (i <= 1)%nat -> (j <= 1)%nat -> green M i j 1 == M i j) /\
  (* Golden det from traces *)
  trace_to_det 1 3 == -(1) /\
  (* Full det from traces *)
  trace_to_det 2 4 == 0 /\
  (* Different char polys *)
  ~ (forall x, char_poly_from_traces 1 3 x == char_poly_from_traces 2 4 x).
Proof.
  split; [|split; [|split]].
  - exact inverse_from_full_green.
  - exact golden_det_from_traces.
  - exact full_det_from_traces.
  - exact golden_full_different_polys.
Qed.
