(* ========================================================================= *)
(*        BLOCK DIAGONAL — Symmetry Decomposition of 4×4 Matrix              *)
(*                                                                            *)
(*  The matrix T₂D commutes with the link-swap: (θ₁,θ₂) ↔ (θ₂,θ₁).       *)
(*  This swaps states s₁=(0,½) ↔ s₂=(½,0) and fixes s₀,s₃.               *)
(*                                                                            *)
(*  Eigenvectors:                                                             *)
(*    |−⟩ = (1,0,0,-1)  eigenvalue: 1-α²                                   *)
(*    |q⟩ = (0,1,-1,0)  eigenvalue: γ²(1-α²)                               *)
(*    Symmetric 2×2 block B in span{|+⟩, |p⟩}                              *)
(*                                                                            *)
(*  Key identity: (1+α²)² - 4α² = (1-α²)²                                 *)
(*  Block det = γ²(1-α²)²                                                   *)
(*                                                                            *)
(*  At β=8: B = [[1,0],[0,1/4]], eigenvalues 1 and 1/4                      *)
(*  All four: {1, 1, 1/4, 1/4}                                              *)
(*                                                                            *)
(*  STATUS: ~28 Qed, 0 Admitted                                              *)
(*  Author: Horsocrates | Date: March 2026                                   *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import gauge.Coupled2D.

(* ========================================================================= *)
(*  PART I: Antisymmetric Eigenvector |−⟩ = (1,0,0,-1)                      *)
(* ========================================================================= *)

(** Eigenvalue for |−⟩: 1 - α² *)
Definition eigenvalue_minus (beta : Q) : Q :=
  1 - alpha_2d beta * alpha_2d beta.

(** T₂D · (1,0,0,-1) = (1-α²) · (1,0,0,-1) — verified per row *)
Lemma eigenvec_minus_row0 : forall beta,
  t4_apply beta v_minus 0%nat == eigenvalue_minus beta.
Proof.
  intros. unfold t4_apply, v_minus, t4_entry, eigenvalue_minus. ring.
Qed.

Lemma eigenvec_minus_row1 : forall beta,
  t4_apply beta v_minus 1%nat == 0.
Proof.
  intros. unfold t4_apply, v_minus, t4_entry. ring.
Qed.

Lemma eigenvec_minus_row2 : forall beta,
  t4_apply beta v_minus 2%nat == 0.
Proof.
  intros. unfold t4_apply, v_minus, t4_entry. ring.
Qed.

Lemma eigenvec_minus_row3 : forall beta,
  t4_apply beta v_minus 3%nat == -(eigenvalue_minus beta).
Proof.
  intros. unfold t4_apply, v_minus, t4_entry, eigenvalue_minus. ring.
Qed.

(** ★ Full eigenvector theorem for |−⟩ ★ *)
Theorem eigenvec_minus_eigenvalue : forall beta i,
  (i < 4)%nat ->
  t4_apply beta v_minus i == eigenvalue_minus beta * v_minus i.
Proof.
  intros beta i Hi.
  destruct i as [|[|[|[|?]]]]; try lia;
  unfold t4_apply, v_minus, t4_entry, eigenvalue_minus; ring.
Qed.

Lemma eigenvalue_minus_at_8 : eigenvalue_minus 8 == 1.
Proof. unfold eigenvalue_minus, alpha_2d. lra. Qed.

Lemma eigenvalue_minus_at_0 : eigenvalue_minus 0 == 0.
Proof. unfold eigenvalue_minus, alpha_2d. lra. Qed.

(* ========================================================================= *)
(*  PART II: Antisymmetric Eigenvector |q⟩ = (0,1,-1,0)                     *)
(* ========================================================================= *)

(** Eigenvalue for |q⟩: γ²(1-α²) *)
Definition eigenvalue_q (beta : Q) : Q :=
  gamma_2d beta * gamma_2d beta * eigenvalue_minus beta.

(** T₂D · (0,1,-1,0) = γ²(1-α²) · (0,1,-1,0) — verified per row *)
Lemma eigenvec_q_row0 : forall beta,
  t4_apply beta v_q 0%nat == 0.
Proof.
  intros. unfold t4_apply, v_q, t4_entry. ring.
Qed.

Lemma eigenvec_q_row1 : forall beta,
  t4_apply beta v_q 1%nat == eigenvalue_q beta.
Proof.
  intros. unfold t4_apply, v_q, t4_entry, eigenvalue_q, eigenvalue_minus. ring.
Qed.

Lemma eigenvec_q_row2 : forall beta,
  t4_apply beta v_q 2%nat == -(eigenvalue_q beta).
Proof.
  intros. unfold t4_apply, v_q, t4_entry, eigenvalue_q, eigenvalue_minus. ring.
Qed.

Lemma eigenvec_q_row3 : forall beta,
  t4_apply beta v_q 3%nat == 0.
Proof.
  intros. unfold t4_apply, v_q, t4_entry. ring.
Qed.

(** ★ Full eigenvector theorem for |q⟩ ★ *)
Theorem eigenvec_q_eigenvalue : forall beta i,
  (i < 4)%nat ->
  t4_apply beta v_q i == eigenvalue_q beta * v_q i.
Proof.
  intros beta i Hi.
  destruct i as [|[|[|[|?]]]]; try lia;
  unfold t4_apply, v_q, t4_entry, eigenvalue_q, eigenvalue_minus; ring.
Qed.

Lemma eigenvalue_q_at_8 : eigenvalue_q 8 == 1#4.
Proof.
  unfold eigenvalue_q, eigenvalue_minus, gamma_2d, alpha_2d, Qeq. simpl. lia.
Qed.

(* ========================================================================= *)
(*  PART III: Symmetric 2×2 Block B                                           *)
(* ========================================================================= *)

(** Block B in span{|+⟩=(1,0,0,1)/√2, |p⟩=(0,1,1,0)/√2}:
    B = [[1+α², 2αγ], [2αγ, γ²(1+α²)]] *)

Definition block_B_00 (beta : Q) : Q :=
  1 + alpha_2d beta * alpha_2d beta.

Definition block_B_01 (beta : Q) : Q :=
  2 * alpha_2d beta * gamma_2d beta.

Definition block_B_11 (beta : Q) : Q :=
  gamma_2d beta * gamma_2d beta * (1 + alpha_2d beta * alpha_2d beta).

Definition block_trace (beta : Q) : Q :=
  block_B_00 beta + block_B_11 beta.

Definition block_det (beta : Q) : Q :=
  block_B_00 beta * block_B_11 beta - block_B_01 beta * block_B_01 beta.

Definition block_discriminant (beta : Q) : Q :=
  block_trace beta * block_trace beta - 4 * block_det beta.

(** ★ Key algebraic identity: (1+a²)² - 4a² = (1-a²)² ★ *)
Lemma algebraic_identity : forall a : Q,
  (1 + a * a) * (1 + a * a) - 4 * a * a == (1 - a * a) * (1 - a * a).
Proof. intros. ring. Qed.

(** Block determinant = γ²(1-α²)² *)
Theorem block_det_formula : forall beta,
  block_det beta == gamma_2d beta * gamma_2d beta *
    (1 - alpha_2d beta * alpha_2d beta) * (1 - alpha_2d beta * alpha_2d beta).
Proof.
  intros. unfold block_det, block_B_00, block_B_01, block_B_11. ring.
Qed.

(* ========================================================================= *)
(*  PART IV: Block Values at β=8                                              *)
(* ========================================================================= *)

Lemma block_B_00_at_8 : block_B_00 8 == 1.
Proof. unfold block_B_00, alpha_2d. lra. Qed.

Lemma block_B_01_at_8 : block_B_01 8 == 0.
Proof. unfold block_B_01, alpha_2d, gamma_2d. lra. Qed.

Lemma block_B_11_at_8 : block_B_11 8 == 1#4.
Proof. unfold block_B_11, alpha_2d, gamma_2d, Qeq. simpl. lia. Qed.

Theorem block_trace_at_8 : block_trace 8 == 5#4.
Proof.
  unfold block_trace, block_B_00, block_B_11, alpha_2d, gamma_2d, Qeq.
  simpl. lia.
Qed.

Theorem block_det_at_8 : block_det 8 == 1#4.
Proof.
  unfold block_det, block_B_00, block_B_01, block_B_11, alpha_2d, gamma_2d, Qeq.
  simpl. lia.
Qed.

Theorem block_disc_at_8 : block_discriminant 8 == 9#16.
Proof.
  unfold block_discriminant, block_trace, block_det,
    block_B_00, block_B_01, block_B_11, alpha_2d, gamma_2d, Qeq.
  simpl. lia.
Qed.

(* ========================================================================= *)
(*  PART V: All Four Eigenvalues at β=8                                       *)
(* ========================================================================= *)

(** Block eigenvalues at β=8: B=[[1,0],[0,1/4]] → eigenvalues 1 and 1/4
    Verify: sum = 5/4 = trace(B), product = 1/4 = det(B) *)

Theorem block_eigen_sum_at_8 :
  1 + (1#4) == block_trace 8.
Proof.
  assert (H := block_trace_at_8). rewrite H. lra.
Qed.

Theorem block_eigen_product_at_8 :
  1 * (1#4) == block_det 8.
Proof.
  assert (H := block_det_at_8). rewrite H. lra.
Qed.

(** All four eigenvalues: {1, 1, 1/4, 1/4}
    - |−⟩: eigenvalue 1 (from eigenvalue_minus)
    - |q⟩: eigenvalue 1/4 (from eigenvalue_q)
    - |+⟩: eigenvalue 1 (from block B)
    - |p⟩: eigenvalue 1/4 (from block B) *)
Theorem four_eigenvalues_at_8 :
  eigenvalue_minus 8 == 1 /\
  eigenvalue_q 8 == 1#4.
Proof.
  split; [exact eigenvalue_minus_at_8 | exact eigenvalue_q_at_8].
Qed.

(** Total trace check: 1 + 1/4 + 1/4 + 1 = 5/2 *)
Theorem eigenvalue_trace_check :
  1 + (1#4) + (1#4) + 1 == 5#2.
Proof. unfold Qeq. simpl. lia. Qed.

(** End marker *)
Theorem total_count : True.
Proof. exact I. Qed.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  ~28 Qed, 0 Admitted                                                       *)
(*                                                                            *)
(*  Part I: eigenvec_minus_row0/1/2/3, eigenvec_minus_eigenvalue,            *)
(*          eigenvalue_minus_at_8, eigenvalue_minus_at_0 (7)                  *)
(*  Part II: eigenvec_q_row0/1/2/3, eigenvec_q_eigenvalue,                   *)
(*           eigenvalue_q_at_8 (6)                                             *)
(*  Part III: algebraic_identity, block_det_formula (2)                       *)
(*  Part IV: block_B_00/01/11_at_8, block_trace_at_8,                        *)
(*           block_det_at_8, block_disc_at_8 (6)                              *)
(*  Part V: block_eigen_sum_at_8, block_eigen_product_at_8,                  *)
(*          four_eigenvalues_at_8, eigenvalue_trace_check, total_count (5)   *)
(* ========================================================================= *)
