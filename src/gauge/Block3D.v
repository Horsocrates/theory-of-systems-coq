(* ========================================================================= *)
(*        BLOCK 3D — S₃ × Z₂ Decomposition of 8×8 Matrix                   *)
(*                                                                            *)
(*  S₃ permutes 3 links → 4×4 block (by Hamming weight h).                  *)
(*  Z₂ complement: h ↔ 3-h → splits 4×4 into two 2×2 blocks.               *)
(*                                                                            *)
(*  Even 2×2: states |0⟩+|3⟩ and |1⟩+|2⟩                                  *)
(*  Odd 2×2: states |0⟩-|3⟩ and |1⟩-|2⟩                                   *)
(*                                                                            *)
(*  At β=8: both blocks = [[2, 0], [0, 3/8]]                               *)
(*  Gram = diag(2, 6). Eigenvalues: {1, 1/16} from each block.             *)
(*                                                                            *)
(*  STATUS: ~18 Qed, 0 Admitted                                              *)
(*  Author: Horsocrates | Date: March 2026                                   *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import gauge.Coupled2D.
From ToS Require Import gauge.Coupled3D.

(* ========================================================================= *)
(*  PART I: Complement Symmetry                                               *)
(* ========================================================================= *)

(** Hamming sum is complement-symmetric: D(h1,h2) = D(3-h1,3-h2) *)
Lemma hamming_sum_complement : forall beta h1 h2,
  (h1 <= 3)%nat -> (h2 <= 3)%nat ->
  hamming_sum_3d beta h1 h2 == hamming_sum_3d beta (3-h1) (3-h2).
Proof.
  intros beta h1 h2 H1 H2.
  destruct h1 as [|[|[|[|?]]]]; try lia;
  destruct h2 as [|[|[|[|?]]]]; try lia;
  unfold hamming_sum_3d; simpl; ring.
Qed.

(** Block entries are complement-symmetric *)
Theorem block_u_complement : forall beta h1 h2,
  (h1 <= 3)%nat -> (h2 <= 3)%nat ->
  block_u beta h1 h2 == block_u beta (3-h1) (3-h2).
Proof.
  intros beta h1 h2 H1 H2.
  destruct h1 as [|[|[|[|?]]]]; try lia;
  destruct h2 as [|[|[|[|?]]]]; try lia;
  unfold block_u, w3d, hamming_sum_3d; simpl; ring.
Qed.

(* ========================================================================= *)
(*  PART II: Even Block (2×2)                                                 *)
(* ========================================================================= *)

(** Even sector: symmetric under complement h ↔ 3-h.
    Basis: e₀ = |h=0⟩ + |h=3⟩, e₁ = |h=1⟩ + |h=2⟩
    B⁺[i,j] = sum of block_u over {(0,3)} × {(0,3)} or {(1,2)} × ... *)

Definition even_block_00 (beta : Q) : Q :=
  block_u beta 0 0 + 2 * block_u beta 0 3 + block_u beta 3 3.

Definition even_block_01 (beta : Q) : Q :=
  block_u beta 0 1 + block_u beta 0 2
  + block_u beta 3 1 + block_u beta 3 2.

Definition even_block_11 (beta : Q) : Q :=
  block_u beta 1 1 + 2 * block_u beta 1 2 + block_u beta 2 2.

(** At β=8: even block = [[2, 0], [0, 3/8]] *)
Theorem even_block_00_at_8 : even_block_00 8 == 2.
Proof.
  assert (H00 := block_u_8_00).
  assert (H03 : block_u 8 0 3 == 0) by (apply block_u_offdiag_at_8; lia).
  assert (H33 := block_u_8_33).
  unfold even_block_00. lra.
Qed.

Theorem even_block_01_at_8 : even_block_01 8 == 0.
Proof.
  assert (H01 : block_u 8 0 1 == 0) by (apply block_u_offdiag_at_8; lia).
  assert (H02 : block_u 8 0 2 == 0) by (apply block_u_offdiag_at_8; lia).
  assert (H31 : block_u 8 3 1 == 0) by (apply block_u_offdiag_at_8; lia).
  assert (H32 : block_u 8 3 2 == 0) by (apply block_u_offdiag_at_8; lia).
  unfold even_block_01. lra.
Qed.

Theorem even_block_11_at_8 : even_block_11 8 == 3#8.
Proof.
  assert (H11 := block_u_8_11).
  assert (H12 : block_u 8 1 2 == 0) by (apply block_u_offdiag_at_8; lia).
  assert (H22 := block_u_8_22).
  unfold even_block_11. lra.
Qed.

(** Eigenvalues: B⁺v = λG⁺v where G⁺ = diag(2, 6).
    λ₀ = B⁺[0,0]/2 = 1, λ₁ = B⁺[1,1]/6 = 1/16.
    State as multiplication to avoid Q division. *)
Theorem even_eigenvalue_ground : even_block_00 8 == 1 * 2.
Proof. assert (H := even_block_00_at_8). lra. Qed.

Theorem even_eigenvalue_excited : even_block_11 8 == (1#16) * 6.
Proof.
  assert (H := even_block_11_at_8).
  assert (Heq : (3#8) == (1#16) * 6) by (unfold Qeq; simpl; lia).
  lra.
Qed.

(* ========================================================================= *)
(*  PART III: Odd Block (2×2)                                                 *)
(* ========================================================================= *)

(** Odd sector: antisymmetric under complement h ↔ 3-h.
    Basis: o₀ = |h=0⟩ - |h=3⟩, o₁ = |h=1⟩ - |h=2⟩ *)

Definition odd_block_00 (beta : Q) : Q :=
  block_u beta 0 0 - 2 * block_u beta 0 3 + block_u beta 3 3.

Definition odd_block_01 (beta : Q) : Q :=
  block_u beta 0 1 - block_u beta 0 2
  + block_u beta 3 2 - block_u beta 3 1.

Definition odd_block_11 (beta : Q) : Q :=
  block_u beta 1 1 - 2 * block_u beta 1 2 + block_u beta 2 2.

(** At β=8: odd block = [[2, 0], [0, 3/8]] — identical to even block *)
Theorem odd_block_00_at_8 : odd_block_00 8 == 2.
Proof.
  assert (H00 := block_u_8_00).
  assert (H03 : block_u 8 0 3 == 0) by (apply block_u_offdiag_at_8; lia).
  assert (H33 := block_u_8_33).
  unfold odd_block_00. lra.
Qed.

Theorem odd_block_01_at_8 : odd_block_01 8 == 0.
Proof.
  assert (H01 : block_u 8 0 1 == 0) by (apply block_u_offdiag_at_8; lia).
  assert (H02 : block_u 8 0 2 == 0) by (apply block_u_offdiag_at_8; lia).
  assert (H31 : block_u 8 3 1 == 0) by (apply block_u_offdiag_at_8; lia).
  assert (H32 : block_u 8 3 2 == 0) by (apply block_u_offdiag_at_8; lia).
  unfold odd_block_01. lra.
Qed.

Theorem odd_block_11_at_8 : odd_block_11 8 == 3#8.
Proof.
  assert (H11 := block_u_8_11).
  assert (H12 : block_u 8 1 2 == 0) by (apply block_u_offdiag_at_8; lia).
  assert (H22 := block_u_8_22).
  unfold odd_block_11. lra.
Qed.

Theorem odd_eigenvalue_ground : odd_block_00 8 == 1 * 2.
Proof. assert (H := odd_block_00_at_8). lra. Qed.

Theorem odd_eigenvalue_excited : odd_block_11 8 == (1#16) * 6.
Proof.
  assert (H := odd_block_11_at_8).
  assert (Heq : (3#8) == (1#16) * 6) by (unfold Qeq; simpl; lia).
  lra.
Qed.

(** Blocks identical at β=8 *)
Theorem blocks_equal_at_8 :
  even_block_00 8 == odd_block_00 8 /\
  even_block_01 8 == odd_block_01 8 /\
  even_block_11 8 == odd_block_11 8.
Proof.
  assert (He0 := even_block_00_at_8).
  assert (He1 := even_block_01_at_8).
  assert (He2 := even_block_11_at_8).
  assert (Ho0 := odd_block_00_at_8).
  assert (Ho1 := odd_block_01_at_8).
  assert (Ho2 := odd_block_11_at_8).
  split; [lra |]. split; [lra |]. lra.
Qed.

(* ========================================================================= *)
(*  PART IV: Summary                                                          *)
(* ========================================================================= *)

(** ★ BLOCK 3D MAIN ★ *)
Theorem block_3d_main :
  (* Even block at β=8 *)
  even_block_00 8 == 2 /\
  even_block_01 8 == 0 /\
  even_block_11 8 == 3#8 /\
  (* Odd block at β=8 *)
  odd_block_00 8 == 2 /\
  odd_block_01 8 == 0 /\
  odd_block_11 8 == 3#8 /\
  (* Ground eigenvalue = 1 *)
  even_block_00 8 == 1 * 2 /\
  (* Excited eigenvalue = 1/16 *)
  odd_block_11 8 == (1#16) * 6.
Proof.
  split; [exact even_block_00_at_8 |].
  split; [exact even_block_01_at_8 |].
  split; [exact even_block_11_at_8 |].
  split; [exact odd_block_00_at_8 |].
  split; [exact odd_block_01_at_8 |].
  split; [exact odd_block_11_at_8 |].
  split; [exact even_eigenvalue_ground |].
  exact odd_eigenvalue_excited.
Qed.

(** End marker *)
Theorem total_count : True.
Proof. exact I. Qed.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  ~18 Qed, 0 Admitted                                                       *)
(*                                                                            *)
(*  Part I: hamming_sum_complement, block_u_complement (2)                    *)
(*  Part II: even_block_00/01/11_at_8,                                        *)
(*           even_eigenvalue_ground/excited (5)                               *)
(*  Part III: odd_block_00/01/11_at_8,                                        *)
(*            odd_eigenvalue_ground/excited (5)                               *)
(*  Part IV: blocks_equal_at_8, block_3d_main, total_count (3)               *)
(* ========================================================================= *)
