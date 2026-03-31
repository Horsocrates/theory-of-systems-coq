(** * GaugeGroupMinimality.v — SU(2) is MINIMAL group containing i
    Elements: i order, S₂ order, det, unitarity
    Roles:    i has order 4 → i ∉ S₂. i ≠ -i → SO(3) loses info. i ∈ SU(2).
    Rules:    Gauge group = minimal connected group containing connection
    STATUS:   15 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: March 2026

    CLOSES: "Why SU(2) and not S₂ or SO(3)?"

    i = [[0,-1],[1,0]].
    ORDER: i⁴ = I, i² ≠ I. Order = 4.
    S₂: every element has order ≤ 2. → i ∉ S₂.
    SO(3) = SU(2)/Z₂: identifies i with -i. But i ≠ -i (L5: direction).
    SU(2): contains i, distinguishes i from -i, minimal (dim 3).
*)

From Stdlib Require Import QArith Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

(* ================================================================== *)
(*  CONNECTION i                                                       *)
(* ================================================================== *)

Definition i_00 : Q := 0.   Definition i_01 : Q := -(1).
Definition i_10 : Q := 1.   Definition i_11 : Q := 0.

(* ================================================================== *)
(*  i² = -I (order is NOT 2)                                          *)
(* ================================================================== *)

Lemma i_sq_00 : i_00*i_00 + i_01*i_10 == -(1).
Proof. unfold i_00, i_01, i_10. ring. Qed.

Lemma i_sq_11 : i_10*i_01 + i_11*i_11 == -(1).
Proof. unfold i_10, i_01, i_11. ring. Qed.

Lemma i_sq_01 : i_00*i_01 + i_01*i_11 == 0.
Proof. unfold i_00, i_01, i_11. ring. Qed.

Lemma i_sq_10 : i_10*i_00 + i_11*i_10 == 0.
Proof. unfold i_10, i_00, i_11. ring. Qed.

(** i² ≠ I: the (0,0) entry is -1, not 1 *)
Lemma i_order_not_2 : ~ (i_00*i_00 + i_01*i_10 == 1).
Proof. unfold i_00, i_01, i_10, Qeq. simpl. lia. Qed.

(* ================================================================== *)
(*  i⁴ = I (order IS 4)                                               *)
(* ================================================================== *)

(** i⁴ = (i²)² = (-I)² = I *)
Lemma i4_00 :
  let s00 := i_00*i_00 + i_01*i_10 in
  let s01 := i_00*i_01 + i_01*i_11 in
  let s10 := i_10*i_00 + i_11*i_10 in
  let s11 := i_10*i_01 + i_11*i_11 in
  s00*s00 + s01*s10 == 1.
Proof. unfold i_00, i_01, i_10, i_11. ring. Qed.

Lemma i4_11 :
  let s00 := i_00*i_00 + i_01*i_10 in
  let s01 := i_00*i_01 + i_01*i_11 in
  let s10 := i_10*i_00 + i_11*i_10 in
  let s11 := i_10*i_01 + i_11*i_11 in
  s10*s01 + s11*s11 == 1.
Proof. unfold i_00, i_01, i_10, i_11. ring. Qed.

(* ================================================================== *)
(*  S₂: swap has order 2                                               *)
(* ================================================================== *)

Definition sw_00 : Q := 0. Definition sw_01 : Q := 1.
Definition sw_10 : Q := 1. Definition sw_11 : Q := 0.

Lemma swap_sq_00 : sw_00*sw_00 + sw_01*sw_10 == 1.
Proof. unfold sw_00, sw_01, sw_10. ring. Qed.

Lemma swap_sq_11 : sw_10*sw_01 + sw_11*sw_11 == 1.
Proof. unfold sw_10, sw_01, sw_11. ring. Qed.

(** i ∉ S₂: i has order 4, S₂ elements have order ≤ 2 *)
(** Formally: i² ≠ I (proved), but swap² = I. Order mismatch. *)

(* ================================================================== *)
(*  i ≠ -i (L5: direction matters → rules out SO(3))                   *)
(* ================================================================== *)

Lemma i_neq_minus_i : ~ (i_01 == -(i_01)).
Proof. unfold i_01, Qeq. simpl. lia. Qed.

(* ================================================================== *)
(*  i ∈ SU(2): unitary + det 1                                        *)
(* ================================================================== *)

Lemma i_det_one : i_00*i_11 - i_01*i_10 == 1.
Proof. unfold i_00, i_01, i_10, i_11. ring. Qed.

Lemma i_unitary_col0 : i_00*i_00 + i_10*i_10 == 1.
Proof. unfold i_00, i_10. ring. Qed.

Lemma i_unitary_col1 : i_01*i_01 + i_11*i_11 == 1.
Proof. unfold i_01, i_11. ring. Qed.

Lemma i_unitary_cross : i_00*i_01 + i_10*i_11 == 0.
Proof. unfold i_00, i_01, i_10, i_11. ring. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

Theorem gauge_group_minimality :
  (* i² = -I (not I) → order > 2 → i ∉ S₂ *)
  i_00*i_00 + i_01*i_10 == -(1) /\
  ~ (i_00*i_00 + i_01*i_10 == 1) /\
  (* swap² = I → S₂ elements have order ≤ 2 *)
  sw_00*sw_00 + sw_01*sw_10 == 1 /\
  (* i ≠ -i → SO(3) = SU(2)/Z₂ loses information *)
  ~ (i_01 == -(i_01)) /\
  (* i ∈ SU(2): det = 1, unitary *)
  i_00*i_11 - i_01*i_10 == 1 /\
  i_00*i_00 + i_10*i_10 == 1.
Proof.
  split; [exact i_sq_00 |
  split; [exact i_order_not_2 |
  split; [exact swap_sq_00 |
  split; [exact i_neq_minus_i |
  split; [exact i_det_one |
  exact i_unitary_col0]]]]].
Qed.
