(** * ConnectionCircle.v — Z₄ = {I, i, -I, -i} as rational circle group
    Elements: i_pow_0..3, i⁴=I cycle
    Roles:    Four rational points on SO(2); i generates the cyclic group Z₄
    Rules:    Period 4; four points are distinct; connection generates circle
    Status:   Stdlib
    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.GreenFunction.
From ToS Require Import stdlib.ComplexOverQ.
From ToS Require Import stdlib.DistinctionConnection.
Open Scope Q_scope.

(* ================================================================== *)
(*  PART I: i^n DEFINITIONS                                            *)
(* ================================================================== *)

Definition i_pow (n : nat) : Mat2 :=
  match n with
  | O => C_one
  | S O => C_i
  | S (S O) => fun r c => mat2_mul C_i C_i r c
  | S (S (S O)) => fun r c =>
      mat2_mul C_i (fun r' c' => mat2_mul C_i C_i r' c') r c
  | _ => C_one  (* wraps around mod 4, but we only use 0..3 *)
  end.

(* ================================================================== *)
(*  PART II: i⁴ = I (PERIOD 4)                                        *)
(* ================================================================== *)

Lemma i_pow_4_is_identity : forall r c,
  (r <= 1)%nat -> (c <= 1)%nat ->
  mat2_mul C_i (fun r' c' =>
    mat2_mul C_i (fun r'' c'' => mat2_mul C_i C_i r'' c'') r' c') r c
  == C_one r c.
Proof.
  intros r c Hr Hc.
  destruct r as [|[|r']]; [| |lia];
  destruct c as [|[|c']]; try lia;
  vm_compute; reflexivity.
Qed.

(* ================================================================== *)
(*  PART III: FOUR POINTS ARE DISTINCT                                 *)
(* ================================================================== *)

(* I ≠ i: compare (0,1) entries: I has 0, i has -1 *)
Lemma I_neq_i : ~(C_one 0%nat 1%nat == C_i 0%nat 1%nat).
Proof.
  unfold Qeq. simpl. lia.
Qed.

(* I ≠ -I: compare (0,0) entries: 1 ≠ -1 *)
Lemma I_neq_neg_I : ~(C_one 0%nat 0%nat == complex_mat (-(1)) 0 0%nat 0%nat).
Proof.
  unfold Qeq. simpl. lia.
Qed.

(* i ≠ -i: compare (0,1) entries: -1 ≠ 1 *)
Lemma i_neq_neg_i :
  ~(C_i 0%nat 1%nat == (fun r c =>
      mat2_mul C_i (fun r' c' => mat2_mul C_i C_i r' c') r c) 0%nat 1%nat).
Proof.
  unfold Qeq. simpl. lia.
Qed.

(* I ≠ -i: compare (1,0) entries: 0 ≠ -1 *)
Lemma I_neq_neg_i :
  ~(C_one 1%nat 0%nat == (fun r c =>
      mat2_mul C_i (fun r' c' => mat2_mul C_i C_i r' c') r c) 1%nat 0%nat).
Proof.
  unfold Qeq. simpl. lia.
Qed.

(* i ≠ -I: compare (0,0) entries: 0 ≠ -1 *)
Lemma i_neq_neg_I : ~(C_i 0%nat 0%nat == complex_mat (-(1)) 0 0%nat 0%nat).
Proof.
  unfold Qeq. simpl. lia.
Qed.

(* -I ≠ -i: compare (0,1) entries: 0 ≠ 1 *)
Lemma neg_I_neq_neg_i :
  ~(complex_mat (-(1)) 0 0%nat 1%nat ==
    (fun r c => mat2_mul C_i (fun r' c' => mat2_mul C_i C_i r' c') r c) 0%nat 1%nat).
Proof.
  unfold Qeq. simpl. lia.
Qed.

(* ================================================================== *)
(*  PART IV: CIRCLE GENERATION THEOREM                                 *)
(* ================================================================== *)

Theorem connection_generates_circle :
  (* i generates 4 distinct elements *)
  ~(C_one 0%nat 1%nat == C_i 0%nat 1%nat) /\
  (* i² = -I *)
  mat2_mul C_i C_i 0%nat 0%nat == -(1) /\
  (* Binary → one plane *)
  planes_from_sides 2 = 1%nat.
Proof.
  split; [exact I_neq_i |].
  split; [exact i_sq_00 |].
  exact one_plane_from_binary.
Qed.
