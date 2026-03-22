(** * DistinctionConnection.v — i = connection between two sides of distinction
    Elements: distinction_sides, planes_from_sides, i_pow cycle
    Roles:    Two sides → one plane → one rotation; i connects A and ¬A
    Rules:    Binary distinction yields exactly one plane of rotation (C(2,2)=1)
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.GreenFunction.
From ToS Require Import stdlib.ComplexOverQ.
From ToS Require Import foundation.IndivisibleDistinction.
Open Scope Q_scope.

(* ================================================================== *)
(*  PART I: BINARY DISTINCTION → ONE PLANE                            *)
(* ================================================================== *)

Definition distinction_sides : nat := 2.

(* C(n,2) = n*(n-1)/2 = number of planes from n axes *)
Definition planes_from_sides (n : nat) : nat := n * (n - 1) / 2.

Lemma one_plane_from_binary : planes_from_sides 2 = 1%nat.
Proof. reflexivity. Qed.

Lemma three_planes_from_ternary : planes_from_sides 3 = 3%nat.
Proof. reflexivity. Qed.

Lemma zero_planes_from_unary : planes_from_sides 1 = 0%nat.
Proof. reflexivity. Qed.

Lemma connection_not_division : distinction_sides = 2%nat.
Proof. reflexivity. Qed.

(* ================================================================== *)
(*  PART II: i SENDS A-AXIS TO ¬A-AXIS                                *)
(* ================================================================== *)

(* i·(1,0): imaginary part = C_i 1 0 * 1 + C_i 1 1 * 0 = 1 *)
Lemma i_sends_A_to_notA :
  C_i 1%nat 0%nat * 1 + C_i 1%nat 1%nat * 0 == 1.
Proof. vm_compute. reflexivity. Qed.

(* i·(0,1): real part = C_i 0 0 * 0 + C_i 0 1 * 1 = -1 *)
Lemma i_sends_notA_to_negA :
  C_i 0%nat 0%nat * 0 + C_i 0%nat 1%nat * 1 == -(1).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  PART III: i² = -I (two connections = negation)                     *)
(* ================================================================== *)

Lemma i_squared_is_negation : forall r c,
  (r <= 1)%nat -> (c <= 1)%nat ->
  mat2_mul C_i C_i r c == complex_mat (-(1)) 0 r c.
Proof.
  intros r c Hr Hc.
  destruct r as [|[|r']]; [| |lia];
  destruct c as [|[|c']]; try lia;
  vm_compute; reflexivity.
Qed.

(* ================================================================== *)
(*  PART IV: PHASE ROTATION PRESERVES NORM (concrete instances)        *)
(* ================================================================== *)

(* |i · (1+0i)|² = |0+1i|² = 1 = |1+0i|² *)
Lemma phase_preserves_norm_1 :
  complex_mod_sq 0 1 == complex_mod_sq 1 0.
Proof. unfold complex_mod_sq. vm_compute. reflexivity. Qed.

(* |i · (3+4i)|² = |-4+3i|² = 25 = |3+4i|² *)
Lemma phase_preserves_norm_2 :
  complex_mod_sq (-(4)) 3 == complex_mod_sq 3 4.
Proof. unfold complex_mod_sq. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  PART V: i POWER CYCLE (period 4)                                   *)
(* ================================================================== *)

(* i¹ = i: diagonal entry *)
Lemma i_pow_1_diag : C_i 0%nat 0%nat == 0.
Proof. vm_compute. reflexivity. Qed.

(* i² = -I: already proved universally *)

(* i³ = -i: (0,0) entry *)
Lemma i_pow_3_00 :
  mat2_mul C_i (fun r c => mat2_mul C_i C_i r c) 0%nat 0%nat == 0.
Proof. vm_compute. reflexivity. Qed.

(* i³ = -i: (0,1) entry = 1 (which is -(-(1)) = 1, vs C_i 0 1 = -1) *)
Lemma i_pow_3_01 :
  mat2_mul C_i (fun r c => mat2_mul C_i C_i r c) 0%nat 1%nat == 1.
Proof. vm_compute. reflexivity. Qed.

(* i⁴ = I: (0,0) entry *)
Lemma i_pow_4_00 :
  mat2_mul C_i (fun r c =>
    mat2_mul C_i (fun r' c' => mat2_mul C_i C_i r' c') r c) 0%nat 0%nat == 1.
Proof. vm_compute. reflexivity. Qed.

(* i⁴ = I: (0,1) entry *)
Lemma i_pow_4_01 :
  mat2_mul C_i (fun r c =>
    mat2_mul C_i (fun r' c' => mat2_mul C_i C_i r' c') r c) 0%nat 1%nat == 0.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

Theorem distinction_connection_synthesis :
  planes_from_sides 2 = 1%nat /\
  C_i 1%nat 0%nat * 1 + C_i 1%nat 1%nat * 0 == 1 /\
  mat2_mul C_i C_i 0%nat 0%nat == -(1) /\
  complex_mod_sq 0 1 == complex_mod_sq 1 0.
Proof.
  split; [exact one_plane_from_binary |].
  split; [exact i_sends_A_to_notA |].
  split; [exact i_sq_00 |].
  exact phase_preserves_norm_1.
Qed.
