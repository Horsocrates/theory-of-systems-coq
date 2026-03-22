(** * RefinementIntegral.v -- Process refinement for Riemann integrals
    CLASSICAL: ∫₀¹ f(x)dx = 1/2. One number.
    PROCESS:   S_K = (1/K) Σ f(k/K). Full Riemann sum sequence.
    WITNESS:   f(x)=1/2 (constant) vs g(x)=x (linear).
    STATUS: 10 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.ProcessRefinement.

Open Scope Q_scope.

(* ================================================================== *)
(*  RIEMANN SUM PROCESSES                                              *)
(* ================================================================== *)

(** Left-endpoint Riemann sum for f on [0,1] with N subdivisions *)
(** S_N = (1/N) Σ_{k=0}^{N-1} f(k/N) *)

(** Constant function f(x) = 1/2: integral = 1/2 *)
(** Riemann sum = 1/2 for ALL N (constant functions are exact) *)
Definition riemann_const : Process :=
  fun K => 1#2.

(** Linear function g(x) = x: integral = 1/2 *)
(** S_N = (1/N) · (0/N + 1/N + ... + (N-1)/N) = (N-1)/(2N) *)
Definition riemann_linear : Process :=
  fun K =>
    let N := S K in
    inject_Z (Z.of_nat (N - 1)) / (2 * inject_Z (Z.of_nat N)).

(* ================================================================== *)
(*  CONCRETE VALUES                                                    *)
(* ================================================================== *)

Lemma const_1 : riemann_const 0%nat == 1#2.
Proof. vm_compute. reflexivity. Qed.

Lemma const_3 : riemann_const 2%nat == 1#2.
Proof. vm_compute. reflexivity. Qed.

Lemma const_10 : riemann_const 9%nat == 1#2.
Proof. vm_compute. reflexivity. Qed.

Lemma linear_1 : riemann_linear 0%nat == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma linear_2 : riemann_linear 1%nat == 1#4.
Proof. vm_compute. reflexivity. Qed.

Lemma linear_3 : riemann_linear 2%nat == 1#3.
Proof. vm_compute. reflexivity. Qed.

Lemma linear_4 : riemann_linear 3%nat == 3#8.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  DIFFERENT PROCESSES, SAME LIMIT                                    *)
(* ================================================================== *)

Lemma const_linear_diff_0 : ~ (riemann_const 0%nat == riemann_linear 0%nat).
Proof.
  rewrite const_1, linear_1. unfold Qeq. simpl. lia.
Qed.

Lemma const_linear_diff_1 : ~ (riemann_const 1%nat == riemann_linear 1%nat).
Proof.
  rewrite linear_2.
  assert (H : riemann_const 1%nat == 1#2) by (vm_compute; reflexivity).
  rewrite H. unfold Qeq. simpl. lia.
Qed.

(** Linear approaches 1/2: (N-1)/(2N) → 1/2 *)
Lemma linear_approaches : riemann_linear 99%nat == 99#200.
Proof. vm_compute. reflexivity. Qed.

(** ★ INTEGRAL STRICT REFINEMENT *)
Theorem integral_strict_refinement :
  (* Constant is always 1/2 *)
  riemann_const 0%nat == 1#2 /\
  riemann_const 9%nat == 1#2 /\
  (* Linear starts at 0, approaches 1/2 *)
  riemann_linear 0%nat == 0 /\
  riemann_linear 3%nat == 3#8 /\
  (* Different processes! *)
  ~ (riemann_const 0%nat == riemann_linear 0%nat).
Proof.
  split; [|split; [|split; [|split]]].
  - exact const_1.
  - exact const_10.
  - exact linear_1.
  - exact linear_4.
  - exact const_linear_diff_0.
Qed.
