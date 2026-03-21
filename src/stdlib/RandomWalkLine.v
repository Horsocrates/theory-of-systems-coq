(** * RandomWalkLine.v -- Random walk on integer line: central binomial coefficients
    Elements: binomial, central_binom, return_line
    Roles:    P(return in 2K steps) = C(2K,K) / 4^K
    Rules:    Exact combinatorial formulas, verifiable against OEIS
    Status:   Stdlib
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

(* ================================================================== *)
(*  BINOMIAL COEFFICIENTS                                              *)
(* ================================================================== *)

Fixpoint binomial (n k : nat) : nat :=
  match n, k with
  | _, O => 1%nat
  | O, S _ => 0%nat
  | S n', S k' => (binomial n' k' + binomial n' (S k'))%nat
  end.

(** Central binomial coefficients: C(2K, K) *)
Definition central_binom (K : nat) : nat := binomial (2 * K) K.

Lemma cb_0 : central_binom 0 = 1%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma cb_1 : central_binom 1 = 2%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma cb_2 : central_binom 2 = 6%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma cb_3 : central_binom 3 = 20%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma cb_4 : central_binom 4 = 70%nat.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  RETURN PROBABILITY ON ℤ                                            *)
(* ================================================================== *)

(** P(return to 0 in 2K steps) = C(2K,K) / 4^K *)
Definition return_line (K : nat) : Q :=
  inject_Z (Z.of_nat (central_binom K)) /
  inject_Z (Z.of_nat (Nat.pow 4 K)).

Lemma return_line_0 : return_line 0 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma return_line_1 : return_line 1 == 1#2.
Proof. vm_compute. reflexivity. Qed.

Lemma return_line_2 : return_line 2 == 3#8.
Proof. vm_compute. reflexivity. Qed.

Lemma return_line_3 : return_line 3 == 5#16.
Proof. vm_compute. reflexivity. Qed.

(** Return probability DECREASES: harder to return as K grows *)
Lemma return_decreasing_12 : return_line 2 < return_line 1.
Proof. rewrite return_line_1, return_line_2. lra. Qed.

Lemma return_decreasing_23 : return_line 3 < return_line 2.
Proof. rewrite return_line_2, return_line_3. lra. Qed.

(** SYNTHESIS *)
Theorem random_walk_line_synthesis :
  (* OEIS A000984: 1, 2, 6, 20, 70 *)
  central_binom 4 = 70%nat /\
  (* Return probabilities: 1, 1/2, 3/8, 5/16 *)
  return_line 2 == 3#8 /\
  return_line 3 == 5#16 /\
  (* Decreasing *)
  return_line 3 < return_line 2.
Proof.
  split; [|split; [|split]].
  - exact cb_4.
  - exact return_line_2.
  - exact return_line_3.
  - exact return_decreasing_23.
Qed.
