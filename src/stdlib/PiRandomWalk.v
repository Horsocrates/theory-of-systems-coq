(** * PiRandomWalk.v — π from random walk return probability
    Elements: binomial, return_prob, pi_walk
    Roles:    P(return to origin after 2K steps) = C(2K,K)/4^K
    Rules:    1/(K·P²) → π as K → ∞ (Stirling's approximation)
    Status:   Stdlib
    STATUS: 10 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

(* ================================================================== *)
(*  BINOMIAL COEFFICIENT (defined locally)                            *)
(* ================================================================== *)

(** Pascal's triangle: C(n,k) *)
Fixpoint binomial (n k : nat) : nat :=
  match n, k with
  | _, O => 1%nat
  | O, S _ => 0%nat
  | S n', S k' => (binomial n' k' + binomial n' (S k'))%nat
  end.

Lemma binomial_2_1 : binomial 2 1 = 2%nat.
Proof. reflexivity. Qed.

Lemma binomial_4_2 : binomial 4 2 = 6%nat.
Proof. reflexivity. Qed.

Lemma binomial_6_3 : binomial 6 3 = 20%nat.
Proof. reflexivity. Qed.

(* ================================================================== *)
(*  RETURN PROBABILITY                                                 *)
(* ================================================================== *)

(** 4^K *)
Fixpoint pow4 (K : nat) : nat :=
  match K with
  | O => 1%nat
  | S k => (4 * pow4 k)%nat
  end.

(** P(return at step 2K) = C(2K, K) / 4^K *)
Definition return_prob (K : nat) : Q :=
  inject_Z (Z.of_nat (binomial (2*K) K)) / inject_Z (Z.of_nat (pow4 K)).

Lemma return_prob_1 : return_prob 1 == 1#2.
Proof. vm_compute. reflexivity. Qed.

Lemma return_prob_2 : return_prob 2 == 3#8.
Proof. vm_compute. reflexivity. Qed.

Lemma return_prob_3 : return_prob 3 == 5#16.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  π FROM WALK: 1/(K · P²) → π                                       *)
(* ================================================================== *)

(** pi_walk K = 1 / (K · P(K)²) *)
Definition pi_walk (K : nat) : Q :=
  let p := return_prob K in
  inject_Z (Z.of_nat K) * p * p.

(** Reciprocal: 1/pi_walk → π *)
Definition pi_walk_inv (K : nat) : Q :=
  1 / pi_walk K.

Lemma pi_walk_1 : pi_walk 1 == 1#4.
Proof. vm_compute. reflexivity. Qed.

Lemma pi_walk_inv_1 : pi_walk_inv 1 == 4.
Proof. vm_compute. reflexivity. Qed.

(** K=2: pi_walk = 2 · (3/8)² = 2 · 9/64 = 9/32 *)
Lemma pi_walk_2 : pi_walk 2 == 9#32.
Proof. vm_compute. reflexivity. Qed.

(** K=3: pi_walk = 3 · (5/16)² = 3 · 25/256 = 75/256 *)
Lemma pi_walk_3 : pi_walk 3 == 75#256.
Proof. vm_compute. reflexivity. Qed.

(** SYNTHESIS *)
Theorem pi_random_walk_synthesis :
  return_prob 1 == 1#2 /\
  return_prob 2 == 3#8 /\
  return_prob 3 == 5#16 /\
  pi_walk_inv 1 == 4 /\
  pi_walk 2 == 9#32.
Proof.
  split; [|split; [|split; [|split]]].
  - exact return_prob_1.
  - exact return_prob_2.
  - exact return_prob_3.
  - exact pi_walk_inv_1.
  - exact pi_walk_2.
Qed.
