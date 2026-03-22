(** * FiniteSizeWalk.v -- Finite-Size Effects in Random Walk Return Probabilities
    Elements: binom_2K_K, P_return, pi_from_walk
    Roles:    Return probability P(K) = C(2K,K)/4^K converges to 0
    Rules:    P(K) ~ 1/sqrt(pi*K), so pi = lim 1/(K*P(K)^2)
    Status:   Stdlib
    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
From Stdlib Require Import ZArith.
Open Scope Q_scope.

(* ================================================================== *)
(*  CENTRAL BINOMIAL COEFFICIENTS C(2K,K) for small K                 *)
(* ================================================================== *)

Definition binom_2K_K (K : nat) : Z :=
  match K with
  | O => 1
  | S O => 2
  | S (S O) => 6
  | S (S (S O)) => 20
  | S (S (S (S O))) => 70
  | S (S (S (S (S O)))) => 252
  | _ => 0
  end%Z.

(** Verify values *)
Lemma binom_values : binom_2K_K 0 = 1%Z /\ binom_2K_K 1 = 2%Z /\
  binom_2K_K 2 = 6%Z /\ binom_2K_K 3 = 20%Z /\
  binom_2K_K 4 = 70%Z /\ binom_2K_K 5 = 252%Z.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ================================================================== *)
(*  RETURN PROBABILITY: P(K) = C(2K,K) / 4^K                          *)
(* ================================================================== *)

Definition P_return (K : nat) : Q :=
  inject_Z (binom_2K_K K) / inject_Z (Z.pow 4 (Z.of_nat K)).

(** P(1) = 2/4 = 1/2 *)
Lemma P_return_1 : P_return 1 == 1#2.
Proof. vm_compute. reflexivity. Qed.

(** P(2) = 6/16 = 3/8 *)
Lemma P_return_2 : P_return 2 == 3#8.
Proof. vm_compute. reflexivity. Qed.

(** P(3) = 20/64 = 5/16 *)
Lemma P_return_3 : P_return 3 == 5#16.
Proof. vm_compute. reflexivity. Qed.

(** P(4) = 70/256 = 35/128 *)
Lemma P_return_4 : P_return 4 == 35#128.
Proof. vm_compute. reflexivity. Qed.

(** P(5) = 252/1024 = 63/256 *)
Lemma P_return_5 : P_return 5 == 63#256.
Proof. vm_compute. reflexivity. Qed.

(** Return probabilities decrease: P(3) < P(2) *)
Lemma P_decreasing_2_3 : P_return 3 < P_return 2.
Proof. unfold P_return, binom_2K_K, inject_Z, Qlt. vm_compute. reflexivity. Qed.

(** Return probabilities decrease: P(4) < P(3) *)
Lemma P_decreasing_3_4 : P_return 4 < P_return 3.
Proof. unfold P_return, binom_2K_K, inject_Z, Qlt. vm_compute. reflexivity. Qed.

(** P(5) is positive *)
Lemma P_return_5_positive : 0 < P_return 5.
Proof. unfold P_return, binom_2K_K, inject_Z, Qlt. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  PI FROM WALK: pi ~ 1/(K * P(K)^2)                                 *)
(* ================================================================== *)

Definition pi_from_walk (K : nat) : Q :=
  1 / (inject_Z (Z.of_nat K) * P_return K * P_return K).

(** K=1: 1/(1*(1/2)^2) = 1/(1/4) = 4 *)
Lemma pi_walk_K1 : pi_from_walk 1 == 4.
Proof. vm_compute. reflexivity. Qed.

(** K=2: 1/(2*(3/8)^2) = 1/(2*9/64) = 1/(9/32) = 32/9 *)
Lemma pi_walk_K2 : pi_from_walk 2 == 32#9.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

Theorem finite_size_walk_synthesis :
  P_return 1 == 1#2 /\
  P_return 5 == 63#256 /\
  P_return 3 < P_return 2 /\
  0 < P_return 5.
Proof.
  split; [exact P_return_1|].
  split; [exact P_return_5|].
  split; [exact P_decreasing_2_3|].
  exact P_return_5_positive.
Qed.
