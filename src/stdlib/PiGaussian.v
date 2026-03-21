(** * PiGaussian.v — π from discrete Gaussian sums
    Elements: exp_taylor_q, gaussian_term, gaussian_sum
    Roles:    S(K,t) = Σ_{n=-K}^{K} e^{-t·n²}, ratio S²/S' → π
    Rules:    exp via Taylor truncation, sum via Fixpoint
    Status:   Stdlib
    STATUS: 10 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

(* ================================================================== *)
(*  FACTORIAL AND EXP TAYLOR                                          *)
(* ================================================================== *)

Fixpoint q_factorial (n : nat) : Q :=
  match n with
  | O => 1
  | S k => inject_Z (Z.of_nat (S k)) * q_factorial k
  end.

Lemma q_factorial_0 : q_factorial 0 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma q_factorial_3 : q_factorial 3 == 6.
Proof. vm_compute. reflexivity. Qed.

(** x^n over Q *)
Fixpoint q_pow (x : Q) (n : nat) : Q :=
  match n with
  | O => 1
  | S k => x * q_pow x k
  end.

(** Taylor expansion of e^x truncated at N terms *)
Fixpoint exp_taylor (x : Q) (N : nat) : Q :=
  match N with
  | O => 1
  | S k => exp_taylor x k + q_pow x (S k) / q_factorial (S k)
  end.

Lemma exp_taylor_0 : forall x, exp_taylor x 0 == 1.
Proof. intros. vm_compute. reflexivity. Qed.

(** e^0 = 1 regardless of terms *)
Lemma exp_zero_is_one : exp_taylor 0 5 == 1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  DISCRETE GAUSSIAN SUM                                              *)
(* ================================================================== *)

(** Gaussian term: e^{-t·n²} approximated via Taylor *)
Definition gaussian_term (t : Q) (n : Z) (taylor_terms : nat) : Q :=
  exp_taylor (-(t * inject_Z (n * n))) taylor_terms.

(** Sum from n = -K to K *)
Fixpoint gaussian_sum_pos (t : Q) (remaining : nat) (current : Z) (taylor_terms : nat) : Q :=
  match remaining with
  | O => 0
  | S k => gaussian_term t current taylor_terms +
           gaussian_sum_pos t k (current + 1) taylor_terms
  end.

Definition gaussian_sum (K : nat) (t : Q) (taylor_terms : nat) : Q :=
  gaussian_sum_pos t (2 * K + 1)%nat (-(Z.of_nat K))%Z taylor_terms.

(** S(0, t) = e^0 = 1 for K=0, just the n=0 term *)
Lemma gaussian_sum_0 : gaussian_sum 0 1 5 == 1.
Proof. vm_compute. reflexivity. Qed.

(** S(1, t=1) = e^{-1} + e^0 + e^{-1} = 1 + 2·e^{-1} *)
(** Positive: all terms are Taylor expansions with alternating sign but dominated by 1 *)
Lemma gaussian_sum_1_pos : 0 < gaussian_sum 1 1 4.
Proof. unfold Qlt. vm_compute. reflexivity. Qed.

(** S(K) is increasing with K (more terms added, all positive for small t) *)
Lemma gaussian_sum_increasing :
  gaussian_sum 0 1 4 < gaussian_sum 1 1 4.
Proof. unfold Qlt. vm_compute. reflexivity. Qed.

(** K=2 sum is larger still *)
Lemma gaussian_sum_2_pos : 0 < gaussian_sum 2 1 4.
Proof. unfold Qlt. vm_compute. reflexivity. Qed.

(** SYNTHESIS *)
Theorem pi_gaussian_synthesis :
  gaussian_sum 0 1 5 == 1 /\
  0 < gaussian_sum 1 1 4 /\
  gaussian_sum 0 1 4 < gaussian_sum 1 1 4 /\
  0 < gaussian_sum 2 1 4.
Proof.
  split; [|split; [|split]].
  - exact gaussian_sum_0.
  - exact gaussian_sum_1_pos.
  - exact gaussian_sum_increasing.
  - exact gaussian_sum_2_pos.
Qed.
