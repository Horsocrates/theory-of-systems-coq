(** * GaussianPrimes.v -- Gaussian integers: norms, splitting, ramification
    Elements: gauss_norm, concrete representations of primes as sums of squares
    Roles:    i connects Z to Z[i]; norm is multiplicative
    Rules:    p ≡ 1 mod 4 splits (5,13,17); p ≡ 3 mod 4 stays prime (3); 2 ramifies
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

(* ================================================================== *)
(*  PART I: GAUSSIAN NORM                                               *)
(* ================================================================== *)

Definition gauss_norm (a b : Z) : Z := a * a + b * b.

(* ================================================================== *)
(*  PART II: PRIMES THAT SPLIT (p ≡ 1 mod 4)                          *)
(* ================================================================== *)

(* 5 = 2^2 + 1^2 *)
Lemma five_splits : gauss_norm 2 1 = 5.
Proof. reflexivity. Qed.

(* 13 = 3^2 + 2^2 *)
Lemma thirteen_splits : gauss_norm 3 2 = 13.
Proof. reflexivity. Qed.

(* 17 = 4^2 + 1^2 *)
Lemma seventeen_splits : gauss_norm 4 1 = 17.
Proof. reflexivity. Qed.

(* 29 = 5^2 + 2^2 *)
Lemma twentynine_splits : gauss_norm 5 2 = 29.
Proof. reflexivity. Qed.

(* 37 = 6^2 + 1^2 *)
Lemma thirtyseven_splits : gauss_norm 6 1 = 37.
Proof. reflexivity. Qed.

(* ================================================================== *)
(*  PART III: 3 IS INERT (no representation as a^2 + b^2)             *)
(* ================================================================== *)

(* For nonneg a,b: if a^2+b^2=3 then a<=1, b<=1, but 0+0=0, 0+1=1, 1+0=1, 1+1=2 *)
Lemma three_no_rep : forall a b, 0 <= a -> 0 <= b -> gauss_norm a b <> 3.
Proof.
  unfold gauss_norm. intros a b Ha Hb.
  intro H.
  assert (Ha2 : a <= 1) by nia.
  assert (Hb2 : b <= 1) by nia.
  nia.
Qed.

(* ================================================================== *)
(*  PART IV: NORM IS MULTIPLICATIVE (concrete)                          *)
(* ================================================================== *)

(* |2+i|^2 * |1+i|^2 = 5 * 2 = 10 *)
(* (2+i)(1+i) = 2+2i+i+i^2 = 1+3i *)
(* |1+3i|^2 = 1+9 = 10 *)
Lemma norm_mult_concrete :
  gauss_norm 2 1 * gauss_norm 1 1 = gauss_norm 1 3.
Proof. reflexivity. Qed.

(* |3+2i|^2 * |1+i|^2 = 13 * 2 = 26 *)
(* (3+2i)(1+i) = 3+3i+2i+2i^2 = 1+5i *)
(* |1+5i|^2 = 1+25 = 26 *)
Lemma norm_mult_concrete_2 :
  gauss_norm 3 2 * gauss_norm 1 1 = gauss_norm 1 5.
Proof. reflexivity. Qed.

(* ================================================================== *)
(*  PART V: 2 RAMIFIES: (1+i)^2 = 2i                                  *)
(* ================================================================== *)

(* (1+i)^2 = 1 + 2i + i^2 = 2i, so |2i|^2 = 4 = 2*|(1+i)|^2 = 2*2=4 *)
Lemma two_ramifies_norm : gauss_norm 0 2 = 4.
Proof. reflexivity. Qed.

Lemma one_plus_i_norm_sq : gauss_norm 1 1 = 2.
Proof. reflexivity. Qed.

Lemma ramification_check : gauss_norm 0 2 = 2 * gauss_norm 1 1.
Proof. reflexivity. Qed.

(* ================================================================== *)
(*  PART VI: CONGRUENCE CHECKS                                          *)
(* ================================================================== *)

Lemma five_mod_4 : 5 mod 4 = 1.
Proof. reflexivity. Qed.

Lemma thirteen_mod_4 : 13 mod 4 = 1.
Proof. reflexivity. Qed.

Lemma three_mod_4 : 3 mod 4 = 3.
Proof. reflexivity. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                           *)
(* ================================================================== *)

Theorem gaussian_primes_synthesis :
  (* Splitting *)
  gauss_norm 2 1 = 5 /\
  gauss_norm 3 2 = 13 /\
  gauss_norm 4 1 = 17 /\
  (* Inert *)
  (forall a b, 0 <= a -> 0 <= b -> gauss_norm a b <> 3) /\
  (* Multiplicativity *)
  gauss_norm 2 1 * gauss_norm 1 1 = gauss_norm 1 3 /\
  (* Ramification *)
  gauss_norm 0 2 = 2 * gauss_norm 1 1.
Proof.
  repeat split; try reflexivity.
  apply three_no_rep.
Qed.
