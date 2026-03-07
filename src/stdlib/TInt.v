(* ========================================================================= *)
(* TInt: Integer Arithmetic as ToS System                                    *)
(*                                                                           *)
(* Part of: Theory of Systems - ToS-Lang Standard Library                    *)
(*                                                                           *)
(* E/R/R Analysis:                                                           *)
(*   Elements: integers (Z)                                                  *)
(*   Roles: SignedQuantity (positive | negative | zero)                      *)
(*   Rules: ring axioms (add, mul, neg)                                      *)
(*   Status: positive | negative | zero                                      *)
(*   Constitution: Z is an integral domain                                   *)
(*                                                                           *)
(* STATUS: 16 Qed, 0 Admitted, 0 axioms                                     *)
(* Author: Horsocrates | Date: 2026                                          *)
(* ========================================================================= *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

From ToS Require Import TheoryOfSystems_Core_ERR.

(* ========================================================================= *)
(*                   PART I: TYPE AND OPERATIONS                             *)
(* ========================================================================= *)

Definition TInt := Z.

(** Status classification via sign *)
Definition tint_sign (x : TInt) : Z := Z.sgn x.

(** Arithmetic operations *)
Definition tint_add (x y : TInt) : TInt := x + y.
Definition tint_mul (x y : TInt) : TInt := x * y.
Definition tint_sub (x y : TInt) : TInt := x - y.
Definition tint_abs (x : TInt) : TInt := Z.abs x.
Definition tint_neg (x : TInt) : TInt := - x.
Definition tint_div (x y : TInt) : TInt := x / y.
Definition tint_mod (x y : TInt) : TInt := x mod y.

(** Status type for D1 classification *)
Inductive tint_status : Set :=
  | TInt_Positive
  | TInt_Negative
  | TInt_Zero.

Definition classify_tint (x : TInt) : tint_status :=
  match x with
  | Z0 => TInt_Zero
  | Zpos _ => TInt_Positive
  | Zneg _ => TInt_Negative
  end.

(* ========================================================================= *)
(*                   PART II: RING PROPERTIES                                *)
(* ========================================================================= *)

(** 1. Addition is commutative *)
Lemma tint_add_comm : forall x y : TInt,
    tint_add x y = tint_add y x.
Proof.
  intros x y. unfold tint_add. lia.
Qed.

(** 2. Addition is associative *)
Lemma tint_add_assoc : forall x y z : TInt,
    tint_add (tint_add x y) z = tint_add x (tint_add y z).
Proof.
  intros x y z. unfold tint_add. lia.
Qed.

(** 3. Multiplication is commutative *)
Lemma tint_mul_comm : forall x y : TInt,
    tint_mul x y = tint_mul y x.
Proof.
  intros x y. unfold tint_mul. apply Z.mul_comm.
Qed.

(** 4. Multiplication is associative *)
Lemma tint_mul_assoc : forall x y z : TInt,
    tint_mul (tint_mul x y) z = tint_mul x (tint_mul y z).
Proof.
  intros x y z. unfold tint_mul. symmetry. apply Z.mul_assoc.
Qed.

(** 5. Distributivity *)
Lemma tint_mul_add_distr : forall x y z : TInt,
    tint_mul x (tint_add y z) = tint_add (tint_mul x y) (tint_mul x z).
Proof.
  intros x y z. unfold tint_mul, tint_add. apply Z.mul_add_distr_l.
Qed.

(** 6. Zero is right identity for addition *)
Lemma tint_add_zero_r : forall x : TInt,
    tint_add x 0 = x.
Proof.
  intros x. unfold tint_add. lia.
Qed.

(** 7. One is right identity for multiplication *)
Lemma tint_mul_one_r : forall x : TInt,
    tint_mul x 1 = x.
Proof.
  intros x. unfold tint_mul. apply Z.mul_1_r.
Qed.

(* ========================================================================= *)
(*                   PART III: ABSOLUTE VALUE AND SIGN                       *)
(* ========================================================================= *)

(** 8. Absolute value is nonneg *)
Lemma tint_abs_nonneg : forall x : TInt,
    0 <= tint_abs x.
Proof.
  intros x. unfold tint_abs. apply Z.abs_nonneg.
Qed.

(** 9. Sign-abs decomposition: sgn(x) * |x| = x *)
Lemma tint_sign_abs : forall x : TInt,
    tint_sign x * tint_abs x = x.
Proof.
  intros x. unfold tint_sign, tint_abs.
  destruct x; simpl; lia.
Qed.

(** 10. Sign of zero is zero *)
Lemma tint_zero_status : tint_sign 0 = 0.
Proof.
  unfold tint_sign. reflexivity.
Qed.

(** 11. Sign of positive is 1 *)
Lemma tint_positive_status : forall x : TInt,
    x > 0 -> tint_sign x = 1.
Proof.
  intros x Hx. unfold tint_sign. apply Z.sgn_pos. lia.
Qed.

(** 12. Sign of negative is -1 *)
Lemma tint_negative_status : forall x : TInt,
    x < 0 -> tint_sign x = -1.
Proof.
  intros x Hx. unfold tint_sign. apply Z.sgn_neg. lia.
Qed.

(* ========================================================================= *)
(*                   PART IV: ADDITIONAL PROPERTIES                          *)
(* ========================================================================= *)

(** 13. Negation is involutive *)
Lemma tint_neg_involutive : forall x : TInt,
    tint_neg (tint_neg x) = x.
Proof.
  intros x. unfold tint_neg. lia.
Qed.

(** 14. Additive inverse *)
Lemma tint_add_neg : forall x : TInt,
    tint_add x (tint_neg x) = 0.
Proof.
  intros x. unfold tint_add, tint_neg. lia.
Qed.

(** 15. No zero divisors (integral domain) *)
Lemma tint_no_zero_divisors : forall x y : TInt,
    tint_mul x y = 0 -> x = 0 \/ y = 0.
Proof.
  intros x y H. unfold tint_mul in H.
  apply Z.mul_eq_0. exact H.
Qed.

(** 16. Positive classification *)
Lemma tint_classify_pos : forall p, classify_tint (Zpos p) = TInt_Positive.
Proof. intros. reflexivity. Qed.

(** 17. Negative classification *)
Lemma tint_classify_neg : forall p, classify_tint (Zneg p) = TInt_Negative.
Proof. intros. reflexivity. Qed.

(** 18. Zero classification *)
Lemma tint_classify_zero : classify_tint 0 = TInt_Zero.
Proof. reflexivity. Qed.
(* ========================================================================= *)
(*                   SUMMARY                                                 *)
(* ========================================================================= *)

(**
  PROVEN (16 Qed):

  Ring axioms:
    tint_add_comm, tint_add_assoc, tint_mul_comm, tint_mul_assoc,
    tint_mul_add_distr, tint_add_zero_r, tint_mul_one_r

  Sign and absolute value:
    tint_abs_nonneg, tint_sign_abs, tint_zero_status,
    tint_positive_status, tint_negative_status

  Additional:
    tint_neg_involutive, tint_add_neg, tint_no_zero_divisors,
    tint_classify_correct

  AXIOMS: 0
*)
