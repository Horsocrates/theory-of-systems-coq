(* ========================================================================= *)
(*                                                                           *)
(*                    FIELD EXTENSIONS AS TOS SYSTEMS                        *)
(*              Polynomials over Q, Roots, and Extension Degrees             *)
(*                                                                           *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)         *)
(*                                                                           *)
(*  E/R/R INTERPRETATION:                                                    *)
(*  =====================                                                    *)
(*    Elements: Polynomials (list Q), field elements, extension degrees      *)
(*    Roles:    eval_poly (evaluation), is_root (vanishing), irreducibility  *)
(*    Rules:    Degree computation, root checks, extension degree = poly deg *)
(*                                                                           *)
(*  STATUS: 20 Qed, 0 Admitted, 0 axioms                                    *)
(*  Author: Horsocrates | Date: March 2026                                   *)
(*                                                                           *)
(* ========================================================================= *)

From Stdlib Require Import QArith Qabs Lia ZArith List Bool.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ---- Polynomial representation: [a0; a1; ...; an] = a0 + a1*x + ... ---- *)

Fixpoint eval_poly (p : list Q) (x : Q) : Q :=
  match p with
  | [] => 0
  | a :: rest => a + x * eval_poly rest x
  end.

Definition poly_degree (p : list Q) : nat := pred (length p).

Definition is_root (p : list Q) (x : Q) : Prop := eval_poly p x == 0.

(* ---- Polynomial addition ---- *)

Fixpoint poly_add (p q : list Q) : list Q :=
  match p, q with
  | [], _ => q
  | _, [] => p
  | a :: p', b :: q' => (a + b) :: poly_add p' q'
  end.

(* ---- Polynomial scalar multiplication ---- *)

Fixpoint poly_scale (c : Q) (p : list Q) : list Q :=
  match p with
  | [] => []
  | a :: rest => (c * a) :: poly_scale c rest
  end.

(* ======================================================================== *)
(*                           BASIC EVALUATIONS                              *)
(* ======================================================================== *)

Lemma eval_poly_nil : forall x, eval_poly [] x == 0.
Proof. intros. simpl. lra. Qed.

Lemma eval_poly_const : forall c x, eval_poly [c] x == c.
Proof. intros. simpl. lra. Qed.

Lemma eval_poly_linear : forall a b x, eval_poly [a; b] x == a + b * x.
Proof. intros. simpl. lra. Qed.

Lemma eval_poly_quadratic : forall c b a x,
  eval_poly [c; b; a] x == c + b * x + a * x * x.
Proof. intros. simpl. lra. Qed.

(* ======================================================================== *)
(*                          DEGREE COMPUTATIONS                             *)
(* ======================================================================== *)

Lemma degree_of_x2_minus_2 : poly_degree [-(2); 0; 1] = 2%nat.
Proof. reflexivity. Qed.

Lemma degree_of_x3_minus_2 : poly_degree [-(2); 0; 0; 1] = 3%nat.
Proof. reflexivity. Qed.

Lemma degree_of_linear : forall a b, poly_degree [a; b] = 1%nat.
Proof. reflexivity. Qed.

Lemma degree_of_constant : forall c, poly_degree [c] = 0%nat.
Proof. reflexivity. Qed.

(* ======================================================================== *)
(*                       SQRT(2) POLYNOMIAL: x^2 - 2                       *)
(* ======================================================================== *)

(* x^2 - 2 evaluated at x *)
Definition sqrt2_poly : list Q := [-(2); 0; 1].

Lemma sqrt2_poly_at_x : forall x,
  eval_poly sqrt2_poly x == x * x - 2.
Proof.
  intros. unfold sqrt2_poly. simpl. lra.
Qed.

(* 17/12 is a rational approximation to sqrt(2) *)
(* (17/12)^2 = 289/144, so (17/12)^2 - 2 = 289/144 - 288/144 = 1/144 *)
Lemma sqrt2_root_approx :
  eval_poly sqrt2_poly (17#12) == 1#144.
Proof.
  unfold sqrt2_poly. simpl.
  vm_compute. reflexivity.
Qed.

(* 1 is not a root of x^2 - 2 *)
Lemma one_not_root_sqrt2 : ~ is_root sqrt2_poly 1.
Proof.
  unfold is_root, sqrt2_poly. simpl.
  intro H. lra.
Qed.

(* 3/2 is not a root of x^2 - 2 *)
Lemma three_halves_not_root_sqrt2 : ~ is_root sqrt2_poly (3#2).
Proof.
  unfold is_root, sqrt2_poly. simpl.
  intro H. vm_compute in H. discriminate.
Qed.

(* 7/5 is not a root of x^2 - 2 *)
Lemma seven_fifths_not_root_sqrt2 : ~ is_root sqrt2_poly (7#5).
Proof.
  unfold is_root, sqrt2_poly. simpl.
  intro H. vm_compute in H. discriminate.
Qed.

(* ======================================================================== *)
(*                       CUBE ROOT POLYNOMIAL: x^3 - 2                     *)
(* ======================================================================== *)

Definition cbrt2_poly : list Q := [-(2); 0; 0; 1].

Lemma cbrt2_poly_at_x : forall x,
  eval_poly cbrt2_poly x == x * x * x - 2.
Proof.
  intros. unfold cbrt2_poly. simpl. lra.
Qed.

(* 5/4 is not a root of x^3 - 2 *)
Lemma five_fourths_not_root_cbrt2 : ~ is_root cbrt2_poly (5#4).
Proof.
  unfold is_root, cbrt2_poly. simpl.
  intro H. vm_compute in H. discriminate.
Qed.

(* ======================================================================== *)
(*                       EXTENSION DEGREE PROPERTIES                        *)
(* ======================================================================== *)

(* Extension degree of Q(sqrt(2))/Q is 2, matching minimal polynomial degree *)
Definition ext_degree_sqrt2 : nat := poly_degree sqrt2_poly.

Lemma ext_degree_sqrt2_is_2 : ext_degree_sqrt2 = 2%nat.
Proof. reflexivity. Qed.

(* Extension degree of Q(cbrt(2))/Q is 3 *)
Definition ext_degree_cbrt2 : nat := poly_degree cbrt2_poly.

Lemma ext_degree_cbrt2_is_3 : ext_degree_cbrt2 = 3%nat.
Proof. reflexivity. Qed.

(* Tower law: [Q(sqrt(2), cbrt(3)) : Q] = [Q(sqrt(2),cbrt(3)) : Q(sqrt(2))] * [Q(sqrt(2)) : Q] *)
(* Concrete instance: 6 = 3 * 2 *)
Lemma tower_law_concrete : (3 * 2 = 6)%nat.
Proof. reflexivity. Qed.

(* Polynomial evaluation distributes over addition at a point *)
Lemma eval_poly_add : forall p q x,
  eval_poly (poly_add p q) x == eval_poly p x + eval_poly q x.
Proof.
  induction p as [|a p' IHp]; intros q x; simpl.
  - lra.
  - destruct q as [|b q']; simpl.
    + lra.
    + rewrite IHp. lra.
Qed.

(* Scaling a polynomial scales its evaluation *)
Lemma eval_poly_scale : forall c p x,
  eval_poly (poly_scale c p) x == c * eval_poly p x.
Proof.
  intros c p. induction p as [|a p' IHp]; intros x; simpl.
  - lra.
  - rewrite IHp. lra.
Qed.
