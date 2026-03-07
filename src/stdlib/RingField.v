(** * RingField.v — Rings and Fields as ToS Systems

    Theory of Systems — Verified Standard Library (Tier 2b)

    Elements: carrier set R, addition +, multiplication *, identity 0 and 1
    Roles:    addition → CombiningOperation, multiplication → ScalingOperation,
              zero → AdditiveIdentity, one → MultiplicativeIdentity
    Rules:    ring axioms (additive group + multiplicative monoid + distribution)
    Status:   zero | nonzero | unit | zero_divisor

    CONNECTION: GroupTheory.v (additive group)

    STATUS: 20 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lqa.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Close Scope Z_scope.
Open Scope Q_scope.

From ToS Require Import GroupTheory.

(* ================================================================= *)
(*  Ring: additive group + commutative multiplicative monoid           *)
(*        + left distributivity (right follows from commutativity)     *)
(* ================================================================= *)

Record Ring := mkRing {
  r_add_group : Group;
  r_mul : g_carrier r_add_group -> g_carrier r_add_group -> g_carrier r_add_group;
  r_one : g_carrier r_add_group;
  r_mul_compat : forall x x' y y',
    g_eq r_add_group x x' -> g_eq r_add_group y y' ->
    g_eq r_add_group (r_mul x y) (r_mul x' y');
  r_mul_assoc : forall x y z,
    g_eq r_add_group (r_mul (r_mul x y) z) (r_mul x (r_mul y z));
  r_mul_comm : forall x y,
    g_eq r_add_group (r_mul x y) (r_mul y x);
  r_mul_one_l : forall x,
    g_eq r_add_group (r_mul r_one x) x;
  r_distrib_l : forall x y z,
    g_eq r_add_group (r_mul x (g_op r_add_group y z))
                     (g_op r_add_group (r_mul x y) (r_mul x z));
}.

(* ================================================================= *)
(*  Field: ring + multiplicative inverse for nonzero elements          *)
(* ================================================================= *)

Record Field := mkField {
  f_ring : Ring;
  f_inv : g_carrier (r_add_group f_ring) -> g_carrier (r_add_group f_ring);
  f_inv_compat : forall x x',
    g_eq (r_add_group f_ring) x x' ->
    g_eq (r_add_group f_ring) (f_inv x) (f_inv x');
  f_inv_r : forall x,
    ~ g_eq (r_add_group f_ring) x (g_id (r_add_group f_ring)) ->
    g_eq (r_add_group f_ring) (r_mul f_ring x (f_inv x)) (r_one f_ring);
}.

(* Convenience notations for ring carrier, equality, addition *)
(* We use the additive group's operations directly. *)

(* ================================================================= *)
(*      PART I: DERIVED RING PROPERTIES (6 Qed)                       *)
(* ================================================================= *)

(** 1. Right multiplicative identity: x * 1 = x *)
Lemma r_mul_one_r : forall (R : Ring) (x : g_carrier (r_add_group R)),
  g_eq (r_add_group R) (r_mul R x (r_one R)) x.
Proof.
  intros R x.
  apply (g_eq_trans (r_add_group R)) with (y := r_mul R (r_one R) x).
  - apply r_mul_comm.
  - apply r_mul_one_l.
Qed.

(** 2. Left annihilation by zero: 0 * x = 0 *)
Lemma r_mul_zero_l : forall (R : Ring) (x : g_carrier (r_add_group R)),
  g_eq (r_add_group R) (r_mul R (g_id (r_add_group R)) x) (g_id (r_add_group R)).
Proof.
  intros R x.
  set (G := r_add_group R).
  set (zero := g_id G).
  set (zx := r_mul R zero x).
  (* Strategy: show zx + zx = zx + 0, then cancel zx from left *)
  apply (g_cancel_l G zx).
  (* Goal: zx + zx = zx + 0 *)
  (* RHS: zx + 0 = zx  by id_r *)
  apply (g_eq_trans G) with (y := zx).
  - (* LHS: zx + zx = (0+0)*x = 0*x = zx *)
    (* First: zx + zx = (0+0)*x — by right distrib *)
    (* (0+0)*x = x*(0+0) = x*0 + x*0 = 0*x + 0*x = zx + zx *)
    (* But actually easier: use distrib_l directly *)
    (* zx + zx = 0*x + 0*x.  We need (0+0)*x = 0*x + 0*x. *)
    (* Use: (0+0)*x comm= x*(0+0) distrib= x*0 + x*0 comm= 0*x + 0*x *)
    apply (g_eq_trans G) with
      (y := r_mul R (g_op G zero zero) x).
    + (* zx + zx = (0+0)*x *)
      apply g_eq_sym.
      apply (g_eq_trans G) with
        (y := r_mul R x (g_op G zero zero)).
      * apply r_mul_comm.
      * apply (g_eq_trans G) with
          (y := g_op G (r_mul R x zero) (r_mul R x zero)).
        -- apply r_distrib_l.
        -- apply g_op_compat; apply r_mul_comm.
    + (* (0+0)*x = 0*x = zx *)
      apply (r_mul_compat R).
      * apply g_id_l.
      * apply g_eq_refl.
  - (* zx = zx + 0 *)
    apply g_eq_sym. apply g_id_r.
Qed.

(** 3. Right annihilation by zero: x * 0 = 0 *)
Lemma r_mul_zero_r : forall (R : Ring) (x : g_carrier (r_add_group R)),
  g_eq (r_add_group R) (r_mul R x (g_id (r_add_group R))) (g_id (r_add_group R)).
Proof.
  intros R x.
  apply (g_eq_trans (r_add_group R)) with
    (y := r_mul R (g_id (r_add_group R)) x).
  - apply r_mul_comm.
  - apply r_mul_zero_l.
Qed.

(** 4. Negation distributes left: (-x) * y = -(x * y) *)
Lemma r_mul_neg_l : forall (R : Ring) (x y : g_carrier (r_add_group R)),
  g_eq (r_add_group R) (r_mul R (g_inv (r_add_group R) x) y)
                        (g_inv (r_add_group R) (r_mul R x y)).
Proof.
  intros R x y.
  set (G := r_add_group R).
  (* Strategy: (-x)*y + x*y = ((-x) + x)*y = 0*y = 0.
     So (-x)*y is the additive inverse of x*y, i.e., -(x*y). *)
  (* g_unique_inv G (x*y) ((-x)*y) :
       (-x)*y + x*y = 0 -> (-x)*y = -(x*y) *)
  apply (g_unique_inv G (r_mul R x y) (r_mul R (g_inv G x) y)).
  (* Goal: (-x)*y + x*y = 0 *)
  (* We prove: (-x)*y + x*y = ((-x) + x)*y = 0*y = 0 *)
  apply (g_eq_trans G) with
    (y := r_mul R (g_op G (g_inv G x) x) y).
  - (* (-x)*y + x*y = ((-x)+x)*y  — right distrib (via comm + distrib_l) *)
    apply g_eq_sym.
    apply (g_eq_trans G) with
      (y := r_mul R y (g_op G (g_inv G x) x)).
    + apply r_mul_comm.
    + apply (g_eq_trans G) with
        (y := g_op G (r_mul R y (g_inv G x)) (r_mul R y x)).
      * apply r_distrib_l.
      * apply (g_eq_trans G) with
          (y := g_op G (r_mul R (g_inv G x) y) (r_mul R x y)).
        -- apply g_op_compat; apply r_mul_comm.
        -- apply g_eq_refl.
  - (* ((-x)+x)*y = 0*y = 0 *)
    apply (g_eq_trans G) with (y := r_mul R (g_id G) y).
    + apply (r_mul_compat R).
      * apply g_inv_l.
      * apply g_eq_refl.
    + apply r_mul_zero_l.
Qed.

(** 5. Right distributivity: (x+y)*z = x*z + y*z *)
Lemma r_distrib_r : forall (R : Ring) (x y z : g_carrier (r_add_group R)),
  g_eq (r_add_group R) (r_mul R (g_op (r_add_group R) x y) z)
                        (g_op (r_add_group R) (r_mul R x z) (r_mul R y z)).
Proof.
  intros R x y z.
  (* (x+y)*z = z*(x+y) = z*x + z*y = x*z + y*z *)
  apply (g_eq_trans (r_add_group R)) with
    (y := r_mul R z (g_op (r_add_group R) x y)).
  - apply r_mul_comm.
  - apply (g_eq_trans (r_add_group R)) with
      (y := g_op (r_add_group R) (r_mul R z x) (r_mul R z y)).
    + apply r_distrib_l.
    + apply g_op_compat; apply r_mul_comm.
Qed.

(** Helper: x * (-y) = -(x * y) — right version of neg_l *)
Lemma r_mul_neg_r : forall (R : Ring) (x y : g_carrier (r_add_group R)),
  g_eq (r_add_group R) (r_mul R x (g_inv (r_add_group R) y))
                        (g_inv (r_add_group R) (r_mul R x y)).
Proof.
  intros R x y.
  set (G := r_add_group R).
  (* x*(-y) = (-y)*x = -(y*x) = -(x*y) *)
  apply (g_eq_trans G) with (y := r_mul R (g_inv G y) x).
  - apply r_mul_comm.
  - apply (g_eq_trans G) with (y := g_inv G (r_mul R y x)).
    + apply r_mul_neg_l.
    + apply g_inv_compat. apply r_mul_comm.
Qed.

(** 6. Negation distributes both: (-x)*(-y) = x*y *)
Lemma r_mul_neg_neg : forall (R : Ring) (x y : g_carrier (r_add_group R)),
  g_eq (r_add_group R) (r_mul R (g_inv (r_add_group R) x) (g_inv (r_add_group R) y))
                        (r_mul R x y).
Proof.
  intros R x y.
  set (G := r_add_group R).
  (* (-x)*(-y) = -(x*(-y)) = -(-(x*y)) = x*y *)
  apply (g_eq_trans G) with (y := g_inv G (r_mul R x (g_inv G y))).
  - apply r_mul_neg_l.
  - apply (g_eq_trans G) with (y := g_inv G (g_inv G (r_mul R x y))).
    + apply g_inv_compat. apply r_mul_neg_r.
    + apply g_inv_inv.
Qed.

(* ================================================================= *)
(*      PART II: Z RING INSTANCE (5 Qed)                               *)
(* ================================================================= *)

(** 7. Z multiplication is associative *)
Lemma Z_ring_mul_assoc : forall x y z : Z,
  ((x * y) * z)%Z = (x * (y * z))%Z.
Proof. intros. lia. Qed.

(** 8. Z multiplication is commutative *)
Lemma Z_ring_mul_comm : forall x y : Z,
  (x * y)%Z = (y * x)%Z.
Proof. intros. lia. Qed.

(** 9. Z multiplication has left identity *)
Lemma Z_ring_one_l : forall x : Z,
  (1 * x)%Z = x.
Proof. intros. lia. Qed.

(** 10. Z multiplication distributes over addition *)
Lemma Z_ring_distrib : forall x y z : Z,
  (x * (y + z))%Z = (x * y + x * z)%Z.
Proof. intros. lia. Qed.

(** 11. Z ring instance *)
Definition Z_ring : Ring := mkRing
  Z_add_group
  Z.mul
  1%Z
  (fun x x' y y' (H1 : x = x') (H2 : y = y') =>
    f_equal2 Z.mul H1 H2)
  Z_ring_mul_assoc
  Z_ring_mul_comm
  Z_ring_one_l
  Z_ring_distrib.

(* ================================================================= *)
(*      PART III: Q RING INSTANCE (6 Qed)                              *)
(* ================================================================= *)

(** 12. Q multiplication is associative *)
Lemma Q_ring_mul_assoc : forall x y z : Q,
  (x * y) * z == x * (y * z).
Proof. intros. ring. Qed.

(** 13. Q multiplication is commutative *)
Lemma Q_ring_mul_comm : forall x y : Q,
  x * y == y * x.
Proof. intros. ring. Qed.

(** 14. Q multiplication has left identity *)
Lemma Q_ring_one_l : forall x : Q,
  1 * x == x.
Proof. intros. ring. Qed.

(** 15. Q multiplication distributes over addition *)
Lemma Q_ring_distrib : forall x y z : Q,
  x * (y + z) == x * y + x * z.
Proof. intros. ring. Qed.

(** 16. Q multiplication compatible with Qeq *)
Lemma Q_ring_mul_compat : forall x x' y y' : Q,
  x == x' -> y == y' -> x * y == x' * y'.
Proof.
  intros x x' y y' Hx Hy.
  apply Qmult_comp; assumption.
Qed.

(** 17. Q ring instance *)
Definition Q_ring : Ring := mkRing
  Q_add_group
  Qmult
  1
  Q_ring_mul_compat
  Q_ring_mul_assoc
  Q_ring_mul_comm
  Q_ring_one_l
  Q_ring_distrib.

(* ================================================================= *)
(*      PART IV: Q FIELD INSTANCE (3 Qed)                              *)
(* ================================================================= *)

(** 18. Q multiplicative inverse of nonzero: x * /x = 1 *)
Lemma Q_field_inv_r : forall x : Q,
  ~ (x == 0) ->
  x * / x == 1.
Proof.
  intros x Hx.
  apply Qmult_inv_r. exact Hx.
Qed.

(** 19. Q inverse compatible with Qeq *)
Lemma Q_field_inv_compat : forall x x' : Q,
  x == x' -> / x == / x'.
Proof.
  intros x x' H.
  apply Qinv_comp. exact H.
Qed.

(** 20. Q field instance *)
Definition Q_field : Field := mkField
  Q_ring
  Qinv
  Q_field_inv_compat
  Q_field_inv_r.

(* ================================================================= *)
(*      PART V: DERIVED FIELD PROPERTIES (2 Qed)                       *)
(* ================================================================= *)

(** 21. Left multiplicative inverse: /x * x = 1 (for nonzero x) *)
Lemma f_inv_l : forall (F : Field) (x : g_carrier (r_add_group (f_ring F))),
  ~ g_eq (r_add_group (f_ring F)) x (g_id (r_add_group (f_ring F))) ->
  g_eq (r_add_group (f_ring F)) (r_mul (f_ring F) (f_inv F x) x) (r_one (f_ring F)).
Proof.
  intros F x Hx.
  apply (g_eq_trans (r_add_group (f_ring F))) with
    (y := r_mul (f_ring F) x (f_inv F x)).
  - apply r_mul_comm.
  - apply f_inv_r. exact Hx.
Qed.

(** 22. Multiplicative cancellation: x * y = x * z -> x <> 0 -> y = z *)
Lemma f_mul_cancel_l : forall (F : Field) (x y z : g_carrier (r_add_group (f_ring F))),
  ~ g_eq (r_add_group (f_ring F)) x (g_id (r_add_group (f_ring F))) ->
  g_eq (r_add_group (f_ring F)) (r_mul (f_ring F) x y) (r_mul (f_ring F) x z) ->
  g_eq (r_add_group (f_ring F)) y z.
Proof.
  intros F x y z Hx Hxy.
  set (G := r_add_group (f_ring F)).
  set (R := f_ring F).
  set (xi := f_inv F x).
  (* y = 1*y = (/x * x)*y = /x * (x*y) = /x * (x*z) = (/x * x)*z = 1*z = z *)
  apply (g_eq_trans G) with (y := r_mul R (r_one R) y).
  - apply g_eq_sym. apply r_mul_one_l.
  - apply (g_eq_trans G) with (y := r_mul R (r_mul R xi x) y).
    + apply (r_mul_compat R).
      * apply g_eq_sym. apply f_inv_l. exact Hx.
      * apply g_eq_refl.
    + apply (g_eq_trans G) with (y := r_mul R xi (r_mul R x y)).
      * apply r_mul_assoc.
      * apply (g_eq_trans G) with (y := r_mul R xi (r_mul R x z)).
        -- apply (r_mul_compat R).
           ++ apply g_eq_refl.
           ++ exact Hxy.
        -- apply (g_eq_trans G) with (y := r_mul R (r_mul R xi x) z).
           ++ apply g_eq_sym. apply r_mul_assoc.
           ++ apply (g_eq_trans G) with (y := r_mul R (r_one R) z).
              ** apply (r_mul_compat R).
                 --- apply f_inv_l. exact Hx.
                 --- apply g_eq_refl.
              ** apply r_mul_one_l.
Qed.

(* ================================================================= *)
(*  Summary: 20 Qed, 0 Admitted, 0 axioms                             *)
(*    7 derived ring properties:                                       *)
(*      r_mul_one_r, r_mul_zero_l, r_mul_zero_r,                       *)
(*      r_mul_neg_l, r_distrib_r, r_mul_neg_r, r_mul_neg_neg           *)
(*    4 Z ring helpers: Z_ring_mul_assoc, Z_ring_mul_comm,             *)
(*      Z_ring_one_l, Z_ring_distrib (+Z_ring Definition)              *)
(*    5 Q ring helpers: Q_ring_mul_assoc, Q_ring_mul_comm,             *)
(*      Q_ring_one_l, Q_ring_distrib, Q_ring_mul_compat (+Q_ring Def)  *)
(*    2 Q field: Q_field_inv_r, Q_field_inv_compat (+Q_field Def)      *)
(*    2 derived field: f_inv_l, f_mul_cancel_l                         *)
(* ================================================================= *)
