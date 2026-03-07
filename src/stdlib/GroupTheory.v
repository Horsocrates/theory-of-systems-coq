(** * GroupTheory.v — Groups as ToS Systems

    Theory of Systems — Verified Standard Library (Tier 2b)

    Elements: group members
    Roles:    g_id -> Identity, generators -> Generators
    Rules:    associativity + identity + inverse (constitution = group axioms)
    Status:   identity | generator | general_member

    Connection: SystemMorphism.v (homomorphism = morphism preserving group)
    Connection: L5Resolution.v (ordered groups)

    STATUS: 22 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: 2026
*)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lqa.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Close Scope Z_scope.
Open Scope Q_scope.

(* ================================================================= *)
(*  Group: a set with an associative binary operation, identity,      *)
(*  and inverses. Uses custom equality g_eq to support setoid groups. *)
(* ================================================================= *)

Record Group := mkGroup {
  g_carrier : Type;
  g_eq : g_carrier -> g_carrier -> Prop;
  g_op : g_carrier -> g_carrier -> g_carrier;
  g_id : g_carrier;
  g_inv : g_carrier -> g_carrier;
  (* Equivalence *)
  g_eq_refl : forall x, g_eq x x;
  g_eq_sym : forall x y, g_eq x y -> g_eq y x;
  g_eq_trans : forall x y z, g_eq x y -> g_eq y z -> g_eq x z;
  (* Compatibility *)
  g_op_compat : forall x x' y y',
    g_eq x x' -> g_eq y y' -> g_eq (g_op x y) (g_op x' y');
  g_inv_compat : forall x x',
    g_eq x x' -> g_eq (g_inv x) (g_inv x');
  (* Group axioms *)
  g_assoc : forall x y z,
    g_eq (g_op (g_op x y) z) (g_op x (g_op y z));
  g_id_l : forall x, g_eq (g_op g_id x) x;
  g_inv_l : forall x, g_eq (g_op (g_inv x) x) g_id;
}.

(* ================================================================= *)
(*            PART I: DERIVED PROPERTIES (9 Qed)                      *)
(* ================================================================= *)

(** Right inverse: x * inv(x) = e *)
Lemma g_inv_r : forall (G : Group) (x : g_carrier G),
  g_eq G (g_op G x (g_inv G x)) (g_id G).
Proof.
  intros G x.
  (* x * inv(x)
     = e * (x * inv(x))                           by id_l^{-1}
     = (inv(inv(x)) * inv(x)) * (x * inv(x))      by inv_l on inv(x)
     = inv(inv(x)) * (inv(x) * (x * inv(x)))      by assoc
     = inv(inv(x)) * ((inv(x) * x) * inv(x))      by assoc
     = inv(inv(x)) * (e * inv(x))                 by inv_l
     = inv(inv(x)) * inv(x)                       by id_l
     = e                                           by inv_l *)
  apply (g_eq_trans G) with (y := g_op G (g_id G) (g_op G x (g_inv G x))).
  - apply g_eq_sym. apply g_id_l.
  - apply (g_eq_trans G) with
      (y := g_op G (g_op G (g_inv G (g_inv G x)) (g_inv G x))
                    (g_op G x (g_inv G x))).
    + apply g_op_compat.
      * apply g_eq_sym. apply g_inv_l.
      * apply g_eq_refl.
    + apply (g_eq_trans G) with
        (y := g_op G (g_inv G (g_inv G x))
                     (g_op G (g_inv G x) (g_op G x (g_inv G x)))).
      * apply g_assoc.
      * apply (g_eq_trans G) with
          (y := g_op G (g_inv G (g_inv G x))
                       (g_op G (g_op G (g_inv G x) x) (g_inv G x))).
        -- apply g_op_compat.
           ++ apply g_eq_refl.
           ++ apply g_eq_sym. apply g_assoc.
        -- apply (g_eq_trans G) with
             (y := g_op G (g_inv G (g_inv G x))
                          (g_op G (g_id G) (g_inv G x))).
           ++ apply g_op_compat.
              ** apply g_eq_refl.
              ** apply g_op_compat.
                 --- apply g_inv_l.
                 --- apply g_eq_refl.
           ++ apply (g_eq_trans G) with
                (y := g_op G (g_inv G (g_inv G x)) (g_inv G x)).
              ** apply g_op_compat.
                 --- apply g_eq_refl.
                 --- apply g_id_l.
              ** apply g_inv_l.
Qed.

(** Right identity: x * e = x *)
Lemma g_id_r : forall (G : Group) (x : g_carrier G),
  g_eq G (g_op G x (g_id G)) x.
Proof.
  intros G x.
  (* x * e = x * (inv(x) * x) = (x * inv(x)) * x = e * x = x *)
  apply (g_eq_trans G) with (y := g_op G x (g_op G (g_inv G x) x)).
  - apply g_op_compat.
    + apply g_eq_refl.
    + apply g_eq_sym. apply g_inv_l.
  - apply (g_eq_trans G) with (y := g_op G (g_op G x (g_inv G x)) x).
    + apply g_eq_sym. apply g_assoc.
    + apply (g_eq_trans G) with (y := g_op G (g_id G) x).
      * apply g_op_compat.
        -- apply g_inv_r.
        -- apply g_eq_refl.
      * apply g_id_l.
Qed.

(** Inverse of identity: inv(e) = e *)
Lemma g_inv_id : forall (G : Group),
  g_eq G (g_inv G (g_id G)) (g_id G).
Proof.
  intros G.
  (* inv(e) * e = e  (by inv_l)
     inv(e) * e = inv(e)  (by id_r)
     so inv(e) = e *)
  apply (g_eq_trans G) with (y := g_op G (g_inv G (g_id G)) (g_id G)).
  - apply g_eq_sym. apply g_id_r.
  - apply g_inv_l.
Qed.

(** Double inverse: inv(inv(x)) = x *)
Lemma g_inv_inv : forall (G : Group) (x : g_carrier G),
  g_eq G (g_inv G (g_inv G x)) x.
Proof.
  intros G x.
  (* inv(inv(x)) = inv(inv(x)) * e
                  = inv(inv(x)) * (inv(x) * x)
                  = (inv(inv(x)) * inv(x)) * x
                  = e * x = x *)
  apply (g_eq_trans G) with
    (y := g_op G (g_inv G (g_inv G x)) (g_id G)).
  - apply g_eq_sym. apply g_id_r.
  - apply (g_eq_trans G) with
      (y := g_op G (g_inv G (g_inv G x)) (g_op G (g_inv G x) x)).
    + apply g_op_compat.
      * apply g_eq_refl.
      * apply g_eq_sym. apply g_inv_l.
    + apply (g_eq_trans G) with
        (y := g_op G (g_op G (g_inv G (g_inv G x)) (g_inv G x)) x).
      * apply g_eq_sym. apply g_assoc.
      * apply (g_eq_trans G) with (y := g_op G (g_id G) x).
        -- apply g_op_compat.
           ++ apply g_inv_l.
           ++ apply g_eq_refl.
        -- apply g_id_l.
Qed.

(** Left cancellation: a*x = a*y -> x = y *)
Lemma g_cancel_l : forall (G : Group) (a x y : g_carrier G),
  g_eq G (g_op G a x) (g_op G a y) -> g_eq G x y.
Proof.
  intros G a x y H.
  (* x = e * x = (inv(a) * a) * x = inv(a) * (a * x)
       = inv(a) * (a * y) = (inv(a) * a) * y = e * y = y *)
  apply (g_eq_trans G) with (y := g_op G (g_id G) x).
  - apply g_eq_sym. apply g_id_l.
  - apply (g_eq_trans G) with
      (y := g_op G (g_op G (g_inv G a) a) x).
    + apply g_op_compat.
      * apply g_eq_sym. apply g_inv_l.
      * apply g_eq_refl.
    + apply (g_eq_trans G) with
        (y := g_op G (g_inv G a) (g_op G a x)).
      * apply g_assoc.
      * apply (g_eq_trans G) with
          (y := g_op G (g_inv G a) (g_op G a y)).
        -- apply g_op_compat.
           ++ apply g_eq_refl.
           ++ exact H.
        -- apply (g_eq_trans G) with
             (y := g_op G (g_op G (g_inv G a) a) y).
           ++ apply g_eq_sym. apply g_assoc.
           ++ apply (g_eq_trans G) with (y := g_op G (g_id G) y).
              ** apply g_op_compat.
                 --- apply g_inv_l.
                 --- apply g_eq_refl.
              ** apply g_id_l.
Qed.

(** Right cancellation: x*a = y*a -> x = y *)
Lemma g_cancel_r : forall (G : Group) (a x y : g_carrier G),
  g_eq G (g_op G x a) (g_op G y a) -> g_eq G x y.
Proof.
  intros G a x y H.
  apply (g_eq_trans G) with (y := g_op G x (g_id G)).
  - apply g_eq_sym. apply g_id_r.
  - apply (g_eq_trans G) with
      (y := g_op G x (g_op G a (g_inv G a))).
    + apply g_op_compat.
      * apply g_eq_refl.
      * apply g_eq_sym. apply g_inv_r.
    + apply (g_eq_trans G) with
        (y := g_op G (g_op G x a) (g_inv G a)).
      * apply g_eq_sym. apply g_assoc.
      * apply (g_eq_trans G) with
          (y := g_op G (g_op G y a) (g_inv G a)).
        -- apply g_op_compat.
           ++ exact H.
           ++ apply g_eq_refl.
        -- apply (g_eq_trans G) with
             (y := g_op G y (g_op G a (g_inv G a))).
           ++ apply g_assoc.
           ++ apply (g_eq_trans G) with (y := g_op G y (g_id G)).
              ** apply g_op_compat.
                 --- apply g_eq_refl.
                 --- apply g_inv_r.
              ** apply g_id_r.
Qed.

(** Inverse of product: inv(x*y) = inv(y) * inv(x) *)
Lemma g_inv_op : forall (G : Group) (x y : g_carrier G),
  g_eq G (g_inv G (g_op G x y)) (g_op G (g_inv G y) (g_inv G x)).
Proof.
  intros G x y.
  (* Strategy: show (x*y) * (inv(y)*inv(x)) = e, then cancel_l *)
  apply (g_cancel_l G (g_op G x y)).
  apply (g_eq_trans G) with (y := g_id G).
  - apply g_inv_r.
  - apply g_eq_sym.
    (* Goal: (x*y) * (inv(y)*inv(x)) = e *)
    (* Chain: = x*(y*(inv(y)*inv(x))) = x*((y*inv(y))*inv(x)) = x*(e*inv(x)) = x*inv(x) = e *)
    apply (g_eq_trans G) with
      (y := g_op G x (g_op G y (g_op G (g_inv G y) (g_inv G x)))).
    + apply g_assoc.
    + apply (g_eq_trans G) with
        (y := g_op G x (g_op G (g_op G y (g_inv G y)) (g_inv G x))).
      * apply g_op_compat.
        -- apply g_eq_refl.
        -- apply g_eq_sym. apply g_assoc.
      * apply (g_eq_trans G) with
          (y := g_op G x (g_op G (g_id G) (g_inv G x))).
        -- apply g_op_compat.
           ++ apply g_eq_refl.
           ++ apply g_op_compat.
              ** apply g_inv_r.
              ** apply g_eq_refl.
        -- apply (g_eq_trans G) with
             (y := g_op G x (g_inv G x)).
           ++ apply g_op_compat.
              ** apply g_eq_refl.
              ** apply g_id_l.
           ++ apply g_inv_r.
Qed.

(** Uniqueness of identity: if e' * x = x then e' = e *)
Lemma g_unique_id : forall (G : Group) (e' x : g_carrier G),
  g_eq G (g_op G e' x) x -> g_eq G e' (g_id G).
Proof.
  intros G e' x H.
  apply (g_cancel_r G x).
  apply (g_eq_trans G) with (y := x).
  - exact H.
  - apply g_eq_sym. apply g_id_l.
Qed.

(** Uniqueness of inverse: if y * x = e then y = inv(x) *)
Lemma g_unique_inv : forall (G : Group) (x y : g_carrier G),
  g_eq G (g_op G y x) (g_id G) -> g_eq G y (g_inv G x).
Proof.
  intros G x y H.
  apply (g_cancel_r G x).
  apply (g_eq_trans G) with (y := g_id G).
  - exact H.
  - apply g_eq_sym. apply g_inv_l.
Qed.

(* ================================================================= *)
(*            PART II: SUBGROUP (2 Qed)                               *)
(* ================================================================= *)

Definition is_subgroup (G : Group) (S : g_carrier G -> Prop) : Prop :=
  S (g_id G) /\
  (forall x, S x -> S (g_inv G x)) /\
  (forall x y, S x -> S y -> S (g_op G x y)).

Lemma subgroup_has_id : forall (G : Group) (S : g_carrier G -> Prop),
  is_subgroup G S -> S (g_id G).
Proof.
  intros G S [Hid _]. exact Hid.
Qed.

Lemma subgroup_closed_inv : forall (G : Group) (S : g_carrier G -> Prop) (x : g_carrier G),
  is_subgroup G S -> S x -> S (g_inv G x).
Proof.
  intros G S x [_ [Hinv _]] Hx. apply Hinv. exact Hx.
Qed.

(* ================================================================= *)
(*            PART III: HOMOMORPHISM (3 Qed)                          *)
(* ================================================================= *)

Definition is_homomorphism (G1 G2 : Group)
  (f : g_carrier G1 -> g_carrier G2) : Prop :=
  (forall x y, g_eq G2 (f (g_op G1 x y)) (g_op G2 (f x) (f y))) /\
  (forall x x', g_eq G1 x x' -> g_eq G2 (f x) (f x')).

(** A homomorphism preserves identity *)
Lemma hom_preserves_id : forall (G1 G2 : Group)
  (f : g_carrier G1 -> g_carrier G2),
  is_homomorphism G1 G2 f ->
  g_eq G2 (f (g_id G1)) (g_id G2).
Proof.
  intros G1 G2 f [Hop Hcompat].
  (* f(e) * f(e) = f(e * e) = f(e) = e * f(e). Cancel_l gives f(e) = e. *)
  apply (g_cancel_l G2 (f (g_id G1))).
  apply (g_eq_trans G2) with (y := f (g_op G1 (g_id G1) (g_id G1))).
  - apply g_eq_sym. apply Hop.
  - apply (g_eq_trans G2) with (y := f (g_id G1)).
    + apply Hcompat. apply g_id_l.
    + apply g_eq_sym. apply g_id_r.
Qed.

(** A homomorphism preserves inverses *)
Lemma hom_preserves_inv : forall (G1 G2 : Group)
  (f : g_carrier G1 -> g_carrier G2) (x : g_carrier G1),
  is_homomorphism G1 G2 f ->
  g_eq G2 (f (g_inv G1 x)) (g_inv G2 (f x)).
Proof.
  intros G1 G2 f x [Hop Hcompat].
  (* f(inv(x)) * f(x) = f(inv(x) * x) = f(e) = e_2.
     By unique_inv: f(inv(x)) = inv(f(x)). *)
  apply (g_unique_inv G2 (f x)).
  apply (g_eq_trans G2) with (y := f (g_op G1 (g_inv G1 x) x)).
  - apply g_eq_sym. apply Hop.
  - apply (g_eq_trans G2) with (y := f (g_id G1)).
    + apply Hcompat. apply g_inv_l.
    + apply hom_preserves_id. split; assumption.
Qed.

(** Composition of homomorphisms is a homomorphism *)
Lemma hom_compose : forall (G1 G2 G3 : Group)
  (f : g_carrier G1 -> g_carrier G2)
  (g : g_carrier G2 -> g_carrier G3),
  is_homomorphism G1 G2 f ->
  is_homomorphism G2 G3 g ->
  is_homomorphism G1 G3 (fun x => g (f x)).
Proof.
  intros G1 G2 G3 f g [Hf_op Hf_compat] [Hg_op Hg_compat].
  split.
  - intros x y.
    (* g(f(x*y)) = g(f(x) * f(y)) = g(f(x)) * g(f(y)) *)
    apply (g_eq_trans G3) with (y := g (g_op G2 (f x) (f y))).
    + apply Hg_compat. apply Hf_op.
    + apply Hg_op.
  - intros x x' Hxx'.
    apply Hg_compat. apply Hf_compat. exact Hxx'.
Qed.

(* ================================================================= *)
(*            PART IV: Z INSTANCE (4 helper Qed + Definition)         *)
(* ================================================================= *)

Lemma Z_add_assoc_eq : forall x y z : Z,
  ((x + y) + z)%Z = (x + (y + z))%Z.
Proof. intros. lia. Qed.

Lemma Z_add_0_l_eq : forall x : Z, (0 + x)%Z = x.
Proof. intros. lia. Qed.

Lemma Z_opp_l_eq : forall x : Z, (- x + x)%Z = 0%Z.
Proof. intros. lia. Qed.

Lemma Z_opp_compat_eq : forall x x' : Z, x = x' -> (- x)%Z = (- x')%Z.
Proof. intros. subst. reflexivity. Qed.

Definition Z_add_group : Group := mkGroup
  Z
  (@eq Z)
  Z.add
  0%Z
  Z.opp
  (@eq_refl Z)
  (@eq_sym Z)
  (@eq_trans Z)
  (fun x x' y y' H1 H2 => f_equal2 Z.add H1 H2)
  Z_opp_compat_eq
  Z_add_assoc_eq
  Z_add_0_l_eq
  Z_opp_l_eq.

(* ================================================================= *)
(*            PART V: Q INSTANCE (4 helper Qed + Definition)          *)
(* ================================================================= *)

Lemma Q_add_assoc_qeq : forall x y z : Q,
  (x + y) + z == x + (y + z).
Proof. intros. ring. Qed.

Lemma Q_add_0_l_qeq : forall x : Q,
  0 + x == x.
Proof. intros. ring. Qed.

Lemma Q_opp_l_qeq : forall x : Q,
  (- x) + x == 0.
Proof. intros. ring. Qed.

Lemma Q_opp_compat_qeq : forall x x' : Q,
  x == x' -> (- x) == (- x').
Proof. intros x x' H. apply Qopp_comp. exact H. Qed.

Definition Q_add_group : Group := mkGroup
  Q
  Qeq
  Qplus
  0
  Qopp
  Qeq_refl
  (fun x y => Qeq_sym x y)
  (fun x y z => Qeq_trans x y z)
  (fun x x' y y' (H1 : x == x') (H2 : y == y') => Qplus_comp x x' H1 y y' H2)
  Q_opp_compat_qeq
  Q_add_assoc_qeq
  Q_add_0_l_qeq
  Q_opp_l_qeq.

(* ================================================================= *)
(*  Summary: 22 Qed, 0 Admitted                                       *)
(*    9 derived properties: g_inv_r, g_id_r, g_inv_id, g_inv_inv,     *)
(*      g_cancel_l, g_cancel_r, g_inv_op, g_unique_id, g_unique_inv   *)
(*    2 subgroup: subgroup_has_id, subgroup_closed_inv                 *)
(*    3 homomorphism: hom_preserves_id, hom_preserves_inv, hom_compose *)
(*    4 Z helpers: Z_add_assoc_eq, Z_add_0_l_eq, Z_opp_l_eq,          *)
(*      Z_opp_compat_eq                                                *)
(*    4 Q helpers: Q_add_assoc_qeq, Q_add_0_l_qeq, Q_opp_l_qeq,      *)
(*      Q_opp_compat_qeq                                               *)
(* ================================================================= *)
