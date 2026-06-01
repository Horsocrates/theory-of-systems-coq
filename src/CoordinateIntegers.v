(** * CoordinateIntegers.v — Integers as Coordinate Differences (ToS System)
    Elements: pairs of step-counts (nat) on the two sides of an origin
    Roles:    fd_pos = steps on the positive side, fd_neg = steps on the negative side;
              the integer denoted is their coordinate difference
    Rules:    formal difference  a + d = b + c  (when does (a,b) denote the same
              integer as (c,d)); isomorphism to standard Z; negation = orientation
              flip; the sign rule (-a)(-b)=ab as a theorem about FormalDiff

    === E/R/R разбор (генеративно Rules -> Roles -> Elements) ===
      Rules    : тождество разностей a+d=b+c — когда два описания дают ОДНО целое;
                 изоморфизм с Z; отрицание = переворот ориентации; правило знаков.
      Roles    : целое = ДВУСТОРОННЯЯ позиция — место (величина) + ориентация (знак);
                 «положительная/отрицательная сторона опоры».
      Elements : счёты шагов (nat) по двум сторонам опоры; конечны (L1+P4).
    Хорошая сформированность: однозначно (счёт = Element, целое/знак = Role,
    разность = Rule); P1 — нуль-опора (граница отсчёта) <> нуль-счёт (величина 0),
    уровни не схлопываются.
    ДИАГНОСТИКА: НЕТ «отрицательного существования» — есть отрицательная СТОРОНА.
    Знак минуса — координатная РОЛЬ (ориентация), не объект и не «нехватка»; не
    смешивать знак минуса / логическое не-P / алгебраическую обратимость (три разные
    вещи). Целое — роль над натуральными счётами, не самостоятельный объект-элемент.

    Status:   F-16 — gives Part III, Ch.1 (целые числа) its OWN formal anchor.
              Previously ToS leaned on stdlib Z without a coordinate construction;
              this file builds the construction and proves it isomorphic to Z.
    STATUS: 13 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: May 2026
*)

From Stdlib Require Import ZArith Lia.

Open Scope Z_scope.

(* ===================================================================== *)
(*  Elements & Roles                                                     *)
(*  An integer is described by a pair of step-counts: how many steps on  *)
(*  the positive side, how many on the negative side. Many descriptions  *)
(*  denote the same integer (3-left-then-5-right = 2-right).             *)
(* ===================================================================== *)

Record FormalDiff := mkFD { fd_pos : nat ; fd_neg : nat }.

(** The integer a FormalDiff denotes: (steps on +) minus (steps on −). *)
Definition fd_to_Z (x : FormalDiff) : Z :=
  Z.of_nat (fd_pos x) - Z.of_nat (fd_neg x).

(** Two coordinate descriptions denote the same integer iff a + d = b + c. *)
Definition fd_equiv (x y : FormalDiff) : Prop :=
  (fd_pos x + fd_neg y = fd_pos y + fd_neg x)%nat.

(* ===================================================================== *)
(*  Rules I — fd_equiv is an equivalence relation                        *)
(* ===================================================================== *)

Lemma fd_equiv_refl : forall x, fd_equiv x x.
Proof. intros x. unfold fd_equiv. lia. Qed.

Lemma fd_equiv_sym : forall x y, fd_equiv x y -> fd_equiv y x.
Proof. intros x y H. unfold fd_equiv in *. lia. Qed.

Lemma fd_equiv_trans :
  forall x y z, fd_equiv x y -> fd_equiv y z -> fd_equiv x z.
Proof. intros x y z Hxy Hyz. unfold fd_equiv in *. lia. Qed.

(* ===================================================================== *)
(*  Rules II — isomorphism with standard Z                               *)
(* ===================================================================== *)

(** fd_equiv is exactly "denotes the same integer". *)
Lemma fd_equiv_iff_Z : forall x y, fd_equiv x y <-> fd_to_Z x = fd_to_Z y.
Proof. intros x y. unfold fd_equiv, fd_to_Z. lia. Qed.

(** Canonical section: every integer is denoted by some FormalDiff. *)
Definition fd_of_Z (z : Z) : FormalDiff :=
  match z with
  | Z0     => mkFD 0%nat 0%nat
  | Zpos p => mkFD (Pos.to_nat p) 0%nat
  | Zneg p => mkFD 0%nat (Pos.to_nat p)
  end.

(** fd_to_Z is onto: it inverts fd_of_Z. Hence Z is covered exactly. *)
Lemma fd_to_of_Z : forall z, fd_to_Z (fd_of_Z z) = z.
Proof.
  intros z. destruct z as [| p | p]; unfold fd_to_Z, fd_of_Z; cbn [fd_pos fd_neg].
  - reflexivity.
  - rewrite positive_nat_Z. lia.
  - rewrite positive_nat_Z. lia.
Qed.

(* ===================================================================== *)
(*  Rules III — arithmetic carried by the coordinate structure           *)
(* ===================================================================== *)

(** Addition: add step-counts side-by-side. Maps to Z addition. *)
Definition fd_add (x y : FormalDiff) : FormalDiff :=
  mkFD (fd_pos x + fd_pos y)%nat (fd_neg x + fd_neg y)%nat.

Lemma fd_add_to_Z : forall x y, fd_to_Z (fd_add x y) = fd_to_Z x + fd_to_Z y.
Proof. intros x y. unfold fd_to_Z, fd_add. cbn [fd_pos fd_neg]. lia. Qed.

(** Negation is the orientation flip: swap the two sides. Maps to Z.opp. *)
Definition fd_opp (x : FormalDiff) : FormalDiff :=
  mkFD (fd_neg x) (fd_pos x).

Lemma fd_opp_to_Z : forall x, fd_to_Z (fd_opp x) = - fd_to_Z x.
Proof. intros x. unfold fd_to_Z, fd_opp. cbn [fd_pos fd_neg]. lia. Qed.

(** The origin denotes 0. *)
Definition fd_zero := mkFD 0%nat 0%nat.

Lemma fd_zero_to_Z : fd_to_Z fd_zero = 0.
Proof. reflexivity. Qed.

(** Multiplication via the coordinate structure; maps to Z multiplication. *)
Definition fd_mul (x y : FormalDiff) : FormalDiff :=
  mkFD (fd_pos x * fd_pos y + fd_neg x * fd_neg y)%nat
       (fd_pos x * fd_neg y + fd_neg x * fd_pos y)%nat.

Lemma fd_mul_to_Z : forall x y, fd_to_Z (fd_mul x y) = fd_to_Z x * fd_to_Z y.
Proof.
  intros x y. unfold fd_to_Z, fd_mul. cbn [fd_pos fd_neg].
  rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul. ring.
Qed.

(** The sign rule, as a theorem: the product of two negative-side
    coordinates lands on the positive side. (−a)(−b) = a·b. *)
Corollary fd_sign_rule : forall a b : nat,
  fd_to_Z (fd_mul (mkFD 0%nat a) (mkFD 0%nat b)) = Z.of_nat a * Z.of_nat b.
Proof.
  intros a b. rewrite fd_mul_to_Z. unfold fd_to_Z. cbn [fd_pos fd_neg]. ring.
Qed.

(* ===================================================================== *)
(*  Rules IV — group laws (up to fd_equiv) and orientation               *)
(* ===================================================================== *)

Lemma fd_add_zero_l : forall x, fd_equiv (fd_add fd_zero x) x.
Proof. intros x. unfold fd_equiv, fd_add, fd_zero. cbn [fd_pos fd_neg]. lia. Qed.

Lemma fd_add_comm : forall x y, fd_equiv (fd_add x y) (fd_add y x).
Proof. intros x y. unfold fd_equiv, fd_add. cbn [fd_pos fd_neg]. lia. Qed.

(** Flipping orientation twice is the identity (two-sidedness is symmetric). *)
Lemma fd_opp_involutive : forall x, fd_opp (fd_opp x) = x.
Proof. intros x. destruct x. reflexivity. Qed.
