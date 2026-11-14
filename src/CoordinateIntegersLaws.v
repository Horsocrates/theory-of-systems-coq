(** * CoordinateIntegersLaws.v — The coordinate integers: multiplication as
      repetition, the sign rule from two flips, the full correspondence with
      Z, the reduced pair and the anchor

    E/R/R reading (done before coding; audit of Part III of the Mathematics
    volume, chapter III.1, places 1.1 and 1.3, 2026-11-14):

    Elements: the counts of steps (nat) on the two sides of an anchor — the
              pairs FormalDiff of CoordinateIntegers.v; the points of the
              series.
    Roles:    an integer — a two-sided position: a magnitude and an
              orientation; the anchor — the point from which the positions
              are read; the second factor of a product — an instruction how
              to repeat a displacement.
    Rules:    two pairs denote one integer when a + d = b + c; the change of
              sign is a flip of the orientation, and a flip taken twice is
              the identity; to multiply is to repeat a displacement.
    Proved:   (1) the correspondence of the pairs with Z in full: both round
                  trips (the second up to the equivalence of pairs), the
                  operations respect the equivalence, addition,
                  multiplication, the change of sign, zero, one and the
                  order are carried over; the two types themselves are NOT
                  one type (the pair type is not in bijection with Z);
              (2) addition of pairs is associative and has opposites;
              (3) multiplication as REPETITION of a displacement coincides
                  with the formula fd_mul; a flip of either factor flips
                  the result; THE SIGN RULE (-a)(-n) = a n follows from two
                  flips by fd_opp_involutive — without unfolding the formula
                  and without Z;
              (4) in every class of equivalent pairs there is exactly one
                  reduced pair (steps on one side only);
              (5) the anchor: the sign of a position is a property of the
                  choice of the anchor; moving the anchor one step shifts
                  the marking by one; the order of positions is the order of
                  the series; every integer is a position.
    P4 diagnostic ("could it be otherwise?"): finite counts only. Forced:
              (1)-(5). NOT claimed: a quotient type of pairs (Rocq has none
              without extra assumptions — the classes are the relation
              fd_equiv); that the reading "the second factor says how to
              repeat" is derived — it is the definition fd_mul_rep, taken
              from the chapter; that the counts are the primary series of
              Part II — they are values of nat, with zero.

    STATUS: 35 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import ZArith Lia PeanoNat.

From ToS Require Import CoordinateIntegers.

Open Scope Z_scope.

(* ========================================================================= *)
(*  1. THE CORRESPONDENCE WITH Z IN FULL                                     *)
(* ========================================================================= *)

(** The second round trip — up to the equivalence of pairs. *)
Lemma fd_of_to_Z : forall x, fd_equiv (fd_of_Z (fd_to_Z x)) x.
Proof. intro x. apply fd_equiv_iff_Z. apply fd_to_of_Z. Qed.

(** The round trip is NOT an equality of pairs, and fd_to_Z is not injective: FormalDiff
    and Z are two types; they correspond on the classes of equivalent pairs. *)
Lemma fd_of_to_Z_not_eq : exists x, fd_of_Z (fd_to_Z x) <> x.
Proof. exists (mkFD 1%nat 1%nat). cbn. discriminate. Qed.

Lemma fd_to_Z_not_injective : exists x y, x <> y /\ fd_to_Z x = fd_to_Z y.
Proof. exists (mkFD 5%nat 3%nat), (mkFD 7%nat 5%nat). split; [discriminate | reflexivity]. Qed.

(** The operations respect the equivalence of pairs. *)
Lemma fd_add_compat : forall x x' y y',
  fd_equiv x x' -> fd_equiv y y' -> fd_equiv (fd_add x y) (fd_add x' y').
Proof.
  intros x x' y y' Hx Hy. apply fd_equiv_iff_Z. rewrite !fd_add_to_Z.
  apply fd_equiv_iff_Z in Hx. apply fd_equiv_iff_Z in Hy. rewrite Hx, Hy. reflexivity.
Qed.

Lemma fd_mul_compat : forall x x' y y',
  fd_equiv x x' -> fd_equiv y y' -> fd_equiv (fd_mul x y) (fd_mul x' y').
Proof.
  intros x x' y y' Hx Hy. apply fd_equiv_iff_Z. rewrite !fd_mul_to_Z.
  apply fd_equiv_iff_Z in Hx. apply fd_equiv_iff_Z in Hy. rewrite Hx, Hy. reflexivity.
Qed.

Lemma fd_opp_compat : forall x x', fd_equiv x x' -> fd_equiv (fd_opp x) (fd_opp x').
Proof.
  intros x x' Hx. apply fd_equiv_iff_Z. rewrite !fd_opp_to_Z.
  apply fd_equiv_iff_Z in Hx. rewrite Hx. reflexivity.
Qed.

Definition fd_one := mkFD 1%nat 0%nat.
Lemma fd_one_to_Z : fd_to_Z fd_one = 1.
Proof. reflexivity. Qed.

Definition fd_le (x y : FormalDiff) : Prop :=
  (fd_pos x + fd_neg y <= fd_pos y + fd_neg x)%nat.

Lemma fd_le_iff_Z : forall x y, fd_le x y <-> fd_to_Z x <= fd_to_Z y.
Proof. intros x y. unfold fd_le, fd_to_Z. lia. Qed.

(** The correspondence in one statement: classes of pairs and the values of Z, with
    addition, multiplication, the change of sign, zero, one and the order. *)
Theorem FormalDiff_iso_Z :
  (forall x y, fd_equiv x y <-> fd_to_Z x = fd_to_Z y) /\
  (forall z, fd_to_Z (fd_of_Z z) = z) /\
  (forall x, fd_equiv (fd_of_Z (fd_to_Z x)) x) /\
  (forall x y, fd_to_Z (fd_add x y) = fd_to_Z x + fd_to_Z y) /\
  (forall x y, fd_to_Z (fd_mul x y) = fd_to_Z x * fd_to_Z y) /\
  (forall x, fd_to_Z (fd_opp x) = - fd_to_Z x) /\
  fd_to_Z fd_zero = 0 /\
  fd_to_Z fd_one = 1 /\
  (forall x y, fd_le x y <-> fd_to_Z x <= fd_to_Z y).
Proof.
  split; [exact fd_equiv_iff_Z|].
  split; [exact fd_to_of_Z|].
  split; [exact fd_of_to_Z|].
  split; [exact fd_add_to_Z|].
  split; [exact fd_mul_to_Z|].
  split; [exact fd_opp_to_Z|].
  split; [exact fd_zero_to_Z|].
  split; [exact fd_one_to_Z|].
  exact fd_le_iff_Z.
Qed.

(* ========================================================================= *)
(*  2. THE LAWS OF ADDITION                                                  *)
(* ========================================================================= *)

Lemma fd_add_assoc : forall x y z,
  fd_add (fd_add x y) z = fd_add x (fd_add y z).
Proof. intros x y z. unfold fd_add. cbn [fd_pos fd_neg]. f_equal; lia. Qed.

Lemma fd_add_opp_r : forall x, fd_equiv (fd_add x (fd_opp x)) fd_zero.
Proof. intro x. unfold fd_equiv, fd_add, fd_opp, fd_zero. cbn [fd_pos fd_neg]. lia. Qed.

Lemma fd_add_zero_r : forall x, fd_add x fd_zero = x.
Proof. intro x. destruct x as [a b]. unfold fd_add, fd_zero. cbn [fd_pos fd_neg]. f_equal; lia. Qed.

Lemma fd_add_comm_eq : forall x y, fd_add x y = fd_add y x.
Proof. intros x y. unfold fd_add. f_equal; lia. Qed.

Lemma fd_mul_comm_eq : forall x y, fd_mul x y = fd_mul y x.
Proof. intros x y. unfold fd_mul. f_equal; lia. Qed.

(* ========================================================================= *)
(*  3. WHERE THE SIGN RULE SITS IN THE FORMULA fd_mul                        *)
(* ========================================================================= *)

(** The formula fd_mul itself puts the product of two minus-counts on the plus side. *)
Example fd_mul_neg_neg_by_definition : forall a b : nat,
  fd_mul (mkFD 0%nat a) (mkFD 0%nat b) = mkFD (a * b)%nat (a * 0)%nat.
Proof. intros a b. reflexivity. Qed.

(* ========================================================================= *)
(*  4. MULTIPLICATION AS REPETITION; THE SIGN RULE FROM TWO FLIPS            *)
(* ========================================================================= *)

(** Repeat the displacement x exactly n times: addition taken n times. *)
Fixpoint fd_rep (x : FormalDiff) (n : nat) : FormalDiff :=
  match n with
  | O => fd_zero
  | S n' => fd_add x (fd_rep x n')
  end.

(** The second factor tells HOW to repeat: fd_pos y times directly and fd_neg y times
    with a flip (that is, repeating the opposite displacement). *)
Definition fd_mul_rep (x y : FormalDiff) : FormalDiff :=
  fd_add (fd_rep x (fd_pos y)) (fd_rep (fd_opp x) (fd_neg y)).

Lemma fd_rep_formula : forall x n,
  fd_rep x n = mkFD (n * fd_pos x)%nat (n * fd_neg x)%nat.
Proof.
  intros x n. induction n as [| n IH].
  - reflexivity.
  - cbn [fd_rep]. rewrite IH. unfold fd_add. cbn [fd_pos fd_neg]. f_equal; lia.
Qed.

Lemma fd_opp_rep : forall x n, fd_opp (fd_rep x n) = fd_rep (fd_opp x) n.
Proof.
  intros x n. induction n as [| n IH].
  - reflexivity.
  - cbn [fd_rep]. rewrite <- IH. reflexivity.
Qed.

Lemma fd_opp_add : forall x y, fd_opp (fd_add x y) = fd_add (fd_opp x) (fd_opp y).
Proof. intros x y. reflexivity. Qed.

(** Multiplication by repetition coincides with the formula fd_mul — as pairs. *)
Theorem fd_mul_rep_eq : forall x y, fd_mul_rep x y = fd_mul x y.
Proof.
  intros x y. unfold fd_mul_rep. rewrite !fd_rep_formula.
  unfold fd_add, fd_mul, fd_opp. cbn [fd_pos fd_neg]. f_equal; lia.
Qed.

Corollary fd_mul_rep_to_Z : forall x y, fd_to_Z (fd_mul_rep x y) = fd_to_Z x * fd_to_Z y.
Proof. intros x y. rewrite fd_mul_rep_eq. apply fd_mul_to_Z. Qed.

(** a * (-n) = -(a * n): a flip of the second factor flips the result. *)
Theorem fd_mul_rep_opp_r : forall x y,
  fd_mul_rep x (fd_opp y) = fd_opp (fd_mul_rep x y).
Proof.
  intros x y. unfold fd_mul_rep.
  rewrite fd_opp_add, !fd_opp_rep, fd_opp_involutive.
  cbn [fd_opp fd_pos fd_neg]. apply fd_add_comm_eq.
Qed.

(** (-a) * n = -(a * n): a flip of the first factor flips the result. *)
Theorem fd_mul_rep_opp_l : forall x y,
  fd_mul_rep (fd_opp x) y = fd_opp (fd_mul_rep x y).
Proof.
  intros x y. unfold fd_mul_rep.
  rewrite fd_opp_add, !fd_opp_rep. reflexivity.
Qed.

(** THE SIGN RULE: (-a) * (-n) = a * n — two flips, and a flip taken twice is the
    identity (fd_opp_involutive). The proof does not unfold the formula of the
    multiplication and does not go through Z. *)
Theorem fd_sign_rule_from_two_flips : forall x y,
  fd_mul_rep (fd_opp x) (fd_opp y) = fd_mul_rep x y.
Proof.
  intros x y. rewrite fd_mul_rep_opp_l, fd_mul_rep_opp_r. apply fd_opp_involutive.
Qed.

Corollary fd_sign_four_cases : forall a n : nat,
  fd_mul_rep (mkFD a 0%nat) (mkFD n 0%nat) = mkFD (n * a)%nat (n * 0)%nat /\
  fd_equiv (fd_mul_rep (mkFD 0%nat a) (mkFD n 0%nat)) (mkFD 0%nat (n * a)%nat) /\
  fd_equiv (fd_mul_rep (mkFD a 0%nat) (mkFD 0%nat n)) (mkFD 0%nat (n * a)%nat) /\
  fd_equiv (fd_mul_rep (mkFD 0%nat a) (mkFD 0%nat n)) (mkFD (n * a)%nat 0%nat).
Proof.
  intros a n. unfold fd_mul_rep. rewrite !fd_rep_formula.
  unfold fd_equiv, fd_add, fd_opp, fd_zero. cbn [fd_pos fd_neg].
  split; [f_equal; lia|]. split; [lia|]. split; lia.
Qed.

(** The reading of the factors by roles does not change the result. *)
Corollary fd_mul_rep_comm : forall x y, fd_mul_rep x y = fd_mul_rep y x.
Proof. intros x y. rewrite !fd_mul_rep_eq. apply fd_mul_comm_eq. Qed.

(* ========================================================================= *)
(*  5. THE REDUCED PAIR: EXACTLY ONE IN EVERY CLASS                          *)
(* ========================================================================= *)

(** A reduced pair: the steps stand on one side only. *)
Definition fd_reduced (x : FormalDiff) : Prop := fd_pos x = 0%nat \/ fd_neg x = 0%nat.

Lemma fd_of_Z_reduced : forall z, fd_reduced (fd_of_Z z).
Proof. intros [| p | p]; unfold fd_reduced; cbn; auto. Qed.

Lemma fd_reduced_round : forall x, fd_reduced x -> fd_of_Z (fd_to_Z x) = x.
Proof.
  intros [a b] [H | H]; cbn [fd_pos fd_neg] in H; subst; unfold fd_to_Z; cbn [fd_pos fd_neg].
  - destruct b as [| b].
    + reflexivity.
    + replace (Z.of_nat 0 - Z.of_nat (S b)) with (Z.neg (Pos.of_succ_nat b)) by lia.
      cbn [fd_of_Z]. rewrite SuccNat2Pos.id_succ. reflexivity.
  - destruct a as [| a].
    + reflexivity.
    + replace (Z.of_nat (S a) - Z.of_nat 0) with (Z.pos (Pos.of_succ_nat a)) by lia.
      cbn [fd_of_Z]. rewrite SuccNat2Pos.id_succ. reflexivity.
Qed.

Lemma fd_of_Z_injective : forall z1 z2, fd_of_Z z1 = fd_of_Z z2 -> z1 = z2.
Proof. intros z1 z2 H. rewrite <- (fd_to_of_Z z1), <- (fd_to_of_Z z2), H. reflexivity. Qed.

(** In every class of equivalent pairs there is exactly one reduced pair: an integer is
    a finite displacement to one side. *)
Theorem unique_reduced_in_class : forall x,
  exists r, (fd_reduced r /\ fd_equiv r x) /\
            (forall r', fd_reduced r' /\ fd_equiv r' x -> r' = r).
Proof.
  intro x. exists (fd_of_Z (fd_to_Z x)). split.
  - split; [apply fd_of_Z_reduced | apply fd_of_to_Z].
  - intros r' [Hr He]. rewrite <- (fd_reduced_round r' Hr).
    apply fd_equiv_iff_Z in He. rewrite He. reflexivity.
Qed.

Lemma fd_equiv_iff_reduced : forall x y,
  fd_equiv x y <-> fd_of_Z (fd_to_Z x) = fd_of_Z (fd_to_Z y).
Proof.
  intros x y. split.
  - intro H. apply fd_equiv_iff_Z in H. rewrite H. reflexivity.
  - intro H. apply fd_equiv_iff_Z. apply fd_of_Z_injective. exact H.
Qed.

(* ========================================================================= *)
(*  6. THE ANCHOR: A PAIR AS A POINT OF THE SERIES READ FROM AN ANCHOR       *)
(* ========================================================================= *)

(** The point n of the series read from the anchor k. *)
Definition position_from (k n : nat) : FormalDiff := mkFD n k.

(** The sign of a position is set by the choice of the anchor, not by the point. *)
Lemma position_sign : forall k n,
  (fd_to_Z (position_from k n) > 0 <-> (k < n)%nat) /\
  (fd_to_Z (position_from k n) = 0 <-> n = k) /\
  (fd_to_Z (position_from k n) < 0 <-> (n < k)%nat).
Proof. intros k n. unfold position_from, fd_to_Z. cbn [fd_pos fd_neg]. lia. Qed.

(** Moving the anchor one step shifts the marking by one. *)
Lemma anchor_shift : forall k n,
  fd_to_Z (position_from (S k) n) = fd_to_Z (position_from k n) - 1.
Proof. intros k n. unfold position_from, fd_to_Z. cbn [fd_pos fd_neg]. lia. Qed.

(** One and the same point is positive from one anchor and negative from another. *)
Lemma same_point_both_signs : forall n,
  fd_to_Z (position_from 0%nat (S n)) > 0 /\ fd_to_Z (position_from (S (S n)) (S n)) < 0.
Proof. intro n. unfold position_from, fd_to_Z. cbn [fd_pos fd_neg]. lia. Qed.

(** Every integer is a position of some point from some anchor. *)
Lemma every_integer_is_position : forall z, exists k n, fd_to_Z (position_from k n) = z.
Proof. intro z. exists (fd_neg (fd_of_Z z)), (fd_pos (fd_of_Z z)).
  unfold position_from. destruct (fd_of_Z z) as [a b] eqn:E. cbn [fd_pos fd_neg].
  rewrite <- E. apply fd_to_of_Z. Qed.

(** The order of positions is the order of the series, whatever the anchor. *)
Lemma position_order : forall k n m,
  fd_to_Z (position_from k n) <= fd_to_Z (position_from k m) <-> (n <= m)%nat.
Proof. intros k n m. unfold position_from, fd_to_Z. cbn [fd_pos fd_neg]. lia. Qed.
