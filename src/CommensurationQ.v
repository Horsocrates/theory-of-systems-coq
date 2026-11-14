(** * CommensurationQ.v — Rational numbers as commensuration: the equation
      q * u = p, division at zero, the positional reading, and a record of
      the commensurate position

    E/R/R reading (done before coding; audit of Part III of the Mathematics
    volume, chapter III.2, places 2.1 and 2.2, 2026-11-14):

    Elements: the unit step and its parts; pairs "steps taken / parts of the
              unit" — the values of the standard type Q.
    Roles:    the small step 1/q — the measure; the position p/q — the small
              step taken p times; the cuts — the new boundaries inside the
              unit step (one less than the parts).
    Rules:    the equation of commensuration q * u = p; two records denote
              one position when the cross products are equal (Qeq).
    Proved:   (1) the type excludes a FRACTION with the zero denominator;
                  the library OPERATION of division is total and returns 0
                  at the zero divisor, where the law of the inverse fails;
              (2) the equation q * u = p determines a step (a solution
                  exists and is unique) EXACTLY when q <> 0: with q = 0 and
                  p <> 0 there is no step, with q = 0 and p = 0 every step
                  fits; the library value at the zero divisor does not solve
                  the equation; a division with q <> 0 built into the type;
              (3) the positional reading: p/q is the small step taken p
                  times, and q small steps make the unit;
              (4) inner points of the unit segment; the mediant lies between;
              (5) a record of the commensurate position (steps and cuts),
                  mutually inverse with Q on the records, with the same
                  equality, addition and multiplication.
    P4 diagnostic ("could it be otherwise?"): finite pairs only. Forced:
              (1)-(5). NOT claimed: a type of rationals of its own beyond
              the standard Q — the record of (5) is the same pair read by
              cuts instead of parts, its content is in the theorems; a
              quotient type (equal positions are related by Qeq / cm_eq);
              density "infinitely many between".

    STATUS: 35 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith ZArith Lia Qreduction Qfield Setoid PArith.Pnat.

From ToS Require Import stdlib.SternBrocot.

Close Scope Z_scope.
Close Scope positive_scope.
Open Scope Q_scope.

(* ========================================================================= *)
(*  1. THE TYPE Q: THE EXCLUDED FRACTION AND THE DIVISION AT ZERO            *)
(* ========================================================================= *)

(** 1/2 and 2/4 are different records and one rational value. *)
Lemma half_neq_two_quarters : (1 # 2) <> (2 # 4).
Proof. discriminate. Qed.

Lemma half_Qeq_two_quarters : (1 # 2) == (2 # 4).
Proof. reflexivity. Qed.

Lemma Qeq_is_cross_product : forall (p r : Z) (q s : positive),
  (p # q) == (r # s) <-> (p * Z.pos s = r * Z.pos q)%Z.
Proof. intros. unfold Qeq. simpl. tauto. Qed.

(** The TYPE excludes a fraction with the zero denominator ... *)
Lemma denominator_never_zero : forall x : Q, Z.pos (Qden x) <> 0%Z.
Proof. intros x H. discriminate H. Qed.

Lemma Qinv_m3_4 : / (-3 # 4) = (-4 # 3).
Proof. reflexivity. Qed.

Lemma Qinv_neg_general : forall p q : positive, / (Z.neg p # q) = (Z.neg q # p).
Proof. reflexivity. Qed.

Lemma Qinv_pos_general : forall p q : positive, / (Z.pos p # q) = (Z.pos q # p).
Proof. reflexivity. Qed.

(** ... but the OPERATION of division of the library is defined everywhere and returns
    zero at the zero divisor; the law of the inverse fails there. *)
Lemma Qinv_of_zero : / 0 = 0.
Proof. reflexivity. Qed.

Lemma Qdiv_by_zero_example : 1 / 0 = 0.
Proof. reflexivity. Qed.

Lemma Qdiv_by_zero : forall x : Q, x / 0 == 0.
Proof. intro x. unfold Qdiv. rewrite Qinv_of_zero. ring. Qed.

Lemma inverse_law_fails_at_zero : ~ (0 * / 0 == 1).
Proof. intro H. unfold Qeq in H. simpl in H. discriminate H. Qed.

(* ========================================================================= *)
(*  2. THE EQUATION OF COMMENSURATION  q * u = p                             *)
(* ========================================================================= *)

(** With q <> 0 the equation q * u = p is solved by u = p / q, and by it only. *)
Theorem commensuration_solved : forall q p : Q, ~ q == 0 -> q * (p / q) == p.
Proof. intros q p Hq. field. exact Hq. Qed.

Theorem commensuration_unique : forall q p u : Q,
  ~ q == 0 -> q * u == p -> u == p / q.
Proof. intros q p u Hq H. rewrite <- H. field. exact Hq. Qed.

(** q = 0, p <> 0: there is no step at all. *)
Theorem zero_parts_no_step : forall p u : Q, ~ p == 0 -> ~ (0 * u == p).
Proof. intros p u Hp H. apply Hp. rewrite <- H. ring. Qed.

(** q = 0, p = 0: every step fits — the equation determines nothing. *)
Theorem zero_parts_any_step : forall u : Q, 0 * u == 0.
Proof. intro u. ring. Qed.

(** The equation DETERMINES a step: a solution exists and is unique (up to Qeq). *)
Definition determines_step (q p : Q) : Prop :=
  exists u : Q, q * u == p /\ forall u' : Q, q * u' == p -> u' == u.

(** The equation of commensuration determines a step exactly when q <> 0. *)
Theorem commensuration_determines_iff : forall q p : Q,
  determines_step q p <-> ~ q == 0.
Proof.
  intros q p. split.
  - intros [u [Hu Huniq]] Hq.
    assert (Hp : p == 0). { rewrite <- Hu, Hq. ring. }
    assert (H1 : q * (u + 1) == p). { rewrite Hq, Hp. ring. }
    specialize (Huniq (u + 1) H1).
    assert (Habs : 1 == 0).
    { setoid_replace 1 with ((u + 1) - u) by ring. rewrite Huniq. ring. }
    unfold Qeq in Habs. simpl in Habs. discriminate Habs.
  - intro Hq. exists (p / q). split.
    + apply commensuration_solved. exact Hq.
    + intros u' H. apply commensuration_unique; assumption.
Qed.

(** The value the library returns at the zero divisor does not solve the equation. *)
Theorem library_value_at_zero_is_not_a_solution : forall p : Q,
  ~ p == 0 -> ~ (0 * (p / 0) == p).
Proof. intros p Hp. apply zero_parts_no_step. exact Hp. Qed.

(** A division with the condition q <> 0 built into the TYPE of the divisor. *)
Definition NonZeroQ : Type := { q : Q | ~ q == 0 }.

Definition step_of (p : Q) (q : NonZeroQ) : Q := p / proj1_sig q.

Theorem step_of_spec : forall (p : Q) (q : NonZeroQ),
  proj1_sig q * step_of p q == p /\
  (forall u : Q, proj1_sig q * u == p -> u == step_of p q).
Proof.
  intros p [q Hq]. unfold step_of. cbn [proj1_sig]. split.
  - apply commensuration_solved. exact Hq.
  - intros u H. apply commensuration_unique; assumption.
Qed.

(** Among the integers the equation 2 * z = 1 has no solution. *)
Lemma two_has_no_integer_inverse : ~ exists z : Z, (2 * z = 1)%Z.
Proof. intros [z H]. lia. Qed.

Lemma Z_has_no_inverse_operation :
  ~ exists inv : Z -> Z, forall x : Z, x <> 0%Z -> (x * inv x = 1)%Z.
Proof. intros [inv H]. specialize (H 2%Z ltac:(discriminate)). lia. Qed.

(* ========================================================================= *)
(*  3. THE POSITIONAL READING  p/q = p TIMES THE SMALL STEP 1/q              *)
(* ========================================================================= *)

(** The position p/q is the small step 1/q taken p times; q small steps make the unit. *)
Lemma position_is_multiple_of_small_step : forall (p : Z) (q : positive),
  p # q == inject_Z p * (1 # q).
Proof. intros p q. unfold Qeq. simpl. ring. Qed.

Lemma small_steps_make_unit : forall q : positive,
  inject_Z (Z.pos q) * (1 # q) == 1.
Proof.
  intros q. unfold Qeq, Qmult, inject_Z. cbn [Qnum Qden].
  rewrite ?Pos2Z.inj_mul. ring.
Qed.

Lemma new_step_reading : forall (p : Z) (q : positive),
  inject_Z (Z.pos q) * (p # q) == inject_Z p.
Proof.
  intros p q. unfold Qeq, Qmult, inject_Z. cbn [Qnum Qden].
  rewrite ?Pos2Z.inj_mul. ring.
Qed.

(* ========================================================================= *)
(*  4. THE UNIT SEGMENT IS DIVISIBLE: INNER POINTS AND THE MEDIANT           *)
(* ========================================================================= *)

(** k/n with k < n lies strictly inside the unit segment. *)
Lemma inner_point : forall k n : positive,
  (k < n)%positive -> 0 < Z.pos k # n /\ Z.pos k # n < 1.
Proof. intros k n H. unfold Qlt. simpl. split; lia. Qed.

(** Between two rationals lies their mediant. *)
Lemma mediant_between_Q : forall (a c : Z) (b d : positive),
  a # b < c # d ->
  a # b < (a + c) # (b + d) /\ (a + c) # (b + d) < c # d.
Proof.
  intros a c b d H. unfold Qlt in *. simpl in *.
  rewrite Pos2Z.inj_add. split.
  - apply mediant_between_left with (d := Z.pos d); [ reflexivity | reflexivity | exact H ].
  - apply mediant_between_right with (b := Z.pos b); [ reflexivity | reflexivity | exact H ].
Qed.

Example mediant_1_3_1_2 : (1 # 3) < (2 # 5) /\ (2 # 5) < (1 # 2).
Proof. exact (mediant_between_Q 1 1 3 2 eq_refl). Qed.

(* ========================================================================= *)
(*  5. A RECORD OF THE COMMENSURATE POSITION: STEPS AND CUTS                 *)
(* ========================================================================= *)

(** A commensurate position: the number of small steps taken and the number of NEW
    boundaries inside the unit step. The parts are one more than the cuts — zero parts
    cannot be written. The record is the pair of Q read differently (cuts, not parts). *)
Record Commens := mkCm { cm_steps : Z ; cm_cuts : nat }.

Definition cm_parts (x : Commens) : positive := Pos.of_succ_nat (cm_cuts x).
Definition cm_to_Q (x : Commens) : Q := cm_steps x # cm_parts x.
Definition cm_of_Q (q : Q) : Commens :=
  mkCm (Qnum q) (Nat.pred (Pos.to_nat (Qden q))).
Definition cm_eq (x y : Commens) : Prop :=
  (cm_steps x * Z.pos (cm_parts y) = cm_steps y * Z.pos (cm_parts x))%Z.

Lemma cm_parts_count : forall x : Commens, Pos.to_nat (cm_parts x) = S (cm_cuts x).
Proof. intro x. unfold cm_parts. apply SuccNat2Pos.id_succ. Qed.

(** The two passages are mutually inverse on the records themselves. *)
Lemma cm_to_of : forall q : Q, cm_to_Q (cm_of_Q q) = q.
Proof.
  intros [n d]. unfold cm_to_Q, cm_of_Q, cm_parts. simpl.
  f_equal. destruct (Pos2Nat.is_succ d) as [k Hk]. rewrite Hk. cbn [Nat.pred].
  apply Pos2Nat.inj. rewrite SuccNat2Pos.id_succ. symmetry. exact Hk.
Qed.

Lemma cm_of_to : forall x : Commens, cm_of_Q (cm_to_Q x) = x.
Proof.
  intros [s c]. unfold cm_of_Q, cm_to_Q, cm_parts. simpl.
  f_equal. apply SuccNat2Pos.pred_id.
Qed.

Lemma cm_eq_iff_Qeq : forall x y : Commens, cm_eq x y <-> cm_to_Q x == cm_to_Q y.
Proof. intros x y. unfold cm_eq, cm_to_Q, Qeq. simpl. tauto. Qed.

(** No cuts: an integer position. *)
Lemma cm_no_cuts_is_integer : forall z : Z, cm_to_Q (mkCm z 0) = inject_Z z.
Proof. reflexivity. Qed.

Lemma cm_position : forall x : Commens,
  cm_to_Q x == inject_Z (cm_steps x) * (1 # cm_parts x).
Proof. intro x. apply position_is_multiple_of_small_step. Qed.

Definition cm_add (x y : Commens) : Commens :=
  mkCm (cm_steps x * Z.pos (cm_parts y) + cm_steps y * Z.pos (cm_parts x))
       (Nat.pred (S (cm_cuts x) * S (cm_cuts y))).

Definition cm_mul (x y : Commens) : Commens :=
  mkCm (cm_steps x * cm_steps y) (Nat.pred (S (cm_cuts x) * S (cm_cuts y))).

Lemma cm_parts_mul : forall c1 c2 : nat,
  Pos.of_succ_nat (Nat.pred (S c1 * S c2))
  = (Pos.of_succ_nat c1 * Pos.of_succ_nat c2)%positive.
Proof.
  intros c1 c2. apply Pos2Nat.inj.
  rewrite Pos2Nat.inj_mul, !SuccNat2Pos.id_succ. simpl. reflexivity.
Qed.

(** Addition and multiplication of positions are carried into those of Q. *)
Lemma cm_add_to_Q : forall x y : Commens,
  cm_to_Q (cm_add x y) = cm_to_Q x + cm_to_Q y.
Proof.
  intros [s1 c1] [s2 c2]. unfold cm_to_Q, cm_add, cm_parts, Qplus.
  cbn [cm_steps cm_cuts Qnum Qden]. rewrite cm_parts_mul. reflexivity.
Qed.

Lemma cm_mul_to_Q : forall x y : Commens,
  cm_to_Q (cm_mul x y) = cm_to_Q x * cm_to_Q y.
Proof.
  intros [s1 c1] [s2 c2]. unfold cm_to_Q, cm_mul, cm_parts, Qmult.
  cbn [cm_steps cm_cuts Qnum Qden]. rewrite cm_parts_mul. reflexivity.
Qed.

(* ===================================================================== *)
(* ===================================================================== *)
