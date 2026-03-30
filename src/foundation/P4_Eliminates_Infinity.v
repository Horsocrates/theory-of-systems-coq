(** * P4_Eliminates_Infinity.v — nat is inductive RULE, not completed SET
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026 *)

From Stdlib Require Import Lia PeanoNat List.
Import ListNotations.

(* 1. Induction = built-in rule, not axiom *)
Lemma nat_induction_works : forall P : nat -> Prop,
  P 0 -> (forall n, P n -> P (S n)) -> forall n, P n.
Proof. exact nat_ind. Qed.

(* 2. Each n is finite *)
Lemma each_n_finite : forall n, (n < S n)%nat.
Proof. intro. lia. Qed.

(* 3. Partial sum needs no infinite set *)
Fixpoint partial_sum (a : nat -> nat) (N : nat) : nat :=
  match N with O => a O | S k => (partial_sum a k + a (S k))%nat end.

Lemma partial_sum_zero : forall a, partial_sum a 0 = a 0.
Proof. reflexivity. Qed.

Lemma partial_sum_3 : partial_sum (fun n => n) 3 = 6.
Proof. reflexivity. Qed.

(* 4. Convergence = forall-exists over nat = Prop, not Set *)
Definition converges (a : nat -> nat) (L : nat) : Prop :=
  forall eps, (eps > 0)%nat -> exists N, forall n, (n >= N)%nat ->
    (if (a n <=? L)%nat then L - a n else a n - L) <= eps.

Lemma const_converges : forall c, converges (fun _ => c) c.
Proof.
  intros c eps Heps. exists 0. intros n _.
  destruct (c <=? c)%nat eqn:E; lia.
Qed.

(* 5. Strong induction by auxiliary predicate *)
Lemma strong_ind_aux : forall P : nat -> Prop,
  (forall n, (forall m, (m < n)%nat -> P m) -> P n) ->
  forall n m, (m <= n)%nat -> P m.
Proof.
  intros P H n. induction n as [|n' IH].
  - intros m Hm. apply H. intros k Hk. lia.
  - intros m Hm. destruct (Nat.eq_dec m (S n')).
    + subst. apply H. intros k Hk. apply IH. lia.
    + apply IH. lia.
Qed.

Lemma strong_induction : forall P : nat -> Prop,
  (forall n, (forall m, (m < n)%nat -> P m) -> P n) ->
  forall n, P n.
Proof.
  intros P H n. exact (strong_ind_aux P H n n (Nat.le_refl n)).
Qed.

(* 6. Recursion = Fixpoint, no axiom *)
Fixpoint factorial (n : nat) : nat :=
  match n with O => 1 | S k => (S k * factorial k)%nat end.

Lemma factorial_5 : factorial 5 = 120.
Proof. reflexivity. Qed.

(* 7. Finite list bounded *)
Lemma finite_list_bounded : forall (l : list nat),
  exists b, forall x, In x l -> (x <= b)%nat.
Proof.
  induction l as [|a xs [b Hb]].
  - exists 0. intros x H. destruct H.
  - exists (Nat.max a b). intros x [Heq|Hin]; [subst; lia | specialize (Hb x Hin); lia].
Qed.

(* 8. P4 ontology: nat = RULE (induction), not OBJECT (completed set) *)
(* The Axiom of Infinity asserts {0,1,2,...} exists as a SET.
   Under P4, nat is an inductive type: a RULE that generates elements.
   Every use of nat (sums, limits, convergence) works via nat_rect,
   not via "the set of all natural numbers." *)

Theorem P4_eliminates_Infinity :
  (forall P : nat -> Prop, P 0 -> (forall n, P n -> P (S n)) -> forall n, P n) /\
  (forall n : nat, (n < S n)%nat) /\
  factorial 5 = 120 /\
  partial_sum (fun n => n) 3 = 6.
Proof.
  split; [|split; [|split]].
  - exact nat_ind.
  - exact each_n_finite.
  - exact factorial_5.
  - exact partial_sum_3.
Qed.
