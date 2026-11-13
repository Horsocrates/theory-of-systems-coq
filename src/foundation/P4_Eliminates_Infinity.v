(** * P4_Eliminates_Infinity.v — nat is inductive RULE, not completed SET
    Elements: natural numbers; finite stages (lists of numbers)
    Roles:    a stage plays "what is actual so far"; nat plays the RULE that
              generates the next number
    Rules:    induction; no finite stage exhausts the numbers; beyond every
              number there is a greater one
    STATUS: 13 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026

    Nov 2026.  The synthesis P4_eliminates_Infinity used to join four facts
    that hold under any reading of infinity (induction, n < n+1, 5! = 120,
    0+1+2+3 = 6).  It now states the process form.  [converges] used to have a
    non-strict inequality, under which the limit is not unique (the constant
    sequence 1 "converged" to 0, 1 and 2); it is strict now: convergence in
    nat is stabilisation and the limit is unique. *)

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
    (if (a n <=? L)%nat then L - a n else a n - L) < eps.

Lemma const_converges : forall c, converges (fun _ => c) c.
Proof.
  intros c eps Heps. exists 0. intros n _.
  destruct (c <=? c)%nat eqn:E; lia.
Qed.

(* 4a. With the strict inequality convergence in nat is stabilisation ... *)
Lemma converges_iff_stabilizes : forall a L,
  converges a L <-> exists N, forall n, (n >= N)%nat -> a n = L.
Proof.
  intros a L. split.
  - intro H. destruct (H 1 (Nat.lt_0_1)) as [N HN]. exists N. intros n Hn.
    specialize (HN n Hn). destruct (a n <=? L) eqn:E.
    + apply Nat.leb_le in E. lia.
    + apply Nat.leb_gt in E. lia.
  - intros [N HN] eps Heps. exists N. intros n Hn. rewrite (HN n Hn).
    rewrite Nat.leb_refl. lia.
Qed.

(* 4b. ... and the limit is unique *)
Lemma converges_unique : forall a L1 L2,
  converges a L1 -> converges a L2 -> L1 = L2.
Proof.
  intros a L1 L2 H1 H2.
  apply converges_iff_stabilizes in H1. apply converges_iff_stabilizes in H2.
  destruct H1 as [N1 H1]. destruct H2 as [N2 H2].
  rewrite <- (H1 (N1 + N2)) by lia. rewrite <- (H2 (N1 + N2)) by lia. reflexivity.
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

(* No finite stage exhausts the natural numbers. *)
Theorem no_finite_stage_exhausts_nat : forall l : list nat, exists n, ~ In n l.
Proof.
  intro l. destruct (finite_list_bounded l) as [b Hb].
  exists (S b). intro Hin. specialize (Hb (S b) Hin). lia.
Qed.

(* Infinity as a process: the rule of induction, the inexhaustibility of the
   stages, and a greater number beyond every number. *)
Theorem P4_eliminates_Infinity :
  (forall P : nat -> Prop, P 0 -> (forall n, P n -> P (S n)) -> forall n, P n) /\
  (forall l : list nat, exists n, ~ In n l) /\
  (forall n : nat, exists m, (n < m)%nat).
Proof.
  split; [exact nat_ind | split; [exact no_finite_stage_exhausts_nat |]].
  intro n. exists (S n). lia.
Qed.
