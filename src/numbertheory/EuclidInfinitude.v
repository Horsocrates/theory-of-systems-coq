(** * EuclidInfinitude.v — Euclid's Infinitude of Primes as ToS System

    Theory of Systems — Number Theory layer (Part XIII)

    Elements: natural numbers; finite lists of primes
    Roles:    "infinitely many primes" -> an UNBOUNDED CONSTRUCTION, not a
              completed infinite set
    Rules:    given any bound N, the prime divisor of N! + 1 exceeds N
    Status:   no finite list can contain all primes (a process, per P4)

    This is the constructive form demanded by P4: "infinity is a process".
    The proof is an ALGORITHM — for any N it produces a concrete witness:
    a prime divisor of N! + 1, which cannot be <= N (else it would divide
    both N! and N!+1, hence 1). Built on PrimeFactorization.exists_prime_divisor.

    RELATED (NOT duplicated): zeta/EulerProduct.v derives the infinitude
    indirectly from the divergence of the Euler product; this file gives the
    direct, classical, constructive Euclid argument over the repo's own
    is_prime / divides predicates.

    STATUS: 5 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.
From Stdlib Require Import ArithRing.
From Stdlib Require Import Factorial.
Import ListNotations.

From ToS Require Import stdlib.Primes.
From ToS Require Import numbertheory.PrimeFactorization.

(* ================================================================= *)
(*  Every 1 <= p <= n divides n!                                      *)
(* ================================================================= *)

(** 1. divides_fact *)
Lemma divides_fact : forall n p, 1 <= p -> p <= n -> divides p (fact n).
Proof.
  induction n as [|m IH]; intros p Hp1 Hpn.
  - lia.
  - destruct (Nat.eq_dec p (S m)) as [-> | Hne].
    + change (fact (S m)) with (S m * fact m). apply divides_mul_l.
    + assert (Hpm : p <= m) by lia.
      change (fact (S m)) with (S m * fact m).
      apply divides_trans with (b := fact m).
      * apply IH; [exact Hp1 | exact Hpm].
      * exists (S m). ring.
Qed.

(* ================================================================= *)
(*  Euclid: for every N there is a larger prime                       *)
(* ================================================================= *)

(** 2. exists_larger_prime — the algorithmic infinitude statement *)
Theorem exists_larger_prime : forall N, exists p, is_prime p /\ N < p.
Proof.
  intros N.
  pose (M := fact N + 1).
  assert (HM : 2 <= M).
  { unfold M. pose proof (fact_neq_0 N). lia. }
  destruct (exists_prime_divisor M HM) as [p [Hp Hpd]].
  exists p. split; [exact Hp|].
  destruct (Nat.le_gt_cases p N) as [Hle | Hgt].
  - exfalso.
    assert (Hpf : divides p (fact N))
      by (apply divides_fact; [destruct Hp; lia | exact Hle]).
    destruct Hpd as [k Hk]. destruct Hpf as [j Hj].
    unfold M in Hk. destruct Hp as [Hp2 _].
    assert (Heq : p * j + 1 = p * k) by lia.
    assert (Hkj : j < k).
    { destruct (Nat.le_gt_cases k j) as [Hkle | Hkgt].
      - assert (p * k <= p * j) by (apply Nat.mul_le_mono_l; exact Hkle). lia.
      - exact Hkgt. }
    assert (Hge : p * (j + 1) <= p * k) by (apply Nat.mul_le_mono_l; lia).
    rewrite Nat.mul_add_distr_l in Hge. lia.
  - exact Hgt.
Qed.

(* ================================================================= *)
(*  No finite list contains all primes                                *)
(* ================================================================= *)

(** 3. bound: any member is at most the running maximum *)
Lemma in_le_fold_max : forall x l, In x l -> x <= fold_right Nat.max 0 l.
Proof.
  induction l as [|a l IH]; simpl; intros H.
  - contradiction.
  - destruct H as [-> | H].
    + lia.
    + apply IH in H. lia.
Qed.

(** 4. Euclid (list form): no finite list of numbers contains every prime *)
Theorem primes_not_finite : forall l, ~ (forall p, is_prime p -> In p l).
Proof.
  intros l Hall.
  destruct (exists_larger_prime (fold_right Nat.max 0 l)) as [p [Hp Hgt]].
  pose proof (Hall p Hp) as Hin.
  apply in_le_fold_max in Hin. lia.
Qed.

(** 5. concrete instance: there is a prime strictly above 100 *)
Example prime_above_100 : exists p, is_prime p /\ 100 < p.
Proof. apply exists_larger_prime. Qed.
