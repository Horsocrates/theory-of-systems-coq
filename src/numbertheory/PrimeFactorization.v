(** * PrimeFactorization.v — Fundamental Theorem of Arithmetic as ToS System

    Theory of Systems — Number Theory layer (Part XIII)

    Elements: natural numbers and their finite lists of prime factors
    Roles:    prime -> atom (generator of the multiplicative monoid of N)
              n     -> composite (a finite product of atoms)
    Rules:    factorization EXISTS (trial division) and is UNIQUE (Euclid's lemma)
    Status:   the multiset of prime factors is a constitutive invariant of n

    This file proves what the whole analytic corpus (src/zeta/, EulerProduct, ...)
    PRESUPPOSES but never establishes: every n >= 1 is a product of primes, and
    that product is unique up to permutation. Built directly on stdlib.Primes
    (divides, is_prime, ...) and stdlib.GCD (gcd, gcd_divides_l/r); the heart is
    Euclid's lemma  p prime, p | a*b  ->  p | a \/ p | b.

    RELATED (NOT duplicated): stdlib/Primes.v (divides/is_prime/sieve),
    stdlib/GCD.v (Euclidean gcd), zeta/EulerProduct.v (uses unique factorization
    implicitly to identify sum_n 1/n^s with prod_p 1/(1-p^-s)).

    STATUS: 21 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.
From Stdlib Require Import ArithRing.
From Stdlib Require Import Permutation.
From Stdlib Require Import Wf_nat.
Import ListNotations.

From ToS Require Import stdlib.Primes.
From ToS Require Import stdlib.GCD.

(* ================================================================= *)
(*  Product of a list of factors                                      *)
(* ================================================================= *)

Definition prod_list (l : list nat) : nat := fold_right Nat.mul 1 l.

Lemma prod_nil : prod_list [] = 1.
Proof. reflexivity. Qed.

Lemma prod_cons : forall x l, prod_list (x :: l) = x * prod_list l.
Proof. reflexivity. Qed.

Lemma prod_app : forall l1 l2, prod_list (l1 ++ l2) = prod_list l1 * prod_list l2.
Proof.
  induction l1 as [|x l1 IH]; simpl; intros l2.
  - ring.
  - rewrite IH. ring.
Qed.

(* Defensive Forall helpers (version-independent) *)
Lemma Forall_app_intro : forall (P : nat -> Prop) l1 l2,
  Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof.
  induction l1 as [|x l1 IH]; simpl; intros l2 H1 H2.
  - exact H2.
  - inversion H1; subst. constructor; auto.
Qed.

Lemma Forall_app_elim : forall (P : nat -> Prop) l1 l2,
  Forall P (l1 ++ l2) -> Forall P l1 /\ Forall P l2.
Proof.
  induction l1 as [|x l1 IH]; simpl; intros l2 H.
  - split; [constructor | exact H].
  - inversion H; subst. apply IH in H3. destruct H3. split; [constructor|]; auto.
Qed.

(* ================================================================= *)
(*  Bridge to stdlib Nat.divide, and primality reflection            *)
(* ================================================================= *)

(** 1. divides (repo: exists k, n = d*k) <-> Nat.divide (exists z, n = z*d) *)
Lemma divides_iff_Ndivide : forall d n, divides d n <-> Nat.divide d n.
Proof.
  intros d n. split.
  - intros [k Hk]. exists k. rewrite Hk. ring.
  - intros [k Hk]. exists k. rewrite Hk. ring.
Qed.

(** 2. boolean primality test reflects the Prop is_prime *)
Lemma is_prime_bool_true_is_prime : forall n,
  is_prime_bool n = true -> is_prime n.
Proof.
  intros n H. split.
  - apply prime_ge_2; exact H.
  - intros d Hd2 Hdn Hdiv.
    pose proof (prime_not_composite n H d Hd2 Hdn) as Hfalse.
    apply (proj2 (divides_bool_correct d n ltac:(lia))) in Hdiv.
    rewrite Hdiv in Hfalse. discriminate.
Qed.

Lemma is_prime_2 : is_prime 2.
Proof. apply is_prime_bool_true_is_prime. reflexivity. Qed.

Lemma is_prime_3 : is_prime 3.
Proof. apply is_prime_bool_true_is_prime. reflexivity. Qed.

(* ================================================================= *)
(*  Divisors of a prime; coprimality                                  *)
(* ================================================================= *)

(** 3. the only divisors of a prime are 1 and itself *)
Lemma prime_divisor_1_or_self : forall p d,
  is_prime p -> divides d p -> d = 1 \/ d = p.
Proof.
  intros p d [Hp2 Hpd] Hdiv.
  assert (Hdle : d <= p) by (apply (divides_le d p); [lia | exact Hdiv]).
  destruct d as [|d'].
  - destruct Hdiv as [k Hk]. simpl in Hk. lia.
  - destruct d' as [|d''].
    + left. reflexivity.
    + destruct (Nat.eq_dec (S (S d'')) p) as [Heq | Hne].
      * right. exact Heq.
      * exfalso. apply (Hpd (S (S d''))); [lia | lia | exact Hdiv].
Qed.

(** 4. a prime not dividing a is coprime to a *)
Lemma prime_coprime_of_not_divides : forall p a,
  is_prime p -> ~ divides p a -> gcd p a = 1.
Proof.
  intros p a Hp Hnd.
  destruct (prime_divisor_1_or_self p (gcd p a) Hp (gcd_divides_l p a)) as [H1 | Hpp].
  - exact H1.
  - exfalso. apply Hnd. rewrite <- Hpp. apply gcd_divides_r.
Qed.

(* ================================================================= *)
(*  Euclid's lemma — the heart of uniqueness                          *)
(* ================================================================= *)

(** 5. p prime, p | a*b  ->  p | a \/ p | b *)
Lemma euclid_lemma : forall p a b,
  is_prime p -> divides p (a * b) -> divides p a \/ divides p b.
Proof.
  intros p a b Hp Hdiv.
  assert (Hp0 : p <> 0) by (destruct Hp; lia).
  destruct (divides_bool p a) eqn:Eba.
  - left. apply (proj1 (divides_bool_correct p a Hp0)). exact Eba.
  - right.
    assert (Hnd : ~ divides p a).
    { intro Hd. apply (proj2 (divides_bool_correct p a Hp0)) in Hd. congruence. }
    assert (Hcop : gcd p a = 1) by (apply prime_coprime_of_not_divides; assumption).
    apply (proj2 (divides_iff_Ndivide p b)).
    apply (Nat.gauss p a b).
    + apply (proj1 (divides_iff_Ndivide p (a * b))). exact Hdiv.
    + exact Hcop.
Qed.

(* ================================================================= *)
(*  Existence of a prime factorization                                *)
(* ================================================================= *)

(** 6. every n >= 1 is a product of a finite list of primes *)
Lemma factor_exists : forall n, 1 <= n ->
  exists l, Forall is_prime l /\ prod_list l = n.
Proof.
  apply (well_founded_induction lt_wf
          (fun n => 1 <= n -> exists l, Forall is_prime l /\ prod_list l = n)).
  intros n IH Hn.
  destruct (Nat.eq_dec n 1) as [->|Hne].
  - exists []. split; [constructor | reflexivity].
  - assert (Hn2 : 2 <= n) by lia.
    destruct (is_prime_bool n) eqn:Hpb.
    + exists [n]. split.
      * constructor; [apply is_prime_bool_true_is_prime; exact Hpb | constructor].
      * simpl. ring.
    + destruct (composite_has_small_factor n Hn2 Hpb) as [d [Hd2 [Hdn Hdivb]]].
      apply (proj1 (divides_bool_correct d n ltac:(lia))) in Hdivb.
      destruct Hdivb as [k Hk].
      assert (Hk2 : 2 <= k) by nia.
      assert (Hkn : k < n) by nia.
      destruct (IH d Hdn ltac:(lia)) as [ld [Hldp Hldprod]].
      destruct (IH k Hkn ltac:(lia)) as [lk [Hlkp Hlkprod]].
      exists (ld ++ lk). split.
      * apply Forall_app_intro; assumption.
      * rewrite prod_app, Hldprod, Hlkprod. lia.
Qed.

(** 7. every n >= 2 has at least one prime divisor *)
Lemma exists_prime_divisor : forall n, 2 <= n ->
  exists p, is_prime p /\ divides p n.
Proof.
  intros n Hn.
  destruct (factor_exists n ltac:(lia)) as [l [Hl Hprod]].
  destruct l as [|p l'].
  - simpl in Hprod. lia.
  - exists p. split.
    + apply (Forall_inv Hl).
    + rewrite <- Hprod. rewrite prod_cons. exists (prod_list l'). reflexivity.
Qed.

(* ================================================================= *)
(*  Uniqueness of the prime factorization (up to permutation)         *)
(* ================================================================= *)

(** 8. a prime dividing a product of primes equals one of them *)
Lemma prime_eq_of_divides : forall p q,
  is_prime p -> is_prime q -> divides p q -> p = q.
Proof.
  intros p q Hp Hq Hdiv.
  destruct Hp as [Hp2 _]. destruct Hq as [Hq2 Hqd].
  assert (Hple : p <= q) by (apply (divides_le p q); [lia | exact Hdiv]).
  destruct (Nat.lt_ge_cases p q) as [Hlt | Hge].
  - exfalso. apply (Hqd p Hp2 Hlt). exact Hdiv.
  - lia.
Qed.

(** 9. p prime dividing prod_list l (all primes)  ->  p in l *)
Lemma prime_in_of_divides_prod : forall l p,
  is_prime p -> Forall is_prime l -> divides p (prod_list l) -> In p l.
Proof.
  induction l as [|q l' IH]; intros p Hp Hall Hdiv; rewrite ?prod_cons in Hdiv.
  - simpl in Hdiv. exfalso.
    assert (Hle : p <= 1) by (apply (divides_le p 1); [lia | exact Hdiv]).
    destruct Hp as [Hp2 _]. lia.
  - pose proof (Forall_inv Hall) as Hq.
    pose proof (Forall_inv_tail Hall) as Hall'.
    destruct (euclid_lemma p q (prod_list l') Hp Hdiv) as [Hpq | Hprest].
    + left. symmetry. apply prime_eq_of_divides; assumption.
    + right. apply IH; assumption.
Qed.

(** 10. a product of primes equal to 1 is the empty product *)
Lemma prod_one_all_primes_nil : forall l,
  Forall is_prime l -> prod_list l = 1 -> l = [].
Proof.
  destruct l as [|q l']; intros Hall Hprod.
  - reflexivity.
  - exfalso. rewrite prod_cons in Hprod.
    pose proof (Forall_inv Hall) as Hq. destruct Hq as [Hq2 _].
    destruct (prod_list l') as [|m] eqn:E.
    + rewrite Nat.mul_0_r in Hprod. discriminate.
    + nia.
Qed.

(** 11. UNIQUENESS: two prime factorizations of the same number are permutations *)
Theorem prime_factorization_unique : forall l1 l2,
  Forall is_prime l1 -> Forall is_prime l2 ->
  prod_list l1 = prod_list l2 -> Permutation l1 l2.
Proof.
  induction l1 as [|p l1' IH]; intros l2 H1 H2 Hprod.
  - simpl in Hprod. symmetry in Hprod.
    apply prod_one_all_primes_nil in Hprod; [subst l2 | exact H2].
    apply Permutation_refl.
  - pose proof (Forall_inv H1) as Hp.
    pose proof (Forall_inv_tail H1) as Hl1'.
    assert (Hdiv : divides p (prod_list l2)).
    { rewrite <- Hprod. rewrite prod_cons. exists (prod_list l1'). reflexivity. }
    assert (Hin : In p l2) by (apply (prime_in_of_divides_prod l2 p); assumption).
    apply in_split in Hin. destruct Hin as [l2a [l2b ->]].
    apply Permutation_cons_app.
    pose proof (Forall_app_elim is_prime l2a (p :: l2b) H2) as [Ha Hpb].
    pose proof (Forall_inv_tail Hpb) as Hb.
    apply IH.
    + exact Hl1'.
    + apply Forall_app_intro; assumption.
    + rewrite prod_cons in Hprod. rewrite prod_app in Hprod. rewrite prod_cons in Hprod.
      rewrite prod_app.
      assert (Hp0 : p <> 0) by (destruct Hp; lia).
      apply (proj1 (Nat.mul_cancel_l _ _ p Hp0)).
      rewrite Hprod. ring.
Qed.

(** 12. FUNDAMENTAL THEOREM OF ARITHMETIC: existence + uniqueness *)
Theorem fundamental_theorem_of_arithmetic : forall n, 1 <= n ->
  (exists l, Forall is_prime l /\ prod_list l = n) /\
  (forall l1 l2, Forall is_prime l1 -> Forall is_prime l2 ->
     prod_list l1 = n -> prod_list l2 = n -> Permutation l1 l2).
Proof.
  intros n Hn. split.
  - apply factor_exists; exact Hn.
  - intros l1 l2 Ha Hb Hp1 Hp2.
    apply prime_factorization_unique; try assumption. rewrite Hp1, Hp2. reflexivity.
Qed.

(* ================================================================= *)
(*  Concrete examples (machine-checked)                               *)
(* ================================================================= *)

(** 13. 12 = 2 * 2 * 3, all prime *)
Example factorization_12 :
  Forall is_prime [2;2;3] /\ prod_list [2;2;3] = 12.
Proof.
  split.
  - constructor; [apply is_prime_2|].
    constructor; [apply is_prime_2|].
    constructor; [apply is_prime_3|]. constructor.
  - reflexivity.
Qed.

(** 14. uniqueness in action: any prime factorization of 12 is a permutation of [2;2;3] *)
Example factorization_12_unique : forall l,
  Forall is_prime l -> prod_list l = 12 -> Permutation l [2;2;3].
Proof.
  intros l Hl Hprod.
  destruct factorization_12 as [Hp12 _].
  apply (prime_factorization_unique l [2;2;3] Hl Hp12).
  rewrite Hprod. reflexivity.
Qed.
