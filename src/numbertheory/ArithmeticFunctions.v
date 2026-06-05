(** * ArithmeticFunctions.v — Arithmetic Functions as ToS System

    Theory of Systems — Number Theory layer (Part XIII)

    Elements: natural numbers; finite lists of divisors / coprime residues
    Roles:    phi / tau / sigma -> MEASURES on N (role-measures)
              a divisor        -> a constituent of n
    Rules:    each function is a finite count/sum over an explicit, decidable
              filter (computable at every n)
    Status:   phi(n), tau(n), sigma(n) are concrete naturals for each n

    The classical multiplicative arithmetic functions, none of which existed
    in the repository (grep-verified): Euler totient phi, divisor count tau,
    divisor sum sigma, the divisor list, and the key number-theoretic lemma
    prime_coprime_below (every 1<=k<p is coprime to a prime p), reusing
    PrimeFactorization.prime_divisor_1_or_self.

    Multiplicativity (phi/tau/sigma of a product of coprimes = product of
    values) is exhibited on concrete coprime instances (Element-side); the
    general theorem needs a CRT bijection and is left to a later layer.

    RELATED: stdlib/GCD.v (coprime), stdlib/Primes.v (is_prime, divides),
    zeta/MobiusSpin.v (mobius VALUES; multiplicativity not there).

    STATUS: 23 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
Import ListNotations.

From ToS Require Import stdlib.Primes.
From ToS Require Import stdlib.GCD.
From ToS Require Import numbertheory.PrimeFactorization.

(* ================================================================= *)
(*  The number-theoretic heart: residues below a prime are coprime    *)
(* ================================================================= *)

(** 1. every 1 <= k < p is coprime to a prime p *)
Lemma prime_coprime_below : forall p k,
  is_prime p -> 1 <= k -> k < p -> coprime p k.
Proof.
  intros p k Hp Hk1 Hkp. unfold coprime.
  destruct (prime_divisor_1_or_self p (gcd p k) Hp (gcd_divides_l p k)) as [H1 | Hpp].
  - exact H1.
  - exfalso.
    assert (Hpk : divides p k) by (rewrite <- Hpp; apply gcd_divides_r).
    assert (p <= k) by (apply (divides_le p k); [lia | exact Hpk]).
    lia.
Qed.

(* ================================================================= *)
(*  Divisors, tau, sigma, phi                                         *)
(* ================================================================= *)

Definition divisors (n : nat) : list nat :=
  filter (fun d => divides_bool d n) (seq 1 n).

Definition tau (n : nat) : nat := length (divisors n).

Definition sigma (n : nat) : nat := fold_right Nat.add 0 (divisors n).

Definition phi (n : nat) : nat :=
  length (filter (fun k => coprime_bool n k) (seq 1 n)).

(* ================================================================= *)
(*  Correctness of the divisor list                                   *)
(* ================================================================= *)

(** 2. membership in (divisors n) characterises the divisors of n *)
Lemma divisors_spec : forall n d,
  In d (divisors n) <-> divides d n /\ 1 <= d /\ d <= n.
Proof.
  intros n d. unfold divisors. rewrite filter_In, in_seq.
  split.
  - intros [Hseq Hdiv].
    apply (proj1 (divides_bool_correct d n ltac:(lia))) in Hdiv.
    split; [exact Hdiv | lia].
  - intros [Hdiv [Hd1 Hdn]].
    split; [lia |].
    apply (proj2 (divides_bool_correct d n ltac:(lia))). exact Hdiv.
Qed.

(* ================================================================= *)
(*  Machine-checked values                                            *)
(* ================================================================= *)

(** 3. the divisor list of 12 *)
Example divisors_12 : divisors 12 = [1; 2; 3; 4; 6; 12].
Proof. vm_compute. reflexivity. Qed.

(** 4. tau(12) = 6 *)
Example tau_12 : tau 12 = 6.
Proof. vm_compute. reflexivity. Qed.

(** 5. sigma(12) = 28 *)
Example sigma_12 : sigma 12 = 28.
Proof. vm_compute. reflexivity. Qed.

(** 6. phi(12) = 4 (the residues 1,5,7,11) *)
Example phi_12 : phi 12 = 4.
Proof. vm_compute. reflexivity. Qed.

(** 7. base values at 1 *)
Example tau_1 : tau 1 = 1.   Proof. vm_compute. reflexivity. Qed.
Example sigma_1 : sigma 1 = 1. Proof. vm_compute. reflexivity. Qed.
Example phi_1 : phi 1 = 1.   Proof. vm_compute. reflexivity. Qed.

(** 8. prime values: tau(7)=2, sigma(7)=8, phi(7)=6 *)
Example tau_7 : tau 7 = 2.   Proof. vm_compute. reflexivity. Qed.
Example sigma_7 : sigma 7 = 8. Proof. vm_compute. reflexivity. Qed.
Example phi_7 : phi 7 = 6.   Proof. vm_compute. reflexivity. Qed.

(** 9. phi at a prime power: phi(8) = 4 = 8 - 4 = 2^3 - 2^2 *)
Example phi_8 : phi 8 = 4.   Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(*  Multiplicativity on coprime instances (Element-side)             *)
(* ================================================================= *)

(** 10. tau(12) = tau(4) * tau(3),  with gcd(4,3)=1 *)
Example tau_mult_12 : tau 12 = tau 4 * tau 3.
Proof. vm_compute. reflexivity. Qed.

(** 11. sigma(12) = sigma(4) * sigma(3) *)
Example sigma_mult_12 : sigma 12 = sigma 4 * sigma 3.
Proof. vm_compute. reflexivity. Qed.

(** 12. phi(12) = phi(4) * phi(3) *)
Example phi_mult_12 : phi 12 = phi 4 * phi 3.
Proof. vm_compute. reflexivity. Qed.

(** 13. another coprime instance: phi(15) = phi(3) * phi(5) = 2 * 4 = 8 *)
Example phi_mult_15 : phi 15 = phi 3 * phi 5.
Proof. vm_compute. reflexivity. Qed.

(** 14. and tau(15) = tau(3) * tau(5) = 2 * 2 = 4 *)
Example tau_mult_15 : tau 15 = tau 3 * tau 5.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(*  Coprimality structure of residues mod a prime                    *)
(* ================================================================= *)

(** 15. concrete: 1,2,3,4 are all coprime to 5 *)
Example coprime_below_5 :
  coprime 5 1 /\ coprime 5 2 /\ coprime 5 3 /\ coprime 5 4.
Proof. repeat split; reflexivity. Qed.

(** 16. each of them follows from the general lemma too *)
Example coprime_below_5_general : coprime 5 4.
Proof. apply prime_coprime_below; [apply is_prime_bool_true_is_prime; reflexivity | lia | lia]. Qed.

(* ================================================================= *)
(*  Elementary facts about the divisor list                          *)
(* ================================================================= *)

(** 17. 1 always divides n (n>=1), so 1 is a divisor *)
Lemma one_in_divisors : forall n, 1 <= n -> In 1 (divisors n).
Proof.
  intros n Hn. apply divisors_spec. split; [apply divides_1 | lia].
Qed.

(** 18. n divides itself, so n is among its divisors *)
Lemma self_in_divisors : forall n, 1 <= n -> In n (divisors n).
Proof.
  intros n Hn. apply divisors_spec. split; [apply divides_refl; lia | lia].
Qed.

(** 19. hence every n>=1 has at least one divisor (tau n >= 1) *)
Lemma tau_ge_1 : forall n, 1 <= n -> 1 <= tau n.
Proof.
  intros n Hn. unfold tau.
  destruct (divisors n) as [|x l] eqn:E.
  - exfalso. pose proof (one_in_divisors n Hn) as Hin. rewrite E in Hin. exact Hin.
  - simpl. lia.
Qed.
