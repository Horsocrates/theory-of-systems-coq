(** * PrimeCounting.v — The Prime-Counting Function pi(x) as ToS System

    Theory of Systems — Number Theory layer (Part XIII)

    Elements: natural numbers; the finite list (sieve x) of primes up to x
    Roles:    pi(x) -> a COUNTER (role-process): a concrete number at each x
    Rules:    pi(x) = length of the decidable sieve of [2, x]
    Status:   pi(x) is computable and monotone; unbounded (Euclid, N2)

    The arithmetic prime-counting function pi(x), grounded directly on the
    repo's sieve (stdlib/Primes.v). Machine-checks the small table from the
    book (pi(10)=4, pi(100)=25, pi(1000)=168), proves the sieve-membership
    characterisation, and monotonicity. Unboundedness is the content of
    EuclidInfinitude.exists_larger_prime (cited there).

    RELATED: stdlib/Primes.v (sieve, is_prime_bool), zeta/PrimeSumBounds.v
    (a prime_count tied to Chebyshev bounds), numbertheory/EuclidInfinitude.v
    (pi is unbounded).

    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
Import ListNotations.

From ToS Require Import stdlib.Primes.

(* ================================================================= *)
(*  Definition                                                        *)
(* ================================================================= *)

(** pi x = number of primes p with 2 <= p <= x *)
Definition pi (x : nat) : nat := length (sieve x).

(* ================================================================= *)
(*  Machine-checked values (the book's table, 13.1.4)                 *)
(* ================================================================= *)

(** 1. pi(10) = 4   (primes 2,3,5,7) *)
Example pi_10 : pi 10 = 4.
Proof. vm_compute. reflexivity. Qed.

(** 2. pi(30) = 10 *)
Example pi_30 : pi 30 = 10.
Proof. vm_compute. reflexivity. Qed.

(** 3. pi(100) = 25 *)
Example pi_100 : pi 100 = 25.
Proof. vm_compute. reflexivity. Qed.

(** 4. pi(1000) = 168 *)
Example pi_1000 : pi 1000 = 168.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(*  Sieve-membership characterisation                                 *)
(* ================================================================= *)

(** 5. p is in the sieve of x iff p is a (boolean) prime in [2, x] *)
Lemma in_sieve_iff : forall x p,
  In p (sieve x) <-> (2 <= p /\ p <= x) /\ is_prime_bool p = true.
Proof.
  intros x p. unfold sieve. rewrite filter_In, in_seq.
  split.
  - intros [Hseq Hpb]. split; [lia | exact Hpb].
  - intros [[Hlo Hhi] Hpb]. split; [lia | exact Hpb].
Qed.

(* ================================================================= *)
(*  Monotonicity                                                      *)
(* ================================================================= *)

(** 6. pi is monotone non-decreasing *)
Lemma pi_monotone : forall x y, x <= y -> pi x <= pi y.
Proof.
  intros x y Hxy. unfold pi, sieve.
  destruct x as [|x'].
  - simpl. lia.
  - replace (y - 1) with ((S x' - 1) + (y - S x')) by lia.
    rewrite seq_app, filter_app, length_app. lia.
Qed.

(* ================================================================= *)
(*  Lower bounds                                                      *)
(* ================================================================= *)

(** 7. 2 is counted as soon as x >= 2 *)
Lemma two_in_sieve : forall x, 2 <= x -> In 2 (sieve x).
Proof.
  intros x Hx. apply in_sieve_iff. split; [lia | reflexivity].
Qed.

(** 8. hence pi(x) >= 1 for x >= 2 *)
Lemma pi_ge_1 : forall x, 2 <= x -> 1 <= pi x.
Proof.
  intros x Hx. unfold pi.
  destruct (sieve x) as [|a l] eqn:E.
  - exfalso. pose proof (two_in_sieve x Hx) as Hin. rewrite E in Hin. exact Hin.
  - simpl. lia.
Qed.

(** 9. concrete growth: pi(1000) far exceeds pi(10) *)
Example pi_grows : pi 10 < pi 1000.
Proof. vm_compute. lia. Qed.
