(** * VonMangoldt.v — The von Mangoldt Function as ToS System

    Theory of Systems — Number Theory layer (Part XIII)

    Elements: natural numbers; prime powers
    Roles:    Lambda -> a SELECTOR (it isolates the prime-power skeleton of N)
    Rules:    Lambda(n) = log p  iff  n = p^k (k>=1), else 0
    Status:   computable; the summatory psi accumulates it

    The von Mangoldt function, central to Chapter 13.6 and to the link with
    -zeta'/zeta = sum_n Lambda(n)/n^s (zeta/LogZeta.v). To stay over N (no
    transcendental log), we formalize the EXPONENTIATED form:
        Lambda_exp(n) = p  if n = p^k (k>=1),  else 1   (i.e. e^{Lambda(n)})
    so that the classical identity  sum_{d|n} Lambda(d) = log n  becomes the
    exact natural-number identity  prod_{d|n} Lambda_exp(d) = n.  That identity
    is machine-checked here for every n <= 20 (Element-side); the general
    statement is the multiplicative content used by LogZeta.

    RELATED: zeta/LogZeta.v (uses Lambda inside the Dirichlet series for
    -zeta'/zeta), zeta/PrimeSumBounds.v (Chebyshev theta/psi), Primes.v
    (smallest_factor), numbertheory/ArithmeticFunctions.v (divisors).

    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
Import ListNotations.

From ToS Require Import stdlib.Primes.
From ToS Require Import numbertheory.ArithmeticFunctions.

(* ================================================================= *)
(*  Prime-power detection and the exponentiated von Mangoldt          *)
(* ================================================================= *)

(** is_pow_aux fuel p n : does n reduce to 1 by repeatedly dividing by p? *)
Fixpoint is_pow_aux (fuel p n : nat) : bool :=
  match fuel with
  | O => false
  | S f =>
    if Nat.eqb n 1 then true
    else if divides_bool p n then is_pow_aux f p (Nat.div n p)
    else false
  end.

(** n is a prime power p^k (k>=1) iff it reduces to 1 by dividing by its
    smallest prime factor *)
Definition is_prime_power_bool (n : nat) : bool :=
  (2 <=? n) && is_pow_aux n (smallest_factor n) n.

(** exponentiated von Mangoldt: e^{Lambda(n)} *)
Definition Lambda_exp (n : nat) : nat :=
  if is_prime_power_bool n then smallest_factor n else 1.

(** product of Lambda_exp over the divisors of n  ( = e^{sum_{d|n} Lambda(d)} ) *)
Definition mangoldt_prod (n : nat) : nat :=
  fold_right Nat.mul 1 (map Lambda_exp (divisors n)).

(** exponentiated summatory function  e^{psi(x)} = prod_{n<=x} Lambda_exp(n) *)
Definition psi_exp (x : nat) : nat :=
  fold_right Nat.mul 1 (map Lambda_exp (seq 1 x)).

(* ================================================================= *)
(*  Values of Lambda_exp (machine-checked)                            *)
(* ================================================================= *)

(** 1. unit: Lambda_exp(1) = 1   (Lambda(1) = 0) *)
Example Lambda_1 : Lambda_exp 1 = 1.  Proof. vm_compute. reflexivity. Qed.

(** 2. primes: Lambda_exp(p) = p *)
Example Lambda_2 : Lambda_exp 2 = 2.  Proof. vm_compute. reflexivity. Qed.
Example Lambda_3 : Lambda_exp 3 = 3.  Proof. vm_compute. reflexivity. Qed.

(** 3. prime powers: Lambda_exp(p^k) = p *)
Example Lambda_4 : Lambda_exp 4 = 2.  Proof. vm_compute. reflexivity. Qed.   (* 2^2 *)
Example Lambda_8 : Lambda_exp 8 = 2.  Proof. vm_compute. reflexivity. Qed.   (* 2^3 *)
Example Lambda_9 : Lambda_exp 9 = 3.  Proof. vm_compute. reflexivity. Qed.   (* 3^2 *)

(** 4. non-prime-powers: Lambda_exp(n) = 1   (Lambda(n) = 0) *)
Example Lambda_6 : Lambda_exp 6 = 1.  Proof. vm_compute. reflexivity. Qed.
Example Lambda_12 : Lambda_exp 12 = 1. Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(*  The fundamental identity  prod_{d|n} Lambda_exp(d) = n            *)
(* ================================================================= *)

(** 5. concrete: 12 = prod over divisors [1;2;3;4;6;12] of Lambda_exp *)
Example mangoldt_prod_12 : mangoldt_prod 12 = 12.
Proof. vm_compute. reflexivity. Qed.

(** 6. concrete: prime power 8 *)
Example mangoldt_prod_8 : mangoldt_prod 8 = 8.
Proof. vm_compute. reflexivity. Qed.

(** 7. THE identity for every n in [1, 20]:  prod_{d|n} Lambda_exp(d) = n *)
Example mangoldt_identity_upto_20 :
  forall n, In n (seq 1 20) -> mangoldt_prod n = n.
Proof.
  intros n H. simpl in H.
  repeat (destruct H as [H | H]; [subst n; vm_compute; reflexivity | ]).
  destruct H.
Qed.

(* ================================================================= *)
(*  Summatory function psi (exponentiated)                            *)
(* ================================================================= *)

(** 8. e^{psi(1)} = 1 *)
Example psi_exp_1 : psi_exp 1 = 1.   Proof. vm_compute. reflexivity. Qed.

(** 9. e^{psi(4)} = 1*2*3*2 = 12  (Lambda over 1,2,3,4) *)
Example psi_exp_4 : psi_exp 4 = 12.  Proof. vm_compute. reflexivity. Qed.

(** 10. e^{psi(10)} accumulates the prime-power skeleton up to 10 *)
Example psi_exp_10 : psi_exp 10 = 2 * 3 * 2 * 5 * 7 * 2 * 3.
Proof. vm_compute. reflexivity. Qed.

(** 11. psi is multiplicatively monotone: e^{psi(4)} divides e^{psi(10)} pattern —
    here simply that the skeleton up to 10 strictly exceeds that up to 4 *)
Example psi_exp_grows : psi_exp 4 < psi_exp 10.
Proof. vm_compute. lia. Qed.
