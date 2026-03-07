(** * Primes.v — Prime Numbers as ToS System

    Theory of Systems — Verified Standard Library (Batch 3)

    Elements: natural numbers
    Roles:    prime → Indivisible, composite → Factorable, 1 → Unit
    Rules:    divisibility (constitution: divisible only by 1 and self)
    Status:   prime | composite | unit

    Connection: ConstitutionChecking.v (is_prime is a decidable constitution)

    STATUS: 21 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* ================================================================= *)
(*  Divisibility                                                       *)
(* ================================================================= *)

Definition divides (d n : nat) : Prop := exists k, n = d * k.

Definition divides_bool (d n : nat) : bool := Nat.eqb (Nat.modulo n d) 0.

(* ================================================================= *)
(*  Primality                                                          *)
(* ================================================================= *)

Definition is_prime (n : nat) : Prop :=
  2 <= n /\ forall d, 2 <= d -> d < n -> ~ divides d n.

(* Check if any number in range [lo, lo+count) divides n *)
Definition has_divisor_in_range (lo count n : nat) : bool :=
  existsb (fun d => divides_bool d n) (seq lo count).

(* Decidable primality test: check divisors 2..(n-1) *)
Definition is_prime_bool (n : nat) : bool :=
  (2 <=? n) && negb (has_divisor_in_range 2 (n - 2) n).

(* Sieve: filter primes up to n *)
Definition sieve (n : nat) : list nat :=
  filter is_prime_bool (seq 2 (n - 1)).

(* Smallest factor by trial division *)
Fixpoint smallest_factor_aux (fuel n d : nat) : nat :=
  match fuel with
  | O => n
  | S f' =>
    if n <? d * d then n
    else if divides_bool d n then d
    else smallest_factor_aux f' n (S d)
  end.

Definition smallest_factor (n : nat) : nat := smallest_factor_aux n n 2.

(* ================================================================= *)
(*  Divisibility Lemmas                                                *)
(* ================================================================= *)

(** 1. divides_bool_correct *)
Lemma divides_bool_correct : forall d n,
  d <> 0 -> (divides_bool d n = true <-> divides d n).
Proof.
  intros d n Hd. unfold divides_bool, divides.
  rewrite Nat.eqb_eq.
  split.
  - intro Hmod.
    exists (Nat.div n d).
    pose proof (Nat.div_mod n d Hd) as Hdm.
    rewrite Hmod in Hdm. rewrite Nat.add_0_r in Hdm.
    exact Hdm.
  - intros [k Hk].
    subst n.
    rewrite Nat.mul_comm.
    apply Nat.mod_mul. assumption.
Qed.

(** 2. divides_refl *)
Lemma divides_refl : forall n, n <> 0 -> divides n n.
Proof.
  intros n Hn. exists 1. lia.
Qed.

(** 3. divides_1 *)
Lemma divides_1 : forall n, divides 1 n.
Proof.
  intro n. exists n. lia.
Qed.

(** 4. divides_0 *)
Lemma divides_0 : forall d, divides d 0.
Proof.
  intro d. exists 0. lia.
Qed.

(** 5. divides_le *)
Lemma divides_le : forall d n, n <> 0 -> divides d n -> d <= n.
Proof.
  intros d n Hn [k Hk].
  destruct k.
  - lia.
  - nia.
Qed.

(** 6. divides_trans *)
Lemma divides_trans : forall a b c,
  divides a b -> divides b c -> divides a c.
Proof.
  intros a b c [k1 Hk1] [k2 Hk2].
  exists (k1 * k2). nia.
Qed.

(* ================================================================= *)
(*  Computational Primality Tests                                      *)
(* ================================================================= *)

(** 7. is_prime_bool_2 *)
Lemma is_prime_bool_2 : is_prime_bool 2 = true.
Proof. reflexivity. Qed.

(** 8. is_prime_bool_3 *)
Lemma is_prime_bool_3 : is_prime_bool 3 = true.
Proof. reflexivity. Qed.

(** 9. is_prime_bool_4 *)
Lemma is_prime_bool_4 : is_prime_bool 4 = false.
Proof. reflexivity. Qed.

(** 10. is_prime_bool_5 *)
Lemma is_prime_bool_5 : is_prime_bool 5 = true.
Proof. reflexivity. Qed.

(** 11. not_prime_0 *)
Lemma not_prime_0 : is_prime_bool 0 = false.
Proof. reflexivity. Qed.

(** 12. not_prime_1 *)
Lemma not_prime_1 : is_prime_bool 1 = false.
Proof. reflexivity. Qed.

(* ================================================================= *)
(*  Sieve Tests                                                        *)
(* ================================================================= *)

(** 13. sieve_5 *)
Lemma sieve_5 : sieve 6 = [2; 3; 5].
Proof. reflexivity. Qed.

(** 14. sieve_10 *)
Lemma sieve_10 : sieve 8 = [2; 3; 5; 7].
Proof. reflexivity. Qed.

(* ================================================================= *)
(*  Structural Primality Lemmas                                        *)
(* ================================================================= *)

(** 15. prime_ge_2 *)
Lemma prime_ge_2 : forall n, is_prime_bool n = true -> 2 <= n.
Proof.
  intros n H. unfold is_prime_bool in H.
  apply andb_true_iff in H. destruct H as [H _].
  apply Nat.leb_le in H. exact H.
Qed.

(* ================================================================= *)
(*  Smallest Factor Tests                                              *)
(* ================================================================= *)

(** 16. smallest_factor_2 *)
Lemma smallest_factor_2 : smallest_factor 2 = 2.
Proof. reflexivity. Qed.

(** 17. smallest_factor_6 *)
Lemma smallest_factor_6 : smallest_factor 6 = 2.
Proof. reflexivity. Qed.

(** 18. smallest_factor_7 *)
Lemma smallest_factor_7 : smallest_factor 7 = 7.
Proof. reflexivity. Qed.

(* ================================================================= *)
(*  Key Theorems                                                       *)
(* ================================================================= *)

(** 19. composite_has_small_factor *)
Lemma composite_has_small_factor : forall n,
  2 <= n -> is_prime_bool n = false ->
  exists d, 2 <= d /\ d < n /\ divides_bool d n = true.
Proof.
  intros n Hn Hcomp.
  unfold is_prime_bool in Hcomp.
  apply andb_false_iff in Hcomp.
  destruct Hcomp as [Hcomp | Hcomp].
  - (* (2 <=? n) = false — contradicts 2 <= n *)
    apply Nat.leb_gt in Hcomp. lia.
  - (* negb (has_divisor_in_range ...) = false *)
    apply negb_false_iff in Hcomp.
    unfold has_divisor_in_range in Hcomp.
    apply existsb_exists in Hcomp.
    destruct Hcomp as [d [Hin Hdiv]].
    exists d. split; [|split].
    + apply in_seq in Hin. lia.
    + apply in_seq in Hin. lia.
    + exact Hdiv.
Qed.

(** 20. prime_not_composite *)
Lemma prime_not_composite : forall n,
  is_prime_bool n = true ->
  forall d, 2 <= d -> d < n -> divides_bool d n = false.
Proof.
  intros n Hprime d Hd Hdn.
  unfold is_prime_bool in Hprime.
  apply andb_true_iff in Hprime.
  destruct Hprime as [Hge Hnodiv].
  apply negb_true_iff in Hnodiv.
  unfold has_divisor_in_range in Hnodiv.
  (* existsb ... = false means forall x in list, f x = false *)
  assert (Hin: In d (seq 2 (n - 2))).
  { apply in_seq. lia. }
  (* From existsb = false, we need: for all elements, the predicate is false *)
  induction (seq 2 (n - 2)) as [|x xs IH].
  - destruct Hin.
  - simpl in Hnodiv. apply orb_false_iff in Hnodiv.
    destruct Hnodiv as [Hx Hrest].
    destruct Hin as [Heq | Hin'].
    + subst x. exact Hx.
    + apply IH; assumption.
Qed.

(** 21. divides_mul_l *)
Lemma divides_mul_l : forall a b, divides a (a * b).
Proof.
  intros a b. exists b. reflexivity.
Qed.
