(** * ModularArith.v — Modular Arithmetic as ToS System

    Theory of Systems — Verified Standard Library (Batch 3)

    Elements: natural numbers modulo m
    Roles:    residue -> Representative, modulus -> Granularity
    Rules:    modular operations (constitution: equality up to multiples)
    Status:   congruent | incongruent

    Connection: Primes.v (prime modulus -> field)
    Connection: GCD.v (coprime residues -> invertible)

    STATUS: 18 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.

From ToS Require Import stdlib.Primes.
From ToS Require Import stdlib.GCD.

(* ================================================================= *)
(*  Definitions                                                        *)
(* ================================================================= *)

(** Two naturals are congruent mod m when they have the same remainder *)
Definition congruent (a b m : nat) : Prop :=
  Nat.modulo a m = Nat.modulo b m.

(** Boolean version of congruence *)
Definition congruent_bool (a b m : nat) : bool :=
  Nat.eqb (Nat.modulo a m) (Nat.modulo b m).

(** Addition in Z/mZ *)
Definition zmod_add (a b m : nat) : nat :=
  Nat.modulo (a + b) m.

(** Multiplication in Z/mZ *)
Definition zmod_mul (a b m : nat) : nat :=
  Nat.modulo (a * b) m.

(** Zero element of Z/mZ *)
Definition zmod_zero (m : nat) : nat := 0.

(** One element of Z/mZ *)
Definition zmod_one (m : nat) : nat := Nat.modulo 1 m.

(* ================================================================= *)
(*  Congruence is an Equivalence Relation                              *)
(* ================================================================= *)

(** 1. congruent_refl — congruence is reflexive *)
Lemma congruent_refl : forall a m, congruent a a m.
Proof.
  intros a m. unfold congruent. reflexivity.
Qed.

(** 2. congruent_sym — congruence is symmetric *)
Lemma congruent_sym : forall a b m,
  congruent a b m -> congruent b a m.
Proof.
  intros a b m H. unfold congruent in *. symmetry. exact H.
Qed.

(** 3. congruent_trans — congruence is transitive *)
Lemma congruent_trans : forall a b c m,
  congruent a b m -> congruent b c m -> congruent a c m.
Proof.
  intros a b c m Hab Hbc. unfold congruent in *.
  rewrite Hab. exact Hbc.
Qed.

(* ================================================================= *)
(*  Boolean Correctness                                                *)
(* ================================================================= *)

(** 4. congruent_bool_correct — boolean test reflects congruence *)
Lemma congruent_bool_correct : forall a b m,
  m <> 0 -> (congruent_bool a b m = true <-> congruent a b m).
Proof.
  intros a b m Hm. unfold congruent_bool, congruent.
  rewrite Nat.eqb_eq. tauto.
Qed.

(* ================================================================= *)
(*  Z/mZ Commutativity                                                 *)
(* ================================================================= *)

(** 5. zmod_add_comm — addition in Z/mZ is commutative *)
Lemma zmod_add_comm : forall a b m,
  zmod_add a b m = zmod_add b a m.
Proof.
  intros a b m. unfold zmod_add.
  rewrite Nat.add_comm. reflexivity.
Qed.

(** 6. zmod_mul_comm — multiplication in Z/mZ is commutative *)
Lemma zmod_mul_comm : forall a b m,
  zmod_mul a b m = zmod_mul b a m.
Proof.
  intros a b m. unfold zmod_mul.
  rewrite Nat.mul_comm. reflexivity.
Qed.

(* ================================================================= *)
(*  Z/mZ Identity Laws                                                 *)
(* ================================================================= *)

(** 7. zmod_add_0_l — zero is left identity for modular addition *)
Lemma zmod_add_0_l : forall b m,
  zmod_add 0 b m = Nat.modulo b m.
Proof.
  intros b m. unfold zmod_add. simpl. reflexivity.
Qed.

(** 8. zmod_mul_0_l — zero annihilates in modular multiplication *)
Lemma zmod_mul_0_l : forall b m,
  zmod_mul 0 b m = 0.
Proof.
  intros b m. unfold zmod_mul. rewrite Nat.mul_0_l.
  destruct m. reflexivity. apply Nat.mod_small. lia.
Qed.

(** 9. zmod_mul_1_l — one is left identity for modular multiplication *)
Lemma zmod_mul_1_l : forall b m,
  m <> 0 -> zmod_mul 1 b m = Nat.modulo b m.
Proof.
  intros b m Hm. unfold zmod_mul.
  rewrite Nat.mul_1_l. reflexivity.
Qed.

(* ================================================================= *)
(*  Z/mZ Associativity                                                 *)
(* ================================================================= *)

(** Helper: (a mod m + b) mod m = (a + b) mod m *)
Lemma add_mod_idemp_l : forall a b m,
  m <> 0 -> Nat.modulo (Nat.modulo a m + b) m = Nat.modulo (a + b) m.
Proof.
  intros a b m Hm.
  assert (Hd: a = m * (a / m) + a mod m).
  { apply Nat.div_mod. exact Hm. }
  assert (Hmod_bound: a mod m < m).
  { apply Nat.mod_upper_bound. exact Hm. }
  (* a + b = (a / m) * m + (a mod m + b) *)
  replace (a + b) with ((a mod m + b) + (a / m) * m) by lia.
  rewrite Nat.mod_add by exact Hm.
  reflexivity.
Qed.

(** Helper: (a + b mod m) mod m = (a + b) mod m *)
Lemma add_mod_idemp_r : forall a b m,
  m <> 0 -> Nat.modulo (a + Nat.modulo b m) m = Nat.modulo (a + b) m.
Proof.
  intros a b m Hm.
  rewrite Nat.add_comm. rewrite add_mod_idemp_l by exact Hm.
  rewrite Nat.add_comm. reflexivity.
Qed.

(** 10. zmod_add_assoc — addition in Z/mZ is associative *)
Lemma zmod_add_assoc : forall a b c m,
  m <> 0 ->
  zmod_add (zmod_add a b m) c m = zmod_add a (zmod_add b c m) m.
Proof.
  intros a b c m Hm. unfold zmod_add.
  rewrite add_mod_idemp_l by exact Hm.
  rewrite add_mod_idemp_r by exact Hm.
  rewrite Nat.add_assoc. reflexivity.
Qed.

(** Helper: (a mod m * b) mod m = (a * b) mod m *)
Lemma mul_mod_idemp_l : forall a b m,
  m <> 0 -> Nat.modulo (Nat.modulo a m * b) m = Nat.modulo (a * b) m.
Proof.
  intros a b m Hm.
  assert (Hd: a = m * (a / m) + a mod m).
  { apply Nat.div_mod. exact Hm. }
  replace (a * b) with (a mod m * b + (a / m) * b * m) by lia.
  rewrite Nat.mod_add by exact Hm.
  reflexivity.
Qed.

(** Helper: (a * (b mod m)) mod m = (a * b) mod m *)
Lemma mul_mod_idemp_r : forall a b m,
  m <> 0 -> Nat.modulo (a * Nat.modulo b m) m = Nat.modulo (a * b) m.
Proof.
  intros a b m Hm.
  rewrite Nat.mul_comm. rewrite mul_mod_idemp_l by exact Hm.
  rewrite Nat.mul_comm. reflexivity.
Qed.

(** 11. zmod_mul_assoc — multiplication in Z/mZ is associative *)
Lemma zmod_mul_assoc : forall a b c m,
  m <> 0 ->
  zmod_mul (zmod_mul a b m) c m = zmod_mul a (zmod_mul b c m) m.
Proof.
  intros a b c m Hm. unfold zmod_mul.
  rewrite mul_mod_idemp_l by exact Hm.
  rewrite mul_mod_idemp_r by exact Hm.
  rewrite Nat.mul_assoc. reflexivity.
Qed.

(* ================================================================= *)
(*  Congruence Compatibility                                           *)
(* ================================================================= *)

(** 12. congruent_add — congruence is compatible with addition *)
Lemma congruent_add : forall a b c d m,
  m <> 0 ->
  congruent a b m -> congruent c d m ->
  congruent (a + c) (b + d) m.
Proof.
  intros a b c d m Hm Hab Hcd.
  unfold congruent in *.
  (* (a+c) mod m = ((a mod m) + (c mod m)) mod m *)
  rewrite <- add_mod_idemp_l by exact Hm.
  rewrite <- add_mod_idemp_r by exact Hm.
  rewrite Hab, Hcd.
  rewrite add_mod_idemp_r by exact Hm.
  rewrite add_mod_idemp_l by exact Hm.
  reflexivity.
Qed.

(** 13. congruent_mul — congruence is compatible with multiplication *)
Lemma congruent_mul : forall a b c d m,
  m <> 0 ->
  congruent a b m -> congruent c d m ->
  congruent (a * c) (b * d) m.
Proof.
  intros a b c d m Hm Hab Hcd.
  unfold congruent in *.
  rewrite <- mul_mod_idemp_l by exact Hm.
  rewrite <- mul_mod_idemp_r by exact Hm.
  rewrite Hab, Hcd.
  rewrite mul_mod_idemp_r by exact Hm.
  rewrite mul_mod_idemp_l by exact Hm.
  reflexivity.
Qed.

(* ================================================================= *)
(*  Idempotence of mod                                                 *)
(* ================================================================= *)

(** 14. mod_mod — modular reduction is idempotent *)
Lemma mod_mod : forall a m,
  m <> 0 -> Nat.modulo (Nat.modulo a m) m = Nat.modulo a m.
Proof.
  intros a m Hm.
  apply Nat.mod_small.
  apply Nat.mod_upper_bound. exact Hm.
Qed.

(* ================================================================= *)
(*  Self-congruence of the Modulus                                     *)
(* ================================================================= *)

(** 15. congruent_mod_self — m is congruent to 0 modulo m *)
Lemma congruent_mod_self : forall m, congruent m 0 m.
Proof.
  intro m. unfold congruent.
  destruct m as [| m'].
  - (* m = 0: 0 mod 0 = 0 mod 0 *)
    simpl. reflexivity.
  - (* m = S m': (S m') mod (S m') = 0 mod (S m') *)
    rewrite Nat.mod_same by lia.
    symmetry. apply Nat.mod_small. lia.
Qed.

(* ================================================================= *)
(*  Computational Examples                                             *)
(* ================================================================= *)

(** 16. zmod_example_add — 3 + 4 = 2 (mod 5) *)
Lemma zmod_example_add : zmod_add 3 4 5 = 2.
Proof. reflexivity. Qed.

(** 17. zmod_example_mul — 3 * 4 = 2 (mod 5) *)
Lemma zmod_example_mul : zmod_mul 3 4 5 = 2.
Proof. reflexivity. Qed.

(** 18. congruent_example — 7 ≡ 2 (mod 5) *)
Lemma congruent_example : congruent 7 2 5.
Proof. reflexivity. Qed.
