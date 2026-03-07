(** * GCD.v — Greatest Common Divisor as ToS System

    Theory of Systems — Verified Standard Library (Batch 3)

    Elements: natural numbers
    Roles:    gcd -> CommonMeasure, coprime -> Independent
    Rules:    Euclidean algorithm (constitution: maximal common divisor)
    Status:   coprime | sharing_factor

    Connection: Primes.v (prime = coprime with all smaller)

    STATUS: 22 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.

From ToS Require Import stdlib.Primes.

(* ================================================================= *)
(*  Definitions                                                        *)
(* ================================================================= *)

(** GCD — wrapper around stdlib Nat.gcd *)
Definition gcd (a b : nat) : nat := Nat.gcd a b.

(** Pedagogical GCD with explicit fuel (Euclidean algorithm) *)
Fixpoint gcd_fuel (fuel a b : nat) : nat :=
  match fuel with
  | O => a
  | S f' =>
    match b with
    | O => a
    | _ => gcd_fuel f' b (Nat.modulo a b)
    end
  end.

(** Coprimality *)
Definition coprime (a b : nat) : Prop := gcd a b = 1.

(** Decidable coprimality *)
Definition coprime_bool (a b : nat) : bool := Nat.eqb (gcd a b) 1.

(** Least Common Multiple *)
Definition lcm (a b : nat) : nat :=
  match gcd a b with
  | O => 0
  | g => (a * b) / g
  end.

(* ================================================================= *)
(*  GCD Basic Properties                                               *)
(* ================================================================= *)

(** 1. gcd_0_r *)
Lemma gcd_0_r : forall a, gcd a 0 = a.
Proof.
  intro a. unfold gcd. apply Nat.gcd_0_r.
Qed.

(** 2. gcd_0_l *)
Lemma gcd_0_l : forall b, gcd 0 b = b.
Proof.
  intro b. unfold gcd. apply Nat.gcd_0_l.
Qed.

(** 3. gcd_diag *)
Lemma gcd_diag : forall a, gcd a a = a.
Proof.
  intro a. unfold gcd. apply Nat.gcd_diag.
Qed.

(** 4. gcd_comm *)
Lemma gcd_comm : forall a b, gcd a b = gcd b a.
Proof.
  intros a b. unfold gcd. apply Nat.gcd_comm.
Qed.

(** 5. gcd_assoc *)
Lemma gcd_assoc : forall a b c, gcd a (gcd b c) = gcd (gcd a b) c.
Proof.
  intros a b c. unfold gcd. apply Nat.gcd_assoc.
Qed.

(** 6. gcd_1_l *)
Lemma gcd_1_l : forall b, gcd 1 b = 1.
Proof.
  intro b. unfold gcd. simpl. reflexivity.
Qed.

(** 7. gcd_1_r *)
Lemma gcd_1_r : forall a, gcd a 1 = 1.
Proof.
  intro a. unfold gcd. rewrite Nat.gcd_comm. simpl. reflexivity.
Qed.

(* ================================================================= *)
(*  GCD and Divisibility                                               *)
(* ================================================================= *)

(** 8. gcd_divides_l — gcd divides left argument *)
Lemma gcd_divides_l : forall a b, divides (gcd a b) a.
Proof.
  intros a b.
  pose proof (Nat.gcd_divide_l a b) as [k Hk].
  exists k. rewrite Nat.mul_comm. exact Hk.
Qed.

(** 9. gcd_divides_r — gcd divides right argument *)
Lemma gcd_divides_r : forall a b, divides (gcd a b) b.
Proof.
  intros a b.
  pose proof (Nat.gcd_divide_r a b) as [k Hk].
  exists k. rewrite Nat.mul_comm. exact Hk.
Qed.

(* ================================================================= *)
(*  Coprimality                                                        *)
(* ================================================================= *)

(** 10. coprime_comm *)
Lemma coprime_comm : forall a b, coprime a b -> coprime b a.
Proof.
  intros a b H. unfold coprime in *. rewrite gcd_comm. exact H.
Qed.

(** 11. coprime_1_l *)
Lemma coprime_1_l : forall b, coprime 1 b.
Proof.
  intro b. unfold coprime. apply gcd_1_l.
Qed.

(** 12. coprime_1_r *)
Lemma coprime_1_r : forall a, coprime a 1.
Proof.
  intro a. unfold coprime. apply gcd_1_r.
Qed.

(* ================================================================= *)
(*  GCD Fuel (Pedagogical Euclidean Algorithm)                         *)
(* ================================================================= *)

(** 13. gcd_fuel_example_6_4 *)
Lemma gcd_fuel_example_6_4 : gcd_fuel 10 6 4 = 2.
Proof. reflexivity. Qed.

(** 14. gcd_fuel_example_12_8 *)
Lemma gcd_fuel_example_12_8 : gcd_fuel 10 12 8 = 4.
Proof. reflexivity. Qed.

(* ================================================================= *)
(*  GCD Computational Examples                                         *)
(* ================================================================= *)

(** 15. gcd_example_6_4 *)
Lemma gcd_example_6_4 : gcd 6 4 = 2.
Proof. reflexivity. Qed.

(** 16. gcd_example_12_8 *)
Lemma gcd_example_12_8 : gcd 12 8 = 4.
Proof. reflexivity. Qed.

(** 17. coprime_example *)
Lemma coprime_example : coprime 3 5.
Proof. reflexivity. Qed.

(* ================================================================= *)
(*  Coprime Boolean Correctness                                        *)
(* ================================================================= *)

(** 18. coprime_bool_correct — coprime_bool reflects coprime *)
Lemma coprime_bool_correct : forall a b,
  coprime_bool a b = true <-> coprime a b.
Proof.
  intros a b. unfold coprime_bool, coprime.
  rewrite Nat.eqb_eq. tauto.
Qed.

(* ================================================================= *)
(*  LCM                                                                *)
(* ================================================================= *)

(** 19. lcm_comm *)
Lemma lcm_comm : forall a b, lcm a b = lcm b a.
Proof.
  intros a b. unfold lcm.
  rewrite gcd_comm. rewrite Nat.mul_comm.
  reflexivity.
Qed.

(** 20. lcm_example *)
Lemma lcm_example : lcm 4 6 = 12.
Proof. reflexivity. Qed.

(* ================================================================= *)
(*  Additional Properties                                              *)
(* ================================================================= *)

(** 21. gcd_mul_diag_l — gcd(a, a*b) = a *)
Lemma gcd_mul_diag_l : forall a b, gcd a (a * b) = a.
Proof.
  intros a b. unfold gcd. apply Nat.gcd_mul_diag_l.
Qed.

(** 22. gcd_example_coprime_7_11 *)
Lemma gcd_example_coprime_7_11 : gcd 7 11 = 1.
Proof. reflexivity. Qed.
