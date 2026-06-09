(* ========================================================================= *)
(*                                                                          *)
(*       INVOLUTIONS: sigma^2 = id IFF ALL CYCLES HAVE LENGTH IN {1, 2}     *)
(*                                                                          *)
(*  CLASSICAL CHARACTERIZATION:                                             *)
(*    A permutation sigma is an INVOLUTION iff every cycle has length 1     *)
(*    or 2. Equivalently, sigma^2 = id (pointwise).                         *)
(*                                                                          *)
(*  L5/mu DERIVATION:                                                       *)
(*    This is the m = 2 special case of perm_identity_iff:                  *)
(*      sigma^m = id  <=>  cycle_length(x) | m for every x                  *)
(*    Specializing m = 2: cycle_length(x) | 2 <=> cycle_length(x) in {1,2}. *)
(*                                                                          *)
(*  THIS FILE PROVES:                                                       *)
(*    (1) involution_iff_cycle_12: bidirectional characterization.          *)
(*    (2) involution_cycle_length_bound: cycle length <= 2.                 *)
(*    (3) cycle_length_2_means_pair: sigma maps x to its cycle partner.    *)
(*                                                                          *)
(*  CONTENT: 0 Admitted, 0 axioms.                                          *)
(* ========================================================================= *)

From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import micromega.Lia.
Import ListNotations.

From ToS Require Import combinatorics.CycleInPermutation.
From ToS Require Import combinatorics.PermutationOrder.

Open Scope nat_scope.

(* ========================================================================= *)
(*               PART I: DIVISORS OF 2                                       *)
(* ========================================================================= *)

(** k divides 2 iff k = 1 or k = 2 (for k >= 1). *)
Lemma divides_2_iff : forall k, 1 <= k -> 2 mod k = 0 <-> (k = 1 \/ k = 2).
Proof.
  intros k Hk. split.
  - intros Hmod.
    destruct k as [|[|[|k']]].
    + lia.
    + left. reflexivity.
    + right. reflexivity.
    + exfalso.
      assert (H : 2 mod S (S (S k')) = 2).
      { apply Nat.mod_small. lia. }
      rewrite Hmod in H. discriminate.
  - intros [Hk1|Hk2].
    + subst k. reflexivity.
    + subst k. reflexivity.
Qed.

(* ========================================================================= *)
(*               PART II: MAIN CHARACTERIZATION                              *)
(* ========================================================================= *)

(** sigma^2 = id (pointwise) iff every cycle length is 1 or 2. *)
Theorem involution_iff_cycle_12 : forall sigma n,
  is_perm sigma n ->
  ((forall x, x < n -> iter_sigma sigma 2 x = x) <->
   (forall x, x < n -> forall k, cycle_length sigma n x = Some k -> k = 1 \/ k = 2)).
Proof.
  intros sigma n Hperm. split.
  - intros Hinv x Hx k Hcl.
    pose proof (Hinv x Hx) as Hiter.
    pose proof (iter_eq_x_implies_div sigma n x k 2 Hperm Hx Hcl Hiter) as Hmod.
    pose proof (cycle_length_some sigma n x Hperm Hx) as [k' [Hcl' [Hk_pos _]]].
    rewrite Hcl in Hcl'. injection Hcl' as <-.
    apply (divides_2_iff k Hk_pos). exact Hmod.
  - intros Hcyc x Hx.
    destruct (cycle_length_some sigma n x Hperm Hx) as [k [Hcl [Hk_pos [_ _]]]].
    apply (iter_id_iff_div sigma n x k 2 Hperm Hx Hcl).
    apply (divides_2_iff k Hk_pos).
    apply (Hcyc x Hx k Hcl).
Qed.

(* ========================================================================= *)
(*               PART III: CYCLE LENGTH BOUND                                *)
(* ========================================================================= *)

(** In an involution, every cycle length is at most 2. *)
Theorem involution_cycle_length_bound : forall sigma n x k,
  is_perm sigma n -> x < n ->
  (forall y, y < n -> iter_sigma sigma 2 y = y) ->
  cycle_length sigma n x = Some k ->
  k <= 2.
Proof.
  intros sigma n x k Hperm Hx Hinv Hcl.
  pose proof (involution_iff_cycle_12 sigma n Hperm) as [Hf _].
  pose proof (Hf Hinv x Hx k Hcl) as [H1|H2]; lia.
Qed.

(* ========================================================================= *)
(*               PART IV: CYCLES OF LENGTH 2 ARE TRANSPOSITIONS              *)
(* ========================================================================= *)

(** If cycle_length(x) = 2, then sigma x ≠ x and sigma (sigma x) = x. *)
Theorem cycle_length_2_transposition : forall sigma n x,
  is_perm sigma n -> x < n ->
  cycle_length sigma n x = Some 2 ->
  sigma x <> x /\ sigma (sigma x) = x.
Proof.
  intros sigma n x Hperm Hx Hcl.
  pose proof (cycle_length_some sigma n x Hperm Hx) as [k [Hcl' [_ [_ Hk_iter]]]].
  rewrite Hcl in Hcl'. injection Hcl' as <-.
  split.
  - intros Hfix.
    (* sigma x = x means iter 1 x = x, but cycle length is 2 (smaller fails). *)
    apply (cycle_length_minimal sigma n x 2 Hcl 1); [|simpl; exact Hfix].
    split; lia.
  - simpl in Hk_iter. exact Hk_iter.
Qed.

(* ========================================================================= *)
(*               PART V: IDENTITY IS AN INVOLUTION                           *)
(* ========================================================================= *)

(** The identity satisfies sigma^2 = id. *)
Theorem identity_is_involution : forall n x,
  x < n -> iter_sigma (fun y : nat => y) 2 x = x.
Proof.
  intros n x Hx. simpl. reflexivity.
Qed.

(* ========================================================================= *)
(*               PART VI: COMMENTARY                                         *)
(* ========================================================================= *)

(**
  WHAT THIS FILE ESTABLISHES:

  Involutions are EXACTLY the permutations whose cycle structure consists
  of fixed points (cycles of length 1) and transpositions (cycles of
  length 2).

  This is the m = 2 case of the general L5/mu characterization:
    sigma^m = id  <=>  cycle_length(x) divides m for all x.

  THE COUNTING CONSEQUENCE:

  The number of involutions on n elements satisfies:
    I(n) = sum_k C(n, 2k) * (2k-1)!! * 1
  where the sum is over k = 0, 1, ..., floor(n/2) (number of
  transpositions, with the rest being fixed points). This is the
  Telephone Number sequence, and can be derived constructively from
  this characterization plus combinatorial counting.

  CONNECTION TO PROJECT'S CENTRAL THESIS:

  H1 (finitization boundary = constructivity boundary):
  In finite S_n, every involution can be DECOMPOSED into its fixed
  points and transpositions; the decomposition is unique and L5/mu-
  extractable.

  By contrast, in infinite groups, "involution" is still defined but
  decomposition into fixed-points-and-transpositions can fail
  (uncountable cardinalities). Finite S_n is the L5/mu-domain.

  WHAT THIS OPENS NEXT:

  - [InvolutionCount.v]: I(n) telephone numbers via recurrence.
  - [DerangementCount.v]: D(n) = n! * sum (-1)^k / k!.
  - [CycleTypeStructure.v]: full structure theory of S_n cycle types.
*)
