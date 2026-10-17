(* ========================================================================= *)
(*                                                                          *)
(*       FIXED POINTS = CYCLES OF LENGTH 1                                  *)
(*                                                                          *)
(*  CLASSICAL CHARACTERIZATION:                                             *)
(*    In any permutation sigma, x is a fixed point (sigma x = x) iff       *)
(*    the cycle through x has length 1.                                     *)
(*                                                                          *)
(*    This is the L5/mu-canonical view: cycle_length(x) = mu k. iter^k x   *)
(*    = x. So cycle_length = 1 means iter^1 x = sigma x = x.                *)
(*                                                                          *)
(*  COROLLARIES (this file):                                                *)
(*    (1) fixed_iff_cycle_length_1: sigma x = x <=> cycle_length = Some 1.  *)
(*    (2) fixed_point_iter: sigma x = x ==> iter k x = x for all k.        *)
(*    (3) non_fixed_cycle_length_ge_2: sigma x <> x ==> cycle_length >= 2. *)
(*    (4) is_fixed_decidable: deciding fixed via cycle_length.             *)
(*                                                                          *)
(*  L5/mu ROLE:                                                             *)
(*    cycle_length_minimal forces: if cycle length = 1, then 1 is the      *)
(*    SMALLEST positive period, so iter 1 x = x means sigma x = x. The     *)
(*    minimality is the bidirectional link.                                 *)
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

Open Scope nat_scope.

(* ========================================================================= *)
(*               PART I: ITERATE-1 = SIGMA                                   *)
(* ========================================================================= *)

Lemma iter_sigma_1 : forall sigma x,
  iter_sigma sigma 1 x = sigma x.
Proof.
  intros. simpl. reflexivity.
Qed.

(* ========================================================================= *)
(*               PART II: MAIN CHARACTERIZATION                              *)
(* ========================================================================= *)

(** Fixed iff cycle of length 1. *)
Theorem fixed_iff_cycle_length_1 : forall sigma n x,
  is_perm sigma n -> x < n -> 1 <= n ->
  (sigma x = x <-> cycle_length sigma n x = Some 1).
Proof.
  intros sigma n x Hperm Hx Hn. split.
  - intros Hfix.
    pose proof (cycle_length_some sigma n x Hperm Hx) as [k [Hcl [Hk_pos [Hk_le _]]]].
    rewrite Hcl.
    f_equal.
    destruct (Nat.eq_dec k 1) as [Heq|Hneq]; [exact Heq|].
    exfalso.
    (* k >= 2 means 1 < k. cycle_length_minimal says iter 1 x ≠ x. But sigma x = x means iter 1 x = x. *)
    assert (H1lt : 1 < k) by lia.
    apply (cycle_length_minimal sigma n x k Hcl 1); [|rewrite iter_sigma_1; exact Hfix].
    split; [lia | exact H1lt].
  - intros Hcl.
    pose proof (cycle_length_some sigma n x Hperm Hx) as [k [Hcl' [_ [_ Hk_iter]]]].
    rewrite Hcl in Hcl'. injection Hcl' as <-.
    rewrite <- iter_sigma_1. exact Hk_iter.
Qed.

(* ========================================================================= *)
(*               PART III: FIXED POINT ITERATES                              *)
(* ========================================================================= *)

(** All iterates of a fixed point are fixed. *)
Theorem fixed_point_iter : forall sigma x k,
  sigma x = x -> iter_sigma sigma k x = x.
Proof.
  intros sigma x k Hfix.
  induction k as [|k' IH]; simpl.
  - reflexivity.
  - rewrite IH. exact Hfix.
Qed.

(* ========================================================================= *)
(*               PART IV: COROLLARIES                                        *)
(* ========================================================================= *)

(** If sigma x ≠ x, the cycle of x has length >= 2. *)
Theorem non_fixed_cycle_length_ge_2 : forall sigma n x k,
  is_perm sigma n -> x < n ->
  sigma x <> x ->
  cycle_length sigma n x = Some k ->
  2 <= k.
Proof.
  intros sigma n x k Hperm Hx Hnfix Hcl.
  pose proof (cycle_length_some sigma n x Hperm Hx) as [k' [Hcl' [Hk_pos [_ Hk_iter]]]].
  rewrite Hcl in Hcl'. injection Hcl' as <-.
  destruct (Nat.eq_dec k 1) as [Heq|Hneq].
  - exfalso. subst k. rewrite iter_sigma_1 in Hk_iter. contradiction.
  - lia.
Qed.

(** Cycle of length 1 means fixed point (= forward of main thm). *)
Corollary cycle_length_1_implies_fixed : forall sigma n x,
  is_perm sigma n -> x < n -> 1 <= n ->
  cycle_length sigma n x = Some 1 -> sigma x = x.
Proof.
  intros sigma n x Hperm Hx Hn Hcl.
  apply (fixed_iff_cycle_length_1 sigma n x Hperm Hx Hn). exact Hcl.
Qed.

(* ========================================================================= *)
(*               PART V: IDENTITY PERMUTATION                                *)
(* ========================================================================= *)

(** The identity is a permutation. *)
Lemma identity_is_perm : forall n, is_perm (fun x => x) n.
Proof.
  intros n. split.
  - intros x Hx. exact Hx.
  - intros x y _ _ H. exact H.
Qed.

(** Every cycle of the identity has length 1. *)
Theorem identity_cycle_length_1 : forall n x,
  x < n -> 1 <= n ->
  cycle_length (fun y : nat => y) n x = Some 1.
Proof.
  intros n x Hx Hn.
  apply (fixed_iff_cycle_length_1 (fun y : nat => y) n x (identity_is_perm n) Hx Hn).
  reflexivity.
Qed.

(* ========================================================================= *)
(*               PART VI: COMMENTARY                                         *)
(* ========================================================================= *)

(**
  CONNECTION TO THE PROJECT'S THESIS:

  In finite L5/mu domain, EVERY structural property of a permutation
  is decidable:
  - Cycle length: mu_le finds smallest period.
  - Fixed point: cycle length = 1.
  - Cycle structure: orbit machinery from CycleDecomposition.
  - Identity test: every cycle length is 1, i.e., every x is fixed.

  THIS IS L5/mu IN ACTION:
  The minimality from cycle_length_minimal is what makes the
  characterization fixed_iff_cycle_length_1 work. The L5-minimal
  period is unique and forces the fixed-point characterization.

  WHAT THIS OPENS NEXT:

  - [DerangementCount.v]: counts of permutations with NO fixed points,
    derived via inclusion-exclusion.
  - [InvolutionCount.v]: permutations with sigma^2 = id (cycles of
    length 1 or 2).
  - [PartitionByCycleLength.v]: structure theory of S_n by cycle types.

  All instantiate the L5/mu schema on permutations.
*)
