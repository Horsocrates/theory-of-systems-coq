(* ========================================================================= *)
(*                                                                          *)
(*       ORBIT REPRESENTATIVES: CANONICAL MINIMUM VIA L5/mu                 *)
(*                                                                          *)
(*  CLASSICAL CONCEPT:                                                      *)
(*    Each orbit of a permutation has a canonical representative -- the    *)
(*    smallest element in the orbit. This file:                            *)
(*      (1) Defines orbit_min via mu_le over orbit membership.             *)
(*      (2) Proves orbit_min is in the orbit (existence).                  *)
(*      (3) Proves orbit_min is the smallest element (minimality).         *)
(*      (4) Proves elements in same orbit share orbit_min (invariance).   *)
(*                                                                          *)
(*  ROLE:                                                                  *)
(*    The orbit_min function is the bridge from cycle structure to         *)
(*    COUNTING orbits: count distinct orbit_min values across [0..n-1].    *)
(*                                                                          *)
(*  L5/mu ROLE:                                                             *)
(*    orbit_min := mu_le (membership-in-orbit predicate). This is the      *)
(*    canonical L5-minimal extraction.                                     *)
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
From ToS Require Import combinatorics.CycleDecomposition.

Open Scope nat_scope.

(* ========================================================================= *)
(*               PART 0: MU_LE_COMPLETE (witness from existence)             *)
(* ========================================================================= *)

(** Auxiliary: mu_le finds a witness <= the given upper bound k. *)
Lemma mu_le_complete : forall P K k,
  k <= K -> P k = true -> exists j, mu_le P K = Some j /\ j <= k.
Proof.
  intros P K. induction K as [|K' IH]; intros k Hk HP.
  - assert (k = 0) by lia. subst. simpl. rewrite HP. exists 0. split; [reflexivity | lia].
  - case_eq (mu_le P K').
    + intros j Em.
      exists j.
      assert (Hgoal : mu_le P (S K') = Some j).
      { simpl. rewrite Em. reflexivity. }
      split; [exact Hgoal|].
      destruct (Compare_dec.le_lt_dec k K') as [Hle|Hgt].
      * destruct (IH _ Hle HP) as [j' [Hj' Hjk]].
        rewrite Em in Hj'. injection Hj' as <-. exact Hjk.
      * apply mu_le_sound in Em. destruct Em as [_ Hjb]. lia.
    + intros En.
      assert (Hkeq : k = S K').
      { destruct (Compare_dec.le_lt_dec k K') as [Hle|Hgt].
        - destruct (IH _ Hle HP) as [j' [Hj' _]]. rewrite En in Hj'. discriminate.
        - lia. }
      subst k.
      exists (S K').
      assert (Hgoal : mu_le P (S K') = Some (S K')).
      { simpl. rewrite En. rewrite HP. reflexivity. }
      split; [exact Hgoal | lia].
Qed.

(* ========================================================================= *)
(*               PART I: DECIDABLE ORBIT MEMBERSHIP                          *)
(* ========================================================================= *)

(** Boolean check: is y in orbit of x? *)
Definition in_orbit_b (sigma : nat -> nat) (n x y : nat) : bool :=
  existsb (Nat.eqb y) (orbit sigma n x).

Lemma in_orbit_b_iff : forall sigma n x y,
  in_orbit_b sigma n x y = true <-> In y (orbit sigma n x).
Proof.
  intros. unfold in_orbit_b.
  rewrite existsb_exists. split.
  - intros [z [Hz Hzy]]. apply Nat.eqb_eq in Hzy. subst z. exact Hz.
  - intros Hin. exists y. split; [exact Hin | apply Nat.eqb_refl].
Qed.

(* ========================================================================= *)
(*               PART II: ORBIT_MIN DEFINITION                               *)
(* ========================================================================= *)

(** Smallest y <= n in orbit of x.  If x < n, this returns a valid orbit element. *)
Definition orbit_min (sigma : nat -> nat) (n x : nat) : nat :=
  match mu_le (in_orbit_b sigma n x) n with
  | Some y => y
  | None => x
  end.

(* ========================================================================= *)
(*               PART III: ORBIT_MIN PROPERTIES                              *)
(* ========================================================================= *)

(** orbit_min(x) is in the orbit. *)
Theorem orbit_min_in_orbit : forall sigma n x,
  is_perm sigma n -> x < n ->
  In (orbit_min sigma n x) (orbit sigma n x).
Proof.
  intros sigma n x Hperm Hx. unfold orbit_min.
  pose proof (x_in_orbit sigma n x Hperm Hx) as Hx_in.
  destruct (mu_le_complete (in_orbit_b sigma n x) n x) as [j [Hmu _]].
  - lia.
  - apply in_orbit_b_iff. exact Hx_in.
  - rewrite Hmu.
    pose proof (mu_le_sound _ _ _ Hmu) as [Hsound _].
    apply in_orbit_b_iff. exact Hsound.
Qed.

(** orbit_min(x) <= any element of orbit(x) (smallest property). *)
Theorem orbit_min_smallest : forall sigma n x y,
  is_perm sigma n -> x < n ->
  In y (orbit sigma n x) -> y <= n ->
  orbit_min sigma n x <= y.
Proof.
  intros sigma n x y Hperm Hx Hy_in Hy_le.
  unfold orbit_min.
  destruct (mu_le_complete (in_orbit_b sigma n x) n y) as [j [Hmu Hj_le]].
  - exact Hy_le.
  - apply in_orbit_b_iff. exact Hy_in.
  - rewrite Hmu. exact Hj_le.
Qed.

(** orbit_min(x) <= x (since x is in orbit(x)). *)
Theorem orbit_min_le_x : forall sigma n x,
  is_perm sigma n -> x < n ->
  orbit_min sigma n x <= x.
Proof.
  intros sigma n x Hperm Hx.
  apply (orbit_min_smallest sigma n x x); [assumption | assumption | | lia].
  apply x_in_orbit; assumption.
Qed.

(** orbit_min(x) < n. *)
Theorem orbit_min_bound : forall sigma n x,
  is_perm sigma n -> x < n ->
  orbit_min sigma n x < n.
Proof.
  intros sigma n x Hperm Hx.
  pose proof (orbit_min_le_x sigma n x Hperm Hx) as Hle. lia.
Qed.

(* ========================================================================= *)
(*               PART IV: ORBIT_MIN IS ORBIT-INVARIANT                       *)
(* ========================================================================= *)

(** Pointwise extensionality for mu_le. *)
Lemma mu_le_ext : forall P Q K,
  (forall k, P k = Q k) -> mu_le P K = mu_le Q K.
Proof.
  intros P Q K Hext. induction K as [|K' IH]; simpl.
  - rewrite Hext. reflexivity.
  - rewrite IH. rewrite Hext. reflexivity.
Qed.

(** Membership-as-bool extensionality from orbit_same. *)
Lemma in_orbit_b_ext : forall sigma n x y z,
  is_perm sigma n -> x < n -> y < n ->
  In y (orbit sigma n x) ->
  in_orbit_b sigma n y z = in_orbit_b sigma n x z.
Proof.
  intros sigma n x y z Hperm Hx Hy Hyx.
  pose proof (orbit_same sigma n x y Hperm Hx Hy Hyx) as Hsame.
  destruct (in_orbit_b sigma n y z) eqn:Ey;
  destruct (in_orbit_b sigma n x z) eqn:Ex; try reflexivity.
  - exfalso.
    apply in_orbit_b_iff in Ey.
    pose proof (proj2 (Hsame z) Ey) as Hin_x.
    apply in_orbit_b_iff in Hin_x. rewrite Hin_x in Ex. discriminate.
  - exfalso.
    apply in_orbit_b_iff in Ex.
    pose proof (proj1 (Hsame z) Ex) as Hin_y.
    apply in_orbit_b_iff in Hin_y. rewrite Hin_y in Ey. discriminate.
Qed.

(** orbit_min is invariant under orbit equivalence. *)
Theorem orbit_min_same : forall sigma n x y,
  is_perm sigma n -> x < n -> y < n ->
  In y (orbit sigma n x) ->
  orbit_min sigma n y = orbit_min sigma n x.
Proof.
  intros sigma n x y Hperm Hx Hy Hyx.
  unfold orbit_min.
  assert (Hext : forall z, in_orbit_b sigma n y z = in_orbit_b sigma n x z).
  { intros z. apply (in_orbit_b_ext sigma n x y z Hperm Hx Hy Hyx). }
  pose proof (mu_le_ext _ _ n Hext) as Heq.
  rewrite Heq.
  destruct (mu_le (in_orbit_b sigma n x) n) as [j|] eqn:Em.
  - reflexivity.
  - exfalso.
    pose proof (x_in_orbit sigma n x Hperm Hx) as Hxin.
    assert (Hxin_b : in_orbit_b sigma n x x = true) by (apply in_orbit_b_iff; exact Hxin).
    pose proof (mu_le_none_all_false _ _ Em x ltac:(lia)) as Hf.
    rewrite Hf in Hxin_b. discriminate.
Qed.

(* ========================================================================= *)
(*               PART V: ORBIT COUNT                                         *)
(* ========================================================================= *)

(** Count the number of orbits by counting x's that are their own orbit_min. *)
Definition orbit_count (sigma : nat -> nat) (n : nat) : nat :=
  length (filter (fun x => Nat.eqb (orbit_min sigma n x) x) (seq 0 n)).

(** Trivial bound: orbit_count <= n. *)
Theorem orbit_count_le_n : forall sigma n,
  orbit_count sigma n <= n.
Proof.
  intros sigma n. unfold orbit_count.
  assert (Hf : forall A (g : A -> bool) (L : list A),
              length (filter g L) <= length L).
  { intros A0 g L. induction L; simpl; [lia|].
    destruct (g a); simpl; lia. }
  pose proof (Hf _ (fun x => Nat.eqb (orbit_min sigma n x) x) (seq 0 n)) as Hb.
  rewrite length_seq in Hb. exact Hb.
Qed.

(* ========================================================================= *)
(*               PART VI: COMMENTARY                                         *)
(* ========================================================================= *)

(**
  THE L5/mu SCHEMA APPLIED TO ORBIT COUNTING:

  Each orbit has a CANONICAL representative -- its smallest element --
  extracted via mu_le. This makes orbit-counting decidable and
  constructively well-defined.

  The orbit_count function counts orbits as: how many x are their
  own smallest orbit representative. By orbit_min_same, this is
  exactly the number of DISTINCT orbits.

  CONNECTION TO BURNSIDE'S LEMMA:

  Burnside: |X / G| = (1/|G|) sum_g |Fix(g)|.
  For cyclic group <sigma>, this would compute orbit_count via fixed
  point counts of all powers of sigma. The L5/mu version here computes
  orbit_count DIRECTLY via canonical representatives.

  CONNECTION TO PROJECT'S CENTRAL THESIS:

  H1: finite orbit structure is fully L5/mu-soluble.
  - Each orbit has a unique L5-minimal representative.
  - The count of orbits is decidable and computable.
  - Membership in an orbit is decidable.

  WHAT THIS OPENS NEXT:

  - [BurnsideCyclicGroup.v]: prove |orbits| = average |Fix(sigma^k)|.
  - [OrbitCountEquals.v]: orbit_count = number of distinct cycles in
    cycle decomposition.
  - [TransitivityClasses.v]: equivalence classes of orbit relation.
*)
