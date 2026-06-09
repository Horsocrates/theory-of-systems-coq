(* ========================================================================= *)
(*                                                                          *)
(*       PERMUTATION ORDER: sigma^m = id IFF CYCLE LENGTHS DIVIDE m         *)
(*                                                                          *)
(*  CLASSICAL THEOREM (group theory of S_n):                                *)
(*    For sigma in S_n, sigma^m = id iff m is divisible by the cycle        *)
(*    length of every element. Equivalently, the ORDER of sigma is the     *)
(*    LCM of its cycle lengths.                                             *)
(*                                                                          *)
(*  THIS FILE PROVES THE DIVISIBILITY CHARACTERIZATION:                    *)
(*    iter sigma^m(x) = x <=> cycle_length(x) divides m                    *)
(*    sigma^m = id (pointwise) <=> cycle_length(x) | m for all x.           *)
(*                                                                          *)
(*  CONSTRUCTIVE PROOF (this file):                                        *)
(*    (<=) If cycle_length(x) = k divides m, then m = k * q and             *)
(*         iter m x = iter (k * q) x = x via Hround.                        *)
(*    (=>) If iter m x = x, then suppose k does not divide m. Write         *)
(*         m = k * q + r with 0 < r < k. Then iter m x = iter r x = x,     *)
(*         contradicting cycle_length_minimal (k is the smallest period).   *)
(*                                                                          *)
(*  L5/mu ROLE:                                                             *)
(*    cycle_length_minimal (from CycleInPermutation) gives the L5-minimal   *)
(*    property: k is the SMALLEST period, so no smaller r > 0 works.        *)
(*    This is the heart of the (=>) direction.                              *)
(*                                                                          *)
(*  E/R/R DECOMPOSITION:                                                    *)
(*    Elements (L1): permutation sigma, exponent m, cycle length k.         *)
(*    Roles (L1):    sigma^m as repeated composition.                       *)
(*    Rules (L2):    sigma^k = identity within orbit (cycle property).      *)
(*    Order (L5):    smallest k via cycle_length is L5-canonical.           *)
(*    Process (P4):  bounded; cycle lengths <= n, m freely.                 *)
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
(*               PART I: ROUND-TRIP LEMMA                                    *)
(* ========================================================================= *)

(** Iterating sigma a multiple of cycle_length(x) returns to x. *)
Lemma iter_round : forall sigma n x k q,
  is_perm sigma n -> x < n ->
  cycle_length sigma n x = Some k ->
  iter_sigma sigma (k * q) x = x.
Proof.
  intros sigma n x k q Hperm Hx Hcl.
  destruct (cycle_length_some sigma n x Hperm Hx) as [k' [Hcl' [_ [_ Hk_iter]]]].
  rewrite Hcl in Hcl'. injection Hcl' as <-.
  induction q as [|q' IHq].
  - simpl. rewrite Nat.mul_0_r. reflexivity.
  - replace (k * S q') with (k + k * q') by lia.
    rewrite iter_compose. rewrite IHq. exact Hk_iter.
Qed.

(* ========================================================================= *)
(*               PART II: REVERSE DIRECTION VIA CYCLE_LENGTH_MINIMAL         *)
(* ========================================================================= *)

(** If sigma^m(x) = x, then cycle_length(x) divides m. *)
Lemma iter_eq_x_implies_div : forall sigma n x k m,
  is_perm sigma n -> x < n ->
  cycle_length sigma n x = Some k ->
  iter_sigma sigma m x = x ->
  m mod k = 0.
Proof.
  intros sigma n x k m Hperm Hx Hcl Hiter.
  destruct (Nat.eq_dec (m mod k) 0) as [Hmod|Hmod]; [exact Hmod|].
  exfalso.
  set (r := m mod k).
  pose proof (cycle_length_some sigma n x Hperm Hx) as [k' [Hcl' [Hk_pos [_ _]]]].
  rewrite Hcl in Hcl'. injection Hcl' as <-.
  assert (Hr_lt : r < k).
  { unfold r. apply Nat.mod_upper_bound. lia. }
  assert (Hr_pos : 1 <= r).
  { unfold r. lia. }
  assert (Hr_iter : iter_sigma sigma r x = x).
  { pose proof (Nat.Div0.div_mod m k) as Hdm.
    rewrite Hdm in Hiter.
    rewrite Nat.add_comm in Hiter.
    rewrite iter_compose in Hiter.
    rewrite (iter_round sigma n x k (m / k) Hperm Hx Hcl) in Hiter.
    exact Hiter. }
  apply (cycle_length_minimal sigma n x k Hcl r).
  - split; [exact Hr_pos | exact Hr_lt].
  - exact Hr_iter.
Qed.

(* ========================================================================= *)
(*               PART III: THE MAIN IFF THEOREM                              *)
(* ========================================================================= *)

(** CHARACTERIZATION: iter sigma^m(x) = x iff cycle_length(x) divides m. *)
Theorem iter_id_iff_div : forall sigma n x k m,
  is_perm sigma n -> x < n ->
  cycle_length sigma n x = Some k ->
  (iter_sigma sigma m x = x <-> m mod k = 0).
Proof.
  intros sigma n x k m Hperm Hx Hcl. split.
  - intros H. apply (iter_eq_x_implies_div sigma n x k m Hperm Hx Hcl H).
  - intros Hmod.
    pose proof (Nat.Div0.div_mod m k) as Hdm.
    rewrite Hmod in Hdm. rewrite Nat.add_0_r in Hdm.
    rewrite Hdm.
    apply (iter_round sigma n x k (m / k) Hperm Hx Hcl).
Qed.

(* ========================================================================= *)
(*               PART IV: GLOBAL PERMUTATION IDENTITY                        *)
(* ========================================================================= *)

(** sigma^m is the identity permutation iff every cycle length divides m. *)
Theorem perm_identity_iff : forall sigma n m,
  is_perm sigma n ->
  ((forall x, x < n -> iter_sigma sigma m x = x) <->
   (forall x, x < n -> forall k, cycle_length sigma n x = Some k -> m mod k = 0)).
Proof.
  intros sigma n m Hperm. split.
  - intros Hid x Hx k Hcl.
    apply (iter_eq_x_implies_div sigma n x k m Hperm Hx Hcl).
    apply Hid. exact Hx.
  - intros Hdiv x Hx.
    destruct (cycle_length_some sigma n x Hperm Hx) as [k [Hcl _]].
    apply (iter_id_iff_div sigma n x k m Hperm Hx Hcl).
    apply (Hdiv x Hx k Hcl).
Qed.

(* ========================================================================= *)
(*               PART V: ORDER EXISTS                                        *)
(* ========================================================================= *)

(** For any permutation on a non-empty finite set, an identity power exists.
    Specifically, the product of cycle lengths works (though not optimal). *)

(** Helper: factorial bound (any cycle length k <= n divides n!) *)
Fixpoint factorial (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n' => S n' * factorial n'
  end.

Lemma factorial_pos : forall n, 1 <= factorial n.
Proof.
  intros n. induction n as [|n' IH]; simpl.
  - lia.
  - assert (1 <= S n' * factorial n') by (apply Nat.mul_pos_pos; lia).
    exact H.
Qed.

(** Any k in [1..n] divides n! *)
Lemma divides_factorial : forall n k, 1 <= k <= n -> factorial n mod k = 0.
Proof.
  intros n k [Hk_pos Hk_le].
  induction n as [|n' IH].
  - lia.
  - destruct (Nat.eq_dec k (S n')) as [Heq|Hneq].
    + subst k.
      change (factorial (S n') mod S n' = 0) with (S n' * factorial n' mod S n' = 0).
      rewrite Nat.mul_comm. apply Nat.Div0.mod_mul.
    + assert (Hk_le' : k <= n') by lia.
      assert (Hfac_mod : factorial n' mod k = 0) by (apply IH; lia).
      change (factorial (S n') mod k = 0) with (S n' * factorial n' mod k = 0).
      assert (Hfac_div : factorial n' = (factorial n' / k) * k).
      { pose proof (Nat.Div0.div_mod (factorial n') k) as Hdm.
        rewrite Hfac_mod in Hdm. rewrite Nat.add_0_r in Hdm. lia. }
      rewrite Hfac_div.
      replace (S n' * (factorial n' / k * k)) with ((S n' * (factorial n' / k)) * k) by lia.
      apply Nat.Div0.mod_mul.
Qed.

(** Order exists: there is m >= 1 with sigma^m = id. *)
Theorem order_exists : forall sigma n,
  is_perm sigma n ->
  exists m, 1 <= m /\ forall x, x < n -> iter_sigma sigma m x = x.
Proof.
  intros sigma n Hperm.
  exists (factorial n).
  split; [apply factorial_pos|].
  intros x Hx.
  destruct (cycle_length_some sigma n x Hperm Hx) as [k [Hcl [Hk_pos [Hk_le _]]]].
  apply (iter_id_iff_div sigma n x k (factorial n) Hperm Hx Hcl).
  apply divides_factorial. split; [exact Hk_pos | exact Hk_le].
Qed.

(* ========================================================================= *)
(*               PART VI: COMMENTARY                                         *)
(* ========================================================================= *)

(**
  WHAT THIS FILE ESTABLISHES:

  The relationship between sigma's iteration structure and its cycle lengths
  is fully characterized:
    iter sigma^m(x) = x   <=>   cycle_length(x) divides m.

  Globally: sigma^m = id (pointwise on [0..n-1]) iff every cycle length
  divides m. The SMALLEST such m is the ORDER of sigma in S_n = LCM of
  cycle lengths.

  THE L5/mu ROLE:

  The PIVOT of this proof is `cycle_length_minimal` (from CycleInPermutation):
  the L5/mu-minimal cycle length CANNOT be matched by a smaller positive
  period. This forces the divisibility relation.

  Inside the L5/mu domain, this is fully constructive:
  - cycle_length extracts the smallest period via mu_le.
  - Multiples are characterized by mod = 0.
  - factorial(n) is divisible by every k in [1..n], giving an explicit
    identity power.

  CONNECTION TO PROJECT'S CENTRAL THESIS:

  H1: finite group theory of S_n is fully L5/mu-soluble.
  - Existence of order: factorial bound.
  - Minimal order (LCM of cycle lengths): would require LCM computation,
    also L5/mu-soluble via repeated divisibility checks.
  - Cycle structure: completely determined by sigma_inverse and orbit theory.

  WHAT THIS OPENS NEXT:

  - [PermutationLCM.v]: minimal order via LCM computation.
  - [SymmetricGroupOrder.v]: |S_n| = n! and all powers.
  - [SignOfPermutation.v]: sign via parity of cycle count.
  - [CayleyDistance.v]: Cayley distance between permutations.

  All of these belong to the L5/mu corpus.
*)
