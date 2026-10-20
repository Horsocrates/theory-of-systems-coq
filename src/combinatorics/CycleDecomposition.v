(* ========================================================================= *)
(*                                                                          *)
(*       ORBIT STRUCTURE OF FINITE PERMUTATIONS VIA L5/mu                   *)
(*                                                                          *)
(*  Builds on CycleInPermutation.v:                                         *)
(*    cycle_exists -> cycle_length_some -> orbit (this file).               *)
(*                                                                          *)
(*  CLASSICAL THEOREM:                                                      *)
(*    Every finite permutation decomposes into DISJOINT CYCLES.             *)
(*    This file establishes the ORBIT data structure - the cycle through    *)
(*    each point - and proves the key invariants:                           *)
(*      (1) x is in its own orbit.                                          *)
(*      (2) Orbit is closed under sigma (and hence under sigma-iteration).  *)
(*      (3) Membership is decidable via iter_sigma index.                   *)
(*      (4) Orbits are inert: applying sigma stays in the orbit.            *)
(*                                                                          *)
(*  CONSTRUCTIVE CONTENT:                                                   *)
(*    orbit(x) := [iter 0 x, iter 1 x, ..., iter (k-1) x]                  *)
(*    where k = cycle_length(x) returned by mu_le.                          *)
(*                                                                          *)
(*  E/R/R DECOMPOSITION:                                                    *)
(*    Elements (L1): orbit (list of iterates).                              *)
(*    Roles (L1):    x as cycle representative, sigma as cycle generator.   *)
(*    Rules (L2):    cycle closure: sigma maps orbit to itself.             *)
(*    Order (L5):    cycle_length = smallest k >= 1 with sigma^k(x) = x.   *)
(*    Process (P4):  bounded iteration; orbit length <= n.                  *)
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
(*               PART I: ORBIT DEFINITION                                    *)
(* ========================================================================= *)

(** orbit sigma n x: the cycle through x in sigma.
    If x has cycle length k, orbit = [x, sigma x, sigma^2 x, ..., sigma^(k-1) x]. *)
Definition orbit (sigma : nat -> nat) (n x : nat) : list nat :=
  match cycle_length sigma n x with
  | Some k => map (fun i => iter_sigma sigma i x) (seq 0 k)
  | None => []
  end.

(* ========================================================================= *)
(*               PART II: BASIC ORBIT PROPERTIES                            *)
(* ========================================================================= *)

(** orbit length equals cycle length. *)
Lemma orbit_length : forall sigma n x k,
  cycle_length sigma n x = Some k -> length (orbit sigma n x) = k.
Proof.
  intros sigma n x k Hcl. unfold orbit. rewrite Hcl.
  rewrite length_map, length_seq. reflexivity.
Qed.

(** x is in its own orbit. *)
Lemma x_in_orbit : forall sigma n x,
  is_perm sigma n -> x < n -> In x (orbit sigma n x).
Proof.
  intros sigma n x Hperm Hx.
  destruct (cycle_length_some sigma n x Hperm Hx) as [k [Hcl [Hk_pos [Hk_le Hk_iter]]]].
  unfold orbit. rewrite Hcl.
  apply in_map_iff. exists 0.
  split; [reflexivity | apply in_seq; lia].
Qed.

(** All orbit elements live in [0..n-1]. *)
Lemma orbit_bound : forall sigma n x y,
  is_perm sigma n -> x < n ->
  In y (orbit sigma n x) -> y < n.
Proof.
  intros sigma n x y Hperm Hx Hin.
  unfold orbit in Hin.
  destruct (cycle_length sigma n x) as [k|]; [|simpl in Hin; contradiction].
  apply in_map_iff in Hin. destruct Hin as [i [Heq _]]. subst y.
  apply iter_bound; assumption.
Qed.

(** Membership characterized via iter_sigma index. *)
Lemma orbit_in_iff : forall sigma n x y k,
  cycle_length sigma n x = Some k ->
  (In y (orbit sigma n x) <-> exists i, i < k /\ iter_sigma sigma i x = y).
Proof.
  intros sigma n x y k Hcl. unfold orbit. rewrite Hcl.
  rewrite in_map_iff. split.
  - intros [i [Heq Hin]]. apply in_seq in Hin. exists i.
    split; [lia | exact Heq].
  - intros [i [Hi Heq]]. exists i.
    split; [exact Heq | apply in_seq; lia].
Qed.

(* ========================================================================= *)
(*               PART III: ORBIT CLOSURE UNDER SIGMA                         *)
(* ========================================================================= *)

(** The orbit "wraps around": iter k x = x where k = cycle_length. *)
Lemma orbit_wraps : forall sigma n x k,
  is_perm sigma n -> x < n ->
  cycle_length sigma n x = Some k ->
  iter_sigma sigma k x = x.
Proof.
  intros sigma n x k Hperm Hx Hcl.
  destruct (cycle_length_some sigma n x Hperm Hx) as [k' [Hcl' [_ [_ Hiter]]]].
  rewrite Hcl in Hcl'. injection Hcl' as <-. exact Hiter.
Qed.

(** Closure under sigma: if y is in orbit x, so is sigma y. *)
Lemma orbit_closed_sigma : forall sigma n x y,
  is_perm sigma n -> x < n ->
  In y (orbit sigma n x) -> In (sigma y) (orbit sigma n x).
Proof.
  intros sigma n x y Hperm Hx Hin.
  destruct (cycle_length_some sigma n x Hperm Hx) as [k [Hcl [Hk_pos [Hk_le Hk_iter]]]].
  pose proof (orbit_in_iff sigma n x y k Hcl) as [Hf _].
  destruct (Hf Hin) as [i [Hi Heq]].
  apply (orbit_in_iff sigma n x (sigma y) k Hcl).
  (* sigma y = sigma (iter i x) = iter (S i) x. If S i = k, this equals x = iter 0 x. *)
  destruct (Nat.eq_dec (S i) k) as [HeqS|HneqS].
  - exists 0. split; [exact Hk_pos|].
    simpl. rewrite <- Heq.
    change (sigma (iter_sigma sigma i x)) with (iter_sigma sigma (S i) x).
    rewrite HeqS. symmetry. exact Hk_iter.
  - exists (S i). split; [lia|].
    simpl. rewrite <- Heq. reflexivity.
Qed.

(** Closure under iteration: iter k y stays in orbit x when y is in orbit x. *)
Lemma orbit_closed_iter : forall sigma n x y k,
  is_perm sigma n -> x < n ->
  In y (orbit sigma n x) ->
  In (iter_sigma sigma k y) (orbit sigma n x).
Proof.
  intros sigma n x y k Hperm Hx Hin.
  induction k as [|k' IH]; simpl.
  - exact Hin.
  - apply orbit_closed_sigma; assumption.
Qed.

(* ========================================================================= *)
(*               PART IV: ORBIT EQUIVALENCE                                  *)
(* ========================================================================= *)

(** Orbits are SAME or DISJOINT: equivalence relation structure. *)

(** If y is in orbit x, then x is in orbit y. *)
Lemma orbit_symmetric : forall sigma n x y,
  is_perm sigma n -> x < n -> y < n ->
  In y (orbit sigma n x) -> In x (orbit sigma n y).
Proof.
  intros sigma n x y Hperm Hx Hy Hin.
  destruct (cycle_length_some sigma n x Hperm Hx) as [k [Hcl [Hk_pos [Hk_le Hk_iter]]]].
  pose proof (orbit_in_iff sigma n x y k Hcl) as [Hf _].
  destruct (Hf Hin) as [i [Hi Heq]].
  (* y = iter i x. Then iter (k - i) y = iter (k - i) (iter i x) = iter k x = x. *)
  (* So x is in the orbit of y at position k - i. *)
  destruct (cycle_length_some sigma n y Hperm Hy) as [ky [Hcl_y [Hky_pos [Hky_le Hky_iter]]]].
  apply (orbit_in_iff sigma n y x ky Hcl_y).
  (* Multi-cycle helper: iter (ky * q) y = y. *)
  assert (Hround : forall q, iter_sigma sigma (ky * q) y = y).
  { intros q. induction q as [|q' IHq].
    - simpl. rewrite Nat.mul_0_r. reflexivity.
    - replace (ky * S q') with (ky + ky * q') by lia.
      rewrite iter_compose. rewrite IHq. exact Hky_iter. }
  destruct (Nat.eq_dec i 0) as [Heqi|Hneqi].
  - subst i. simpl in Heq. subst y. exists 0. split; [lia | reflexivity].
  - assert (Hki : iter_sigma sigma (k - i) y = x).
    { subst y. rewrite <- iter_compose.
      replace (k - i + i) with k by lia. exact Hk_iter. }
    set (idx := (k - i) mod ky).
    exists idx.
    split.
    + unfold idx. apply Nat.mod_upper_bound. lia.
    + unfold idx.
      pose proof (Nat.Div0.div_mod (k - i) ky) as Hdm.
      rewrite Hdm in Hki.
      rewrite Nat.add_comm in Hki.
      rewrite iter_compose in Hki.
      rewrite Hround in Hki.
      exact Hki.
Qed.

(** Any iterate of x lands in orbit x (mod cycle reduction). *)
Theorem iter_in_orbit_any : forall sigma n x m,
  is_perm sigma n -> x < n ->
  In (iter_sigma sigma m x) (orbit sigma n x).
Proof.
  intros sigma n x m Hperm Hx.
  destruct (cycle_length_some sigma n x Hperm Hx) as [k [Hcl [Hk_pos [_ Hk_iter]]]].
  apply (orbit_in_iff sigma n x (iter_sigma sigma m x) k Hcl).
  set (idx := m mod k).
  assert (Hround : forall q, iter_sigma sigma (k * q) x = x).
  { intros q. induction q as [|q' IHq].
    - simpl. rewrite Nat.mul_0_r. reflexivity.
    - replace (k * S q') with (k + k * q') by lia.
      rewrite iter_compose. rewrite IHq. exact Hk_iter. }
  exists idx.
  split.
  - unfold idx. apply Nat.mod_upper_bound. lia.
  - unfold idx.
    pose proof (Nat.Div0.div_mod m k) as Hdm.
    rewrite Hdm at 2.
    rewrite Nat.add_comm.
    rewrite iter_compose.
    rewrite Hround. reflexivity.
Qed.

(* ========================================================================= *)
(*               PART V: ORBIT EQUIVALENCE                                   *)
(* ========================================================================= *)

(** ORBIT PARTITION: if y is in orbit x, then orbit x and orbit y are EQUAL as sets. *)
Theorem orbit_same : forall sigma n x y,
  is_perm sigma n -> x < n -> y < n ->
  In y (orbit sigma n x) ->
  (forall z, In z (orbit sigma n x) <-> In z (orbit sigma n y)).
Proof.
  intros sigma n x y Hperm Hx Hy Hyx z.
  (* By orbit_symmetric, x in orbit y. *)
  pose proof (orbit_symmetric sigma n x y Hperm Hx Hy Hyx) as Hxy.
  split.
  - intros Hzx.
    (* z in orbit x, x in orbit y. By orbit_in_iff, z = iter i x for some i. *)
    destruct (cycle_length_some sigma n x Hperm Hx) as [kx [Hcl_x _]].
    pose proof (orbit_in_iff sigma n x z kx Hcl_x) as [Hf _].
    destruct (Hf Hzx) as [i [_ Hi_eq]]. subst z.
    (* iter i x = iter i (something reachable from y) — but we need orbit_iter via y *)
    (* Easier: orbit_closed_iter applied to Hxy gives iter i x in orbit y. *)
    apply (orbit_closed_iter sigma n y x i Hperm Hy Hxy).
  - intros Hzy.
    destruct (cycle_length_some sigma n y Hperm Hy) as [ky [Hcl_y _]].
    pose proof (orbit_in_iff sigma n y z ky Hcl_y) as [Hf _].
    destruct (Hf Hzy) as [i [_ Hi_eq]]. subst z.
    apply (orbit_closed_iter sigma n x y i Hperm Hx Hyx).
Qed.

(** ORBITS ARE EITHER EQUAL OR DISJOINT. *)
Theorem orbit_partition : forall sigma n x y,
  is_perm sigma n -> x < n -> y < n ->
  (forall z, In z (orbit sigma n x) <-> In z (orbit sigma n y)) \/
  (forall z, ~ (In z (orbit sigma n x) /\ In z (orbit sigma n y))).
Proof.
  intros sigma n x y Hperm Hx Hy.
  destruct (List.in_dec Nat.eq_dec y (orbit sigma n x)) as [Hyx|Hyx].
  - left. apply orbit_same; assumption.
  - right. intros z [Hz_x Hz_y].
    (* If z in both orbits, then by orbit_same applied to z,
       orbit x = orbit z = orbit y. Hence y in orbit x. Contradiction. *)
    pose proof (orbit_bound sigma n x z Hperm Hx Hz_x) as Hz.
    apply Hyx.
    (* y in orbit z (since z in orbit y, orbit_symmetric, then orbit_same) *)
    pose proof (orbit_same sigma n y z Hperm Hy Hz Hz_y) as Hyz_x_eq.
    (* Hyz_x_eq says: orbit y and orbit z are the same set *)
    pose proof (orbit_same sigma n x z Hperm Hx Hz Hz_x) as Hxz_eq.
    (* Hxz_eq: orbit x and orbit z are the same set *)
    apply (Hxz_eq y), (Hyz_x_eq y).
    apply x_in_orbit; assumption.
Qed.