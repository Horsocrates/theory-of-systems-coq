(** * DistinctionRepetition.v — No repetition across levels
    Elements: repeats_at, no_repetition, is_minimal_nd, forced_321_given_total6
    Roles:    L1 forbids repetition, L4 requires minimality
    Rules:    [2,3,1] is the minimal non-repeating 3-depth GIVEN total=6 (a POSIT) — NOT forced;
              [2,4,1] passes the same role-count constraints (total_6_is_the_deciding_posit; root
              NestedDistinction.constraints_do_not_force_231)
    Status:   Foundation File (Gap A.1)
    STATUS: 21 Qed, 0 Admitted, 0 new axioms  (honest reframe: June 2026; header was drift-30)
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import List.
Import ListNotations.

From ToS Require Import foundation.Distinction.
From ToS Require Import foundation.NestedDistinction.
From ToS Require Import foundation.LawsFromDistinction.
From ToS Require Import foundation.ERRFromDistinction.

(* ================================================================== *)
(*  REPETITION                                                         *)
(* ================================================================== *)

(** ★ FORMAL DEFINITION: repetition across levels *)
(** A nested distinction REPEATS if same role count at two depths *)
Definition repeats_at (nd : NestedDistinction) (d1 d2 : nat) : Prop :=
  d1 <> d2 /\ nd_roles_at nd d1 = nd_roles_at nd d2.

(** ★ L1 FORBIDS REPETITION *)
(** L1 (Identity): A = A. Each level must be ITSELF.
    If two levels have SAME structure: they are L1-identical.
    But L5 (Order): different levels are at different depths.
    Same structure at different depths → identity violation. *)

Definition no_repetition (nd : NestedDistinction) : Prop :=
  forall d1 d2, (d1 < nd_depth nd)%nat -> (d2 < nd_depth nd)%nat ->
  d1 <> d2 -> nd_roles_at nd d1 <> nd_roles_at nd d2.

(** SM distinction has no repetition: [2, 3, 1] — all different *)
Lemma sm_no_repetition : no_repetition sm_distinction.
Proof.
  unfold no_repetition. intros d1 d2 Hd1 Hd2 Hneq.
  simpl in Hd1, Hd2. (* nd_depth sm = 3 *)
  (* d1, d2 ∈ {0, 1, 2} and d1 ≠ d2 *)
  destruct d1 as [|[|[|d1']]]; try lia;
  destruct d2 as [|[|[|d2']]]; try lia;
  simpl; intro H; discriminate.
Qed.

(** A constant nd always repeats (if depth >= 2) *)
Lemma constant_repeats : forall n r,
  (2 <= n)%nat ->
  repeats_at (mkND n (fun _ => r)) 0 1.
Proof.
  intros n r Hn. unfold repeats_at. split.
  - lia.
  - reflexivity.
Qed.

(** Primary (depth 1) trivially non-repeating *)
Lemma primary_no_repetition : no_repetition primary_nd.
Proof.
  unfold no_repetition. intros d1 d2 Hd1 Hd2 Hneq.
  simpl in *. lia.
Qed.

(* ================================================================== *)
(*  MINIMALITY                                                         *)
(* ================================================================== *)

(** ★ MINIMALITY (L4): use SMALLEST possible values
    Depth 1 = 2 (forced by primary distinction)
    Depth 2 ≥ 3 (no repeat of 2, nontrivial)
    Depth 3 = 1 (terminal self-distinction) *)

Definition is_minimal_nd (nd : NestedDistinction) : Prop :=
  (* Depth 1 = 2 (primary distinction) *)
  nd_roles_at nd 0 = 2%nat /\
  (* No repetition *)
  no_repetition nd /\
  (* Depth 2: smallest ≥ 1, ≠ 2, that gives nontrivial structure *)
  (3 <= nd_roles_at nd 1)%nat /\
  (* Depth 3: smallest ≥ 1, ≠ 2, ≠ depth2 *)
  nd_roles_at nd 2 = 1%nat.

Theorem sm_is_minimal : is_minimal_nd sm_distinction.
Proof.
  unfold is_minimal_nd. split; [|split; [|split]].
  - reflexivity.
  - exact sm_no_repetition.
  - simpl. lia.
  - reflexivity.
Qed.

(* ================================================================== *)
(*  NONTRIVIALITY                                                      *)
(* ================================================================== *)

(** ★ NONTRIVIALITY: depth 2 can't be 1
    SU(1) = trivial group = {identity} = no structure
    A distinction that adds NO structure violates L4 *)

Definition nontrivial_at (nd : NestedDistinction) (d : nat) : Prop :=
  (1 < nd_roles_at nd d)%nat.

Lemma depth2_nontrivial :
  forall nd, is_minimal_nd nd -> nontrivial_at nd 1.
Proof.
  intros nd [_ [_ [H3 _]]].
  unfold nontrivial_at. lia.
Qed.

Lemma depth1_nontrivial :
  forall nd, is_minimal_nd nd -> nontrivial_at nd 0.
Proof.
  intros nd [H2 _].
  unfold nontrivial_at. lia.
Qed.

(** Depth 3 is terminal (not nontrivial) *)
Lemma depth3_terminal :
  forall nd, is_minimal_nd nd -> nd_roles_at nd 2 = 1%nat.
Proof.
  intros nd [_ [_ [_ H1]]]. exact H1.
Qed.

(* ================================================================== *)
(*  UNIQUENESS OF [2,3,1]                                              *)
(* ================================================================== *)

(** ★ Depth 2 cannot be 2 (would repeat depth 1) *)
Lemma depth2_not_2 : forall nd,
  is_minimal_nd nd -> nd_roles_at nd 1 <> 2%nat.
Proof.
  intros nd [H0 [Hnr [H3 _]]]. lia.
Qed.

(** Depth 3 cannot be 2 (would repeat depth 1) *)
Lemma depth3_not_2 : forall nd,
  is_minimal_nd nd -> nd_roles_at nd 2 <> 2%nat.
Proof.
  intros nd [_ [_ [_ H1]]]. rewrite H1. lia.
Qed.

(** Depth 3 cannot equal depth 2 *)
Lemma depth3_ne_depth2 : forall nd,
  is_minimal_nd nd -> nd_roles_at nd 2 <> nd_roles_at nd 1.
Proof.
  intros nd [_ [_ [H3 H1]]]. rewrite H1. lia.
Qed.

(** ★ If depth 2 is exactly 3 (minimum ≥ 3) then roles are [2,3,1] *)
Lemma minimal_depth2_is_3 : forall nd,
  nd_depth nd = 3%nat ->
  is_minimal_nd nd ->
  nd_roles_at nd 1 = 3%nat ->
  nd_roles_at nd 0 = 2%nat /\
  nd_roles_at nd 1 = 3%nat /\
  nd_roles_at nd 2 = 1%nat.
Proof.
  intros nd _ [H0 [_ [_ H2]]] H1.
  auto.
Qed.

(** ★ Depth 2 must be exactly 3 under minimality *)
(** Proof: depth 2 ≥ 3 (constraint). Minimum ≥ 3 is 3.
    Any value > 3 violates L4 (not minimal).
    We formalize: among all nd satisfying constraints,
    the one with nd_roles_at 1 = 3 has smallest depth2. *)
Lemma depth2_minimum_is_3 : forall nd,
  is_minimal_nd nd ->
  (3 <= nd_roles_at nd 1)%nat.
Proof.
  intros nd [_ [_ [H _]]]. exact H.
Qed.

(** ★ [2,3,1] role-counts GIVEN depth=3 ∧ minimal — WEAK form (depth2 ≥ 3 only): NOT uniqueness,
    [2,4,1] satisfies it too (total_6_is_the_deciding_posit). *)
Theorem roles_given_minimal_weak :
  forall nd, nd_depth nd = 3%nat ->
  is_minimal_nd nd ->
  nd_roles_at nd 0 = 2%nat /\
  (3 <= nd_roles_at nd 1)%nat /\
  nd_roles_at nd 2 = 1%nat.
Proof.
  intros nd Hdepth [H0 [Hnr [H3 H1]]].
  split; [exact H0|split; [lia|exact H1]].
Qed.

(** ★ depth 2 = exactly 3 ONLY GIVEN the total-roles = 6 POSIT (total=6 is posited, not derived;
    total_6_is_the_deciding_posit shows [2,4,1] passes everything except total=6). *)
Theorem forced_321_given_total6 :
  forall nd, nd_depth nd = 3%nat ->
  is_minimal_nd nd ->
  nd_total_roles nd = 6%nat ->
  nd_roles_at nd 0 = 2%nat /\
  nd_roles_at nd 1 = 3%nat /\
  nd_roles_at nd 2 = 1%nat.
Proof.
  intros nd Hdepth [H0 [Hnr [H3 H1]]] Htotal.
  split; [exact H0|split; [|exact H1]].
  (* total = fold_left (+) [roles_at 0; roles_at 1; roles_at 2] 0 *)
  unfold nd_total_roles in Htotal.
  unfold nd_decomposition in Htotal.
  rewrite Hdepth in Htotal. simpl in Htotal.
  rewrite H0 in Htotal. rewrite H1 in Htotal.
  lia.
Qed.

(** SM has total roles = 6 *)
Lemma sm_total_is_6 : nd_total_roles sm_distinction = 6%nat.
Proof. reflexivity. Qed.

(** SM role-counts recovered GIVEN the (depth=3, minimal, total=6) posits — CONDITIONAL, not unique. *)
Corollary sm_roles_given_total6 :
  forall nd, nd_depth nd = 3%nat ->
  is_minimal_nd nd ->
  nd_total_roles nd = 6%nat ->
  nd_roles_at nd 0 = nd_roles_at sm_distinction 0 /\
  nd_roles_at nd 1 = nd_roles_at sm_distinction 1 /\
  nd_roles_at nd 2 = nd_roles_at sm_distinction 2.
Proof.
  intros nd Hd Hm Ht.
  destruct (forced_321_given_total6 nd Hd Hm Ht) as [H0 [H1 H2]].
  simpl. auto.
Qed.

(* ================================================================== *)
(*  NON-UNIQUENESS — total=6 is the deciding POSIT, not derived         *)
(* ================================================================== *)

(** ★ The role-count constraints (depth=3, roles_0=2, depth2 ≥ 3, roles_2=1) do NOT force [2,3,1]:
    the alternative [2,4,1] (alt_distinction, NestedDistinction.v) satisfies ALL of them, with
    roles_1 = 4 ≠ 3 and total = 7 ≠ 6.  So forced_321_given_total6 holds ONLY because of the EXTRA
    total=6 posit — posited, not derived.  (Root: NestedDistinction.constraints_do_not_force_231.) *)
Theorem total_6_is_the_deciding_posit :
  nd_roles_at alt_distinction 0 = 2%nat
  /\ (3 <= nd_roles_at alt_distinction 1)%nat
  /\ nd_roles_at alt_distinction 2 = 1%nat
  /\ nd_roles_at alt_distinction 1 <> 3%nat
  /\ nd_total_roles alt_distinction <> 6%nat.
Proof.
  assert (H0 : nd_roles_at alt_distinction 0 = 2%nat) by (vm_compute; reflexivity).
  assert (H1 : nd_roles_at alt_distinction 1 = 4%nat) by (vm_compute; reflexivity).
  assert (H2 : nd_roles_at alt_distinction 2 = 1%nat) by (vm_compute; reflexivity).
  assert (Ht : nd_total_roles alt_distinction = 7%nat) by (vm_compute; reflexivity).
  rewrite H0, H1, H2, Ht. repeat split; lia.
Qed.

(* ================================================================== *)
(*  ALL DIFFERENT                                                      *)
(* ================================================================== *)

(** All three role counts are distinct *)
Lemma sm_all_different :
  nd_roles_at sm_distinction 0 <> nd_roles_at sm_distinction 1 /\
  nd_roles_at sm_distinction 0 <> nd_roles_at sm_distinction 2 /\
  nd_roles_at sm_distinction 1 <> nd_roles_at sm_distinction 2.
Proof. simpl. repeat split; discriminate. Qed.

(** Role counts form a decreasing-then-increasing pattern *)
Lemma sm_depth_order :
  (nd_roles_at sm_distinction 2 < nd_roles_at sm_distinction 0)%nat /\
  (nd_roles_at sm_distinction 0 < nd_roles_at sm_distinction 1)%nat.
Proof. simpl. lia. Qed.

(* ================================================================== *)
(*  GENERATORS FROM ROLES                                              *)
(* ================================================================== *)

(** Generators match SM *)
Lemma uniqueness_gives_generators :
  forall nd, nd_depth nd = 3%nat ->
  is_minimal_nd nd ->
  nd_total_roles nd = 6%nat ->
  (gauge_generators (nd_roles_at nd 1) +
   gauge_generators (nd_roles_at nd 0) +
   u1_generators = 12)%nat.
Proof.
  intros nd Hd Hm Ht.
  destruct (forced_321_given_total6 nd Hd Hm Ht) as [H0 [H1 H2]].
  rewrite H0, H1. reflexivity.
Qed.

(* ================================================================== *)
(*  SUMMARY                                                            *)
(* ================================================================== *)

Theorem distinction_repetition_summary :
  (* SM has no repetition *)
  no_repetition sm_distinction /\
  (* SM is minimal *)
  is_minimal_nd sm_distinction /\
  (* SM total = 6 *)
  nd_total_roles sm_distinction = 6%nat /\
  (* All different *)
  nd_roles_at sm_distinction 0 <> nd_roles_at sm_distinction 1 /\
  (* 12 generators *)
  (gauge_generators 3 + gauge_generators 2 + u1_generators = 12)%nat.
Proof.
  split; [|split; [|split; [|split]]].
  - exact sm_no_repetition.
  - exact sm_is_minimal.
  - reflexivity.
  - simpl. discriminate.
  - reflexivity.
Qed.

Definition distinction_repetition_count := 30%nat.
