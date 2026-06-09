(* ========================================================================= *)
(*                  CATALAN NUMBERS via the CYCLE LEMMA                     *)
(*                                                                          *)
(*  Goal: derive the explicit formula                                       *)
(*                                                                          *)
(*           C_n = C(2n, n) / (n + 1) = (2n)! / (n! * (n+1)!)               *)
(*                                                                          *)
(*  within the Theory of Systems framework, using the Dvoretzky-Motzkin     *)
(*  cycle lemma. The chain of reasoning:                                    *)
(*                                                                          *)
(*  1. |Dyck_n| counted via cycle lemma on augmented sequences              *)
(*     (length 2n+1, with n+1 U-steps and n D-steps):                       *)
(*                                                                          *)
(*          (2n+1) * |Dyck_n| = C(2n+1, n)                                  *)
(*                                                                          *)
(*  2. Algebraic identity (proven from factorials):                         *)
(*                                                                          *)
(*          (n+1) * C(2n+1, n) = (2n+1) * C(2n, n)                          *)
(*                                                                          *)
(*  3. Combining:                                                           *)
(*                                                                          *)
(*          (n+1) * |Dyck_n| = C(2n, n)                                     *)
(*                                                                          *)
(* ========================================================================= *)
(*                                                                          *)
(*  E/R/R DECOMPOSITION of the system Dyck_n:                               *)
(*                                                                          *)
(*    ELEMENTS (L1):  Step = {U, D}                                         *)
(*                    The primitive distinction A vs not-A.                 *)
(*                                                                          *)
(*    ROLES (L1):     - position: pi : Steps -> [1, 2n] (L5, horizontal)    *)
(*                    - height:   h(k) = #U_[0..k] - #D_[0..k] (cumulative) *)
(*                    - matching: mu : U-steps -> D-steps (non-crossing)    *)
(*                                                                          *)
(*    RULES (L2):     - Closure (L4 Sufficient Reason): #U = #D = n         *)
(*                    - Non-negativity (L4 + L2): h(k) >= 0                 *)
(*                    - Determinism (L1 Identity): path = step sequence     *)
(*                    - Bivalence (L3 Excluded Middle): each pos is U xor D *)
(*                    - Discreteness (P4 Process Finitude): n finite        *)
(*                                                                          *)
(*  LEVEL HIERARCHY for the cycle lemma:                                    *)
(*                                                                          *)
(*    L3 (meta) : orbit class [w] = orbit under Z/(2n+1)                    *)
(*       up                                                                  *)
(*    L2 (rules): cyclic shift sigma; predicate is_good; counting           *)
(*       up                                                                  *)
(*    L1 (elem):  augmented step sequences (length 2n+1)                    *)
(*                                                                          *)
(*  L5 (Law of Order) is doubly active:                                     *)
(*    - horizontal: positions in path are ordered                           *)
(*    - vertical:   shift is L2-operation on L1 objects, blocks self-ref    *)
(*                                                                          *)
(*  L5 PRINCIPLE OF MINIMAL INDEX is the engine of the cycle lemma:         *)
(*    among all cyclic rotations achieving the minimum prefix sum, take     *)
(*    the LARGEST index. This is the unique "good" rotation.                *)
(*                                                                          *)
(*  P4 (Finitude): C_n counts a FINITE process — the family {Dyck_n} is    *)
(*    a process producing finite systems on demand. No axiom of infinity    *)
(*    is needed, no Axiom of Choice. The proof is fully constructive.       *)
(*                                                                          *)
(*  STATUS: Definitions + basic invariants fully proved.                    *)
(*          Cycle lemma core + aperiodicity stated with proof sketch.       *)
(*          Algebraic simplification fully proved.                          *)
(*                                                                          *)
(*  Author: Theory of Systems formalization | Date: May 2026                *)
(* ========================================================================= *)

From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Arith.Factorial.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import setoid_ring.ArithRing.
From Stdlib Require Import Sorting.Permutation.
Import ListNotations.

Open Scope nat_scope.

(* ========================================================================= *)
(*                  PART I: STEPS, PATHS, COUNTS                            *)
(* ========================================================================= *)

(** ELEMENTS of the system: two-valued distinction. *)
Definition Step : Set := bool.
Definition U : Step := true.   (* up-step,   +1 to height *)
Definition D : Step := false.  (* down-step, -1 to height *)

(** A path is a finite sequence of steps. P4 (Finitude) is automatic:
    list nat is structurally finite. *)
Definition Path : Set := list Step.

Fixpoint count_U (p : Path) : nat :=
  match p with
  | [] => 0
  | true :: rest => S (count_U rest)
  | false :: rest => count_U rest
  end.

Fixpoint count_D (p : Path) : nat :=
  match p with
  | [] => 0
  | true :: rest => count_D rest
  | false :: rest => S (count_D rest)
  end.

(** Basic counting lemmas — these instantiate L1 (Identity) on counts. *)
Lemma count_U_app : forall p q, count_U (p ++ q) = count_U p + count_U q.
Proof.
  induction p as [|a p IH]; simpl; intros q; auto.
  destruct a; simpl; rewrite IH; lia.
Qed.

Lemma count_D_app : forall p q, count_D (p ++ q) = count_D p + count_D q.
Proof.
  induction p as [|a p IH]; simpl; intros q; auto.
  destruct a; simpl; rewrite IH; lia.
Qed.

Lemma count_UD_length : forall p, count_U p + count_D p = length p.
Proof.
  induction p as [|a p IH]; simpl; auto.
  destruct a; simpl; lia.
Qed.

Lemma length_app_nat : forall (p q : Path), length (p ++ q) = length p + length q.
Proof. intros; apply length_app. Qed.

(* ========================================================================= *)
(*                  PART II: HEIGHTS AND DYCK CONDITION                     *)
(* ========================================================================= *)

(** Height after k steps = (# U-steps) - (# D-steps) in prefix of length k.
    Signed; we use Z because in augmented sequences heights can dip below 0. *)
Definition height_at (p : Path) (k : nat) : Z :=
  (Z.of_nat (count_U (firstn k p)) - Z.of_nat (count_D (firstn k p)))%Z.

(** Total height of a path. *)
Definition total_height (p : Path) : Z :=
  height_at p (length p).

Lemma firstn_all_eq : forall (p : Path), firstn (length p) p = p.
Proof.
  induction p as [|a p IH]; simpl; auto.
  rewrite IH; reflexivity.
Qed.

Lemma total_height_eq : forall p,
  total_height p = (Z.of_nat (count_U p) - Z.of_nat (count_D p))%Z.
Proof.
  intros p. unfold total_height, height_at.
  rewrite firstn_all_eq. reflexivity.
Qed.

(** is_dyck encodes the Constitution (L2 Rules) of the system:
    - Closure (L4):       count_U = count_D
    - Non-negativity:     all prefix heights >= 0  *)
Definition is_dyck (p : Path) : Prop :=
  count_U p = count_D p /\
  (forall k, k <= length p -> (0 <= height_at p k)%Z).

(* ========================================================================= *)
(*                  PART III: CYCLIC ROTATION (L2 operation on L1)          *)
(* ========================================================================= *)

(** Rotate by one position. Constructively well-defined; on empty list,
    yields empty list (identity), which is a fixed point — L5 vacuously
    satisfied on the empty system. *)
Definition rotate_one (p : Path) : Path :=
  match p with
  | [] => []
  | x :: rest => rest ++ [x]
  end.

Fixpoint rotate_k (k : nat) (p : Path) : Path :=
  match k with
  | 0 => p
  | S k' => rotate_one (rotate_k k' p)
  end.

(** Rotation invariants — these establish that rotation is an L2-operation
    that preserves the Constitution at L1 (counts) but permutes Roles
    (positions). *)
Lemma rotate_one_length : forall p, length (rotate_one p) = length p.
Proof.
  intros [|x p]; simpl; auto.
  rewrite length_app. simpl. lia.
Qed.

Lemma rotate_k_length : forall k p, length (rotate_k k p) = length p.
Proof.
  induction k as [|k IH]; simpl; intros p; auto.
  rewrite rotate_one_length. apply IH.
Qed.

Lemma rotate_one_count_U : forall p, count_U (rotate_one p) = count_U p.
Proof.
  intros [|x p]; simpl; auto.
  rewrite count_U_app. destruct x; simpl; lia.
Qed.

Lemma rotate_one_count_D : forall p, count_D (rotate_one p) = count_D p.
Proof.
  intros [|x p]; simpl; auto.
  rewrite count_D_app. destruct x; simpl; lia.
Qed.

Lemma rotate_k_count_U : forall k p, count_U (rotate_k k p) = count_U p.
Proof.
  induction k as [|k IH]; simpl; intros p; auto.
  rewrite rotate_one_count_U. apply IH.
Qed.

Lemma rotate_k_count_D : forall k p, count_D (rotate_k k p) = count_D p.
Proof.
  induction k as [|k IH]; simpl; intros p; auto.
  rewrite rotate_one_count_D. apply IH.
Qed.

Lemma rotate_k_total_height : forall k p,
  total_height (rotate_k k p) = total_height p.
Proof.
  intros k p. rewrite !total_height_eq.
  rewrite rotate_k_count_U, rotate_k_count_D. reflexivity.
Qed.

(* ========================================================================= *)
(*                  PART IV: AUGMENTED SEQUENCES & GOOD PREDICATE           *)
(* ========================================================================= *)

(** An augmented sequence has n+1 U-steps and n D-steps, total length 2n+1.
    Total height = +1. This is the substrate of the cycle lemma. *)
Definition is_augmented (n : nat) (p : Path) : Prop :=
  length p = 2 * n + 1 /\ count_U p = n + 1 /\ count_D p = n.

Lemma augmented_total_height : forall n p,
  is_augmented n p -> total_height p = 1%Z.
Proof.
  intros n p [_ [HU HD]].
  rewrite total_height_eq, HU, HD.
  rewrite Nat2Z.inj_add. simpl. lia.
Qed.

(** is_good: every non-empty prefix has strictly positive height.
    This is the "completely positive" condition of the cycle lemma. *)
Definition is_good (p : Path) : Prop :=
  forall k, 1 <= k -> k <= length p -> (1 <= height_at p k)%Z.

(** Rotation preserves augmented-ness (because counts are preserved). *)
Lemma rotate_k_augmented : forall n k p,
  is_augmented n p -> is_augmented n (rotate_k k p).
Proof.
  intros n k p [HL [HU HD]].
  unfold is_augmented. repeat split.
  - rewrite rotate_k_length. exact HL.
  - rewrite rotate_k_count_U. exact HU.
  - rewrite rotate_k_count_D. exact HD.
Qed.

(* ========================================================================= *)
(*                  PART V: CYCLE LEMMA (Dvoretzky-Motzkin)                 *)
(* ========================================================================= *)

(** ----------------------------------------------------------------------- *)
(** PROOF SKETCH for the cycle lemma:                                      *)
(**                                                                        *)
(** Let p be an augmented sequence of length m = 2n+1. The prefix sums    *)
(** S_0 = 0, S_1, S_2, ..., S_m = 1 are a sequence in Z.                  *)
(**                                                                        *)
(** EXISTENCE: Let jstar := largest index j in [0, m-1] such that        *)
(**   S_j = min { S_0, S_1, ..., S_m }                                    *)
(** (largest such index — this is L5 applied to find unique rotation.)    *)
(**                                                                        *)
(** Claim: rotating p by jstar positions gives a "good" sequence.         *)
(**                                                                        *)
(** Proof: Let q := rotate_k jstar p. Prefix sums of q:                   *)
(**   - For 1 <= k <= m - jstar:                                          *)
(**       S_k(q) = S_(jstar+k)(p) - S_(jstar)(p)                          *)
(**     Since jstar is the LARGEST minimum index,                         *)
(**     S_(jstar+k)(p) > S_(jstar)(p) for all k in [1, m-jstar],          *)
(**     so S_k(q) >= 1.                                                   *)
(**   - For m - jstar < k <= m:                                           *)
(**       S_k(q) = (S_m(p) - S_(jstar)(p)) + S_(k-(m-jstar))(p)           *)
(**              = (1 - S_(jstar)(p)) + S_(k-m+jstar)(p)                  *)
(**     Since jstar is a minimum,                                         *)
(**     S_(k-m+jstar)(p) >= S_(jstar)(p), giving S_k(q) >= 1.             *)
(**                                                                        *)
(** UNIQUENESS: Suppose rotation by i also gives a good sequence.         *)
(** By the same prefix sum analysis, i must be a position where           *)
(** the prefix sum achieves its global minimum, AND no later index        *)
(** also achieves it (else some prefix sum equals 0, breaking is_good).   *)
(** Hence i is the LARGEST minimum index, so i = jstar.                   *)
(**                                                                        *)
(** APERIODICITY: For augmented sequences, gcd(n+1, n) = 1, hence no      *)
(** nontrivial rotation fixes the sequence (period would divide both     *)
(** n+1 and n, hence 1, hence trivial). All 2n+1 rotations are distinct. *)
(** ----------------------------------------------------------------------- *)

(** Decidable boolean version of [is_good]; useful for selecting the      *)
(** unique good rotation. *)
Definition heightZ_at_bool (p : Path) (k : nat) : Z := height_at p k.

Fixpoint forall_pos_heights (p : Path) (k : nat) : bool :=
  match k with
  | 0 => true
  | S k' =>
      Z.leb 1 (height_at p (S k')) && forall_pos_heights p k'
  end.

Definition is_good_b (p : Path) : bool :=
  forall_pos_heights p (length p).

(** [find_good] searches for a rotation index in [0, m) that yields a    *)
(** good sequence. We define it as the smallest such index (L5).         *)
Fixpoint find_good_aux (p : Path) (m : nat) (cur : nat) : nat :=
  match cur with
  | 0 => 0
  | S cur' =>
      let trial := m - cur in
      if is_good_b (rotate_k trial p) then trial
      else find_good_aux p m cur'
  end.

Definition find_good (p : Path) : nat := find_good_aux p (length p) (length p).

(** =================================================================== *)
(** ROTATION-HEIGHT FORMULAS: how prefix heights transform under rotation. *)
(** =================================================================== *)

(** Composition: rotate_k k (rotate_k j p) = rotate_k (k+j) p. *)
Lemma rotate_k_compose : forall k j p,
  rotate_k k (rotate_k j p) = rotate_k (k + j) p.
Proof.
  induction k as [|k IH]; intros j p; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(** Rotation by exactly length p returns the path. *)
Lemma rotate_one_skipn : forall x rest,
  rotate_one (x :: rest) = rest ++ [x].
Proof. reflexivity. Qed.

(** Key formula: for rotate_one of a non-empty path, prefix heights shift. *)
Lemma height_at_rotate_one_le : forall x rest k,
  k <= length rest ->
  (height_at (rotate_one (x :: rest)) k
   = height_at (x :: rest) (S k) - height_at (x :: rest) 1)%Z.
Proof.
  intros x rest k Hk.
  unfold rotate_one, height_at.
  rewrite firstn_app.
  replace (k - length rest) with 0 by lia.
  cbn [firstn]. rewrite app_nil_r.
  destruct x.
  - cbn [count_U count_D].
    rewrite Nat2Z.inj_succ. lia.
  - cbn [count_U count_D].
    rewrite Nat2Z.inj_succ. lia.
Qed.

(** Generalized: rotate_one on any non-empty path. *)
Lemma height_at_rotate_one_le_gen : forall p k,
  k < length p ->
  (height_at (rotate_one p) k = height_at p (S k) - height_at p 1)%Z.
Proof.
  intros [|x rest] k Hk.
  - simpl in Hk. lia.
  - simpl in Hk. apply height_at_rotate_one_le. lia.
Qed.

(** Top-of-rotation formula (length rest = length p - 1). *)
Lemma height_at_rotate_one_top : forall x rest,
  (height_at (rotate_one (x :: rest)) (length rest)
   = total_height (x :: rest) - height_at (x :: rest) 1)%Z.
Proof.
  intros x rest.
  rewrite (height_at_rotate_one_le x rest (length rest)) by lia.
  unfold total_height. simpl length.
  reflexivity.
Qed.

(** Height_at = 0 at index 0. *)
Lemma height_at_0 : forall p, height_at p 0 = 0%Z.
Proof. intros p. unfold height_at. cbn [firstn count_U count_D]. lia. Qed.

(** General rotation formula (no-wrap case): for j + k <= length p,
    height_at (rotate_k j p) k = height_at p (k+j) - height_at p j. *)
Lemma height_at_rotate_k_no_wrap : forall j p k,
  j + k <= length p ->
  (height_at (rotate_k j p) k = height_at p (k + j) - height_at p j)%Z.
Proof.
  induction j as [|j IH]; intros p k Hk.
  - simpl rotate_k. replace (k + 0) with k by lia.
    rewrite height_at_0. lia.
  - simpl rotate_k.
    assert (Hk_lt : k < length p) by (simpl in Hk; lia).
    assert (Hk_lt' : k < length (rotate_k j p)) by (rewrite rotate_k_length; exact Hk_lt).
    rewrite height_at_rotate_one_le_gen by exact Hk_lt'.
    rewrite (IH p (S k)) by lia.
    rewrite (IH p 1) by lia.
    replace (k + S j) with (S k + j) by lia.
    replace (1 + j) with (S j) by lia.
    lia.
Qed.

(** Augmented sequences have length 2n+1 explicitly. *)
Lemma augmented_length : forall n p,
  is_augmented n p -> length p = 2 * n + 1.
Proof. intros n p [HL _]. exact HL. Qed.

(** =================================================================== *)
(** PREFIX HEIGHTS as a list (computational handle on argmin).          *)
(** =================================================================== *)

Fixpoint prefix_heights_from (p : Path) (acc : Z) : list Z :=
  match p with
  | [] => [acc]
  | true :: rest => acc :: prefix_heights_from rest (acc + 1)%Z
  | false :: rest => acc :: prefix_heights_from rest (acc - 1)%Z
  end.

Definition prefix_heights (p : Path) : list Z := prefix_heights_from p 0%Z.

Lemma prefix_heights_from_length : forall p acc,
  length (prefix_heights_from p acc) = S (length p).
Proof.
  induction p as [|b rest IH]; intros acc; simpl; auto.
  destruct b; simpl; rewrite IH; reflexivity.
Qed.

Lemma prefix_heights_length : forall p, length (prefix_heights p) = S (length p).
Proof. intros p. apply prefix_heights_from_length. Qed.

(** Connection between nth of prefix_heights and height_at. *)
Lemma nth_prefix_heights_from : forall p k acc,
  k <= length p ->
  nth k (prefix_heights_from p acc) 0%Z = (acc + height_at p k)%Z.
Proof.
  induction p as [|b rest IH]; intros k acc Hk.
  - simpl in Hk. assert (k = 0) by lia. subst.
    simpl. rewrite height_at_0. lia.
  - destruct k as [|k'].
    + destruct b; simpl; rewrite height_at_0; lia.
    + simpl in Hk.
      destruct b.
      * simpl. rewrite IH by lia.
        unfold height_at.
        change (firstn (S k') (true :: rest)) with (true :: firstn k' rest).
        cbn [count_U count_D].
        rewrite Nat2Z.inj_succ. lia.
      * simpl. rewrite IH by lia.
        unfold height_at.
        change (firstn (S k') (false :: rest)) with (false :: firstn k' rest).
        cbn [count_U count_D].
        rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma nth_prefix_heights : forall p k,
  k <= length p ->
  nth k (prefix_heights p) 0%Z = height_at p k.
Proof.
  intros p k Hk. unfold prefix_heights.
  rewrite nth_prefix_heights_from by lia. lia.
Qed.

(** =================================================================== *)
(** ARGMIN: largest index achieving minimum prefix height.              *)
(** =================================================================== *)

(** Walks through a list, tracking the running minimum AND the LARGEST
    index where it was last achieved. *)
Fixpoint find_last_min (l : list Z) (cur_idx : nat) (best_val : Z) (best_idx : nat)
  : nat :=
  match l with
  | [] => best_idx
  | h :: rest =>
      if Z.leb h best_val
      then find_last_min rest (S cur_idx) h cur_idx
      else find_last_min rest (S cur_idx) best_val best_idx
  end.

Definition last_min_idx (p : Path) : nat :=
  match prefix_heights p with
  | [] => 0
  | h :: rest => find_last_min rest 1 h 0
  end.

(** Helper: bound on find_last_min output. *)
Lemma find_last_min_lt : forall l cur best_val best_idx,
  best_idx < cur ->
  find_last_min l cur best_val best_idx < cur + length l.
Proof.
  induction l as [|h rest IH]; intros cur best_val best_idx Hbi; simpl.
  - lia.
  - destruct (Z.leb h best_val).
    + specialize (IH (S cur) h cur ltac:(lia)). lia.
    + specialize (IH (S cur) best_val best_idx ltac:(lia)). lia.
Qed.

(** PROPERTY 1 (BOUND). *)
Lemma last_min_idx_le_length : forall p,
  last_min_idx p <= length p.
Proof.
  intros p. unfold last_min_idx.
  pose proof (prefix_heights_length p) as Hlen.
  destruct (prefix_heights p) as [|h rest] eqn:Eh.
  - lia.
  - simpl in Hlen.
    pose proof (find_last_min_lt rest 1 h 0 ltac:(lia)) as Hlt.
    lia.
Qed.

(** Helper: invariant lemma for find_last_min correctness via index matching. *)
Lemma find_last_min_correct : forall l H cur best_val best_idx,
  (forall i, i < length l -> nth i l 0%Z = nth (cur + i) H 0%Z) ->
  cur + length l = length H ->
  best_idx < cur ->
  nth best_idx H 0%Z = best_val ->
  (forall j, j < cur -> (best_val <= nth j H 0%Z)%Z) ->
  (forall j, best_idx < j -> j < cur -> (best_val < nth j H 0%Z)%Z) ->
  let r := find_last_min l cur best_val best_idx in
  r < length H /\
  (forall k, k < length H -> (nth r H 0%Z <= nth k H 0%Z)%Z) /\
  (forall k, r < k -> k < length H -> (nth r H 0%Z < nth k H 0%Z)%Z).
Proof.
  induction l as [|h rest IH]; intros H cur best_val best_idx Hmatch Hsum Hbi Hbval Hmin Hstrict.
  - simpl in Hsum. assert (Hcur : cur = length H) by lia. simpl.
    repeat split.
    + lia.
    + intros k Hk. rewrite Hbval. apply Hmin. lia.
    + intros k Hr Hk. rewrite Hbval. apply Hstrict; lia.
  - simpl in Hsum.
    assert (Hh : nth cur H 0%Z = h).
    { specialize (Hmatch 0 ltac:(simpl; lia)).
      simpl in Hmatch. rewrite Nat.add_0_r in Hmatch.
      rewrite <- Hmatch. reflexivity. }
    simpl find_last_min.
    assert (Hmatch_rest : forall i, i < length rest -> nth i rest 0%Z = nth (S cur + i) H 0%Z).
    { intros i Hi.
      specialize (Hmatch (S i) ltac:(simpl; lia)).
      simpl in Hmatch. rewrite Hmatch. f_equal. lia. }
    destruct (Z.leb_spec h best_val) as [Hle|Hgt].
    + apply (IH H (S cur) h cur).
      * exact Hmatch_rest.
      * lia.
      * lia.
      * exact Hh.
      * intros j Hj.
        destruct (Nat.eq_dec j cur) as [Heq|Hne].
        -- rewrite Heq, Hh. lia.
        -- assert (Hjc : j < cur) by lia.
           pose proof (Hmin j Hjc). lia.
      * intros j Hcj Hjsc.
        assert (Hjeq : j = cur) by lia. rewrite Hjeq, Hh. lia.
    + apply (IH H (S cur) best_val best_idx).
      * exact Hmatch_rest.
      * lia.
      * lia.
      * exact Hbval.
      * intros j Hj.
        destruct (Nat.eq_dec j cur) as [Heq|Hne].
        -- rewrite Heq, Hh. lia.
        -- apply Hmin. lia.
      * intros j Hbij Hjsc.
        destruct (Nat.eq_dec j cur) as [Heq|Hne].
        -- rewrite Heq, Hh. lia.
        -- apply Hstrict. exact Hbij. lia.
Qed.

(** Specialize: for prefix_heights p with H = prefix_heights p. *)
Lemma last_min_idx_correct : forall p,
  let r := last_min_idx p in
  r <= length p /\
  (forall k, k <= length p -> (nth r (prefix_heights p) 0%Z <= nth k (prefix_heights p) 0%Z)%Z) /\
  (forall k, r < k -> k <= length p -> (nth r (prefix_heights p) 0%Z < nth k (prefix_heights p) 0%Z)%Z).
Proof.
  intros p. unfold last_min_idx.
  pose proof (prefix_heights_length p) as Hlen.
  destruct (prefix_heights p) as [|h rest] eqn:Eh.
  - simpl in Hlen. lia.
  - simpl in Hlen.
    set (H := h :: rest).
    assert (Hh_nth : nth 0 H 0%Z = h) by reflexivity.
    pose proof (find_last_min_correct rest H 1 h 0) as Hcorr.
    assert (Hmatch : forall i, i < length rest -> nth i rest 0%Z = nth (1 + i) H 0%Z).
    { intros i Hi. subst H. simpl. reflexivity. }
    assert (Hsum : 1 + length rest = length H) by (subst H; simpl; lia).
    assert (Hmin0 : forall j, j < 1 -> (h <= nth j H 0%Z)%Z).
    { intros j Hj. assert (Hjeq : j = 0) by lia. rewrite Hjeq, Hh_nth. lia. }
    assert (Hstrict0 : forall j, 0 < j -> j < 1 -> (h < nth j H 0%Z)%Z).
    { intros. lia. }
    specialize (Hcorr Hmatch Hsum ltac:(lia) Hh_nth Hmin0 Hstrict0).
    simpl in Hcorr.
    destruct Hcorr as [Hbnd [Hminall Hstrall]].
    subst H. simpl length in *.
    repeat split.
    + lia.
    + intros k Hk. apply Hminall. lia.
    + intros k Hr Hk. apply Hstrall; lia.
Qed.

(** PROPERTY 2 (MINIMUM). *)
Lemma last_min_idx_is_min : forall p k,
  k <= length p ->
  (height_at p (last_min_idx p) <= height_at p k)%Z.
Proof.
  intros p k Hk.
  pose proof (last_min_idx_correct p) as [Hbnd [Hmin _]].
  rewrite <- (nth_prefix_heights p (last_min_idx p) Hbnd).
  rewrite <- (nth_prefix_heights p k Hk).
  apply Hmin. exact Hk.
Qed.

(** PROPERTY 3 (STRICT AFTER). *)
Lemma last_min_idx_strict_after : forall p k,
  last_min_idx p < k -> k <= length p ->
  (height_at p (last_min_idx p) < height_at p k)%Z.
Proof.
  intros p k Hr Hk.
  pose proof (last_min_idx_correct p) as [Hbnd [_ Hstr]].
  rewrite <- (nth_prefix_heights p (last_min_idx p) Hbnd).
  rewrite <- (nth_prefix_heights p k Hk).
  apply Hstr; exact Hr || exact Hk.
Qed.

(** =================================================================== *)
(** WRAP-FORMULA for rotation heights (the second case).               *)
(** =================================================================== *)

Lemma height_at_rotate_k_wrap : forall j p k,
  1 <= j -> j <= length p ->
  length p < k + j -> k <= length p ->
  (height_at (rotate_k j p) k
   = total_height p + height_at p (k + j - length p) - height_at p j)%Z.
Proof.
  induction j as [|j IH]; intros p k Hj1 Hjp Hwrap Hk.
  - lia.
  - destruct j as [|j'].
    + (* j = 0, S j = 1 *)
      assert (Hk_eq : k = length p) by lia.
      subst k.
      replace (length p + 1 - length p) with 1 by lia.
      pose proof (rotate_k_total_height 1 p) as Htot.
      unfold total_height in Htot.
      rewrite rotate_k_length in Htot.
      unfold total_height. rewrite Htot. lia.
    + (* j = S j' so S j = S (S j') *)
      destruct (Nat.eq_dec k (length p)) as [Hk_eq|Hk_neq].
      * subst k.
        replace (length p + S (S j') - length p) with (S (S j')) by lia.
        pose proof (rotate_k_total_height (S (S j')) p) as Htot.
        unfold total_height in Htot.
        rewrite rotate_k_length in Htot.
        unfold total_height. rewrite Htot. lia.
      * assert (Hk_lt : k < length p) by lia.
        assert (Hcompose : rotate_k (S (S j')) p = rotate_one (rotate_k (S j') p))
          by reflexivity.
        rewrite Hcompose.
        rewrite height_at_rotate_one_le_gen.
        2: { rewrite rotate_k_length. lia. }
        rewrite (IH p (S k)) by lia.
        rewrite (height_at_rotate_k_no_wrap (S j') p 1) by lia.
        replace (1 + S j') with (S (S j')) by lia.
        replace (S k + S j' - length p) with (k + S (S j') - length p) by lia.
        lia.
Qed.

(** =================================================================== *)
(** EXISTENCE (cycle lemma, half 1) — full proof using above.           *)
(** =================================================================== *)
Theorem cycle_lemma_exists : forall n p,
  is_augmented n p ->
  exists j, j < 2 * n + 1 /\ is_good (rotate_k j p).
Proof.
  intros n p Haug.
  pose proof (augmented_length n p Haug) as Hlen.
  pose proof (augmented_total_height n p Haug) as Htotal_raw.
  assert (Htotal : height_at p (length p) = 1%Z).
  { unfold total_height in Htotal_raw. exact Htotal_raw. }
  set (j := last_min_idx p) in *.
  pose proof (last_min_idx_le_length p) as Hjbound.
  fold j in Hjbound.
  assert (Hj_min : (height_at p j <= 0)%Z).
  { pose proof (last_min_idx_is_min p 0 (Nat.le_0_l _)) as Hh0.
    rewrite height_at_0 in Hh0. fold j in Hh0. exact Hh0. }
  assert (Hj_lt : j < 2 * n + 1).
  { destruct (Nat.eq_dec j (length p)) as [Heq|Hneq].
    - exfalso. rewrite Heq in Hj_min. rewrite Htotal in Hj_min. lia.
    - rewrite <- Hlen. lia. }
  exists j. split; [exact Hj_lt|].
  intros k Hk1 Hklen.
  rewrite rotate_k_length in Hklen.
  rewrite Hlen in Hklen.
  destruct (Nat.le_gt_cases (k + j) (length p)) as [Hkw|Hkw].
  - rewrite height_at_rotate_k_no_wrap by lia.
    pose proof (last_min_idx_strict_after p (k + j)) as Hstrict.
    fold j in Hstrict.
    assert (Hkj_lt : j < k + j) by lia.
    specialize (Hstrict Hkj_lt Hkw). lia.
  - assert (Hj1 : 1 <= j).
    { destruct (Nat.eq_dec j 0) as [Hj0|Hj0]; [|lia].
      exfalso. rewrite Hj0 in Hkw. rewrite Hlen in Hkw. lia. }
    rewrite height_at_rotate_k_wrap; [|lia|lia|lia|lia].
    unfold total_height. rewrite Htotal.
    assert (Hidx_lb : 1 <= k + j - length p) by lia.
    assert (Hidx_ub : k + j - length p <= j) by lia.
    pose proof (last_min_idx_is_min p (k + j - length p)) as Hmin.
    fold j in Hmin.
    specialize (Hmin ltac:(lia)). lia.
Qed.

(** =================================================================== *)
(** UNIQUENESS via "good has no nontrivial good rotation"               *)
(** =================================================================== *)

(** A good augmented sequence has no non-trivial good rotation. *)
Lemma good_aug_no_nontrivial_good_rotation : forall n q r,
  is_augmented n q -> is_good q ->
  1 <= r -> r < 2 * n + 1 ->
  ~ is_good (rotate_k r q).
Proof.
  intros n q r Haug Hgood Hr1 Hrm Hgood_rot.
  pose proof (augmented_length n q Haug) as Hqlen.
  set (m := 2 * n + 1) in *.
  (* Step 1: rotation height formula at index m - r. *)
  assert (Hr_le : r <= m) by lia.
  assert (Hmr_pos : 1 <= m - r) by lia.
  assert (Hmr_bound : r + (m - r) <= length q) by lia.
  pose proof (height_at_rotate_k_no_wrap r q (m - r) Hmr_bound) as Hformula.
  (* Hformula : height_at (rotate_k r q) (m - r) = height_at q ((m - r) + r) - height_at q r *)
  replace ((m - r) + r) with m in Hformula by lia.
  (* Step 2: height_at q m = 1 (augmented). *)
  pose proof (augmented_total_height n q Haug) as Htotal.
  unfold total_height in Htotal. rewrite Hqlen in Htotal.
  rewrite Htotal in Hformula.
  (* Hformula : height_at (rotate_k r q) (m - r) = 1 - height_at q r *)
  (* Step 3: is_good_rot gives 1 <= height_at (rotate_k r q) (m - r). *)
  assert (Hmr_lq : m - r <= length (rotate_k r q)) by (rewrite rotate_k_length; lia).
  pose proof (Hgood_rot (m - r) Hmr_pos Hmr_lq) as Hgood_at_mr.
  (* Step 4: is_good q gives 1 <= height_at q r. *)
  assert (Hr_lq : r <= length q) by lia.
  pose proof (Hgood r Hr1 Hr_lq) as Hgood_at_r.
  (* Step 5: contradiction. *)
  lia.
Qed.

(** UNIQUENESS proper. *)
Theorem cycle_lemma_unique : forall n p i j,
  is_augmented n p ->
  i < 2 * n + 1 -> j < 2 * n + 1 ->
  is_good (rotate_k i p) -> is_good (rotate_k j p) ->
  i = j.
Proof.
  intros n p i j Haug Hi Hj Hgi Hgj.
  destruct (Nat.lt_trichotomy i j) as [Hij|[Hij|Hij]]; [|exact Hij|].
  - (* i < j *)
    exfalso.
    set (q := rotate_k i p).
    assert (Hq_aug : is_augmented n q) by (subst q; apply rotate_k_augmented; exact Haug).
    assert (Hq_good : is_good q) by exact Hgi.
    pose proof (rotate_k_compose (j - i) i p) as Hcompose.
    replace (j - i + i) with j in Hcompose by lia.
    (* Hcompose : rotate_k (j - i) (rotate_k i p) = rotate_k j p *)
    fold q in Hcompose.
    rewrite <- Hcompose in Hgj.
    (* Hgj : is_good (rotate_k (j - i) q) *)
    assert (Hji_pos : 1 <= j - i) by lia.
    assert (Hji_bound : j - i < 2 * n + 1) by lia.
    exact (good_aug_no_nontrivial_good_rotation n q (j - i) Hq_aug Hq_good Hji_pos Hji_bound Hgj).
  - (* i > j: symmetric *)
    exfalso.
    set (q := rotate_k j p).
    assert (Hq_aug : is_augmented n q) by (subst q; apply rotate_k_augmented; exact Haug).
    assert (Hq_good : is_good q) by exact Hgj.
    pose proof (rotate_k_compose (i - j) j p) as Hcompose.
    replace (i - j + j) with i in Hcompose by lia.
    fold q in Hcompose.
    rewrite <- Hcompose in Hgi.
    assert (Hij_pos : 1 <= i - j) by lia.
    assert (Hij_bound : i - j < 2 * n + 1) by lia.
    exact (good_aug_no_nontrivial_good_rotation n q (i - j) Hq_aug Hq_good Hij_pos Hij_bound Hgi).
Qed.

(** APERIODICITY note: this property holds for augmented sequences (since
    gcd(n+1, n) = 1), but the cycle_lemma_count assembly via Phi-bijection
    does NOT require aperiodicity. We omit it here. *)

(* ========================================================================= *)
(*                  PART VI: BIJECTION GOOD <-> DYCK                        *)
(* ========================================================================= *)

(** Stripping the first step of an augmented sequence. *)
Definition strip_first (p : Path) : Path := tl p.

(** Prepending U gives the inverse direction. *)
Definition prepend_U (p : Path) : Path := U :: p.

(** A good augmented sequence must start with U: otherwise height_at p 1 = -1 < 1. *)
Lemma good_augmented_starts_U : forall n p,
  is_augmented n p -> is_good p -> exists rest, p = U :: rest.
Proof.
  intros n p Haug Hgood.
  destruct Haug as [HL [HU HD]].
  destruct p as [|a rest].
  - simpl in HL. lia.
  - exists rest. f_equal.
    destruct a; auto.
    (* If a = D (false), then height_at p 1 = -1, contradicting is_good. *)
    exfalso.
    assert (Hk1: (1 <= 1)%nat) by lia.
    assert (Hk1L: (1 <= length (false :: rest))%nat).
    { simpl. lia. }
    specialize (Hgood 1 Hk1 Hk1L).
    unfold height_at in Hgood. simpl in Hgood.
    lia.
Qed.

(** Height behaviour when prepending U: shifts all prefix sums up by 1. *)
Lemma height_at_cons_U : forall p k,
  height_at (true :: p) (S k) = (1 + height_at p k)%Z.
Proof.
  intros p k.
  unfold height_at.
  cbn [firstn count_U count_D].
  rewrite Nat2Z.inj_succ. lia.
Qed.

(** Stripping a good augmented sequence yields a Dyck path of length 2n. *)
Lemma good_to_dyck : forall n p,
  is_augmented n p -> is_good p ->
  length (strip_first p) = 2 * n /\
  count_U (strip_first p) = n /\
  count_D (strip_first p) = n /\
  is_dyck (strip_first p).
Proof.
  intros n p Haug Hgood.
  pose proof (good_augmented_starts_U n p Haug Hgood) as [rest Heq].
  destruct Haug as [HL [HU HD]].
  unfold U in Heq. subst p.
  unfold strip_first. cbn [tl].
  change (length (true :: rest)) with (S (length rest)) in HL.
  change (count_U (true :: rest)) with (S (count_U rest)) in HU.
  change (count_D (true :: rest)) with (count_D rest) in HD.
  split; [|split; [|split]].
  - lia.
  - lia.
  - exact HD.
  - unfold is_dyck. split; [lia|].
    intros k Hk.
    assert (Hk1 : 1 <= S k) by lia.
    assert (Hk2 : S k <= length (true :: rest)).
    { change (length (true :: rest)) with (S (length rest)). lia. }
    pose proof (Hgood (S k) Hk1 Hk2) as Hh.
    rewrite height_at_cons_U in Hh.
    lia.
Qed.

(** Conversely, prepending U to a Dyck path gives a good augmented sequence. *)
Lemma dyck_to_good : forall n p,
  length p = 2 * n -> count_U p = n -> count_D p = n -> is_dyck p ->
  is_augmented n (prepend_U p) /\ is_good (prepend_U p).
Proof.
  intros n p HL HU HD [Hbal Hnn].
  unfold prepend_U, U. split.
  - unfold is_augmented. cbn [length count_U count_D]. repeat split; lia.
  - intros k Hk1 Hk2.
    destruct k as [|k']; [lia|].
    assert (Hk' : k' <= length p).
    { cbn [length] in Hk2. lia. }
    specialize (Hnn k' Hk').
    rewrite height_at_cons_U. lia.
Qed.

(* ========================================================================= *)
(*                  PART VII: BINOMIAL COEFFICIENTS                         *)
(* ========================================================================= *)

(** Defined via Pascal's rule — gives natural number values, no division. *)
Fixpoint binomial (n k : nat) : nat :=
  match n, k with
  | _,    0    => 1
  | 0,    S _  => 0
  | S n', S k' => binomial n' k' + binomial n' (S k')
  end.

Lemma binomial_0_0 : binomial 0 0 = 1.
Proof. reflexivity. Qed.

Lemma binomial_n_0 : forall n, binomial n 0 = 1.
Proof. destruct n; reflexivity. Qed.

Lemma binomial_lt : forall n k, n < k -> binomial n k = 0.
Proof.
  induction n as [|n IH]; intros k Hk.
  - destruct k; simpl; auto. lia.
  - destruct k as [|k]; simpl. lia.
    rewrite !IH; auto; lia.
Qed.

Lemma binomial_n_n : forall n, binomial n n = 1.
Proof.
  induction n as [|n IH]; simpl; auto.
  rewrite IH. rewrite binomial_lt; auto.
Qed.

(** Key identity for the cycle lemma -> Catalan formula transition:       *)
(**    (n+1) * C(2n+1, n) = (2n+1) * C(2n, n)                              *)
(** Equivalently, both equal (2n+1)! / (n! * n!). *)
(** Proof via the relation between binomial and factorial. *)

(** Unfolding lemmas for fact and binomial — avoid [simpl]'s
    over-aggressive reduction (which expands [S k * x] to [x + k * x]). *)
Lemma fact_S_eq : forall n, fact (S n) = S n * fact n.
Proof. reflexivity. Qed.

Lemma binomial_S_S_eq : forall n k,
  binomial (S n) (S k) = binomial n k + binomial n (S k).
Proof. reflexivity. Qed.

(** Connection between binomial and factorial. *)
Lemma binomial_fact : forall n k, k <= n ->
  binomial n k * (fact k * fact (n - k)) = fact n.
Proof.
  induction n as [|n IH]; intros k Hk.
  - inversion Hk. reflexivity.
  - destruct k as [|k].
    + (* k = 0: binomial (S n) 0 = 1, fact 0 = 1 *)
      simpl. replace (n - 0) with n by lia. lia.
    + assert (Hkn : k <= n) by lia.
      rewrite binomial_S_S_eq.
      replace (S n - S k) with (n - k) by lia.
      rewrite (fact_S_eq k).
      rewrite (fact_S_eq n).
      destruct (Nat.le_gt_cases (S k) n) as [HSkn|HSkn].
      * (* S k <= n: use IH for both branches *)
        pose proof (IH k Hkn) as IH1.
        pose proof (IH (S k) HSkn) as IH2.
        replace (n - k) with (S (n - S k)) by lia.
        replace (n - k) with (S (n - S k)) in IH1 by lia.
        rewrite (fact_S_eq (n - S k)).
        rewrite (fact_S_eq (n - S k)) in IH1.
        rewrite (fact_S_eq k) in IH2.
        (* Goal: (binomial n k + binomial n (S k))
                 * (S k * fact k * (S (n - S k) * fact (n - S k)))
                 = S n * fact n
           IH1:  binomial n k * (fact k * (S (n - S k) * fact (n - S k))) = fact n
           IH2:  binomial n (S k) * (S k * fact k * fact (n - S k)) = fact n *)
        assert (E1 : binomial n k *
                     (S k * fact k * (S (n - S k) * fact (n - S k)))
                     = S k * fact n).
        { rewrite <- IH1. ring. }
        assert (E2 : binomial n (S k) *
                     (S k * fact k * (S (n - S k) * fact (n - S k)))
                     = S (n - S k) * fact n).
        { rewrite <- IH2. ring. }
        replace (S n) with (S k + S (n - S k)) by lia.
        nia.
      * (* S k > n and S k <= S n, so k = n *)
        assert (k = n) by lia. subst.
        assert (Hzero : binomial n (S n) = 0) by (apply binomial_lt; lia).
        rewrite Hzero.
        rewrite binomial_n_n.
        replace (n - n) with 0 by lia.
        cbn [fact]. lia.
Qed.

(** The key algebraic identity. *)
Theorem cycle_to_catalan_identity : forall n,
  (n + 1) * binomial (2 * n + 1) n = (2 * n + 1) * binomial (2 * n) n.
Proof.
  intros n.
  pose proof (binomial_fact (2 * n + 1) n) as H1.
  specialize (H1 ltac:(lia)).
  replace (2 * n + 1 - n) with (S n) in H1 by lia.
  rewrite (fact_S_eq n) in H1.
  (* H1: binomial (2n+1) n * (fact n * (S n * fact n)) = fact (2n+1) *)

  pose proof (binomial_fact (2 * n) n) as H2.
  specialize (H2 ltac:(lia)).
  replace (2 * n - n) with n in H2 by lia.
  (* H2: binomial (2n) n * (fact n * fact n) = fact (2n) *)

  assert (Hfact : fact (2 * n + 1) = (2 * n + 1) * fact (2 * n)).
  { replace (2 * n + 1) with (S (2 * n)) by lia. apply fact_S_eq. }

  rewrite Hfact in H1.
  rewrite <- H2 in H1.
  (* H1: binomial (2n+1) n * (fact n * (S n * fact n))
       = (2n+1) * (binomial (2n) n * (fact n * fact n)) *)
  replace (S n) with (n + 1) in H1 by lia.

  (* Rearrange both sides into (fact n * fact n) * (target identity). *)
  assert (Hl : binomial (2 * n + 1) n * (fact n * ((n + 1) * fact n))
             = fact n * fact n * ((n + 1) * binomial (2 * n + 1) n)) by ring.
  assert (Hr : (2 * n + 1) * (binomial (2 * n) n * (fact n * fact n))
             = fact n * fact n * ((2 * n + 1) * binomial (2 * n) n)) by ring.
  rewrite Hl, Hr in H1.

  (* Cancel the positive factor (fact n * fact n). *)
  apply Nat.mul_cancel_l in H1.
  - exact H1.
  - pose proof (lt_O_fact n) as Hfn. nia.
Qed.

(* ========================================================================= *)
(*                  PART VIII: COUNTING DYCK PATHS                          *)
(* ========================================================================= *)

(** Enumeration of all length-m binary paths. *)
Fixpoint all_paths (m : nat) : list Path :=
  match m with
  | 0 => [[]]
  | S m' =>
      let prev := all_paths m' in
      map (cons true) prev ++ map (cons false) prev
  end.

Lemma all_paths_length : forall m p, In p (all_paths m) -> length p = m.
Proof.
  induction m as [|m IH]; intros p Hin; simpl in Hin.
  - destruct Hin as [Heq|[]]. subst. reflexivity.
  - apply in_app_or in Hin. destruct Hin as [Hin|Hin];
    apply in_map_iff in Hin; destruct Hin as [p' [Heq Hin']];
    subst; simpl; f_equal; apply IH; exact Hin'.
Qed.

(** Decidable Dyck. *)
Fixpoint is_dyck_b_aux (p : Path) (h : Z) : bool :=
  match p with
  | [] => Z.eqb h 0
  | true :: rest => is_dyck_b_aux rest (h + 1)
  | false :: rest =>
      if Z.ltb (h - 1) 0 then false
      else is_dyck_b_aux rest (h - 1)
  end.

Definition is_dyck_b (p : Path) : bool := is_dyck_b_aux p 0.

(** Count of Dyck paths of length 2n. *)
Definition num_dyck (n : nat) : nat :=
  length (filter is_dyck_b (all_paths (2 * n))).

(** Count of augmented sequences. *)
Definition is_augmented_b (n : nat) (p : Path) : bool :=
  Nat.eqb (count_U p) (n + 1) && Nat.eqb (count_D p) n.

Definition num_augmented (n : nat) : nat :=
  length (filter (is_augmented_b n) (all_paths (2 * n + 1))).

(** ----- Helper: filter over [map (cons b) l] reduces to filter under cons. *)
Lemma filter_map_cons_length :
  forall (b : Step) (l : list Path) (pred : Path -> bool),
  length (filter pred (map (cons b) l))
  = length (filter (fun p => pred (b :: p)) l).
Proof.
  induction l as [|p l IH]; intros pred; simpl; auto.
  destruct (pred (b :: p)); simpl; rewrite IH; reflexivity.
Qed.

(** Count paths of length [len] with [count_D = k] equals C(len, k). *)
Lemma count_D_eq_binomial : forall len k,
  length (filter (fun p => Nat.eqb (count_D p) k) (all_paths len))
  = binomial len k.
Proof.
  induction len as [|len IH]; intros k.
  - simpl. destruct k; reflexivity.
  - simpl.
    rewrite filter_app, length_app.
    rewrite filter_map_cons_length, filter_map_cons_length.
    destruct k as [|k'].
    + (* k = 0 *)
      assert (HT : forall xs,
        length (filter (fun p : Path => Nat.eqb (count_D (true :: p)) 0) xs)
        = length (filter (fun p : Path => Nat.eqb (count_D p) 0) xs))
        by (induction xs; simpl; auto).
      assert (HF : forall xs,
        length (filter (fun p : Path => Nat.eqb (count_D (false :: p)) 0) xs) = 0)
        by (induction xs; simpl; auto).
      rewrite HT, HF, IH.
      rewrite !binomial_n_0. lia.
    + (* k = S k' *)
      assert (HT : forall xs,
        length (filter (fun p : Path => Nat.eqb (count_D (true :: p)) (S k')) xs)
        = length (filter (fun p : Path => Nat.eqb (count_D p) (S k')) xs))
        by (induction xs; simpl; auto).
      assert (HF : forall xs,
        length (filter (fun p : Path => Nat.eqb (count_D (false :: p)) (S k')) xs)
        = length (filter (fun p : Path => Nat.eqb (count_D p) k') xs))
        by (induction xs; simpl; auto).
      rewrite HT, HF, IH, IH.
      change (binomial (S len) (S k')) with (binomial len k' + binomial len (S k')).
      lia.
Qed.

(** Equivalence between is_augmented_b and the simpler count_D-only check,
    valid for paths drawn from all_paths(2n+1). *)
Lemma is_augmented_b_eq_count_D : forall n p,
  In p (all_paths (2 * n + 1)) ->
  is_augmented_b n p = Nat.eqb (count_D p) n.
Proof.
  intros n p Hin.
  pose proof (all_paths_length _ _ Hin) as Hlen.
  pose proof (count_UD_length p) as HUD.
  unfold is_augmented_b.
  destruct (Nat.eqb_spec (count_D p) n) as [HD|HD].
  - assert (Hcu : count_U p = n + 1) by lia.
    rewrite Hcu, Nat.eqb_refl. reflexivity.
  - apply Bool.andb_false_r.
Qed.

(** The number of augmented sequences = C(2n+1, n). *)
Theorem num_augmented_binomial : forall n,
  num_augmented n = binomial (2 * n + 1) n.
Proof.
  intros n. unfold num_augmented.
  erewrite filter_ext_in.
  - apply count_D_eq_binomial.
  - intros p Hin. apply is_augmented_b_eq_count_D. exact Hin.
Qed.

(* ========================================================================= *)
(*                  PART IX: THE CYCLE LEMMA COUNT THEOREM                  *)
(* ========================================================================= *)

(** Count of good augmented sequences. *)
Definition num_good (n : nat) : nat :=
  length (filter (fun p => andb (is_augmented_b n p) (is_good_b p))
                 (all_paths (2 * n + 1))).

(** ----------------------------------------------------------------------- *)
(** Boolean correctness lemmas to support num_good = num_dyck.            *)
(** ----------------------------------------------------------------------- *)

(** Helper: forall_pos_heights returns false if any inner check fails. *)
Lemma forall_pos_heights_with_neg_first : forall p k,
  1 <= k ->
  Z.leb 1 (height_at p 1) = false ->
  forall_pos_heights p k = false.
Proof.
  intros p k Hk Hh.
  induction k as [|k' IH].
  - lia.
  - cbn [forall_pos_heights].
    destruct k' as [|k''].
    + rewrite Hh. reflexivity.
    + rewrite IH by lia. apply Bool.andb_false_r.
Qed.

(** is_good_b on (false :: _) is always false. *)
Lemma is_good_b_false_cons : forall rest,
  is_good_b (false :: rest) = false.
Proof.
  intros rest. unfold is_good_b.
  apply forall_pos_heights_with_neg_first.
  - cbn [length]. lia.
  - unfold height_at. cbn [firstn count_U count_D]. reflexivity.
Qed.

(** forall_pos_heights reflects the prefix-height property. *)
Lemma forall_pos_heights_iff : forall p k,
  forall_pos_heights p k = true <->
  (forall i, 1 <= i -> i <= k -> (1 <= height_at p i)%Z).
Proof.
  intros p. induction k as [|k IH]; intros.
  - simpl. split.
    + intros _ i Hi1 Hi0. lia.
    + intros. reflexivity.
  - cbn [forall_pos_heights]. rewrite Bool.andb_true_iff, Z.leb_le, IH.
    split.
    + intros [Hsk Hrest] i Hi1 HiSk.
      destruct (Nat.eq_dec i (S k)) as [Heq|Hne].
      * rewrite Heq. exact Hsk.
      * apply Hrest; lia.
    + intros H. split.
      * apply H; lia.
      * intros i Hi1 Hik. apply H; lia.
Qed.

(** is_good_b reflects is_good. *)
Lemma is_good_b_iff : forall p,
  is_good_b p = true <-> is_good p.
Proof.
  intros p. unfold is_good_b, is_good.
  apply forall_pos_heights_iff.
Qed.

(** is_dyck_b_aux returns true iff the height stays ≥ 0 throughout and
    ends at 0 (when started at non-negative h). *)
Lemma is_dyck_b_aux_iff : forall p h,
  (0 <= h)%Z ->
  is_dyck_b_aux p h = true <->
  (forall k, k <= length p -> (0 <= h + height_at p k)%Z) /\
  (h + height_at p (length p) = 0)%Z.
Proof.
  intros p. induction p as [|x rest IH]; intros h Hh0.
  - cbn [is_dyck_b_aux length]. rewrite Z.eqb_eq.
    split.
    + intros Hh. split.
      * intros k Hk. assert (k = 0) by lia. subst.
        rewrite height_at_0. lia.
      * rewrite height_at_0. lia.
    + intros [_ Hh]. rewrite height_at_0 in Hh. lia.
  - destruct x.
    + (* true *)
      cbn [is_dyck_b_aux]. rewrite IH by lia.
      split; intros [Hall Hfin].
      * split.
        -- intros k Hk. destruct k as [|k']; cbn [length] in Hk.
           ++ rewrite height_at_0. lia.
           ++ specialize (Hall k' ltac:(lia)).
              unfold height_at.
              change (firstn (S k') (true :: rest)) with (true :: firstn k' rest).
              cbn [count_U count_D]. rewrite Nat2Z.inj_succ.
              unfold height_at in Hall. lia.
        -- cbn [length].
           unfold height_at.
           change (firstn (S (length rest)) (true :: rest)) with (true :: firstn (length rest) rest).
           cbn [count_U count_D]. rewrite Nat2Z.inj_succ.
           unfold height_at in Hfin. lia.
      * split.
        -- intros k Hk.
           specialize (Hall (S k) ltac:(cbn [length]; lia)).
           unfold height_at in Hall.
           change (firstn (S k) (true :: rest)) with (true :: firstn k rest) in Hall.
           cbn [count_U count_D] in Hall. rewrite Nat2Z.inj_succ in Hall.
           unfold height_at. lia.
        -- cbn [length] in Hfin.
           unfold height_at in Hfin.
           change (firstn (S (length rest)) (true :: rest)) with (true :: firstn (length rest) rest) in Hfin.
           cbn [count_U count_D] in Hfin. rewrite Nat2Z.inj_succ in Hfin.
           unfold height_at. lia.
    + (* false *)
      cbn [is_dyck_b_aux].
      destruct (Z.ltb_spec (h - 1) 0) as [Hneg|Hpos].
      * split.
        -- discriminate.
        -- intros [Hall Hfin].
           specialize (Hall 1 ltac:(cbn [length]; lia)).
           unfold height_at in Hall.
           change (firstn 1 (false :: rest)) with (false :: @nil Step) in Hall.
           cbn [count_U count_D] in Hall. lia.
      * rewrite IH by lia.
        split; intros [Hall Hfin].
        -- split.
           ++ intros k Hk. destruct k as [|k']; cbn [length] in Hk.
              ** rewrite height_at_0. lia.
              ** specialize (Hall k' ltac:(lia)).
                 unfold height_at.
                 change (firstn (S k') (false :: rest)) with (false :: firstn k' rest).
                 cbn [count_U count_D]. rewrite Nat2Z.inj_succ.
                 unfold height_at in Hall. lia.
           ++ cbn [length].
              unfold height_at.
              change (firstn (S (length rest)) (false :: rest)) with (false :: firstn (length rest) rest).
              cbn [count_U count_D]. rewrite Nat2Z.inj_succ.
              unfold height_at in Hfin. lia.
        -- split.
           ++ intros k Hk.
              specialize (Hall (S k) ltac:(cbn [length]; lia)).
              unfold height_at in Hall.
              change (firstn (S k) (false :: rest)) with (false :: firstn k rest) in Hall.
              cbn [count_U count_D] in Hall. rewrite Nat2Z.inj_succ in Hall.
              unfold height_at. lia.
           ++ cbn [length] in Hfin.
              unfold height_at in Hfin.
              change (firstn (S (length rest)) (false :: rest)) with (false :: firstn (length rest) rest) in Hfin.
              cbn [count_U count_D] in Hfin. rewrite Nat2Z.inj_succ in Hfin.
              unfold height_at. lia.
Qed.

(** is_dyck_b reflects the Dyck-path property. *)
Lemma is_dyck_b_iff : forall p,
  is_dyck_b p = true <->
  (forall k, k <= length p -> (0 <= height_at p k)%Z) /\
  (height_at p (length p) = 0)%Z.
Proof.
  intros p. unfold is_dyck_b.
  rewrite is_dyck_b_aux_iff by lia.
  split; intros [Hall Hfin]; split.
  - intros k Hk. specialize (Hall k Hk). lia.
  - lia.
  - intros k Hk. specialize (Hall k Hk). lia.
  - lia.
Qed.

(** For p of length 2n: count_U p = n iff height_at p (length p) = 0. *)
Lemma length_2n_count_U_iff_height_0 : forall n p,
  length p = 2 * n ->
  count_U p = n <-> height_at p (length p) = 0%Z.
Proof.
  intros n p Hlen.
  pose proof (count_UD_length p) as HUD.
  rewrite Hlen in HUD.
  unfold height_at. rewrite firstn_all_eq.
  split.
  - intros HcU.
    assert (count_D p = n) by lia.
    rewrite HcU, H. lia.
  - intros Hh. lia.
Qed.

(** The combined boolean equality on the true branch. *)
Lemma good_aug_true_iff_dyck_b : forall n p,
  length p = 2 * n ->
  andb (is_augmented_b n (true :: p)) (is_good_b (true :: p)) = is_dyck_b p.
Proof.
  intros n p Hlen.
  apply Bool.eq_true_iff_eq.
  rewrite Bool.andb_true_iff, is_good_b_iff, is_dyck_b_iff.
  unfold is_augmented_b.
  rewrite Bool.andb_true_iff, !Nat.eqb_eq.
  change (count_U (true :: p)) with (S (count_U p)).
  change (count_D (true :: p)) with (count_D p).
  pose proof (count_UD_length p) as HUD0.
  assert (HUD : count_U p + count_D p = 2 * n).
  { transitivity (length p). exact HUD0. exact Hlen. }
  clear HUD0.
  split.
  - intros [[HcU HcD] Hgood].
    unfold is_good in Hgood.
    split.
    + intros k Hk.
      assert (Hk1 : 1 <= S k) by lia.
      assert (Hk2 : S k <= length (true :: p)).
      { apply le_n_S. exact Hk. }
      specialize (Hgood (S k) Hk1 Hk2).
      rewrite (height_at_cons_U p k) in Hgood.
      lia.
    + unfold height_at. rewrite firstn_all_eq. lia.
  - intros [Hall Hfin].
    repeat split.
    + (* count_U p = n: from Hfin, count_U p = count_D p; combined with HUD = length 2n *)
      assert (HcU_eq : count_U p = count_D p).
      { unfold height_at in Hfin. rewrite firstn_all_eq in Hfin. lia. }
      lia.
    + (* count_D p = n *)
      assert (HcU_eq : count_U p = count_D p).
      { unfold height_at in Hfin. rewrite firstn_all_eq in Hfin. lia. }
      lia.
    + (* is_good (true :: p) *)
      unfold is_good. intros k Hk1 Hk2.
      change (length (true :: p)) with (S (length p)) in Hk2.
      destruct k as [|k']; [lia|].
      rewrite height_at_cons_U.
      assert (Hk2' : k' <= length p) by lia.
      specialize (Hall k' Hk2'). lia.
Qed.

(** ----------------------------------------------------------------------- *)
(** SUB-LEMMA 1: num_good = num_dyck                                       *)
(** ----------------------------------------------------------------------- *)
Lemma num_good_eq_num_dyck : forall n, num_good n = num_dyck n.
Proof.
  intros n. unfold num_good, num_dyck.
  replace (2 * n + 1) with (S (2 * n)) by lia.
  cbn [all_paths].
  rewrite filter_app, length_app.
  rewrite filter_map_cons_length, filter_map_cons_length.
  assert (Hfalse_zero : forall xs,
    length (filter (fun p => andb (is_augmented_b n (false :: p))
                                  (is_good_b (false :: p))) xs) = 0).
  { intros xs. induction xs as [|x rest IH]; simpl; auto.
    rewrite is_good_b_false_cons, Bool.andb_false_r. exact IH. }
  rewrite Hfalse_zero, Nat.add_0_r.
  f_equal. apply filter_ext_in.
  intros p Hp.
  pose proof (all_paths_length _ _ Hp) as Hplen.
  apply good_aug_true_iff_dyck_b. exact Hplen.
Qed.

(** ----------------------------------------------------------------------- *)
(** Helpers for the Phi-bijection proof.                                   *)
(** ----------------------------------------------------------------------- *)

(** Bool version of cycle_lemma_exists. *)
Lemma cycle_lemma_exists_b : forall n p,
  is_augmented n p ->
  exists j, j < 2 * n + 1 /\ is_good_b (rotate_k j p) = true.
Proof.
  intros n p Haug.
  destruct (cycle_lemma_exists n p Haug) as [j [Hjm Hjgood]].
  exists j. split; auto.
  apply is_good_b_iff. exact Hjgood.
Qed.

(** Bool version of cycle_lemma_unique. *)
Lemma cycle_lemma_unique_b : forall n p i j,
  is_augmented n p ->
  i < 2 * n + 1 -> j < 2 * n + 1 ->
  is_good_b (rotate_k i p) = true -> is_good_b (rotate_k j p) = true ->
  i = j.
Proof.
  intros n p i j Haug Hi Hj Hig Hjg.
  apply is_good_b_iff in Hig.
  apply is_good_b_iff in Hjg.
  apply (cycle_lemma_unique n p i j Haug Hi Hj Hig Hjg).
Qed.

(** is_augmented_b is equivalent to is_augmented under length constraint. *)
Lemma is_augmented_b_iff_pred : forall n p,
  length p = 2 * n + 1 ->
  is_augmented_b n p = true <-> is_augmented n p.
Proof.
  intros n p Hlen.
  pose proof (count_UD_length p) as Hud.
  assert (Hud' : count_U p + count_D p = 2 * n + 1).
  { transitivity (length p). exact Hud. exact Hlen. }
  unfold is_augmented_b, is_augmented.
  rewrite Bool.andb_true_iff, !Nat.eqb_eq.
  split.
  - intros [HcU HcD]. auto.
  - intros [HL [HcU HcD]]. auto.
Qed.

(** rotate_one is injective on same-length paths. *)
Lemma rotate_one_injective : forall p q,
  length p = length q ->
  rotate_one p = rotate_one q -> p = q.
Proof.
  intros [|x p'] [|y q'] Hlen H; simpl in *.
  - reflexivity.
  - discriminate Hlen.
  - discriminate Hlen.
  - apply app_inj_tail in H. destruct H as [Hp Hxy]. subst. reflexivity.
Qed.

(** rotate_k is injective on same-length paths. *)
Lemma rotate_k_injective : forall j p q,
  length p = length q ->
  rotate_k j p = rotate_k j q -> p = q.
Proof.
  induction j as [|j IH]; simpl; intros p q Hlen H.
  - exact H.
  - apply rotate_one_injective in H; [|rewrite !rotate_k_length; exact Hlen].
    apply IH; auto.
Qed.

(** Splits firstn (S j) into firstn j + last element. *)
Lemma firstn_S_split : forall (p : Path) (j : nat),
  j < length p ->
  firstn (S j) p = firstn j p ++ [nth j p false].
Proof.
  intros p. induction p as [|x rest IH]; intros j Hj; simpl in *.
  - lia.
  - destruct j as [|j']; simpl.
    + reflexivity.
    + rewrite IH by lia. reflexivity.
Qed.

(** Splits skipn at position j into head + skipn (S j). *)
Lemma skipn_cons_split : forall (p : Path) (j : nat),
  j < length p ->
  skipn j p = nth j p false :: skipn (S j) p.
Proof.
  intros p. induction p as [|x rest IH]; intros j Hj; simpl in *.
  - lia.
  - destruct j as [|j']; simpl.
    + reflexivity.
    + apply IH. lia.
Qed.

(** Key identity: rotate_k j p = skipn j p ++ firstn j p. *)
Lemma rotate_k_skipn_firstn : forall j p,
  j <= length p ->
  rotate_k j p = skipn j p ++ firstn j p.
Proof.
  induction j as [|j IH]; intros p Hj.
  - simpl. rewrite app_nil_r. reflexivity.
  - change (rotate_k (S j) p) with (rotate_one (rotate_k j p)).
    rewrite IH by lia.
    assert (Hj_lt : j < length p) by lia.
    pose proof (skipn_cons_split p j Hj_lt) as Hsk.
    rewrite Hsk.
    change (rotate_one ((nth j p false :: skipn (S j) p) ++ firstn j p))
      with ((skipn (S j) p ++ firstn j p) ++ [nth j p false]).
    pose proof (firstn_S_split p j Hj_lt) as Hfst.
    rewrite Hfst.
    rewrite <- app_assoc. reflexivity.
Qed.

(** Rotation by full length returns the path. *)
Lemma rotate_k_full : forall p, rotate_k (length p) p = p.
Proof.
  intros p.
  rewrite rotate_k_skipn_firstn by lia.
  rewrite skipn_all, firstn_all_eq.
  reflexivity.
Qed.

(** Every path of length m is in all_paths m. *)
Lemma all_paths_complete : forall p, In p (all_paths (length p)).
Proof.
  induction p as [|x rest IH]; simpl.
  - left; reflexivity.
  - apply in_or_app.
    destruct x.
    + left. apply in_map_iff. exists rest. split; auto.
    + right. apply in_map_iff. exists rest. split; auto.
Qed.

Lemma all_paths_complete_len : forall p m, length p = m -> In p (all_paths m).
Proof. intros p m H. subst. apply all_paths_complete. Qed.

(** Map cons preserves NoDup. *)
Lemma NoDup_map_cons_step : forall (b : Step) (l : list Path),
  NoDup l -> NoDup (map (cons b) l).
Proof.
  intros b l Hnd.
  induction Hnd as [|x rest Hnotin Hnd' IH]; simpl.
  - constructor.
  - constructor; auto.
    intros Hin. apply in_map_iff in Hin.
    destruct Hin as [y [Hy Hyin]].
    injection Hy as Hy'. subst y. apply Hnotin. exact Hyin.
Qed.

(** NoDup of concatenation of disjoint NoDup lists. *)
Lemma NoDup_app_disj : forall {A : Type} (l1 l2 : list A),
  NoDup l1 -> NoDup l2 ->
  (forall x, In x l1 -> ~ In x l2) ->
  NoDup (l1 ++ l2).
Proof.
  intros A l1 l2 H1 H2 Hdisj.
  induction H1 as [|x rest Hnotin Hnd1 IH]; simpl.
  - exact H2.
  - constructor.
    + intros Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
      * apply Hnotin. exact Hin.
      * apply (Hdisj x); [left; reflexivity | exact Hin].
    + apply IH. intros y Hy. apply Hdisj. right. exact Hy.
Qed.

(** NoDup of all_paths. *)
Lemma NoDup_all_paths : forall m, NoDup (all_paths m).
Proof.
  induction m as [|m IH]; simpl.
  - constructor; [intros H; inversion H | constructor].
  - apply NoDup_app_disj.
    + apply NoDup_map_cons_step. exact IH.
    + apply NoDup_map_cons_step. exact IH.
    + intros x H1 H2.
      apply in_map_iff in H1, H2.
      destruct H1 as [x1 [Hx1 _]].
      destruct H2 as [x2 [Hx2 _]].
      rewrite <- Hx1 in Hx2. discriminate.
Qed.

(** Injective f on a list preserves NoDup of map f. *)
Lemma NoDup_map_inj_on : forall {A B : Type} (f : A -> B) (l : list A),
  (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  NoDup l -> NoDup (map f l).
Proof.
  intros A B f l Hinj Hnd.
  induction Hnd as [|x rest Hnotin Hnd' IH]; simpl.
  - constructor.
  - constructor.
    + intros Hin. apply in_map_iff in Hin.
      destruct Hin as [y [Hy Hyin]].
      assert (Heq : x = y).
      { apply Hinj.
        - left; reflexivity.
        - right; exact Hyin.
        - rewrite Hy. reflexivity. }
      subst y. apply Hnotin. exact Hyin.
    + apply IH. intros x' y' H1 H2 Heq.
      apply Hinj.
      * right; exact H1.
      * right; exact H2.
      * exact Heq.
Qed.

(** Length of list_prod. *)
Lemma list_prod_length_eq : forall {A B : Type} (l1 : list A) (l2 : list B),
  length (list_prod l1 l2) = length l1 * length l2.
Proof.
  intros A B l1 l2.
  induction l1 as [|x rest IH]; simpl.
  - reflexivity.
  - rewrite length_app, length_map, IH. reflexivity.
Qed.

(** NoDup of list_prod. *)
Lemma NoDup_list_prod : forall {A B : Type} (l1 : list A) (l2 : list B),
  NoDup l1 -> NoDup l2 -> NoDup (list_prod l1 l2).
Proof.
  intros A B l1 l2 Hnd1 Hnd2.
  induction Hnd1 as [|x rest Hnotin Hnd1' IH]; simpl.
  - constructor.
  - apply NoDup_app_disj.
    + apply NoDup_map_inj_on.
      * intros y1 y2 _ _ Heq. injection Heq; auto.
      * exact Hnd2.
    + apply IH.
    + intros pair Hin_map Hin_rest.
      apply in_map_iff in Hin_map. destruct Hin_map as [y [Hpair _]]. subst pair.
      apply in_prod_iff in Hin_rest. destruct Hin_rest as [Hin_x _].
      apply Hnotin. exact Hin_x.
Qed.

(** ----------------------------------------------------------------------- *)
(** SUB-LEMMA 2: (2n+1) * num_good = num_augmented (via Phi-bijection)    *)
(** ----------------------------------------------------------------------- *)
Lemma rotation_count_relation : forall n,
  (2 * n + 1) * num_good n = num_augmented n.
Proof.
  intros n.
  set (m := 2 * n + 1).
  unfold num_good, num_augmented. fold m.
  set (good_list := filter (fun p : Path => andb (is_augmented_b n p) (is_good_b p))
                           (all_paths m)).
  set (aug_list := filter (is_augmented_b n) (all_paths m)).
  set (m_seq := seq 0 m).
  set (phi := fun pair : Path * nat => rotate_k (snd pair) (fst pair)).
  set (rotation_list := map phi (list_prod good_list m_seq)).

  (* Step 1: |rotation_list| = num_good * m. *)
  assert (Hlen_rot : length rotation_list = length good_list * m).
  { subst rotation_list. rewrite length_map.
    rewrite list_prod_length_eq.
    subst m_seq. rewrite length_seq. reflexivity. }

  (* Step 2: Permutation rotation_list aug_list. *)
  assert (Hperm : Permutation rotation_list aug_list).
  { apply NoDup_Permutation.
    - (* NoDup rotation_list *)
      subst rotation_list.
      apply NoDup_map_inj_on.
      + (* Phi is injective on list_prod good_list m_seq *)
        intros (q1, j1) (q2, j2) Hin1 Hin2 Hphi_eq.
        unfold phi in Hphi_eq. simpl in Hphi_eq.
        apply in_prod_iff in Hin1.
        apply in_prod_iff in Hin2.
        destruct Hin1 as [Hq1_in Hj1_in].
        destruct Hin2 as [Hq2_in Hj2_in].
        subst good_list. apply filter_In in Hq1_in.
        destruct Hq1_in as [Hq1_path Hq1_ab].
        apply Bool.andb_true_iff in Hq1_ab.
        destruct Hq1_ab as [Hq1_aug_b Hq1_good_b].
        apply filter_In in Hq2_in.
        destruct Hq2_in as [Hq2_path Hq2_ab].
        apply Bool.andb_true_iff in Hq2_ab.
        destruct Hq2_ab as [Hq2_aug_b Hq2_good_b].
        subst m_seq. apply in_seq in Hj1_in, Hj2_in.
        pose proof (all_paths_length _ _ Hq1_path) as Hlen_q1.
        pose proof (all_paths_length _ _ Hq2_path) as Hlen_q2.
        apply is_augmented_b_iff_pred in Hq1_aug_b; [|exact Hlen_q1].
        apply is_augmented_b_iff_pred in Hq2_aug_b; [|exact Hlen_q2].
        apply is_good_b_iff in Hq1_good_b, Hq2_good_b.
        destruct (Nat.eq_dec j1 j2) as [Heq|Hneq].
        * subst j2. f_equal.
          apply rotate_k_injective in Hphi_eq; [exact Hphi_eq|lia].
        * exfalso.
          destruct (Nat.lt_ge_cases j1 j2) as [Hlt|Hge].
          -- pose proof (rotate_k_compose j1 (j2 - j1) q2) as Hcomp.
             replace (j1 + (j2 - j1)) with j2 in Hcomp by lia.
             rewrite <- Hcomp in Hphi_eq.
             apply rotate_k_injective in Hphi_eq;
               [|rewrite rotate_k_length; lia].
             assert (Hr : 1 <= j2 - j1) by lia.
             assert (Hr2 : j2 - j1 < 2 * n + 1) by lia.
             pose proof (good_aug_no_nontrivial_good_rotation n q2 (j2 - j1)
                          Hq2_aug_b Hq2_good_b Hr Hr2) as Hnotgood.
             apply Hnotgood. rewrite <- Hphi_eq. exact Hq1_good_b.
          -- assert (Hjlt : j2 < j1) by lia.
             pose proof (rotate_k_compose j2 (j1 - j2) q1) as Hcomp.
             replace (j2 + (j1 - j2)) with j1 in Hcomp by lia.
             rewrite <- Hcomp in Hphi_eq.
             symmetry in Hphi_eq.
             apply rotate_k_injective in Hphi_eq;
               [|rewrite rotate_k_length; lia].
             assert (Hr : 1 <= j1 - j2) by lia.
             assert (Hr2 : j1 - j2 < 2 * n + 1) by lia.
             pose proof (good_aug_no_nontrivial_good_rotation n q1 (j1 - j2)
                          Hq1_aug_b Hq1_good_b Hr Hr2) as Hnotgood.
             apply Hnotgood. rewrite <- Hphi_eq. exact Hq2_good_b.
      + (* NoDup (list_prod good_list m_seq) *)
        apply NoDup_list_prod.
        * subst good_list. apply NoDup_filter. apply NoDup_all_paths.
        * subst m_seq. apply seq_NoDup.
    - (* NoDup aug_list *)
      subst aug_list. apply NoDup_filter. apply NoDup_all_paths.
    - (* In equivalence *)
      intros p. split.
      + (* p in rotation_list -> p in aug_list *)
        intros Hin. subst rotation_list.
        apply in_map_iff in Hin.
        destruct Hin as [(q, j) [Hphi_eq Hin_qj]].
        unfold phi in Hphi_eq. simpl in Hphi_eq. subst p.
        apply in_prod_iff in Hin_qj.
        destruct Hin_qj as [Hq_in Hj_in].
        subst good_list. apply filter_In in Hq_in.
        destruct Hq_in as [Hq_path Hq_ab].
        apply Bool.andb_true_iff in Hq_ab.
        destruct Hq_ab as [Hq_aug_b _].
        pose proof (all_paths_length _ _ Hq_path) as Hlen_q.
        pose proof (is_augmented_b_iff_pred n q Hlen_q) as Hiff.
        apply Hiff in Hq_aug_b.
        pose proof (rotate_k_augmented n j q Hq_aug_b) as Hrot_aug.
        subst aug_list. apply filter_In. split.
        * apply all_paths_complete_len.
          rewrite rotate_k_length. exact Hlen_q.
        * apply is_augmented_b_iff_pred.
          -- rewrite rotate_k_length. exact Hlen_q.
          -- exact Hrot_aug.
      + (* p in aug_list -> p in rotation_list *)
        intros Hin. subst aug_list.
        apply filter_In in Hin.
        destruct Hin as [Hp_path Hp_aug_b].
        pose proof (all_paths_length _ _ Hp_path) as Hlen_p.
        pose proof (is_augmented_b_iff_pred n p Hlen_p) as Hiff.
        apply Hiff in Hp_aug_b.
        destruct (cycle_lemma_exists n p Hp_aug_b) as [j_star [Hjstar Hgood_star]].
        set (q := rotate_k j_star p).
        pose proof (rotate_k_augmented n j_star p Hp_aug_b) as Hq_aug.
        fold q in Hq_aug.
        (* Choose j: if j_star = 0 then 0 else m - j_star *)
        destruct (Nat.eq_dec j_star 0) as [Hjs0|Hjsn0].
        * (* j_star = 0: p is good, q = p, take j = 0 *)
          subst j_star. simpl in Hgood_star.
          subst rotation_list. apply in_map_iff.
          exists (p, 0). split.
          -- unfold phi. simpl. reflexivity.
          -- apply in_prod_iff. split.
             ++ subst good_list. apply filter_In. split.
                ** exact Hp_path.
                ** apply Bool.andb_true_iff. split.
                   --- apply is_augmented_b_iff_pred; auto.
                   --- apply is_good_b_iff. exact Hgood_star.
             ++ subst m_seq. apply in_seq. split; [lia | unfold m; lia].
        * (* j_star > 0: take j = m - j_star *)
          set (j := m - j_star).
          subst rotation_list. apply in_map_iff.
          exists (q, j). split.
          -- unfold phi. simpl.
             unfold q, j.
             pose proof (rotate_k_compose (m - j_star) j_star p) as Hcomp.
             replace (m - j_star + j_star) with m in Hcomp by (unfold m; lia).
             pose proof (rotate_k_full p) as Hfull.
             rewrite Hlen_p in Hfull. fold m in Hfull.
             rewrite Hcomp, Hfull. reflexivity.
          -- apply in_prod_iff. split.
             ++ subst good_list. apply filter_In. split.
                ** apply all_paths_complete_len. unfold q.
                   rewrite rotate_k_length. exact Hlen_p.
                ** apply Bool.andb_true_iff. split.
                   --- apply is_augmented_b_iff_pred.
                       +++ unfold q. rewrite rotate_k_length. exact Hlen_p.
                       +++ exact Hq_aug.
                   --- apply is_good_b_iff. unfold q. exact Hgood_star.
             ++ subst m_seq. apply in_seq.
                unfold j. split; [lia | unfold m; lia].
  }

  apply Permutation_length in Hperm.
  rewrite Hlen_rot in Hperm.
  rewrite Nat.mul_comm in Hperm.
  exact Hperm.
Qed.

(** This is the heart of the derivation. By the cycle lemma:
    - Each augmented sequence belongs to a unique cyclic orbit of size 2n+1
    - Each orbit contains exactly one good sequence
    - Good sequences are in bijection with Dyck paths (strip first U)

    Therefore:    (2n+1) * |Dyck_n| = |augmented_n| = C(2n+1, n).        *)
Theorem cycle_lemma_count : forall n,
  (2 * n + 1) * num_dyck n = binomial (2 * n + 1) n.
Proof.
  intros n.
  rewrite <- (num_good_eq_num_dyck n).
  rewrite (rotation_count_relation n).
  apply num_augmented_binomial.
Qed.

(* ========================================================================= *)
(*                  PART X: THE EXPLICIT FORMULA                            *)
(* ========================================================================= *)

(** Main theorem: the Catalan number equals C(2n,n)/(n+1).
    Equivalently: (n+1) * C_n = C(2n, n). *)
Theorem catalan_explicit_formula : forall n,
  (n + 1) * num_dyck n = binomial (2 * n) n.
Proof.
  intros n.
  pose proof (cycle_lemma_count n) as Hcyc.
  pose proof (cycle_to_catalan_identity n) as Halg.
  (* Hcyc: (2n+1) * num_dyck n = C(2n+1, n)                    *)
  (* Halg: (n+1) * C(2n+1, n) = (2n+1) * C(2n, n)              *)
  (* From these: (n+1) * (2n+1) * num_dyck n = (n+1) * C(2n+1, n) = (2n+1) * C(2n, n).
     Since 2n+1 > 0, we can cancel:  (n+1) * num_dyck n = C(2n, n).  *)
  assert (Hpos: 2 * n + 1 > 0) by lia.
  nia.
Qed.

(** Equivalent factorial form: n! * (n+1)! * C_n = (2n)!. *)
Theorem catalan_factorial_formula : forall n,
  fact n * fact (n + 1) * num_dyck n = fact (2 * n).
Proof.
  intros n.
  pose proof (catalan_explicit_formula n) as Hexpl.
  (* Hexpl: (n+1) * num_dyck n = C(2n, n) *)
  pose proof (binomial_fact (2 * n) n) as Hbf.
  assert (Hle: n <= 2 * n) by lia.
  specialize (Hbf Hle).
  (* Hbf: C(2n,n) * (fact n * fact (2n - n)) = fact (2n)
     i.e., C(2n,n) * (fact n * fact n) = fact (2n) *)
  replace (2 * n - n) with n in Hbf by lia.
  (* fact (n+1) = (n+1) * fact n *)
  assert (Hfn1: fact (n + 1) = (n + 1) * fact n).
  { replace (n + 1) with (S n) by lia. simpl. reflexivity. }
  rewrite Hfn1.
  (* Goal: fact n * ((n+1) * fact n) * num_dyck n = fact (2n)
     = (n+1) * num_dyck n * (fact n * fact n) = C(2n,n) * (fact n * fact n)
     = fact (2n)  by Hbf. *)
  nia.
Qed.

(* ========================================================================= *)
(*                  PART XI: ERR SYSTEM SUMMARY                             *)
(* ========================================================================= *)

(** A summary statement bundling the E/R/R structure with the derived
    formula. This makes explicit that the formula is a Product of the
    L2 system Dyck_n applied to L3 (counting / orbit analysis). *)

Record CatalanSystem (n : nat) : Type := mkCatalanSystem {
  cs_paths : list Path;                                     (* Elements   *)
  cs_paths_all_dyck : forall p, In p cs_paths -> is_dyck p; (* Rules      *)
  cs_paths_length : forall p, In p cs_paths -> length p = 2 * n; (* Role: position *)
  cs_count : nat;                                           (* counted    *)
  cs_count_eq : cs_count = length cs_paths;
  cs_formula : (n + 1) * cs_count = binomial (2 * n) n      (* Theorem    *)
}.

(** The build_catalan_system constructor would package the list of Dyck
    paths into the CatalanSystem record. Since it is purely cosmetic — the
    underlying formula is [catalan_explicit_formula] — and constructing it
    requires the boolean Dyck check correctness lemma (is_dyck_b -> is_dyck),
    we omit it. The record schema above documents the intended structure. *)

(* ========================================================================= *)
(*                  REMAINING ADMITTED (with proof sketches above)         *)
(*                                                                          *)
(*   1. cycle_lemma_exists       — argmin-of-prefix-sums construction       *)
(*   2. cycle_lemma_unique       — uniqueness from same construction        *)
(*   3. rotate_aperiodic         — gcd(n+1, n) = 1 forces full orbits       *)
(*   4. good_to_dyck             — height shift after stripping first U    *)
(*   5. dyck_to_good             — inverse direction                        *)
(*   6. num_augmented_binomial   — standard combinatorial count             *)
(*   7. cycle_lemma_count        — assembles 1-6 into the count equation    *)
(*   8. build_catalan_system     — wraps num_dyck into the record           *)
(*                                                                          *)
(* FULLY PROVED:                                                            *)
(*   - All rotation invariants (length, count_U, count_D, total_height)    *)
(*   - augmented_total_height                                                *)
(*   - rotate_k_augmented                                                    *)
(*   - good_augmented_starts_U                                               *)
(*   - binomial_fact, binomial_n_n, binomial_lt, binomial_n_0               *)
(*   - cycle_to_catalan_identity  (the KEY algebraic step)                 *)
(*   - catalan_explicit_formula   (modulo cycle_lemma_count)                *)
(*   - catalan_factorial_formula  (modulo catalan_explicit_formula)         *)
(* ========================================================================= *)
