(* ========================================================================= *)
(*           UNIVERSE POLYMORPHISM: PARAMETRIC LEVELS                       *)
(*                                                                          *)
(*   Level arithmetic, depth analysis, and polymorphic predicates over      *)
(*   the ToS level hierarchy.                                               *)
(*                                                                          *)
(*   STATUS: 0 Admitted                                                     *)
(*   Author: Horsocrates | Date: March 2026                                 *)
(* ========================================================================= *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.

From ToS Require Import TheoryOfSystems_Core_ERR.

(* ========================================================================= *)
(*                   PART I: LEVEL ARITHMETIC                               *)
(* ========================================================================= *)

(** Level addition: shift a level upward by n steps *)
Fixpoint level_add (l : Level) (n : nat) : Level :=
  match n with
  | O => l
  | S n' => LS (level_add l n')
  end.

(** Lemma 1: Adding zero is identity *)
Lemma level_add_zero : forall l, level_add l 0 = l.
Proof.
  intros l. simpl. reflexivity.
Qed.

(** Lemma 2: Adding successor wraps with LS *)
Lemma level_add_succ : forall l n, level_add l (S n) = LS (level_add l n).
Proof.
  intros l n. simpl. reflexivity.
Qed.

(* ========================================================================= *)
(*                   PART II: DEPTH PROPERTIES                              *)
(* ========================================================================= *)

(** Lemma 3: Level depth is always positive *)
Lemma level_depth_positive : forall l, (level_depth l >= 1)%nat.
Proof.
  induction l; simpl; lia.
Qed.

(** Lemma 4: Depth of level_add *)
Lemma level_depth_add : forall l n,
  level_depth (level_add l n) = (level_depth l + n)%nat.
Proof.
  intros l n. induction n as [| n' IH].
  - simpl. lia.
  - simpl. rewrite IH. lia.
Qed.

(** Lemma 5: Depth is injective — levels with equal depth are equal *)
Lemma level_depth_injective : forall l1 l2,
  level_depth l1 = level_depth l2 -> l1 = l2.
Proof.
  induction l1 as [| l1' IH]; induction l2 as [| l2']; intros Heq.
  - reflexivity.
  - simpl in Heq. pose proof (level_depth_positive l2'). lia.
  - simpl in Heq. pose proof (level_depth_positive l1'). lia.
  - simpl in Heq. f_equal. apply IH. lia.
Qed.

(* ========================================================================= *)
(*                   PART III: LEVEL ORDERING PROPERTIES                    *)
(* ========================================================================= *)

(** Helper: l << LS l for any level *)
Lemma level_lt_LS : forall l, l << LS l.
Proof.
  intros l. simpl. left. reflexivity.
Qed.

(** Lemma 6: level_add with S n produces a strictly greater level *)
Lemma level_add_monotone : forall l n, l << level_add l (S n).
Proof.
  intros l n. induction n as [| n' IH].
  - simpl. left. reflexivity.
  - simpl. right. exact IH.
Qed.

(** Lemma 7: level_lt depth — already in Core_ERR, but we prove a corollary:
    if l1 << l2, then depth l1 + 1 <= depth l2 *)
Lemma level_lt_depth_gap : forall l1 l2,
  l1 << l2 -> (level_depth l1 + 1 <= level_depth l2)%nat.
Proof.
  intros l1 l2 H.
  apply level_lt_depth in H. lia.
Qed.

(* ========================================================================= *)
(*                   PART IV: DECIDABILITY                                  *)
(* ========================================================================= *)

(** Lemma 8: Equality on levels is decidable *)
Lemma level_eq_dec : forall (l1 l2 : Level), {l1 = l2} + {l1 <> l2}.
Proof.
  induction l1 as [| l1' IH]; destruct l2 as [| l2'].
  - left. reflexivity.
  - right. discriminate.
  - right. discriminate.
  - destruct (IH l2') as [Heq | Hneq].
    + left. f_equal. exact Heq.
    + right. intros H. apply Hneq. inversion H. reflexivity.
Qed.

(** Lemma 9: Strict ordering on levels is decidable *)
Lemma level_lt_dec : forall (l1 l2 : Level), {l1 << l2} + {~ l1 << l2}.
Proof.
  intros l1 l2. revert l1.
  induction l2 as [| l2' IH]; intros l1.
  - (* l2 = L1 : nothing is << L1 *)
    right. simpl. tauto.
  - (* l2 = LS l2' : l1 << LS l2' iff l1 = l2' \/ l1 << l2' *)
    simpl.
    destruct (level_eq_dec l1 l2') as [Heq | Hneq].
    + left. left. exact Heq.
    + destruct (IH l1) as [Hlt | Hnlt].
      * left. right. exact Hlt.
      * right. intros [H | H]; contradiction.
Qed.

(* ========================================================================= *)
(*                   PART V: LEVEL ADDITION ASSOCIATIVITY                   *)
(* ========================================================================= *)

(** Lemma 10: level_add is associative wrt nat addition *)
Lemma level_add_assoc : forall l m n,
  level_add (level_add l m) n = level_add l (m + n).
Proof.
  intros l m n. induction n as [| n' IH].
  - simpl. rewrite Nat.add_0_r. reflexivity.
  - simpl. rewrite IH. f_equal.
    rewrite Nat.add_succ_r. reflexivity.
Qed.

(* ========================================================================= *)
(*                   PART VI: NO LEVEL COLLAPSE                             *)
(* ========================================================================= *)

(** Lemma 11: LS is injective *)
Lemma LS_injective : forall l1 l2, LS l1 = LS l2 -> l1 = l2.
Proof.
  intros l1 l2 H. inversion H. reflexivity.
Qed.

(** Lemma 12: There is no function that uniformly maps LS L back to L
    for all L — i.e., LS has no left-inverse that is the identity on
    "predecessors". More precisely: LS is not surjective (L1 is not in range). *)
Lemma LS_not_surjective : ~ (forall l, exists l', LS l' = l).
Proof.
  intros H.
  destruct (H L1) as [l' Habs].
  discriminate.
Qed.

(* ========================================================================= *)
(*                   PART VII: POLYMORPHIC PREDICATES                       *)
(* ========================================================================= *)

(** Level-polymorphic universal quantification *)
Definition ForAllLevels (P : Level -> Prop) : Prop :=
  forall L, P L.

(** Lemma 13: ForAllLevels is closed under implication *)
Lemma forall_levels_impl : forall (P Q : Level -> Prop),
  ForAllLevels P ->
  (forall L, P L -> Q L) ->
  ForAllLevels Q.
Proof.
  intros P Q HP HPQ L.
  apply HPQ. apply HP.
Qed.

(** Lemma 14: ForAllLevels conjunction *)
Lemma forall_levels_conj : forall (P Q : Level -> Prop),
  ForAllLevels P ->
  ForAllLevels Q ->
  ForAllLevels (fun L => P L /\ Q L).
Proof.
  intros P Q HP HQ L.
  split; [apply HP | apply HQ].
Qed.

(** Lemma 15: If P holds for L1 and is preserved by LS, then ForAllLevels P
    (structural induction principle restated for ForAllLevels) *)
Lemma forall_levels_induction : forall (P : Level -> Prop),
  P L1 ->
  (forall l, P l -> P (LS l)) ->
  ForAllLevels P.
Proof.
  intros P Hbase Hstep L.
  induction L as [| L' IH].
  - exact Hbase.
  - apply Hstep. exact IH.
Qed.

(** Helper: LS preserves strict ordering *)
Lemma LS_preserves_lt : forall l1 l2,
  l1 << l2 -> LS l1 << LS l2.
Proof.
  intros l1 l2 H. revert l1 H.
  induction l2 as [| l2' IH]; intros l1 H.
  - simpl in H. contradiction.
  - simpl in H. destruct H as [Heq | Hlt].
    + subst. simpl. left. reflexivity.
    + simpl. right. apply IH. exact Hlt.
Qed.

(** Lemma 16: level_add preserves ordering *)
Lemma level_add_preserves_lt : forall l1 l2 n,
  l1 << l2 -> level_add l1 n << level_add l2 n.
Proof.
  intros l1 l2 n H. induction n as [| n' IH].
  - simpl. exact H.
  - simpl. apply LS_preserves_lt. exact IH.
Qed.

(** Lemma 17: L1 is the unique minimal element — nothing is below L1 *)
Lemma L1_minimal : forall l, ~ (l << L1).
Proof.
  intros l H. simpl in H. exact H.
Qed.

(** Lemma 18: Every level other than L1 has a predecessor *)
Lemma level_pred_exists : forall l, l <> L1 -> exists l', l = LS l'.
Proof.
  intros l Hneq.
  destruct l as [| l'].
  - exfalso. apply Hneq. reflexivity.
  - exists l'. reflexivity.
Qed.

(** Lemma 19: Antisymmetry — l1 << l2 and l2 << l1 is impossible *)
Lemma level_lt_antisym : forall l1 l2, l1 << l2 -> ~ (l2 << l1).
Proof.
  intros l1 l2 H12 H21.
  apply (level_lt_irrefl l1).
  exact (level_lt_trans l1 l2 l1 H12 H21).
Qed.

(** Helper: L1 is below any LS level *)
Lemma L1_lt_any_LS : forall l, L1 << LS l.
Proof.
  induction l as [| l' IH].
  - simpl. left. reflexivity.
  - simpl. right. exact IH.
Qed.

(** Helper: any LS level is above L1 *)
Lemma any_LS_gt_L1 : forall l, LS l << L1 -> False.
Proof.
  intros l H. simpl in H. exact H.
Qed.

(** Lemma 20: Trichotomy — for any two levels, exactly one of
    l1 << l2, l1 = l2, or l2 << l1 holds *)
Lemma level_trichotomy : forall l1 l2,
  l1 << l2 \/ l1 = l2 \/ l2 << l1.
Proof.
  induction l1 as [| l1' IH]; intros l2.
  - destruct l2 as [| l2'].
    + right. left. reflexivity.
    + left. apply L1_lt_any_LS.
  - destruct l2 as [| l2'].
    + right. right. apply L1_lt_any_LS.
    + destruct (IH l2') as [Hlt | [Heq | Hgt]].
      * left. apply LS_preserves_lt. exact Hlt.
      * right. left. f_equal. exact Heq.
      * right. right. apply LS_preserves_lt. exact Hgt.
Qed.
