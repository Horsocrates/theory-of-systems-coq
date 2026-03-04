(* ========================================================================= *)
(*           SOFTMAX PROBABILITY SOUNDNESS                                   *)
(*                                                                           *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)         *)
(*                                                                           *)
(*  PURPOSE: Bridge between interval bounds on neural network outputs        *)
(*  and probability statements. Shows that if outputs satisfy                *)
(*  v_i in [lo_i, hi_i] with all values positive, then the normalized        *)
(*  probability P(class=i) = v_i / Sum v_j is soundly bounded:              *)
(*                                                                           *)
(*    lo_i / Sum hi_j  <=  P(class=i)  <=  hi_i / Sum lo_j                  *)
(*                                                                           *)
(*  Cross-multiplication form (division-free):                               *)
(*    lo_i * Sum v_j  <=  v_i * Sum hi_j    (lower bound)                   *)
(*    v_i * Sum lo_j  <=  hi_i * Sum v_j    (upper bound)                   *)
(*                                                                           *)
(*  This directly corresponds to PInterval_Softmax.v in the RegulusAI       *)
(*  repository, providing the formal foundation for interval-based           *)
(*  neural network uncertainty quantification.                               *)
(*                                                                           *)
(*  STATUS: 14 Qed, 0 Admitted (100%)                                       *)
(*                                                                           *)
(*  AXIOMS: NONE - fully constructive over Q                                 *)
(*                                                                           *)
(*  Author: Horsocrates | Date: March 2026                                   *)
(* ========================================================================= *)

Require Import Coq.QArith.QArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Import ListNotations.

Open Scope Q_scope.

(* ========================================================================= *)
(* SECTION 1: LIST SUMS                                                       *)
(* ========================================================================= *)

(** Sum of a list of rationals *)
Fixpoint Qsum (l : list Q) : Q :=
  match l with
  | [] => 0
  | x :: rest => x + Qsum rest
  end.

Lemma Qsum_app : forall l1 l2,
  Qsum (l1 ++ l2) == Qsum l1 + Qsum l2.
Proof.
  intros l1. induction l1 as [| x r IH].
  - intro l2. simpl. ring.
  - intro l2. simpl. rewrite IH. ring.
Qed.

Lemma Qsum_nonneg : forall l,
  Forall (fun x => 0 <= x) l -> 0 <= Qsum l.
Proof.
  intros l H. induction l as [| x r IH].
  - simpl. lra.
  - inversion H; subst. simpl.
    assert (Hr : 0 <= Qsum r) by (apply IH; assumption).
    cbv beta in *. lra.
Qed.

(** Strictly positive implies non-negative (for Forall) *)
Lemma pos_implies_nonneg : forall l,
  Forall (fun x => 0 < x) l -> Forall (fun x => 0 <= x) l.
Proof.
  induction l as [| x r IH]; intro H.
  - constructor.
  - inversion H; subst. constructor.
    + cbv beta in *. lra.
    + apply IH. assumption.
Qed.

Lemma Qsum_positive : forall l,
  l <> [] -> Forall (fun x => 0 < x) l -> 0 < Qsum l.
Proof.
  intros l Hne Hpos.
  destruct l as [| x r].
  - contradiction.
  - inversion Hpos; subst. simpl.
    assert (Hx : 0 < x) by (cbv beta in *; assumption).
    assert (Hr : 0 <= Qsum r).
    { apply Qsum_nonneg. apply pos_implies_nonneg. assumption. }
    lra.
Qed.

(* ========================================================================= *)
(* SECTION 2: POINTWISE ORDERING OF LISTS                                     *)
(* ========================================================================= *)

(** Pointwise <= on lists of equal length *)
Fixpoint list_le (l1 l2 : list Q) : Prop :=
  match l1, l2 with
  | [], [] => True
  | x :: r1, y :: r2 => x <= y /\ list_le r1 r2
  | _, _ => False
  end.

Lemma list_le_length : forall l1 l2,
  list_le l1 l2 -> length l1 = length l2.
Proof.
  intros l1. induction l1 as [| x r1 IH].
  - intros [| y r2] H; [reflexivity | contradiction].
  - intros [| y r2] H; [contradiction |].
    destruct H as [_ Hr]. simpl. f_equal. apply IH. exact Hr.
Qed.

Lemma list_le_nth : forall l1 l2 i d,
  list_le l1 l2 -> (i < length l1)%nat ->
  nth i l1 d <= nth i l2 d.
Proof.
  intros l1. induction l1 as [| x r1 IH].
  - intros. simpl in *. lia.
  - intros [| y r2] i d H Hi; [contradiction |].
    destruct H as [Hxy Hr].
    destruct i as [| i'].
    + simpl. exact Hxy.
    + simpl. apply IH. exact Hr. simpl in Hi. lia.
Qed.

(** If lo is all-positive and lo <= vals, then vals is all-nonneg *)
Lemma list_le_nonneg : forall lo vals,
  list_le lo vals ->
  Forall (fun x => 0 < x) lo ->
  Forall (fun x => 0 <= x) vals.
Proof.
  intros lo. induction lo as [| l r IH].
  - intros [| v s] H _; [constructor | contradiction].
  - intros [| v s] H Hpos; [contradiction |].
    destruct H as [Hlv Hr].
    inversion Hpos; subst.
    constructor.
    + cbv beta in *. lra.
    + apply IH; assumption.
Qed.

(** Helper: Forall P on nth element *)
Lemma Forall_nth_default : forall (P : Q -> Prop) l i d,
  Forall P l -> (i < length l)%nat -> P (nth i l d).
Proof.
  intros P l. induction l as [| x r IH].
  - intros. simpl in *. lia.
  - intros [| i'] d Hfa Hi.
    + inversion Hfa; subst. simpl. assumption.
    + inversion Hfa; subst. simpl. apply IH; [assumption | simpl in Hi; lia].
Qed.

Lemma Qsum_le : forall l1 l2,
  list_le l1 l2 -> Qsum l1 <= Qsum l2.
Proof.
  intros l1. induction l1 as [| x r1 IH].
  - intros [| y r2] H; [simpl; lra | contradiction].
  - intros [| y r2] H; [contradiction |].
    destruct H as [Hxy Hr]. simpl.
    assert (Hrec : Qsum r1 <= Qsum r2) by (apply IH; exact Hr).
    lra.
Qed.

(* ========================================================================= *)
(* SECTION 3: CROSS-MULTIPLICATION BOUNDS                                     *)
(*                                                                           *)
(*  The core technique: instead of dividing (which requires nonzero          *)
(*  denominator and loses precision), we cross-multiply.                     *)
(*                                                                           *)
(*  To prove lo_i / Sum(hi) <= v_i / Sum(v), it suffices to show            *)
(*  lo_i * Sum(v) <= v_i * Sum(hi) (both denominators positive).            *)
(*                                                                           *)
(*  Two-step monotonicity:                                                   *)
(*    lo_i * Sum(v) <= v_i * Sum(v) <= v_i * Sum(hi)                        *)
(*  (first: lo_i <= v_i, multiply by nonneg Sum(v))                         *)
(*  (second: Sum(v) <= Sum(hi), multiply by nonneg v_i)                     *)
(* ========================================================================= *)

(** Left-multiplication preserves <= *)
Lemma Qmult_le_l : forall z x y,
  0 <= z -> x <= y -> z * x <= z * y.
Proof.
  intros z x y Hz Hxy.
  assert (H : x * z <= y * z) by (apply Qmult_le_compat_r; assumption).
  assert (Hzx : z * x == x * z) by ring.
  assert (Hzy : z * y == y * z) by ring.
  lra.
Qed.

(** Lower bound: lo_i * Sum(v) <= v_i * Sum(hi) *)
Lemma cross_mul_lower : forall lo vals hi i,
  list_le lo vals ->
  list_le vals hi ->
  Forall (fun x => 0 < x) lo ->
  (i < length vals)%nat ->
  nth i lo 0 * Qsum vals <= nth i vals 0 * Qsum hi.
Proof.
  intros lo vals hi i Hlo_v Hv_hi Hpos Hi.
  (* Pointwise bound: lo_i <= v_i *)
  assert (Hlen_lo : length lo = length vals) by (apply list_le_length; exact Hlo_v).
  assert (Hle_i : nth i lo 0 <= nth i vals 0).
  { apply list_le_nth; [exact Hlo_v | lia]. }
  (* Sum(v) >= 0 *)
  assert (Hsum_v_nn : 0 <= Qsum vals).
  { apply Qsum_nonneg. eapply list_le_nonneg; eassumption. }
  (* v_i >= 0 *)
  assert (Hvi_nn : 0 <= nth i vals 0).
  { apply Forall_nth_default with (i := i) (d := 0).
    - eapply list_le_nonneg; eassumption.
    - exact Hi. }
  (* Sum(v) <= Sum(hi) *)
  assert (Hsum_le : Qsum vals <= Qsum hi).
  { apply Qsum_le; assumption. }
  (* Step 1: lo_i * Sum(v) <= v_i * Sum(v) *)
  assert (H1 : nth i lo 0 * Qsum vals <= nth i vals 0 * Qsum vals).
  { apply Qmult_le_compat_r; assumption. }
  (* Step 2: v_i * Sum(v) <= v_i * Sum(hi) *)
  assert (H2 : nth i vals 0 * Qsum vals <= nth i vals 0 * Qsum hi).
  { apply Qmult_le_l; assumption. }
  (* Combine *)
  lra.
Qed.

(** Upper bound: v_i * Sum(lo) <= hi_i * Sum(v) *)
Lemma cross_mul_upper : forall lo vals hi i,
  list_le lo vals ->
  list_le vals hi ->
  Forall (fun x => 0 < x) lo ->
  (i < length vals)%nat ->
  nth i vals 0 * Qsum lo <= nth i hi 0 * Qsum vals.
Proof.
  intros lo vals hi i Hlo_v Hv_hi Hpos Hi.
  (* Pointwise bound: v_i <= hi_i *)
  assert (Hle_i : nth i vals 0 <= nth i hi 0).
  { apply list_le_nth.
    - exact Hv_hi.
    - exact Hi. }
  (* Sum(lo) >= 0 *)
  assert (Hsum_lo_nn : 0 <= Qsum lo).
  { apply Qsum_nonneg.
    apply pos_implies_nonneg. exact Hpos. }
  (* hi_i >= 0 (lo positive, lo <= vals <= hi, so hi >= lo > 0) *)
  assert (Hhi_nn : 0 <= nth i hi 0).
  { assert (Hvals_nn : Forall (fun x => 0 <= x) vals).
    { eapply list_le_nonneg; eassumption. }
    assert (Hhi_nn_all : Forall (fun x => 0 <= x) hi).
    { assert (Hlen : length vals = length hi).
      { apply list_le_length; assumption. }
      clear - Hv_hi Hvals_nn.
      revert hi Hv_hi.
      induction vals as [| v s IH].
      - intros [| h t] H; [constructor | contradiction].
      - intros [| h t] H; [contradiction |].
        destruct H as [Hvh Hr].
        inversion Hvals_nn; subst.
        constructor.
        + cbv beta in *. lra.
        + apply IH; assumption. }
    apply Forall_nth_default with (i := i) (d := 0); [exact Hhi_nn_all |].
    assert (Hlen2 : length vals = length hi) by (apply list_le_length; assumption).
    lia. }
  (* Sum(lo) <= Sum(v) *)
  assert (Hsum_le : Qsum lo <= Qsum vals).
  { apply Qsum_le; assumption. }
  (* Step 1: v_i * Sum(lo) <= hi_i * Sum(lo) *)
  assert (H1 : nth i vals 0 * Qsum lo <= nth i hi 0 * Qsum lo).
  { apply Qmult_le_compat_r; assumption. }
  (* Step 2: hi_i * Sum(lo) <= hi_i * Sum(v) *)
  assert (H2 : nth i hi 0 * Qsum lo <= nth i hi 0 * Qsum vals).
  { apply Qmult_le_l; assumption. }
  (* Combine *)
  lra.
Qed.

(* ========================================================================= *)
(* SECTION 4: MAIN SOUNDNESS THEOREM                                          *)
(*                                                                           *)
(*  If outputs v_i lie in [lo_i, hi_i] and all lo values are positive,       *)
(*  then the normalized probability p_i = v_i / Sum(v) satisfies:            *)
(*                                                                           *)
(*    lo_i * Sum(v) <= v_i * Sum(hi)    (i.e., lo_i/Sum(hi) <= p_i)         *)
(*    v_i * Sum(lo) <= hi_i * Sum(v)    (i.e., p_i <= hi_i/Sum(lo))         *)
(*                                                                           *)
(*  This is the key result for interval-based neural network verification:  *)
(*  IBP bounds on logit values → sound probability bounds.                   *)
(* ========================================================================= *)

Theorem softmax_probability_sound : forall lo vals hi i,
  list_le lo vals ->
  list_le vals hi ->
  Forall (fun x => 0 < x) lo ->
  (i < length vals)%nat ->
  nth i lo 0 * Qsum vals <= nth i vals 0 * Qsum hi /\
  nth i vals 0 * Qsum lo <= nth i hi 0 * Qsum vals.
Proof.
  intros lo vals hi i Hlo_v Hv_hi Hpos Hi.
  split.
  - exact (cross_mul_lower lo vals hi i Hlo_v Hv_hi Hpos Hi).
  - exact (cross_mul_upper lo vals hi i Hlo_v Hv_hi Hpos Hi).
Qed.

(** The probability interval [lo_i/Sum(hi), hi_i/Sum(lo)] is non-degenerate:
    lo_i * Sum(lo) <= hi_i * Sum(hi), so lo_i/Sum(hi) <= hi_i/Sum(lo). *)
Lemma probability_bounds_consistent : forall lo hi i,
  list_le lo hi ->
  Forall (fun x => 0 < x) lo ->
  (i < length lo)%nat ->
  nth i lo 0 * Qsum lo <= nth i hi 0 * Qsum hi.
Proof.
  intros lo hi i Hle Hpos Hi.
  (* lo_i <= hi_i *)
  assert (Hle_i : nth i lo 0 <= nth i hi 0).
  { apply list_le_nth; assumption. }
  (* Sum(lo) >= 0 *)
  assert (Hsum_nn : 0 <= Qsum lo).
  { apply Qsum_nonneg.
    apply pos_implies_nonneg. exact Hpos. }
  (* hi_i >= 0 *)
  assert (Hhi_nn : 0 <= nth i hi 0).
  { assert (Hlo_i : 0 < nth i lo 0).
    { apply Forall_nth_default with (i := i) (d := 0); assumption. }
    lra. }
  (* Sum(lo) <= Sum(hi) *)
  assert (Hsum_le : Qsum lo <= Qsum hi).
  { apply Qsum_le; assumption. }
  (* Step 1: lo_i * Sum(lo) <= hi_i * Sum(lo) *)
  assert (H1 : nth i lo 0 * Qsum lo <= nth i hi 0 * Qsum lo).
  { apply Qmult_le_compat_r; assumption. }
  (* Step 2: hi_i * Sum(lo) <= hi_i * Sum(hi) *)
  assert (H2 : nth i hi 0 * Qsum lo <= nth i hi 0 * Qsum hi).
  { apply Qmult_le_l; assumption. }
  (* Combine *)
  lra.
Qed.

(* ========================================================================= *)
(* SECTION 5: VERIFICATION                                                    *)
(* ========================================================================= *)

Check Qsum_app.
Check Qsum_nonneg.
Check Qsum_positive.
Check list_le_length.
Check list_le_nth.
Check list_le_nonneg.
Check Forall_nth_default.
Check Qsum_le.
Check Qmult_le_l.
Check cross_mul_lower.
Check cross_mul_upper.
Check softmax_probability_sound.
Check probability_bounds_consistent.

Print Assumptions softmax_probability_sound.
Print Assumptions probability_bounds_consistent.
Print Assumptions cross_mul_lower.
