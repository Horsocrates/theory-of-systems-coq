(** * ProcessFastWalshCost.v -- The fast Walsh butterfly on a list with a count of its additions and subtractions, as a ToS System

    Elements: a list of 2^k rationals; the natural number of additions and
              subtractions performed.
    Roles:    [zipw op a b] -- the pointwise operation on two lists;
              [fwht_c k l]  -- the butterfly on a list, returning the result
                               together with the number of additions and
                               subtractions it performed.
    Rules:    T(0) = 0, T(k+1) = 2 T(k) + 2^(k+1); hence T(k) = k * 2^k. The
              values are those of the matrix transform.

    Proved (no axioms):
      - [fwht_c_length]: the result has 2^k entries;
      - [fwht_c_ops]: on an input of length 2^k the count is exactly k * 2^k;
      - [fwht_c_correct]: the entries are those of [fwht];
      - [fwht_c_cost_and_value]: count k * 2^k, entries equal to the matrix
        transform [op_apply (had k)];
      - [fwht_c_8]: N = 8, 24 operations.

    P4 diagnostic: the count is a natural number computed together with the
      result -- an Element at every stage. Nothing asymptotic is stated.

    NOT claimed:
      - the class O(N log N) as an asymptotic statement, or optimality
        (lower bounds);
      - the cost of the list operations (firstn, skipn, append) or of
        rational arithmetic;
      - a comparison with the cost of the matrix transform.

    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa Bool List.
Import ListNotations.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.
From ToS Require Import process.ProcessSelfAdjointSpectral.
From ToS Require Import process.ProcessWalshHadamard.
From ToS Require Import process.ProcessFastWalsh.
From ToS Require Import process.ProcessWalshReconstruction.

Open Scope Q_scope.

(* ===================================================================== *)
(*  1. The butterfly on a list with a counter                           *)
(* ===================================================================== *)

Fixpoint zipw (op : Q -> Q -> Q) (a b : list Q) : list Q :=
  match a, b with
  | x :: a', y :: b' => op x y :: zipw op a' b'
  | _, _ => nil
  end.

(** The result and the number of additions and subtractions performed. *)
Fixpoint fwht_c (k : nat) (l : list Q) : list Q * nat :=
  match k with
  | O => (l, O)
  | S k' =>
      let ra := fwht_c k' (firstn (pow2 k') l) in
      let rb := fwht_c k' (skipn (pow2 k') l) in
      let s := zipw Qplus (fst ra) (fst rb) in
      let d := zipw Qminus (fst ra) (fst rb) in
      (s ++ d, (snd ra + snd rb + (length s + length d))%nat)
  end.

Lemma zipw_length : forall op (a b : list Q),
  length a = length b -> length (zipw op a b) = length a.
Proof.
  intros op a. induction a as [|x a IH]; intros [|y b] H; cbn in *;
    try reflexivity; try discriminate.
  f_equal. apply IH. lia.
Qed.

Lemma zipw_nth : forall op (a b : list Q) i,
  length a = length b -> (i < length a)%nat ->
  nth i (zipw op a b) 0 = op (nth i a 0) (nth i b 0).
Proof.
  intros op a. induction a as [|x a IH]; intros [|y b] i H Hi; cbn in *;
    try lia; try discriminate.
  destruct i as [|i]; [ reflexivity | apply IH; lia ].
Qed.

Lemma nth_firstn_lt : forall (l : list Q) n i,
  (i < n)%nat -> nth i (firstn n l) 0 = nth i l 0.
Proof.
  induction l as [|x l IH]; intros n i Hi.
  - rewrite firstn_nil. reflexivity.
  - destruct n as [|n]; [ lia | ]. cbn [firstn].
    destruct i as [|i]; cbn [nth]; [ reflexivity | apply IH; lia ].
Qed.

Lemma nth_skipn_add : forall (l : list Q) n i,
  nth i (skipn n l) 0 = nth (n + i) l 0.
Proof.
  induction l as [|x l IH]; intros n i.
  - rewrite skipn_nil. destruct i, n; reflexivity.
  - destruct n as [|n]; cbn [skipn Nat.add nth]; [ reflexivity | apply IH ].
Qed.

Lemma fwht_c_length : forall k l,
  length l = pow2 k -> length (fst (fwht_c k l)) = pow2 k.
Proof.
  induction k as [|k IH]; intros l Hl.
  - exact Hl.
  - cbn [fwht_c fst]. cbn [pow2] in Hl.
    assert (Ha : length (fst (fwht_c k (firstn (pow2 k) l))) = pow2 k)
      by (apply IH; rewrite length_firstn; lia).
    assert (Hb : length (fst (fwht_c k (skipn (pow2 k) l))) = pow2 k)
      by (apply IH; rewrite length_skipn; lia).
    rewrite length_app, !zipw_length by lia. cbn [pow2]. lia.
Qed.

(* ===================================================================== *)
(*  2. The count is k * 2^k                                             *)
(* ===================================================================== *)

Theorem fwht_c_ops : forall k l,
  length l = pow2 k -> snd (fwht_c k l) = (k * pow2 k)%nat.
Proof.
  induction k as [|k IH]; intros l Hl.
  - reflexivity.
  - cbn [fwht_c snd]. cbn [pow2] in Hl.
    assert (Hf : length (firstn (pow2 k) l) = pow2 k) by (rewrite length_firstn; lia).
    assert (Hs : length (skipn (pow2 k) l) = pow2 k) by (rewrite length_skipn; lia).
    rewrite (IH _ Hf), (IH _ Hs).
    pose proof (fwht_c_length k _ Hf) as Ha.
    pose proof (fwht_c_length k _ Hs) as Hb.
    rewrite !zipw_length by lia. rewrite Ha. cbn [pow2]. lia.
Qed.

(* ===================================================================== *)
(*  3. The values are those of the matrix transform                     *)
(* ===================================================================== *)

(** fwht depends only on the first 2^k values of its argument. *)
Lemma fwht_ext_bounded : forall k (f g : nat -> Q),
  (forall j, (j < pow2 k)%nat -> f j == g j) ->
  forall i, (i < pow2 k)%nat -> fwht k f i == fwht k g i.
Proof.
  intros k f g H i Hi.
  rewrite (fwht_correct k f i Hi), (fwht_correct k g i Hi).
  apply op_apply_ext_bounded. exact H.
Qed.

(** The butterfly on a list gives the values of fwht. *)
Theorem fwht_c_correct : forall k l, length l = pow2 k ->
  forall i, (i < pow2 k)%nat ->
  nth i (fst (fwht_c k l)) 0 == fwht k (fun j => nth j l 0) i.
Proof.
  induction k as [|k IH]; intros l Hl i Hi.
  - cbn [fwht_c fst fwht]. reflexivity.
  - cbn [pow2] in Hl, Hi.
    assert (Hf : length (firstn (pow2 k) l) = pow2 k) by (rewrite length_firstn; lia).
    assert (Hs : length (skipn (pow2 k) l) = pow2 k) by (rewrite length_skipn; lia).
    pose proof (fwht_c_length k _ Hf) as Ha.
    pose proof (fwht_c_length k _ Hs) as Hb.
    assert (HA : forall j, (j < pow2 k)%nat ->
              nth j (fst (fwht_c k (firstn (pow2 k) l))) 0
              == fwht k (fun j => nth j l 0) j).
    { intros j Hj. rewrite (IH _ Hf j Hj).
      apply fwht_ext_bounded; [ | exact Hj ]. intros m Hm.
      rewrite (nth_firstn_lt l (pow2 k) m Hm). reflexivity. }
    assert (HB : forall j, (j < pow2 k)%nat ->
              nth j (fst (fwht_c k (skipn (pow2 k) l))) 0
              == fwht k (fun j => nth (pow2 k + j) l 0) j).
    { intros j Hj. rewrite (IH _ Hs j Hj).
      apply fwht_ext_bounded; [ | exact Hj ]. intros m Hm.
      rewrite (nth_skipn_add l (pow2 k) m). reflexivity. }
    cbn [fwht_c fst fwht].
    destruct (Nat.leb (pow2 k) i) eqn:E.
    + apply Nat.leb_le in E.
      rewrite app_nth2 by (rewrite zipw_length; lia).
      rewrite zipw_length by lia. rewrite Ha.
      rewrite zipw_nth by lia.
      rewrite (HA (i - pow2 k)%nat ltac:(lia)), (HB (i - pow2 k)%nat ltac:(lia)).
      reflexivity.
    + apply Nat.leb_gt in E.
      rewrite app_nth1 by (rewrite zipw_length; lia).
      rewrite zipw_nth by lia.
      rewrite (HA i E), (HB i E). reflexivity.
Qed.

(** k * 2^k additions and subtractions; the result is the matrix transform. *)
Theorem fwht_c_cost_and_value : forall k l, length l = pow2 k ->
  snd (fwht_c k l) = (k * pow2 k)%nat
  /\ forall i, (i < pow2 k)%nat ->
       nth i (fst (fwht_c k l)) 0 == op_apply (had k) (fun j => nth j l 0) (pow2 k) i.
Proof.
  intros k l Hl. split.
  - exact (fwht_c_ops k l Hl).
  - intros i Hi. rewrite (fwht_c_correct k l Hl i Hi). exact (fwht_correct k _ i Hi).
Qed.

(** N = 8: 24 operations. *)
Example fwht_c_8 :
  fwht_c 3 [1; 2; 3; 4; 5; 6; 7; 8]
  = ([36; -4; -8; 0; -16; 0; 0; 0], 24%nat).
Proof. vm_compute. reflexivity. Qed.

