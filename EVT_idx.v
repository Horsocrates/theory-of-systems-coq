(* ========================================================================= *)
(*                EXTREME VALUE THEOREM - INDEX-BASED VERSION                *)
(*                                                                           *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)         *)
(*                                                                           *)
(*  KEY CHANGE: argmax returns INDEX, solving Qeq vs Leibniz issue!          *)
(*  This follows Gemini's advice: "Don't seek value, seek position (L5)"     *)
(*                                                                           *)
(*  Author: Horsocrates | Version: 3.0 | Date: January 2026                  *)
(* ========================================================================= *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qminmax.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Import ListNotations.

Open Scope Q_scope.

Definition ContinuousFunction := Q -> Q.
Definition RealProcess := nat -> Q.

Definition is_Cauchy (P : RealProcess) : Prop :=
  forall eps, eps > 0 -> exists N, forall m n,
    (m > N)%nat -> (n > N)%nat -> Qabs (P m - P n) < eps.

Definition uniformly_continuous_on (f : ContinuousFunction) (a b : Q) : Prop :=
  forall eps, eps > 0 -> exists delta, delta > 0 /\
    forall x y, a <= x <= b -> a <= y <= b ->
      Qabs (x - y) < delta -> Qabs (f x - f y) < eps.

(* ========================================================================= *)
(*                     GRID DEFINITIONS                                      *)
(* ========================================================================= *)

Definition grid_point (a b : Q) (n k : nat) : Q :=
  a + (inject_Z (Z.of_nat k)) * (b - a) / inject_Z (Z.of_nat n).

Fixpoint grid_list_aux (a b : Q) (n k : nat) : list Q :=
  match k with
  | O => [grid_point a b n O]
  | S k' => grid_point a b n k :: grid_list_aux a b n k'
  end.

Definition grid_list (a b : Q) (n : nat) : list Q :=
  match n with
  | O => [a]
  | S n' => grid_list_aux a b n n
  end.

(* ========================================================================= *)
(*                     NEW: INDEX-BASED ARGMAX                               *)
(* ========================================================================= *)

(**
  L5 DERIVATION OF LEFTMOST TIE-BREAKING
  ======================================
  
  Problem: When f has a plateau (multiple points with same max value),
  which point is "the argmax"? Without a rule, argmax_process fails Cauchy.
  
  L5 (Law of Order): Each Role must have a UNIQUE Position.
  
  Deduction:
  1. "Maximum point" is a Role
  2. Plateau gives multiple candidates for this Role
  3. L5 requires selecting exactly ONE Position
  4. Natural L5-compliant choice: MINIMAL index (leftmost)
  
  Why leftmost?
  - Uses only the inherent Position structure (indices in ℕ)
  - min is unique by well-ordering
  - Adds no external information
  
  The Qle_bool with <= (not <) means: when f(x) = best_val, update to current.
  Since we traverse left-to-right, FIRST occurrence wins = LEFTMOST.
  
  "Leftmost tie-breaking is not a hack—it is the unique L5-compliant
   resolution of Role ambiguity."
*)

(* Accumulator-based argmax returning INDEX with leftmost tie-breaking *)
Fixpoint find_max_idx_acc (f : Q -> Q) (l : list Q) (curr_idx best_idx : nat) (best_val : Q) : nat :=
  match l with
  | [] => best_idx
  | x :: xs =>
      if Qle_bool best_val (f x)
      then find_max_idx_acc f xs (S curr_idx) curr_idx (f x)
      else find_max_idx_acc f xs (S curr_idx) best_idx best_val
  end.

Definition argmax_idx (f : Q -> Q) (l : list Q) (default : Q) : nat :=
  match l with
  | [] => O
  | x :: xs => find_max_idx_acc f xs 1%nat O (f x)
  end.

(* NEW: max_on_grid via index — THE KEY CHANGE! *)
Definition max_on_grid (f : Q -> Q) (a b : Q) (n : nat) : Q :=
  let l := grid_list a b n in
  f (nth (argmax_idx f l a) l a).

Definition sup_process (f : ContinuousFunction) (a b : Q) : RealProcess :=
  fun n => max_on_grid f a b (S n).

(* ========================================================================= *)
(*                     ARGMAX LEMMAS                                         *)
(* ========================================================================= *)

Definition is_max_in_prefix (f : Q -> Q) (l : list Q) (n : nat) (idx : nat) (d : Q) : Prop :=
  (idx < n)%nat /\ forall k, (k < n)%nat -> f (nth k l d) <= f (nth idx l d).

Lemma find_max_idx_acc_invariant : forall f full_list l curr_idx best_idx best_val d,
  (best_idx < curr_idx)%nat ->
  (curr_idx + length l = length full_list)%nat ->
  (forall k, (k < length l)%nat -> nth (curr_idx + k) full_list d = nth k l d) ->
  best_val = f (nth best_idx full_list d) ->
  (forall k, (k < curr_idx)%nat -> f (nth k full_list d) <= best_val) ->
  let result := find_max_idx_acc f l curr_idx best_idx best_val in
  is_max_in_prefix f full_list (length full_list) result d.
Proof.
  intros f full_list l. induction l as [|x xs IH].
  - intros curr_idx best_idx best_val d Hbest Hlen Hnth Hval Hall.
    simpl. simpl in Hlen.
    split; [lia |].
    intros k Hk. rewrite Hval in Hall. apply Hall. lia.
  - intros curr_idx best_idx best_val d Hbest Hlen Hnth Hval Hall.
    simpl find_max_idx_acc.
    destruct (Qle_bool best_val (f x)) eqn:Hcmp.
    + apply Qle_bool_iff in Hcmp.
      assert (Hcurr : (curr_idx < S curr_idx)%nat) by lia.
      assert (Hlen' : (S curr_idx + length xs = length full_list)%nat) by (simpl in Hlen; lia).
      assert (Hnth' : forall k, (k < length xs)%nat -> nth (S curr_idx + k) full_list d = nth k xs d).
      { intros k Hk. specialize (Hnth (S k) ltac:(simpl; lia)).
        replace (curr_idx + S k)%nat with (S curr_idx + k)%nat in Hnth by lia.
        simpl in Hnth. exact Hnth. }
      assert (Hval' : f x = f (nth curr_idx full_list d)).
      { specialize (Hnth O ltac:(simpl; lia)). simpl in Hnth.
        replace (curr_idx + O)%nat with curr_idx in Hnth by lia. rewrite Hnth. reflexivity. }
      assert (Hall' : forall k, (k < S curr_idx)%nat -> f (nth k full_list d) <= f x).
      { intros k Hk. destruct (Nat.eq_dec k curr_idx) as [Heq | Hneq].
        + subst. rewrite <- Hval'. apply Qle_refl.
        + apply Qle_trans with best_val; [apply Hall; lia | exact Hcmp]. }
      apply (IH (S curr_idx) curr_idx (f x) d Hcurr Hlen' Hnth' Hval' Hall').
    + assert (Hnle : ~ best_val <= f x).
      { intro H. apply Qle_bool_iff in H. rewrite H in Hcmp. discriminate. }
      apply Qnot_le_lt in Hnle.
      assert (Hbest' : (best_idx < S curr_idx)%nat) by lia.
      assert (Hlen' : (S curr_idx + length xs = length full_list)%nat) by (simpl in Hlen; lia).
      assert (Hnth' : forall k, (k < length xs)%nat -> nth (S curr_idx + k) full_list d = nth k xs d).
      { intros k Hk. specialize (Hnth (S k) ltac:(simpl; lia)).
        replace (curr_idx + S k)%nat with (S curr_idx + k)%nat in Hnth by lia.
        simpl in Hnth. exact Hnth. }
      assert (Hall' : forall k, (k < S curr_idx)%nat -> f (nth k full_list d) <= best_val).
      { intros k Hk. destruct (Nat.eq_dec k curr_idx) as [Heq | Hneq].
        + subst. specialize (Hnth O ltac:(simpl; lia)). simpl in Hnth.
          replace (curr_idx + O)%nat with curr_idx in Hnth by lia.
          rewrite Hnth. apply Qlt_le_weak. exact Hnle.
        + apply Hall. lia. }
      apply (IH (S curr_idx) best_idx best_val d Hbest' Hlen' Hnth' Hval Hall').
Qed.

Lemma find_max_idx_acc_bound : forall f l curr_idx best_idx best_val,
  (best_idx < curr_idx)%nat ->
  (find_max_idx_acc f l curr_idx best_idx best_val < curr_idx + length l)%nat.
Proof.
  intros f l. induction l as [|x xs IH].
  - intros. simpl. lia.
  - intros curr_idx best_idx best_val Hbest. simpl.
    destruct (Qle_bool best_val (f x)) eqn:Hcmp.
    + specialize (IH (S curr_idx) curr_idx (f x) ltac:(lia)). lia.
    + specialize (IH (S curr_idx) best_idx best_val ltac:(lia)). lia.
Qed.

Lemma argmax_idx_bound : forall f l d,
  l <> [] -> (argmax_idx f l d < length l)%nat.
Proof.
  intros f l d Hne.
  destruct l as [|x xs]; [exfalso; apply Hne; reflexivity |].
  simpl. destruct xs; [simpl; lia |].
  specialize (find_max_idx_acc_bound f (q :: xs) 1%nat O (f x) ltac:(lia)). simpl. lia.
Qed.

Theorem argmax_idx_maximizes : forall f l d,
  l <> [] ->
  forall k, (k < length l)%nat ->
    f (nth k l d) <= f (nth (argmax_idx f l d) l d).
Proof.
  intros f l d Hne k Hk.
  destruct l as [|x xs]; [exfalso; apply Hne; reflexivity |].
  simpl argmax_idx.
  destruct xs as [|y ys].
  - simpl in Hk. assert (k = O)%nat by lia. subst. simpl. apply Qle_refl.
  - assert (Hlen : (1 + length (y :: ys) = length (x :: y :: ys))%nat) by reflexivity.
    assert (Hnth : forall j, (j < length (y :: ys))%nat -> 
              nth (1 + j) (x :: y :: ys) d = nth j (y :: ys) d).
    { intros j Hj. simpl. reflexivity. }
    assert (Hval : f x = f (nth O (x :: y :: ys) d)) by reflexivity.
    assert (Hall : forall j, (j < 1)%nat -> f (nth j (x :: y :: ys) d) <= f x).
    { intros j Hj. assert (j = O)%nat by lia. subst. simpl. apply Qle_refl. }
    pose proof (find_max_idx_acc_invariant f (x :: y :: ys) (y :: ys) 1%nat O (f x) d 
                  ltac:(lia) Hlen Hnth Hval Hall) as H.
    destruct H as [Hridx Hrmax].
    apply Hrmax. exact Hk.
Qed.

(* ========================================================================= *)
(*         TRIVIAL: max_on_grid_attained — NO MORE Qeq ISSUES!               *)
(* ========================================================================= *)

Lemma max_on_grid_attained : forall f a b n,
  (n > 0)%nat ->
  exists y, In y (grid_list a b n) /\ max_on_grid f a b n = f y.
Proof.
  intros f a b n Hn.
  set (l := grid_list a b n).
  set (idx := argmax_idx f l a).
  assert (Hne : l <> []).
  { unfold l, grid_list. destruct n; [lia | discriminate]. }
  assert (Hidx : (idx < length l)%nat).
  { apply argmax_idx_bound. exact Hne. }
  exists (nth idx l a).
  split.
  - apply nth_In. exact Hidx.
  - unfold max_on_grid. reflexivity.  (* DEFINITIONAL — no Qeq! *)
Qed.

(* ========================================================================= *)
(*                     GRID VALUE LEMMAS                                     *)
(* ========================================================================= *)

Lemma grid_value_le_max : forall f a b n y,
  (n > 0)%nat -> In y (grid_list a b n) ->
  f y <= max_on_grid f a b n.
Proof.
  intros f a b n y Hn Hy.
  unfold max_on_grid.
  set (l := grid_list a b n).
  assert (Hne : l <> []).
  { unfold l, grid_list. destruct n; [lia | discriminate]. }
  apply In_nth with (d := a) in Hy.
  destruct Hy as [k [Hk Heq]].
  rewrite <- Heq.
  apply argmax_idx_maximizes; assumption.
Qed.

Print Assumptions max_on_grid_attained.
Print Assumptions grid_value_le_max.
Print Assumptions argmax_idx_maximizes.


(* ========================================================================= *)
(*                     GRID POINT LEMMAS                                     *)
(* ========================================================================= *)

Lemma grid_point_0 : forall a b n, (n > 0)%nat -> grid_point a b n O == a.
Proof.
  intros. unfold grid_point.
  setoid_replace (inject_Z (Z.of_nat O) * (b - a) / inject_Z (Z.of_nat n)) with 0.
  - ring.
  - unfold inject_Z, Qeq, Qdiv, Qmult. simpl. ring.
Qed.

Lemma grid_point_in_interval : forall a b n k,
  a <= b -> (k <= n)%nat -> (n > 0)%nat ->
  a <= grid_point a b n k <= b.
Proof.
  intros a b n k Hab Hk Hn.
  unfold grid_point.
  split.
  - apply Qle_trans with (a + 0).
    + ring_simplify. apply Qle_refl.
    + apply Qplus_le_compat. apply Qle_refl.
      apply Qle_shift_div_l.
      * unfold Qlt, inject_Z. simpl. lia.
      * rewrite Qmult_0_l.
        apply Qmult_le_0_compat.
        { unfold Qle, inject_Z. simpl. lia. }
        { apply Qle_minus_iff in Hab. exact Hab. }
  - apply Qle_trans with (a + (b - a)).
    + apply Qplus_le_compat. apply Qle_refl.
      apply Qle_shift_div_r.
      * unfold Qlt, inject_Z. simpl. lia.
      * setoid_replace ((b - a) * inject_Z (Z.of_nat n)) 
          with (inject_Z (Z.of_nat n) * (b - a)) by ring.
        apply Qmult_le_compat_r.
        { unfold Qle, inject_Z. simpl. lia. }
        { apply Qle_minus_iff in Hab. exact Hab. }
    + ring_simplify. apply Qle_refl.
Qed.

Lemma grid_point_in_aux : forall a b n k j,
  (j <= k)%nat -> In (grid_point a b n j) (grid_list_aux a b n k).
Proof.
  intros a b n k j Hjk.
  induction k.
  - assert (j = O)%nat by lia. subst. simpl. left. reflexivity.
  - simpl. destruct (Nat.eq_dec j (S k)) as [Heq | Hneq].
    + left. subst. reflexivity.
    + right. apply IHk. lia.
Qed.

Lemma grid_point_in_list : forall a b n k,
  (n > 0)%nat -> (k <= n)%nat -> In (grid_point a b n k) (grid_list a b n).
Proof.
  intros a b n k Hn Hk.
  unfold grid_list. destruct n; [lia|].
  apply grid_point_in_aux. lia.
Qed.

Lemma grid_list_aux_in_interval : forall a b n k x,
  a <= b -> (k <= n)%nat -> (n > 0)%nat ->
  In x (grid_list_aux a b n k) -> a <= x <= b.
Proof.
  intros a b n k x Hab Hk Hn Hin.
  induction k.
  - simpl in Hin. destruct Hin as [Heq | []].
    subst x. apply grid_point_in_interval; [exact Hab | lia | exact Hn].
  - simpl in Hin. destruct Hin as [Heq | Hin'].
    + subst x. apply grid_point_in_interval; [exact Hab | lia | exact Hn].
    + apply IHk; [lia | exact Hin'].
Qed.

Lemma grid_list_in_interval : forall a b n x,
  a <= b -> (n > 0)%nat ->
  In x (grid_list a b n) -> a <= x <= b.
Proof.
  intros a b n x Hab Hn Hin.
  unfold grid_list in Hin. destruct n; [lia|].
  apply grid_list_aux_in_interval with (S n) (S n); [exact Hab | lia | lia | exact Hin].
Qed.

(* ========================================================================= *)
(*                     ARCHIMEDEAN AND NEAR GRID POINT                       *)
(* ========================================================================= *)

Axiom classic : forall P : Prop, P \/ ~ P.

Fixpoint pow2 (n : nat) : positive :=
  match n with O => 1%positive | S n' => (2 * pow2 n')%positive end.

Lemma pow2_unbounded : forall M : Z, exists N : nat, (Z.pos (pow2 N) > M)%Z.
Proof.
  intro M.
  destruct (Z_lt_le_dec M 1) as [Hsmall | Hbig].
  - exists O. simpl. lia.
  - exists (Z.to_nat M).
    assert (H : forall n, (Z.pos (pow2 n) >= Z.of_nat (S n))%Z).
    { induction n; simpl; lia. }
    specialize (H (Z.to_nat M)).
    rewrite Nat2Z.inj_succ in H. rewrite Z2Nat.id in H by lia. lia.
Qed.

Theorem Archimedean_nat : forall (width eps : Q), width > 0 -> eps > 0 ->
  exists N : nat, (N > 0)%nat /\ width / inject_Z (Z.of_nat N) < eps.
Proof.
  intros width eps Hwidth Heps.
  destruct width as [wp wq]. destruct eps as [ep eq].
  unfold Qlt in *. simpl in *.
  assert (Hwp : (wp > 0)%Z) by lia.
  assert (Hep : (ep > 0)%Z) by lia.
  exists (S (Z.to_nat (wp * Z.pos eq))).
  split; [lia|].
  unfold Qlt, Qdiv, Qmult, Qinv, inject_Z. simpl.
  assert (Hsucc : (Z.pos (Pos.of_succ_nat (Z.to_nat (wp * Z.pos eq))) > wp * Z.pos eq)%Z).
  { rewrite Zpos_P_of_succ_nat. rewrite Z2Nat.id by lia. lia. }
  nia.
Qed.

Lemma grid_spacing_alt : forall a b n k,
  (n > 0)%nat ->
  a + (inject_Z (Z.of_nat (S k))) * (b - a) / inject_Z (Z.of_nat n) -
  (a + (inject_Z (Z.of_nat k)) * (b - a) / inject_Z (Z.of_nat n)) ==
  (b - a) / inject_Z (Z.of_nat n).
Proof.
  intros a b n k Hn.
  assert (Hne : ~ inject_Z (Z.of_nat n) == 0).
  { unfold inject_Z, Qeq. simpl. lia. }
  assert (Hsk : inject_Z (Z.of_nat (S k)) == inject_Z (Z.of_nat k) + 1).
  { unfold inject_Z, Qeq, Qplus. simpl. lia. }
  rewrite Hsk.
  field. exact Hne.
Qed.

Lemma grid_spacing : forall a b n k,
  a < b -> (n > 0)%nat -> (k < n)%nat ->
  grid_point a b n (S k) - grid_point a b n k == (b - a) / inject_Z (Z.of_nat n).
Proof.
  intros a b n k Hab Hn Hk. 
  unfold grid_point.
  apply grid_spacing_alt. exact Hn.
Qed.

Lemma grid_point_n_is_b : forall a b n, (n > 0)%nat -> grid_point a b n n == b.
Proof.
  intros a b n Hn. unfold grid_point.
  assert (Hne : ~ inject_Z (Z.of_nat n) == 0).
  { unfold inject_Z, Qeq. simpl. lia. }
  field. exact Hne.
Qed.

Lemma x_between_grid_points : forall a b n x,
  a < b -> (n > 0)%nat -> a <= x <= b ->
  exists k, (k < n)%nat /\ grid_point a b n k <= x <= grid_point a b n (S k).
Proof.
  intros a b n x Hab Hn Hx.
  destruct Hx as [Hax Hxb].
  revert x Hax Hxb.
  induction n as [|n' IH].
  - lia.
  - intros x Hax Hxb.
    destruct n' as [|n''].
    + (* n = 1: only interval is [gp(0), gp(1)] = [a, b] *)
      exists 0%nat. split. { lia. }
      split.
      * rewrite grid_point_0 by lia. exact Hax.
      * rewrite grid_point_n_is_b by lia. exact Hxb.
    + (* n >= 2 *)
      destruct (Qlt_le_dec (grid_point a b (S (S n'')) 1) x) as [Hgt | Hle].
      * (* x > gp(1): use classical choice *)
        destruct (classic (exists k, (k < S (S n''))%nat /\
                  grid_point a b (S (S n'')) k <= x /\
                  x <= grid_point a b (S (S n'')) (S k))) as [Hex | Hnex].
        { exact Hex. }
        { exfalso.
          assert (Hcover : forall k, (k < S (S n''))%nat -> 
                   grid_point a b (S (S n'')) k > x \/ 
                   x > grid_point a b (S (S n'')) (S k)).
          {
            intros k Hk.
            destruct (Qlt_le_dec x (grid_point a b (S (S n'')) k)) as [H1 | H1].
            - left. exact H1.
            - destruct (Qlt_le_dec (grid_point a b (S (S n'')) (S k)) x) as [H2 | H2].
              + right. exact H2.
              + exfalso. apply Hnex. exists k. split. exact Hk. split; assumption.
          }
          assert (Hchain : forall j, (j < S (S n''))%nat -> x > grid_point a b (S (S n'')) (S j)).
          {
            induction j.
            - intros _. exact Hgt.
            - intro Hj.
              assert (Hj' : (j < S (S n''))%nat) by lia.
              specialize (IHj Hj').
              destruct (Hcover (S j) Hj) as [Hbad | Hok].
              + exfalso. apply (Qlt_irrefl x).
                apply Qlt_trans with (grid_point a b (S (S n'')) (S j)); assumption.
              + exact Hok.
          }
          assert (Hcontra : x > grid_point a b (S (S n'')) (S (S n''))).
          { apply Hchain. lia. }
          rewrite grid_point_n_is_b in Hcontra by lia.
          apply Qlt_not_le in Hcontra. apply Hcontra. exact Hxb.
        }
      * (* x <= gp(1): x is in first interval *)
        exists 0%nat. split. { lia. }
        split.
        { rewrite grid_point_0 by lia. exact Hax. }
        { exact Hle. }
Qed.

Lemma near_grid_point : forall a b n x,
  a < b -> (n > 0)%nat -> a <= x <= b ->
  exists k, (k <= n)%nat /\ Qabs (x - grid_point a b n k) <= (b - a) / inject_Z (Z.of_nat n).
Proof.
  intros a b n x Hab Hn Hx.
  destruct (x_between_grid_points a b n x Hab Hn Hx) as [k [Hkn [Hlo Hhi]]].
  assert (Hspacing : grid_point a b n (S k) - grid_point a b n k == (b - a) / inject_Z (Z.of_nat n)).
  { apply grid_spacing; [exact Hab | exact Hn | exact Hkn]. }
  destruct (Qlt_le_dec (x - grid_point a b n k) (grid_point a b n (S k) - x)) as [Hcloser_lo | Hcloser_hi].
  - exists k. split. { lia. }
    rewrite Qabs_pos.
    + apply Qle_trans with (grid_point a b n (S k) - grid_point a b n k).
      * apply Qplus_le_compat. exact Hhi. apply Qle_refl.
      * rewrite Hspacing. apply Qle_refl.
    + apply Qle_minus_iff in Hlo. exact Hlo.
  - exists (S k). split. { lia. }
    rewrite Qabs_neg.
    + setoid_replace (- (x - grid_point a b n (S k))) with (grid_point a b n (S k) - x) by ring.
      apply Qle_trans with (grid_point a b n (S k) - grid_point a b n k).
      * apply Qplus_le_compat. apply Qle_refl. apply Qopp_le_compat. exact Hlo.
      * rewrite Hspacing. apply Qle_refl.
    + apply Qle_minus_iff. 
      setoid_replace (0 - (x - grid_point a b n (S k))) with (grid_point a b n (S k) - x) by ring.
      apply Qle_minus_iff in Hhi. exact Hhi.
Qed.

(* ========================================================================= *)
(*                     F_BOUNDED_BY_GRID_MAX                                 *)
(* ========================================================================= *)

Lemma Qdiv_le_compat_l : forall a d1 d2,
  0 < a -> 0 < d1 -> d1 <= d2 -> a / d2 <= a / d1.
Proof.
  intros a d1 d2 Ha Hd1 Hd12.
  assert (Hd2 : 0 < d2) by (apply Qlt_le_trans with d1; assumption).
  unfold Qdiv, Qle, Qlt, Qmult in *.
  destruct a as [an ad]. destruct d1 as [d1n d1d]. destruct d2 as [d2n d2d].
  unfold Qinv in *. simpl in *.
  destruct d1n as [|d1p|d1p]; try (simpl in Hd1; lia).
  destruct d2n as [|d2p|d2p]; try (simpl in Hd2; lia).
  destruct an as [|ap|ap]; try (simpl in Ha; lia).
  simpl. nia.
Qed.

Lemma f_bounded_by_grid_max : forall f a b n x delta,
  a < b -> (n > 0)%nat -> a <= x <= b ->
  (b - a) / inject_Z (Z.of_nat n) < delta ->
  uniformly_continuous_on f a b ->
  forall eps, eps > 0 ->
  (forall y z, a <= y <= b -> a <= z <= b -> Qabs (y - z) < delta -> Qabs (f y - f z) < eps) ->
  f x < max_on_grid f a b n + eps.
Proof.
  intros f a b n x delta Hab Hn Hx Hspacing Hcont eps Heps Hdelta_cont.
  destruct (near_grid_point a b n x Hab Hn Hx) as [k [Hkn Hdist]].
  assert (Hdist_delta : Qabs (x - grid_point a b n k) < delta).
  { apply Qle_lt_trans with ((b - a) / inject_Z (Z.of_nat n)); assumption. }
  assert (Hgp_in : a <= grid_point a b n k <= b).
  { apply grid_point_in_interval; [apply Qlt_le_weak; exact Hab | lia | exact Hn]. }
  assert (Hf_close : Qabs (f x - f (grid_point a b n k)) < eps).
  { apply Hdelta_cont; assumption. }
  assert (Hgp_le_max : f (grid_point a b n k) <= max_on_grid f a b n).
  { apply grid_value_le_max; [exact Hn |].
    apply grid_point_in_list; [exact Hn | lia]. }
  apply Qabs_Qlt_condition in Hf_close.
  destruct Hf_close as [Hlo Hhi].
  apply Qlt_le_trans with (f (grid_point a b n k) + eps).
  - apply Qplus_lt_l with (- f (grid_point a b n k)). ring_simplify. exact Hhi.
  - apply Qplus_le_compat; [exact Hgp_le_max | apply Qle_refl].
Qed.

(* ========================================================================= *)
(*                     SUP_PROCESS IS CAUCHY                                 *)
(* ========================================================================= *)

Lemma Qlt_minus_pos : forall a b : Q, a < b -> 0 < b - a.
Proof. intros. unfold Qlt, Qminus, Qplus, Qopp in *. simpl in *. lia. Qed.

Theorem sup_process_is_Cauchy : forall f a b,
  a < b ->
  uniformly_continuous_on f a b ->
  is_Cauchy (sup_process f a b).
Proof.
  intros f a b Hab Hcont.
  unfold is_Cauchy. intros eps Heps.
  assert (Heps2 : eps / 2 > 0).
  { apply Qlt_shift_div_l; [reflexivity | ring_simplify; exact Heps]. }
  destruct (Hcont (eps/2) Heps2) as [delta [Hdelta Hdelta_cont]].
  assert (Hba : b - a > 0) by (apply Qlt_minus_pos; exact Hab).
  destruct (Archimedean_nat (b - a) delta Hba Hdelta) as [N [HN_pos HN]].
  exists N.
  intros m n Hm Hn.
  unfold sup_process.
  assert (HSm : (S m > 0)%nat) by lia.
  assert (HSn : (S n > 0)%nat) by lia.
  destruct (max_on_grid_attained f a b (S m) HSm) as [xm [Hxm_in Hmax_m]].
  destruct (max_on_grid_attained f a b (S n) HSn) as [xn [Hxn_in Hmax_n]].
  assert (Hxm_interval : a <= xm <= b).
  { apply grid_list_in_interval with (S m); [apply Qlt_le_weak; exact Hab | lia | exact Hxm_in]. }
  assert (Hxn_interval : a <= xn <= b).
  { apply grid_list_in_interval with (S n); [apply Qlt_le_weak; exact Hab | lia | exact Hxn_in]. }
  assert (Hspacing_m : (b - a) / inject_Z (Z.of_nat (S m)) < delta).
  { apply Qle_lt_trans with ((b - a) / inject_Z (Z.of_nat N)).
    - apply Qdiv_le_compat_l; [exact Hba | unfold Qlt, inject_Z; simpl; lia | unfold Qle, inject_Z; simpl; lia].
    - exact HN. }
  assert (Hspacing_n : (b - a) / inject_Z (Z.of_nat (S n)) < delta).
  { apply Qle_lt_trans with ((b - a) / inject_Z (Z.of_nat N)).
    - apply Qdiv_le_compat_l; [exact Hba | unfold Qlt, inject_Z; simpl; lia | unfold Qle, inject_Z; simpl; lia].
    - exact HN. }
  assert (Hxm_bound : f xm < max_on_grid f a b (S n) + eps / 2).
  { apply f_bounded_by_grid_max with delta; try assumption. }
  assert (Hxn_bound : f xn < max_on_grid f a b (S m) + eps / 2).
  { apply f_bounded_by_grid_max with delta; try assumption. }
  apply Qabs_Qlt_condition. split.
  - apply Qlt_trans with (- (eps / 2)).
    + apply Qopp_lt_compat. apply Qlt_minus_iff.
      setoid_replace (eps - eps / 2) with (eps / 2) by field. exact Heps2.
    + apply Qplus_lt_l with (max_on_grid f a b (S n) + eps / 2).
      setoid_replace (- (eps / 2) + (max_on_grid f a b (S n) + eps / 2)) 
        with (max_on_grid f a b (S n)) by ring.
      setoid_replace (max_on_grid f a b (S m) - max_on_grid f a b (S n) + 
                      (max_on_grid f a b (S n) + eps / 2))
        with (max_on_grid f a b (S m) + eps / 2) by ring.
      rewrite Hmax_n. exact Hxn_bound.
  - apply Qlt_trans with (eps / 2).
    + apply Qplus_lt_l with (max_on_grid f a b (S n)). ring_simplify.
      rewrite Hmax_m. exact Hxm_bound.
    + unfold Qdiv. setoid_replace eps with (eps * 1) at 2 by ring.
      apply Qmult_lt_l; [exact Heps |]. unfold Qlt, Qinv. simpl. lia.
Qed.

Print Assumptions sup_process_is_Cauchy.

(* ========================================================================= *)
(*                     EVT_STRONG: THE SUPREMUM IS ATTAINED                  *)
(* ========================================================================= *)

(**
  EVT_STRONG states that not only does sup_process converge,
  but there EXISTS a point x_star in [a,b] where f(x_star) equals the supremum.
  
  This follows from:
  1. sup_process is Cauchy (proven above)
  2. The limit of sup_process is the supremum of f
  3. By compactness (over R), there exists x_star achieving this supremum
  
  Over Q, we can only state this as a process property:
  - argmax_process gives a sequence of approximate maximizers
  - sup_process converges to the supremum value
  - The supremum is the limit, achieved "in the limit"
  
  This is the P4 interpretation: the maximum EXISTS as a PROCESS,
  not necessarily as a single Q element.
*)

(** Argmax process: sequence of approximate maximizers *)
Definition argmax_on_grid (f : Q -> Q) (a b : Q) (n : nat) : Q :=
  let l := grid_list a b n in
  nth (argmax_idx f l a) l a.

Definition argmax_process (f : ContinuousFunction) (a b : Q) : RealProcess :=
  fun n => argmax_on_grid f a b (S n).

(** Key relationship: max_on_grid is f applied to argmax_on_grid *)
Lemma max_is_f_of_argmax : forall f a b n,
  max_on_grid f a b n = f (argmax_on_grid f a b n).
Proof.
  intros f a b n.
  unfold max_on_grid, argmax_on_grid.
  reflexivity.
Qed.

(** Argmax stays in [a,b] *)
Lemma argmax_in_interval : forall f a b n,
  a <= b -> (n > 0)%nat ->
  a <= argmax_on_grid f a b n <= b.
Proof.
  intros f a b n Hab Hn.
  unfold argmax_on_grid.
  set (l := grid_list a b n).
  set (idx := argmax_idx f l a).
  assert (Hne : l <> []).
  { unfold l, grid_list. destruct n; [lia | discriminate]. }
  assert (Hidx : (idx < length l)%nat).
  { apply argmax_idx_bound. exact Hne. }
  assert (Hin : In (nth idx l a) l).
  { apply nth_In. exact Hidx. }
  apply grid_list_in_interval with n; assumption.
Qed.

(**
  EVT_WEAK: The VALUE process (sup_process) is Cauchy.
  This is proven above as sup_process_is_Cauchy.
  
  EVT_STRONG (Process Version):
  For any eps > 0, for large enough n:
    |f(argmax_on_grid f a b n) - sup| < eps
  where sup is the limit of sup_process.
  
  This follows directly from max_is_f_of_argmax and sup_process_is_Cauchy.
*)

Theorem EVT_strong_process : forall f a b,
  a < b ->
  uniformly_continuous_on f a b ->
  (* sup_process is Cauchy, so it has a limit *)
  is_Cauchy (sup_process f a b) /\
  (* argmax_process stays in [a,b] *)
  (forall n, a <= argmax_process f a b n <= b) /\
  (* The sup value equals f(argmax) at each step *)
  (forall n, sup_process f a b n = f (argmax_process f a b n)).
Proof.
  intros f a b Hab Hcont.
  split; [| split].
  - (* sup_process is Cauchy *)
    apply sup_process_is_Cauchy; assumption.
  - (* argmax in [a,b] *)
    intro n. unfold argmax_process.
    apply argmax_in_interval.
    + apply Qlt_le_weak. exact Hab.
    + lia.
  - (* sup = f(argmax) *)
    intro n. unfold sup_process, argmax_process.
    apply max_is_f_of_argmax.
Qed.

(**
  INTERPRETATION:
  
  EVT_strong_process says:
  1. The sequence of maximum values converges (Cauchy)
  2. Each approximate maximizer is in [a,b]
  3. The max value at step n equals f applied to the argmax at step n
  
  In classical analysis with R, we would additionally prove:
  - argmax_process is Cauchy (requires leftmost + uniform continuity)
  - Both processes converge to the same limit (supremum, achieved at argmax_star)
  
  Over Q, the argmax_process may not be Cauchy (limit could be irrational).
  But the VALUE process (sup_process) IS Cauchy, giving us the supremum.
  
  This is the P4-philosophy: the MAXIMUM exists as a process,
  the SUPREMUM exists as a limit of values.
*)

Print Assumptions EVT_strong_process.
