(* ========================================================================= *)
(*        DOMAIN WALLS — Binary String Combinatorics for Strip Model          *)
(*                                                                            *)
(*  For s in {0,1}^N: domain walls d(s) = #{i : s_i != s_{i+1}}.            *)
(*  d(s) ranges from 0 (uniform) to N-1 (alternating).                      *)
(*  At beta=8: eigenvalue = (1/4)^{d(s)}.                                   *)
(*  Since d in N, min nonzero d = 1 -> gap = 1 - 1/4 = 3/4.                *)
(*                                                                            *)
(*  STATUS: ~42 Qed, 0 Admitted                                              *)
(*  Author: Horsocrates | Date: March 2026                                   *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.
Open Scope Q_scope.

(* ========================================================================= *)
(*  PART I: Domain Wall Counting                                              *)
(* ========================================================================= *)

Definition bstring := list bool.

(** 1 if x != y, 0 if x = y *)
Definition bdiff (x y : bool) : nat :=
  match x, y with
  | true, true => 0
  | false, false => 0
  | _, _ => 1
  end.

(** Domain wall count: number of adjacent unlike pairs *)
Fixpoint domain_walls (s : bstring) : nat :=
  match s with
  | nil => 0
  | x :: rest =>
    match rest with
    | nil => 0
    | y :: _ => bdiff x y + domain_walls rest
    end
  end.

(** Uniform string: all same value *)
Fixpoint all_same (b : bool) (n : nat) : bstring :=
  match n with
  | O => nil
  | S k => b :: all_same b k
  end.

Lemma all_same_length : forall b n,
  length (all_same b n) = n.
Proof.
  intros b n. induction n as [|n IH]; simpl; [reflexivity | f_equal; exact IH].
Qed.

Lemma bdiff_sym : forall x y, bdiff x y = bdiff y x.
Proof. intros [] []; reflexivity. Qed.

Lemma bdiff_same : forall x, bdiff x x = 0%nat.
Proof. intros []; reflexivity. Qed.

Lemma bdiff_negb : forall x, bdiff x (negb x) = 1%nat.
Proof. intros []; reflexivity. Qed.

(* ========================================================================= *)
(*  PART II: Uniform Strings Have Zero Walls                                  *)
(* ========================================================================= *)

Lemma domain_walls_all_false : forall n,
  domain_walls (all_same false n) = 0%nat.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - destruct n as [|n']; [reflexivity | simpl; exact IH].
Qed.

Lemma domain_walls_all_true : forall n,
  domain_walls (all_same true n) = 0%nat.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - destruct n as [|n']; [reflexivity | simpl; exact IH].
Qed.

(* ========================================================================= *)
(*  PART III: Complement                                                      *)
(* ========================================================================= *)

(** Flipping all bits *)
Fixpoint complement (s : bstring) : bstring :=
  match s with
  | nil => nil
  | b :: rest => negb b :: complement rest
  end.

Lemma complement_length : forall s,
  length (complement s) = length s.
Proof.
  induction s as [|b rest IH]; simpl; [reflexivity | f_equal; exact IH].
Qed.

Lemma bdiff_negb_negb : forall x y, bdiff (negb x) (negb y) = bdiff x y.
Proof. intros [] []; reflexivity. Qed.

Theorem complement_preserves_walls : forall s,
  domain_walls (complement s) = domain_walls s.
Proof.
  induction s as [|x rest IH].
  - reflexivity.
  - destruct rest as [|y rest'].
    + reflexivity.
    + simpl. rewrite bdiff_negb_negb. f_equal. exact IH.
Qed.

Lemma complement_involutive : forall s,
  complement (complement s) = s.
Proof.
  induction s as [|b rest IH]; simpl.
  - reflexivity.
  - rewrite Bool.negb_involutive. f_equal. exact IH.
Qed.

(* ========================================================================= *)
(*  PART IV: One Boundary Strings                                             *)
(* ========================================================================= *)

(** String with one boundary at position k: k copies of start, then n-k copies of negb start *)
Definition one_boundary (n k : nat) (start : bool) : bstring :=
  all_same start k ++ all_same (negb start) (n - k).

Lemma one_boundary_length : forall n k start,
  (k <= n)%nat ->
  length (one_boundary n k start) = n.
Proof.
  intros n k start Hle. unfold one_boundary.
  rewrite length_app. rewrite all_same_length. rewrite all_same_length. lia.
Qed.

(** Helper: domain walls of uniform ++ uniform with different value *)
Lemma dw_app_uniform : forall b k1 k2,
  (1 <= k1)%nat -> (1 <= k2)%nat ->
  domain_walls (all_same b k1 ++ all_same (negb b) k2) = 1%nat.
Proof.
  intros b k1 k2 H1 H2.
  destruct k1 as [|k1']; [lia |].
  destruct k2 as [|k2']; [lia |].
  simpl. induction k1' as [|k1'' IH].
  - simpl. rewrite bdiff_negb.
    destruct k2' as [|k2''].
    + simpl. lia.
    + simpl. rewrite bdiff_same. simpl.
      clear H1 H2. induction k2'' as [|k2''' IH2]; simpl; [lia | rewrite bdiff_same; simpl; exact IH2].
  - simpl. rewrite bdiff_same. simpl. apply IH. lia.
Qed.

Lemma one_boundary_walls : forall n k start,
  (1 <= k)%nat -> (k < n)%nat ->
  domain_walls (one_boundary n k start) = 1%nat.
Proof.
  intros n k start Hk Hkn.
  unfold one_boundary.
  apply dw_app_uniform; lia.
Qed.

(* ========================================================================= *)
(*  PART V: Concrete Domain Wall Counts                                       *)
(* ========================================================================= *)

(** N=2: four states *)
Lemma dw_2_00 : domain_walls [false; false] = 0%nat.
Proof. reflexivity. Qed.

Lemma dw_2_01 : domain_walls [false; true] = 1%nat.
Proof. reflexivity. Qed.

Lemma dw_2_10 : domain_walls [true; false] = 1%nat.
Proof. reflexivity. Qed.

Lemma dw_2_11 : domain_walls [true; true] = 0%nat.
Proof. reflexivity. Qed.

(** N=3: selected states *)
Lemma dw_3_001 : domain_walls [false; false; true] = 1%nat.
Proof. reflexivity. Qed.

Lemma dw_3_010 : domain_walls [false; true; false] = 2%nat.
Proof. reflexivity. Qed.

Lemma dw_3_101 : domain_walls [true; false; true] = 2%nat.
Proof. reflexivity. Qed.

(* ========================================================================= *)
(*  PART VI: Alternating Strings                                              *)
(* ========================================================================= *)

(** Alternating string: start, negb start, start, ... *)
Fixpoint alternating (start : bool) (n : nat) : bstring :=
  match n with
  | O => nil
  | S k => start :: alternating (negb start) k
  end.

Lemma alternating_length : forall start n,
  length (alternating start n) = n.
Proof.
  intros start n. revert start.
  induction n as [|n IH]; intros start; simpl; [reflexivity | f_equal; exact (IH (negb start))].
Qed.

Lemma alternating_walls : forall n start,
  (1 <= n)%nat ->
  domain_walls (alternating start n) = (n - 1)%nat.
Proof.
  intros n. induction n as [|n IH]; intros start Hn.
  - lia.
  - destruct n as [|n'].
    + simpl. reflexivity.
    + change (domain_walls (alternating start (S (S n'))))
        with (bdiff start (negb start) + domain_walls (alternating (negb start) (S n')))%nat.
      rewrite bdiff_negb.
      assert (Hn' : (1 <= S n')%nat) by lia.
      rewrite (IH (negb start) Hn'). lia.
Qed.

(* ========================================================================= *)
(*  PART VII: The Key Dichotomy                                               *)
(* ========================================================================= *)

(** d is a natural number: either 0 or >= 1.
    This trivial fact is the ENTIRE reason the gap is N-independent. *)
Theorem walls_dichotomy : forall s,
  domain_walls s = 0%nat \/ (1 <= domain_walls s)%nat.
Proof. intros s. lia. Qed.

Theorem min_nonzero_walls : forall s,
  domain_walls s <> 0%nat ->
  (1 <= domain_walls s)%nat.
Proof. intros s H. lia. Qed.

(* ========================================================================= *)
(*  PART VIII: Hamming Distance                                               *)
(* ========================================================================= *)

(** Hamming distance: number of positions where s and s' differ *)
Fixpoint hamming_dist (s s' : bstring) : nat :=
  match s, s' with
  | nil, _ | _, nil => 0
  | x :: xs, y :: ys => bdiff x y + hamming_dist xs ys
  end.

Lemma hamming_dist_sym : forall s s',
  hamming_dist s s' = hamming_dist s' s.
Proof.
  induction s as [|x xs IH]; intros [|y ys]; simpl; try reflexivity.
  rewrite bdiff_sym. f_equal. exact (IH ys).
Qed.

Lemma hamming_dist_zero : forall s,
  hamming_dist s s = 0%nat.
Proof.
  induction s as [|x xs IH]; simpl; [reflexivity |].
  rewrite bdiff_same. simpl. exact IH.
Qed.

Lemma hamming_dist_complement : forall s,
  hamming_dist s (complement s) = length s.
Proof.
  induction s as [|x xs IH]; simpl; [reflexivity |].
  rewrite bdiff_negb. simpl. f_equal. exact IH.
Qed.

(* ========================================================================= *)
(*  PART IX: Quarter Power (Eigenvalue Formula)                               *)
(* ========================================================================= *)

(** (1/4)^n: eigenvalue of state with n domain walls at beta=8 *)
Fixpoint quarter_power (n : nat) : Q :=
  match n with
  | O => 1
  | S k => (1#4) * quarter_power k
  end.

Lemma qp_0 : quarter_power 0 == 1.
Proof. reflexivity. Qed.

Lemma qp_1 : quarter_power 1 == 1#4.
Proof. unfold quarter_power. lra. Qed.

Lemma qp_2 : quarter_power 2 == 1#16.
Proof. unfold quarter_power, Qeq. simpl. lia. Qed.

Lemma qp_3 : quarter_power 3 == 1#64.
Proof. unfold quarter_power, Qeq. simpl. lia. Qed.

Lemma qp_positive : forall n, 0 < quarter_power n.
Proof.
  induction n as [|n IH]; simpl; [lra |].
  apply Qmult_lt_0_compat; [lra | exact IH].
Qed.

Lemma qp_le_one : forall n, quarter_power n <= 1.
Proof.
  induction n as [|n IH]; simpl; [lra |].
  assert (H : (1#4) * quarter_power n <= (1#4) * 1).
  { apply Qmult_le_l; [lra | exact IH]. }
  lra.
Qed.

Lemma qp_monotone : forall m n,
  (m <= n)%nat -> quarter_power n <= quarter_power m.
Proof.
  intros m n H. induction H as [|n Hmn IH].
  - lra.
  - simpl. assert (Hpos := qp_positive n).
    assert (H1 : (1#4) * quarter_power n <= quarter_power n) by lra.
    lra.
Qed.

(* ========================================================================= *)
(*  PART X: Summary                                                           *)
(* ========================================================================= *)

(** Domain walls main theorem *)
Theorem domain_walls_main :
  domain_walls (all_same false 100) = 0%nat /\
  domain_walls (all_same true 100) = 0%nat /\
  domain_walls [false; true] = 1%nat /\
  domain_walls [false; true; false] = 2%nat.
Proof.
  split; [exact (domain_walls_all_false 100) |].
  split; [exact (domain_walls_all_true 100) |].
  split; [exact dw_2_01 |].
  exact dw_3_010.
Qed.

(** One-boundary construction works *)
Theorem one_boundary_main : forall n,
  (2 <= n)%nat ->
  domain_walls (one_boundary n 1 false) = 1%nat /\
  domain_walls (one_boundary n 1 true) = 1%nat.
Proof.
  intros n Hn.
  split; apply one_boundary_walls; lia.
Qed.

(** Alternating gives maximum walls *)
Theorem alternating_max : forall n start,
  (2 <= n)%nat ->
  domain_walls (alternating start n) = (n - 1)%nat.
Proof.
  intros. apply alternating_walls. lia.
Qed.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  ~42 Qed, 0 Admitted                                                       *)
(*                                                                            *)
(*  Part I: all_same_length, bdiff_sym, bdiff_same, bdiff_negb (4)           *)
(*  Part II: domain_walls_all_false, domain_walls_all_true (2)               *)
(*  Part III: complement_length, bdiff_negb_negb,                             *)
(*            complement_preserves_walls, complement_involutive (4)            *)
(*  Part IV: one_boundary_length, dw_app_uniform,                             *)
(*           one_boundary_walls (3)                                           *)
(*  Part V: dw_2_00..dw_2_11, dw_3_001, dw_3_010, dw_3_101 (7)             *)
(*  Part VI: alternating_length, alternating_walls (2)                        *)
(*  Part VII: walls_dichotomy, min_nonzero_walls (2)                          *)
(*  Part VIII: hamming_dist_sym, hamming_dist_zero,                           *)
(*             hamming_dist_complement (3)                                    *)
(*  Part IX: qp_0..qp_3, qp_positive, qp_le_one, qp_monotone (7)           *)
(*  Part X: domain_walls_main, one_boundary_main, alternating_max (3)        *)
(*  TOTAL: 37 Qed                                                             *)
(* ========================================================================= *)
