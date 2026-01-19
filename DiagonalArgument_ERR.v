(* ========================================================================= *)
(*                                                                           *)
(*                 CANTOR'S DIAGONAL ARGUMENT - INTEGRATED VERSION           *)
(*              Combining Structural Foundation with Q-Arithmetic            *)
(*                                                                           *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)         *)
(*                                                                           *)
(*  Author:  Horsocrates                                                     *)
(*  Version: 5.0 (E/R/R Integration)                                         *)
(*  Date:    January 2026                                                    *)
(*                                                                           *)
(*  STATUS: 41 Qed, 1 Admitted (97.6%)                                       *)
(*                                                                           *)
(* ========================================================================= *)
(*                                                                           *)
(*  E/R/R INTERPRETATION:                                                    *)
(*  =====================                                                    *)
(*                                                                           *)
(*  This file operates at L3 (Enumeration level):                            *)
(*                                                                           *)
(*    Elements(L3) = Enumeration = nat -> TernaryProcess                     *)
(*    Roles(L3)    = enum_equiv (equivalence of enumerations)                *)
(*    Rules(L3)    = diagonal construction (flip digit at position n)        *)
(*                                                                           *)
(*  Products(L3) = Diagonal D (differs from all E(n))                        *)
(*                                                                           *)
(*  ACTUALIZATION (P4):                                                      *)
(*    The diagonal is constructed by PROCESS:                                *)
(*    - At each step n, flip the n-th digit of E(n)                          *)
(*    - Constitution: ternary_flip ensures {0,2} (no boundary digit 1)       *)
(*    - Product: A CauchyProcess not in the range of E                       *)
(*                                                                           *)
(* ========================================================================= *)
(*                                                                           *)
(*  KEY INSIGHT: TWO-LEVEL ARCHITECTURE                                      *)
(*  ------------------------------------                                     *)
(*  Level Z: Digits {0, 2} - structural, discrete, fully provable            *)
(*  Level Q: Approximations - continuous, requires bounds                    *)
(*                                                                           *)
(*  The diagonal_differs_structurally theorem is PROVED at Z-level.          *)
(*  We then "lift" this to Q-level via approximation bounds.                 *)
(*                                                                           *)
(*  PHILOSOPHY (Theory of Systems):                                          *)
(*  - Distinction (digit choice) is PRIMARY (L1: A/~A)                       *)
(*  - Numbers emerge from sequences of distinctions (P4: process)            *)
(*  - Avoiding digit 1 = avoiding boundary = clean binary choice (L4)        *)
(*  - flip(0) = 2, flip(2) = 0 embodies the primordial A/~A distinction      *)
(*                                                                           *)
(* ========================================================================= *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.

Set Implicit Arguments.
Open Scope Q_scope.

(* ========================================================================= *)
(*                     PART I: FOUNDATIONS                                   *)
(* ========================================================================= *)

(* ========================================================================= *)
(*                     SECTION 1: POWERS OF 3                                *)
(* ========================================================================= *)

Fixpoint pow3 (n : nat) : positive :=
  match n with
  | O => 1%positive
  | S n' => (3 * pow3 n')%positive
  end.

Definition Qpow3 (n : nat) : Q := Z.pos (pow3 n) # 1.

Lemma Qpow3_pos : forall n, 0 < Qpow3 n.
Proof. intro n. unfold Qpow3, Qlt. simpl. lia. Qed.

Lemma Qpow3_nonzero : forall n, ~ Qpow3 n == 0.
Proof.
  intro n. intro H.
  pose proof (Qpow3_pos n) as Hpos.
  rewrite H in Hpos. apply Qlt_irrefl in Hpos. exact Hpos.
Qed.

Lemma Qpow3_S : forall n, Qpow3 (S n) == 3 * Qpow3 n.
Proof.
  intro n. unfold Qpow3. simpl.
  unfold Qeq, Qmult. simpl. ring.
Qed.

Lemma Qinv_pow3_pos : forall n, 0 < / Qpow3 n.
Proof. intro n. apply Qinv_lt_0_compat. apply Qpow3_pos. Qed.

Lemma pow3_mono_strict : forall m n, (m < n)%nat -> (pow3 m < pow3 n)%positive.
Proof.
  intros m n Hmn. induction Hmn.
  - simpl. lia.
  - simpl. lia.
Qed.

Lemma inv_pow3_mono : forall m n, (m <= n)%nat -> / Qpow3 n <= / Qpow3 m.
Proof.
  intros m n Hmn.
  destruct (Nat.eq_dec m n) as [Heq | Hneq].
  - subst. apply Qle_refl.
  - assert (Hlt : (m < n)%nat) by lia.
    apply Qlt_le_weak.
    apply Qinv_lt_contravar.
    + exact (Qpow3_pos m).
    + exact (Qpow3_pos n).
    + unfold Qpow3, Qlt. simpl.
      assert (H: (pow3 m < pow3 n)%positive).
      { apply pow3_mono_strict. exact Hlt. }
      lia.
Qed.

(* Key: 1/3^{n+1} = (1/3) * 1/3^n *)
Lemma inv_pow3_step : forall n,
  / Qpow3 (S n) == (1 # 3) * / Qpow3 n.
Proof.
  intro n.
  rewrite Qpow3_S.
  field.
  apply Qpow3_nonzero.
Qed.

(* 3/3^{n+1} = 1/3^n *)
Lemma three_over_pow3_S : forall n,
  3 * / Qpow3 (S n) == / Qpow3 n.
Proof.
  intro n.
  rewrite Qpow3_S.
  field.
  apply Qpow3_nonzero.
Qed.

(* Helper lemma: p - q <= 0 iff p <= q *)
Lemma Qminus_le_0 : forall p q, p - q <= 0 <-> p <= q.
Proof.
  intros p q.
  unfold Qle, Qminus, Qplus, Qopp. simpl.
  destruct p as [pn pd], q as [qn qd]. simpl.
  split; intro H; nia.
Qed.

(* Helper lemma: 0 <= q - p iff p <= q *)
Lemma Qle_0_minus : forall p q, 0 <= q - p <-> p <= q.
Proof.
  intros p q.
  unfold Qle, Qminus, Qplus, Qopp. simpl.
  destruct p as [pn pd], q as [qn qd]. simpl.
  split; intro H; nia.
Qed.

(* ========================================================================= *)
(*                     SECTION 2: TERNARY DIGITS (Z-LEVEL)                   *)
(* ========================================================================= *)

(*
   A TernaryExp is a sequence of digits, each either 0 or 2.
   This is the PRIMARY object - numbers are DERIVED from it.
*)

Record TernaryExp := mkTernary {
  digit : nat -> Z;
  digit_valid : forall k, digit k = 0%Z \/ digit k = 2%Z
}.

Lemma digit_bounds : forall (T : TernaryExp) k,
  (0 <= digit T k <= 2)%Z.
Proof.
  intros T k.
  destruct (digit_valid T k) as [H | H]; rewrite H; lia.
Qed.

Lemma digit_nonneg : forall (T : TernaryExp) k,
  (0 <= digit T k)%Z.
Proof.
  intros T k. pose proof (digit_bounds T k). lia.
Qed.

(* ========================================================================= *)
(*                     SECTION 3: PARTIAL SUMS (Q-LEVEL)                     *)
(* ========================================================================= *)

(*
   Partial sum: Sum_{k=0}^{n-1} digit(k) / 3^{k+1}
   This converts digit sequence to Q approximation.
*)

Fixpoint partial_sum (T : TernaryExp) (n : nat) : Q :=
  match n with
  | O => 0
  | S n' => partial_sum T n' + (digit T n' # pow3 (S n'))
  end.

Definition to_Q (T : TernaryExp) (n : nat) : Q := partial_sum T n.

Lemma partial_sum_0 : forall T, partial_sum T 0 == 0.
Proof. intro T. reflexivity. Qed.

Lemma partial_sum_S : forall T n,
  partial_sum T (S n) == partial_sum T n + (digit T n # pow3 (S n)).
Proof. intros T n. reflexivity. Qed.

(* Partial sum is non-negative *)
Lemma partial_sum_nonneg : forall T n, 0 <= partial_sum T n.
Proof.
  intros T n. induction n.
  - simpl. apply Qle_refl.
  - simpl.
    apply Qle_trans with (partial_sum T n + 0).
    + rewrite Qplus_0_r. exact IHn.
    + apply Qplus_le_r.
      unfold Qle. simpl.
      pose proof (digit_nonneg T n). lia.
Qed.

(* Each term is bounded by 2/3^{k+1} *)
Lemma term_bound : forall T k,
  (digit T k # pow3 (S k)) <= 2 # pow3 (S k).
Proof.
  intros T k.
  unfold Qle. simpl.
  pose proof (digit_bounds T k) as [H1 H2].
  nia.
Qed.

(* Partial sums are monotonically increasing *)
Lemma partial_sum_mono : forall T m n,
  (m <= n)%nat -> partial_sum T m <= partial_sum T n.
Proof.
  intros T m n Hmn.
  induction Hmn.
  - apply Qle_refl.
  - simpl.
    apply Qle_trans with (partial_sum T m0).
    + exact IHHmn.
    + setoid_replace (partial_sum T m0) with (partial_sum T m0 + 0) at 1 by ring.
      apply Qplus_le_r. unfold Qle. simpl.
      pose proof (digit_nonneg T m0). lia.
Qed.

(* ========================================================================= *)
(*                     SECTION 4: GEOMETRIC SERIES BOUNDS                    *)
(* ========================================================================= *)

(*
   KEY BOUND: partial_sum T n <= 1 - 1/3^n
   
   Proof by induction:
   - Base: partial_sum T 0 = 0 <= 1 - 1 = 0 
   - Step: ps(n) + d_n/3^{n+1} <= (1 - 1/3^n) + 2/3^{n+1}
                                = 1 - 1/3^n + 2/3^{n+1}
                                = 1 - 3/3^{n+1} + 2/3^{n+1}
                                = 1 - 1/3^{n+1} 
*)

Lemma partial_sum_bound : forall T n,
  partial_sum T n <= 1 - / Qpow3 n.
Proof.
  intros T.
  induction n.
  - (* Base case: ps(0) = 0 <= 1 - 1 = 0 *)
    simpl. unfold Qpow3. simpl.
    unfold Qle, Qminus, Qinv. simpl. lia.
  - (* Inductive step *)
    simpl partial_sum.
    (* ps(n) + d_n/3^{n+1} <= (1 - 1/3^n) + 2/3^{n+1} *)
    apply Qle_trans with ((1 - / Qpow3 n) + (2 # pow3 (S n))).
    + apply Qplus_le_compat.
      * exact IHn.
      * apply term_bound.
    + (* Need: 1 - 1/3^n + 2/3^{n+1} <= 1 - 1/3^{n+1} *)
      (* Use: 1/3^n = 3/3^{n+1} *)
      (* So: 1 - 3/3^{n+1} + 2/3^{n+1} = 1 - 1/3^{n+1} *)
      assert (Heq : / Qpow3 n == 3 * / Qpow3 (S n)).
      { symmetry. apply three_over_pow3_S. }
      assert (Hterm : (2 # pow3 (S n)) == 2 * / Qpow3 (S n)).
      { unfold Qpow3, Qinv, Qmult, Qeq. simpl. ring. }
      setoid_rewrite Heq.
      setoid_rewrite Hterm.
      unfold Qminus.
      ring_simplify.
      apply Qle_refl.
Qed.

(* Corollary: partial_sum is in [0, 1] *)
Lemma partial_sum_in_unit : forall T n,
  0 <= partial_sum T n <= 1.
Proof.
  intros T n. split.
  - apply partial_sum_nonneg.
  - apply Qle_trans with (1 - / Qpow3 n).
    + apply partial_sum_bound.
    + unfold Qminus.
      setoid_replace 1 with (1 + 0) at 2 by ring.
      apply Qplus_le_r.
      setoid_replace 0 with (- 0) by ring.
      apply Qopp_le_compat.
      apply Qlt_le_weak. apply Qinv_pow3_pos.
Qed.

(* Tail bound: difference of partial sums *)
(* 
   This is the geometric series bound:
   ps(n) - ps(m) = Sum_{k=m}^{n-1} d_k/3^{k+1} 
                 <= Sum_{k=m}^{n-1} 2/3^{k+1} 
                 = 2/3^{m+1} * (1 - (1/3)^{n-m}) / (1 - 1/3)
                 = 1/3^m * (1 - 1/3^{n-m}) 
                 <= 1/3^m
*)

(* Stronger version: exact bound *)
Lemma tail_bound_exact : forall T m n,
  (m <= n)%nat ->
  partial_sum T n - partial_sum T m <= / Qpow3 m - / Qpow3 n.
Proof.
  intros T m n Hmn.
  induction Hmn.
  - (* Base case: n = m *)
    unfold Qminus. ring_simplify. apply Qle_refl.
  - (* Inductive step: m <= m0 -> m <= S m0 *)
    simpl partial_sum.
    (* Goal: ps(m0) + d_{m0}/3^{m0+1} - ps(m) <= 1/3^m - 1/3^{S m0} *)
    
    (* Step 1: Use partial_sum_mono and term_bound to get upper bound *)
    (* ps(S m0) - ps(m) <= ps(S m0) - ps(m0) + ps(m0) - ps(m) *)
    (*                   = d_{m0}/3^{m0+1} + (ps(m0) - ps(m)) *)
    
    (* First, show: ps(m0) + d/3^{m0+1} - ps(m) <= (ps(m0) - ps(m)) + d/3^{m0+1} *)
    (* This is just rearrangement *)
    apply Qle_trans with ((partial_sum T m0 - partial_sum T m) + (digit T m0 # pow3 (S m0))).
    + (* ps(m0) + d - ps(m) <= (ps(m0) - ps(m)) + d *)
      (* This is equality modulo Qeq *)
      unfold Qle, Qminus, Qplus, Qopp. simpl. lia.
    + (* (ps(m0) - ps(m)) + d <= (1/3^m - 1/3^{m0}) + 2/3^{m0+1} <= 1/3^m - 1/3^{S m0} *)
      apply Qle_trans with ((/ Qpow3 m - / Qpow3 m0) + (2 # pow3 (S m0))).
      * apply Qplus_le_compat.
        -- exact IHHmn.
        -- apply term_bound.
      * (* 1/3^m - 1/3^{m0} + 2/3^{m0+1} <= 1/3^m - 1/3^{S m0} *)
        (* Using: 1/3^{m0} = 3/3^{S m0} *)
        (* LHS = 1/3^m - 3/3^{S m0} + 2/3^{S m0} = 1/3^m - 1/3^{S m0} = RHS *)
        assert (Heq : / Qpow3 m0 == 3 * / Qpow3 (S m0)).
        { symmetry. apply three_over_pow3_S. }
        assert (Hterm : (2 # pow3 (S m0)) == 2 * / Qpow3 (S m0)).
        { unfold Qpow3, Qinv, Qmult, Qeq. simpl. ring. }
        setoid_rewrite Heq. setoid_rewrite Hterm.
        ring_simplify.
        apply Qle_refl.
Qed.

(* Main tail bound *)
Lemma tail_bound : forall T m n,
  (m <= n)%nat ->
  partial_sum T n - partial_sum T m <= / Qpow3 m.
Proof.
  intros T m n Hmn.
  apply Qle_trans with (/ Qpow3 m - / Qpow3 n).
  - apply tail_bound_exact. exact Hmn.
  - (* 1/3^m - 1/3^n <= 1/3^m since 1/3^n > 0 *)
    unfold Qminus.
    setoid_replace (/ Qpow3 m) with (/ Qpow3 m + 0) at 2 by ring.
    apply Qplus_le_r.
    setoid_replace 0 with (- 0) by ring.
    apply Qopp_le_compat.
    apply Qlt_le_weak. apply Qinv_pow3_pos.
Qed.

(* ========================================================================= *)
(*                     SECTION 5: DIGIT EXTRACTION FROM Q                    *)
(* ========================================================================= *)

Definition Qfloor (q : Q) : Z :=
  let (n, d) := q in (n / Z.pos d)%Z.

Definition extract_digit (q : Q) (k : nat) : Z :=
  let scaled := q * Qpow3 k in
  let floored := Qfloor scaled in
  (floored mod 3)%Z.

Lemma extract_digit_range : forall q k,
  (0 <= extract_digit q k < 3)%Z.
Proof.
  intros q k. unfold extract_digit.
  apply Z.mod_pos_bound. lia.
Qed.

(* ========================================================================= *)
(*                     SECTION 6: TERNARY FLIP                               *)
(* ========================================================================= *)

Definition ternary_flip (d : Z) : Z :=
  if (d =? 0)%Z then 2%Z
  else if (d =? 2)%Z then 0%Z
  else 2%Z.

Lemma ternary_flip_valid : forall d,
  ternary_flip d = 0%Z \/ ternary_flip d = 2%Z.
Proof.
  intro d. unfold ternary_flip.
  destruct (d =? 0)%Z; [right; reflexivity |].
  destruct (d =? 2)%Z; [left; reflexivity | right; reflexivity].
Qed.

Lemma ternary_flip_bounds : forall d,
  (0 <= ternary_flip d <= 2)%Z.
Proof.
  intro d.
  destruct (ternary_flip_valid d) as [H | H]; rewrite H; lia.
Qed.

(* KEY LEMMA: flip always differs from original *)
Lemma ternary_flip_differs : forall d,
  (0 <= d < 3)%Z -> (ternary_flip d <> d)%Z.
Proof.
  intros d Hd. unfold ternary_flip.
  destruct (d =? 0)%Z eqn:H0.
  - apply Z.eqb_eq in H0. lia.
  - destruct (d =? 2)%Z eqn:H2.
    + apply Z.eqb_eq in H2. lia.
    + apply Z.eqb_neq in H0. apply Z.eqb_neq in H2. lia.
Qed.

(* Stronger: |flip(d) - d| >= 1 *)
Lemma ternary_flip_diff_ge_1 : forall d,
  (0 <= d < 3)%Z -> (Z.abs (ternary_flip d - d) >= 1)%Z.
Proof.
  intros d Hd. unfold ternary_flip.
  destruct (d =? 0)%Z eqn:H0.
  - apply Z.eqb_eq in H0. subst. simpl. lia.
  - destruct (d =? 2)%Z eqn:H2.
    + apply Z.eqb_eq in H2. subst. simpl. lia.
    + apply Z.eqb_neq in H0. apply Z.eqb_neq in H2.
      assert (d = 1)%Z by lia. subst. simpl. lia.
Qed.

(* When both are in {0,2}, diff is exactly 2 *)
Lemma ternary_flip_diff_extreme : forall d,
  (d = 0 \/ d = 2)%Z -> (Z.abs (ternary_flip d - d) = 2)%Z.
Proof.
  intros d [H | H]; subst; unfold ternary_flip; simpl; reflexivity.
Qed.

(* ========================================================================= *)
(*                     PART II: DIAGONAL CONSTRUCTION                        *)
(* ========================================================================= *)

(* ========================================================================= *)
(*                     SECTION 7: REAL PROCESSES                             *)
(* ========================================================================= *)

Definition RealProcess := nat -> Q.

Definition is_Cauchy (R : RealProcess) : Prop :=
  forall eps : Q, eps > 0 ->
  exists N : nat, forall m n : nat,
    (m > N)%nat -> (n > N)%nat ->
    Qabs (R m - R n) < eps.

Definition in_unit_interval (R : RealProcess) : Prop :=
  forall n : nat, 0 <= R n /\ R n <= 1.

Definition equiv (R1 R2 : RealProcess) : Prop :=
  forall eps : Q, eps > 0 ->
  exists N : nat, forall n : nat,
    (n > N)%nat -> Qabs (R1 n - R2 n) < eps.

Definition not_equiv (R1 R2 : RealProcess) : Prop :=
  exists eps : Q, eps > 0 /\
  forall N : nat, exists n : nat,
    (n > N)%nat /\ Qabs (R1 n - R2 n) >= eps.

(* ========================================================================= *)
(*                     SECTION 8: ENUMERATION                                *)
(* ========================================================================= *)

Definition Enumeration := nat -> RealProcess.

Definition valid_enumeration (E : Enumeration) : Prop :=
  forall n : nat, is_Cauchy (E n) /\ in_unit_interval (E n).

(* ========================================================================= *)
(*                     SECTION 9: DIAGONAL DIGIT CONSTRUCTION                *)
(* ========================================================================= *)

(*
   Given enumeration E : nat -> (nat -> Q),
   construct diagonal digits that differ from each E(n) at position n.
*)

Definition diagonal_digit (E : Enumeration) (k : nat) : Z :=
  ternary_flip (extract_digit (E k k) k).

Lemma diagonal_digit_valid : forall E k,
  diagonal_digit E k = 0%Z \/ diagonal_digit E k = 2%Z.
Proof.
  intros E k. unfold diagonal_digit. apply ternary_flip_valid.
Qed.

Definition diagonal_exp (E : Enumeration) : TernaryExp :=
  mkTernary (diagonal_digit E) (diagonal_digit_valid E).

(* ========================================================================= *)
(*            SECTION 10: THE KEY STRUCTURAL THEOREM (Z-LEVEL)               *)
(* ========================================================================= *)

(*
   THIS IS FULLY PROVED - the core of the diagonal argument!
   At position n, the diagonal digit differs from E(n)'s digit.
*)

Theorem diagonal_differs_structurally : forall E n,
  diagonal_digit E n <> extract_digit (E n n) n.
Proof.
  intros E n.
  unfold diagonal_digit.
  apply ternary_flip_differs.
  apply extract_digit_range.
Qed.

(* Quantitative version *)
Theorem diagonal_diff_ge_1 : forall E n,
  (Z.abs (diagonal_digit E n - extract_digit (E n n) n) >= 1)%Z.
Proof.
  intros E n.
  unfold diagonal_digit.
  apply ternary_flip_diff_ge_1.
  apply extract_digit_range.
Qed.

(* ========================================================================= *)
(*                     SECTION 11: DIAGONAL AS REAL PROCESS                  *)
(* ========================================================================= *)

Definition diagonal (E : Enumeration) : RealProcess :=
  fun n => partial_sum (diagonal_exp E) n.

(* Diagonal is in [0, 1] *)
Theorem diagonal_in_unit : forall E,
  valid_enumeration E ->
  in_unit_interval (diagonal E).
Proof.
  intros E Hvalid n.
  unfold diagonal.
  apply partial_sum_in_unit.
Qed.

(* ========================================================================= *)
(*                     SECTION 12: ARCHIMEDEAN PROPERTY                      *)
(* ========================================================================= *)

(* Key lemma: 3^n >= n + 1 for all n *)
Lemma pow3_ge_Sn : forall n, (Z.pos (pow3 n) >= Z.of_nat (S n))%Z.
Proof.
  induction n.
  - simpl. lia.
  - simpl pow3.
    replace (Z.pos (3 * pow3 n)) with (3 * Z.pos (pow3 n))%Z by lia.
    replace (Z.of_nat (S (S n))) with (Z.of_nat (S n) + 1)%Z by lia.
    lia.
Qed.

(* Corollary: weaker version *)
Lemma pow3_ge_n : forall n, (Z.pos (pow3 n) >= Z.of_nat n)%Z.
Proof.
  intro n. pose proof (pow3_ge_Sn n). lia.
Qed.

(* Helper: convert positive to nat for comparison *)
Lemma positive_nat_Z : forall p : positive,
  Z.of_nat (Pos.to_nat p) = Z.pos p.
Proof.
  intro p. rewrite positive_nat_Z. reflexivity.
Qed.

(* For any positive p, exists N such that 3^N > p *)
Lemma pow3_exceeds_pos : forall p : positive, exists N : nat, (pow3 N > p)%positive.
Proof.
  intro p.
  exists (S (Pos.to_nat p)).
  pose proof (pow3_ge_Sn (S (Pos.to_nat p))) as H.
  assert (Hnat : (Z.of_nat (S (S (Pos.to_nat p))) = Z.pos p + 2)%Z).
  { rewrite Nat2Z.inj_succ. rewrite Nat2Z.inj_succ.
    rewrite positive_nat_Z. lia. }
  rewrite Hnat in H. lia.
Qed.

(* 3^n is unbounded over Z *)
Lemma pow3_unbounded : forall M : Z, exists N : nat, (Z.pos (pow3 N) > M)%Z.
Proof.
  intro M.
  destruct (Z_lt_le_dec M 1) as [Hsmall | Hbig].
  - exists 0%nat. simpl. lia.
  - assert (Hpos : exists p, M = Z.pos p) by (exists (Z.to_pos M); lia).
    destruct Hpos as [p Hp]. subst M.
    destruct (pow3_exceeds_pos p) as [N HN].
    exists N. lia.
Qed.

(* Archimedean property: 3^n grows without bound *)
Theorem archimedean_pow3 : forall eps : Q,
  eps > 0 -> exists N : nat, / Qpow3 N < eps.
Proof.
  intros eps Heps.
  destruct eps as [p q].
  unfold Qlt in Heps. simpl in Heps.
  assert (Hp : (p > 0)%Z) by lia.
  destruct (pow3_exceeds_pos q) as [N HN].
  exists N.
  unfold Qlt, Qdiv, Qmult, Qinv, Qpow3. simpl.
  (* Goal: 1 * Z.pos q < p * (1 * Z.pos (pow3 N)) *)
  (* i.e., Z.pos q < p * Z.pos (pow3 N) *)
  (* We have pow3 N > q, so Z.pos (pow3 N) > Z.pos q *)
  (* And p >= 1, so p * Z.pos (pow3 N) >= Z.pos (pow3 N) > Z.pos q *)
  nia.
Qed.

(* ========================================================================= *)
(*                     SECTION 13: DIAGONAL IS CAUCHY                        *)
(* ========================================================================= *)

Theorem diagonal_is_Cauchy : forall E,
  valid_enumeration E ->
  is_Cauchy (diagonal E).
Proof.
  intros E Hvalid.
  unfold is_Cauchy, diagonal.
  intros eps Heps.
  
  (* Step 1: Find N such that 1/3^N < eps *)
  destruct (@archimedean_pow3 eps Heps) as [N HN].
  
  (* Step 2: Claim: this N works *)
  exists N.
  intros m n Hm Hn.
  
  (* Step 3: Case split on m <= n or n <= m *)
  (* Goal: Qabs (partial_sum m - partial_sum n) < eps *)
  destruct (Nat.le_ge_cases m n) as [Hmn | Hnm].
  
  - (* Case m <= n *)
    (* partial_sum m <= partial_sum n, so partial_sum m - partial_sum n <= 0 *)
    assert (Hdiff : partial_sum (diagonal_exp E) m <= partial_sum (diagonal_exp E) n).
    { apply partial_sum_mono. exact Hmn. }
    
    (* Use Qabs_Qlt_condition: |x| < y iff -y < x < y *)
    (* Here x = ps m - ps n <= 0 *)
    apply Qabs_Qlt_condition.
    split.
    + (* -eps < ps m - ps n *)
      (* ps m - ps n = -(ps n - ps m) >= -1/3^m > -eps *)
      (* Need: ps n - ps m < eps, then apply Qopp_lt_compat *)
      assert (Hbound : partial_sum (diagonal_exp E) n - partial_sum (diagonal_exp E) m < eps).
      { apply Qle_lt_trans with (/ Qpow3 m).
        - apply tail_bound. exact Hmn.
        - apply Qle_lt_trans with (/ Qpow3 N).
          + apply inv_pow3_mono. lia.
          + exact HN. }
      (* From ps n - ps m < eps, get -eps < -(ps n - ps m) = ps m - ps n *)
      assert (Hopp : - eps < - (partial_sum (diagonal_exp E) n - partial_sum (diagonal_exp E) m)).
      { apply Qopp_lt_compat. exact Hbound. }
      setoid_replace (partial_sum (diagonal_exp E) m - partial_sum (diagonal_exp E) n)
        with (- (partial_sum (diagonal_exp E) n - partial_sum (diagonal_exp E) m)) by ring.
      exact Hopp.
    + (* ps m - ps n < eps *)
      (* ps m - ps n <= 0 < eps *)
      apply Qle_lt_trans with 0.
      * apply Qminus_le_0. exact Hdiff.
      * exact Heps.
      
  - (* Case n <= m *)
    (* partial_sum n <= partial_sum m, so partial_sum m - partial_sum n >= 0 *)
    assert (Hdiff : partial_sum (diagonal_exp E) n <= partial_sum (diagonal_exp E) m).
    { apply partial_sum_mono. exact Hnm. }
    
    apply Qabs_Qlt_condition.
    split.
    + (* -eps < ps m - ps n *)
      (* ps m - ps n >= 0 > -eps *)
      apply Qlt_le_trans with 0.
      * setoid_replace 0 with (- 0) by ring.
        apply Qopp_lt_compat. exact Heps.
      * (* 0 <= ps m - ps n *)
        apply Qle_0_minus. exact Hdiff.
    + (* ps m - ps n < eps *)
      (* ps m - ps n <= 1/3^n < eps *)
      apply Qle_lt_trans with (/ Qpow3 n).
      * apply tail_bound. exact Hnm.
      * apply Qle_lt_trans with (/ Qpow3 N).
        -- apply inv_pow3_mono. lia.
        -- exact HN.
Qed.

(* ========================================================================= *)
(*            SECTION 14: LIFTING Z-DIFFERENCE TO Q-DIFFERENCE               *)
(* ========================================================================= *)

(*
   THE BRIDGE: Converting structural Z-level difference to Q-level separation.
   
   Key insight:
   - diagonal_digit E n  extract_digit (E n n) n  [PROVED at Z-level]
   - |diagonal_digit E n - extract_digit (E n n) n| >= 1  [PROVED]
   - This contributes >= 1/3^{n+1} to Q-difference at position n
   - Tail errors are bounded by 1/3^m for m large enough
   - If we take m >> n, the difference persists
*)

(* Buffer for stability *)
Definition precision_buffer : nat := 10.

(*
   At position m = n + buffer, the n-th digit contribution dominates.
   
   diagonal(m) contributes diagonal_digit(n) / 3^{n+1} at position n
   E(n)(m) has digit extract_digit(E n m) n at position n
   
   The key is: for m large enough, extract_digit(E n m) n ~= extract_digit(E n n) n
   due to Cauchy stability of E(n).
*)

Lemma digit_contribution_diff : forall E n,
  let d_diag := diagonal_digit E n in
  let d_enum := extract_digit (E n n) n in
  Qabs ((d_diag # pow3 (S n)) - (d_enum # pow3 (S n))) >= / Qpow3 (S n).
Proof.
  intros E n d_diag d_enum.
  pose proof (diagonal_diff_ge_1 E n) as Hdiff.
  unfold d_diag, d_enum in *.
  (* |d_diag - d_enum| >= 1 at Z-level *)
  (* Need: |(d_diag - d_enum) / 3^{n+1}| >= 1/3^{n+1} *)
  remember (diagonal_digit E n - extract_digit (E n n) n)%Z as diff eqn:Hdiff_eq.
  unfold Qabs, Qminus. simpl.
  destruct diff eqn:Heq.
  - (* difference = 0, contradicts Hdiff *)
    exfalso.
    subst diff. simpl in Hdiff. lia.
  - (* difference > 0 *)
    unfold Qge, Qle, Qinv. simpl.
    (* Z.abs (Z.pos p) = Z.pos p, need Z.pos p >= 1 *)
    subst diff. simpl in Hdiff. nia.
  - (* difference < 0 *)
    unfold Qge, Qle, Qinv. simpl.
    subst diff. simpl in Hdiff. nia.
Qed.

(* The main separation lemma *)
(* 
   MATHEMATICAL ARGUMENT (complete):
   1. diagonal_digit(n) = flip(extract_digit(E n n, n)) ≠ extract_digit(E n n, n) [PROVED]
   2. This contributes |diff| >= 1/3^{n+1} to Q-difference at position n [PROVED]
   3. By Cauchy property of E n, for large m: |E n m - E n n| < delta
   4. If delta < 1/(2*3^{n+1}), digit at position n changes by at most 1
   5. Since diagonal_digit ∈ {0,2} and flip ensures difference, |diagonal_digit(n) - d_n| >= 1
   6. Tail errors are O(1/3^m), negligible for m >> n
   
   The formalization requires careful Cauchy epsilon-delta argument that is technically
   involved but mathematically straightforward. The structural core is fully proved.
*)
(* =========================================================================
   IMPORTANT NOTE ON DIGIT STABILITY
   =========================================================================
   
   This lemma requires "digit stability": showing that extract_digit(E n m, n)
   remains close to extract_digit(E n n, n) for large m.
   
   THE PROBLEM: Qfloor and (mod 3) are DISCONTINUOUS operations (L3 level).
   Near boundaries like 0.999... = 1.000..., tiny Q-changes cause digit jumps.
   
   Example: If E n n ≈ 1/3 - ε, digit = 0. If E n m ≈ 1/3 + ε, digit = 1.
   The Cauchy property guarantees |E n m - E n n| < δ, but NOT digit stability!
   
   Worse: If original digit = 1 and it shifts to 2, and flip(1) = 2,
   then diagonal_digit = 2 = shifted_digit, giving difference = 0.
   
   SOLUTION (Theory of Systems / P4):
   
   The "digit manipulation" approach is fundamentally flawed because it
   applies discrete L3 operations to continuous L2 processes.
   
   The CORRECT approach is "Digit Stability through Geometry" as implemented
   in ShrinkingIntervals_uncountable_CLEAN.v:
   
   1. Use TRISECTION instead of digit extraction
   2. Choose sub-interval that AVOIDS E(n) with guaranteed GAP
   3. Gap = delta = 1/(12 * 3^n) ensures stability
   4. No Qfloor/mod needed — pure interval arithmetic
   
   This file preserves the digit-based diagonal as a PEDAGOGICAL example
   showing why the naive Cantor approach has technical difficulties.
   
   For the COMPLETE, FULLY PROVED uncountability theorem, see:
   ShrinkingIntervals_uncountable_CLEAN.v : unit_interval_uncountable_trisect_v2
   ========================================================================= *)

Lemma diagonal_differs_at_n : forall E n,
  valid_enumeration E ->
  exists eps : Q, eps > 0 /\
    forall m, (m > n + precision_buffer)%nat ->
    Qabs (diagonal E m - E n m) >= eps.
Proof.
  intros E n Hvalid.
  
  (* Use eps = 1/(2 * 3^{n+2}) *)
  exists (/ Qpow3 (S (S n)) / 2).
  split.
  - (* eps > 0 *)
    apply Qlt_shift_div_l.
    + reflexivity.
    + rewrite Qmult_0_l. apply Qinv_pow3_pos.
  - intros m Hm.
    (* ADMITTED due to digit stability problem (see note above).
       
       The structural core IS proved:
       1. diagonal_differs_structurally: flip(digit) ≠ digit [PROVED - Z level]
       2. digit_contribution_diff: |d_diag - d_enum| / 3^{n+1} >= 1/3^{n+1} [PROVED]
       3. tail_bound: tail <= 1/3^m [PROVED]
       
       What's missing: digit stability under Cauchy convergence.
       This is NOT provable in general due to Qfloor discontinuity.
       
       For the COMPLETE proof, use the interval-based approach in
       ShrinkingIntervals_uncountable_CLEAN.v which avoids this issue entirely.
    *)
    admit.
Admitted.

(* ========================================================================= *)
(*                     SECTION 15: DIAGONAL NOT IN ENUMERATION               *)
(* ========================================================================= *)

Theorem diagonal_not_in_enumeration : forall (E : Enumeration) (n : nat),
  valid_enumeration E ->
  not_equiv (diagonal E) (E n).
Proof.
  intros E n Hvalid.
  unfold not_equiv.
  
  pose proof (@diagonal_differs_at_n E n Hvalid) as [eps [Heps Hsep]].
  exists eps. split.
  - exact Heps.
  - intro N.
    (* Choose m = max(N, n + precision_buffer) + 1 *)
    (* This ensures m > N and m > n + precision_buffer *)
    set (m := S (Nat.max N (n + precision_buffer))).
    exists m.
    split.
    + (* m > N *)
      unfold m.
      apply Nat.lt_succ_r.
      apply Nat.le_max_l.
    + (* Qabs (diagonal E m - E n m) >= eps *)
      apply Hsep.
      (* m > n + precision_buffer *)
      unfold m.
      apply Nat.lt_succ_r.
      apply Nat.le_max_r.
Qed.

(* ========================================================================= *)
(*                     SECTION 16: MAIN THEOREM                              *)
(* ========================================================================= *)

Theorem unit_interval_uncountable : forall E : Enumeration,
  valid_enumeration E ->
  exists D : RealProcess,
    is_Cauchy D /\
    in_unit_interval D /\
    forall n : nat, not_equiv D (E n).
Proof.
  intros E Hvalid.
  exists (diagonal E).
  split; [| split].
  - apply diagonal_is_Cauchy. exact Hvalid.
  - apply diagonal_in_unit. exact Hvalid.
  - intro n. apply diagonal_not_in_enumeration. exact Hvalid.
Qed.

(* ========================================================================= *)
(*                     VERIFICATION & STATUS                                 *)
(* ========================================================================= *)

Check unit_interval_uncountable.
Print Assumptions unit_interval_uncountable.

(*
   =======================================================================
   STATUS: DIGIT-BASED DIAGONAL (PEDAGOGICAL VERSION)
   =======================================================================
   
   This file demonstrates the CLASSICAL Cantor diagonal argument using
   ternary digit extraction and flip. It serves as a PEDAGOGICAL example.
   
   FULLY PROVED (Qed) - 41 lemmas:
   - diagonal_differs_structurally : flip(digit) <> digit [Z-level - THE CORE]
   - diagonal_diff_ge_1 : |flip - orig| >= 1 [Z-level]
   - digit_contribution_diff : Q-contribution difference >= 1/3^{n+1}
   - partial_sum_bound : ps(n) <= 1 - 1/3^n
   - partial_sum_in_unit : ps(n) in [0, 1]
   - archimedean_pow3 : forall eps>0. exists N. 1/3^N < eps
   - diagonal_in_unit : diagonal in [0, 1]
   - diagonal_is_Cauchy : diagonal converges
   - diagonal_not_in_enumeration : diagonal <> E(n) for all n
   - unit_interval_uncountable : main theorem (depends on Admitted)
   
   ADMITTED (1 lemma) - FUNDAMENTAL LIMITATION:
   - diagonal_differs_at_n : requires "digit stability"
   
   =======================================================================
   WHY DIGIT STABILITY IS PROBLEMATIC (Theory of Systems perspective)
   =======================================================================
   
   The function extract_digit uses Qfloor and (mod 3), which are
   DISCONTINUOUS operations. This is trying to apply L3 (discrete)
   operations to L2 (continuous processes).
   
   Near boundaries (e.g., 0.333... vs 0.334...), tiny Q-changes cause
   digit jumps. The Cauchy property guarantees |E n m - E n n| < delta,
   but NOT that their digits remain the same.
   
   This is the "0.999... = 1.000..." problem in constructive analysis.
   
   =======================================================================
   THE SOLUTION: INTERVAL-BASED APPROACH (P4-compatible)
   =======================================================================
   
   The CORRECT approach in Theory of Systems is to avoid digit extraction
   entirely and use "Digit Stability through Geometry":
   
   1. TRISECTION: Divide interval into three parts
   2. AVOIDANCE: Choose sub-interval that AVOIDS E(n) with guaranteed GAP
   3. GAP BOUND: delta = 1/(12 * 3^n) ensures stability
   4. PURE GEOMETRY: No Qfloor, no mod - only interval arithmetic
   
   This is implemented in: ShrinkingIntervals_uncountable_CLEAN.v
   Main theorem: unit_interval_uncountable_trisect_v2 (FULLY PROVED, 0 Admitted)
   
   Key insight (Gemini 2025): "Trisection ALWAYS works because the enemy
   occupies at most 1/3 of the interval, leaving 2/3 free with guaranteed gap."
   
   =======================================================================
   PHILOSOPHICAL SIGNIFICANCE
   =======================================================================
   
   The digit-based diagonal is a "naive translation" of Cantor's argument
   that struggles with the L2/L3 boundary (continuous vs discrete).
   
   The interval-based approach embodies P4 (Finitude) properly:
   - Each step is finite and decidable
   - No discontinuous operations on continuous objects
   - Gap provides "sufficient reason" (L4) for separation
   
   Both prove uncountability, but the interval approach is:
   - More robust (no edge cases)
   - More aligned with Theory of Systems
   - Fully formalizable without technical gaps
   
   =======================================================================
   DEPENDENCIES
   =======================================================================
   
   Axioms used: classic (L3 - Excluded Middle)
   NOT used: Axiom of Infinity, Axiom of Choice
   
   For COMPLETE proof: See ShrinkingIntervals_uncountable_CLEAN.v
   
   =======================================================================
*)
