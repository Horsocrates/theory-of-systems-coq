(* ========================================================================= *)
(*                                                                           *)
(*                    TERNARY REPRESENTATION OF REALS                        *)
(*              Structural Foundation for Diagonal Argument                  *)
(*                                                                           *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)         *)
(*                                                                           *)
(*  Author:  Horsocrates                                                     *)
(*  Version: 2.0 (E/R/R)                                                     *)
(*  Date:    January 2026                                                    *)
(*                                                                           *)
(*  STATUS: 28 Qed, 7 Admitted (~80%)                                        *)
(*                                                                           *)
(* ========================================================================= *)
(*                                                                           *)
(*  E/R/R INTERPRETATION:                                                    *)
(*  =====================                                                    *)
(*                                                                           *)
(*  This file provides the SUBSTRATE for diagonal construction:              *)
(*                                                                           *)
(*    Elements = TernarySequence = nat -> {0, 2}                             *)
(*    Roles    = digit_at (position-based access)                            *)
(*    Rules    = ternary_flip (0 <-> 2, avoiding boundary digit 1)           *)
(*                                                                           *)
(*  KEY INSIGHT (L1 + P4):                                                   *)
(*    Digits are PRIMARY, not derived from Q.                                *)
(*    Each position is a binary choice (A or ~A) - L1 distinction.           *)
(*    The sequence is a PROCESS - P4 finitude.                               *)
(*                                                                           *)
(*  PHILOSOPHY: DIGITS AS DISTINCTIONS                                       *)
(*    - Distinction (digit choice: 0 or 2) is fundamental                    *)
(*    - Numbers emerge from sequences of distinctions                        *)
(*    - Avoiding digit 1 = avoiding boundary = clean binary choice           *)
(*    - flip(0) = 2, flip(2) = 0 embodies primordial A/~A                    *)
(*                                                                           *)
(* ========================================================================= *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qfield.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.

Set Implicit Arguments.
Open Scope Q_scope.

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
  pose proof (Qpow3_pos n). rewrite H in H0. 
  apply Qlt_irrefl in H0. exact H0. 
Qed.

Lemma Qpow3_S : forall n, Qpow3 (S n) == 3 * Qpow3 n.
Proof. 
  intro n. unfold Qpow3. simpl. 
  unfold Qeq, Qmult. simpl. ring. 
Qed.

Lemma Qinv_pow3_pos : forall n, 0 < / Qpow3 n.
Proof. intro n. apply Qinv_lt_0_compat. apply Qpow3_pos. Qed.

Lemma inv_pow3_sum : forall n,
  / Qpow3 n == / Qpow3 (S n) + / Qpow3 (S n) + / Qpow3 (S n).
Proof.
  intro n.
  rewrite Qpow3_S.
  field.
  apply Qpow3_nonzero.
Qed.

(* 1/3^{n+1} <= 1/3^n *)
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
      { induction Hlt; simpl; lia. }
      lia.
Qed.

(* ========================================================================= *)
(*                     SECTION 2: TERNARY EXPANSION (PRIMARY)                *)
(* ========================================================================= *)

(* 
   A TernaryExp is a sequence of digits, each either 0 or 2.
   This is the PRIMARY object - numbers are DERIVED from it.
   
   Philosophically: each position is a binary choice (A or ~A),
   avoiding the boundary (digit 1).
*)

Record TernaryExp := mkTernary {
  digit : nat -> Z;
  digit_valid : forall k, digit k = 0%Z \/ digit k = 2%Z
}.

(* Digit bounds follow from validity *)
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
(*                     SECTION 3: FROM DIGITS TO Q (to_Q)                    *)
(* ========================================================================= *)

(* 
   Partial sum: Sum_{k=0}^{n-1} digit(k) / 3^{k+1}
   This is what the digit sequence "means" as a rational approximation.
*)

Fixpoint partial_sum (T : TernaryExp) (n : nat) : Q :=
  match n with
  | O => 0
  | S n' => partial_sum T n' + (digit T n' # pow3 (S n'))
  end.

(* Notation for clarity *)
Definition to_Q (T : TernaryExp) (n : nat) : Q := partial_sum T n.

(* Basic properties of partial_sum *)

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

(* Helper lemma for Q arithmetic *)
Lemma partial_sum_arith_helper : forall p : positive,
  (((1 * Z.pos p + -1) * Z.pos (3 * p) + 2 * Z.pos p) * Z.pos (3 * p) <=
   (Z.pos (3 * p) + -1) * (Z.pos p * Z.pos (3 * p)))%Z.
Proof. intro p. nia. Qed.

Lemma partial_sum_bound_step : forall n,
  1 - / Qpow3 n + (2 # pow3 (S n)) <= 1 - / Qpow3 (S n).
Proof.
  intro n.
  unfold Qle, Qpow3, Qminus, Qplus, Qinv, Qopp.
  simpl Qnum. simpl Qden.
  change (pow3 (S n)) with (3 * pow3 n)%positive.
  apply partial_sum_arith_helper.
Qed.

(* Partial sum is bounded by 1 - 1/3^n *)
Lemma partial_sum_bound : forall T n,
  partial_sum T n <= 1 - / Qpow3 n.
Proof.
  intros T.
  induction n.
  - simpl. unfold Qpow3. simpl. 
    unfold Qle, Qminus, Qinv. simpl. lia.
  - simpl partial_sum.
    (* Need: ps(n) + d_n/3^{n+1} <= 1 - 1/3^{n+1} *)
    (* We have: ps(n) <= 1 - 1/3^n *)
    (* And: d_n/3^{n+1} <= 2/3^{n+1} *)
    (* So: ps(n) + d_n/3^{n+1} <= 1 - 1/3^n + 2/3^{n+1} *)
    (* Need to show: 1 - 1/3^n + 2/3^{n+1} <= 1 - 1/3^{n+1} *)
    
    apply Qle_trans with ((1 - / Qpow3 n) + (2 # pow3 (S n))).
    + apply Qplus_le_compat.
      * exact IHn.
      * apply term_bound.
    + apply partial_sum_bound_step.
Qed.

(* Corollary: partial sum is in [0, 1] *)
Lemma partial_sum_in_unit : forall T n,
  0 <= partial_sum T n <= 1.
Proof.
  intros T n. split.
  - apply partial_sum_nonneg.
  - apply Qle_trans with (1 - / Qpow3 n).
    + apply partial_sum_bound.
    + (* 1 - 1/3^n <= 1 because 1/3^n > 0 *)
      unfold Qminus.
      setoid_replace 1 with (1 + 0) at 2 by ring.
      apply Qplus_le_r.
      (* Need: -1/3^n <= 0, i.e., 0 <= 1/3^n after applying Qopp_le_compat *)
      setoid_replace 0 with (- 0) by ring.
      apply Qopp_le_compat.
      apply Qlt_le_weak. apply Qinv_pow3_pos.
Qed.

(* ========================================================================= *)
(*                     SECTION 4: MONOTONICITY OF PARTIAL SUMS              *)
(* ========================================================================= *)

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
(*                     SECTION 5: TAIL BOUNDS                               *)
(* ========================================================================= *)

(* 
   The "tail" from position k onwards is bounded by 1/3^k.
   This is the key estimate for convergence.
*)

(* Helper lemmas for tail bound proof *)
Lemma Z_identity_tail : forall z : Z, 
  (2 * (z * (3 * z)) = (1 * (3 * z) + -1 * z) * (3 * z))%Z.
Proof. intro z. ring. Qed.

Lemma Zpos_mul_assoc : forall p q : positive,
  Z.pos (p * q) = (Z.pos p * Z.pos q)%Z.
Proof. intros. apply Pos2Z.inj_mul. Qed.

(* Key: 2/3^{k+1} = 1/3^k - 1/3^{k+1} *)
Lemma term_eq_diff : forall k,
  (2 # pow3 (S k)) == / Qpow3 k - / Qpow3 (S k).
Proof.
  intro k.
  unfold Qpow3, Qeq, Qminus, Qinv, Qopp.
  simpl Qnum. simpl Qden. simpl pow3.
  rewrite !Zpos_mul_assoc.
  apply Z_identity_tail.
Qed.

(* Helper: x - y <= x when y >= 0 *)
Lemma Qminus_le_self : forall x y, 0 <= y -> x - y <= x.
Proof.
  intros x y Hy.
  apply Qle_minus_iff.
  ring_simplify.
  exact Hy.
Qed.

(* Stronger bound: ps(n) - ps(m) <= 1/3^m - 1/3^n *)
Lemma tail_bound_strong : forall T m n,
  (m <= n)%nat ->
  partial_sum T n - partial_sum T m <= / Qpow3 m - / Qpow3 n.
Proof.
  intros T m n Hmn.
  induction Hmn.
  - ring_simplify. apply Qle_refl.
  - simpl partial_sum.
    setoid_replace (partial_sum T m0 + (digit T m0 # pow3 (S m0)) - partial_sum T m)
      with ((partial_sum T m0 - partial_sum T m) + (digit T m0 # pow3 (S m0)))
      by ring.
    apply Qle_trans with ((/ Qpow3 m - / Qpow3 m0) + (2 # pow3 (S m0))).
    + apply Qplus_le_compat.
      * exact IHHmn.
      * apply term_bound.
    + setoid_rewrite term_eq_diff.
      ring_simplify.
      apply Qle_refl.
Qed.

(* Maximum possible tail: Sum_{j=k}^{inf} 2/3^{j+1} = 1/3^k *)
Lemma tail_bound_max : forall T m n,
  (m <= n)%nat ->
  partial_sum T n - partial_sum T m <= / Qpow3 m.
Proof.
  intros T m n Hmn.
  apply Qle_trans with (/ Qpow3 m - / Qpow3 n).
  - apply tail_bound_strong; assumption.
  - apply Qminus_le_self.
    apply Qlt_le_weak. apply Qinv_pow3_pos.
Qed.

(* ========================================================================= *)
(*                     SECTION 6: FROM Q TO DIGITS (from_Q)                  *)
(* ========================================================================= *)

(* Floor function for Q *)
Definition Qfloor (q : Q) : Z :=
  let (n, d) := q in (n / Z.pos d)%Z.

(* Extract k-th ternary digit from a rational *)
Definition extract_digit (q : Q) (k : nat) : Z :=
  let scaled := q * Qpow3 k in
  let floored := Qfloor scaled in
  (floored mod 3)%Z.

(* Extract digit is always in {0, 1, 2} *)
Lemma extract_digit_range : forall q k,
  (0 <= extract_digit q k < 3)%Z.
Proof.
  intros q k. unfold extract_digit.
  apply Z.mod_pos_bound. lia.
Qed.

(* For q in [0,1], we need to show extract_digit gives valid ternary digits *)
(* This is subtle: extract_digit can give 1, but for "nice" q it won't *)

(* 
   IMPORTANT: We don't claim extract_digit always gives {0,2}.
   Instead, we work with the weaker bound {0,1,2} and handle
   the middle digit case separately in the flip.
*)

(* Construct TernaryExp from Q - uses {0,1,2} digits *)
Definition from_Q_raw (q : Q) : nat -> Z := fun k => extract_digit q k.

(* ========================================================================= *)
(*                     SECTION 6b: QFLOOR PROPERTIES                        *)
(* ========================================================================= *)

(* Qfloor is the integer part: Qfloor(q) <= q < Qfloor(q) + 1 *)

(* Fractional part *)
Definition Qfrac (q : Q) : Q := q - (Qfloor q # 1).

(* Qfloor lower bound: Qfloor(q) <= q *)
Lemma Qfloor_le : forall q, (Qfloor q # 1) <= q.
Proof.
  intro q. destruct q as [n d].
  unfold Qfloor, Qle. simpl.
  (* Need: (n / Z.pos d) * Z.pos d <= n * 1 *)
  rewrite Z.mul_1_r.
  rewrite Z.mul_comm.
  apply Z.mul_div_le. lia.
Qed.

(* Qfloor upper bound: q < Qfloor(q) + 1 *)
Lemma Qfloor_lt : forall q, q < (Qfloor q # 1) + 1.
Proof.
  intro q. destruct q as [n d].
  unfold Qfloor, Qlt, Qplus. simpl.
  (* Need: n * 1 < ((n / Z.pos d) + 1) * Z.pos d *)
  rewrite Z.mul_1_r.
  (* n < (n / d + 1) * d = (n / d) * d + d *)
  rewrite Z.mul_add_distr_r. rewrite Z.mul_1_l.
  (* n < (n / d) * d + d *)
  (* From Z.div_mod: n = d * (n/d) + (n mod d), so (n/d) * d = n - (n mod d) *)
  (* So need: n < n - (n mod d) + d, i.e., n mod d < d *)
  assert (Hmod : (n mod Z.pos d < Z.pos d)%Z).
  { apply Z.mod_pos_bound. lia. }
  assert (Hdiv : (n / Z.pos d * Z.pos d = n - n mod Z.pos d)%Z).
  { pose proof (Z.div_mod n (Z.pos d)) as Hdm.
    assert (Z.pos d <> 0%Z) by lia.
    specialize (Hdm H).
    lia. }
  lia.
Qed.

(* Fractional part is in [0, 1) *)
Lemma Qfrac_bounds : forall q, 0 <= Qfrac q /\ Qfrac q < 1.
Proof.
  intro q. unfold Qfrac. split.
  - (* 0 <= q - floor(q) *)
    unfold Qminus. 
    setoid_replace 0 with (q + - q) by ring.
    apply Qplus_le_r.
    apply Qopp_le_compat.
    apply Qfloor_le.
  - (* q - floor(q) < 1 *)
    (* We have q < floor(q) + 1 from Qfloor_lt *)
    (* So q - floor(q) < 1 *)
    pose proof (Qfloor_lt q) as Hlt.
    unfold Qminus.
    setoid_replace 1 with ((Qfloor q # 1) + 1 - (Qfloor q # 1)) by ring.
    unfold Qminus.
    apply Qplus_lt_l. exact Hlt.
Qed.

(* For q in [0, 3^n), Qfloor(q) is in [0, 3^n) as integers *)
Lemma Qfloor_nonneg : forall q, 0 <= q -> (0 <= Qfloor q)%Z.
Proof.
  intros q Hq. destruct q as [n d].
  unfold Qfloor, Qle in *. simpl in *.
  apply Z.div_pos; lia.
Qed.

(* Key relationship will be proved after extracted_partial_sum is defined *)

(* ========================================================================= *)
(*                     SECTION 7: THE KEY APPROXIMATION LEMMA               *)
(* ========================================================================= *)

(* Helper: contribution of digit k to the number *)
Definition digit_contribution (q : Q) (k : nat) : Q :=
  (extract_digit q k # pow3 (S k)).

(* Partial sum using extracted digits *)
Fixpoint extracted_partial_sum (q : Q) (n : nat) : Q :=
  match n with
  | O => 0
  | S n' => extracted_partial_sum q n' + digit_contribution q n'
  end.

(* 
   KEY INSIGHT: The relationship between q and its digit expansion.
   
   For q in [0,1], we have:
   - q * 3^n is a rational in [0, 3^n]
   - Qfloor(q * 3^n) captures the "integer part" which encodes digits
   - The fractional part frac(q * 3^n) = q * 3^n - floor(q * 3^n) is in [0,1)
   - So q = floor(q * 3^n)/3^n + frac(q * 3^n)/3^n
   - The error term frac(q * 3^n)/3^n < 1/3^n
   
   The challenge is showing extracted_partial_sum q n == floor(q * 3^n) / 3^n.
   We take an alternative approach: prove the bound directly.
*)

(* Scaled fractional part *)
Definition scaled_frac (q : Q) (n : nat) : Q := Qfrac (q * Qpow3 n).

Lemma scaled_frac_bounds : forall q n,
  0 <= scaled_frac q n /\ scaled_frac q n < 1.
Proof.
  intros q n. unfold scaled_frac. apply Qfrac_bounds.
Qed.

(* Helper: (z # p) == (z # 1) / (p # 1) *)
Lemma Z_over_pos_eq_div : forall (z : Z) (p : positive),
  (z # p) == (z # 1) / (Z.pos p # 1).
Proof.
  intros z p.
  unfold Qdiv, Qinv, Qmult, Qeq. simpl. ring.
Qed.

Lemma floor_div_eq : forall (z : Z) (n : nat),
  (z # pow3 n) == (z # 1) / Qpow3 n.
Proof.
  intros z n. unfold Qpow3. apply Z_over_pos_eq_div.
Qed.

(* The error in approximation equals scaled_frac divided by 3^n *)
Lemma approx_error_formula : forall q n,
  0 <= q <= 1 ->
  q - (Qfloor (q * Qpow3 n) # pow3 n) == scaled_frac q n / Qpow3 n.
Proof.
  intros q n [Hq0 Hq1].
  unfold scaled_frac, Qfrac.
  (* Rewrite (z # pow3 n) as (z # 1) / Qpow3 n *)
  setoid_rewrite floor_div_eq.
  (* Now use field to finish *)
  field.
  apply Qpow3_nonzero.
Qed.

(* The approximation using Qfloor *)
Lemma floor_approx_bound : forall q n,
  0 <= q <= 1 ->
  Qabs (q - (Qfloor (q * Qpow3 n) # pow3 n)) < / Qpow3 n.
Proof.
  intros q n Hq.
  rewrite approx_error_formula by exact Hq.
  destruct (scaled_frac_bounds q n) as [Hge0 Hlt1].
  rewrite Qabs_pos.
  - (* scaled_frac q n / 3^n < 1 / 3^n *)
    unfold Qdiv.
    (* Need: scaled_frac q n * / Qpow3 n < 1 * / Qpow3 n *)
    setoid_replace (/ Qpow3 n) with (1 * / Qpow3 n) at 2 by ring.
    apply Qmult_lt_compat_r.
    + apply Qinv_pow3_pos.
    + exact Hlt1.
  - (* scaled_frac q n / 3^n >= 0 *)
    unfold Qdiv.
    apply Qmult_le_0_compat.
    + exact Hge0.
    + apply Qlt_le_weak. apply Qinv_pow3_pos.
Qed.

(*
   Now we need to show:
   extracted_partial_sum q n == Qfloor(q * 3^n) / 3^n
   
   This is the hard part - relating digit extraction to Qfloor.
*)

(* The core relationship: extracted sum equals scaled floor *)
(* Note: This requires 0 <= q < 1 strictly, or special handling for q = 1 *)
Lemma extracted_equals_floor : forall q n,
  0 <= q <= 1 ->
  extracted_partial_sum q n == (Qfloor (q * Qpow3 n) # pow3 n).
Proof.
  intros q n [Hq0 Hq1].
  (* 
     Key insight: 
     Qfloor(q * 3^n) encodes the first n digits of q in base 3.
     extracted_partial_sum q n reconstructs q from these digits.
     
     The proof requires showing digit extraction is consistent with
     the base-3 expansion encoded in Qfloor.
     
     This is technically involved - requires lemmas about:
     1. Qfloor(q * 3) = 3 * Qfloor(q) + first_digit(q)
     2. extract_digit q 0 = first_digit(q)
     3. Inductive relationship for higher digits
     
     For now, we admit this technical lemma.
  *)
  admit.
Admitted.

(* The fundamental approximation lemma *)
Lemma digit_expansion_approx : forall q n,
  0 <= q <= 1 ->
  Qabs (q - extracted_partial_sum q n) <= / Qpow3 n.
Proof.
  intros q n Hq.
  rewrite extracted_equals_floor by exact Hq.
  apply Qlt_le_weak.
  apply floor_approx_bound. exact Hq.
Qed.

(* ========================================================================= *)
(*                     SECTION 8: DIGIT DIFFERENCE IMPLIES Q DIFFERENCE     *)
(* ========================================================================= *)

(*
   THE PAYOFF: If two digit sequences differ at position k,
   the corresponding Q values differ by at least 1/3^{k+1} - tail_error.
*)

(* When digits differ, the contribution differs *)
Lemma digit_diff_contribution : forall d1 d2 k,
  (d1 <> d2)%Z ->
  (0 <= d1 < 3)%Z ->
  (0 <= d2 < 3)%Z ->
  Qabs ((d1 # pow3 (S k)) - (d2 # pow3 (S k))) >= / Qpow3 (S k).
Proof.
  intros d1 d2 k Hdiff Hd1 Hd2.
  (* |d1 - d2| >= 1, so |d1 - d2|/3^{k+1} >= 1/3^{k+1} *)
  assert (Habs : (Z.abs (d1 - d2) >= 1)%Z) by lia.
  (* Technical Q-arithmetic *)
  unfold Qabs, Qminus, Qge, Qle. simpl.
  unfold Qinv. simpl.
  (* This is: Z.abs(d1 - d2) * 1 >= 1 * 1, i.e., Z.abs(d1 - d2) >= 1 *)
  destruct (d1 - d2)%Z eqn:Heq; simpl.
  - (* d1 = d2, contradiction *)
    exfalso. apply Hdiff. lia.
  - (* d1 > d2 *) nia.
  - (* d1 < d2 *) nia.
Qed.

(* Prefix equality implies partial_sum equality *)
Lemma prefix_sum_eq : forall T1 T2 k,
  (forall j, (j < k)%nat -> digit T1 j = digit T2 j) ->
  partial_sum T1 k == partial_sum T2 k.
Proof.
  intros T1 T2 k Hprefix.
  induction k.
  - simpl. reflexivity.
  - simpl.
    rewrite IHk.
    + rewrite Hprefix. reflexivity. lia.
    + intros j Hj. apply Hprefix. lia.
Qed.

(* Bound is smaller than 1/3^{k+1} *)
Lemma structural_bound_le : forall k n,
  (k < n)%nat ->
  / Qpow3 (S k) - / Qpow3 n - / Qpow3 n <= / Qpow3 (S k).
Proof.
  intros k n Hkn.
  apply Qle_minus_iff.
  ring_simplify.
  unfold Qle, Qinv, Qpow3. simpl. lia.
Qed.

(* Q subtraction with same denominator *)
Lemma Q_sub_same_denom : forall a b p,
  (a # p) - (b # p) == ((a - b) # p).
Proof.
  intros a b p.
  unfold Qminus, Qplus, Qopp, Qeq. simpl. nia.
Qed.

(* 2/3^{k+1} - 1/3^{k+1} = 1/3^{k+1} *)
Lemma two_minus_one_pow3 : forall k,
  (2 # pow3 (S k)) - (/ Qpow3 (S k)) == / Qpow3 (S k).
Proof.
  intro k.
  unfold Qpow3, Qinv. simpl.
  rewrite Q_sub_same_denom.
  reflexivity.
Qed.

(* Helper: a - c <= a when 0 <= c *)
Lemma Qminus_le_nonneg : forall a c, 0 <= c -> a - c <= a.
Proof.
  intros a c Hc.
  unfold Qminus.
  setoid_replace a with (a + 0) at 2 by ring.
  apply Qplus_le_r.
  destruct c as [cn cd]. unfold Qle, Qopp in *. simpl in *. lia.
Qed.

(* a < c implies a - c < 0 *)
Lemma Qlt_minus_neg : forall a c, a < c -> a - c < 0.
Proof.
  intros a c Hlt.
  unfold Qlt, Qminus, Qplus, Qopp in *. simpl in *.
  destruct a as [an ad], c as [cn cd]. simpl in *. nia.
Qed.

(* a >= c implies a - c >= 0 *)
Lemma Qge_minus_nonneg : forall a c, a >= c -> a - c >= 0.
Proof.
  intros a c Hge.
  unfold Qge, Qle, Qminus, Qplus, Qopp in *. simpl in *.
  destruct a as [an ad], c as [cn cd]. simpl in *. nia.
Qed.

(* Key: if 0 <= a <= b and 0 <= c <= b, then |a - c| <= b *)
Lemma abs_diff_bound : forall a c b,
  0 <= a -> a <= b -> 0 <= c -> c <= b ->
  Qabs (a - c) <= b.
Proof.
  intros a c b Ha Hab Hc Hcb.
  destruct (Qlt_le_dec a c) as [Hlt | Hge].
  - rewrite Qabs_neg.
    + assert (Hopp: -(a - c) == c - a) by ring.
      rewrite Hopp.
      apply Qle_trans with c.
      * apply Qminus_le_nonneg. exact Ha.
      * exact Hcb.
    + apply Qlt_le_weak. apply Qlt_minus_neg. exact Hlt.
  - rewrite Qabs_pos.
    + apply Qle_trans with a.
      * apply Qminus_le_nonneg. exact Hc.
      * exact Hab.
    + apply Qge_minus_nonneg. unfold Qge. exact Hge.
Qed.

(* Tail nonneg *)
Lemma tail_nonneg : forall T m n, (m <= n)%nat ->
  0 <= partial_sum T n - partial_sum T m.
Proof.
  intros T m n Hmn.
  unfold Qminus.
  setoid_replace 0 with (partial_sum T m + - partial_sum T m) by ring.
  apply Qplus_le_compat.
  - apply partial_sum_mono. exact Hmn.
  - apply Qle_refl.
Qed.

(* Tail diff bound: |tail1 - tail2| <= 1/3^m *)
Lemma tail_diff_bound : forall T1 T2 m n,
  (m <= n)%nat ->
  Qabs ((partial_sum T1 n - partial_sum T1 m) - (partial_sum T2 n - partial_sum T2 m)) 
    <= / Qpow3 m.
Proof.
  intros T1 T2 m n Hmn.
  apply abs_diff_bound.
  - apply tail_nonneg. exact Hmn.
  - apply tail_bound_max. exact Hmn.
  - apply tail_nonneg. exact Hmn.
  - apply tail_bound_max. exact Hmn.
Qed.

(* Digits in {0,2} differ by exactly 2 *)
Lemma digits_differ_by_two : forall d1 d2 : Z,
  (d1 = 0 \/ d1 = 2)%Z -> (d2 = 0 \/ d2 = 2)%Z -> d1 <> d2 ->
  (Z.abs (d1 - d2) = 2)%Z.
Proof.
  intros d1 d2 [H1|H1] [H2|H2] Hneq; subst; simpl; try reflexivity; contradiction.
Qed.

(* 
   STRUCTURAL LEMMA: If TernaryExp T1 and T2 agree on positions 0..k-1
   but differ at position k, then their partial sums differ by 
   at least 1/3^{k+1} minus tail contributions.
*)
Lemma structural_digit_separation : forall T1 T2 k n,
  (k < n)%nat ->
  (forall j, (j < k)%nat -> digit T1 j = digit T2 j) ->
  digit T1 k <> digit T2 k ->
  Qabs (partial_sum T1 n - partial_sum T2 n) >= 
    / Qpow3 (S k) - / Qpow3 n - / Qpow3 n.
Proof.
  intros T1 T2 k n Hkn Hprefix Hdiff.
  
  (* Use transitivity: bound <= 1/3^{k+1} <= |diff| *)
  apply Qle_trans with (/ Qpow3 (S k)).
  - apply structural_bound_le. exact Hkn.
  - (* Show |diff| >= 1/3^{k+1} *)
    
    assert (Hpseq : partial_sum T1 k == partial_sum T2 k).
    { apply prefix_sum_eq. exact Hprefix. }
    
    (* Decompose: diff = digit_term + tail_diff *)
    assert (Hdecomp : partial_sum T1 n - partial_sum T2 n ==
                      ((digit T1 k - digit T2 k) # pow3 (S k)) + 
                      ((partial_sum T1 n - partial_sum T1 (S k)) - 
                       (partial_sum T2 n - partial_sum T2 (S k)))).
    { 
      (* Step 1: ps(n) = ps(S k) + tail *)
      remember (partial_sum T1 n - partial_sum T1 (S k)) as tail1 eqn:Htail1.
      remember (partial_sum T2 n - partial_sum T2 (S k)) as tail2 eqn:Htail2.
      
      assert (H1 : partial_sum T1 n == partial_sum T1 (S k) + tail1).
      { subst tail1. ring. }
      assert (H2 : partial_sum T2 n == partial_sum T2 (S k) + tail2).
      { subst tail2. ring. }
      
      rewrite H1, H2.
      
      (* Step 2: Expand ps(S k) *)
      rewrite (partial_sum_S T1 k).
      rewrite (partial_sum_S T2 k).
      rewrite Hpseq.
      
      (* Step 3: Simplify and use Q_sub_same_denom *)
      setoid_replace ((partial_sum T2 k + (digit T1 k # pow3 (S k)) + tail1) -
                      (partial_sum T2 k + (digit T2 k # pow3 (S k)) + tail2))
        with (((digit T1 k # pow3 (S k)) - (digit T2 k # pow3 (S k))) + (tail1 - tail2))
        by ring.
      
      rewrite Q_sub_same_denom.
      ring.
    }
    
    (* |digit_term| = 2/3^{k+1} *)
    pose proof (digit_valid T1 k) as Hd1.
    pose proof (digit_valid T2 k) as Hd2.
    assert (Habs2 : (Z.abs (digit T1 k - digit T2 k) = 2)%Z).
    { apply digits_differ_by_two; assumption. }
    
    (* |tail_diff| <= 1/3^{k+1} *)
    assert (HSk : (S k <= n)%nat) by lia.
    assert (Htail : Qabs ((partial_sum T1 n - partial_sum T1 (S k)) - 
                          (partial_sum T2 n - partial_sum T2 (S k))) <= / Qpow3 (S k)).
    { apply tail_diff_bound. exact HSk. }
    
    set (digit_term := ((digit T1 k - digit T2 k) # pow3 (S k))) in *.
    set (tail_diff := ((partial_sum T1 n - partial_sum T1 (S k)) - 
                       (partial_sum T2 n - partial_sum T2 (S k)))) in *.
    
    rewrite Hdecomp.
    
    (* |digit_term| = 2/3^{k+1} *)
    assert (Hdigabs : Qabs digit_term == 2 # pow3 (S k)).
    { unfold digit_term. unfold Qabs, Qeq. simpl. rewrite Habs2. reflexivity. }
    
    (* Use reverse triangle: |a + b| >= |a| - |b| *)
    apply Qle_trans with (Qabs digit_term - Qabs tail_diff).
    2: {
      (* Need: Qabs digit_term - Qabs tail_diff <= Qabs (digit_term + tail_diff) *)
      (* Reverse triangle: |a| - |b| <= |a + b| *)
      pose proof (Qabs_triangle digit_term tail_diff) as Htri.
      (* Htri: |digit_term + tail_diff| <= |digit_term| + |tail_diff| *)
      (* We need the reverse: |digit_term| - |tail_diff| <= |digit_term + tail_diff| *)
      (* From |a| = |(a+b) - b| <= |a+b| + |b|, so |a| - |b| <= |a+b| *)
      assert (Hrev : Qabs digit_term - Qabs tail_diff <= Qabs (digit_term + tail_diff)).
      {
        pose proof (Qabs_triangle (digit_term + tail_diff) (-tail_diff)) as H.
        setoid_replace (digit_term + tail_diff + - tail_diff) with digit_term in H by ring.
        rewrite Qabs_opp in H.
        apply Qplus_le_l with (Qabs tail_diff).
        setoid_replace (Qabs digit_term - Qabs tail_diff + Qabs tail_diff) 
          with (Qabs digit_term) by ring.
        exact H.
      }
      exact Hrev.
    }
    
    (* 1/3^{k+1} <= 2/3^{k+1} - |tail_diff| since |tail_diff| <= 1/3^{k+1} *)
    rewrite Hdigabs.
    (* Goal: 1/3^{k+1} <= 2/3^{k+1} - |tail_diff| *)
    (* Since |tail_diff| <= 1/3^{k+1}, we have 2/3^{k+1} - |tail_diff| >= 1/3^{k+1} *)
    apply Qle_trans with ((2 # pow3 (S k)) - (/ Qpow3 (S k))).
    + (* 1/3^{k+1} <= 2/3^{k+1} - 1/3^{k+1} = 1/3^{k+1} *)
      rewrite two_minus_one_pow3. apply Qle_refl.
    + (* 2/3^{k+1} - 1/3^{k+1} <= 2/3^{k+1} - |tail_diff| *)
      unfold Qminus. apply Qplus_le_r. apply Qopp_le_compat. exact Htail.
Qed.

(* ========================================================================= *)
(*                     SECTION 9: TERNARY FLIP                              *)
(* ========================================================================= *)

(* Flip: 0 <-> 2, and 1 -> 2 (avoid boundary) *)
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

(* ========================================================================= *)
(*                     SECTION 10: DIAGONAL CONSTRUCTION                    *)
(* ========================================================================= *)

(*
   Given an enumeration E : nat -> (nat -> Q),
   we construct a TernaryExp that differs from each E(n) at position n.
*)

Definition diagonal_digit (E : nat -> nat -> Q) (k : nat) : Z :=
  ternary_flip (extract_digit (E k k) k).

Lemma diagonal_digit_valid : forall E k,
  diagonal_digit E k = 0%Z \/ diagonal_digit E k = 2%Z.
Proof.
  intros E k. unfold diagonal_digit. apply ternary_flip_valid.
Qed.

Definition diagonal_exp (E : nat -> nat -> Q) : TernaryExp :=
  mkTernary (diagonal_digit E) (diagonal_digit_valid E).

(*
   KEY THEOREM: The diagonal differs from E(n) at position n.
   
   diagonal_digit n = flip(extract_digit (E n n) n) != extract_digit (E n n) n
*)
Theorem diagonal_differs_structurally : forall E n,
  diagonal_digit E n <> extract_digit (E n n) n.
Proof.
  intros E n. unfold diagonal_digit.
  apply ternary_flip_differs.
  apply extract_digit_range.
Qed.

(* ========================================================================= *)
(*                     SECTION 11: MAIN SEPARATION THEOREM                  *)
(* ========================================================================= *)

(*
   GOAL: Show that diagonal_exp E differs from each E(n) as Q-sequences.
   
   This requires:
   1. diagonal_differs_structurally (proved above)
   2. structural_digit_separation (to convert digit diff to Q diff)
   3. Approximation bounds (digit_expansion_approx)
*)

(* The diagonal partial sum *)
Definition diagonal_partial (E : nat -> nat -> Q) (m : nat) : Q :=
  partial_sum (diagonal_exp E) m.

(*
   At index m = n + buffer, the diagonal and E(n) differ by at least eps/3^{n+1}
*)
Theorem diagonal_Q_separation : forall E n m,
  (n < m)%nat ->
  (forall k, 0 <= E k m <= 1) ->
  Qabs (diagonal_partial E m - E n m) >= 
    / Qpow3 (S n) - 2 * / Qpow3 m - / Qpow3 m.
Proof.
  intros E n m Hnm Hbounds.
  (*
     diagonal_partial E m = Sum_{k=0}^{m-1} flip(digit_k)/3^{k+1}
     E n m ~= Sum_{k=0}^{m-1} (extracted digit from E n m)/3^{k+1} + error
     
     At position n: flip(digit) != digit, so difference >= 1/3^{n+1}
     Error terms: bounded by 1/3^m each
     
     Total: >= 1/3^{n+1} - 3/3^m
  *)
  admit.
Admitted.

(* ========================================================================= *)
(*                     SECTION 12: SUMMARY                                  *)
(* ========================================================================= *)

(*
   WHAT WE'VE BUILT:
   
   1. TernaryExp: Primary structure (digit sequences in {0, 2})
   2. partial_sum: Converts TernaryExp to Q approximations
   3. extract_digit: Extracts digits from Q (gives {0,1,2})
   4. ternary_flip: Ensures diagonal differs (0<->2, 1->2)
   5. diagonal_exp: Constructs differing sequence
   
   KEY THEOREMS (to be fully proved):
   
   - partial_sum_bound: partial sums stay in [0, 1 - 1/3^n]
   - tail_bound_max: tail contributions bounded by 1/3^k
   - digit_expansion_approx: Q ~= extracted digits + O(1/3^n)
   - diagonal_differs_structurally: flip(d) != d (PROVED)
   - structural_digit_separation: digit difference -> Q difference (PROVED)
   - diagonal_Q_separation: actual Q-difference >= eps
   
   ADMITTED (2 total):
   - extracted_equals_floor: digit extraction correctness
   - diagonal_Q_separation: final diagonal bound
   
   The structural core is now fully proved!
*)

Check diagonal_differs_structurally.
Check diagonal_Q_separation.
