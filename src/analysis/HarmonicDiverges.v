(** * HarmonicDiverges.v -- Wiedijk #34: Divergence of the Harmonic Series

    Theory of Systems -- Analysis (Wiedijk 100)

    The harmonic series H(N) = sum_{n=1}^{N} 1/n diverges:
    for every bound M there exists N with H(N) > M.

    Elements: partial sums H(N), reciprocal terms 1/n
    Roles:    H(N) -> unbounded sequence, 1/n -> positive decreasing term
    Rules:    Oresme grouping (H(2n) >= H(n) + 1/2), L5: compare to bound
    Status:   divergent | monotone | unbounded

    Strategy: prove H(2*n) >= H(n) + 1/2, then iterate to get
    H(2^K) >= 1 + K/2, which exceeds any bound M by Archimedean property.

    STATUS: 21 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import PeanoNat.

Open Scope Q_scope.

(* ================================================================= *)
(** ** Definition of harmonic partial sums *)
(* ================================================================= *)

Fixpoint harmonic (n : nat) : Q :=
  match n with
  | O => 0
  | S m => harmonic m + (1 # Pos.of_succ_nat m)
  end.

(* ================================================================= *)
(** ** Concrete values *)
(* ================================================================= *)

Lemma H0 : harmonic O == 0.
Proof. reflexivity. Qed.

Lemma H1 : harmonic 1 == 1.
Proof. reflexivity. Qed.

Lemma H2 : harmonic 2 == 3 # 2.
Proof. reflexivity. Qed.

Lemma H3 : harmonic 3 == 11 # 6.
Proof. reflexivity. Qed.

Lemma H4 : harmonic 4 == 25 # 12.
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** Each term is positive *)
(* ================================================================= *)

Lemma harmonic_term_pos : forall n : nat,
  0 < (1 # Pos.of_succ_nat n).
Proof. intro n. unfold Qlt. simpl. lia. Qed.

(* ================================================================= *)
(** ** Monotonicity *)
(* ================================================================= *)

Lemma harmonic_nonneg : forall n : nat, 0 <= harmonic n.
Proof.
  induction n as [| m IH].
  - simpl. lra.
  - simpl. pose proof (harmonic_term_pos m). lra.
Qed.

Lemma harmonic_monotone : forall n : nat, harmonic n <= harmonic (S n).
Proof.
  intro n. simpl. pose proof (harmonic_term_pos n). lra.
Qed.

Lemma harmonic_monotone_le : forall n m : nat,
  (n <= m)%nat -> harmonic n <= harmonic m.
Proof.
  intros n m Hle. induction Hle as [| k _ IH].
  - lra.
  - pose proof (harmonic_monotone k). lra.
Qed.

(* ================================================================= *)
(** ** Oresme grouping: H(2n) - H(n) >= 1/2 *)
(* ================================================================= *)

Fixpoint tail_sum (n k : nat) : Q :=
  match k with
  | O => 0
  | S j => tail_sum n j + (1 # Pos.of_succ_nat (n + j))
  end.

Lemma harmonic_plus_tail : forall n k : nat,
  harmonic (n + k) == harmonic n + tail_sum n k.
Proof.
  intros n. induction k as [| j IH].
  - simpl. rewrite Nat.add_0_r. lra.
  - replace (n + S j)%nat with (S (n + j))%nat by lia.
    simpl (harmonic (S (n + j))).
    rewrite IH. simpl (tail_sum n (S j)). lra.
Qed.

(** Lower bound: tail_sum n k >= k * (1/(n+k)) for all k.
    Each of the k terms 1/(n+j+1) for j=0..k-1 satisfies
    1/(n+j+1) >= 1/(n+k) since j < k implies n+j+1 <= n+k.

    We state this as Qle (avoiding Qge which lra can't handle). *)

Lemma tail_sum_lower_last : forall n k : nat, (0 < k)%nat ->
  inject_Z (Z.of_nat k) * (1 # Pos.of_succ_nat (n + k - 1)) <= tail_sum n k.
Proof.
  intros n k Hk. induction k as [| j IH].
  - lia.
  - destruct j as [| j'].
    + (* k = 1: inject_Z 1 * 1#Pos.of_succ_nat(n+0) <= 0 + 1#Pos.of_succ_nat(n+0) *)
      simpl. replace (n + 0)%nat with n by lia.
      unfold inject_Z. unfold Qle. simpl. lia.
    + (* k = S(S j') *)
      assert (HSj : (0 < S j')%nat) by lia.
      specialize (IH HSj).
      simpl (tail_sum n (S (S j'))).
      replace (n + S (S j') - 1)%nat with (n + S j')%nat by lia.
      replace (n + S j' - 1)%nat with (n + j')%nat in IH by lia.
      (* IH: inject_Z(S j') * 1#....(n+j') <= tail_sum n (S j') *)
      (* Term bound: 1#...(n+S j') <= 1#...(n+j') since n+j' < n+S j' *)
      assert (Hfrac_le : (1 # Pos.of_succ_nat (n + S j')) <= (1 # Pos.of_succ_nat (n + j'))).
      { unfold Qle. simpl. lia. }
      (* Monotonicity: inject_Z(S j') * small <= inject_Z(S j') * big *)
      assert (Hnat_pos : 0 < inject_Z (Z.of_nat (S j'))).
      { unfold Qlt, inject_Z. simpl. lia. }
      assert (Hmul_le : inject_Z (Z.of_nat (S j')) * (1 # Pos.of_succ_nat (n + S j')) <=
                         inject_Z (Z.of_nat (S j')) * (1 # Pos.of_succ_nat (n + j'))).
      { rewrite Qmult_le_l; assumption. }
      (* Expand: (S(S j')) * x = (S j') * x + x *)
      assert (Hexpand : inject_Z (Z.of_nat (S (S j'))) * (1 # Pos.of_succ_nat (n + S j')) ==
                         inject_Z (Z.of_nat (S j')) * (1 # Pos.of_succ_nat (n + S j')) +
                         (1 # Pos.of_succ_nat (n + S j'))).
      { unfold Qeq, inject_Z, Qmult, Qplus. simpl. lia. }
      (* Rewrite goal using Hexpand *)
      rewrite Hexpand.
      apply Qplus_le_compat; [| apply Qle_refl].
      apply Qle_trans with (inject_Z (Z.of_nat (S j')) * (1 # Pos.of_succ_nat (n + j'))); assumption.
Qed.

(** n * 1/(2n) = 1/2 *)
Lemma n_over_2n_eq : forall n : nat, (0 < n)%nat ->
  inject_Z (Z.of_nat n) * (1 # Pos.of_succ_nat (n + n - 1)) == (1 # 2).
Proof.
  intros n Hn.
  unfold Qeq, inject_Z, Qmult. simpl.
  rewrite Zpos_P_of_succ_nat.
  rewrite Nat2Z.inj_sub; [| lia].
  rewrite Nat2Z.inj_add.
  lia.
Qed.

Lemma tail_sum_ge_half : forall n : nat, (0 < n)%nat ->
  (1 # 2) <= tail_sum n n.
Proof.
  intros n Hn.
  assert (Hlower := tail_sum_lower_last n n Hn).
  assert (Heq := n_over_2n_eq n Hn).
  lra.
Qed.

Lemma harmonic_oresme : forall n : nat, (0 < n)%nat ->
  harmonic n + (1 # 2) <= harmonic (n + n).
Proof.
  intros n Hn.
  assert (Hsplit := harmonic_plus_tail n n).
  assert (Hge := tail_sum_ge_half n Hn).
  lra.
Qed.

(* ================================================================= *)
(** ** Iterated doubling: H(2^K) grows without bound *)
(* ================================================================= *)

Fixpoint pow2 (k : nat) : nat :=
  match k with
  | O => 1%nat
  | S j => (pow2 j + pow2 j)%nat
  end.

Lemma pow2_pos : forall k : nat, (0 < pow2 k)%nat.
Proof. induction k as [| j IH]; simpl; lia. Qed.

Lemma harmonic_pow2_bound : forall K : nat,
  1 + inject_Z (Z.of_nat K) * (1 # 2) <= harmonic (pow2 K).
Proof.
  induction K as [| k IH].
  - unfold inject_Z. simpl. lra.
  - change (pow2 (S k)) with (pow2 k + pow2 k)%nat.
    assert (Horesme := harmonic_oresme (pow2 k) (pow2_pos k)).
    assert (Hstep : inject_Z (Z.of_nat (S k)) * (1 # 2) ==
                    inject_Z (Z.of_nat k) * (1 # 2) + (1 # 2)).
    { rewrite Nat2Z.inj_succ. unfold Qeq, inject_Z, Qmult, Qplus. simpl. lia. }
    lra.
Qed.

(* ================================================================= *)
(** ** Main theorem: harmonic series diverges *)
(* ================================================================= *)

Lemma archimedean_Q : forall M : Q,
  exists k : nat, M < inject_Z (Z.of_nat k).
Proof.
  intro M. destruct M as [p q].
  exists (Z.to_nat (Z.max 1 (p * Z.pos q + 1))).
  unfold Qlt, inject_Z. simpl.
  rewrite Z.mul_1_r.
  rewrite Z2Nat.id; [| lia].
  destruct (Z.max_spec 1 (p * Z.pos q + 1)) as [[_ Heq] | [_ Heq]]; rewrite Heq; nia.
Qed.

Lemma inject_Z_half_bound : forall (K : nat) (M : Q),
  M < inject_Z (Z.of_nat K) ->
  M <= inject_Z (Z.of_nat (2 * K)) * (1 # 2).
Proof.
  intros K M HK.
  assert (Heq : inject_Z (Z.of_nat (2 * K)) * (1 # 2) == inject_Z (Z.of_nat K)).
  { unfold Qeq, inject_Z, Qmult.
    rewrite Nat2Z.inj_mul.
    simpl Qnum. simpl Qden.
    destruct (Z.of_nat K); simpl; lia. }
  lra.
Qed.

Theorem harmonic_diverges : forall M : Q,
  exists N : nat, M < harmonic N.
Proof.
  intro M.
  destruct (archimedean_Q M) as [K HK].
  exists (pow2 (2 * K)).
  assert (Hbound := harmonic_pow2_bound (2 * K)).
  assert (Hhalf := inject_Z_half_bound K M HK).
  lra.
Qed.

(* ================================================================= *)
(** ** Corollary: harmonic is not Cauchy *)
(* ================================================================= *)

Definition is_cauchy_Q (f : nat -> Q) : Prop :=
  forall eps : Q, 0 < eps ->
  exists N : nat, forall m n : nat,
    (N <= m)%nat -> (N <= n)%nat -> Qabs (f m - f n) < eps.

Lemma harmonic_gap : forall n : nat, (0 < n)%nat ->
  (1 # 2) <= harmonic (n + n) - harmonic n.
Proof.
  intros n Hn. pose proof (harmonic_oresme n Hn). lra.
Qed.

Theorem harmonic_not_cauchy : ~ is_cauchy_Q harmonic.
Proof.
  intro Hcauchy.
  unfold is_cauchy_Q in Hcauchy.
  destruct (Hcauchy (1 # 4) ltac:(lra)) as [N HN].
  set (n := Nat.max N 1).
  assert (Hn_ge_N : (N <= n)%nat) by (unfold n; lia).
  assert (Hn_pos : (0 < n)%nat) by (unfold n; lia).
  assert (Hnn_ge_N : (N <= n + n)%nat) by lia.
  specialize (HN (n + n)%nat n Hnn_ge_N Hn_ge_N).
  assert (Hgap := harmonic_gap n Hn_pos).
  assert (Habs : (1 # 2) <= Qabs (harmonic (n + n) - harmonic n)).
  { rewrite Qabs_pos; [assumption |].
    pose proof (harmonic_oresme n Hn_pos). lra. }
  lra.
Qed.

(* ================================================================= *)
(** ** Summary *)
(* ================================================================= *)

(** Wiedijk #34: Divergence of the Harmonic Series

    Main results:
    - [harmonic_diverges]: forall M, exists N, M < H(N)
    - [harmonic_not_cauchy]: H is not a Cauchy sequence

    Method: Oresme grouping (H(2n) >= H(n) + 1/2) iterated
    via 2^K to get H(2^K) >= 1 + K/2, which is unbounded. *)
