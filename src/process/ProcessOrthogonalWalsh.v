(** * ProcessOrthogonalWalsh.v -- Orthogonal systems without normalisation and the Walsh system, as a ToS System

    Elements: vectors with N rational coordinates; a family e of vectors; the
              squared norms d_k > 0 of its first K0 vectors; the +-1 rows
              [had k i] of the Hadamard matrix of size N = 2^k; finite sums.
    Roles:    orthogonal system  -- the first K0 vectors of e are pairwise
                                    orthogonal, <e_k, e_k> = d_k (no vector
                                    is divided by a root);
              [og_coef k]        -- the Fourier coefficient <e_k, f> / d_k;
              partial sum P_K    -- Sum_{k<K} og_coef k * e_k;
              [walsh_n k s]      -- the Walsh rows divided by a rational s
                                    with s^2 = N, when such an s is given.
    Rules:    the theory of an orthonormal system holds for an orthogonal one
              with the weights d_k: residual identity, Bessel, best
              approximation with uniqueness, Parseval as the criterion of
              completeness. The observable quantities contain d_k = N, never
              sqrt N.

    Proved (no axioms):
      - for an orthogonal system, K <= K0: [proj_ortho_og], [proj_coord_og],
        [gen_resid_og], [resid_ortho_og], [resid_norm_og], [bessel_og],
        [best_approx_eq_og], [best_approx_og], [best_approx_unique_og],
        [parseval_iff_complete_og]; the orthonormal case is d = 1
        ([on_is_og]);
      - the Walsh rows for EVERY N = 2^k ([walsh_og]): [walsh_bessel],
        [walsh_best_approx], [walsh_parseval_divided], [walsh_complete],
        [walsh_coef_is_transform], [walsh_rows_distinct];
      - the normalised Walsh system, given a rational s with s^2 = N:
        [walsh_normalized_on], [walsh_normalized_bessel],
        [walsh_normalized_parseval], [walsh_normalized_complete];
      - such an s exists exactly for even k
        ([walsh_rational_norm_iff_even]): for N = 4^j the rows divided by
        2^j are orthonormal ([walsh_4j_orthonormal], [walsh_4_orthonormal]);
        for odd k there is none ([walsh_odd_no_rational_norm],
        [walsh_2_no_rational_norm]).

    P4 diagnostic: all sums are finite. Nothing is divided by a root: where
      the classical text normalises by 1 / sqrt N, the coefficient is divided
      by the rational d_k = N. The root sqrt N for odd k is a process and is
      not used; the statement that it is not a rational number is a theorem.

    NOT claimed:
      - an orthonormal Walsh system over Q for odd k;
      - the root sqrt N as a number (ProcessHadamardGate.v takes it as a
        rational parameter, which has no instance for N = 2);
      - sequency ordering of the rows;
      - anything about infinitely many coordinates.

    STATUS: 32 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa Bool PeanoNat Arith.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.
From ToS Require Import process.ProcessFubiniGeneral.
From ToS Require Import process.ProcessCompactSpectral.
From ToS Require Import process.ProcessL2CauchySchwarz.
From ToS Require Import process.ProcessL2Bessel.
From ToS Require Import process.ProcessL2BesselGeneral.
From ToS Require Import process.ProcessL2Parseval.
From ToS Require Import process.ProcessDCT.
From ToS Require Import process.ProcessPositionMomentum.
From ToS Require Import process.ProcessSelfAdjointSpectral.
From ToS Require Import process.ProcessWalshHadamard.
From ToS Require Import process.ProcessFourierON.
From ToS Require Import process.ProcessL2Orthonormal.
From ToS Require Import process.ProcessOrthonormalFourier.
From ToS Require analysis.Sqrt2Irrational.

Open Scope Q_scope.

(* ===================================================================== *)
(*  1. The size N = 2^k as a positive rational                          *)
(* ===================================================================== *)

Lemma pow2_Q_pos : forall k, 0 < inject_Z (Z.of_nat (pow2 k)).
Proof.
  intro k.
  assert (H : inject_Z 0 < inject_Z (Z.of_nat (pow2 k))).
  { rewrite <- Zlt_Qlt. pose proof (pow2_pos k). lia. }
  exact H.
Qed.

Lemma pow2_Q_neq0 : forall k, ~ inject_Z (Z.of_nat (pow2 k)) == 0.
Proof.
  intros k E. pose proof (pow2_Q_pos k) as H. rewrite E in H.
  exact (Qlt_irrefl 0 H).
Qed.

(* ===================================================================== *)
(*  2. Orthogonal systems: the same theory with no root                 *)
(* ===================================================================== *)

Section OrthogonalSystem.

(** The first K0 vectors of e are pairwise orthogonal on N coordinates,
    with squared norms d k > 0; no vector is normalised. *)
Variable e : nat -> nat -> Q.
Variable N K0 : nat.
Variable d : nat -> Q.
Hypothesis Hd : forall k, (k < K0)%nat -> 0 < d k.
Hypothesis Hog : forall i j, (i < K0)%nat -> (j < K0)%nat ->
  seq_inner (e i) (e j) N == (if Nat.eqb i j then d i else 0).

(** The vector number K is orthogonal to the combinations of the first K. *)
Lemma proj_ortho_og : forall (coef : nat -> Q) (K : nat), (K < K0)%nat ->
  seq_inner (e K) (fun m => q_sum (fun k => coef k * e k m) K) N == 0.
Proof.
  intros coef K HK.
  rewrite (inner_proj_swap e coef (e K) K N).
  apply q_sum_zero_bounded. intros k Hk.
  rewrite (Hog K k HK ltac:(lia)).
  assert (Hneq : Nat.eqb K k = false) by (apply Nat.eqb_neq; lia).
  rewrite Hneq. ring.
Qed.

(** <e_j, Sum_{k<K} coef_k e_k> = d_j coef_j for j < K <= K0. *)
Lemma proj_coord_og : forall (coef : nat -> Q) (j K : nat),
  (j < K)%nat -> (K <= K0)%nat ->
  seq_inner (e j) (fun m => q_sum (fun k => coef k * e k m) K) N == d j * coef j.
Proof.
  intros coef j K Hj HK.
  rewrite (inner_proj_swap e coef (e j) K N).
  transitivity (q_sum (fun k => (if (j =? k)%nat then d j else 0) * coef k) K).
  { apply q_sum_ext_bounded. intros k Hk.
    rewrite (Hog j k ltac:(lia) ltac:(lia)). ring. }
  exact (q_sum_delta (d j) coef j K Hj).
Qed.

Variable f : nat -> Q.

(** General residual identity for arbitrary coefficients a:
    ||f - Sum_{k<K} a_k e_k||^2 = ||f||^2 + Sum_{k<K} (d_k a_k^2 - 2 a_k <e_k,f>). *)
Lemma gen_resid_og : forall (a : nat -> Q) (K : nat), (K <= K0)%nat ->
  seq_inner (fun m => f m - q_sum (fun k => a k * e k m) K)
            (fun m => f m - q_sum (fun k => a k * e k m) K) N
  == seq_inner f f N
     + q_sum (fun k => d k * (a k * a k) - 2 * a k * seq_inner (e k) f N) K.
Proof.
  intros a K. induction K as [|K IH]; intro HK.
  - transitivity (seq_inner f f N).
    + apply seq_inner_ext; intro m; cbn [q_sum]; ring.
    + cbn [q_sum]; ring.
  - transitivity
      (seq_inner (fun m => (f m - q_sum (fun k => a k * e k m) K) - a K * e K m)
                 (fun m => (f m - q_sum (fun k => a k * e k m) K) - a K * e K m) N).
    + apply seq_inner_ext; intro m; cbn [q_sum]; ring.
    + rewrite (seq_inner_resid
                 (fun m => f m - q_sum (fun k => a k * e k m) K) (e K) (a K) N).
      rewrite (IH ltac:(lia)).
      rewrite (seq_inner_sub_r (e K) f (fun m => q_sum (fun k => a k * e k m) K) N).
      rewrite (proj_ortho_og a K ltac:(lia)).
      rewrite (Hog K K ltac:(lia) ltac:(lia)), Nat.eqb_refl.
      cbn [q_sum]. ring.
Qed.

(** The Fourier coefficient of an orthogonal system: <e_k, f> / d_k. *)
Definition og_coef (k : nat) : Q := seq_inner (e k) f N / d k.

Lemma og_weight_nz : forall k, (k < K0)%nat -> ~ d k == 0.
Proof. intros k Hk H0. pose proof (Hd k Hk) as H. rewrite H0 in H. lra. Qed.

(** The residual is orthogonal to every direction already taken. *)
Theorem resid_ortho_og : forall (j K : nat), (j < K)%nat -> (K <= K0)%nat ->
  seq_inner (e j) (fun m => f m - q_sum (fun k => og_coef k * e k m) K) N == 0.
Proof.
  intros j K Hj HK.
  rewrite (seq_inner_sub_r (e j) f (fun m => q_sum (fun k => og_coef k * e k m) K) N).
  rewrite (proj_coord_og og_coef j K Hj HK).
  unfold og_coef. field. apply og_weight_nz. lia.
Qed.

(** Residual identity: ||f - P_K||^2 = ||f||^2 - Sum_{k<K} <e_k,f>^2 / d_k. *)
Lemma resid_norm_og : forall K, (K <= K0)%nat ->
  seq_inner (fun m => f m - q_sum (fun k => og_coef k * e k m) K)
            (fun m => f m - q_sum (fun k => og_coef k * e k m) K) N
  == seq_inner f f N
     - q_sum (fun k => seq_inner (e k) f N * seq_inner (e k) f N / d k) K.
Proof.
  intros K HK. rewrite (gen_resid_og og_coef K HK).
  assert (E : q_sum (fun k => d k * (og_coef k * og_coef k) - 2 * og_coef k * seq_inner (e k) f N) K
              == q_sum (fun k => (- (1)) * (seq_inner (e k) f N * seq_inner (e k) f N / d k)) K).
  { apply q_sum_ext_bounded. intros k Hk. unfold og_coef. field.
    apply og_weight_nz. lia. }
  rewrite E, q_sum_scale. ring.
Qed.

(** Bessel for an orthogonal system: Sum_{k<K} <e_k,f>^2 / d_k <= ||f||^2. *)
Theorem bessel_og : forall K, (K <= K0)%nat ->
  q_sum (fun k => seq_inner (e k) f N * seq_inner (e k) f N / d k) K <= seq_inner f f N.
Proof.
  intros K HK. pose proof (resid_norm_og K HK) as Hrn.
  assert (Hnn : 0 <= seq_inner (fun m => f m - q_sum (fun k => og_coef k * e k m) K)
                               (fun m => f m - q_sum (fun k => og_coef k * e k m) K) N).
  { unfold seq_inner. apply q_sum_nonneg. intro i. apply q_sq_nonneg. }
  rewrite Hrn in Hnn. lra.
Qed.

(** Best-approximation identity:
    ||f - Sum a_k e_k||^2 = ||f - P_K||^2 + Sum_{k<K} d_k (a_k - c_k)^2. *)
Theorem best_approx_eq_og : forall (a : nat -> Q) (K : nat), (K <= K0)%nat ->
  seq_inner (fun m => f m - q_sum (fun k => a k * e k m) K)
            (fun m => f m - q_sum (fun k => a k * e k m) K) N
  == seq_inner (fun m => f m - q_sum (fun k => og_coef k * e k m) K)
               (fun m => f m - q_sum (fun k => og_coef k * e k m) K) N
     + q_sum (fun k => d k * ((a k - og_coef k) * (a k - og_coef k))) K.
Proof.
  intros a K HK.
  rewrite (gen_resid_og a K HK), (gen_resid_og og_coef K HK).
  rewrite <- Qplus_assoc. apply Qplus_comp; [ reflexivity | ].
  rewrite <- q_sum_plus. apply q_sum_ext_bounded. intros k Hk.
  unfold og_coef. field. apply og_weight_nz. lia.
Qed.

Corollary best_approx_og : forall (a : nat -> Q) (K : nat), (K <= K0)%nat ->
  seq_inner (fun m => f m - q_sum (fun k => og_coef k * e k m) K)
            (fun m => f m - q_sum (fun k => og_coef k * e k m) K) N
  <= seq_inner (fun m => f m - q_sum (fun k => a k * e k m) K)
               (fun m => f m - q_sum (fun k => a k * e k m) K) N.
Proof.
  intros a K HK. rewrite (best_approx_eq_og a K HK).
  assert (Hnn : 0 <= q_sum (fun k => d k * ((a k - og_coef k) * (a k - og_coef k))) K).
  { apply Qle_trans with (q_sum (fun _ : nat => 0) K).
    - rewrite q_sum_zero. lra.
    - apply q_sum_le_bounded. intros k Hk.
      apply Qmult_le_0_compat; [ apply Qlt_le_weak; apply Hd; lia | apply q_sq_nonneg ]. }
  lra.
Qed.

(** The minimum is attained exactly at the coefficients <e_k, f> / d_k. *)
Theorem best_approx_unique_og : forall (a : nat -> Q) (K : nat), (K <= K0)%nat ->
  (seq_inner (fun m => f m - q_sum (fun k => a k * e k m) K)
             (fun m => f m - q_sum (fun k => a k * e k m) K) N
   == seq_inner (fun m => f m - q_sum (fun k => og_coef k * e k m) K)
                (fun m => f m - q_sum (fun k => og_coef k * e k m) K) N)
  <-> (forall k, (k < K)%nat -> a k == og_coef k).
Proof.
  intros a K HK. pose proof (best_approx_eq_og a K HK) as Hba. split.
  - intros Heq k Hk.
    assert (Hz : q_sum (fun k => d k * ((a k - og_coef k) * (a k - og_coef k))) K == 0)
      by lra.
    assert (Hnn : forall i, (i < K)%nat ->
              0 <= d i * ((a i - og_coef i) * (a i - og_coef i))).
    { intros i Hi.
      apply Qmult_le_0_compat; [ apply Qlt_le_weak; apply Hd; lia | apply q_sq_nonneg ]. }
    pose proof (q_sum_nonneg_zero_bounded
                  (fun k => d k * ((a k - og_coef k) * (a k - og_coef k))) K Hnn Hz k Hk)
      as Hk0.
    cbv beta in Hk0.
    assert (Hdk : 0 < d k) by (apply Hd; lia).
    assert (Hsq : (a k - og_coef k) * (a k - og_coef k) == 0).
    { destruct (Qmult_integral _ _ Hk0) as [H0 | H0]; [ lra | exact H0 ]. }
    destruct (Qmult_integral _ _ Hsq) as [H0 | H0]; lra.
  - intro Hall.
    assert (Hz : q_sum (fun k => d k * ((a k - og_coef k) * (a k - og_coef k))) K == 0).
    { apply q_sum_zero_bounded. intros k Hk. cbv beta. rewrite (Hall k Hk). ring. }
    lra.
Qed.

(** Parseval as a finite criterion of completeness, orthogonal form. *)
Theorem parseval_iff_complete_og : forall K, (K <= K0)%nat ->
  (q_sum (fun k => seq_inner (e k) f N * seq_inner (e k) f N / d k) K == seq_inner f f N)
  <-> (forall m, (m < N)%nat -> q_sum (fun k => og_coef k * e k m) K == f m).
Proof.
  intros K HK. pose proof (resid_norm_og K HK) as Hrn. split.
  - intros Hp m Hm.
    assert (Hz : seq_inner (fun m => f m - q_sum (fun k => og_coef k * e k m) K)
                           (fun m => f m - q_sum (fun k => og_coef k * e k m) K) N == 0)
      by lra.
    pose proof (q_sum_sq_zero (fun m => f m - q_sum (fun k => og_coef k * e k m) K)
                  N Hz m Hm) as Hgm.
    cbv beta in Hgm. lra.
  - intros Hc.
    assert (Hz : seq_inner (fun m => f m - q_sum (fun k => og_coef k * e k m) K)
                           (fun m => f m - q_sum (fun k => og_coef k * e k m) K) N == 0).
    { apply seq_inner_self_zero_of_coords. intros i Hi. cbv beta.
      rewrite (Hc i Hi). ring. }
    lra.
Qed.

End OrthogonalSystem.

(** The orthonormal case is the case d = 1. *)
Lemma on_is_og : forall (e : nat -> nat -> Q) (N K0 : nat),
  (forall i j, (i < K0)%nat -> (j < K0)%nat ->
     seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0)) ->
  forall i j, (i < K0)%nat -> (j < K0)%nat ->
     seq_inner (e i) (e j) N == (if Nat.eqb i j then (fun _ : nat => 1) i else 0).
Proof. intros e N K0 H i j Hi Hj. exact (H i j Hi Hj). Qed.

(* ===================================================================== *)
(*  3. The Walsh rows: an orthogonal system for every N = 2^k           *)
(* ===================================================================== *)

(** d = N, K0 = N; no root, no parameter. *)
Lemma walsh_og : forall k i j, (i < pow2 k)%nat -> (j < pow2 k)%nat ->
  seq_inner (had k i) (had k j) (pow2 k)
  == (if Nat.eqb i j then inject_Z (Z.of_nat (pow2 k)) else 0).
Proof. intros k i j Hi Hj. unfold seq_inner. exact (hadamard_orthogonal k i j Hi Hj). Qed.

(** The pairing <H_i, f> is the i-th coordinate of the transform Hf. *)
Lemma walsh_coef_is_transform : forall k (f : nat -> Q) (i : nat),
  seq_inner (had k i) f (pow2 k) = op_apply (had k) f (pow2 k) i.
Proof. reflexivity. Qed.

(** Bessel for the Walsh system, every k, every K <= N. *)
Theorem walsh_bessel : forall (k : nat) (f : nat -> Q) (K : nat), (K <= pow2 k)%nat ->
  q_sum (fun i => seq_inner (had k i) f (pow2 k) * seq_inner (had k i) f (pow2 k)
                  / inject_Z (Z.of_nat (pow2 k))) K
  <= seq_inner f f (pow2 k).
Proof.
  intros k f K HK.
  exact (bessel_og (had k) (pow2 k) (pow2 k) (fun _ => inject_Z (Z.of_nat (pow2 k)))
           (fun _ _ => pow2_Q_pos k) (walsh_og k) f K HK).
Qed.

(** The Walsh partial sum with the coefficients <H_i, f> / N is the best
    approximation among all combinations of the first K Walsh rows. *)
Theorem walsh_best_approx : forall (k : nat) (f a : nat -> Q) (K : nat), (K <= pow2 k)%nat ->
  seq_inner (fun m => f m - q_sum (fun i => seq_inner (had k i) f (pow2 k)
                                            / inject_Z (Z.of_nat (pow2 k)) * had k i m) K)
            (fun m => f m - q_sum (fun i => seq_inner (had k i) f (pow2 k)
                                            / inject_Z (Z.of_nat (pow2 k)) * had k i m) K)
            (pow2 k)
  <= seq_inner (fun m => f m - q_sum (fun i => a i * had k i m) K)
               (fun m => f m - q_sum (fun i => a i * had k i m) K) (pow2 k).
Proof.
  intros k f a K HK.
  exact (best_approx_og (had k) (pow2 k) (pow2 k) (fun _ => inject_Z (Z.of_nat (pow2 k)))
           (fun _ _ => pow2_Q_pos k) (walsh_og k) f a K HK).
Qed.

(** Parseval in the divided form, every k: Sum_{i<N} <H_i,f>^2 / N = ||f||^2. *)
Theorem walsh_parseval_divided : forall (k : nat) (f : nat -> Q),
  q_sum (fun i => seq_inner (had k i) f (pow2 k) * seq_inner (had k i) f (pow2 k)
                  / inject_Z (Z.of_nat (pow2 k))) (pow2 k)
  == seq_inner f f (pow2 k).
Proof.
  intros k f. pose proof (pow2_Q_pos k) as HN.
  transitivity (q_sum (fun i => / inject_Z (Z.of_nat (pow2 k))
                                * (op_apply (had k) f (pow2 k) i
                                   * op_apply (had k) f (pow2 k) i)) (pow2 k)).
  { apply q_sum_ext. intro i. unfold seq_inner, op_apply. field. lra. }
  rewrite q_sum_scale.
  pose proof (parseval_walsh k f) as HP. unfold seq_inner in HP. unfold seq_inner.
  rewrite HP. field. lra.
Qed.

(** Completeness on N coordinates, every k:
    f(m) = Sum_{i<N} (<H_i,f> / N) H_i(m). *)
Theorem walsh_complete : forall (k : nat) (f : nat -> Q) (m : nat), (m < pow2 k)%nat ->
  q_sum (fun i => seq_inner (had k i) f (pow2 k) / inject_Z (Z.of_nat (pow2 k)) * had k i m)
        (pow2 k) == f m.
Proof.
  intros k f.
  exact (proj1 (parseval_iff_complete_og (had k) (pow2 k) (pow2 k)
                  (fun _ => inject_Z (Z.of_nat (pow2 k)))
                  (fun _ _ => pow2_Q_pos k) (walsh_og k) f (pow2 k) (le_n (pow2 k)))
               (walsh_parseval_divided k f)).
Qed.

(** Different rows are different functions on {0..N-1}: the N characters
    are pairwise distinct. *)
Theorem walsh_rows_distinct : forall k i i', (i < pow2 k)%nat -> (i' < pow2 k)%nat ->
  i <> i' -> ~ (forall j, (j < pow2 k)%nat -> had k i j == had k i' j).
Proof.
  intros k i i' Hi Hi' Hne Hall.
  pose proof (hadamard_orthogonal k i i' Hi Hi') as Ho.
  assert (Hneq : Nat.eqb i i' = false) by (apply Nat.eqb_neq; exact Hne).
  rewrite Hneq in Ho.
  assert (Hn : q_sum (fun j => had k i j * had k i' j) (pow2 k)
               == inject_Z (Z.of_nat (pow2 k))).
  { transitivity (q_sum (fun j => had k i j * had k i j) (pow2 k)).
    - apply q_sum_ext_bounded. intros j Hj. rewrite (Hall j Hj). reflexivity.
    - apply walsh_norm. }
  rewrite Hn in Ho. exact (pow2_Q_neq0 k Ho).
Qed.

(* ===================================================================== *)
(*  4. The normalised Walsh system: exactly for even k                  *)
(* ===================================================================== *)

Definition walsh_n (k : nat) (s : Q) : nat -> nat -> Q := fun i m => had k i m / s.

(** If a rational s with s^2 = N is given, the rows H_i / s (i < N) are
    orthonormal on N = 2^k coordinates: the premise of ProcessL2Orthonormal.v
    with K0 = N. *)
Theorem walsh_normalized_on : forall (k : nat) (s : Q),
  s * s == inject_Z (Z.of_nat (pow2 k)) ->
  forall i j, (i < pow2 k)%nat -> (j < pow2 k)%nat ->
  seq_inner (walsh_n k s i) (walsh_n k s j) (pow2 k) == (if Nat.eqb i j then 1 else 0).
Proof.
  intros k s Hs i j Hi Hj.
  pose proof (pow2_Q_pos k) as HN.
  assert (Hs0 : ~ s == 0).
  { intro H0. rewrite H0 in Hs. lra. }
  unfold seq_inner, walsh_n.
  transitivity (q_sum (fun m => / (s * s) * (had k i m * had k j m)) (pow2 k)).
  { apply q_sum_ext. intro m. field. exact Hs0. }
  rewrite q_sum_scale. rewrite (hadamard_orthogonal k i j Hi Hj).
  destruct (Nat.eqb i j).
  - rewrite Hs. field. lra.
  - ring.
Qed.

Corollary walsh_normalized_bessel : forall (k : nat) (s : Q),
  s * s == inject_Z (Z.of_nat (pow2 k)) ->
  forall (f : nat -> Q) (K : nat), (K <= pow2 k)%nat ->
  q_sum (fun i => seq_inner (walsh_n k s i) f (pow2 k)
                  * seq_inner (walsh_n k s i) f (pow2 k)) K
  <= seq_inner f f (pow2 k).
Proof.
  intros k s Hs f K HK.
  exact (bessel_b (walsh_n k s) (pow2 k) (pow2 k) (walsh_normalized_on k s Hs) f K HK).
Qed.

(** Parseval's equality for the normalised Walsh system. *)
Theorem walsh_normalized_parseval : forall (k : nat) (s : Q),
  s * s == inject_Z (Z.of_nat (pow2 k)) ->
  forall f : nat -> Q,
  q_sum (fun i => seq_inner (walsh_n k s i) f (pow2 k)
                  * seq_inner (walsh_n k s i) f (pow2 k)) (pow2 k)
  == seq_inner f f (pow2 k).
Proof.
  intros k s Hs f.
  pose proof (pow2_Q_pos k) as HN.
  assert (Hs0 : ~ s == 0).
  { intro H0. rewrite H0 in Hs. lra. }
  assert (Hc : forall i, seq_inner (walsh_n k s i) f (pow2 k)
                         == / s * op_apply (had k) f (pow2 k) i).
  { intro i. unfold seq_inner, walsh_n, op_apply. rewrite <- q_sum_scale.
    apply q_sum_ext. intro m. field. exact Hs0. }
  transitivity (q_sum (fun i => / (s * s) * (op_apply (had k) f (pow2 k) i
                                             * op_apply (had k) f (pow2 k) i)) (pow2 k)).
  { apply q_sum_ext. intro i. rewrite (Hc i). field. exact Hs0. }
  rewrite q_sum_scale.
  pose proof (parseval_walsh k f) as HP. unfold seq_inner in HP. unfold seq_inner.
  rewrite HP. rewrite Hs. field. lra.
Qed.

(** Hence the normalised Walsh system is complete on N coordinates. *)
Corollary walsh_normalized_complete : forall (k : nat) (s : Q),
  s * s == inject_Z (Z.of_nat (pow2 k)) ->
  forall (f : nat -> Q) (m : nat), (m < pow2 k)%nat ->
  q_sum (fun i => seq_inner (walsh_n k s i) f (pow2 k) * walsh_n k s i m) (pow2 k) == f m.
Proof.
  intros k s Hs f.
  exact (proj1 (parseval_iff_complete_b (walsh_n k s) (pow2 k) (pow2 k)
                  (walsh_normalized_on k s Hs) f (pow2 k) (le_n (pow2 k)))
               (walsh_normalized_parseval k s Hs f)).
Qed.

(** For even k the premise holds: N = 4^j, s = 2^j. *)
Lemma pow2_double : forall j, pow2 (2 * j) = (pow2 j * pow2 j)%nat.
Proof.
  induction j as [|j IH].
  - reflexivity.
  - replace (2 * S j)%nat with (S (S (2 * j))) by lia.
    cbn [pow2]. rewrite IH. ring.
Qed.

Lemma walsh_even_norm_exists : forall j,
  inject_Z (Z.of_nat (pow2 j)) * inject_Z (Z.of_nat (pow2 j))
  == inject_Z (Z.of_nat (pow2 (2 * j))).
Proof.
  intro j. rewrite pow2_double. rewrite Nat2Z.inj_mul, inject_Z_mult. reflexivity.
Qed.

(** A rational orthonormal Walsh system for every N = 4^j. *)
Theorem walsh_4j_orthonormal : forall j i i',
  (i < pow2 (2 * j))%nat -> (i' < pow2 (2 * j))%nat ->
  seq_inner (walsh_n (2 * j) (inject_Z (Z.of_nat (pow2 j))) i)
            (walsh_n (2 * j) (inject_Z (Z.of_nat (pow2 j))) i') (pow2 (2 * j))
  == (if Nat.eqb i i' then 1 else 0).
Proof.
  intros j i i' Hi Hi'.
  exact (walsh_normalized_on (2 * j) (inject_Z (Z.of_nat (pow2 j)))
           (walsh_even_norm_exists j) i i' Hi Hi').
Qed.

(** N = 4, s = 2. *)
Example walsh_4_orthonormal : forall i i', (i < 4)%nat -> (i' < 4)%nat ->
  seq_inner (walsh_n 2 2 i) (walsh_n 2 2 i') 4%nat == (if Nat.eqb i i' then 1 else 0).
Proof.
  intros i i' Hi Hi'.
  apply (walsh_normalized_on 2%nat 2); [ reflexivity | exact Hi | exact Hi' ].
Qed.

(** For odd k there is no rational s with s^2 = N. *)
Theorem walsh_odd_no_rational_norm : forall (j : nat) (s : Q),
  ~ (s * s == inject_Z (Z.of_nat (pow2 (S (2 * j))))).
Proof.
  intros j s Hs.
  pose proof (pow2_Q_pos j) as Hp.
  set (p := inject_Z (Z.of_nat (pow2 j))) in *.
  assert (HN : inject_Z (Z.of_nat (pow2 (S (2 * j)))) == 2 * (p * p)).
  { cbn [pow2]. rewrite pow2_double.
    rewrite !Nat2Z.inj_mul, !inject_Z_mult. unfold p. reflexivity. }
  rewrite HN in Hs.
  apply (Sqrt2Irrational.no_rational_sqrt2 (s / p)).
  transitivity ((s * s) / (p * p)).
  - field. lra.
  - rewrite Hs. field. lra.
Qed.

Corollary walsh_2_no_rational_norm : forall s : Q, ~ (s * s == 2).
Proof. exact Sqrt2Irrational.no_rational_sqrt2. Qed.

(** A rational normalising factor exists exactly for even k. *)
Theorem walsh_rational_norm_iff_even : forall k : nat,
  (exists s : Q, s * s == inject_Z (Z.of_nat (pow2 k))) <-> Nat.Even k.
Proof.
  intro k. split.
  - intros [s Hs]. destruct (Nat.Even_or_Odd k) as [He | [m Hm]]; [ exact He | exfalso ].
    subst k. replace (2 * m + 1)%nat with (S (2 * m)) in Hs by lia.
    exact (walsh_odd_no_rational_norm m s Hs).
  - intros [m Hm]. subst k. exists (inject_Z (Z.of_nat (pow2 m))).
    exact (walsh_even_norm_exists m).
Qed.

