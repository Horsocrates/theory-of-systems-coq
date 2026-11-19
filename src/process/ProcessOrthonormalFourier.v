(** * ProcessOrthonormalFourier.v -- The residual, the best approximation and the Fourier error of a finite orthonormal system, as a ToS System

    Elements: vectors with N rational coordinates ([nat -> Q] read below N);
              a family e of vectors; finite sums [q_sum]; the coefficients
              <e_k, f>; the number K of directions taken.
    Roles:    [seq_inner a b N]  -- the pairing;
              orthonormal system -- the first K0 vectors of e are pairwise
                                    orthogonal and of norm 1 on N coordinates
                                    (the satisfiable premise of
                                    ProcessL2Orthonormal.v);
              partial sum P_K    -- Sum_{k<K} <e_k, f> e_k;
              [ferr e f N K]     -- the squared error ||f - P_K||^2 of the
                                    K-term partial sum: a function of the
                                    stage K of the truncation process;
              [captured c K]     -- the energy of the first K coefficients.
    Rules:    the pairing is bilinear and symmetric; the residual is
              orthogonal to the directions taken; error = total energy -
              captured energy; one more coefficient lowers the error by its
              square; N orthonormal vectors on N coordinates restore every
              vector.

    Proved (no axioms):
      - [seq_inner_bilinear_symmetric];
      - under orthonormality of the first K0 vectors, for K <= K0:
        [proj_coord_b], [resid_ortho_b], [coef_e_resid_b],
        [best_approx_eq_b] (the excess of arbitrary coefficients is exactly
        Sum (a_k - c_k)^2), [best_approx_unique_b];
      - [on_count_le_dim]: an orthonormal system on N coordinates has at
        most N vectors;
      - [parseval_3_4_from_criterion]: f = (3, 4) as an instance of the
        completeness criterion;
      - the Fourier error: [ferr_nonneg] (no premise), [fourier_error_eq_b],
        [fourier_energy_balance_b], [bessel_from_error_b],
        [fourier_error_step_b], [fourier_error_monotone_b],
        [fourier_error_zero_iff_b], [fourier_error_zero_iff_recovers_b],
        [fourier_partial_best_b], [fourier_error_is_tail_b];
        [monotone_fails_without_on]: without orthonormality the error can
        grow;
      - a full system (N orthonormal vectors on N coordinates):
        [full_on_column_norm], [full_on_dual], [full_on_recovers],
        [full_on_parseval], [fourier_truncation_ends_exactly];
        instances [std_truncation_ends_exactly],
        [rot_truncation_ends_exactly].

    P4 diagnostic: K ranges over the vectors actually given (K <= K0 <= N);
      the truncation process K |-> P_K has finitely many stages at a fixed N
      and ends with exact recovery at K = N. Nothing is said about a
      completed infinite basis; the passage N -> infinity is a separate
      process and is not taken here.

    NOT claimed:
      - convergence of Fourier series when the truncation N is not fixed;
      - existence of orthonormal systems other than the examples given
        (normalisation needs square roots, which are processes here);
      - the trigonometric system (its values are not rational);
      - the root error ||f - P_K|| (only its square).

    STATUS: 30 Qed, 0 Admitted, 0 axioms
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
From ToS Require Import process.ProcessFourierCompression.
From ToS Require Import process.ProcessL2Orthonormal.

Open Scope Q_scope.

(* ===================================================================== *)
(*  1. The pairing is bilinear and symmetric                            *)
(* ===================================================================== *)

Lemma seq_inner_lin_r : forall (h a b : nat -> Q) (x y : Q) (N : nat),
  seq_inner h (fun m => x * a m + y * b m) N
  == x * seq_inner h a N + y * seq_inner h b N.
Proof.
  intros h a b x y N. unfold seq_inner.
  induction N as [|k IH]; cbn [q_sum]; [ ring | rewrite IH; ring ].
Qed.

Lemma seq_inner_lin_l : forall (h a b : nat -> Q) (x y : Q) (N : nat),
  seq_inner (fun m => x * a m + y * b m) h N
  == x * seq_inner a h N + y * seq_inner b h N.
Proof.
  intros h a b x y N. unfold seq_inner.
  induction N as [|k IH]; cbn [q_sum]; [ ring | rewrite IH; ring ].
Qed.

Theorem seq_inner_bilinear_symmetric :
  (forall a b N, seq_inner a b N == seq_inner b a N)
  /\ (forall h a b x y N, seq_inner h (fun m => x * a m + y * b m) N
                          == x * seq_inner h a N + y * seq_inner h b N)
  /\ (forall h a b x y N, seq_inner (fun m => x * a m + y * b m) h N
                          == x * seq_inner a h N + y * seq_inner b h N).
Proof.
  split; [ exact seq_inner_sym | split ].
  - exact seq_inner_lin_r.
  - exact seq_inner_lin_l.
Qed.

(* ===================================================================== *)
(*  2. The residual and the best approximation, K <= K0                 *)
(* ===================================================================== *)

Section OrthonormalResidual.

(** The first K0 vectors of e are orthonormal on N coordinates. *)
Variable e : nat -> nat -> Q.
Variable N K0 : nat.
Hypothesis Hon : forall i j, (i < K0)%nat -> (j < K0)%nat ->
  seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0).
Variable f : nat -> Q.

(** <e_j, Sum_{k<K} coef_k e_k> = coef_j for j < K <= K0. *)
Lemma proj_coord_b : forall (coef : nat -> Q) (j K : nat),
  (j < K)%nat -> (K <= K0)%nat ->
  seq_inner (e j) (fun m => q_sum (fun k => coef k * e k m) K) N == coef j.
Proof.
  intros coef j K Hj HK.
  rewrite (inner_proj_swap e coef (e j) K N).
  transitivity (q_sum (fun k => (if (j =? k)%nat then 1 else 0) * coef k) K).
  { apply q_sum_ext_bounded. intros k Hk.
    rewrite (Hon j k ltac:(lia) ltac:(lia)). ring. }
  rewrite (q_sum_delta 1 coef j K Hj). ring.
Qed.

(** The residual is orthogonal to every direction already taken. *)
Theorem resid_ortho_b : forall (j K : nat), (j < K)%nat -> (K <= K0)%nat ->
  seq_inner (e j) (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K) N == 0.
Proof.
  intros j K Hj HK.
  rewrite (seq_inner_sub_r (e j) f
             (fun m => q_sum (fun k => seq_inner (e k) f N * e k m) K) N).
  rewrite (proj_coord_b (fun k => seq_inner (e k) f N) j K Hj HK). ring.
Qed.

(** The projection does not touch the coordinate not yet taken:
    <e_K, f - P_K> = <e_K, f>. *)
Lemma coef_e_resid_b : forall K, (K < K0)%nat ->
  seq_inner (e K) (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K) N
  == seq_inner (e K) f N.
Proof.
  intros K HK.
  rewrite (seq_inner_sub_r (e K) f
             (fun m => q_sum (fun k => seq_inner (e k) f N * e k m) K) N).
  rewrite (proj_ortho_b e N K0 Hon (fun k => seq_inner (e k) f N) K HK). ring.
Qed.

(** The best-approximation identity:
    ||f - Sum a_k e_k||^2 = ||f - P_K||^2 + Sum_{k<K} (a_k - <e_k,f>)^2. *)
Theorem best_approx_eq_b : forall (a : nat -> Q) (K : nat), (K <= K0)%nat ->
  seq_inner (fun m => f m - q_sum (fun k => a k * e k m) K)
            (fun m => f m - q_sum (fun k => a k * e k m) K) N
  == seq_inner (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K)
               (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K) N
     + q_sum (fun k => (a k - seq_inner (e k) f N) * (a k - seq_inner (e k) f N)) K.
Proof.
  intros a K HK.
  pose proof (gen_resid e N K0 Hon f a K HK) as Ha.
  pose proof (gen_resid e N K0 Hon f (fun k => seq_inner (e k) f N) K HK) as Hc.
  cbv beta in Hc.
  rewrite Ha, Hc.
  rewrite <- Qplus_assoc. apply Qplus_comp; [ reflexivity | ].
  rewrite <- q_sum_plus. apply q_sum_ext. intro k. ring.
Qed.

(** The minimum is attained exactly at the Fourier coefficients. *)
Theorem best_approx_unique_b : forall (a : nat -> Q) (K : nat), (K <= K0)%nat ->
  (seq_inner (fun m => f m - q_sum (fun k => a k * e k m) K)
             (fun m => f m - q_sum (fun k => a k * e k m) K) N
   == seq_inner (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K)
                (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K) N)
  <-> (forall k, (k < K)%nat -> a k == seq_inner (e k) f N).
Proof.
  intros a K HK. pose proof (best_approx_eq_b a K HK) as Hba. split.
  - intro Heq.
    assert (Hz :
      q_sum (fun k => (a k - seq_inner (e k) f N) * (a k - seq_inner (e k) f N)) K == 0)
      by lra.
    intros k Hk.
    pose proof (q_sum_sq_zero (fun k => a k - seq_inner (e k) f N) K Hz k Hk) as Hk0.
    cbn beta in Hk0. lra.
  - intro Hall.
    assert (Hz :
      q_sum (fun k => (a k - seq_inner (e k) f N) * (a k - seq_inner (e k) f N)) K == 0).
    { apply q_sum_zero_bounded. intros k Hk. rewrite (Hall k Hk). ring. }
    lra.
Qed.

End OrthonormalResidual.

(* ===================================================================== *)
(*  3. At most N orthonormal vectors on N coordinates                   *)
(* ===================================================================== *)

(** Bessel for the standard vector delta_m gives Sum_{k<K0} e_k(m)^2 <= 1;
    summing over m < N and exchanging the sums gives K0 <= N. *)
Theorem on_count_le_dim : forall (e : nat -> nat -> Q) (N K0 : nat),
  (forall i j, (i < K0)%nat -> (j < K0)%nat ->
     seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0)) ->
  (K0 <= N)%nat.
Proof.
  intros e N K0 Hon.
  assert (Hb : forall m, (m < N)%nat -> q_sum (fun k => e k m * e k m) K0 <= 1).
  { intros m Hm.
    pose proof (bessel_b e N K0 Hon (delta m) K0 (le_n K0)) as H.
    assert (E1 : q_sum (fun k => seq_inner (e k) (delta m) N
                                 * seq_inner (e k) (delta m) N) K0
                 == q_sum (fun k => e k m * e k m) K0).
    { apply q_sum_ext. intro k. rewrite (seq_inner_delta (e k) N m Hm). reflexivity. }
    assert (E2 : seq_inner (delta m) (delta m) N == 1).
    { rewrite (seq_inner_delta (delta m) N m Hm). unfold delta.
      rewrite Nat.eqb_refl. reflexivity. }
    rewrite E1, E2 in H. exact H. }
  assert (Hsum : q_sum (fun m => q_sum (fun k => e k m * e k m) K0) N
                 <= q_sum (fun _ : nat => 1) N).
  { apply q_sum_le_bounded. exact Hb. }
  assert (Hswap : q_sum (fun m => q_sum (fun k => e k m * e k m) K0) N
                  == q_sum (fun k => q_sum (fun m => e k m * e k m) N) K0).
  { exact (q_sum_swap (fun m k => e k m * e k m) N K0). }
  assert (Hone : q_sum (fun k => q_sum (fun m => e k m * e k m) N) K0
                 == q_sum (fun _ : nat => 1) K0).
  { apply q_sum_ext_bounded. intros k Hk. pose proof (Hon k k Hk Hk) as Hkk.
    rewrite Nat.eqb_refl in Hkk. unfold seq_inner in Hkk. exact Hkk. }
  rewrite Hswap, Hone in Hsum. rewrite !q_sum_ones in Hsum.
  rewrite <- Zle_Qle in Hsum. lia.
Qed.

(* ===================================================================== *)
(*  4. The vector (3, 4) as an instance of the criterion                *)
(* ===================================================================== *)

(** For the standard basis of two coordinates and f = (3, 4): Parseval's
    equality holds (9 + 16 = 25), and by the criterion
    [parseval_iff_complete_b] the expansion restores both coordinates. *)
Example parseval_3_4_from_criterion :
  let f := fun n => if Nat.eqb n 0 then 3 else 4 in
  q_sum (fun k => seq_inner (delta k) f 2%nat * seq_inner (delta k) f 2%nat) 2%nat
  == seq_inner f f 2%nat
  /\ (forall m, (m < 2)%nat ->
        q_sum (fun k => seq_inner (delta k) f 2%nat * delta k m) 2%nat == f m).
Proof.
  intro f.
  pose proof (parseval_std_all f 2%nat) as HP. split; [ exact HP | ].
  exact (proj1 (parseval_iff_complete_b delta 2%nat 2%nat (std_basis_on 2%nat) f 2%nat
                  (le_n 2%nat)) HP).
Qed.

(* ===================================================================== *)
(*  5. The Fourier error                                                *)
(* ===================================================================== *)

(** The squared error of the K-term partial sum on N coordinates. *)
Definition ferr (e : nat -> nat -> Q) (f : nat -> Q) (N K : nat) : Q :=
  seq_inner (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K)
            (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K) N.

(** The error is nonnegative for ANY family e: a sum of squares. *)
Lemma ferr_nonneg : forall (e : nat -> nat -> Q) (f : nat -> Q) (N K : nat),
  0 <= ferr e f N K.
Proof.
  intros e f N K. unfold ferr, seq_inner. apply q_sum_nonneg. intro i. apply q_sq_nonneg.
Qed.

(** Without orthonormality the error can grow: one coordinate, e_0 = (2),
    f = (1); the error is 1 at K = 0 and 9 at K = 1. *)
Example monotone_fails_without_on :
  ferr (fun _ _ : nat => 2) (fun _ : nat => 1) 1%nat 0%nat
  < ferr (fun _ _ : nat => 2) (fun _ : nat => 1) 1%nat 1%nat.
Proof. vm_compute. reflexivity. Qed.

Section FourierError.

(** The first K0 vectors of e are orthonormal on N coordinates. *)
Variable e : nat -> nat -> Q.
Variable N K0 : nat.
Hypothesis Hon : forall i j, (i < K0)%nat -> (j < K0)%nat ->
  seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0).
Variable f : nat -> Q.

Local Notation cf := (fun k => seq_inner (e k) f N).

(** Error = total energy - captured energy. *)
Lemma fourier_error_eq_b : forall K, (K <= K0)%nat ->
  ferr e f N K == seq_inner f f N - captured cf K.
Proof.
  intros K HK. unfold ferr. rewrite (resid_norm_b e N K0 Hon f K HK).
  unfold captured. reflexivity.
Qed.

Lemma fourier_energy_balance_b : forall K, (K <= K0)%nat ->
  seq_inner f f N == captured cf K + ferr e f N K.
Proof. intros K HK. pose proof (fourier_error_eq_b K HK) as H. lra. Qed.

(** Bessel's inequality from the nonnegativity of the error: the two are
    linked by the error identity, which needs orthonormality. *)
Lemma bessel_from_error_b : forall K, (K <= K0)%nat ->
  captured cf K <= seq_inner f f N.
Proof.
  intros K HK. pose proof (fourier_error_eq_b K HK) as H.
  pose proof (ferr_nonneg e f N K) as Hn. lra.
Qed.

(** One more coefficient lowers the error by exactly its square. *)
Lemma fourier_error_step_b : forall K, (S K <= K0)%nat ->
  ferr e f N (S K) == ferr e f N K - seq_inner (e K) f N * seq_inner (e K) f N.
Proof.
  intros K HK.
  pose proof (fourier_error_eq_b (S K) HK) as H1.
  pose proof (fourier_error_eq_b K ltac:(lia)) as H0.
  pose proof (captured_step cf K) as Hs. cbv beta in Hs.
  lra.
Qed.

(** The error does not grow with K. *)
Lemma fourier_error_monotone_b : forall K K', (K <= K')%nat -> (K' <= K0)%nat ->
  ferr e f N K' <= ferr e f N K.
Proof.
  intros K K' Hle HK'.
  pose proof (fourier_error_eq_b K' HK') as H1.
  pose proof (fourier_error_eq_b K ltac:(lia)) as H0.
  pose proof (captured_mono cf K K' Hle) as Hm.
  lra.
Qed.

(** Error zero <-> Parseval's equality. *)
Lemma fourier_error_zero_iff_b : forall K, (K <= K0)%nat ->
  ferr e f N K == 0 <-> captured cf K == seq_inner f f N.
Proof.
  intros K HK. pose proof (fourier_error_eq_b K HK) as H. split; intro Hx; lra.
Qed.

(** Error zero <-> the partial sum restores f on every coordinate. *)
Theorem fourier_error_zero_iff_recovers_b : forall K, (K <= K0)%nat ->
  ferr e f N K == 0
  <-> (forall m, (m < N)%nat -> q_sum (fun k => seq_inner (e k) f N * e k m) K == f m).
Proof.
  intros K HK.
  pose proof (fourier_error_zero_iff_b K HK) as H1. unfold captured in H1. cbv beta in H1.
  pose proof (parseval_iff_complete_b e N K0 Hon f K HK) as H2.
  split; intro H.
  - apply (proj1 H2). apply (proj1 H1). exact H.
  - apply (proj2 H1). apply (proj2 H2). exact H.
Qed.

(** The partial sum is a best K-term approximation. *)
Theorem fourier_partial_best_b : forall (a : nat -> Q) (K : nat), (K <= K0)%nat ->
  ferr e f N K
  <= seq_inner (fun m => f m - q_sum (fun k => a k * e k m) K)
               (fun m => f m - q_sum (fun k => a k * e k m) K) N.
Proof. intros a K HK. exact (best_approx_b e N K0 Hon f a K HK). Qed.

(** If the K0 vectors are complete for f (Parseval at K0), the error of the
    K-term sum is the energy of the dropped coefficients. *)
Lemma fourier_error_is_tail_b : forall K, (K <= K0)%nat ->
  captured cf K0 == seq_inner f f N ->
  ferr e f N K
  == q_sum (fun i => seq_inner (e (K + i)%nat) f N * seq_inner (e (K + i)%nat) f N)
           (K0 - K)%nat.
Proof.
  intros K HK Hp.
  pose proof (fourier_error_eq_b K HK) as H.
  pose proof (truncation_error_eq cf K K0 HK) as Ht. cbv beta in Ht.
  lra.
Qed.

End FourierError.

(* ===================================================================== *)
(*  6. A full orthonormal system is complete                            *)
(* ===================================================================== *)

Lemma q_sum_nonneg_bounded : forall (g : nat -> Q) (N : nat),
  (forall i, (i < N)%nat -> 0 <= g i) -> 0 <= q_sum g N.
Proof.
  intros g N H. apply Qle_trans with (q_sum (fun _ : nat => 0) N).
  - rewrite q_sum_zero. apply Qle_refl.
  - apply q_sum_le_bounded. exact H.
Qed.

Lemma q_sum_nonneg_zero_bounded : forall (g : nat -> Q) (N : nat),
  (forall i, (i < N)%nat -> 0 <= g i) -> q_sum g N == 0 ->
  forall i, (i < N)%nat -> g i == 0.
Proof.
  intros g N. induction N as [|k IH]; intros Hnn Hsum i Hi.
  - lia.
  - cbn [q_sum] in Hsum.
    assert (H1 : 0 <= q_sum g k)
      by (apply q_sum_nonneg_bounded; intros j Hj; apply Hnn; lia).
    assert (H2 : 0 <= g k) by (apply Hnn; lia).
    destruct (Nat.eqb i k) eqn:E.
    + apply Nat.eqb_eq in E. subst i. lra.
    + apply Nat.eqb_neq in E. apply IH; [ intros j Hj; apply Hnn; lia | lra | lia ].
Qed.

Section FullSystem.

(** N orthonormal vectors on N coordinates. *)
Variable e : nat -> nat -> Q.
Variable N : nat.
Hypothesis Hon : forall i j, (i < N)%nat -> (j < N)%nat ->
  seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0).

(** Sum_{k<N} e_k(m)^2 = 1 for every coordinate m < N. *)
Lemma full_on_column_norm : forall m, (m < N)%nat ->
  q_sum (fun k => e k m * e k m) N == 1.
Proof.
  assert (Hb : forall m, (m < N)%nat -> q_sum (fun k => e k m * e k m) N <= 1).
  { intros m Hm.
    pose proof (bessel_b e N N Hon (delta m) N (le_n N)) as H.
    assert (E1 : q_sum (fun k => seq_inner (e k) (delta m) N
                                 * seq_inner (e k) (delta m) N) N
                 == q_sum (fun k => e k m * e k m) N).
    { apply q_sum_ext. intro k. rewrite (seq_inner_delta (e k) N m Hm). reflexivity. }
    assert (E2 : seq_inner (delta m) (delta m) N == 1).
    { rewrite (seq_inner_delta (delta m) N m Hm). unfold delta.
      rewrite Nat.eqb_refl. reflexivity. }
    rewrite E1, E2 in H. exact H. }
  assert (Htot : q_sum (fun m => 1 - q_sum (fun k => e k m * e k m) N) N == 0).
  { pose proof (q_sum_minus (fun _ : nat => 1)
                            (fun m => q_sum (fun k => e k m * e k m) N) N) as Hmin.
    cbv beta in Hmin.
    assert (Hswap : q_sum (fun m => q_sum (fun k => e k m * e k m) N) N
                    == q_sum (fun k => q_sum (fun m => e k m * e k m) N) N)
      by exact (q_sum_swap (fun m k => e k m * e k m) N N).
    assert (Hone : q_sum (fun k => q_sum (fun m => e k m * e k m) N) N
                   == q_sum (fun _ : nat => 1) N).
    { apply q_sum_ext_bounded. intros k Hk. pose proof (Hon k k Hk Hk) as Hkk.
      rewrite Nat.eqb_refl in Hkk. unfold seq_inner in Hkk. exact Hkk. }
    lra. }
  intros m Hm.
  assert (Hnn : forall i, (i < N)%nat -> 0 <= 1 - q_sum (fun k => e k i * e k i) N).
  { intros i Hi. pose proof (Hb i Hi). lra. }
  pose proof (q_sum_nonneg_zero_bounded
                (fun m => 1 - q_sum (fun k => e k m * e k m) N) N Hnn Htot m Hm) as H.
  cbv beta in H. lra.
Qed.

(** The dual relation: Sum_{k<N} e_k(m) e_k(m') = [m = m']. *)
Lemma full_on_dual : forall m m', (m < N)%nat -> (m' < N)%nat ->
  q_sum (fun k => e k m * e k m') N == (if Nat.eqb m' m then 1 else 0).
Proof.
  intros m m' Hm Hm'.
  assert (Hp : q_sum (fun k => seq_inner (e k) (delta m) N
                               * seq_inner (e k) (delta m) N) N
               == seq_inner (delta m) (delta m) N).
  { transitivity (q_sum (fun k => e k m * e k m) N).
    - apply q_sum_ext. intro k. rewrite (seq_inner_delta (e k) N m Hm). reflexivity.
    - rewrite (full_on_column_norm m Hm). rewrite (seq_inner_delta (delta m) N m Hm).
      unfold delta. rewrite Nat.eqb_refl. reflexivity. }
  pose proof (proj1 (parseval_iff_complete_b e N N Hon (delta m) N (le_n N)) Hp m' Hm')
    as Hc.
  transitivity (q_sum (fun k => seq_inner (e k) (delta m) N * e k m') N).
  - apply q_sum_ext. intro k. rewrite (seq_inner_delta (e k) N m Hm). reflexivity.
  - rewrite Hc. unfold delta. reflexivity.
Qed.

(** The N-term sum restores every f on every coordinate. *)
Theorem full_on_recovers : forall (f : nat -> Q) (m : nat), (m < N)%nat ->
  q_sum (fun k => seq_inner (e k) f N * e k m) N == f m.
Proof.
  intros f m Hm.
  transitivity (q_sum (fun k => q_sum (fun i => f i * (e k i * e k m)) N) N).
  { apply q_sum_ext. intro k. unfold seq_inner.
    transitivity (q_sum (fun i => e k m * (e k i * f i)) N).
    - transitivity (e k m * q_sum (fun i => e k i * f i) N); [ ring | ].
      symmetry. exact (q_sum_scale (e k m) (fun i => e k i * f i) N).
    - apply q_sum_ext. intro i. ring. }
  transitivity (q_sum (fun i => q_sum (fun k => f i * (e k i * e k m)) N) N).
  { symmetry. exact (q_sum_swap (fun i k => f i * (e k i * e k m)) N N). }
  transitivity (q_sum (fun i => f i * delta m i) N).
  { apply q_sum_ext_bounded. intros i Hi. cbv beta.
    transitivity (f i * q_sum (fun k => e k i * e k m) N).
    - exact (q_sum_scale (f i) (fun k => e k i * e k m) N).
    - rewrite (full_on_dual i m Hi Hm). unfold delta.
      rewrite (Nat.eqb_sym m i). reflexivity. }
  exact (seq_inner_delta f N m Hm).
Qed.

(** Parseval's equality at K = N for every f. *)
Theorem full_on_parseval : forall f : nat -> Q,
  q_sum (fun k => seq_inner (e k) f N * seq_inner (e k) f N) N == seq_inner f f N.
Proof.
  intro f. apply (proj2 (parseval_iff_complete_b e N N Hon f N (le_n N))).
  intros m Hm. exact (full_on_recovers f m Hm).
Qed.

(** The truncation process of a full orthonormal system: the error starts
    at the total energy, does not grow, and is zero at K = N. *)
Theorem fourier_truncation_ends_exactly : forall f : nat -> Q,
  ferr e f N 0 == seq_inner f f N
  /\ (forall K K', (K <= K')%nat -> (K' <= N)%nat -> ferr e f N K' <= ferr e f N K)
  /\ ferr e f N N == 0.
Proof.
  intro f. split; [ | split ].
  - rewrite (fourier_error_eq_b e N N Hon f 0 (Nat.le_0_l N)).
    unfold captured. cbn [q_sum]. ring.
  - intros K K' Hle HK'. exact (fourier_error_monotone_b e N N Hon f K K' Hle HK').
  - apply (proj2 (fourier_error_zero_iff_b e N N Hon f N (le_n N))).
    unfold captured. exact (full_on_parseval f).
Qed.

End FullSystem.

(** The standard system: exact recovery at K = N for every f and N. *)
Corollary std_truncation_ends_exactly : forall (f : nat -> Q) (N : nat),
  ferr delta f N N == 0.
Proof.
  intros f N.
  exact (proj2 (proj2 (fourier_truncation_ends_exactly delta N (std_basis_on N) f))).
Qed.

(** The rotated basis (3/5, 4/5), (-4/5, 3/5): exact recovery at K = 2. *)
Example rot_truncation_ends_exactly : forall f : nat -> Q,
  ferr rot f 2%nat 2%nat == 0.
Proof.
  intro f.
  exact (proj2 (proj2 (fourier_truncation_ends_exactly rot 2%nat rot_orthonormal f))).
Qed.

