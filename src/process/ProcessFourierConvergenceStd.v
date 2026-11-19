(** * ProcessFourierConvergenceStd.v -- Convergence of the Fourier series in the standard system when the truncation is not fixed, as a ToS System

    Elements: a sequence f : nat -> Q of rational coordinates; the truncation
              N (the number of coordinates read); the number K of terms of
              the partial sum; finite sums.
    Roles:    [captured f n]   -- the energy process n |-> Sum_{i<n} f_i^2;
              [ferr delta f N K] -- the squared error of the K-term partial
                                    sum on N coordinates (standard system);
              [std_psum f N K] -- the K-term partial sum as a vector: a stage
                                  of the sequence of partial sums;
              [l2_limit]       -- the coordinate-wise limit built in
                                  ProcessL2RieszFischer.v.
    Rules:    for K <= N the error is the energy between K and N; for N <= K
              it is zero. Hence the error is small for ALL truncations N at
              once exactly when the energy process is a Cauchy process.

    Proved (no axioms):
      - [std_partial_sum], [std_error_formula], [std_error_is_tail],
        [std_error_zero_beyond];
      - [std_fourier_l2_convergence_iff]: the energy process of f is Cauchy
        <-> the residual of the Fourier series tends to zero uniformly in
        the truncation N ([std_fourier_tail_to_zero] and its converse);
      - [std_partial_sums_cauchy]: the partial sums are then L2-Cauchy with a
        stage independent of N; [std_partial_sums_L2CauchySq]: the premise
        of Riesz-Fischer holds; [std_limit_is_f]: the coordinates of the
        constructed limit are those of f; [std_fourier_riesz_fischer];
      - the premise is satisfiable: [finite_support_energy_cauchy];
        f_i = 2^(-i) -- [geometric_energy_cauchy],
        [geometric_fourier_converges];
      - [rf_conclusion_is_hypothesis]: the conclusion of [l2_riesz_fischer]
        is its premise unfolded.

    P4 diagnostic: nothing is summed to infinity. "The series converges"
      is read as: for every eps there is a stage M after which the error is
      below eps at EVERY truncation N -- a statement about finite sums. The
      premise that the energy process is Cauchy is honest: it is not derived
      from boundedness (that step would need classical logic).

    NOT claimed:
      - convergence for an arbitrary orthonormal system (only the standard
        one; other complete systems are not built for unbounded N);
      - that every f with bounded energy has a Cauchy energy process;
      - pointwise convergence, the Gibbs phenomenon, trigonometric series.

    STATUS: 26 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.
From ToS Require Import process.ProcessFubiniGeneral.
From ToS Require Import process.ProcessCompactSpectral.
From ToS Require Import process.ProcessL2CauchySchwarz.
From ToS Require Import process.ProcessL2Triangle.
From ToS Require Import process.ProcessL2BesselGeneral.
From ToS Require Import process.ProcessL2Parseval.
From ToS Require Import process.ProcessL2RieszFischer.
From ToS Require Import process.ProcessDCT.
From ToS Require Import process.ProcessPositionMomentum.
From ToS Require Import process.ProcessFourierCompression.
From ToS Require Import process.ProcessL2Orthonormal.
From ToS Require Import process.ProcessOrthonormalFourier.

Open Scope Q_scope.

(* ===================================================================== *)
(*  1. The standard system: the error is a piece of the energy          *)
(* ===================================================================== *)

Lemma seq_inner_self_ext_bounded : forall (g h : nat -> Q) (N : nat),
  (forall i, (i < N)%nat -> g i == h i) -> seq_inner g g N == seq_inner h h N.
Proof.
  intros g h N H. unfold seq_inner. apply q_sum_ext_bounded.
  intros i Hi. cbv beta. rewrite (H i Hi). reflexivity.
Qed.

(** The K-term partial sum of the standard system at a coordinate m < N. *)
Lemma std_partial_sum : forall (f : nat -> Q) (N K m : nat), (m < N)%nat ->
  q_sum (fun k => seq_inner (delta k) f N * delta k m) K
  == (if (m <? K)%nat then f m else 0).
Proof.
  intros f N K m Hm. destruct (Nat.ltb m K) eqn:E.
  - apply Nat.ltb_lt in E.
    transitivity (q_sum (fun k => (if Nat.eqb m k then 1 else 0)
                                  * seq_inner (delta k) f N) K).
    + apply q_sum_ext. intro k.
      change (delta k m) with (if Nat.eqb m k then 1 else 0). ring.
    + transitivity (1 * seq_inner (delta m) f N).
      * exact (q_sum_delta 1 (fun k => seq_inner (delta k) f N) m K E).
      * rewrite (seq_inner_sym (delta m) f N), (seq_inner_delta f N m Hm). ring.
  - apply Nat.ltb_ge in E.
    apply q_sum_zero_bounded. intros k Hk. cbv beta.
    change (delta k m) with (if Nat.eqb m k then 1 else 0).
    assert (Hne : Nat.eqb m k = false) by (apply Nat.eqb_neq; lia).
    rewrite Hne. ring.
Qed.

Lemma std_error_formula : forall (f : nat -> Q) (N K : nat),
  ferr delta f N K == q_sum (fun m => if (m <? K)%nat then 0 else f m * f m) N.
Proof.
  intros f N K. unfold ferr.
  transitivity (seq_inner (fun m => f m - (if (m <? K)%nat then f m else 0))
                          (fun m => f m - (if (m <? K)%nat then f m else 0)) N).
  - apply seq_inner_self_ext_bounded. intros m Hm. cbv beta.
    rewrite (std_partial_sum f N K m Hm). reflexivity.
  - unfold seq_inner. apply q_sum_ext. intro m. destruct (Nat.ltb m K); ring.
Qed.

Lemma std_tail_zero : forall (f : nat -> Q) (K N : nat), (N <= K)%nat ->
  q_sum (fun m => if (m <? K)%nat then 0 else f m * f m) N == 0.
Proof.
  intros f K N H. apply q_sum_zero_bounded. intros m Hm. cbv beta.
  assert (E : (m <? K)%nat = true) by (apply Nat.ltb_lt; lia).
  rewrite E. reflexivity.
Qed.

Lemma std_tail_formula : forall (f : nat -> Q) (K N : nat), (K <= N)%nat ->
  q_sum (fun m => if (m <? K)%nat then 0 else f m * f m) N
  == captured f N - captured f K.
Proof.
  intros f K N. induction N as [|n IH]; intro H.
  - assert (HK : K = 0%nat) by lia. subst K. unfold captured. cbn [q_sum]. ring.
  - destruct (Nat.eq_dec K (S n)) as [HeqK | Hne].
    + subst K. rewrite (std_tail_zero f (S n) (S n) (le_n _)). ring.
    + cbn [q_sum]. rewrite (IH ltac:(lia)).
      assert (E : (n <? K)%nat = false) by (apply Nat.ltb_ge; lia).
      rewrite E. unfold captured. cbn [q_sum]. ring.
Qed.

(** For K <= N the error on N coordinates is the energy between K and N. *)
Theorem std_error_is_tail : forall (f : nat -> Q) (N K : nat), (K <= N)%nat ->
  ferr delta f N K == captured f N - captured f K.
Proof.
  intros f N K H. rewrite (std_error_formula f N K). exact (std_tail_formula f K N H).
Qed.

(** For N <= K the error on N coordinates is zero. *)
Theorem std_error_zero_beyond : forall (f : nat -> Q) (N K : nat), (N <= K)%nat ->
  ferr delta f N K == 0.
Proof.
  intros f N K H. rewrite (std_error_formula f N K). exact (std_tail_zero f K N H).
Qed.

(* ===================================================================== *)
(*  2. The residual tends to zero <-> the energy process is Cauchy      *)
(* ===================================================================== *)

(** If the energy process K |-> Sum_{i<K} f_i^2 is Cauchy, the residual of
    the Fourier series of f tends to zero, uniformly in the truncation N. *)
Theorem std_fourier_tail_to_zero : forall f : nat -> Q,
  is_Cauchy (fun n => captured f n) ->
  forall eps, 0 < eps -> exists M, forall K N, (M <= K)%nat -> ferr delta f N K < eps.
Proof.
  intros f HC eps Heps. destruct (HC eps Heps) as [M HM]. exists M. intros K N HK.
  destruct (Nat.le_gt_cases K N) as [Hle | Hgt].
  - rewrite (std_error_is_tail f N K Hle).
    pose proof (HM N K ltac:(lia) HK) as H. cbv beta in H.
    apply Qle_lt_trans with (Qabs (captured f N - captured f K));
      [ apply Qle_Qabs | exact H ].
  - rewrite (std_error_zero_beyond f N K ltac:(lia)). exact Heps.
Qed.

(** Conversely. *)
Theorem std_fourier_tail_to_zero_conv : forall f : nat -> Q,
  (forall eps, 0 < eps -> exists M, forall K N, (M <= K)%nat -> ferr delta f N K < eps) ->
  is_Cauchy (fun n => captured f n).
Proof.
  intros f H. unfold is_Cauchy. intros eps Heps.
  destruct (H eps Heps) as [M HM]. exists M. intros m n Hm Hn.
  destruct (Nat.le_gt_cases m n) as [Hle | Hgt].
  - pose proof (HM m n Hm) as H1. rewrite (std_error_is_tail f n m Hle) in H1.
    pose proof (captured_mono f m n Hle) as Hmono.
    rewrite Qabs_Qminus. rewrite Qabs_pos; [ exact H1 | lra ].
  - pose proof (HM n m Hn) as H1.
    rewrite (std_error_is_tail f m n ltac:(lia)) in H1.
    pose proof (captured_mono f n m ltac:(lia)) as Hmono.
    rewrite Qabs_pos; [ exact H1 | lra ].
Qed.

Theorem std_fourier_l2_convergence_iff : forall f : nat -> Q,
  is_Cauchy (fun n => captured f n)
  <-> (forall eps, 0 < eps -> exists M, forall K N, (M <= K)%nat ->
         ferr delta f N K < eps).
Proof.
  intro f. split;
    [ apply std_fourier_tail_to_zero | apply std_fourier_tail_to_zero_conv ].
Qed.

(* ===================================================================== *)
(*  3. The partial sums are L2-Cauchy; the limit is f                   *)
(* ===================================================================== *)

(** The partial sums of the standard system as a sequence of vectors. *)
Definition std_psum (f : nat -> Q) (N : nat) : nat -> nat -> Q :=
  fun K m => q_sum (fun k => seq_inner (delta k) f N * delta k m) K.

(** They form an L2-Cauchy sequence at every truncation N, with a stage M
    that does not depend on N. *)
Theorem std_partial_sums_cauchy : forall f : nat -> Q,
  is_Cauchy (fun n => captured f n) ->
  forall eps, 0 < eps -> exists M, forall N K K', (M <= K)%nat -> (M <= K')%nat ->
    seq_inner (fun i => std_psum f N K i - std_psum f N K' i)
              (fun i => std_psum f N K i - std_psum f N K' i) N <= eps.
Proof.
  intros f HC eps Heps.
  assert (H4 : 0 < eps * (1 # 4)) by lra.
  destruct (std_fourier_tail_to_zero f HC (eps * (1 # 4)) H4) as [M HM].
  exists M. intros N K K' HK HK'.
  pose proof (HM K N HK) as H1. pose proof (HM K' N HK') as H2.
  pose proof (l2_dist_sq_triangle (std_psum f N K) f (std_psum f N K') N) as Htri.
  unfold l2_dist_sq in Htri.
  assert (E1 : q_sum (fun i => (std_psum f N K i - f i) * (std_psum f N K i - f i)) N
               == ferr delta f N K).
  { unfold ferr, std_psum, seq_inner. apply q_sum_ext. intro i. cbv beta. ring. }
  assert (E2 : q_sum (fun i => (f i - std_psum f N K' i) * (f i - std_psum f N K' i)) N
               == ferr delta f N K').
  { unfold ferr, std_psum, seq_inner. apply q_sum_ext. intro i. cbv beta. ring. }
  apply Qle_trans with (2 * ferr delta f N K + 2 * ferr delta f N K'); [ | lra ].
  rewrite <- E1, <- E2. exact Htri.
Qed.

(** In particular the premise of l2_riesz_fischer holds at every N. *)
Corollary std_partial_sums_L2CauchySq : forall (f : nat -> Q) (N : nat),
  is_Cauchy (fun n => captured f n) -> L2CauchySq (std_psum f N) N.
Proof.
  intros f N HC eps Heps. destruct (std_partial_sums_cauchy f HC eps Heps) as [M HM].
  exists M. intros m n Hm Hn. exact (HM N m n Hm Hn).
Qed.

(** The coordinates of the constructed limit are eventually those of f. *)
Lemma std_limit_is_f : forall (f : nat -> Q) (N m s : nat),
  (m < N)%nat -> (m < s)%nat -> l2_limit (std_psum f N) m s == f m.
Proof.
  intros f N m s Hm Hs. unfold l2_limit, std_psum.
  rewrite (std_partial_sum f N s m Hm).
  assert (E : (m <? s)%nat = true) by (apply Nat.ltb_lt; exact Hs).
  rewrite E. reflexivity.
Qed.

(** Riesz-Fischer applied to the partial sums: the coordinates of the limit
    are Cauchy processes, the distance from the partial sums to the limit
    is a Cauchy process and tends to zero. *)
Corollary std_fourier_riesz_fischer : forall (f : nat -> Q) (N : nat),
  is_Cauchy (fun n => captured f n) ->
  (forall i, (i < N)%nat -> is_Cauchy (l2_limit (std_psum f N) i))
  /\ (forall n, is_Cauchy (dist_to_limit (std_psum f N) N n))
  /\ (forall eps, eps > 0 -> exists M, forall n, (M <= n)%nat ->
        exists S, forall s, (S <= s)%nat -> dist_to_limit (std_psum f N) N n s <= eps).
Proof.
  intros f N HC.
  exact (riesz_fischer_process_form (std_psum f N) N (std_partial_sums_L2CauchySq f N HC)).
Qed.

(* ===================================================================== *)
(*  4. The premise is satisfiable                                       *)
(* ===================================================================== *)

(** A sequence with finite support. *)
Lemma captured_stationary : forall (f : nat -> Q) (n0 : nat),
  (forall i, (n0 <= i)%nat -> f i == 0) ->
  forall n, (n0 <= n)%nat -> captured f n == captured f n0.
Proof.
  intros f n0 H n Hn. induction Hn as [|n Hn IH].
  - reflexivity.
  - rewrite captured_step, IH, (H n Hn). ring.
Qed.

Example finite_support_energy_cauchy : forall (f : nat -> Q) (n0 : nat),
  (forall i, (n0 <= i)%nat -> f i == 0) -> is_Cauchy (fun n => captured f n).
Proof.
  intros f n0 H. unfold is_Cauchy. intros eps Heps. exists n0. intros m n Hm Hn.
  rewrite (captured_stationary f n0 H m Hm), (captured_stationary f n0 H n Hn).
  assert (E : captured f n0 - captured f n0 == 0) by ring.
  rewrite E. exact Heps.
Qed.

(** A sequence with infinitely many nonzero coordinates: f_i = 2^(-i). Its
    energy process Sum_{i<n} 4^(-i) is Cauchy. *)
Fixpoint half_pow (i : nat) : Q :=
  match i with
  | O => 1
  | S j => (1 # 2) * half_pow j
  end.

Lemma half_pow_sq_S : forall n, half_pow (S n) * half_pow (S n) == (1 # 4) * (half_pow n * half_pow n).
Proof. intro n. cbn [half_pow]. ring. Qed.

Lemma half_pow_sq_le_1 : forall n, half_pow n * half_pow n <= 1.
Proof.
  induction n as [|n IH].
  - cbn [half_pow]. lra.
  - pose proof (half_pow_sq_S n) as H. pose proof (q_sq_nonneg (half_pow n)) as H0. lra.
Qed.

Lemma half_pow_sq_antitone : forall m n, (m <= n)%nat -> half_pow n * half_pow n <= half_pow m * half_pow m.
Proof.
  intros m n H. induction H as [|n H IH].
  - apply Qle_refl.
  - pose proof (half_pow_sq_S n) as Hs. pose proof (q_sq_nonneg (half_pow n)) as H0. lra.
Qed.

Lemma geometric_energy_closed : forall n,
  3 * captured half_pow n == 4 - 4 * (half_pow n * half_pow n).
Proof.
  induction n as [|n IH].
  - unfold captured. cbn [q_sum half_pow]. ring.
  - pose proof (captured_step half_pow n) as Hc. pose proof (half_pow_sq_S n) as Hs. lra.
Qed.

Lemma natQ_S : forall K : nat,
  inject_Z (Z.of_nat (S K)) == inject_Z (Z.of_nat K) + 1.
Proof.
  intro K. rewrite Nat2Z.inj_succ. unfold Z.succ. rewrite inject_Z_plus. reflexivity.
Qed.

Lemma natQ_nonneg : forall K : nat, 0 <= inject_Z (Z.of_nat K).
Proof. intro K. unfold Qle, inject_Z. simpl. lia. Qed.

Lemma natQ_half_pow_sq_le_1 : forall K : nat, inject_Z (Z.of_nat K) * (half_pow K * half_pow K) <= 1.
Proof.
  induction K as [|K IH].
  - change (inject_Z (Z.of_nat 0)) with 0. lra.
  - pose proof (natQ_S K) as Hn. pose proof (half_pow_sq_S K) as Hs.
    pose proof (half_pow_sq_le_1 K) as H1. pose proof (q_sq_nonneg (half_pow K)) as H0.
    rewrite Hn, Hs. lra.
Qed.

Example geometric_energy_cauchy : is_Cauchy (fun n => captured half_pow n).
Proof.
  unfold is_Cauchy. intros eps Heps.
  destruct (q_archimedean 2 eps Heps) as [K HK].
  pose proof (natQ_half_pow_sq_le_1 K) as Hq. pose proof (natQ_nonneg K) as Hk.
  assert (Hsmall : 2 * (half_pow K * half_pow K) < eps).
  { destruct (Qlt_le_dec (2 * (half_pow K * half_pow K)) eps) as [Hlt | Hge];
      [ exact Hlt | exfalso ].
    assert (Hx : eps * inject_Z (Z.of_nat K)
                 <= 2 * (half_pow K * half_pow K) * inject_Z (Z.of_nat K))
      by (apply Qmult_le_compat_r; assumption).
    lra. }
  exists K. intros m n Hm Hn. cbv beta.
  assert (Hpair : forall a b, (K <= a)%nat -> (a <= b)%nat ->
            0 <= captured half_pow b - captured half_pow a
            /\ captured half_pow b - captured half_pow a < eps).
  { intros a b Ha Hab.
    pose proof (geometric_energy_closed a) as Ea.
    pose proof (geometric_energy_closed b) as Eb.
    pose proof (q_sq_nonneg (half_pow b)) as Hb0.
    pose proof (half_pow_sq_antitone K a Ha) as Hanti.
    pose proof (captured_mono half_pow a b Hab) as Hmono.
    split; lra. }
  destruct (Nat.le_gt_cases m n) as [Hle | Hgt].
  - destruct (Hpair m n Hm Hle) as [H0 H1].
    rewrite Qabs_Qminus. rewrite Qabs_pos; assumption.
  - destruct (Hpair n m Hn ltac:(lia)) as [H0 H1].
    rewrite Qabs_pos; assumption.
Qed.

Corollary geometric_fourier_converges :
  forall eps, 0 < eps -> exists M, forall K N, (M <= K)%nat ->
    ferr delta half_pow N K < eps.
Proof. exact (std_fourier_tail_to_zero half_pow geometric_energy_cauchy). Qed.

(* ===================================================================== *)
(*  5. Riesz-Fischer at a fixed truncation restates its premise         *)
(* ===================================================================== *)

(** The conclusion of l2_riesz_fischer is its premise, by the definition of
    l2_limit: the theorem does not by itself give convergence of partial
    sums; sections 2-3 above supply the premise for the standard system. *)
Lemma rf_conclusion_is_hypothesis : forall (F : nat -> nat -> Q) (N : nat),
  L2CauchySq F N <->
  (forall eps, eps > 0 -> exists M, forall n s, (M <= n)%nat -> (M <= s)%nat ->
     seq_inner (fun i => F n i - l2_limit F i s)
               (fun i => F n i - l2_limit F i s) N <= eps).
Proof. intros F N. split; intro H; exact H. Qed.

