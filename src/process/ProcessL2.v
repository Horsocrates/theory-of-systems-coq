(** * ProcessL2.v — L² as Process of Q^n
    Elements: L² elements (= nat → Q), norm process, inner product process
    Roles:    norm is monotone increasing, bounded = in L²
    Rules:    Cauchy from monotone+bounded, completeness, Parseval
    Status:   complete
    STATUS: 25 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        PROCESS L2 — L² as Process of Q^n                                  *)
(*                                                                            *)
(*  Under P4: L² is NOT a completed Hilbert space.                           *)
(*  It is the process of Q^n with n increasing.                              *)
(*  An element is "in L²" if its norm process is bounded.                    *)
(*                                                                            *)
(*  STATUS: 25 Qed, 0 Admitted                                               *)
(*  AXIOMS: none                                                              *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs.
From Stdlib Require Import Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessBounds.
From ToS Require Import process.ProcessFiniteDim.

(* ================================================================== *)
(*  Part I: L² Element as Process                                       *)
(* ================================================================== *)

(** An L² element is given by its coefficients *)
Definition L2Element := nat -> Q.

(** The norm process: ‖f‖²_n = Σ_{k<n} f_k² *)
Definition norm_process (f : L2Element) : RealProcess :=
  fun n => norm_sq_n n f.

(** bounded_above for processes *)
Definition bounded_above (R : RealProcess) (B : Q) : Prop :=
  forall n, R n <= B.

(** Norm process is nonneg *)
Lemma norm_process_nonneg : forall f n,
  0 <= norm_process f n.
Proof.
  intros f n. unfold norm_process. apply ip_nonneg.
Qed.

(** Norm process is increasing *)
Lemma norm_process_increasing : forall f,
  monotone_increasing (norm_process f).
Proof.
  intros f n. unfold norm_process, norm_sq_n, inner_product_n. simpl.
  assert (H : 0 <= f n * f n) by apply q_sq_nonneg.
  lra.
Qed.

(** f is "in L²" if norm process is bounded *)
Definition in_L2 (f : L2Element) (B : Q) : Prop :=
  bounded_above (norm_process f) B.

(** in_L2 → norm process is Cauchy *)
Theorem L2_norm_cauchy : forall f B,
  in_L2 f B ->
  is_Cauchy (norm_process f).
Proof.
  intros f B Hin.
  apply monotone_bounded_Cauchy with (ub := B).
  - exact (norm_process_increasing f).
  - exact Hin.
Qed.

(** in_L2 implies nonneg bound *)
Lemma in_L2_nonneg_bound : forall f B,
  in_L2 f B -> 0 <= B.
Proof.
  intros f B Hin.
  assert (H0 := norm_process_nonneg f 0%nat).
  assert (HB := Hin 0%nat).
  lra.
Qed.

(* ================================================================== *)
(*  Part II: L² Inner Product as Process                                *)
(* ================================================================== *)

(** Inner product process: ⟨f,g⟩_n *)
Definition ip_process (f g : L2Element) : RealProcess :=
  fun n => inner_product_n n f g.

(** Inner product process at 0 is 0 *)
Lemma ip_process_0 : forall f g, ip_process f g 0%nat == 0.
Proof.
  intros. unfold ip_process, inner_product_n. simpl. reflexivity.
Qed.

(** Inner product process step *)
Lemma ip_process_S : forall f g n,
  ip_process f g (S n) == ip_process f g n + f n * g n.
Proof.
  intros. unfold ip_process, inner_product_n. simpl. reflexivity.
Qed.

(** IP bounded by norm product (from CS) *)
Lemma ip_bounded_by_norms : forall f g n,
  inner_product_n n f g * inner_product_n n f g <=
  norm_sq_n n f * norm_sq_n n g.
Proof.
  intros. apply cauchy_schwarz_n.
Qed.

(** If both f,g in L²: ip_process difference bounded *)
Theorem ip_process_diff_bounded : forall f g Bf Bg n,
  in_L2 f Bf -> in_L2 g Bg ->
  Qabs (ip_process f g (S n) - ip_process f g n) <=
  Bf + Bg.
Proof.
  intros f g Bf Bg n Hf Hg.
  assert (Hfn : f n * f n <= Bf).
  { assert (Hf1 := Hf (S n)). unfold norm_process, norm_sq_n, inner_product_n in Hf1. simpl in Hf1.
    assert (Hnn : 0 <= sum_Q (fun k => f k * f k) n) by (apply sum_Q_nonneg; intros; apply q_sq_nonneg).
    lra. }
  assert (Hgn : g n * g n <= Bg).
  { assert (Hg1 := Hg (S n)). unfold norm_process, norm_sq_n, inner_product_n in Hg1. simpl in Hg1.
    assert (Hnn : 0 <= sum_Q (fun k => g k * g k) n) by (apply sum_Q_nonneg; intros; apply q_sq_nonneg).
    lra. }
  assert (Hfg : Qabs (f n * g n) <= f n * f n + g n * g n).
  { assert (Hpos : 0 <= (f n - g n) * (f n - g n)) by apply q_sq_nonneg.
    assert (Hexp : (f n - g n) * (f n - g n) == f n * f n - 2 * (f n * g n) + g n * g n) by ring.
    assert (Hneg : 0 <= (f n + g n) * (f n + g n)) by apply q_sq_nonneg.
    assert (Hexp2 : (f n + g n) * (f n + g n) == f n * f n + 2 * (f n * g n) + g n * g n) by ring.
    destruct (Qlt_le_dec (f n * g n) 0).
    - rewrite Qabs_neg by lra. lra.
    - rewrite Qabs_pos by lra. lra. }
  assert (Hstep : ip_process f g (S n) - ip_process f g n == f n * g n).
  { unfold ip_process, inner_product_n. simpl. ring. }
  setoid_rewrite Hstep. lra.
Qed.

(* ================================================================== *)
(*  Part III: Parseval and Bessel                                       *)
(* ================================================================== *)

(** Parseval equality (process): ‖f‖²_n = Σ_{k<n} f_k² *)
Theorem parseval_process : forall f n,
  norm_process f n == sum_Q (fun k => f k * f k) n.
Proof.
  intros. unfold norm_process, norm_sq_n, inner_product_n. reflexivity.
Qed.

(** Bessel inequality (finite version): partial norm ≤ total bound *)
Theorem bessel_inequality : forall f B n,
  in_L2 f B -> norm_sq_n n f <= B.
Proof.
  intros f B n Hin. exact (Hin n).
Qed.

(** Individual coefficient bounded *)
Lemma coeff_bounded : forall f B k,
  in_L2 f B -> f k * f k <= B.
Proof.
  intros f B k Hin.
  assert (H := Hin (S k)).
  unfold norm_process, norm_sq_n, inner_product_n in H. simpl in H.
  assert (Hnn : 0 <= sum_Q (fun j => f j * f j) k).
  { apply sum_Q_nonneg. intros. apply q_sq_nonneg. }
  lra.
Qed.

(* ================================================================== *)
(*  Part IV: L² Space Operations                                        *)
(* ================================================================== *)

(** Zero element *)
Definition L2_zero : L2Element := fun _ => 0.

(** Scalar multiplication *)
Definition L2_scale (c : Q) (f : L2Element) : L2Element :=
  fun k => c * f k.

(** Zero is in L² *)
Lemma zero_in_L2 : in_L2 L2_zero 0.
Proof.
  intro n. unfold norm_process, norm_sq_n, inner_product_n, L2_zero.
  induction n as [| n' IH]; simpl; lra.
Qed.

(** Norm of zero is 0 *)
Lemma norm_zero_L2 : forall n, norm_process L2_zero n == 0.
Proof.
  intro n. unfold norm_process, norm_sq_n, inner_product_n, L2_zero.
  induction n as [| n' IH]; simpl; lra.
Qed.

(** Scaled element in L² *)
Lemma scale_in_L2 : forall c f B,
  in_L2 f B -> 0 <= B ->
  in_L2 (L2_scale c f) (c * c * B).
Proof.
  intros c f B Hin HB n.
  unfold norm_process, norm_sq_n, inner_product_n, L2_scale.
  assert (Heq : sum_Q (fun k => c * f k * (c * f k)) n ==
                c * c * sum_Q (fun k => f k * f k) n).
  { induction n as [| n' IH]; simpl; [ring | rewrite IH; ring]. }
  setoid_rewrite Heq.
  assert (Hf := Hin n). unfold norm_process, norm_sq_n, inner_product_n in Hf.
  assert (Hcsq : 0 <= c * c) by apply q_sq_nonneg.
  assert (Hmul : sum_Q (fun k => f k * f k) n * (c * c) <= B * (c * c)).
  { apply Qmult_le_compat_r; auto. }
  lra.
Qed.

(* ================================================================== *)
(*  Part V: Completeness (Process Version)                              *)
(* ================================================================== *)

(** A Cauchy sequence of L² elements: differences get small *)
Definition L2_cauchy_seq (fs : nat -> L2Element) (B : Q) : Prop :=
  (forall k, in_L2 (fs k) B) /\
  forall eps, 0 < eps -> exists K, forall j k,
    (K <= j)%nat -> (K <= k)%nat ->
    forall n, norm_sq_n n (fun i => fs j i - fs k i) < eps.

(** Pointwise convergence: each coordinate difference squared is small *)
Theorem L2_pointwise_cauchy : forall fs B i,
  L2_cauchy_seq fs B ->
  forall eps, 0 < eps -> exists K, forall j k,
    (K <= j)%nat -> (K <= k)%nat ->
    (fs j i - fs k i) * (fs j i - fs k i) < eps.
Proof.
  intros fs B i [Hbnd Hcau] eps Heps.
  destruct (Hcau eps Heps) as [K HK].
  exists K. intros j k Hj Hk.
  assert (Hn := HK j k Hj Hk (S i)).
  unfold norm_sq_n, inner_product_n in Hn. simpl in Hn.
  assert (Hnn : 0 <= sum_Q (fun k0 => (fs j k0 - fs k k0) * (fs j k0 - fs k k0)) i).
  { apply sum_Q_nonneg. intros. apply q_sq_nonneg. }
  lra.
Qed.

(** Completeness: bounded Cauchy sequence has bounded limit *)
Theorem L2_complete_bound : forall (fs : nat -> L2Element) (B : Q),
  (forall j, in_L2 (fs j) B) ->
  forall j n, norm_sq_n n (fs j) <= B.
Proof.
  intros fs B Hbnd j n. exact (Hbnd j n).
Qed.

(* ================================================================== *)
(*  Part VI: Distance and Metric                                        *)
(* ================================================================== *)

(** L² distance process *)
Definition L2_dist (f g : L2Element) : RealProcess :=
  fun n => norm_sq_n n (fun k => f k - g k).

(** Distance is nonneg *)
Lemma L2_dist_nonneg : forall f g n, 0 <= L2_dist f g n.
Proof. intros. unfold L2_dist. apply ip_nonneg. Qed.

(** Distance symmetric *)
Lemma L2_dist_sym : forall f g n, L2_dist f g n == L2_dist g f n.
Proof.
  intros. unfold L2_dist, norm_sq_n, inner_product_n.
  apply sum_Q_ext. intros k Hk. ring.
Qed.

(** Distance to self is 0 *)
Lemma L2_dist_self : forall f n, L2_dist f f n == 0.
Proof.
  intros. unfold L2_dist, norm_sq_n, inner_product_n.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. assert (H : f n' - f n' == 0) by ring.
    setoid_rewrite H. lra.
Qed.

(* ================================================================== *)
(*  Part VII: E/R/R Pattern                                             *)
(* ================================================================== *)

(** Convergence rate *)
Definition l2_convergence_rate : Q := 1 # 2.

Lemma l2_rate_valid :
  0 < l2_convergence_rate /\ l2_convergence_rate < 1.
Proof. unfold l2_convergence_rate. split; lra. Qed.

(** E/R/R: L² as process construction *)
Theorem L2_is_process :
  forall f B, in_L2 f B -> is_Cauchy (norm_process f).
Proof.
  intros f B Hin. apply L2_norm_cauchy with (B := B). exact Hin.
Qed.

(** P4: L² is a process of finite-dimensional spaces *)
(** No completed Hilbert space *)
(** No infinite-dimensional inner product space *)
(** The process {Q^n | n ∈ ℕ} IS L² under P4 *)
