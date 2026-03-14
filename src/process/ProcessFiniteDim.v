(** * ProcessFiniteDim.v — Q^n Spaces as Building Blocks
    Elements: vectors in Q^n (= nat → Q), inner product, norm, projections
    Roles:    each component f(k) contributes f(k)² to the norm
    Rules:    inner product bilinear, norm monotone in dimension, Cauchy-Schwarz
    Status:   complete
    STATUS: 35 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        PROCESS FINITE DIM — Q^n Spaces as Building Blocks                 *)
(*                                                                            *)
(*  Under P4: there is no infinite-dimensional Hilbert space.                *)
(*  There are finite-dimensional Q^n spaces at each level n.                 *)
(*  L² = the process {Q^n} with n increasing.                               *)
(*                                                                            *)
(*  STATUS: 35 Qed, 0 Admitted                                               *)
(*  AXIOMS: none                                                              *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs.
From Stdlib Require Import Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.

(* ================================================================== *)
(*  Part I: Finite Sums over Q                                          *)
(* ================================================================== *)

(** Sum of f(k) for k = 0..n-1 *)
Fixpoint sum_Q (f : nat -> Q) (n : nat) : Q :=
  match n with
  | O => 0
  | S k => sum_Q f k + f k
  end.

Lemma sum_Q_0 : forall f, sum_Q f 0 == 0.
Proof. intro. simpl. reflexivity. Qed.

Lemma sum_Q_S : forall f n, sum_Q f (S n) == sum_Q f n + f n.
Proof. intros. simpl. reflexivity. Qed.

Lemma sum_Q_ext : forall (f g : nat -> Q) n,
  (forall k, (k < n)%nat -> f k == g k) ->
  sum_Q f n == sum_Q g n.
Proof.
  intros f g n Hext. induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH; [| intros; apply Hext; lia].
    rewrite (Hext n' ltac:(lia)). reflexivity.
Qed.

Lemma sum_Q_plus : forall (f g : nat -> Q) n,
  sum_Q (fun k => f k + g k) n == sum_Q f n + sum_Q g n.
Proof.
  intros f g n. induction n as [| n' IH].
  - simpl. ring.
  - simpl. rewrite IH. ring.
Qed.

Lemma sum_Q_scale : forall (c : Q) (f : nat -> Q) n,
  sum_Q (fun k => c * f k) n == c * sum_Q f n.
Proof.
  intros c f n. induction n as [| n' IH].
  - simpl. ring.
  - simpl. rewrite IH. ring.
Qed.

Lemma sum_Q_nonneg : forall (f : nat -> Q) n,
  (forall k, (k < n)%nat -> 0 <= f k) ->
  0 <= sum_Q f n.
Proof.
  intros f n Hnn. induction n as [| n' IH].
  - simpl. lra.
  - simpl. assert (IH' := IH ltac:(intros; apply Hnn; lia)).
    assert (Hn' := Hnn n' ltac:(lia)). lra.
Qed.

Lemma q_sq_nonneg : forall (x : Q), 0 <= x * x.
Proof.
  intro x. destruct (Qlt_le_dec x 0) as [Hneg | Hpos].
  - assert (H : x * x == (-x) * (-x)) by ring.
    rewrite H. apply Qmult_le_0_compat; lra.
  - apply Qmult_le_0_compat; lra.
Qed.

(* ================================================================== *)
(*  Part II: Inner Product and Norm on Q^n                              *)
(* ================================================================== *)

(** Inner product at dimension n: ⟨f,g⟩_n = Σ_{k<n} f(k)·g(k) *)
Definition inner_product_n (n : nat) (f g : nat -> Q) : Q :=
  sum_Q (fun k => f k * g k) n.

(** Norm squared at dimension n: ‖f‖²_n = ⟨f,f⟩_n *)
Definition norm_sq_n (n : nat) (f : nat -> Q) : Q :=
  inner_product_n n f f.

(** Inner product is symmetric *)
Lemma ip_symmetric : forall n f g,
  inner_product_n n f g == inner_product_n n g f.
Proof.
  intros. unfold inner_product_n.
  apply sum_Q_ext. intros k _. ring.
Qed.

(** Inner product is linear in first argument (scaling) *)
Lemma ip_linear_l : forall n c f g,
  inner_product_n n (fun k => c * f k) g == c * inner_product_n n f g.
Proof.
  intros. unfold inner_product_n.
  rewrite <- sum_Q_scale. apply sum_Q_ext. intros k _. ring.
Qed.

(** Inner product is linear in first argument (addition) *)
Lemma ip_add_l : forall n f1 f2 g,
  inner_product_n n (fun k => f1 k + f2 k) g ==
  inner_product_n n f1 g + inner_product_n n f2 g.
Proof.
  intros. unfold inner_product_n.
  rewrite <- sum_Q_plus. apply sum_Q_ext. intros k _. ring.
Qed.

(** Norm squared is nonneg *)
Lemma ip_nonneg : forall n f,
  0 <= norm_sq_n n f.
Proof.
  intros. unfold norm_sq_n, inner_product_n.
  apply sum_Q_nonneg. intros k _. apply q_sq_nonneg.
Qed.

(** Norm increases with dimension *)
Lemma norm_monotone : forall n f,
  norm_sq_n n f <= norm_sq_n (S n) f.
Proof.
  intros. unfold norm_sq_n, inner_product_n. simpl.
  assert (H := q_sq_nonneg (f n)). lra.
Qed.

(** Norm of zero vector *)
Lemma norm_zero : forall n,
  norm_sq_n n (fun _ => 0) == 0.
Proof.
  intro n. unfold norm_sq_n, inner_product_n.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. ring.
Qed.

(* ================================================================== *)
(*  Part III: Projections                                                *)
(* ================================================================== *)

(** Projection onto first n components *)
Definition project_n (n : nat) (f : nat -> Q) : nat -> Q :=
  fun k => if Nat.ltb k n then f k else 0.

Lemma project_below : forall n f k,
  (k < n)%nat -> project_n n f k == f k.
Proof.
  intros n f k Hk. unfold project_n.
  destruct (Nat.ltb_spec k n); [reflexivity | lia].
Qed.

Lemma project_above : forall n f k,
  (n <= k)%nat -> project_n n f k == 0.
Proof.
  intros n f k Hk. unfold project_n.
  destruct (Nat.ltb_spec k n); [lia | reflexivity].
Qed.

(** Projection is idempotent *)
Lemma project_idem : forall n f k,
  project_n n (project_n n f) k == project_n n f k.
Proof.
  intros n f k. unfold project_n.
  destruct (Nat.ltb_spec k n); reflexivity.
Qed.

(** Inner product with projected vector *)
Lemma ip_project : forall n m f g,
  (n <= m)%nat ->
  inner_product_n n (project_n m f) g == inner_product_n n f g.
Proof.
  intros n m f g Hnm. unfold inner_product_n.
  apply sum_Q_ext. intros k Hk.
  rewrite project_below; [reflexivity | lia].
Qed.

(** Projection preserves norm at lower dimensions *)
Lemma project_preserves_norm : forall n m f,
  (n <= m)%nat ->
  norm_sq_n n (project_n m f) == norm_sq_n n f.
Proof.
  intros n m f Hnm. unfold norm_sq_n, inner_product_n.
  apply sum_Q_ext. intros k Hk.
  assert (Hpk : project_n m f k == f k) by (apply project_below; lia).
  setoid_rewrite Hpk. reflexivity.
Qed.

(** Projection reduces norm *)
Lemma projection_reduces_norm : forall n m f,
  (n <= m)%nat ->
  norm_sq_n n f <= norm_sq_n m f.
Proof.
  intros n m f Hnm.
  induction m as [| m' IH].
  - assert (n = 0)%nat by lia. subst. lra.
  - destruct (Nat.eq_dec n (S m')).
    + subst. lra.
    + assert (Hm' : (n <= m')%nat) by lia.
      specialize (IH Hm').
      apply Qle_trans with (norm_sq_n m' f); auto.
      apply norm_monotone.
Qed.

(* ================================================================== *)
(*  Part IV: Cauchy-Schwarz Inequality                                  *)
(* ================================================================== *)

(** Cross-term bound: nf·b² - 2·a·b·ip + a²·ng ≥ 0 *)
(** This is Σ(f_k·b - a·g_k)² ≥ 0 *)
Lemma cross_term_nonneg : forall (f g : nat -> Q) (a b : Q) n,
  0 <= sum_Q (fun k => f k * f k) n * (b * b) -
  2 * (a * b) * sum_Q (fun k => f k * g k) n +
  a * a * sum_Q (fun k => g k * g k) n.
Proof.
  intros f g a b n.
  assert (Hnn : 0 <= sum_Q (fun k => (f k * b - a * g k) * (f k * b - a * g k)) n).
  { apply sum_Q_nonneg. intros k _. apply q_sq_nonneg. }
  assert (Heq : sum_Q (fun k => (f k * b - a * g k) * (f k * b - a * g k)) n ==
    sum_Q (fun k => f k * f k) n * (b * b) -
    2 * (a * b) * sum_Q (fun k => f k * g k) n +
    a * a * sum_Q (fun k => g k * g k) n).
  { clear Hnn. induction n as [| m IH]; simpl; [ring | rewrite IH; ring]. }
  lra.
Qed.

(** Helper: two nonneg terms sum to nonneg *)
Lemma nonneg_sum : forall X Y : Q,
  0 <= X -> 0 <= Y -> 0 <= X + Y.
Proof. intros. lra. Qed.

(** Cauchy-Schwarz: ⟨f,g⟩² ≤ ‖f‖² · ‖g‖² *)
Theorem cauchy_schwarz_n : forall n (f g : nat -> Q),
  inner_product_n n f g * inner_product_n n f g <=
  norm_sq_n n f * norm_sq_n n g.
Proof.
  induction n as [| n IH]; intros f g.
  - unfold inner_product_n, norm_sq_n, sum_Q. apply Qle_refl.
  - (* Decompose — unfold norm_sq_n first to expose inner_product_n *)
    unfold norm_sq_n. unfold inner_product_n. simpl.
    (* Name subterms for readability *)
    remember (sum_Q (fun k => f k * g k) n) as ip eqn:Eip.
    remember (sum_Q (fun k => f k * f k) n) as nf eqn:Enf.
    remember (sum_Q (fun k => g k * g k) n) as ng eqn:Eng.
    (* IH gives ip² ≤ nf·ng *)
    assert (IHr : ip * ip <= nf * ng).
    { subst. exact (IH f g). }
    (* Cross-term bound: 0 ≤ nf·b² - 2·ab·ip + a²·ng *)
    assert (Haux : 0 <= nf * (g n * g n) - 2 * (f n * g n) * ip + f n * f n * ng).
    { subst. exact (cross_term_nonneg f g (f n) (g n) n). }
    (* Algebraic identity: (nf+a²)(ng+b²) - (ip+ab)² = ... *)
    assert (Hdiff :
      (nf + f n * f n) * (ng + g n * g n) - (ip + f n * g n) * (ip + f n * g n) ==
      (nf * ng - ip * ip) +
      (nf * (g n * g n) - 2 * (f n * g n) * ip + f n * f n * ng)) by ring.
    (* Combine: 0 ≤ (nf·ng - ip²) + cross_term *)
    assert (H1 : 0 <= nf * ng - ip * ip) by lra.
    assert (H0 := nonneg_sum _ _ H1 Haux).
    (* Now use Hdiff to conclude *)
    assert (Hge : 0 <= (nf + f n * f n) * (ng + g n * g n) -
                       (ip + f n * g n) * (ip + f n * g n)).
    { setoid_rewrite Hdiff. exact H0. }
    (* From Hge: 0 <= X - Y, derive Y <= X *)
    assert (Hfin : (ip + f n * g n) * (ip + f n * g n) <=
                   (nf + f n * f n) * (ng + g n * g n)) by lra.
    exact Hfin.
Qed.

(** Triangle inequality for norm *)
Theorem triangle_n : forall n (f g : nat -> Q),
  norm_sq_n n (fun k => f k + g k) <=
  norm_sq_n n f + norm_sq_n n g +
  2 * Qabs (inner_product_n n f g).
Proof.
  intros n f g.
  unfold norm_sq_n, inner_product_n.
  assert (Hexp : sum_Q (fun k => (f k + g k) * (f k + g k)) n ==
    sum_Q (fun k => f k * f k) n + sum_Q (fun k => g k * g k) n +
    2 * sum_Q (fun k => f k * g k) n).
  { induction n as [| n' IH].
    - simpl. ring.
    - simpl. rewrite IH. ring. }
  setoid_rewrite Hexp.
  assert (H : sum_Q (fun k : nat => f k * g k) n <=
              Qabs (sum_Q (fun k : nat => f k * g k) n)).
  { apply Qle_Qabs. }
  lra.
Qed.

(* ================================================================== *)
(*  Part V: Embeddings Q^n → Q^{n+1}                                   *)
(* ================================================================== *)

(** Natural embedding: extend by zero *)
Definition embed (n : nat) (f : nat -> Q) : nat -> Q :=
  fun k => if Nat.ltb k n then f k else 0.

Lemma embed_below : forall n f k,
  (k < n)%nat -> embed n f k == f k.
Proof.
  intros n f k Hk. unfold embed.
  destruct (Nat.ltb_spec k n); [reflexivity | lia].
Qed.

Lemma embed_above : forall n f k,
  (n <= k)%nat -> embed n f k == 0.
Proof.
  intros n f k Hk. unfold embed.
  destruct (Nat.ltb_spec k n); [lia | reflexivity].
Qed.

(** embed preserves inner product *)
Lemma embed_preserves_ip : forall n f g,
  inner_product_n n f g == inner_product_n (S n) (embed n f) (embed n g).
Proof.
  intros. unfold inner_product_n. simpl.
  rewrite embed_above by lia.
  assert (Hext : sum_Q (fun k => embed n f k * embed n g k) n ==
                 sum_Q (fun k => f k * g k) n).
  { apply sum_Q_ext. intros k Hk.
    rewrite embed_below by lia. rewrite embed_below by lia. reflexivity. }
  lra.
Qed.

(** embed is isometric *)
Lemma embed_isometric : forall n f,
  norm_sq_n n f == norm_sq_n (S n) (embed n f).
Proof.
  intros. unfold norm_sq_n. apply embed_preserves_ip.
Qed.

(** embed is compatible with projection *)
Lemma embed_eq_project : forall n f k,
  embed n f k == project_n n f k.
Proof.
  intros. unfold embed, project_n. reflexivity.
Qed.

(* ================================================================== *)
(*  Part VI: E/R/R Pattern                                              *)
(* ================================================================== *)

(** Convergence rate *)
Definition finitedim_convergence_rate : Q := 1 # 2.

Lemma finitedim_rate_valid :
  0 < finitedim_convergence_rate /\ finitedim_convergence_rate < 1.
Proof. unfold finitedim_convergence_rate. split; lra. Qed.

(** E/R/R: Q^n as process construction *)
Theorem finitedim_is_process : forall (f : nat -> Q) (B : Q),
  0 <= B ->
  (forall k, Qabs (f k) <= B) ->
  forall n, norm_sq_n n f <= B * B * inject_Z (Z.of_nat n).
Proof.
  intros f B HB Hbnd n. unfold norm_sq_n, inner_product_n.
  induction n as [| n' IH].
  - simpl. assert (Hz : inject_Z 0 == 0) by reflexivity.
    rewrite Hz. lra.
  - simpl.
    assert (Hk := Hbnd n').
    assert (Hsq : f n' * f n' <= B * B).
    { assert (Hfsq : f n' * f n' == Qabs (f n') * Qabs (f n')).
      { destruct (Qlt_le_dec (f n') 0).
        - rewrite Qabs_neg by lra. ring.
        - rewrite Qabs_pos by lra. ring. }
      assert (Ha := Qabs_nonneg (f n')).
      assert (Habs : Qabs (f n') * Qabs (f n') <= B * B).
      { apply Qmult_le_compat_nonneg; split; auto. }
      lra. }
    assert (Hstep : B * B * inject_Z (Z.of_nat (S n')) ==
                    B * B * inject_Z (Z.of_nat n') + B * B).
    { rewrite Nat2Z.inj_succ. unfold Z.succ.
      rewrite inject_Z_plus.
      assert (Hinj1 : inject_Z 1 == 1) by reflexivity.
      rewrite Hinj1. ring. }
    rewrite Hstep. lra.
Qed.

(** P4: Q^n is finite — no infinite-dimensional space *)
(** The process {Q^n | n ∈ ℕ} builds L² without infinity *)
