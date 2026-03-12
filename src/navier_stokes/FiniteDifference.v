(* ========================================================================= *)
(*        FINITE DIFFERENCES — Discrete Derivatives on Grid                    *)
(*                                                                            *)
(*  Forward difference: (df)(i) = f(i+1) - f(i)                              *)
(*  Second difference:  (d2f)(i) = f(i+2) - 2f(i+1) + f(i)                  *)
(*  Abel summation: S df*g + S f(+1)*dg = f(N)g(N) - f(0)g(0)               *)
(*                                                                            *)
(*  STATUS: ~42 Qed, 0 Admitted                                              *)
(*  Author: Horsocrates | Date: March 2026                                   *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.
From ToS Require Import navier_stokes.GridFunction.
Open Scope Q_scope.

(* ========================================================================= *)
(*  PART I: Forward Difference                                                *)
(* ========================================================================= *)

(** Forward difference: (df)(i) = f(i+1) - f(i) *)
Definition fd (f : grid_fn) : grid_fn := fun i => f (S i) - f i.

Lemma fd_zero : forall i, fd gf_zero i == 0.
Proof. intros. unfold fd, gf_zero. lra. Qed.

Lemma fd_const : forall c i, fd (gf_const c) i == 0.
Proof. intros. unfold fd, gf_const. lra. Qed.

Lemma fd_add : forall (f g : grid_fn) i,
  fd (gf_add f g) i == fd f i + fd g i.
Proof. intros. unfold fd, gf_add. lra. Qed.

Lemma fd_scale : forall c (f : grid_fn) i,
  fd (gf_scale c f) i == c * fd f i.
Proof. intros. unfold fd, gf_scale. lra. Qed.

Lemma fd_sub : forall (f g : grid_fn) i,
  fd (gf_sub f g) i == fd f i - fd g i.
Proof. intros. unfold fd, gf_sub. lra. Qed.

Lemma fd_neg : forall (f : grid_fn) i,
  fd (fun j => - f j) i == - fd f i.
Proof. intros. unfold fd. lra. Qed.

Lemma fd_linear : forall a b (f g : grid_fn) i,
  fd (fun j => a * f j + b * g j) i == a * fd f i + b * fd g i.
Proof. intros. unfold fd. lra. Qed.

(** Telescoping sum: sum of forward differences = endpoint difference *)
Lemma sum_fd : forall (f : grid_fn) N,
  sum_Q_ns (fd f) N == f N - f 0%nat.
Proof.
  intros f N. unfold fd.
  destruct N as [|n].
  - simpl. lra.
  - apply sum_ns_telescope. lia.
Qed.

(** For periodic functions: total forward difference vanishes *)
Lemma sum_fd_periodic : forall (f : grid_fn) N,
  f N == f 0%nat ->
  sum_Q_ns (fd f) N == 0.
Proof.
  intros f N Hper. rewrite sum_fd. lra.
Qed.

(* ========================================================================= *)
(*  PART II: Second Difference (Discrete Laplacian)                           *)
(* ========================================================================= *)

(** Second difference: d2f(i) = f(i+2) - 2f(i+1) + f(i) *)
Definition dd (f : grid_fn) : grid_fn :=
  fun i => f (S (S i)) - 2 * f (S i) + f i.

Lemma dd_eq_fd_fd : forall (f : grid_fn) i,
  dd f i == fd (fd f) i.
Proof. intros. unfold dd, fd. lra. Qed.

Lemma dd_zero : forall i, dd gf_zero i == 0.
Proof. intros. unfold dd, gf_zero. lra. Qed.

Lemma dd_const : forall c i, dd (gf_const c) i == 0.
Proof. intros. unfold dd, gf_const. lra. Qed.

Lemma dd_add : forall (f g : grid_fn) i,
  dd (gf_add f g) i == dd f i + dd g i.
Proof. intros. unfold dd, gf_add. lra. Qed.

Lemma dd_scale : forall c (f : grid_fn) i,
  dd (gf_scale c f) i == c * dd f i.
Proof. intros. unfold dd, gf_scale. lra. Qed.

Lemma dd_sub : forall (f g : grid_fn) i,
  dd (gf_sub f g) i == dd f i - dd g i.
Proof. intros. unfold dd, gf_sub. lra. Qed.

Lemma dd_linear : forall a b (f g : grid_fn) i,
  dd (fun j => a * f j + b * g j) i == a * dd f i + b * dd g i.
Proof. intros. unfold dd. lra. Qed.

(* ========================================================================= *)
(*  PART III: Gradient Norm                                                   *)
(* ========================================================================= *)

(** Gradient norm squared: ||df||^2 = S (fd f i)^2 *)
Definition gradient_norm_sq (N : nat) (f : grid_fn) : Q :=
  sum_Q_ns (fun i => fd f i * fd f i) N.

Lemma gradient_nonneg : forall N (f : grid_fn),
  0 <= gradient_norm_sq N f.
Proof.
  intros. unfold gradient_norm_sq.
  apply sum_ns_nonneg. intros. apply Qsq_nonneg.
Qed.

Lemma gradient_zero_fn : forall N,
  gradient_norm_sq N gf_zero == 0.
Proof.
  intros. unfold gradient_norm_sq.
  induction N as [|n IH]; simpl; [lra |].
  rewrite fd_zero. rewrite IH. lra.
Qed.

Lemma gradient_const : forall N c,
  gradient_norm_sq N (gf_const c) == 0.
Proof.
  intros. unfold gradient_norm_sq.
  induction N as [|n IH]; simpl; [lra |].
  rewrite fd_const. rewrite IH. lra.
Qed.

Lemma gradient_scale : forall N c (f : grid_fn),
  gradient_norm_sq N (gf_scale c f) == c * c * gradient_norm_sq N f.
Proof.
  intros. unfold gradient_norm_sq.
  rewrite <- sum_ns_scale.
  apply sum_ns_ext. intros. rewrite fd_scale. lra.
Qed.

Lemma gradient_add_bound : forall N (f g : grid_fn),
  gradient_norm_sq N (gf_add f g) <=
  2 * (gradient_norm_sq N f + gradient_norm_sq N g).
Proof.
  intros. unfold gradient_norm_sq.
  induction N as [|n IH]; [simpl; lra |].
  simpl sum_Q_ns.
  assert (Hfd : fd (gf_add f g) n == fd f n + fd g n) by apply fd_add.
  assert (Hsq : 0 <= (fd f n - fd g n) * (fd f n - fd g n)) by apply Qsq_nonneg.
  assert (Hterm : fd (gf_add f g) n * fd (gf_add f g) n <=
                  2 * (fd f n * fd f n + fd g n * fd g n)).
  { rewrite Hfd. lra. }
  lra.
Qed.

(* ========================================================================= *)
(*  PART IV: Abel Summation (Discrete Integration by Parts)                   *)
(* ========================================================================= *)

(** Discrete product rule:
    f(i+1)g(i+1) - f(i)g(i) = df(i)*g(i) + f(i+1)*dg(i) *)
Lemma discrete_product_rule : forall (f g : grid_fn) i,
  f (S i) * g (S i) - f i * g i == fd f i * g i + f (S i) * fd g i.
Proof. intros. unfold fd. lra. Qed.

(** Abel summation / summation by parts:
    sum df*g + sum f(+1)*dg = f(N)g(N) - f(0)g(0) *)
Theorem abel_summation : forall N (f g : grid_fn),
  sum_Q_ns (fun i => fd f i * g i) N +
  sum_Q_ns (fun i => f (S i) * fd g i) N ==
  f N * g N - f 0%nat * g 0%nat.
Proof.
  intros N f g. induction N as [|n IH].
  - simpl. lra.
  - simpl sum_Q_ns.
    assert (Hpr := discrete_product_rule f g n).
    lra.
Qed.

(** For periodic functions: boundary terms cancel *)
Theorem abel_periodic : forall N (f g : grid_fn),
  f N == f 0%nat -> g N == g 0%nat ->
  sum_Q_ns (fun i => fd f i * g i) N ==
  - sum_Q_ns (fun i => f (S i) * fd g i) N.
Proof.
  intros N f g Hf Hg.
  assert (HA := abel_summation N f g).
  (* boundary = f(N)*g(N) - f(0)*g(0) = 0 because f,g periodic *)
  assert (Hbd : f N * g N - f 0%nat * g 0%nat == 0).
  { rewrite Hf. rewrite Hg. lra. }
  lra.
Qed.

(** Abel summation applied to f and itself *)
Lemma abel_self : forall N (f : grid_fn),
  sum_Q_ns (fun i => fd f i * f i) N +
  sum_Q_ns (fun i => f (S i) * fd f i) N ==
  f N * f N - f 0%nat * f 0%nat.
Proof. intros. apply abel_summation. Qed.

(** Periodic self-pairing *)
Lemma abel_self_periodic : forall N (f : grid_fn),
  f N == f 0%nat ->
  sum_Q_ns (fun i => fd f i * f i) N ==
  - sum_Q_ns (fun i => f (S i) * fd f i) N.
Proof.
  intros N f Hf. apply abel_periodic; assumption.
Qed.

(* ========================================================================= *)
(*  PART V: Periodicity                                                       *)
(* ========================================================================= *)

Definition is_periodic (N : nat) (f : grid_fn) : Prop := f N == f 0%nat.

Lemma periodic_zero : forall N, is_periodic N gf_zero.
Proof. intros. unfold is_periodic, gf_zero. lra. Qed.

Lemma periodic_const : forall N c, is_periodic N (gf_const c).
Proof. intros. unfold is_periodic, gf_const. lra. Qed.

Lemma periodic_add : forall N (f g : grid_fn),
  is_periodic N f -> is_periodic N g -> is_periodic N (gf_add f g).
Proof.
  intros N f g Hf Hg. unfold is_periodic, gf_add in *.
  rewrite Hf, Hg. lra.
Qed.

Lemma periodic_scale : forall N c (f : grid_fn),
  is_periodic N f -> is_periodic N (gf_scale c f).
Proof.
  intros N c f Hf. unfold is_periodic, gf_scale in *.
  rewrite Hf. lra.
Qed.

Lemma periodic_sub : forall N (f g : grid_fn),
  is_periodic N f -> is_periodic N g -> is_periodic N (gf_sub f g).
Proof.
  intros N f g Hf Hg. unfold is_periodic, gf_sub in *.
  rewrite Hf, Hg. lra.
Qed.

(* ========================================================================= *)
(*  PART VI: Fundamental Theorem of Discrete Calculus                         *)
(* ========================================================================= *)

(** The value at position i is the sum of forward differences:
    f(i) = f(0) + sum_{j<i} df(j) *)
Lemma value_from_diffs : forall (f : grid_fn) i,
  f i == f 0%nat + sum_Q_ns (fd f) i.
Proof. intros f i. rewrite sum_fd. lra. Qed.

(** For f(0) = 0: f(i) = sum of forward differences *)
Lemma value_from_diffs_zero : forall (f : grid_fn) i,
  f 0%nat == 0 -> f i == sum_Q_ns (fd f) i.
Proof. intros f i H0. rewrite value_from_diffs. lra. Qed.

(** Norm of gradient bounds pointwise oscillation:
    (f(N) - f(0))^2 <= N * gradient_norm_sq N f (by Cauchy-Schwarz) *)
Lemma endpoint_bound : forall N (f : grid_fn),
  (f N - f 0%nat) * (f N - f 0%nat) <=
  inject_Z (Z.of_nat N) * gradient_norm_sq N f.
Proof.
  intros N f. unfold gradient_norm_sq.
  rewrite <- sum_fd.
  assert (Hcs := cauchy_schwarz_sq N (gf_const 1) (fd f)).
  unfold gf_norm_sq, gf_inner, gf_const in Hcs.
  (* LHS of CS: (sum 1 * fd f) = sum (fd f) *)
  assert (Hinn : sum_Q_ns (fun i : nat => 1 * fd f i) N ==
                 sum_Q_ns (fd f) N).
  { apply sum_ns_ext. intros. lra. }
  (* norm of const 1: sum 1*1 = N *)
  assert (Hn1 : sum_Q_ns (fun _ : nat => 1 * 1) N ==
                inject_Z (Z.of_nat N)).
  { clear. induction N as [|n IH].
    - simpl. unfold Qeq. simpl. lia.
    - simpl sum_Q_ns.
      assert (H1 : (1 : Q) * 1 == 1) by lra.
      rewrite H1. rewrite IH.
      rewrite Nat2Z.inj_succ. unfold Z.succ.
      unfold Qeq, inject_Z, Qplus. simpl. lia. }
  rewrite Hinn in Hcs. rewrite Hn1 in Hcs. exact Hcs.
Qed.

(** Poincare constant *)
Definition poincare_const (N : nat) : Q :=
  inject_Z (Z.of_nat N).

Lemma poincare_const_nonneg : forall N,
  0 <= poincare_const N.
Proof.
  intros. unfold poincare_const, Qle, inject_Z. simpl. lia.
Qed.

(* ========================================================================= *)
(*  PART VII: Mode Eigenvalues                                                *)
(* ========================================================================= *)

(** Eigenvalue bound for mode k: lambda_k <= 4k^2 *)
Definition mode_eigenvalue_bound (k : nat) : Q :=
  inject_Z (Z.of_nat (4 * k * k)).

Lemma mode_eigen_nonneg : forall k, 0 <= mode_eigenvalue_bound k.
Proof.
  intros. unfold mode_eigenvalue_bound, Qle, inject_Z. simpl. lia.
Qed.

Lemma mode_eigen_zero : mode_eigenvalue_bound 0 == 0.
Proof. unfold mode_eigenvalue_bound. simpl. reflexivity. Qed.

Lemma mode_eigen_one : mode_eigenvalue_bound 1 == 4.
Proof. unfold mode_eigenvalue_bound. simpl. reflexivity. Qed.

Lemma mode_eigen_monotone : forall k,
  mode_eigenvalue_bound k <= mode_eigenvalue_bound (S k).
Proof.
  intros. unfold mode_eigenvalue_bound, Qle, inject_Z. simpl. lia.
Qed.

Lemma mode_eigen_positive : forall k,
  (1 <= k)%nat -> 0 < mode_eigenvalue_bound k.
Proof.
  intros k Hk. unfold mode_eigenvalue_bound, Qlt, inject_Z. simpl. lia.
Qed.

(* ========================================================================= *)
(*  PART VIII: Summary                                                        *)
(* ========================================================================= *)

Theorem finite_difference_main :
  (* 1. Forward difference of constant = 0 *)
  (forall c i, fd (gf_const c) i == 0) /\
  (* 2. Forward difference is linear *)
  (forall a b f g i,
    fd (fun j => a * f j + b * g j) i == a * fd f i + b * fd g i) /\
  (* 3. Telescoping: sum of diffs = endpoint difference *)
  (forall f N, sum_Q_ns (fd f) N == f N - f 0%nat) /\
  (* 4. Abel summation *)
  (forall N f g,
    sum_Q_ns (fun i => fd f i * g i) N +
    sum_Q_ns (fun i => f (S i) * fd g i) N ==
    f N * g N - f 0%nat * g 0%nat) /\
  (* 5. Gradient norm is nonneg *)
  (forall N f, 0 <= gradient_norm_sq N f).
Proof.
  split; [exact fd_const |].
  split; [exact fd_linear |].
  split; [exact sum_fd |].
  split; [exact abel_summation |].
  exact gradient_nonneg.
Qed.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  ~42 Qed, 0 Admitted                                                       *)
(* ========================================================================= *)
