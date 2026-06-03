(** * ProcessPDEGreen.v — Discrete summation by parts / Green's identity and
      Laplacian energy bounds, over ℚ (Part IX, batch D; energy tools)

    Elements: grid functions u : nat→Q, finite sums Σ_{j<N}, nodes
    Roles:    fd = role-gradient, dd = role-Laplacian, Σ = role-integral; the discrete
              Green identity = role-tool relating energy and gradient
    Rules:    summation by parts ⟨u∘S, Δu⟩ = −‖∇u‖² (periodic); ‖Δu‖² ≤ 4‖∇u‖²;
              cyclic shift leaves a periodic sum invariant (forward and predecessor)

    These are the discrete-calculus tools for the PDE-as-process chapters: the discrete
    Green identity (summation by parts) and the Laplacian norm bound are exactly what the
    heat-equation energy estimate (Глава 9.2) needs. Reuses the grid/finite-difference
    infrastructure of the navier_stokes/ cluster.

    ============ E/R/R разбор ============
      Rules (L5): ⟨u∘S, Δu⟩=−‖∇u‖² (суммирование по частям); ‖Δu‖²≤4‖∇u‖²; циклический
                  сдвиг сохраняет периодическую сумму.
      Roles (L4): fd = роль-градиент; dd = роль-лапласиан; формула Грина = роль-инструмент.
      Elements  : грид-функции u:nat→Q, конечные суммы, узлы (L1+P4).
    ДИАГНОСТИКА: дискретное интегрирование по частям над конечной сеткой — над ℚ, 0 аксиом;
    непрерывная формула Грина — роль-предел.

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import navier_stokes.GridFunction.
From ToS Require Import navier_stokes.FiniteDifference.

Open Scope Q_scope.

(* ===================================================================== *)
(*  Cyclic shifts of a finite sum                                          *)
(* ===================================================================== *)

(** Forward shift: Σ_{j<N} g(j+1) = Σ_{j<N} g(j) − g(0) + g(N). *)
Lemma sum_ns_shift_S : forall (g : nat -> Q) N,
  sum_Q_ns (fun j => g (S j)) N == sum_Q_ns g N - g 0%nat + g N.
Proof.
  intros g N. induction N as [|n IH].
  - simpl. lra.
  - rewrite (sum_ns_S (fun j => g (S j)) n). rewrite IH.
    rewrite (sum_ns_S g n). cbn beta. lra.
Qed.

(** Forward shift on a periodic sum: invariant. *)
Lemma sum_ns_shift_periodic : forall (g : nat -> Q) N,
  g N == g 0%nat -> sum_Q_ns (fun j => g (S j)) N == sum_Q_ns g N.
Proof. intros g N H. rewrite sum_ns_shift_S. lra. Qed.

(** Peel the first term off a sum. *)
Lemma sum_ns_peel_front : forall (h : nat -> Q) m,
  sum_Q_ns h (S m) == h 0%nat + sum_Q_ns (fun k => h (S k)) m.
Proof.
  intros h m. induction m as [|m IH].
  - rewrite (sum_ns_S h 0), (sum_ns_0 h), (sum_ns_0 (fun k => h (S k))). lra.
  - rewrite (sum_ns_S h (S m)). rewrite IH.
    rewrite (sum_ns_S (fun k => h (S k)) m). cbn beta. lra.
Qed.

(** Cyclic predecessor on a grid of N points: ppred 0 = N−1, ppred (S k) = k. *)
Definition ppred (N j : nat) : nat := match j with O => Nat.pred N | S k => k end.

(** Predecessor shift on a periodic sum: invariant (the predecessor map is a cyclic
    permutation of {0,…,N−1}). *)
Lemma sum_pred_shift_periodic : forall (g : nat -> Q) N,
  (0 < N)%nat -> sum_Q_ns (fun j => g (ppred N j)) N == sum_Q_ns g N.
Proof.
  intros g N HN. destruct N as [|m]; [lia |].
  rewrite (sum_ns_peel_front (fun j => g (ppred (S m) j)) m).
  (* head term: g (ppred (S m) 0) = g (Nat.pred (S m)) = g m *)
  cbn [ppred]. cbn [Nat.pred].
  (* tail: Σ_{k<m} g (ppred (S m) (S k)) = Σ_{k<m} g k *)
  assert (Htail : sum_Q_ns (fun k => g (ppred (S m) (S k))) m == sum_Q_ns g m).
  { apply sum_ns_ext. intros k Hk. cbn [ppred]. reflexivity. }
  rewrite Htail. rewrite (sum_ns_S g m). lra.
Qed.

(* ===================================================================== *)
(*  Discrete Green's identity (summation by parts)                         *)
(* ===================================================================== *)

(** Discrete Green / Dirichlet identity on a periodic grid:
    Σ_{i<N} u(i+1)·(Δu)(i) = −‖∇u‖².  (∇ = fd, Δ = dd.)
    Periodicity needed: u(N)=u(0) and u(N+1)=u(1). *)
Lemma green_dirichlet_periodic : forall N (u : grid_fn),
  u N == u 0%nat -> u (S N) == u (S 0%nat) ->
  sum_Q_ns (fun i => u (S i) * dd u i) N == - gradient_norm_sq N u.
Proof.
  intros N u H0 H1.
  pose proof (abel_summation N u (fd u)) as HA.
  assert (Hbd : u N * fd u N - u 0%nat * fd u 0%nat == 0).
  { unfold fd. rewrite !H0. rewrite !H1. ring. }
  assert (Heq : sum_Q_ns (fun i => u (S i) * dd u i) N ==
                sum_Q_ns (fun i => u (S i) * fd (fd u) i) N).
  { apply sum_ns_ext. intros i Hi. rewrite (dd_eq_fd_fd u i). reflexivity. }
  unfold gradient_norm_sq. rewrite Heq. lra.
Qed.

(* ===================================================================== *)
(*  Laplacian norm bound: ‖Δu‖² ≤ 4‖∇u‖²                                   *)
(* ===================================================================== *)

Lemma sq_sub_bound : forall a b : Q, (a - b) * (a - b) <= 2*(a*a) + 2*(b*b).
Proof.
  intros a b.
  assert (Hid : 2*(a*a) + 2*(b*b) - (a - b)*(a - b) == (a + b)*(a + b)) by ring.
  assert (H : 0 <= (a + b) * (a + b)) by apply Qsq_nonneg.
  lra.
Qed.

(** ‖Δu‖² = ‖∇(∇u)‖² (since Δ = ∇∘∇). *)
Lemma lap_norm_eq_grad_grad : forall N (u : grid_fn),
  gf_norm_sq N (dd u) == gradient_norm_sq N (fd u).
Proof.
  intros N u. unfold gf_norm_sq, gf_inner, gradient_norm_sq.
  apply sum_ns_ext. intros i Hi. rewrite !(dd_eq_fd_fd u i). reflexivity.
Qed.

(** ★ The discrete Laplacian norm is controlled by the gradient norm (the inverse
    estimate the heat energy bound needs): ‖Δu‖² ≤ 4‖∇u‖² when the gradient is periodic. *)
Lemma lap_norm_bound : forall N (u : grid_fn),
  fd u N == fd u 0%nat ->
  gf_norm_sq N (dd u) <= 4 * gradient_norm_sq N u.
Proof.
  intros N u Hw.
  rewrite lap_norm_eq_grad_grad. unfold gradient_norm_sq.
  set (w := fd u) in *.
  assert (Hw2 : w N == w 0%nat) by exact Hw.
  apply Qle_trans with
    (sum_Q_ns (fun i => 2*(w (S i) * w (S i)) + 2*(w i * w i)) N).
  - apply sum_ns_le. intros i Hi. unfold fd. apply sq_sub_bound.
  - rewrite sum_ns_add.
    rewrite (sum_ns_scale 2 (fun i => w (S i) * w (S i)) N).
    rewrite (sum_ns_scale 2 (fun i => w i * w i) N).
    assert (Hshift : sum_Q_ns (fun i => w (S i) * w (S i)) N ==
                     sum_Q_ns (fun i => w i * w i) N).
    { apply (sum_ns_shift_periodic (fun k => w k * w k) N).
      cbn beta. rewrite !Hw2. reflexivity. }
    rewrite Hshift. lra.
Qed.

Print Assumptions green_dirichlet_periodic.
Print Assumptions lap_norm_bound.
Print Assumptions sum_pred_shift_periodic.
