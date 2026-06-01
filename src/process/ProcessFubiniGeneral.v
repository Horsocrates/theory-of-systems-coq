(** * ProcessFubiniGeneral.v — Fubini equality on a general N×M grid (F-1, Part VI)

    Elements: rational grid samples f(i,j); finite double sums
    Roles:    iterated integral (either order) as a process value
    Rules:    double-sum commutation Σᵢⱼ = Σⱼᵢ (discrete Fubini), at every refinement

    Continuous Fubini, honestly. The EQUALITY of the two iterated integrals
        ∫(∫f dx)dy   =   ∫(∫f dy)dx
    is, at the level of any finite grid, just the commutation of a finite DOUBLE
    SUM — and that holds EXACTLY at every refinement, with NO limit needed. So for
    a function f sampled on a refining grid (a continuous f included), the two
    iterated Riemann sums agree at every stage, hence coincide as processes.

    V.7 proved Fubini only for a FIXED, small step grid (FubiniProcess.v:
    fubini_step on a list of rectangles). Here we prove the general N×M version
    for an arbitrary grid-sampled function — q_sum_swap and fubini_iterated_eq —
    so the Fubini EQUALITY closes for continuous integrands sampled on grids.

    HONEST RESIDUE (F-1, as V.7 §7.5 stated): connecting the iterated/grid sums to
    the DOUBLE INTEGRAL as a convergent limit — i.e. that the grid sums of a
    continuous f converge — needs uniform continuity on a compact (Heine–Borel)
    and is Q-limited; that layer is NOT assembled here. What IS closed here is the
    order-of-integration EQUALITY, generally and constructively.

    ============ E/R/R разбор ============
      Rules (L5): коммутация двойной суммы (Фубини) — на каждой стадии, без предела.
      Roles (L4): повторный интеграл (любой порядок) = роль-значение; «порядок
                  интегрирования» = роль-режим, которую правило объявляет несущественной.
      Elements  : сеточные выборки f(i,j), конечные суммы (L1+P4).
    ДИАГНОСТИКА: «порядок не важен» — Правило о конечном процессе, верное на каждой
    стадии; сходимость сеток к двойному интегралу (завершённое значение) — P4-граница.

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: May 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.   (* q_sum *)

Open Scope Q_scope.

(* ===================================================================== *)
(*  Finite-sum helpers                                                   *)
(* ===================================================================== *)

Lemma q_sum_zero : forall (N : nat), q_sum (fun _ => 0) N == 0.
Proof. induction N as [|k IH]; cbn [q_sum]; [ reflexivity | rewrite IH; ring ]. Qed.

Lemma q_sum_ext : forall (g h : nat -> Q) (N : nat),
  (forall i, g i == h i) -> q_sum g N == q_sum h N.
Proof.
  intros g h N H. induction N as [|k IH]; cbn [q_sum].
  - reflexivity.
  - rewrite IH. rewrite (H k). reflexivity.
Qed.

Lemma q_sum_plus : forall (a b : nat -> Q) (N : nat),
  q_sum (fun i => a i + b i) N == q_sum a N + q_sum b N.
Proof. intros a b N. induction N as [|k IH]; cbn [q_sum]; [ ring | rewrite IH; ring ]. Qed.

Lemma q_sum_scale : forall (c : Q) (g : nat -> Q) (N : nat),
  q_sum (fun i => c * g i) N == c * q_sum g N.
Proof. intros c g N. induction N as [|k IH]; cbn [q_sum]; [ ring | rewrite IH; ring ]. Qed.

(* ===================================================================== *)
(*  Iterated double sums and the discrete Fubini (sum-swap).             *)
(* ===================================================================== *)

Definition dsum_xy (f : nat -> nat -> Q) (N M : nat) : Q :=
  q_sum (fun i => q_sum (fun j => f i j) M) N.

Definition dsum_yx (f : nat -> nat -> Q) (N M : nat) : Q :=
  q_sum (fun j => q_sum (fun i => f i j) N) M.

(** Discrete Fubini: a finite double sum commutes (general N×M). *)
Theorem q_sum_swap : forall (f : nat -> nat -> Q) (N M : nat),
  dsum_xy f N M == dsum_yx f N M.
Proof.
  intros f N M. unfold dsum_xy, dsum_yx.
  induction N as [|k IH].
  - (* N = 0: LHS = 0; RHS = Σⱼ (Σᵢ<0 ...) = Σⱼ 0 = 0 *)
    transitivity (0:Q).
    + reflexivity.
    + symmetry. transitivity (q_sum (fun _ : nat => 0) M).
      * apply q_sum_ext. intro j. reflexivity.
      * apply q_sum_zero.
  - (* step *)
    change (q_sum (fun i => q_sum (fun j => f i j) M) (S k))
      with (q_sum (fun i => q_sum (fun j => f i j) M) k + q_sum (fun j => f k j) M).
    change (q_sum (fun j => q_sum (fun i => f i j) (S k)) M)
      with (q_sum (fun j => q_sum (fun i => f i j) k + f k j) M).
    assert (Hsplit :
      q_sum (fun j => q_sum (fun i => f i j) k + f k j) M
      == q_sum (fun j => q_sum (fun i => f i j) k) M + q_sum (fun j => f k j) M)
      by apply q_sum_plus.
    rewrite Hsplit, IH. reflexivity.
Qed.

(* ===================================================================== *)
(*  Iterated Riemann integrals on a grid, and their equality.             *)
(*    ∫(∫f dx)dy = wx·Σᵢ(wy·Σⱼ f(i,j)) ;  ∫(∫f dy)dx = wy·Σⱼ(wx·Σᵢ f(i,j)) *)
(* ===================================================================== *)

Definition iter_xy (f : nat -> nat -> Q) (wx wy : Q) (N M : nat) : Q :=
  wx * q_sum (fun i => wy * q_sum (fun j => f i j) M) N.

Definition iter_yx (f : nat -> nat -> Q) (wx wy : Q) (N M : nat) : Q :=
  wy * q_sum (fun j => wx * q_sum (fun i => f i j) N) M.

(** Continuous-Fubini EQUALITY (general grid): iterated integrals agree. *)
Theorem fubini_iterated_eq : forall f wx wy N M,
  iter_xy f wx wy N M == iter_yx f wx wy N M.
Proof.
  intros f wx wy N M. unfold iter_xy, iter_yx.
  assert (Hx : q_sum (fun i => wy * q_sum (fun j => f i j) M) N == wy * dsum_xy f N M).
  { unfold dsum_xy. apply q_sum_scale. }
  assert (Hy : q_sum (fun j => wx * q_sum (fun i => f i j) N) M == wx * dsum_yx f N M).
  { unfold dsum_yx. apply q_sum_scale. }
  rewrite Hx, Hy.
  rewrite (q_sum_swap f N M).
  ring.
Qed.

(** Process form: at every refinement n (N=M=n) the two iterated integrals
    coincide — the iterated-integral processes are equal pointwise, hence
    process-equivalent, with NO limit needed for the equality. *)
Corollary fubini_iterated_process_eq : forall f wx wy n,
  iter_xy f wx wy n n == iter_yx f wx wy n n.
Proof. intros f wx wy n. apply fubini_iterated_eq. Qed.

(* Computational sanity check: a 2×2 grid, f(i,j) explicit. *)
Example fubini_2x2_concrete :
  let f := fun i j => if Nat.eqb i 0 then (if Nat.eqb j 0 then 1 else 2)
                      else (if Nat.eqb j 0 then 3 else 4) in
  iter_xy f 1 1 2 2 == iter_yx f 1 1 2 2.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions fubini_iterated_eq.
