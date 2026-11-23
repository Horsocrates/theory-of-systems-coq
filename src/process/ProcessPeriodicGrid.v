(** * ProcessPeriodicGrid.v — The periodic grid as a property of the profile; Green's
      formula and the Laplacian bound with their boundary terms (Part IX, chapters 1-2)

    Elements: grid functions u : nat -> Q; a period N; the values u_j at all natural
              numbers j; finite sums over the nodes 0..N-1.
    Roles:    full periodicity u_{j+N} = u_j = the role "the grid is a circle of N
              nodes"; the two equalities u_N = u_0, u_{N+1} = u_1 = what Green's
              formula actually uses; the boundary terms = what remains without them.
    Rules:    full periodicity is preserved by linear combinations and by shifts of
              the index; it implies the premises of the lemmas of FiniteDifference.v
              and ProcessPDEGreen.v; without a condition at the ends Green's formula
              and the Laplacian bound hold with explicit boundary terms.

    ============ E/R/R разбор ============
      Rules (L5): u (j + N) == u j при всех j — полная периодичность; из неё —
                  равенства на краях, формула Грина, оценка лапласиана; без условий
                  на края — те же формулы с граничными членами.
      Roles (L4): период N — роль-замыкание сетки в круг; граничные члены —
                  роль-поток через края; условие Дирихле — роль-закрытый край.
      Elements  : рациональные значения в узлах, конечные суммы (L1 + P4).
    ДИАГНОСТИКА P4: профиль — правило, дающее значение в каждом натуральном узле;
    «периодическая сетка» — свойство этого правила, а не завершённый объект; все
    суммы — по N узлам.

    PROVED (all closed under the global context):
      - full periodicity [gperiodic]: its consequences at the ends, by multiples of
        the period, reduction modulo N; the periodic extension [pext] of any profile
        is periodic and agrees with the profile on the nodes 0..N-1;
      - it is preserved by linear combinations and by the shift of the index;
      - sums over shifted nodes ([gperiodic_sum_shift], [gperiodic_sum_pred]);
      - Green's formula and the Laplacian bound under full periodicity
        ([gperiodic_green], [gperiodic_lap_bound]);
      - both for EVERY grid function, with explicit boundary terms
        ([green_boundary], [lap_norm_bound_boundary]); zero ends
        ([green_zero_boundary]);
      - the conditions are needed: the bound fails without its premise
        ([lap_bound_not_unconditional]); the single equality u_N = u_0 does not
        give Green's formula ([green_not_from_is_periodic]); the constant 4 is
        attained ([lap_bound_sharp]).

    NOT claimed: any statement about a continuous Laplacian, integrals or limits of
    refinement; boundary conditions other than periodic and zero ends.

    STATUS: 27 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa Arith.
From ToS Require Import navier_stokes.GridFunction.
From ToS Require Import navier_stokes.FiniteDifference.
From ToS Require Import process.ProcessPDEGreen.

Open Scope Q_scope.

(* ===================================================================== *)
(*  1. Full periodicity                                                    *)
(* ===================================================================== *)

(** The profile is periodic with the period N: u_{j+N} = u_j for every j. *)
Definition gperiodic (N : nat) (u : grid_fn) : Prop :=
  forall j, u (j + N)%nat == u j.

Lemma gperiodic_N0 : forall N u, gperiodic N u -> u N == u 0%nat.
Proof. intros N u H. exact (H 0%nat). Qed.

Lemma gperiodic_SN : forall N u, gperiodic N u -> u (S N) == u 1%nat.
Proof. intros N u H. exact (H 1%nat). Qed.

(** It implies the one-equation notion of FiniteDifference.v. *)
Lemma gperiodic_is_periodic : forall N u, gperiodic N u -> is_periodic N u.
Proof. intros N u H. exact (H 0%nat). Qed.

Lemma gperiodic_mult : forall N u m j, gperiodic N u -> u (j + m * N)%nat == u j.
Proof.
  intros N u m j H. induction m as [|m IH].
  - replace (j + 0 * N)%nat with j by lia. reflexivity.
  - replace (j + S m * N)%nat with ((j + m * N) + N)%nat by lia.
    rewrite (H (j + m * N)%nat). exact IH.
Qed.

(** Every value is the value at a node of the grid 0..N-1. *)
Lemma gperiodic_mod : forall N u j, (0 < N)%nat -> gperiodic N u ->
  u j == u (j mod N)%nat.
Proof.
  intros N u j HN H.
  assert (E : j = (j mod N + (j / N) * N)%nat).
  { pose proof (Nat.div_mod_eq j N). lia. }
  transitivity (u (j mod N + (j / N) * N)%nat).
  - rewrite <- E. reflexivity.
  - apply gperiodic_mult. exact H.
Qed.

(** The periodic extension of a profile given on the nodes 0..N-1. *)
Definition pext (N : nat) (u : grid_fn) : grid_fn := fun j => u (j mod N)%nat.

Lemma pext_gperiodic : forall N u, (0 < N)%nat -> gperiodic N (pext N u).
Proof.
  intros N u HN j. unfold pext.
  replace ((j + N) mod N)%nat with (j mod N)%nat; [ reflexivity | ].
  replace (j + N)%nat with (j + 1 * N)%nat by lia.
  symmetry. apply Nat.Div0.mod_add.
Qed.

Lemma pext_agrees : forall N u j, (j < N)%nat -> pext N u j = u j.
Proof.
  intros N u j Hj. unfold pext. rewrite Nat.mod_small; [ reflexivity | exact Hj ].
Qed.

(** A periodic profile is its own periodic extension. *)
Lemma gperiodic_pext : forall N u j, (0 < N)%nat -> gperiodic N u ->
  pext N u j == u j.
Proof.
  intros N u j HN H. unfold pext. symmetry. apply gperiodic_mod; assumption.
Qed.

(* ===================================================================== *)
(*  2. What preserves periodicity                                          *)
(* ===================================================================== *)

Lemma gperiodic_const : forall N c, gperiodic N (fun _ => c).
Proof. intros N c j. reflexivity. Qed.

Lemma gperiodic_linear : forall N a b (f g : grid_fn),
  gperiodic N f -> gperiodic N g -> gperiodic N (fun k => a * f k + b * g k).
Proof.
  intros N a b f g Hf Hg j. cbv beta. rewrite (Hf j), (Hg j). reflexivity.
Qed.

Lemma gperiodic_shift : forall N u, gperiodic N u -> gperiodic N (fun k => u (S k)).
Proof. intros N u H j. cbv beta. exact (H (S j)). Qed.

(** The cyclic predecessor of the grid respects the period. *)
Lemma gperiodic_ppred : forall N u j, (0 < N)%nat -> gperiodic N u ->
  u (ppred N (j + N)) == u (ppred N j).
Proof.
  intros N u j HN H. destruct j as [|k].
  - destruct N as [|m]; [ lia | ]. cbn [Nat.add ppred Nat.pred]. reflexivity.
  - cbn [Nat.add ppred]. apply H.
Qed.

Lemma gperiodic_pred : forall N u, (0 < N)%nat -> gperiodic N u ->
  gperiodic N (fun k => u (ppred N k)).
Proof. intros N u HN H j. cbv beta. apply gperiodic_ppred; assumption. Qed.

(* ===================================================================== *)
(*  3. Sums over shifted nodes                                             *)
(* ===================================================================== *)

Lemma gperiodic_sum_shift : forall N u, gperiodic N u ->
  sum_Q_ns (fun j => u (S j)) N == sum_Q_ns u N.
Proof.
  intros N u H.
  transitivity (sum_Q_ns (fun j => u j) N).
  - exact (sum_ns_shift_periodic (fun k => u k) N (H 0%nat)).
  - apply sum_ns_ext. intros; reflexivity.
Qed.

(** The predecessor shift needs no periodicity: it permutes the nodes 0..N-1. *)
Lemma gperiodic_sum_pred : forall N (u : grid_fn), (0 < N)%nat ->
  sum_Q_ns (fun j => u (ppred N j)) N == sum_Q_ns u N.
Proof.
  intros N u HN.
  transitivity (sum_Q_ns (fun j => u j) N).
  - exact (sum_pred_shift_periodic (fun k => u k) N HN).
  - apply sum_ns_ext. intros; reflexivity.
Qed.

(* ===================================================================== *)
(*  4. Green's formula and the Laplacian bound on the periodic grid        *)
(* ===================================================================== *)

Theorem gperiodic_green : forall N (u : grid_fn), gperiodic N u ->
  sum_Q_ns (fun i => u (S i) * dd u i) N == - gradient_norm_sq N u.
Proof.
  intros N u H. apply green_dirichlet_periodic.
  - exact (H 0%nat).
  - exact (H 1%nat).
Qed.

Theorem gperiodic_lap_bound : forall N (u : grid_fn), gperiodic N u ->
  gf_norm_sq N (dd u) <= 4 * gradient_norm_sq N u.
Proof.
  intros N u H. apply lap_norm_bound. unfold fd.
  assert (H0 : u N == u 0%nat) by exact (H 0%nat).
  assert (H1 : u (S N) == u 1%nat) by exact (H 1%nat).
  lra.
Qed.

(* ===================================================================== *)
(*  5. Every grid function: the boundary terms                             *)
(* ===================================================================== *)

(** Green's formula with the boundary terms, no condition at the ends. *)
Theorem green_boundary : forall N (u : grid_fn),
  sum_Q_ns (fun i => u (S i) * dd u i) N ==
  - gradient_norm_sq N u + (u N * fd u N - u 0%nat * fd u 0%nat).
Proof.
  intros N u.
  pose proof (abel_summation N u (fd u)) as HA.
  assert (Heq : sum_Q_ns (fun i => u (S i) * dd u i) N ==
                sum_Q_ns (fun i => u (S i) * fd (fd u) i) N).
  { apply sum_ns_ext. intros i Hi. rewrite (dd_eq_fd_fd u i). reflexivity. }
  unfold gradient_norm_sq. rewrite Heq. lra.
Qed.

(** Zero values at the ends (the Dirichlet condition): the boundary terms vanish. *)
Corollary green_zero_boundary : forall N (u : grid_fn),
  u 0%nat == 0 -> u N == 0 ->
  sum_Q_ns (fun i => u (S i) * dd u i) N == - gradient_norm_sq N u.
Proof.
  intros N u H0 HN. rewrite green_boundary.
  assert (E : u N * fd u N - u 0%nat * fd u 0%nat == 0).
  { rewrite H0, HN. ring. }
  rewrite E. ring.
Qed.

(** The Laplacian bound for every grid function, with the boundary term. *)
Theorem lap_norm_bound_boundary : forall N (u : grid_fn),
  gf_norm_sq N (dd u) <=
  4 * gradient_norm_sq N u + 2 * (fd u N * fd u N - fd u 0%nat * fd u 0%nat).
Proof.
  intros N u.
  rewrite lap_norm_eq_grad_grad. unfold gradient_norm_sq.
  set (w := fd u).
  apply Qle_trans with
    (sum_Q_ns (fun i => 2*(w (S i) * w (S i)) + 2*(w i * w i)) N).
  - apply sum_ns_le. intros i Hi. unfold fd. apply sq_sub_bound.
  - rewrite sum_ns_add.
    rewrite (sum_ns_scale 2 (fun i => w (S i) * w (S i)) N).
    rewrite (sum_ns_scale 2 (fun i => w i * w i) N).
    pose proof (sum_ns_shift_S (fun k => w k * w k) N) as Hshift.
    cbn beta in Hshift. rewrite Hshift. lra.
Qed.

(* ===================================================================== *)
(*  6. The conditions are needed                                           *)
(* ===================================================================== *)

(** u = (0, 0, 1, 0, ...): the premise fd u N == fd u 0 fails for N = 1. *)
Definition cex_lap : grid_fn := fun j => if Nat.eqb j 2 then 1 else 0.

Lemma lap_bound_fails_without_condition :
  4 * gradient_norm_sq 1 cex_lap < gf_norm_sq 1 (dd cex_lap).
Proof. vm_compute. reflexivity. Qed.

Theorem lap_bound_not_unconditional :
  ~ (forall N (u : grid_fn), gf_norm_sq N (dd u) <= 4 * gradient_norm_sq N u).
Proof.
  intro Hall. apply (Qlt_not_le _ _ lap_bound_fails_without_condition). apply Hall.
Qed.

(** u = (1, 1, 0, 1, ...): "periodic" in the one-equation sense (u 1 == u 0),
    yet the second equality u 2 == u 1 fails, and so does Green's identity. *)
Definition cex_green : grid_fn := fun j => if Nat.eqb j 2 then 0 else 1.

Lemma cex_green_is_periodic : is_periodic 1 cex_green.
Proof. unfold is_periodic. vm_compute. reflexivity. Qed.

Lemma green_fails_with_one_equation :
  ~ (sum_Q_ns (fun i => cex_green (S i) * dd cex_green i) 1
     == - gradient_norm_sq 1 cex_green).
Proof. vm_compute. intro E. discriminate E. Qed.

Theorem green_not_from_is_periodic :
  ~ (forall N (u : grid_fn), is_periodic N u ->
       sum_Q_ns (fun i => u (S i) * dd u i) N == - gradient_norm_sq N u).
Proof.
  intro Hall. apply green_fails_with_one_equation. apply Hall.
  exact cex_green_is_periodic.
Qed.

(** The constant 4 is attained: the saw-tooth profile 0,1,0,1,... on two nodes. *)
Definition zigzag : grid_fn := fun j => if Nat.even j then 0 else 1.

Lemma zigzag_gperiodic : gperiodic 2%nat zigzag.
Proof.
  intro j. unfold zigzag.
  replace (j + 2)%nat with (S (S j)) by lia. cbn [Nat.even]. reflexivity.
Qed.

Lemma lap_bound_sharp :
  gf_norm_sq 2 (dd zigzag) == 4 * gradient_norm_sq 2 zigzag.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions gperiodic_green.
Print Assumptions lap_norm_bound_boundary.
