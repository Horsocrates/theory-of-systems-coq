(** * ProcessWaveEnergy.v — The wave equation as a propagation process on a grid,
      over ℚ (Part IX, batch B; hyperbolic PDE; causality first)

    Elements: rational node values u_j, finite grid, two time levels (u^n, u^{n−1})
    Roles:    (u^n, u^{n−1}) = role-state-pair; s = c²(Δt/Δx)² = role-Courant²; the
              wavefront = role-propagation-boundary; finite speed = role-causality
    Rules:    leapfrog step u^{n+1}_j = 2u^n_j − u^{n−1}_j + s·(u^n_{j+1} − 2u^n_j + u^n_{j−1})
              (central in time and space); FINITE domain of dependence (a node's next value
              depends only on its three neighbours and its own previous value), hence finite
              propagation speed (≤ 1 node per step); CFL c² ≤ 1

    The wave equation PROPAGATES a disturbance. The primary, robust fact is CAUSALITY: the
    update is local, so a disturbance spreads by at most one node per step (finite speed).
    Energy conservation for the leapfrog scheme is design-sensitive; here we establish
    causality (local + finite-speed) and exhibit propagation concretely. The completed
    continuous wave is the role-limit.

    ============ E/R/R разбор ============
      Rules (L5): u^{n+1}=2u^n−u^{n−1}+s·Δ_h u^n; конечная область зависимости; скорость ≤1
                  узла/шаг; CFL c²≤1.
      Roles (L4): (u^n,u^{n−1}) = роль-пара; s = роль-Куранта²; фронт = роль-граница; скорость
                  = роль-конечная.
      Elements  : рациональные u_j, конечная сетка, два уровня времени (L1+P4).
    ДИАГНОСТИКА: волна = процесс распространения; конечная скорость (причинность) — над ℚ,
    0 аксиом; завершённая волна / сохранение энергии (дизайн-чувствительно) — роль-предел/граница.

    STATUS: 6 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import navier_stokes.GridFunction.
From ToS Require Import process.ProcessPDEGreen.   (* ppred *)

Open Scope Q_scope.

(* ===================================================================== *)
(*  The leapfrog wave scheme (central in time and space, periodic)         *)
(* ===================================================================== *)

(** u^{n+1}_j = 2·u^n_j − u^{n−1}_j + s·(u^n_{j+1} − 2·u^n_j + u^n_{j−1}). *)
Definition wave_step (s : Q) (N : nat) (uprev ucur : grid_fn) : grid_fn :=
  fun j => 2 * ucur j - uprev j
           + s * (ucur (S j) - 2 * ucur j + ucur (ppred N j)).

(* ===================================================================== *)
(*  Linearity (in the state pair)                                          *)
(* ===================================================================== *)

Lemma wave_step_linear : forall s N a b (p1 p2 q1 q2 : grid_fn) j,
  wave_step s N (fun k => a * p1 k + b * p2 k) (fun k => a * q1 k + b * q2 k) j
  == a * wave_step s N p1 q1 j + b * wave_step s N p2 q2 j.
Proof. intros. unfold wave_step. ring. Qed.

(* ===================================================================== *)
(*  PRIMARY: causality / finite domain of dependence                       *)
(* ===================================================================== *)

(** ★ Local causality: if the current state is zero at j−1, j, j+1 and the previous
    state is zero at j, then the next state is zero at j. A node's next value depends
    only on a FINITE neighbourhood — the discrete domain of dependence. *)
Lemma wave_step_local_zero : forall s N (uprev ucur : grid_fn) j,
  ucur (ppred N j) == 0 -> ucur j == 0 -> ucur (S j) == 0 -> uprev j == 0 ->
  wave_step s N uprev ucur j == 0.
Proof.
  intros s N uprev ucur j Hpm Hc HpS Hpv. unfold wave_step.
  rewrite Hpm, Hc, HpS, Hpv. ring.
Qed.

(** ★ Finite propagation speed: if both levels are quiet on a block [a,b], the next
    state is still quiet on the interior [a+1, b−1] — a disturbance penetrates a quiet
    region by at most one node per step. *)
Lemma wave_step_interior_zero : forall s N (uprev ucur : grid_fn) a b,
  (forall k, (a <= k <= b)%nat -> ucur k == 0) ->
  (forall k, (a <= k <= b)%nat -> uprev k == 0) ->
  forall j, (S a <= j)%nat -> (S j <= b)%nat -> wave_step s N uprev ucur j == 0.
Proof.
  intros s N uprev ucur a b Hcur Hprev j Hj1 Hj2.
  unfold wave_step.
  destruct j as [|k]; [lia |].
  cbn [ppred].
  assert (Hk  : ucur k == 0)         by (apply Hcur; lia).
  assert (Hj  : ucur (S k) == 0)     by (apply Hcur; lia).
  assert (Hsj : ucur (S (S k)) == 0) by (apply Hcur; lia).
  assert (Hp  : uprev (S k) == 0)    by (apply Hprev; lia).
  rewrite Hk, Hj, Hsj, Hp. ring.
Qed.

(* ===================================================================== *)
(*  Concrete propagation: an impulse spreads one node per step             *)
(* ===================================================================== *)

Definition wzero : grid_fn := fun _ => 0.
(** Impulse at node 2 (5-point grid), zero initial velocity (uprev = ucur). *)
Definition wimp : grid_fn := fun j => match j with S (S O) => 1 | _ => 0 end.

(** The peak at node 2 becomes 1 after one step (s = 1/2). *)
Lemma wave_peak_value : wave_step (1#2) 5%nat wzero wimp 2%nat == 1.
Proof. vm_compute. reflexivity. Qed.

(** ★ The disturbance REACHES the neighbour (node 1): value 1/2. *)
Lemma wave_reaches_neighbor : wave_step (1#2) 5%nat wzero wimp 1%nat == 1#2.
Proof. vm_compute. reflexivity. Qed.

(** ★ Finite speed: node 0 (distance 2 from the impulse) is NOT yet reached — still 0. *)
Lemma wave_finite_speed_concrete : wave_step (1#2) 5%nat wzero wimp 0%nat == 0.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions wave_step_local_zero.
Print Assumptions wave_step_interior_zero.
