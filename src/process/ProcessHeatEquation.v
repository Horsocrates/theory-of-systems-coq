(** * ProcessHeatEquation.v — The heat equation as a smoothing process on a grid,
      over ℚ (Part IX, CENTERPIECE; parabolic PDE)

    Elements: rational node values u_j, finite periodic grid, finite time step n
    Roles:    u^n = role-state (temperature profile); r = role-diffusion-rate (CFL);
              the box [min,max] = role-invariant (maximum principle); energy = role-
              dissipating quantity; smoothing = role-process
    Rules:    heat_step r u_j = r·u_{j−1} + (1−2r)·u_j + r·u_{j+1} (forward Euler in time,
              central difference in space); 0≤r≤1/2 ⟹ convex combination ⟹ maximum
              principle; energy E=Σu_j² non-increasing (diffusion); CFL r≤1/2

    The heat equation is a process of SMOOTHING: each step replaces a value by a convex
    combination of itself and its neighbours, redistributing toward the local average. Two
    layers (per GPT): the MAXIMUM PRINCIPLE (box preservation) is primary and constructive;
    the ENERGY non-increase is the second layer (via Jensen + the cyclic-shift / Laplacian
    tools of ProcessPDEGreen). The completed continuous solution u(x,t) and the refinement
    limit are role-limits.

    ============ E/R/R разбор ============
      Rules (L5): heat_step = выпуклая комбинация соседей при r≤1/2; принцип максимума;
                  энергия не растёт; CFL r≤1/2.
      Roles (L4): u^n = роль-состояние; r = роль-скорость; бокс = роль-инвариант;
                  энергия = роль-диссипирующая; сглаживание = роль-процесс.
      Elements  : рациональные u_j, конечная сетка, шаг n (L1+P4).
    ДИАГНОСТИКА: тепло = процесс сглаживания (перераспределение к среднему); устойчивость =
    CFL; u(x,t) и непрерывный предел — роль-пределы.

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import navier_stokes.GridFunction.
From ToS Require Import process.ProcessPDEGreen.
(* ProcessPDEGreen re-exports navier_stokes.GridFunction + FiniteDifference:
   grid_fn, sum_Q_ns, gf_norm_sq, gf_inner, sum_ns_le, sum_ns_add, sum_ns_scale,
   Qsq_nonneg, ppred, sum_ns_shift_periodic, sum_pred_shift_periodic. *)

Open Scope Q_scope.

(* ===================================================================== *)
(*  The explicit heat scheme (centered in space, periodic)                 *)
(* ===================================================================== *)

(** u^{n+1}_j = r·u_{j−1} + (1−2r)·u_j + r·u_{j+1}  (left neighbour = cyclic predecessor) *)
Definition heat_step (r : Q) (N : nat) (u : grid_fn) : grid_fn :=
  fun j => r * u (ppred N j) + (1 - 2*r) * u j + r * u (S j).

Fixpoint heat_iter (r : Q) (N : nat) (u : grid_fn) (n : nat) : grid_fn :=
  match n with
  | O => u
  | S m => heat_step r N (heat_iter r N u m)
  end.

(** The profile stays within a box: lo ≤ u_j ≤ hi at every node. *)
Definition in_box (u : grid_fn) (lo hi : Q) : Prop :=
  forall k, lo <= u k /\ u k <= hi.

(* ===================================================================== *)
(*  Linearity                                                              *)
(* ===================================================================== *)

Lemma heat_step_linear : forall r N a b (f g : grid_fn) j,
  heat_step r N (fun k => a * f k + b * g k) j
  == a * heat_step r N f j + b * heat_step r N g j.
Proof. intros. unfold heat_step. ring. Qed.

(* ===================================================================== *)
(*  PRIMARY: maximum principle / box preservation (CFL r ≤ 1/2)            *)
(* ===================================================================== *)

(** ★ One heat step preserves the box: the new value is a convex combination
    (coefficients r, 1−2r, r ≥ 0 summing to 1) of three boxed values. *)
Lemma heat_step_box : forall r N (u : grid_fn) lo hi,
  0 <= r -> 2*r <= 1 -> in_box u lo hi -> in_box (heat_step r N u) lo hi.
Proof.
  intros r N u lo hi Hr Hr2 Hbox k. unfold heat_step.
  destruct (Hbox (ppred N k)) as [HP1 HP2].
  destruct (Hbox k) as [Hk1 Hk2].
  destruct (Hbox (S k)) as [HS1 HS2].
  split.
  - nra.
  - nra.
Qed.

(** Maximum principle over the whole time evolution. *)
Lemma heat_iter_box : forall r N lo hi,
  0 <= r -> 2*r <= 1 ->
  forall n u, in_box u lo hi -> in_box (heat_iter r N u n) lo hi.
Proof.
  intros r N lo hi Hr Hr2 n. induction n as [|m IH]; intros u Hbox.
  - simpl. exact Hbox.
  - simpl. apply heat_step_box; [exact Hr | exact Hr2 |]. apply IH. exact Hbox.
Qed.

(* ===================================================================== *)
(*  SECONDARY: energy non-increase (diffusion dissipates), via Jensen      *)
(* ===================================================================== *)

(** Jensen for a 3-point convex combination of squares: the square of a convex
    combination is ≤ the convex combination of squares (variance ≥ 0). *)
Lemma jensen3 : forall r a b c : Q,
  0 <= r -> 2*r <= 1 ->
  (r*a + (1-2*r)*b + r*c) * (r*a + (1-2*r)*b + r*c)
  <= r*(a*a) + (1-2*r)*(b*b) + r*(c*c).
Proof.
  intros r a b c Hr Hr2.
  assert (H12 : 0 <= 1 - 2*r) by lra.
  assert (Hid : r*(a*a) + (1-2*r)*(b*b) + r*(c*c)
                - (r*a + (1-2*r)*b + r*c) * (r*a + (1-2*r)*b + r*c)
                == r*(1-2*r)*((a-b)*(a-b)) + (r*r)*((a-c)*(a-c))
                   + (1-2*r)*r*((b-c)*(b-c))) by ring.
  assert (T1 : 0 <= r*(1-2*r)*((a-b)*(a-b))).
  { apply Qmult_le_0_compat; [apply Qmult_le_0_compat; [exact Hr | exact H12] | apply Qsq_nonneg]. }
  assert (T2 : 0 <= (r*r)*((a-c)*(a-c))).
  { apply Qmult_le_0_compat; [apply Qsq_nonneg | apply Qsq_nonneg]. }
  assert (T3 : 0 <= (1-2*r)*r*((b-c)*(b-c))).
  { apply Qmult_le_0_compat; [apply Qmult_le_0_compat; [exact H12 | exact Hr] | apply Qsq_nonneg]. }
  lra.
Qed.

(** ★ The discrete energy E = Σ u_j² does not increase under one heat step
    (0 ≤ r ≤ 1/2, periodic grid): diffusion dissipates energy. *)
Lemma heat_step_energy : forall r N (u : grid_fn),
  0 <= r -> 2*r <= 1 -> (0 < N)%nat -> u N == u 0%nat ->
  gf_norm_sq N (heat_step r N u) <= gf_norm_sq N u.
Proof.
  intros r N u Hr Hr2 HN Hper. unfold gf_norm_sq, gf_inner.
  apply Qle_trans with
    (sum_Q_ns (fun j => r*(u (ppred N j) * u (ppred N j))
                        + (1-2*r)*(u j * u j)
                        + r*(u (S j) * u (S j))) N).
  - apply sum_ns_le. intros j Hj. unfold heat_step. apply jensen3; assumption.
  - rewrite sum_ns_add. rewrite sum_ns_add.
    rewrite (sum_ns_scale r (fun j => u (ppred N j) * u (ppred N j)) N).
    rewrite (sum_ns_scale (1-2*r) (fun j => u j * u j) N).
    rewrite (sum_ns_scale r (fun j => u (S j) * u (S j)) N).
    assert (HP : sum_Q_ns (fun j => u (ppred N j) * u (ppred N j)) N
                 == sum_Q_ns (fun j => u j * u j) N).
    { exact (sum_pred_shift_periodic (fun k => u k * u k) N HN). }
    assert (HS : sum_Q_ns (fun j => u (S j) * u (S j)) N
                 == sum_Q_ns (fun j => u j * u j) N).
    { apply (sum_ns_shift_periodic (fun k => u k * u k) N).
      cbn beta. rewrite !Hper. reflexivity. }
    rewrite HP, HS. lra.
Qed.

(* ===================================================================== *)
(*  Concrete smoothing: an impulse on N=4 flattens, energy drops           *)
(* ===================================================================== *)

(** Impulse profile on the 4-point periodic grid: u(0)=u(4)=1, else 0. *)
Definition u_imp : grid_fn :=
  fun j => match j with O => 1 | S (S (S (S O))) => 1 | _ => 0 end.

(** The peak drops from 1 to 1/2 in one step (r = 1/4). *)
Lemma heat_peak_drops : heat_step (1#4) 4%nat u_imp 0%nat == 1#2.
Proof. vm_compute. reflexivity. Qed.

(** New energy after one step is 3/8. *)
Lemma heat_energy_value : gf_norm_sq 4%nat (heat_step (1#4) 4%nat u_imp) == 3#8.
Proof. vm_compute. reflexivity. Qed.

(** ★ Energy strictly drops (3/8 < 1 = initial energy): smoothing dissipates. *)
Lemma heat_energy_decreased :
  gf_norm_sq 4%nat (heat_step (1#4) 4%nat u_imp) < gf_norm_sq 4%nat u_imp.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions heat_step_box.
Print Assumptions heat_step_energy.
