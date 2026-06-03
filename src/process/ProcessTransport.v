(** * ProcessTransport.v — The transport (advection) equation as a profile-moving
      process on a grid, over ℚ (Part IX, batch C; the simplest PDE-process)

    Elements: rational node values u_j, finite periodic grid, finite time step
    Roles:    u^n = role-profile; ν = role-Courant-number; mass Σu = role-conserved;
              the shift = role-transport; a = role-velocity
    Rules:    upwind step u^{n+1}_j = (1−ν)·u_j + ν·u_{j−1} (ν = a·Δt/Δx, a>0);
              0≤ν≤1 ⟹ convex combination (box/nonnegativity preserved); mass Σu conserved;
              ν=1 ⟹ exact one-node shift; CFL a·Δt/Δx ≤ 1

    The transport equation ∂_t u + a·∂_x u = 0 just MOVES a profile rightward. The upwind
    step blends a node with its upstream neighbour: a convex combination when the Courant
    number ν ≤ 1 (CFL). Mass is conserved (nothing created or destroyed, only moved); at
    ν=1 the profile shifts exactly one node. The completed continuous solution u(x−at) is
    the role-limit; nonlinear advection (Burgers) and shocks are the honest frontier.

    ============ E/R/R разбор ============
      Rules (L5): u^{n+1}_j=(1−ν)u_j+ν u_{j−1}; ν≤1 ⟹ выпуклая комбинация; масса сохраняется;
                  ν=1 ⟹ сдвиг; CFL aΔt/Δx≤1.
      Roles (L4): u^n = роль-профиль; ν = роль-Куранта; масса = роль-сохраняющаяся;
                  сдвиг = роль-перенос.
      Elements  : рациональные u_j, конечная сетка/шаг (L1+P4).
    ДИАГНОСТИКА: перенос = процесс движения профиля; сохранение массы = ничего не
    создаётся/исчезает; CFL = ≤1 узла за шаг; u(x−at), Burgers/ударные волны — роль-предел/граница.

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import navier_stokes.GridFunction.
From ToS Require Import process.ProcessPDEGreen.   (* ppred, sum_pred_shift_periodic *)

Open Scope Q_scope.

(* ===================================================================== *)
(*  The upwind transport scheme (ν = Courant number, periodic grid)        *)
(* ===================================================================== *)

(** u^{n+1}_j = (1−ν)·u_j + ν·u_{j−1}  (upstream neighbour = cyclic predecessor). *)
Definition transport_step (nu : Q) (N : nat) (u : grid_fn) : grid_fn :=
  fun j => (1 - nu) * u j + nu * u (ppred N j).

Fixpoint transport_iter (nu : Q) (N : nat) (u : grid_fn) (n : nat) : grid_fn :=
  match n with
  | O => u
  | S m => transport_step nu N (transport_iter nu N u m)
  end.

Definition in_box (u : grid_fn) (lo hi : Q) : Prop :=
  forall k, lo <= u k /\ u k <= hi.

(* ===================================================================== *)
(*  Linearity                                                              *)
(* ===================================================================== *)

Lemma transport_step_linear : forall nu N a b (f g : grid_fn) j,
  transport_step nu N (fun k => a * f k + b * g k) j
  == a * transport_step nu N f j + b * transport_step nu N g j.
Proof. intros. unfold transport_step. ring. Qed.

(* ===================================================================== *)
(*  CFL ν ≤ 1: box preservation, monotonicity, nonnegativity              *)
(* ===================================================================== *)

(** ★ One upwind step preserves the box: the new value is a convex combination
    (coefficients 1−ν, ν ≥ 0 summing to 1) of two boxed values. *)
Lemma transport_step_box : forall nu N (u : grid_fn) lo hi,
  0 <= nu -> nu <= 1 -> in_box u lo hi -> in_box (transport_step nu N u) lo hi.
Proof.
  intros nu N u lo hi Hnu Hnu1 Hbox k. unfold transport_step.
  destruct (Hbox k) as [Hk1 Hk2].
  destruct (Hbox (ppred N k)) as [Hp1 Hp2].
  split; nra.
Qed.

(** Box preservation over the whole evolution. *)
Lemma transport_iter_box : forall nu N lo hi,
  0 <= nu -> nu <= 1 ->
  forall n u, in_box u lo hi -> in_box (transport_iter nu N u n) lo hi.
Proof.
  intros nu N lo hi Hnu Hnu1 n. induction n as [|m IH]; intros u Hbox.
  - simpl. exact Hbox.
  - simpl. apply transport_step_box; [exact Hnu | exact Hnu1 |]. apply IH. exact Hbox.
Qed.

(** Nonnegativity (e.g. a density) is preserved. *)
Lemma transport_step_nonneg : forall nu N (u : grid_fn),
  0 <= nu -> nu <= 1 -> (forall k, 0 <= u k) ->
  forall j, 0 <= transport_step nu N u j.
Proof.
  intros nu N u Hnu Hnu1 Hpos j. unfold transport_step.
  pose proof (Hpos j). pose proof (Hpos (ppred N j)). nra.
Qed.

(* ===================================================================== *)
(*  Mass conservation (periodic grid)                                      *)
(* ===================================================================== *)

(** ★ Total mass Σ u_j is conserved by one upwind step: transport moves the profile
    without creating or destroying mass. (Needs only N>0 — the predecessor map is a
    cyclic permutation.) *)
Lemma transport_mass : forall nu N (u : grid_fn),
  (0 < N)%nat -> sum_Q_ns (transport_step nu N u) N == sum_Q_ns u N.
Proof.
  intros nu N u HN. unfold transport_step.
  rewrite sum_ns_add.
  rewrite (sum_ns_scale (1 - nu) u N).
  rewrite (sum_ns_scale nu (fun j => u (ppred N j)) N).
  rewrite (sum_pred_shift_periodic u N HN).
  lra.
Qed.

(* ===================================================================== *)
(*  Exact shift at ν = 1                                                   *)
(* ===================================================================== *)

(** ★ At the maximal stable Courant number ν=1, the profile shifts exactly one node:
    u^{n+1}_j = u_{j−1}. *)
Lemma transport_shift : forall N (u : grid_fn) j,
  transport_step 1 N u j == u (ppred N j).
Proof. intros. unfold transport_step. ring. Qed.

(* ===================================================================== *)
(*  Concrete: a profile moves, mass is conserved                           *)
(* ===================================================================== *)

(** Profile (5,3,0,0) on the 4-point grid. *)
Definition p_prof : grid_fn :=
  fun j => match j with O => 5 | S O => 3 | _ => 0 end.

(** Mass (= 8) is conserved by a half-Courant step. *)
Lemma transport_mass_concrete :
  sum_Q_ns (transport_step (1#2) 4%nat p_prof) 4%nat == 8.
Proof. vm_compute. reflexivity. Qed.

(** Full shift (ν=1): node 1 receives the old node-0 value 5. *)
Lemma transport_full_shift :
  transport_step 1 4%nat p_prof 1%nat == 5.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions transport_step_box.
Print Assumptions transport_mass.
