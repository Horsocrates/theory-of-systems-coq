(** * ProcessBurgersStep.v — The first step into nonlinearity: the conservative upwind step
      for the Burgers equation (Part IX, chapter 4)

    Elements: rational profiles u on the nodes of the grid; the ratio lam = dt/dx;
              the flux u^2/2 at a node; differences of neighbouring nodes.
    Roles:    lam (u_j + u_{j-1})/2 = the local Courant number, which now depends on
              the solution; mass = the conserved quantity; lam hi <= 1 = the regime
              in which the step still averages; the difference of neighbours = the
              slope that the nonlinear step can make steeper.
    Rules:    the step is the upwind difference of the flux u^2/2; it is the linear
              transport step with a local Courant number; hence it conserves mass
              for every lam and keeps a nonnegative profile in its box when
              lam hi <= 1; unlike the linear step it can increase the slope.

    ============ E/R/R разбор ============
      Rules (L5): шаг — разность потоков u^2/2 против потока; он есть шаг линейного
                  переноса с местным числом Куранта; сумма сохраняется; бокс
                  неотрицательного профиля сохраняется при lam hi <= 1.
      Roles (L4): местное число Куранта — роль-скорость, зависящая от решения;
                  масса — роль-сохраняющаяся величина; разность соседей — роль-наклон.
      Elements  : рациональные профили на одном шаге (L1 + P4).
    ДИАГНОСТИКА P4: все утверждения — об одном шаге схемы на конечной сетке;
    разрыва, ударной волны и предела измельчения в утверждениях нет.

    PROVED (all closed under the global context):
      - the step is the transport step with the local Courant number
        ([burgers_step_local_courant]);
      - mass is conserved for every lam ([burgers_mass]);
      - a nonnegative profile stays in its box when lam hi <= 1 ([burgers_step_box]);
      - one computation: the slope of a descending ramp grows from 1/4 to 5/16 while
        the mass stays ([burgers_steepens_concrete]) — the linear step cannot do
        this ([transport_no_steepening] in ProcessTransportProcess.v).

    NOT claimed: shock waves, weak or entropy solutions, convergence of the scheme,
    behaviour over many steps, steepening as a general theorem.

    STATUS: 5 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import navier_stokes.GridFunction.
From ToS Require Import process.ProcessPDEGreen.
From ToS Require Import process.ProcessTransport.
From ToS Require Import process.ProcessTransportProcess.

Open Scope Q_scope.

(** The conservative upwind step for the flux u^2/2. *)
Definition burgers_step (lam : Q) (N : nat) (u : grid_fn) : grid_fn :=
  fun j => u j - lam * (1#2) * (u j * u j - u (ppred N j) * u (ppred N j)).

(** The Burgers step is the transport step with a Courant number that depends on
    the solution. *)
Lemma burgers_step_local_courant : forall lam N (u : grid_fn) j,
  burgers_step lam N u j
  == transport_step (lam * (1#2) * (u j + u (ppred N j))) N u j.
Proof. intros. unfold burgers_step, transport_step. ring. Qed.

(** Mass is conserved for every lam. *)
Theorem burgers_mass : forall lam N (u : grid_fn), (0 < N)%nat ->
  sum_Q_ns (burgers_step lam N u) N == sum_Q_ns u N.
Proof.
  intros lam N u HN.
  rewrite (sum_ns_ext (burgers_step lam N u)
    (fun j => (u j + (- (lam * (1#2))) * (u j * u j))
              + (lam * (1#2)) * (u (ppred N j) * u (ppred N j))) N).
  2: { intros i Hi. unfold burgers_step. ring. }
  rewrite (sum_ns_add
    (fun j => u j + (- (lam * (1#2))) * (u j * u j))
    (fun j => (lam * (1#2)) * (u (ppred N j) * u (ppred N j))) N).
  rewrite (sum_ns_add u (fun j => (- (lam * (1#2))) * (u j * u j)) N).
  rewrite (sum_ns_scale (- (lam * (1#2))) (fun j => u j * u j) N).
  rewrite (sum_ns_scale (lam * (1#2)) (fun j => u (ppred N j) * u (ppred N j)) N).
  pose proof (sum_pred_shift_periodic (fun j => u j * u j) N HN) as Hs.
  cbv beta in Hs. rewrite Hs. ring.
Qed.

(** The box is kept for nonnegative profiles when lam * hi <= 1. *)
Theorem burgers_step_box : forall lam N (u : grid_fn) lo hi,
  0 <= lam -> 0 <= lo -> lam * hi <= 1 ->
  in_box u lo hi -> in_box (burgers_step lam N u) lo hi.
Proof.
  intros lam N u lo hi Hl Hlo Hcfl Hb k.
  destruct (Hb k) as [A1 A2]. destruct (Hb (ppred N k)) as [B1 B2].
  assert (Hh : 0 <= 1#2) by (unfold Qle; simpl; lia).
  set (c := lam * (1#2) * (u k + u (ppred N k))).
  assert (Hc0 : 0 <= c).
  { unfold c. apply Qmult_le_0_compat; [ apply Qmult_le_0_compat; assumption | lra ]. }
  assert (Hc1 : c <= 1).
  { unfold c.
    assert (E1 : lam * u k <= lam * hi) by nra.
    assert (E2 : lam * u (ppred N k) <= lam * hi) by nra.
    lra. }
  assert (E : burgers_step lam N u k == (1 - c) * u k + c * u (ppred N k)).
  { unfold burgers_step, c. ring. }
  rewrite E. split; nra.
Qed.

(** One computation: the slope of the descending part grows (from 1/4 to 5/16),
    and the mass stays. *)
Definition ramp8 : grid_fn :=
  fun j => match j with
           | O => 1 | S O => 3#4 | S (S O) => 1#2 | S (S (S O)) => 1#4 | _ => 0
           end.

Lemma ramp8_in_box : in_box ramp8 0 1.
Proof.
  intro k. unfold ramp8.
  destruct k as [|[|[|[|k]]]]; split; unfold Qle; simpl; lia.
Qed.

Lemma burgers_steepens_concrete :
  bdiff 8 ramp8 2%nat == - (1#4)
  /\ bdiff 8 (burgers_step 1 8 ramp8) 2%nat == - (5#16)
  /\ sum_Q_ns (burgers_step 1 8 ramp8) 8 == sum_Q_ns ramp8 8.
Proof. split; [ | split ]; vm_compute; reflexivity. Qed.

Print Assumptions burgers_mass.
Print Assumptions burgers_step_box.
