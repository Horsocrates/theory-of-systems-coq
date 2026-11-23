(** * ProcessHeatProcess.v — The heat scheme on the whole process: periodicity, energy,
      mass, the stability condition (Part IX, chapter 2)

    Elements: rational profiles u^n = heat_iter r N u n at every finite step n; the
              rate r; the node-wise dissipation; the sum ("mass") and the L2-energy
              over the nodes 0..N-1.
    Roles:    full periodicity = the role of the closed grid, kept by every step;
              energy = the dissipating quantity; mass = the conserved quantity;
              0 <= r <= 1/2 = the regime in which the step averages; the dissipation
              = the exact amount of energy lost in one step.
    Rules:    the step preserves full periodicity; hence the one-step energy lemma
              applies at every step; the sum is conserved; the maximum principle
              holds for every profile exactly when 0 <= r <= 1/2.

    ============ E/R/R разбор ============
      Rules (L5): шаг сохраняет полную периодичность; отсюда оценка энергии на
                  каждом шаге и на всём процессе; сохранение суммы; баланс энергии
                  с точной диссипацией; условие 0 <= r <= 1/2 — необходимое и
                  достаточное для принципа максимума.
      Roles (L4): периодичность — роль-замкнутость сетки; энергия — роль-диссипирующая
                  величина; масса — роль-сохраняющаяся величина; диссипация — роль-мера
                  сглаживания за шаг.
      Elements  : рациональные профили на каждом конечном шаге (L1 + P4).
    ДИАГНОСТИКА P4: «на всём процессе» значит «при всяком конечном номере шага n»;
    предела при n → ∞ и предела измельчения сетки в утверждениях нет.

    PROVED (all closed under the global context):
      - the premise u N == u 0 of the one-step energy lemma is NOT preserved by the
        step, and under it the energy can grow at the second step
        ([premise_not_preserved], [energy_two_steps_fails]);
      - the step preserves full periodicity ([heat_step_gperiodic],
        [heat_iter_gperiodic]); the energy does not grow at any step and stays below
        the initial one ([heat_iter_energy_step], [heat_iter_energy_mono],
        [heat_iter_energy]);
      - the sum over the nodes is conserved, for every r ([heat_step_mass],
        [heat_iter_mass]);
      - the exact energy balance with the node-wise dissipation
        ([heat_energy_balance], [heat_iter_energy_balance]) and strict decrease
        ([heat_energy_strict]);
      - the stability condition is exact: the maximum principle for every profile
        is equivalent to 0 <= r <= 1/2 ([heat_box_iff]); beyond it the energy grows
        ([heat_alt_energy_grows]); at r = 1/2 it can stay constant
        ([heat_alt_energy_conserved_half]);
      - stability with respect to the initial data ([heat_iter_stable]);
      - the example of the chapter: all four nodes after the step
        ([heat_impulse_profile]); the periodic impulse ([pext_impulse_profile],
        [pext_impulse_energy]).

    NOT claimed: convergence to the uniform profile as n grows; any limit of
    refinement; the heat kernel; boundary conditions other than periodic.

    STATUS: 42 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa Arith.
From ToS Require Import navier_stokes.GridFunction.
From ToS Require Import navier_stokes.FiniteDifference.
From ToS Require Import process.ProcessPDEGreen.
From ToS Require Import process.ProcessHeatEquation.
From ToS Require Import process.ProcessPeriodicGrid.

Open Scope Q_scope.

(* ===================================================================== *)
(*  1. The premise of the one-step energy lemma is not kept by the step    *)
(* ===================================================================== *)

(** A profile on the grid N = 2: u0 = 1, u1 = 0, u2 = 1 (= u0), u3 = 100. The
    premise u N == u 0 holds; the value at the node N+1 is not bound by it. *)
Definition u_bad : grid_fn :=
  fun j => match j with
           | O => 1
           | S O => 0
           | S (S O) => 1
           | S (S (S O)) => 100
           | _ => 0
           end.

Lemma u_bad_premise : u_bad 2%nat == u_bad 0%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma premise_not_preserved :
  ~ (heat_step (1#4) 2%nat u_bad 2%nat == heat_step (1#4) 2%nat u_bad 0%nat).
Proof. vm_compute. discriminate. Qed.

(** The first step lowers the energy (1 -> 1/2), the second raises it (-> 733/16). *)
Lemma u_bad_energies :
  gf_norm_sq 2%nat u_bad == 1 /\
  gf_norm_sq 2%nat (heat_iter (1#4) 2%nat u_bad 1%nat) == 1#2 /\
  gf_norm_sq 2%nat (heat_iter (1#4) 2%nat u_bad 2%nat) == 733#16.
Proof. split; [ | split ]; vm_compute; reflexivity. Qed.

(** From the premises of heat_step_energy no bound for two steps follows. *)
Theorem energy_two_steps_fails :
  exists (r : Q) (N : nat) (u : grid_fn),
    0 <= r /\ 2*r <= 1 /\ (0 < N)%nat /\ u N == u 0%nat /\
    gf_norm_sq N u < gf_norm_sq N (heat_iter r N u 2%nat).
Proof.
  exists (1#4), 2%nat, u_bad.
  split; [ unfold Qle; simpl; lia | ].
  split; [ unfold Qle; simpl; lia | ].
  split; [ lia | ].
  split; [ exact u_bad_premise | ].
  vm_compute. reflexivity.
Qed.

(* ===================================================================== *)
(*  2. Full periodicity: the energy does not grow on the whole process     *)
(* ===================================================================== *)

(** The step preserves periodicity. *)
Lemma heat_step_gperiodic : forall r N u,
  (0 < N)%nat -> gperiodic N u -> gperiodic N (heat_step r N u).
Proof.
  intros r N u HN H j. unfold heat_step.
  rewrite (gperiodic_ppred N u j HN H).
  assert (Hs : u (S (j + N)) == u (S j)) by exact (H (S j)).
  rewrite Hs, (H j). reflexivity.
Qed.

Lemma heat_iter_gperiodic : forall r N u n,
  (0 < N)%nat -> gperiodic N u -> gperiodic N (heat_iter r N u n).
Proof.
  intros r N u n HN H. induction n as [|m IH].
  - exact H.
  - cbn [heat_iter]. apply heat_step_gperiodic; assumption.
Qed.

(** The energy does not grow from step to step, for every number of the step. *)
Theorem heat_iter_energy_step : forall r N u n,
  0 <= r -> 2*r <= 1 -> (0 < N)%nat -> gperiodic N u ->
  gf_norm_sq N (heat_iter r N u (S n)) <= gf_norm_sq N (heat_iter r N u n).
Proof.
  intros r N u n Hr Hr2 HN H. cbn [heat_iter].
  apply heat_step_energy; try assumption.
  apply gperiodic_N0. apply heat_iter_gperiodic; assumption.
Qed.

Theorem heat_iter_energy_mono : forall r N u n m,
  0 <= r -> 2*r <= 1 -> (0 < N)%nat -> gperiodic N u -> (n <= m)%nat ->
  gf_norm_sq N (heat_iter r N u m) <= gf_norm_sq N (heat_iter r N u n).
Proof.
  intros r N u n m Hr Hr2 HN H Hnm. induction Hnm as [|m Hle IH].
  - apply Qle_refl.
  - eapply Qle_trans; [ apply heat_iter_energy_step; assumption | exact IH ].
Qed.

Theorem heat_iter_energy : forall r N u n,
  0 <= r -> 2*r <= 1 -> (0 < N)%nat -> gperiodic N u ->
  gf_norm_sq N (heat_iter r N u n) <= gf_norm_sq N u.
Proof.
  intros r N u n Hr Hr2 HN H.
  exact (heat_iter_energy_mono r N u 0%nat n Hr Hr2 HN H (Nat.le_0_l n)).
Qed.

(* ===================================================================== *)
(*  3. Conservation of the sum ("mass")                                    *)
(* ===================================================================== *)

(** One step conserves the sum of the values over the nodes; no condition on r. *)
Theorem heat_step_mass : forall r N (u : grid_fn),
  (0 < N)%nat -> u N == u 0%nat ->
  sum_Q_ns (heat_step r N u) N == sum_Q_ns u N.
Proof.
  intros r N u HN Hper.
  transitivity (sum_Q_ns (fun j => r * u (ppred N j) + (1 - 2*r) * u j + r * u (S j)) N).
  { apply sum_ns_ext. intros j Hj. unfold heat_step. reflexivity. }
  rewrite sum_ns_add. rewrite sum_ns_add.
  rewrite (sum_ns_scale r (fun j => u (ppred N j)) N).
  rewrite (sum_ns_scale (1 - 2*r) (fun j => u j) N).
  rewrite (sum_ns_scale r (fun j => u (S j)) N).
  assert (HP : sum_Q_ns (fun j => u (ppred N j)) N == sum_Q_ns (fun j => u j) N).
  { exact (sum_pred_shift_periodic (fun k => u k) N HN). }
  assert (HS : sum_Q_ns (fun j => u (S j)) N == sum_Q_ns (fun j => u j) N).
  { exact (sum_ns_shift_periodic (fun k => u k) N Hper). }
  rewrite HP, HS.
  assert (He : sum_Q_ns (fun j => u j) N == sum_Q_ns u N).
  { apply sum_ns_ext. intros; reflexivity. }
  rewrite He. ring.
Qed.

(** The sum is conserved on the whole process (periodic profile). *)
Theorem heat_iter_mass : forall r N u n,
  (0 < N)%nat -> gperiodic N u ->
  sum_Q_ns (heat_iter r N u n) N == sum_Q_ns u N.
Proof.
  intros r N u n HN H. induction n as [|m IH].
  - reflexivity.
  - cbn [heat_iter]. rewrite heat_step_mass; [ exact IH | exact HN | ].
    apply gperiodic_N0. apply heat_iter_gperiodic; assumption.
Qed.

(** A constant profile is a fixed point (the weights sum to one). *)
Lemma heat_step_const : forall r N c j, heat_step r N (fun _ => c) j == c.
Proof. intros. unfold heat_step. ring. Qed.

(* ===================================================================== *)
(*  4. The stability condition 0 <= r <= 1/2 is exact                      *)
(* ===================================================================== *)

Definition spike1 : grid_fn := fun j => match j with S O => 1 | _ => 0 end.
Definition dip1   : grid_fn := fun j => match j with S O => 0 | _ => 1 end.

Lemma spike1_box : in_box spike1 0 1.
Proof.
  intro k. unfold spike1. destruct k as [|[|k]]; split; unfold Qle; simpl; lia.
Qed.

Lemma dip1_box : in_box dip1 0 1.
Proof.
  intro k. unfold dip1. destruct k as [|[|k]]; split; unfold Qle; simpl; lia.
Qed.

Lemma heat_step_spike1 : forall r N, heat_step r N spike1 1%nat == 1 - 2*r.
Proof. intros. unfold heat_step, spike1. cbn [ppred]. ring. Qed.

Lemma heat_step_dip1 : forall r N, heat_step r N dip1 1%nat == 2*r.
Proof. intros. unfold heat_step, dip1. cbn [ppred]. ring. Qed.

(** The maximum principle for every profile is equivalent to 0 <= r <= 1/2. *)
Theorem heat_box_iff : forall r N,
  (forall (u : grid_fn) lo hi, in_box u lo hi -> in_box (heat_step r N u) lo hi)
  <-> (0 <= r /\ 2*r <= 1).
Proof.
  intros r N. split.
  - intro H. split.
    + destruct (H dip1 0 1 dip1_box 1%nat) as [H1 _].
      rewrite heat_step_dip1 in H1. lra.
    + destruct (H spike1 0 1 spike1_box 1%nat) as [H1 _].
      rewrite heat_step_spike1 in H1. lra.
  - intros [Hr Hr2] u lo hi Hb. apply heat_step_box; assumption.
Qed.

(** The alternating profile on the grid of two nodes. *)
Definition heat_alt : grid_fn := fun j => if Nat.even j then 1 else -1.

Lemma heat_alt_gperiodic : gperiodic 2%nat heat_alt.
Proof.
  intro j. unfold heat_alt.
  replace (j + 2)%nat with (S (S j)) by lia. cbn [Nat.even]. reflexivity.
Qed.

Lemma heat_alt_energy0 : gf_norm_sq 2%nat heat_alt == 2.
Proof. vm_compute. reflexivity. Qed.

Lemma heat_alt_step_energy : forall r,
  gf_norm_sq 2%nat (heat_step r 2%nat heat_alt) == 2 * ((1 - 4*r) * (1 - 4*r)).
Proof.
  intro r. unfold gf_norm_sq, gf_inner. cbn [sum_Q_ns].
  unfold heat_step, heat_alt. cbn [ppred Nat.pred Nat.even]. ring.
Qed.

(** For r > 1/2 the energy grows on the periodic grid. *)
Theorem heat_alt_energy_grows : forall r, 1 < 2*r ->
  gf_norm_sq 2%nat heat_alt < gf_norm_sq 2%nat (heat_step r 2%nat heat_alt).
Proof.
  intros r Hr. rewrite heat_alt_step_energy, heat_alt_energy0.
  assert (H : 1 < (1 - 4*r) * (1 - 4*r)) by nra.
  lra.
Qed.

(** At r = 1/2 the energy of the alternating profile stays: no strict decrease. *)
Lemma heat_alt_energy_conserved_half :
  gf_norm_sq 2%nat (heat_step (1#2) 2%nat heat_alt) == gf_norm_sq 2%nat heat_alt.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  5. The exact energy balance and strict decrease                        *)
(* ===================================================================== *)

(** Node-wise dissipation: three nonnegative terms (the variance of the convex
    combination). *)
Definition heat_diss (r : Q) (N : nat) (u : grid_fn) (j : nat) : Q :=
  r*(1-2*r)*((u (ppred N j) - u j)*(u (ppred N j) - u j))
  + (r*r)*((u (ppred N j) - u (S j))*(u (ppred N j) - u (S j)))
  + (1-2*r)*r*((u j - u (S j))*(u j - u (S j))).

Lemma heat_diss_nonneg : forall r N u j, 0 <= r -> 2*r <= 1 -> 0 <= heat_diss r N u j.
Proof.
  intros r N u j Hr Hr2. unfold heat_diss.
  assert (H12 : 0 <= 1 - 2*r) by lra.
  assert (T1 : 0 <= r*(1-2*r)*((u (ppred N j) - u j)*(u (ppred N j) - u j))).
  { apply Qmult_le_0_compat; [ apply Qmult_le_0_compat; assumption | apply Qsq_nonneg ]. }
  assert (T2 : 0 <= (r*r)*((u (ppred N j) - u (S j))*(u (ppred N j) - u (S j)))).
  { apply Qmult_le_0_compat; apply Qsq_nonneg. }
  assert (T3 : 0 <= (1-2*r)*r*((u j - u (S j))*(u j - u (S j)))).
  { apply Qmult_le_0_compat; [ apply Qmult_le_0_compat; assumption | apply Qsq_nonneg ]. }
  lra.
Qed.

(** The balance: E(u') + the sum of dissipations = E(u). No condition on r. *)
Theorem heat_energy_balance : forall r N (u : grid_fn),
  (0 < N)%nat -> u N == u 0%nat ->
  gf_norm_sq N (heat_step r N u) + sum_Q_ns (heat_diss r N u) N == gf_norm_sq N u.
Proof.
  intros r N u HN Hper. unfold gf_norm_sq, gf_inner.
  rewrite <- (sum_ns_add (fun i => heat_step r N u i * heat_step r N u i) (heat_diss r N u) N).
  transitivity
    (sum_Q_ns (fun j => r*(u (ppred N j) * u (ppred N j))
                        + (1-2*r)*(u j * u j)
                        + r*(u (S j) * u (S j))) N).
  - apply sum_ns_ext. intros j Hj. unfold heat_step, heat_diss. ring.
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
    rewrite HP, HS. ring.
Qed.

(** The balance at every step of the process (periodic profile). *)
Theorem heat_iter_energy_balance : forall r N u n,
  (0 < N)%nat -> gperiodic N u ->
  gf_norm_sq N (heat_iter r N u (S n))
    + sum_Q_ns (heat_diss r N (heat_iter r N u n)) N
  == gf_norm_sq N (heat_iter r N u n).
Proof.
  intros r N u n HN H. cbn [heat_iter].
  apply heat_energy_balance; [ exact HN | ].
  apply gperiodic_N0. apply heat_iter_gperiodic; assumption.
Qed.

Lemma sum_ns_pos : forall (f : nat -> Q) n k,
  (forall i, (i < n)%nat -> 0 <= f i) -> (k < n)%nat -> 0 < f k -> 0 < sum_Q_ns f n.
Proof.
  intros f n. induction n as [|m IH]; intros k Hnn Hk Hpos; [ lia | ].
  rewrite sum_ns_S.
  assert (Hm : 0 <= f m) by (apply Hnn; lia).
  assert (Hs : 0 <= sum_Q_ns f m) by (apply sum_ns_nonneg; intros; apply Hnn; lia).
  destruct (Nat.eq_dec k m) as [Heq|Hne].
  - subst k. lra.
  - assert (H0 : 0 < sum_Q_ns f m).
    { apply (IH k); [ intros; apply Hnn; lia | lia | exact Hpos ]. }
    lra.
Qed.

Lemma heat_sq_pos : forall x : Q, ~ x == 0 -> 0 < x * x.
Proof.
  intros x Hx. destruct (Qlt_le_dec 0 (x * x)) as [H|H]; [ exact H | ].
  exfalso. apply Hx. apply Qsq_eq_0.
  pose proof (Qsq_nonneg x). lra.
Qed.

(** Strict decrease: 0 < r < 1/2 and the profile is not constant on the grid. *)
Theorem heat_energy_strict : forall r N (u : grid_fn) k,
  0 < r -> 2*r < 1 -> (0 < N)%nat -> u N == u 0%nat ->
  (k < N)%nat -> ~ u k == u (S k) ->
  gf_norm_sq N (heat_step r N u) < gf_norm_sq N u.
Proof.
  intros r N u k Hr Hr2 HN Hper Hk Hne.
  pose proof (heat_energy_balance r N u HN Hper) as Hb.
  assert (Hpos : 0 < sum_Q_ns (heat_diss r N u) N).
  { apply (sum_ns_pos (heat_diss r N u) N k).
    - intros i Hi. apply heat_diss_nonneg; lra.
    - exact Hk.
    - unfold heat_diss.
      assert (H12 : 0 < 1 - 2*r) by lra.
      assert (T1 : 0 <= r*(1-2*r)*((u (ppred N k) - u k)*(u (ppred N k) - u k))).
      { apply Qmult_le_0_compat; [ apply Qmult_le_0_compat; lra | apply Qsq_nonneg ]. }
      assert (T2 : 0 <= (r*r)*((u (ppred N k) - u (S k))*(u (ppred N k) - u (S k)))).
      { apply Qmult_le_0_compat; apply Qsq_nonneg. }
      assert (T3 : 0 < (1-2*r)*r*((u k - u (S k))*(u k - u (S k)))).
      { apply Qmult_lt_0_compat; [ apply Qmult_lt_0_compat; lra | ].
        apply heat_sq_pos. intro H0. apply Hne. lra. }
      lra. }
  lra.
Qed.

(* ===================================================================== *)
(*  6. The step written through the Laplacian                              *)
(* ===================================================================== *)

(** The Euler step with the centred second difference is the same formula. *)
Lemma heat_step_euler_form : forall r N (u : grid_fn) j,
  heat_step r N u j == u j + r * (u (S j) - 2 * u j + u (ppred N j)).
Proof. intros. unfold heat_step. ring. Qed.

(** At an inner node the centred difference is [dd] with the index shifted. *)
Lemma heat_step_dd : forall r N (u : grid_fn) k,
  heat_step r N u (S k) == u (S k) + r * dd u k.
Proof. intros. unfold heat_step, dd. cbn [ppred]. ring. Qed.

(* ===================================================================== *)
(*  7. Stability with respect to the initial data                          *)
(* ===================================================================== *)

Lemma heat_step_ext : forall r N (u v : grid_fn),
  (forall k, u k == v k) -> forall j, heat_step r N u j == heat_step r N v j.
Proof. intros r N u v H j. unfold heat_step. rewrite !H. reflexivity. Qed.

Lemma heat_iter_sub : forall r N (u v : grid_fn) n j,
  heat_iter r N (fun k => u k - v k) n j == heat_iter r N u n j - heat_iter r N v n j.
Proof.
  intros r N u v n. induction n as [|m IH]; intro j.
  - cbn [heat_iter]. reflexivity.
  - cbn [heat_iter].
    rewrite (heat_step_ext r N _ (fun k => heat_iter r N u m k - heat_iter r N v m k) IH j).
    unfold heat_step. ring.
Qed.

(** Two processes whose initial profiles differ by at most d at every node differ
    by at most d at every step. *)
Theorem heat_iter_stable : forall r N (u v : grid_fn) d n,
  0 <= r -> 2*r <= 1 ->
  (forall k, Qabs (u k - v k) <= d) ->
  forall k, Qabs (heat_iter r N u n k - heat_iter r N v n k) <= d.
Proof.
  intros r N u v d n Hr Hr2 Hd k.
  assert (Hbox : in_box (fun j => u j - v j) (- d) d).
  { intro j. apply Qabs_Qle_condition. apply Hd. }
  pose proof (heat_iter_box r N (- d) d Hr Hr2 n (fun j => u j - v j) Hbox k) as [H1 H2].
  rewrite heat_iter_sub in H1, H2.
  apply Qabs_Qle_condition. split; assumption.
Qed.

(* ===================================================================== *)
(*  8. The example of the chapter                                          *)
(* ===================================================================== *)

(** The whole profile after one step: (1/2, 1/4, 0, 1/4). *)
Lemma heat_impulse_profile :
  heat_step (1#4) 4%nat u_imp 0%nat == 1#2 /\
  heat_step (1#4) 4%nat u_imp 1%nat == 1#4 /\
  heat_step (1#4) 4%nat u_imp 2%nat == 0 /\
  heat_step (1#4) 4%nat u_imp 3%nat == 1#4.
Proof. split; [ | split; [ | split ] ]; vm_compute; reflexivity. Qed.

Lemma imp_mass : sum_Q_ns u_imp 4%nat == 1 /\ sum_Q_ns (heat_step (1#4) 4%nat u_imp) 4%nat == 1.
Proof. split; vm_compute; reflexivity. Qed.

(** [u_imp] equals 1 at the nodes 0 and 4 and 0 elsewhere (0 at the node 8): it is
    not periodic. *)
Lemma u_imp_not_gperiodic : ~ gperiodic 4%nat u_imp.
Proof. intro H. specialize (H 4%nat). vm_compute in H. discriminate H. Qed.

(** Its premise u 4 == u 0 is lost at the step 4, and at the step 5 the sum over
    the four nodes is no longer 1. *)
Lemma imp_premise_lost_step4 :
  heat_iter (1#4) 4%nat u_imp 4%nat 4%nat == 71#256 /\
  heat_iter (1#4) 4%nat u_imp 4%nat 0%nat == 9#32.
Proof. split; vm_compute; reflexivity. Qed.

Lemma imp_mass_leaks_step5 :
  sum_Q_ns (heat_iter (1#4) 4%nat u_imp 4%nat) 4%nat == 1 /\
  sum_Q_ns (heat_iter (1#4) 4%nat u_imp 5%nat) 4%nat == 1023#1024.
Proof. split; vm_compute; reflexivity. Qed.

(** The impulse as a periodic profile: 1 at the nodes divisible by 4. *)
Lemma pext_impulse_gperiodic : gperiodic 4%nat (pext 4%nat u_imp).
Proof. apply pext_gperiodic. lia. Qed.

Lemma pext_impulse_profile :
  heat_step (1#4) 4%nat (pext 4%nat u_imp) 0%nat == 1#2 /\
  heat_step (1#4) 4%nat (pext 4%nat u_imp) 1%nat == 1#4 /\
  heat_step (1#4) 4%nat (pext 4%nat u_imp) 2%nat == 0 /\
  heat_step (1#4) 4%nat (pext 4%nat u_imp) 3%nat == 1#4.
Proof. split; [ | split; [ | split ] ]; vm_compute; reflexivity. Qed.

Lemma pext_impulse_energy :
  gf_norm_sq 4%nat (pext 4%nat u_imp) == 1 /\
  gf_norm_sq 4%nat (heat_step (1#4) 4%nat (pext 4%nat u_imp)) == 3#8.
Proof. split; vm_compute; reflexivity. Qed.

(** For the periodic impulse the sum stays 1 at the step 5. *)
Lemma pext_impulse_step5 :
  sum_Q_ns (heat_iter (1#4) 4%nat (pext 4%nat u_imp) 5%nat) 4%nat == 1 /\
  gf_norm_sq 4%nat (heat_iter (1#4) 4%nat (pext 4%nat u_imp) 5%nat) == 513#2048.
Proof. split; vm_compute; reflexivity. Qed.

Print Assumptions heat_iter_energy.
Print Assumptions heat_box_iff.
