(** * ProcessWaveConservation.v — The discrete energy of the leapfrog wave scheme: it
      is conserved on the whole process; the Courant condition s <= 1 is exactly the
      condition under which it is nonnegative; beyond it the values grow without
      bound (Part IX, chapter 3)

    Elements: rational node values on two time levels a (previous), b (current);
              finite sums over the nodes 0..N-1; the Courant square s; natural
              numbers n (steps).
    Roles:    E(a, b) = sum (b - a)^2 + s * sum (D b)(D a) = role-conserved
              quantity (the cross term links the two levels); s <= 1 = role-regime
              in which E is nonnegative and bounds the increments; the alternating
              profile = role-witness of what happens beyond the regime (a single
              mode, which the scheme turns into a scalar oscillator recurrence);
              the constant profile with a nonzero velocity = role-witness that E
              bounds increments, not the levels themselves.
    Rules:    summation by parts on a periodic grid turns the change of the
              kinetic part into minus the change of the cross part, for every s.
              E >= (1 - s) * sum (b - a)^2 for s >= 0.

    ============ E/R/R разбор ============
      Rules (L5): суммирование по частям на периодической сетке: приращение суммы
                  квадратов разности уровней гасится приращением перекрёстного
                  члена — при всяком s; E >= (1 - s) * сумма квадратов разности
                  уровней при s >= 0.
      Roles (L4): E — роль-сохраняющаяся величина; s <= 1 — роль-режим, в котором
                  E неотрицательна и ограничивает приращения; знакопеременный
                  профиль — роль-свидетель за пределом режима; постоянный профиль
                  с ненулевой скоростью — роль-свидетель того, что E ограничивает
                  приращения, а не сами значения.
      Elements  : рациональные значения в узлах на двух уровнях, конечные суммы,
                  конечный номер шага (L1 + P4).
    ДИАГНОСТИКА P4: энергия — конечная сумма рациональных чисел на каждом шаге;
    «сохраняется на всём процессе» — «равна начальной при всяком конечном n»;
    «растёт без границы» — «для всякого B найдётся шаг, на котором значение
    больше B». Интеграла энергии непрерывной волны здесь нет.

    PROVED (all closed under the global context):
      - E is conserved by one step ([wave_energy_step]) and on the whole process
        for periodic initial levels, for every s ([wave_energy_conserved]);
      - the energy with the potential part on ONE level is not conserved by the
        same scheme ([wave_energy_naive_not_conserved]) while E is
        ([wave_energy_cross_example]);
      - for 0 <= s: E >= (1 - s) * sum (b - a)^2 ([wave_energy_lower]); for
        0 <= s <= 1 E >= 0 ([wave_energy_nonneg]); the increments are bounded by
        the initial energy on all steps ([wave_cfl_increment_bound]);
      - the condition is exact: on a grid with an even number of nodes E >= 0 for
        all periodic states iff s <= 1 ([wave_alt_energy],
        [wave_energy_nonneg_iff_cfl]);
      - on the alternating mode the scheme is the scalar recurrence
        y'' = (q - 2) y with q = 2 - 4 s ([wave_alt_mode_step],
        [wave_alt_mode_iter], [wosc_second_difference]); for s > 1 its values
        exceed every bound ([wave_unstable_beyond_cfl]);
      - E does not bound the levels themselves: a constant profile with a unit
        velocity drifts linearly for every s ([wave_const_mode_drift]).

    NOT claimed: the energy integral of the continuous wave or its conservation;
    convergence of the scheme; growth beyond the Courant condition on a grid with
    an odd number of nodes; a bound of the levels (it is false: see the drift);
    dispersion.

    STATUS: 34 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa PeanoNat.
From ToS Require Import navier_stokes.GridFunction.
From ToS Require Import navier_stokes.FiniteDifference.
From ToS Require Import process.ProcessPDEGreen.
From ToS Require Import process.ProcessWaveEnergy.
From ToS Require Import process.ProcessPeriodicGrid.
From ToS Require Import process.ProcessExpLadder.
From ToS Require Import process.ProcessWaveProcess.

Open Scope Q_scope.

(* ===================================================================== *)
(*  1. The energy of a pair of levels and its conservation                 *)
(* ===================================================================== *)

(** a — the previous level, b — the current one. The "kinetic" part is the sum of
    squares of the difference of the levels; the "potential" part is the cross
    term s * sum (D b)(D a), which links the two levels. *)
Definition wave_energy (s : Q) (N : nat) (a b : grid_fn) : Q :=
  sum_Q_ns (fun j => (b j - a j) * (b j - a j)) N
  + s * sum_Q_ns (fun j => fd b j * fd a j) N.

(** The spatial operator of the step. *)
Definition wlap (N : nat) (b : grid_fn) : grid_fn :=
  fun j => b (S j) - 2 * b j + b (ppred N j).

Lemma wave_step_eq : forall s N (a b : grid_fn) j,
  wave_step s N a b j == 2 * b j - a j + s * wlap N b j.
Proof. intros. unfold wave_step, wlap. reflexivity. Qed.

(** Summation by parts on a periodic grid, in the form needed here. *)
Lemma wave_green : forall N (b w : grid_fn), (0 < N)%nat ->
  b N == b 0%nat -> b (S N) == b 1%nat -> w N == w 0%nat ->
  sum_Q_ns (fun j => fd b j * fd w j) N
  == - sum_Q_ns (fun j => w j * wlap N b j) N.
Proof.
  intros N b w HN Hb0 Hb1 Hw.
  assert (Hfd : fd b N == fd b 0%nat).
  { unfold fd. rewrite Hb0, Hb1. reflexivity. }
  pose proof (abel_periodic N w (fd b) Hw Hfd) as HA.
  assert (E1 : sum_Q_ns (fun j => fd b j * fd w j) N
               == sum_Q_ns (fun i => fd w i * fd b i) N).
  { apply sum_ns_ext. intros i _. ring. }
  assert (E2 : sum_Q_ns (fun i => w (S i) * fd (fd b) i) N
               == sum_Q_ns (fun i => w (S i) * wlap N b (S i)) N).
  { apply sum_ns_ext. intros i _. unfold wlap, fd. cbn [ppred]. ring. }
  pose proof (sum_ns_shift_S (fun k => w k * wlap N b k) N) as HS. cbn beta in HS.
  assert (E3 : w N * wlap N b N == w 0%nat * wlap N b 0%nat).
  { destruct N as [|m]; [ lia | ]. unfold wlap. cbn [ppred Nat.pred].
    rewrite Hw, Hb0, Hb1. reflexivity. }
  rewrite E1, HA, E2, HS, E3. ring.
Qed.

(** Conservation over one step: for every s, every N > 0 and all levels that are
    periodic at the joint. *)
Theorem wave_energy_step : forall s N (a b : grid_fn), (0 < N)%nat ->
  a N == a 0%nat -> b N == b 0%nat -> b (S N) == b 1%nat ->
  wave_energy s N b (wave_step s N a b) == wave_energy s N a b.
Proof.
  intros s N a b HN Ha Hb0 Hb1.
  set (c := wave_step s N a b).
  set (w := fun j => c j - a j).
  assert (Hw : w N == w 0%nat).
  { unfold w, c, wave_step. destruct N as [|m]; [ lia | ]. cbn [ppred Nat.pred].
    rewrite Ha, Hb0, Hb1. reflexivity. }
  pose proof (wave_green N b w HN Hb0 Hb1 Hw) as HG.
  unfold wave_energy.
  assert (H1 : sum_Q_ns (fun j => (c j - b j) * (c j - b j)) N
             == sum_Q_ns (fun j => (b j - a j) * (b j - a j)) N
                + s * sum_Q_ns (fun j => w j * wlap N b j) N).
  { rewrite <- sum_ns_scale, <- sum_ns_add. apply sum_ns_ext. intros j _.
    unfold w, c, wave_step, wlap. ring. }
  assert (H2 : sum_Q_ns (fun j => fd c j * fd b j) N
             == sum_Q_ns (fun j => fd b j * fd a j) N
                + sum_Q_ns (fun j => fd b j * fd w j) N).
  { rewrite <- sum_ns_add. apply sum_ns_ext. intros j _. unfold w, fd. ring. }
  rewrite H1, H2, HG. ring.
Qed.

(** Conservation on the whole process: for every s, every N > 0, all periodic
    initial levels and every number of steps. *)
Theorem wave_energy_conserved : forall s N (u0 u1 : grid_fn) n, (0 < N)%nat ->
  gperiodic N u0 -> gperiodic N u1 ->
  wave_energy s N (fst (wave_iter s N u0 u1 n)) (snd (wave_iter s N u0 u1 n))
  == wave_energy s N u0 u1.
Proof.
  intros s N u0 u1 n HN H0 H1. induction n as [|n IH].
  - cbn [wave_iter fst snd]. reflexivity.
  - cbn [wave_iter fst snd].
    destruct (wave_iter_gperiodic s N u0 u1 n HN H0 H1) as [Hp Hc].
    apply Qeq_trans with
      (wave_energy s N (fst (wave_iter s N u0 u1 n)) (snd (wave_iter s N u0 u1 n))).
    + apply wave_energy_step;
        [ exact HN | exact (Hp 0%nat) | exact (Hc 0%nat) | exact (Hc 1%nat) ].
    + exact IH.
Qed.

(** "Sensitivity to the choice of the energy": the energy with the potential part
    on ONE level is not conserved by the scheme; the cross energy is. The example:
    a periodic impulse, N = 5, s = 1/2. *)
Definition wave_energy_naive (s : Q) (N : nat) (a b : grid_fn) : Q :=
  sum_Q_ns (fun j => (b j - a j) * (b j - a j)) N
  + s * sum_Q_ns (fun j => fd b j * fd b j) N.

Definition wimpP : grid_fn := fun j => if (j mod 5 =? 2)%nat then 1 else 0.

Lemma wimpP_gperiodic : gperiodic 5 wimpP.
Proof.
  intro k. unfold wimpP.
  replace ((k + 5) mod 5)%nat with (k mod 5)%nat; [ reflexivity | ].
  replace (k + 5)%nat with (k + 1 * 5)%nat by lia.
  symmetry. apply Nat.Div0.mod_add.
Qed.

Lemma wave_energy_naive_not_conserved :
  wave_energy_naive (1#2) 5%nat wzero wimpP == 2 /\
  wave_energy_naive (1#2) 5%nat wimpP (wave_step (1#2) 5%nat wzero wimpP) == 1.
Proof. split; vm_compute; reflexivity. Qed.

Lemma wave_energy_cross_example :
  wave_energy (1#2) 5%nat wzero wimpP == 1 /\
  wave_energy (1#2) 5%nat wimpP (wave_step (1#2) 5%nat wzero wimpP) == 1.
Proof. split; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(*  2. The Courant condition s <= 1: what it gives                         *)
(* ===================================================================== *)

Lemma sum_fd_sq_bound : forall N (d : grid_fn), d N == d 0%nat ->
  sum_Q_ns (fun j => fd d j * fd d j) N <= 4 * sum_Q_ns (fun j => d j * d j) N.
Proof.
  intros N d Hd.
  apply Qle_trans with
    (sum_Q_ns (fun i => 2*(d (S i) * d (S i)) + 2*(d i * d i)) N).
  - apply sum_ns_le. intros i Hi. unfold fd. apply sq_sub_bound.
  - rewrite sum_ns_add.
    rewrite (sum_ns_scale 2 (fun i => d (S i) * d (S i)) N).
    rewrite (sum_ns_scale 2 (fun i => d i * d i) N).
    assert (Hshift : sum_Q_ns (fun i => d (S i) * d (S i)) N ==
                     sum_Q_ns (fun i => d i * d i) N).
    { apply (sum_ns_shift_periodic (fun k => d k * d k) N).
      cbn beta. rewrite Hd. reflexivity. }
    rewrite Hshift. lra.
Qed.

(** A lower bound of the energy for s >= 0: E >= (1 - s) * sum (b - a)^2. *)
Theorem wave_energy_lower : forall s N (a b : grid_fn),
  0 <= s -> a N == a 0%nat -> b N == b 0%nat ->
  (1 - s) * sum_Q_ns (fun j => (b j - a j) * (b j - a j)) N <= wave_energy s N a b.
Proof.
  intros s N a b Hs Ha Hb. unfold wave_energy.
  set (d := fun k : nat => b k - a k).
  assert (HdN : d N == d 0%nat) by (unfold d; rewrite Ha, Hb; reflexivity).
  pose proof (sum_fd_sq_bound N d HdN) as HM.
  assert (HDeq : sum_Q_ns (fun j => d j * d j) N
                 == sum_Q_ns (fun j => (b j - a j) * (b j - a j)) N).
  { apply sum_ns_ext. intros j _. unfold d. reflexivity. }
  assert (HP : 0 <= sum_Q_ns (fun j => (fd b j + fd a j) * (fd b j + fd a j)) N)
    by apply sum_ns_sq_nonneg.
  assert (HX : 4 * sum_Q_ns (fun j => fd b j * fd a j) N
               == sum_Q_ns (fun j => (fd b j + fd a j) * (fd b j + fd a j)) N
                  - sum_Q_ns (fun j => fd d j * fd d j) N).
  { rewrite <- sum_ns_scale.
    assert (Hneg : - sum_Q_ns (fun j => fd d j * fd d j) N
                   == sum_Q_ns (fun j => - (fd d j * fd d j)) N)
      by (symmetry; apply sum_ns_neg).
    unfold Qminus. rewrite Hneg, <- sum_ns_add.
    apply sum_ns_ext. intros j _. unfold d, fd. ring. }
  set (D := sum_Q_ns (fun j => (b j - a j) * (b j - a j)) N) in *.
  set (X := sum_Q_ns (fun j => fd b j * fd a j) N) in *.
  set (P := sum_Q_ns (fun j => (fd b j + fd a j) * (fd b j + fd a j)) N) in *.
  set (M := sum_Q_ns (fun j => fd d j * fd d j) N) in *.
  set (D' := sum_Q_ns (fun j => d j * d j) N) in *.
  assert (Hsum : 0 <= X + D) by lra.
  assert (Hprod : 0 <= s * (X + D)) by (apply Qmult_le_0_compat; assumption).
  assert (Hid : D + s * X - (1 - s) * D == s * (X + D)) by ring.
  lra.
Qed.

(** For 0 <= s <= 1 the energy is nonnegative. *)
Corollary wave_energy_nonneg : forall s N (a b : grid_fn),
  0 <= s -> s <= 1 -> a N == a 0%nat -> b N == b 0%nat ->
  0 <= wave_energy s N a b.
Proof.
  intros s N a b Hs0 Hs1 Ha Hb.
  pose proof (wave_energy_lower s N a b Hs0 Ha Hb) as HL.
  assert (HD : 0 <= sum_Q_ns (fun j => (b j - a j) * (b j - a j)) N)
    by apply sum_ns_sq_nonneg.
  assert (H0 : 0 <= (1 - s) * sum_Q_ns (fun j => (b j - a j) * (b j - a j)) N)
    by (apply Qmult_le_0_compat; [ lra | exact HD ]).
  lra.
Qed.

(** Stability in the energy norm: the sum of squares of the time increment is
    bounded by the initial energy on ALL steps (the bound has content for s < 1). *)
Theorem wave_cfl_increment_bound : forall s N (u0 u1 : grid_fn) n, (0 < N)%nat ->
  0 <= s -> gperiodic N u0 -> gperiodic N u1 ->
  (1 - s) * sum_Q_ns (fun j =>
       (snd (wave_iter s N u0 u1 n) j - fst (wave_iter s N u0 u1 n) j) *
       (snd (wave_iter s N u0 u1 n) j - fst (wave_iter s N u0 u1 n) j)) N
  <= wave_energy s N u0 u1.
Proof.
  intros s N u0 u1 n HN Hs H0 H1.
  destruct (wave_iter_gperiodic s N u0 u1 n HN H0 H1) as [Hp Hc].
  pose proof (wave_energy_lower s N _ _ Hs (Hp 0%nat) (Hc 0%nat)) as HL.
  pose proof (wave_energy_conserved s N u0 u1 n HN H0 H1) as HC.
  rewrite HC in HL. exact HL.
Qed.

(* ===================================================================== *)
(*  3. Natural numbers as rationals; the sum of a constant                 *)
(* ===================================================================== *)

Lemma inject_nat_S : forall n, inject_Z (Z.of_nat (S n)) == inject_Z (Z.of_nat n) + 1.
Proof.
  intro n. rewrite Nat2Z.inj_succ. unfold Z.succ. rewrite inject_Z_plus. reflexivity.
Qed.

Lemma inject_nat_nonneg : forall n, 0 <= inject_Z (Z.of_nat n).
Proof.
  intro n. change 0 with (inject_Z 0). rewrite <- Zle_Qle. lia.
Qed.

Lemma inject_nat_pos : forall n, (0 < n)%nat -> 0 < inject_Z (Z.of_nat n).
Proof.
  intros n Hn. change 0 with (inject_Z 0). rewrite <- Zlt_Qlt. lia.
Qed.

Lemma sum_ns_const : forall (c : Q) N,
  sum_Q_ns (fun _ => c) N == inject_Z (Z.of_nat N) * c.
Proof.
  intros c N. induction N as [|n IH].
  - rewrite sum_ns_0. cbn [Z.of_nat inject_Z]. ring.
  - rewrite sum_ns_S, IH, inject_nat_S. ring.
Qed.

(* ===================================================================== *)
(*  4. The alternating mode                                                *)
(* ===================================================================== *)

Definition walt : grid_fn := fun j => if Nat.even j then 1 else - (1).
Definition wnalt : grid_fn := fun j => - walt j.

Lemma walt_S : forall k, walt (S k) == - walt k.
Proof.
  intro k. unfold walt. rewrite Nat.even_succ, <- Nat.negb_even.
  destruct (Nat.even k); cbn [negb]; ring.
Qed.

Lemma walt_sq : forall k, walt k * walt k == 1.
Proof. intro k. unfold walt. destruct (Nat.even k); ring. Qed.

Lemma walt_ppred : forall N j, (0 < N)%nat -> Nat.even N = true ->
  walt (ppred N j) == - walt j.
Proof.
  intros N j HN He. destruct j as [|k].
  - cbn [ppred]. destruct N as [|M]; [ lia | ]. cbn [Nat.pred].
    unfold walt. rewrite Nat.even_succ in He. rewrite <- Nat.negb_even in He.
    destruct (Nat.even M); cbn [negb] in He; [ discriminate | ].
    vm_compute. reflexivity.
  - cbn [ppred]. rewrite (walt_S k). ring.
Qed.

Lemma walt_add_even : forall (N k : nat), Nat.even N = true -> walt (k + N)%nat == walt k.
Proof.
  intros N k He. unfold walt. rewrite Nat.even_add, He.
  destruct (Nat.even k); reflexivity.
Qed.

Lemma walt_gperiodic : forall N, Nat.even N = true -> gperiodic N walt.
Proof. intros N He k. apply walt_add_even. exact He. Qed.

Lemma wnalt_gperiodic : forall N, Nat.even N = true -> gperiodic N wnalt.
Proof. intros N He k. unfold wnalt. rewrite (walt_add_even N k He). reflexivity. Qed.

(** The energy of the alternating state: E = 4 N (1 - s). *)
Lemma wave_alt_energy : forall s N,
  wave_energy s N wnalt walt == inject_Z (Z.of_nat N) * (4 * (1 - s)).
Proof.
  intros s N. unfold wave_energy.
  rewrite (sum_ns_ext (fun j => (walt j - wnalt j) * (walt j - wnalt j)) (fun _ => 4) N).
  2: { intros j _. unfold wnalt.
       setoid_replace ((walt j - - walt j) * (walt j - - walt j))
         with (4 * (walt j * walt j)) by ring.
       rewrite walt_sq. ring. }
  rewrite (sum_ns_ext (fun j => fd walt j * fd wnalt j) (fun _ => - (4)) N).
  2: { intros j _. unfold fd, wnalt. rewrite (walt_S j).
       setoid_replace ((- walt j - walt j) * (- - walt j - - walt j))
         with (- (4) * (walt j * walt j)) by ring.
       rewrite walt_sq. ring. }
  rewrite !sum_ns_const. ring.
Qed.

(** The condition is exact: the energy is nonnegative on all periodic states
    iff s <= 1 (on a grid with an even number of nodes). *)
Theorem wave_energy_nonneg_iff_cfl : forall s N, (0 < N)%nat -> Nat.even N = true ->
  0 <= s ->
  ((forall a b : grid_fn, gperiodic N a -> gperiodic N b -> 0 <= wave_energy s N a b)
   <-> s <= 1).
Proof.
  intros s N HN He Hs. split.
  - intro H.
    pose proof (H wnalt walt (wnalt_gperiodic N He) (walt_gperiodic N He)) as HE.
    rewrite wave_alt_energy in HE.
    pose proof (inject_nat_pos N HN) as Hn.
    destruct (Qlt_le_dec 1 s) as [Hbig | Hle]; [ exfalso | exact Hle ].
    set (m := inject_Z (Z.of_nat N)) in *.
    assert (Hp : 0 < m * (4 * (s - 1))) by (apply Qmult_lt_0_compat; lra).
    lra.
  - intros Hs1 a b Ha Hb.
    apply wave_energy_nonneg; [ exact Hs | exact Hs1 | exact (Ha 0%nat) | exact (Hb 0%nat) ].
Qed.

(* ===================================================================== *)
(*  5. One mode is one oscillator                                          *)
(* ===================================================================== *)

(** On the alternating mode the leapfrog step acts on the amplitudes alone. *)
Lemma wave_alt_mode_step : forall s N a b j, (0 < N)%nat -> Nat.even N = true ->
  wave_step s N (fun k => a * walt k) (fun k => b * walt k) j
  == ((2 - 4 * s) * b - a) * walt j.
Proof.
  intros s N a b j HN He. unfold wave_step. cbv beta.
  rewrite (walt_S j), (walt_ppred N j HN He). ring.
Qed.

(** The scalar three-term recurrence y_{n+1} = q y_n - y_{n-1}, as the pair
    (y_n, y_{n+1}). *)
Fixpoint wosc (q y0 y1 : Q) (n : nat) : Q * Q :=
  match n with
  | O => (y0, y1)
  | S k => (snd (wosc q y0 y1 k), q * snd (wosc q y0 y1 k) - fst (wosc q y0 y1 k))
  end.

(** It is the central second difference of an oscillator:
    y_{n+2} - 2 y_{n+1} + y_n = (q - 2) y_{n+1}. *)
Lemma wosc_second_difference : forall q y0 y1 n,
  snd (wosc q y0 y1 (S n)) - 2 * snd (wosc q y0 y1 n) + fst (wosc q y0 y1 n)
  == (q - 2) * snd (wosc q y0 y1 n).
Proof. intros. cbn [wosc fst snd]. ring. Qed.

(** The whole process on the alternating mode is this recurrence with q = 2 - 4 s. *)
Theorem wave_alt_mode_iter : forall s N y0 y1 n, (0 < N)%nat -> Nat.even N = true ->
  forall j,
    fst (wave_iter s N (fun k => y0 * walt k) (fun k => y1 * walt k) n) j
      == fst (wosc (2 - 4 * s) y0 y1 n) * walt j /\
    snd (wave_iter s N (fun k => y0 * walt k) (fun k => y1 * walt k) n) j
      == snd (wosc (2 - 4 * s) y0 y1 n) * walt j.
Proof.
  intros s N y0 y1 n HN He. induction n as [|n IH]; intro j.
  - cbn [wave_iter wosc fst snd]. split; reflexivity.
  - cbn [wave_iter wosc fst snd]. split.
    + apply (IH j).
    + rewrite (wave_step_ext s N _ _
                 (fun k => fst (wosc (2 - 4 * s) y0 y1 n) * walt k)
                 (fun k => snd (wosc (2 - 4 * s) y0 y1 n) * walt k)).
      * apply wave_alt_mode_step; assumption.
      * intro k. apply (IH k).
      * intro k. apply (IH k).
Qed.

Corollary wave_alt_iter_values : forall s N n j, (0 < N)%nat -> Nat.even N = true ->
  snd (wave_iter s N wnalt walt n) j == snd (wosc (2 - 4 * s) (- (1)) 1 n) * walt j.
Proof.
  intros s N n j HN He.
  assert (E0 : forall k, wnalt k == - (1) * walt k) by (intro k; unfold wnalt; ring).
  assert (E1 : forall k, walt k == 1 * walt k) by (intro k; ring).
  destruct (wave_iter_ext s N wnalt walt (fun k => - (1) * walt k) (fun k => 1 * walt k)
              E0 E1 n j) as [_ E].
  rewrite E. apply (wave_alt_mode_iter s N (- (1)) 1 n HN He j).
Qed.

(* ===================================================================== *)
(*  6. Beyond the Courant condition: growth without bound                  *)
(* ===================================================================== *)

(** For q = -2 - d with d >= 0 the recurrence started from (-1, 1) alternates in
    sign and grows at least linearly. *)
Lemma wosc_growth : forall q d, 0 <= d -> q == - (2) - d -> forall n,
  (fst (wosc q (- (1)) 1 n) <= 0 /\ 0 <= snd (wosc q (- (1)) 1 n) /\
   - fst (wosc q (- (1)) 1 n) <= snd (wosc q (- (1)) 1 n) /\
   1 + inject_Z (Z.of_nat n) * d <= snd (wosc q (- (1)) 1 n))
  \/
  (0 <= fst (wosc q (- (1)) 1 n) /\ snd (wosc q (- (1)) 1 n) <= 0 /\
   fst (wosc q (- (1)) 1 n) <= - snd (wosc q (- (1)) 1 n) /\
   1 + inject_Z (Z.of_nat n) * d <= - snd (wosc q (- (1)) 1 n)).
Proof.
  intros q d Hd Hq n. induction n as [|n IH].
  - left. cbn [wosc fst snd]. change (inject_Z (Z.of_nat 0)) with 0.
    split; [ lra | ].
    split; [ lra | ].
    split; [ lra | ].
    setoid_replace (1 + 0 * d) with 1 by ring. apply Qle_refl.
  - cbn [wosc fst snd]. rewrite inject_nat_S.
    pose proof (inject_nat_nonneg n) as Hm.
    set (m := inject_Z (Z.of_nat n)) in *.
    set (a := fst (wosc q (- (1)) 1 n)) in *.
    set (b := snd (wosc q (- (1)) 1 n)) in *.
    assert (Hmd : 0 <= m * d) by (apply Qmult_le_0_compat; assumption).
    assert (Eb : q * b - a == - (2) * b - d * b - a) by (rewrite Hq; ring).
    destruct IH as [[A1 [A2 [A3 A4]]] | [A1 [A2 [A3 A4]]]].
    + right.
      assert (Hdb : 0 <= d * (b - 1)) by (apply Qmult_le_0_compat; lra).
      rewrite Eb. split; [ lra | ]. split; [ lra | ]. split; lra.
    + left.
      assert (Hdb : 0 <= d * (- b - 1)) by (apply Qmult_le_0_compat; lra).
      rewrite Eb. split; [ lra | ]. split; [ lra | ]. split; lra.
Qed.

Lemma wosc_abs_growth : forall q d, 0 <= d -> q == - (2) - d -> forall n,
  1 + inject_Z (Z.of_nat n) * d <= Qabs (snd (wosc q (- (1)) 1 n)).
Proof.
  intros q d Hd Hq n.
  destruct (wosc_growth q d Hd Hq n) as [[_ [A2 [_ A4]]] | [_ [A2 [_ A4]]]].
  - rewrite Qabs_pos by exact A2. exact A4.
  - rewrite Qabs_neg by exact A2. exact A4.
Qed.

(** For s > 1, on a grid with an even number of nodes, the values of a periodic
    solution exceed every bound. *)
Theorem wave_unstable_beyond_cfl : forall s N, (0 < N)%nat -> Nat.even N = true ->
  1 < s ->
  forall B : Q, exists n, B < Qabs (snd (wave_iter s N wnalt walt n) 0%nat).
Proof.
  intros s N HN He Hs B.
  assert (Hd : 0 < 4 * s - 4) by lra.
  destruct (ladder_archimedean B (4 * s - 4) Hd) as [K HK].
  exists K.
  rewrite (wave_alt_iter_values s N K 0%nat HN He).
  rewrite Qabs_Qmult.
  assert (Ha : Qabs (walt 0%nat) == 1) by (vm_compute; reflexivity).
  rewrite Ha, Qmult_1_r.
  pose proof (wosc_abs_growth (2 - 4 * s) (4 * s - 4) (Qlt_le_weak _ _ Hd)
                ltac:(ring) K) as HG.
  set (m := inject_Z (Z.of_nat K)) in *.
  set (y := Qabs (snd (wosc (2 - 4 * s) (- (1)) 1 K))) in *.
  lra.
Qed.

(** The first values for s = 2 on the two-node grid: 1, -5, 29, -169. *)
Lemma wave_growth_example :
  snd (wave_iter 2 2%nat wnalt walt 1%nat) 0%nat == - (5) /\
  snd (wave_iter 2 2%nat wnalt walt 2%nat) 0%nat == 29 /\
  snd (wave_iter 2 2%nat wnalt walt 3%nat) 0%nat == - (169).
Proof.
  split; [ vm_compute; reflexivity | ].
  split; vm_compute; reflexivity.
Qed.

(* ===================================================================== *)
(*  7. The energy bounds increments, not the levels                        *)
(* ===================================================================== *)

Lemma wave_step_const : forall s N a b j,
  wave_step s N (fun _ => a) (fun _ => b) j == 2 * b - a.
Proof. intros. unfold wave_step. ring. Qed.

(** A constant profile with a unit velocity drifts linearly, for every s: after
    n steps the levels are n and n + 1. *)
Theorem wave_const_mode_drift : forall s N n j,
  fst (wave_iter s N (fun _ => 0) (fun _ => 1) n) j == inject_Z (Z.of_nat n) /\
  snd (wave_iter s N (fun _ => 0) (fun _ => 1) n) j == inject_Z (Z.of_nat n) + 1.
Proof.
  intros s N n. induction n as [|n IH]; intro j.
  - cbn [wave_iter fst snd Z.of_nat inject_Z]. split; ring.
  - cbn [wave_iter fst snd]. rewrite inject_nat_S. split.
    + apply (IH j).
    + rewrite (wave_step_ext s N _ _
                 (fun _ => inject_Z (Z.of_nat n)) (fun _ => inject_Z (Z.of_nat n) + 1)).
      * rewrite wave_step_const. ring.
      * intro k. apply (IH k).
      * intro k. apply (IH k).
Qed.

(** Its energy is the same on every step: N (the sum of the squared increments). *)
Lemma wave_const_mode_energy : forall s N,
  wave_energy s N (fun _ => 0) (fun _ => 1) == inject_Z (Z.of_nat N).
Proof.
  intros s N. unfold wave_energy.
  rewrite (sum_ns_ext (fun j => (1 - 0) * (1 - 0)) (fun _ => 1) N) by (intros; ring).
  rewrite (sum_ns_ext (fun j => fd (fun _ => 1) j * fd (fun _ => 0) j) (fun _ => 0) N)
    by (intros; unfold fd; ring).
  rewrite !sum_ns_const. ring.
Qed.

Print Assumptions wave_energy_conserved.
Print Assumptions wave_energy_nonneg_iff_cfl.
Print Assumptions wave_unstable_beyond_cfl.
Print Assumptions wave_const_mode_drift.
