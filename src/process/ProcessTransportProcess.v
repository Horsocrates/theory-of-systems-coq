(** * ProcessTransportProcess.v — The upwind transport scheme on the whole process: mass,
      positivity, the Courant condition, the exact shift (Part IX, chapter 4)

    Elements: rational profiles u^n = transport_iter nu N u n at every finite step n;
              the Courant number nu; sums, sums of absolute values and sums of squares
              over the nodes 0..N-1; differences of neighbouring nodes.
    Roles:    mass = the conserved quantity; nonnegativity and the box = invariants of
              the convex step; 0 <= nu <= 1 = the regime in which the step averages;
              the alternating profile = the mode that grows outside this regime;
              nu (1 - nu) = the rate of numerical diffusion; nu = 1 = the pure shift.
    Rules:    one step conserves the sum for every nu, hence so does every number of
              steps; under 0 <= nu <= 1 the step is monotone, keeps signs and bounds
              and does not increase the differences of neighbours; outside it the
              values grow without bound; at nu = 1 the profile moves by one node per
              step and returns after N steps.

    ============ E/R/R разбор ============
      Rules (L5): шаг против потока; сохранение суммы при всяком nu; при 0 <= nu <= 1 —
                  монотонность, неотрицательность, бокс, невозрастание суммы модулей,
                  суммы квадратов и разностей соседей; вне условия — неограниченный
                  рост знакопеременного профиля; при nu = 1 — точный сдвиг.
      Roles (L4): масса — роль-сохраняющаяся величина; число Куранта — роль-доля
                  смещения; nu (1 - nu) — роль-численная диффузия; знакопеременный
                  профиль — роль-свидетель неустойчивости.
      Elements  : рациональные профили на каждом конечном шаге (L1 + P4).
    ДИАГНОСТИКА P4: «на всём процессе» значит «при всяком конечном номере шага n»;
    «растёт без границы» — «для всякого B найдётся шаг, на котором значение больше B».

    PROVED (all closed under the global context):
      - mass on the whole process, for every nu ([transport_iter_mass]);
      - nonnegativity on the whole process ([transport_iter_nonneg]); the same and
        the box on the nodes of the grid only ([transport_iter_nonneg_grid],
        [transport_iter_box_grid]);
      - the Courant condition is exact for nonnegativity ([transport_nonneg_iff_cfl]);
        outside it the alternating profile grows without bound on a grid with an
        even number of nodes ([transport_unstable_outside_cfl]);
      - under the condition: comparison, the uniform bound, stability with respect
        to the initial data, the sum of absolute values ([transport_iter_mono],
        [transport_iter_sup], [transport_iter_stable], [transport_step_l1]);
      - the exact balance of the sum of squares with the factor nu (1 - nu)
        ([transport_step_energy]); it does not grow under the condition and is
        conserved at nu = 1;
      - the step preserves full periodicity ([transport_iter_gperiodic]); at nu = 1
        the profile is shifted by n nodes in n steps and returns after N steps
        ([transport_iter_shift], [transport_full_cycle]); at nu = 0 it stands;
      - the linear step does not increase the differences of neighbouring nodes
        ([transport_no_steepening]);
      - all the nodes of the example of the chapter ([p_prof_half_step],
        [p_prof_full_step], [p_prof_full_cycle]).

    NOT claimed: the exact solution u0(x - a t) as a function; any limit of
    refinement; growth outside the Courant condition on a grid with an odd number
    of nodes; nonlinear transport.

    STATUS: 40 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import navier_stokes.GridFunction.
From ToS Require Import process.ProcessPDEGreen.
From ToS Require Import process.ProcessTransport.
From ToS Require Import process.ProcessPeriodicGrid.
From ToS Require Import process.ProcessExpProcess.
From ToS Require Import process.ProcessExpLadder.

Open Scope Q_scope.

(* ===================================================================== *)
(*  0. The example of the chapter: the profile (5, 3, 0, 0), four nodes    *)
(* ===================================================================== *)

Lemma p_prof_mass : sum_Q_ns p_prof 4%nat == 8.
Proof. vm_compute. reflexivity. Qed.

(** The half step: (5,3,0,0) -> (5/2, 4, 3/2, 0). *)
Lemma p_prof_half_step :
  transport_step (1#2) 4%nat p_prof 0%nat == 5#2 /\
  transport_step (1#2) 4%nat p_prof 1%nat == 4 /\
  transport_step (1#2) 4%nat p_prof 2%nat == 3#2 /\
  transport_step (1#2) 4%nat p_prof 3%nat == 0.
Proof. split; [ | split; [ | split ] ]; vm_compute; reflexivity. Qed.

(** The full step: (5,3,0,0) -> (0,5,3,0), all four nodes. *)
Lemma p_prof_full_step :
  transport_step 1 4%nat p_prof 0%nat == 0 /\
  transport_step 1 4%nat p_prof 1%nat == 5 /\
  transport_step 1 4%nat p_prof 2%nat == 3 /\
  transport_step 1 4%nat p_prof 3%nat == 0.
Proof. split; [ | split; [ | split ] ]; vm_compute; reflexivity. Qed.

(** Four full steps bring the profile back. *)
Lemma p_prof_full_cycle :
  transport_iter 1 4%nat p_prof 4%nat 0%nat == 5 /\
  transport_iter 1 4%nat p_prof 4%nat 1%nat == 3 /\
  transport_iter 1 4%nat p_prof 4%nat 2%nat == 0 /\
  transport_iter 1 4%nat p_prof 4%nat 3%nat == 0.
Proof. split; [ | split; [ | split ] ]; vm_compute; reflexivity. Qed.

(** nu = 0: the profile stands. *)
Lemma transport_step_zero : forall N (u : grid_fn) j, transport_step 0 N u j == u j.
Proof. intros. unfold transport_step. ring. Qed.

(* ===================================================================== *)
(*  1. Mass on the whole process                                           *)
(* ===================================================================== *)

Theorem transport_iter_mass : forall nu N (u : grid_fn) n,
  (0 < N)%nat -> sum_Q_ns (transport_iter nu N u n) N == sum_Q_ns u N.
Proof.
  intros nu N u n HN. induction n as [|m IH].
  - cbn [transport_iter]. reflexivity.
  - cbn [transport_iter].
    rewrite (transport_mass nu N (transport_iter nu N u m) HN). exact IH.
Qed.

(* ===================================================================== *)
(*  2. Nonnegativity on the whole process                                  *)
(* ===================================================================== *)

Theorem transport_iter_nonneg : forall nu N, 0 <= nu -> nu <= 1 ->
  forall n (u : grid_fn), (forall k, 0 <= u k) ->
  forall j, 0 <= transport_iter nu N u n j.
Proof.
  intros nu N H0 H1 n. induction n as [|m IH]; intros u Hu j.
  - cbn [transport_iter]. apply Hu.
  - cbn [transport_iter]. apply transport_step_nonneg; [exact H0 | exact H1 | ].
    intro k. apply IH. exact Hu.
Qed.

(* ===================================================================== *)
(*  3. The box and nonnegativity on the nodes of the grid j < N            *)
(* ===================================================================== *)

Lemma ppred_lt : forall N j, (j < N)%nat -> (ppred N j < N)%nat.
Proof. intros N j H. destruct j as [|k]; cbn [ppred]; lia. Qed.

Definition in_box_grid (N : nat) (u : grid_fn) (lo hi : Q) : Prop :=
  forall k, (k < N)%nat -> lo <= u k /\ u k <= hi.

Lemma transport_step_box_grid : forall nu N (u : grid_fn) lo hi,
  0 <= nu -> nu <= 1 ->
  in_box_grid N u lo hi -> in_box_grid N (transport_step nu N u) lo hi.
Proof.
  intros nu N u lo hi H0 H1 Hb k Hk. unfold transport_step.
  destruct (Hb k Hk) as [A1 A2].
  destruct (Hb (ppred N k) (ppred_lt N k Hk)) as [B1 B2].
  split; nra.
Qed.

Theorem transport_iter_box_grid : forall nu N lo hi, 0 <= nu -> nu <= 1 ->
  forall n (u : grid_fn), in_box_grid N u lo hi ->
  in_box_grid N (transport_iter nu N u n) lo hi.
Proof.
  intros nu N lo hi H0 H1 n. induction n as [|m IH]; intros u Hb.
  - cbn [transport_iter]. exact Hb.
  - cbn [transport_iter]. apply transport_step_box_grid; [exact H0 | exact H1 | ].
    apply IH. exact Hb.
Qed.

Theorem transport_iter_nonneg_grid : forall nu N, 0 <= nu -> nu <= 1 ->
  forall n (u : grid_fn), (forall k, (k < N)%nat -> 0 <= u k) ->
  forall j, (j < N)%nat -> 0 <= transport_iter nu N u n j.
Proof.
  intros nu N H0 H1 n. induction n as [|m IH]; intros u Hu j Hj.
  - cbn [transport_iter]. apply Hu. exact Hj.
  - cbn [transport_iter]. unfold transport_step.
    pose proof (IH u Hu j Hj) as A.
    pose proof (IH u Hu (ppred N j) (ppred_lt N j Hj)) as B.
    nra.
Qed.

(** A profile kept in [0,3] on the four nodes of the grid, yet not [in_box]:
    the premise [in_box] asks for the bound outside the grid as well. *)
Definition off_grid : grid_fn := fun j => if Nat.ltb j 4 then 0 else 10.

Lemma off_grid_in_box_grid : in_box_grid 4 off_grid 0 3.
Proof.
  intros k Hk. unfold off_grid.
  destruct (Nat.ltb_spec k 4) as [_|Hge]; [ | lia ].
  split; lra.
Qed.

Lemma off_grid_not_in_box : ~ in_box off_grid 0 3.
Proof.
  intro H. destruct (H 4%nat) as [_ H2]. vm_compute in H2. apply H2. reflexivity.
Qed.

(* ===================================================================== *)
(*  4. The condition 0 <= nu <= 1 is necessary for nonnegativity           *)
(* ===================================================================== *)

Definition delta0 : grid_fn := fun j => match j with O => 1 | S _ => 0 end.

Lemma delta0_nonneg : forall k, 0 <= delta0 k.
Proof. intro k. destruct k; unfold delta0; lra. Qed.

Theorem transport_nonneg_needs_cfl : forall nu N, (2 <= N)%nat ->
  (forall u : grid_fn, (forall k, 0 <= u k) ->
     forall j, (j < N)%nat -> 0 <= transport_step nu N u j) ->
  0 <= nu /\ nu <= 1.
Proof.
  intros nu N HN H.
  destruct N as [|[|M]]; [lia | lia | ].
  pose proof (H delta0 delta0_nonneg 0%nat ltac:(lia)) as A.
  pose proof (H delta0 delta0_nonneg 1%nat ltac:(lia)) as B.
  unfold transport_step in A, B.
  cbv beta iota delta [delta0 ppred Nat.pred] in A, B.
  split; lra.
Qed.

Theorem transport_nonneg_iff_cfl : forall nu N, (2 <= N)%nat ->
  ((forall u : grid_fn, (forall k, 0 <= u k) ->
      forall j, (j < N)%nat -> 0 <= transport_step nu N u j)
   <-> (0 <= nu /\ nu <= 1)).
Proof.
  intros nu N HN. split.
  - apply transport_nonneg_needs_cfl. exact HN.
  - intros [H0 H1] u Hu j _. apply transport_step_nonneg; assumption.
Qed.

(* ===================================================================== *)
(*  5. Outside the condition: the alternating profile grows without bound  *)
(* ===================================================================== *)

Definition transport_alt : grid_fn := fun j => if Nat.even j then 1 else - (1).

Lemma transport_alt_S : forall k, transport_alt (S k) == - transport_alt k.
Proof.
  intro k. unfold transport_alt. rewrite Nat.even_succ, <- Nat.negb_even.
  destruct (Nat.even k); cbn [negb]; ring.
Qed.

Lemma transport_alt_in_box : in_box transport_alt (- (1)) 1.
Proof. intro k. unfold transport_alt. destruct (Nat.even k); split; lra. Qed.

Lemma alt_mode_step : forall nu N j, (0 < N)%nat -> Nat.even N = true ->
  transport_step nu N transport_alt j == (1 - 2 * nu) * transport_alt j.
Proof.
  intros nu N j HN He. unfold transport_step.
  destruct j as [|k].
  - cbn [ppred]. destruct N as [|M]; [lia | ]. cbn [Nat.pred].
    assert (HM : transport_alt M == - transport_alt 0%nat).
    { unfold transport_alt. rewrite Nat.even_succ in He. rewrite <- Nat.negb_even in He.
      destruct (Nat.even M); cbn [negb] in He; [discriminate | ].
      vm_compute. reflexivity. }
    rewrite HM. ring.
  - cbn [ppred]. rewrite (transport_alt_S k). ring.
Qed.

Lemma transport_step_ext : forall nu N (u v : grid_fn),
  (forall k, u k == v k) ->
  forall j, transport_step nu N u j == transport_step nu N v j.
Proof.
  intros nu N u v H j. unfold transport_step.
  rewrite (H j), (H (ppred N j)). reflexivity.
Qed.

Lemma transport_iter_ext : forall nu N (u v : grid_fn),
  (forall k, u k == v k) ->
  forall n j, transport_iter nu N u n j == transport_iter nu N v n j.
Proof.
  intros nu N u v H n. induction n as [|m IH]; intro j.
  - cbn [transport_iter]. apply H.
  - cbn [transport_iter]. apply transport_step_ext. exact IH.
Qed.

Lemma qpow_abs : forall r n, Qabs (qpow r n) == qpow (Qabs r) n.
Proof.
  intros r n. induction n as [|m IH]; cbn [qpow].
  - reflexivity.
  - rewrite Qabs_Qmult, IH. reflexivity.
Qed.

(** The alternating profile is an eigenvector of the step with the factor 1 - 2 nu. *)
Theorem alt_mode_iter : forall nu N n j, (0 < N)%nat -> Nat.even N = true ->
  transport_iter nu N transport_alt n j == qpow (1 - 2 * nu) n * transport_alt j.
Proof.
  intros nu N n. induction n as [|m IH]; intros j HN He.
  - cbn [transport_iter qpow]. ring.
  - cbn [transport_iter qpow].
    rewrite (transport_step_ext nu N (transport_iter nu N transport_alt m)
               (fun k => qpow (1 - 2 * nu) m * transport_alt k)
               (fun k => IH k HN He) j).
    pose proof (alt_mode_step nu N j HN He) as S1.
    unfold transport_step in S1 |- *. cbv beta.
    setoid_replace ((1 - nu) * (qpow (1 - 2 * nu) m * transport_alt j)
                    + nu * (qpow (1 - 2 * nu) m * transport_alt (ppred N j)))
      with (qpow (1 - 2 * nu) m
            * ((1 - nu) * transport_alt j + nu * transport_alt (ppred N j))) by ring.
    rewrite S1. ring.
Qed.

Theorem alt_mode_growth : forall nu N n, (0 < N)%nat -> Nat.even N = true ->
  1 <= Qabs (1 - 2 * nu) ->
  1 + inject_Z (Z.of_nat n) * (Qabs (1 - 2 * nu) - 1)
  <= Qabs (transport_iter nu N transport_alt n 0%nat).
Proof.
  intros nu N n HN He Hr.
  rewrite (alt_mode_iter nu N n 0%nat HN He).
  rewrite Qabs_Qmult, qpow_abs.
  assert (Ha : Qabs (transport_alt 0%nat) == 1) by (vm_compute; reflexivity).
  rewrite Ha, Qmult_1_r.
  rewrite (qpow_wd (Qabs (1 - 2 * nu)) (1 + (Qabs (1 - 2 * nu) - 1)) n) by ring.
  apply bernoulli_nonneg. lra.
Qed.

(** For nu > 1 or nu < 0 the values of a profile from the box [-1,1] exceed every bound. *)
Theorem transport_unstable_outside_cfl : forall nu N, (0 < N)%nat -> Nat.even N = true ->
  nu < 0 \/ 1 < nu ->
  forall B : Q, exists n, B < Qabs (transport_iter nu N transport_alt n 0%nat).
Proof.
  intros nu N HN He Hnu B.
  assert (Hd : 0 < Qabs (1 - 2 * nu) - 1).
  { destruct Hnu as [Hneg | Hbig].
    - rewrite Qabs_pos by lra. lra.
    - rewrite Qabs_neg by lra. lra. }
  destruct (ladder_archimedean B (Qabs (1 - 2 * nu) - 1) Hd) as [K HK].
  exists K.
  eapply Qlt_le_trans; [ | apply (alt_mode_growth nu N K HN He); lra ].
  set (q := inject_Z (Z.of_nat K)) in *.
  set (a := Qabs (1 - 2 * nu)) in *.
  lra.
Qed.

(* ===================================================================== *)
(*  6. Under the condition: stability on the whole process                 *)
(* ===================================================================== *)

(** The comparison principle (the step is monotone). *)
Lemma transport_step_mono : forall nu N (u v : grid_fn), 0 <= nu -> nu <= 1 ->
  (forall k, u k <= v k) ->
  forall j, transport_step nu N u j <= transport_step nu N v j.
Proof.
  intros nu N u v H0 H1 H j. unfold transport_step.
  pose proof (H j). pose proof (H (ppred N j)). nra.
Qed.

Theorem transport_iter_mono : forall nu N, 0 <= nu -> nu <= 1 ->
  forall n (u v : grid_fn), (forall k, u k <= v k) ->
  forall j, transport_iter nu N u n j <= transport_iter nu N v n j.
Proof.
  intros nu N H0 H1 n. induction n as [|m IH]; intros u v H j.
  - cbn [transport_iter]. apply H.
  - cbn [transport_iter]. apply transport_step_mono; [exact H0 | exact H1 | ].
    intro k. apply IH. exact H.
Qed.

(** The uniform norm does not grow. *)
Theorem transport_iter_sup : forall nu N M, 0 <= nu -> nu <= 1 ->
  forall n (u : grid_fn), (forall k, Qabs (u k) <= M) ->
  forall j, Qabs (transport_iter nu N u n j) <= M.
Proof.
  intros nu N M H0 H1 n u Hu j.
  assert (Hb : in_box u (- M) M).
  { intro k. apply Qabs_Qle_condition. apply Hu. }
  apply Qabs_Qle_condition.
  exact (transport_iter_box nu N (- M) M H0 H1 n u Hb j).
Qed.

(** The difference of two trajectories is the trajectory of the difference. *)
Lemma transport_iter_diff : forall nu N (u v : grid_fn) n j,
  transport_iter nu N (fun k => u k - v k) n j
  == transport_iter nu N u n j - transport_iter nu N v n j.
Proof.
  intros nu N u v n. induction n as [|m IH]; intro j.
  - cbn [transport_iter]. reflexivity.
  - cbn [transport_iter].
    rewrite (transport_step_ext nu N _
               (fun k => transport_iter nu N u m k - transport_iter nu N v m k) IH j).
    unfold transport_step. ring.
Qed.

(** Stability with respect to the initial data on the whole process. *)
Theorem transport_iter_stable : forall nu N eps, 0 <= nu -> nu <= 1 ->
  forall (u v : grid_fn), (forall k, Qabs (u k - v k) <= eps) ->
  forall n j, Qabs (transport_iter nu N u n j - transport_iter nu N v n j) <= eps.
Proof.
  intros nu N eps H0 H1 u v H n j.
  rewrite <- (transport_iter_diff nu N u v n j).
  apply (transport_iter_sup nu N eps H0 H1 n (fun k => u k - v k)). exact H.
Qed.

(** The sum of absolute values over the nodes does not grow. *)
Lemma transport_step_l1 : forall nu N (u : grid_fn), 0 <= nu -> nu <= 1 -> (0 < N)%nat ->
  sum_Q_ns (fun j => Qabs (transport_step nu N u j)) N
  <= sum_Q_ns (fun j => Qabs (u j)) N.
Proof.
  intros nu N u H0 H1 HN.
  apply Qle_trans with
    (sum_Q_ns (fun j => (1 - nu) * Qabs (u j) + nu * Qabs (u (ppred N j))) N).
  - apply sum_ns_le. intros i Hi. unfold transport_step.
    eapply Qle_trans; [ apply Qabs_triangle | ].
    rewrite !Qabs_Qmult.
    rewrite (Qabs_pos (1 - nu)) by lra. rewrite (Qabs_pos nu) by lra.
    apply Qle_refl.
  - rewrite (sum_ns_add (fun j => (1 - nu) * Qabs (u j))
                        (fun j => nu * Qabs (u (ppred N j))) N).
    rewrite (sum_ns_scale (1 - nu) (fun j => Qabs (u j)) N).
    rewrite (sum_ns_scale nu (fun j => Qabs (u (ppred N j))) N).
    pose proof (sum_pred_shift_periodic (fun j => Qabs (u j)) N HN) as Hs.
    cbv beta in Hs. rewrite Hs. lra.
Qed.

(* ===================================================================== *)
(*  7. Numerical diffusion: the exact balance of the sum of squares        *)
(* ===================================================================== *)

Theorem transport_step_energy : forall nu N (u : grid_fn), (0 < N)%nat ->
  sum_Q_ns (fun j => transport_step nu N u j * transport_step nu N u j) N
  == sum_Q_ns (fun j => u j * u j) N
     - nu * (1 - nu)
       * sum_Q_ns (fun j => (u j - u (ppred N j)) * (u j - u (ppred N j))) N.
Proof.
  intros nu N u HN.
  rewrite (sum_ns_ext
    (fun j => transport_step nu N u j * transport_step nu N u j)
    (fun j => ((1 - nu) * (u j * u j) + nu * (u (ppred N j) * u (ppred N j)))
              + (- (nu * (1 - nu))) * ((u j - u (ppred N j)) * (u j - u (ppred N j)))) N).
  2: { intros i Hi. unfold transport_step. ring. }
  rewrite (sum_ns_add
    (fun j => (1 - nu) * (u j * u j) + nu * (u (ppred N j) * u (ppred N j)))
    (fun j => (- (nu * (1 - nu))) * ((u j - u (ppred N j)) * (u j - u (ppred N j)))) N).
  rewrite (sum_ns_add
    (fun j => (1 - nu) * (u j * u j))
    (fun j => nu * (u (ppred N j) * u (ppred N j))) N).
  rewrite (sum_ns_scale (1 - nu) (fun j => u j * u j) N).
  rewrite (sum_ns_scale nu (fun j => u (ppred N j) * u (ppred N j)) N).
  rewrite (sum_ns_scale (- (nu * (1 - nu)))
             (fun j => (u j - u (ppred N j)) * (u j - u (ppred N j))) N).
  pose proof (sum_pred_shift_periodic (fun j => u j * u j) N HN) as Hs.
  cbv beta in Hs. rewrite Hs. ring.
Qed.

(** Under the condition the sum of squares does not grow. *)
Corollary transport_step_energy_le : forall nu N (u : grid_fn),
  (0 < N)%nat -> 0 <= nu -> nu <= 1 ->
  sum_Q_ns (fun j => transport_step nu N u j * transport_step nu N u j) N
  <= sum_Q_ns (fun j => u j * u j) N.
Proof.
  intros nu N u HN H0 H1. rewrite (transport_step_energy nu N u HN).
  pose proof (sum_ns_sq_nonneg (fun j => u j - u (ppred N j)) N) as Hsq.
  cbv beta in Hsq.
  set (D := sum_Q_ns (fun j => (u j - u (ppred N j)) * (u j - u (ppred N j))) N) in *.
  assert (Hc : 0 <= nu * (1 - nu)) by (apply Qmult_le_0_compat; lra).
  assert (Hp : 0 <= nu * (1 - nu) * D) by (apply Qmult_le_0_compat; assumption).
  lra.
Qed.

(** At nu = 1 it is conserved exactly. *)
Corollary transport_full_step_energy : forall N (u : grid_fn), (0 < N)%nat ->
  sum_Q_ns (fun j => transport_step 1 N u j * transport_step 1 N u j) N
  == sum_Q_ns (fun j => u j * u j) N.
Proof. intros N u HN. rewrite (transport_step_energy 1 N u HN). ring. Qed.

(* ===================================================================== *)
(*  8. Periodicity and the exact shift at nu = 1                           *)
(* ===================================================================== *)

Lemma transport_step_gperiodic : forall nu N u,
  (0 < N)%nat -> gperiodic N u -> gperiodic N (transport_step nu N u).
Proof.
  intros nu N u HN H j. unfold transport_step.
  rewrite (gperiodic_ppred N u j HN H), (H j). reflexivity.
Qed.

Lemma transport_iter_gperiodic : forall nu N u n,
  (0 < N)%nat -> gperiodic N u -> gperiodic N (transport_iter nu N u n).
Proof.
  intros nu N u n HN H. induction n as [|m IH].
  - exact H.
  - cbn [transport_iter]. apply transport_step_gperiodic; assumption.
Qed.

(** In n steps the profile is shifted by n nodes. *)
Theorem transport_iter_shift : forall N (u : grid_fn) n k,
  transport_iter 1 N u n (n + k)%nat == u k.
Proof.
  intros N u n. induction n as [|m IH]; intro k.
  - cbn [transport_iter]. reflexivity.
  - cbn [transport_iter]. rewrite transport_shift.
    replace (ppred N (S m + k)) with (m + k)%nat by reflexivity. apply IH.
Qed.

(** On the periodic grid N full steps bring every profile back. *)
Theorem transport_full_cycle : forall N (u : grid_fn) k,
  (0 < N)%nat -> gperiodic N u -> transport_iter 1 N u N k == u k.
Proof.
  intros N u k HN H.
  transitivity (transport_iter 1 N u N (k + N)%nat).
  - symmetry. exact (transport_iter_gperiodic 1 N u N HN H k).
  - replace (k + N)%nat with (N + k)%nat by lia. apply transport_iter_shift.
Qed.

(* ===================================================================== *)
(*  9. The linear step does not increase the differences of neighbours     *)
(* ===================================================================== *)

Definition bdiff (N : nat) (u : grid_fn) : grid_fn := fun j => u j - u (ppred N j).

Lemma transport_step_bdiff : forall nu N (u : grid_fn) j,
  bdiff N (transport_step nu N u) j == transport_step nu N (bdiff N u) j.
Proof. intros. unfold bdiff, transport_step. ring. Qed.

Theorem transport_no_steepening : forall nu N (u : grid_fn) lo hi,
  0 <= nu -> nu <= 1 ->
  in_box (bdiff N u) lo hi -> in_box (bdiff N (transport_step nu N u)) lo hi.
Proof.
  intros nu N u lo hi H0 H1 Hb k.
  destruct (transport_step_box nu N (bdiff N u) lo hi H0 H1 Hb k) as [A B].
  rewrite (transport_step_bdiff nu N u k). split; assumption.
Qed.

Print Assumptions transport_iter_mass.
Print Assumptions transport_unstable_outside_cfl.
