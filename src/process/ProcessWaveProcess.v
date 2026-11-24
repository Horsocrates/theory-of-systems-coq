(** * ProcessWaveProcess.v — The leapfrog wave scheme on the whole process: the state
      after n steps, finite speed and the cone of dependence over n steps, travelling
      profiles at the Courant number 1 (Part IX, chapter 3)

    Elements: rational node values on two time levels; the state after n steps as a
              pair of grid functions (previous level, current level); natural
              numbers n (steps), j (nodes), a, b (ends of a block of nodes).
    Roles:    the pair of levels = role-state; n = role-time; the block [a, b] =
              role-quiet region (or the region where two states agree); the block
              [a + n, b - n] = role-what the edges have not reached in n steps;
              [j - n, j + n] = role-cone of dependence of the node j; s = 1 =
              role-regime in which a travelling profile is moved exactly.
    Rules:    the leapfrog step of ProcessWaveEnergy.v reads the current level at
              j - 1, j, j + 1 and the previous level at j. Iterated, it gives: the
              edges of a quiet block move inwards by at most one node per step;
              two states that agree on a block agree after n steps on the block
              shortened by n nodes at each end.

    ============ E/R/R разбор ============
      Rules (L5): шаг чехарды читает три соседних узла текущего уровня и свой узел
                  прошлого; повторённый n раз, он сдвигает края тихой области внутрь
                  не более чем на узел за шаг; совпадающие на отрезке состояния
                  совпадают после n шагов на отрезке, укороченном на n с каждого края.
      Roles (L4): пара уровней — роль-состояние; n — роль-время; [a+n, b-n] —
                  роль-недостигнутое; [j-n, j+n] — роль-конус зависимости узла j;
                  s = 1 — роль-режим точного переноса бегущего профиля.
      Elements  : рациональные значения в узлах на двух уровнях, конечный номер шага
                  (L1 + P4).
    ДИАГНОСТИКА P4: «за n шагов» — при всяком конечном n; конус зависимости — конечный
    отрезок узлов, а не завершённый объект; бегущий профиль — сдвиг номера узла на
    каждом конечном шаге.

    PROVED (all closed under the global context):
      - the example of the chapter on all five nodes ([wave_impulse_profile]); its
        data have a nonzero grid velocity ([wave_example_velocity_nonzero]); the
        same impulse with zero velocity splits into two halves
        ([wave_zero_velocity_profile]);
      - the domain of dependence of one step in the general form ([wave_step_dep]);
      - the state after n steps ([wave_iter]); finite speed over n steps
        ([wave_finite_speed_n], [wave_quiet_n]); the cone of dependence over n
        steps ([wave_dependence_cone_n], [wave_value_depends_on_cone]); the bound
        is attained ([wave_two_steps_reach]);
      - full periodicity is preserved by the step and by the process
        ([wave_step_gperiodic], [wave_iter_gperiodic]);
      - at the Courant number 1 a travelling periodic profile is moved exactly, by
        one node per step, on the whole process ([wave_travelling_n]).

    NOT claimed: a completed continuous wave, the continuous cone of influence as an
    object, d'Alembert's formula for functions of a real argument, dispersion,
    behaviour as t -> infinity. Energy and the Courant condition are the subject of
    ProcessWaveConservation.v.

    STATUS: 17 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa PeanoNat.
From ToS Require Import navier_stokes.GridFunction.
From ToS Require Import process.ProcessPDEGreen.
From ToS Require Import process.ProcessWaveEnergy.
From ToS Require Import process.ProcessPeriodicGrid.

Open Scope Q_scope.

(* ===================================================================== *)
(*  0. The example of the chapter on all five nodes                        *)
(* ===================================================================== *)

(** Previous level zero, current level the impulse at node 2; s = 1/2. *)
Lemma wave_impulse_profile :
  wave_step (1#2) 5%nat wzero wimp 0%nat == 0 /\
  wave_step (1#2) 5%nat wzero wimp 1%nat == 1#2 /\
  wave_step (1#2) 5%nat wzero wimp 2%nat == 1 /\
  wave_step (1#2) 5%nat wzero wimp 3%nat == 1#2 /\
  wave_step (1#2) 5%nat wzero wimp 4%nat == 0.
Proof.
  split; [ vm_compute; reflexivity | ].
  split; [ vm_compute; reflexivity | ].
  split; [ vm_compute; reflexivity | ].
  split; vm_compute; reflexivity.
Qed.

(** In these data the grid velocity (the difference of the two levels) at node 2
    is 1, not 0. *)
Lemma wave_example_velocity_nonzero : wimp 2%nat - wzero 2%nat == 1.
Proof. vm_compute. reflexivity. Qed.

(** The same impulse with ZERO initial velocity (the previous level equals the
    current one): the peak becomes zero, the neighbours get 1/2 each. *)
Lemma wave_zero_velocity_profile :
  wave_step (1#2) 5%nat wimp wimp 0%nat == 0 /\
  wave_step (1#2) 5%nat wimp wimp 1%nat == 1#2 /\
  wave_step (1#2) 5%nat wimp wimp 2%nat == 0 /\
  wave_step (1#2) 5%nat wimp wimp 3%nat == 1#2 /\
  wave_step (1#2) 5%nat wimp wimp 4%nat == 0.
Proof.
  split; [ vm_compute; reflexivity | ].
  split; [ vm_compute; reflexivity | ].
  split; [ vm_compute; reflexivity | ].
  split; vm_compute; reflexivity.
Qed.

(* ===================================================================== *)
(*  1. The domain of dependence of one step, in the general form           *)
(* ===================================================================== *)

(** The value of the step at j is determined by the current level at j-1, j, j+1
    and by the previous level at j. *)
Lemma wave_step_dep : forall s N (p1 c1 p2 c2 : grid_fn) j,
  c1 (ppred N j) == c2 (ppred N j) -> c1 j == c2 j -> c1 (S j) == c2 (S j) ->
  p1 j == p2 j ->
  wave_step s N p1 c1 j == wave_step s N p2 c2 j.
Proof.
  intros s N p1 c1 p2 c2 j Hm Hc HS Hp. unfold wave_step.
  rewrite Hm, Hc, HS, Hp. reflexivity.
Qed.

Lemma wave_step_ext : forall s N (p1 c1 p2 c2 : grid_fn),
  (forall k, p1 k == p2 k) -> (forall k, c1 k == c2 k) ->
  forall j, wave_step s N p1 c1 j == wave_step s N p2 c2 j.
Proof. intros s N p1 c1 p2 c2 Hp Hc j. apply wave_step_dep; auto. Qed.

(* ===================================================================== *)
(*  2. The state after n steps                                             *)
(* ===================================================================== *)

(** The pair (previous level, current level) after n steps. *)
Fixpoint wave_iter (s : Q) (N : nat) (u0 u1 : grid_fn) (n : nat) : grid_fn * grid_fn :=
  match n with
  | O => (u0, u1)
  | S k => (snd (wave_iter s N u0 u1 k),
            wave_step s N (fst (wave_iter s N u0 u1 k)) (snd (wave_iter s N u0 u1 k)))
  end.

Lemma wave_iter_ext : forall s N (u0 u1 v0 v1 : grid_fn),
  (forall k, u0 k == v0 k) -> (forall k, u1 k == v1 k) ->
  forall n j,
    fst (wave_iter s N u0 u1 n) j == fst (wave_iter s N v0 v1 n) j /\
    snd (wave_iter s N u0 u1 n) j == snd (wave_iter s N v0 v1 n) j.
Proof.
  intros s N u0 u1 v0 v1 H0 H1 n. induction n as [|n IH]; intro j.
  - cbn [wave_iter fst snd]. split; [ apply H0 | apply H1 ].
  - cbn [wave_iter fst snd]. split.
    + apply (IH j).
    + apply wave_step_ext; intro k; apply (IH k).
Qed.

(* ===================================================================== *)
(*  3. Finite speed and the cone of dependence over n steps                *)
(* ===================================================================== *)

(** Both initial levels are zero on [a, b]  =>  both levels after n steps are
    zero on [a + n, b - n]. For every s and every N. *)
Theorem wave_finite_speed_n : forall s N (u0 u1 : grid_fn) a b,
  (forall k, (a <= k <= b)%nat -> u0 k == 0) ->
  (forall k, (a <= k <= b)%nat -> u1 k == 0) ->
  forall n j, (a + n <= j)%nat -> (j + n <= b)%nat ->
    fst (wave_iter s N u0 u1 n) j == 0 /\ snd (wave_iter s N u0 u1 n) j == 0.
Proof.
  intros s N u0 u1 a b H0 H1 n. induction n as [|n IH]; intros j Ha Hb.
  - cbn [wave_iter fst snd]. split; [ apply H0 | apply H1 ]; lia.
  - cbn [wave_iter fst snd]. split.
    + apply (IH j); lia.
    + apply (wave_step_interior_zero s N _ _ (a + n)%nat (b - n)%nat).
      * intros k Hk. apply (IH k); lia.
      * intros k Hk. apply (IH k); lia.
      * lia.
      * lia.
Qed.

(** A node whose neighbourhood of radius n is quiet stays quiet for n steps. *)
Corollary wave_quiet_n : forall s N (u0 u1 : grid_fn) n j, (n <= j)%nat ->
  (forall k, (j - n <= k <= j + n)%nat -> u0 k == 0) ->
  (forall k, (j - n <= k <= j + n)%nat -> u1 k == 0) ->
  forall m, (m <= n)%nat -> snd (wave_iter s N u0 u1 m) j == 0.
Proof.
  intros s N u0 u1 n j Hn H0 H1 m Hm.
  apply (wave_finite_speed_n s N u0 u1 (j - n)%nat (j + n)%nat H0 H1 m j); lia.
Qed.

(** Two initial states that agree on [a, b] give states that agree on
    [a + n, b - n] after n steps. *)
Theorem wave_dependence_cone_n : forall s N (u0 u1 v0 v1 : grid_fn) a b,
  (forall k, (a <= k <= b)%nat -> u0 k == v0 k) ->
  (forall k, (a <= k <= b)%nat -> u1 k == v1 k) ->
  forall n j, (a + n <= j)%nat -> (j + n <= b)%nat ->
    fst (wave_iter s N u0 u1 n) j == fst (wave_iter s N v0 v1 n) j /\
    snd (wave_iter s N u0 u1 n) j == snd (wave_iter s N v0 v1 n) j.
Proof.
  intros s N u0 u1 v0 v1 a b H0 H1 n. induction n as [|n IH]; intros j Ha Hb.
  - cbn [wave_iter fst snd]. split; [ apply H0 | apply H1 ]; lia.
  - cbn [wave_iter fst snd]. split.
    + apply (IH j); lia.
    + destruct j as [|k]; [ lia | ].
      apply wave_step_dep.
      * cbn [ppred]. apply (IH k); lia.
      * apply (IH (S k)); lia.
      * apply (IH (S (S k))); lia.
      * apply (IH (S k)); lia.
Qed.

(** Pointwise form: the value at the node j after n steps is determined by the
    initial data on [j - n, j + n] (for n <= j). *)
Corollary wave_value_depends_on_cone : forall s N (u0 u1 v0 v1 : grid_fn) n j,
  (n <= j)%nat ->
  (forall k, (j - n <= k <= j + n)%nat -> u0 k == v0 k) ->
  (forall k, (j - n <= k <= j + n)%nat -> u1 k == v1 k) ->
  snd (wave_iter s N u0 u1 n) j == snd (wave_iter s N v0 v1 n) j.
Proof.
  intros s N u0 u1 v0 v1 n j Hn H0 H1.
  apply (wave_dependence_cone_n s N u0 u1 v0 v1 (j - n)%nat (j + n)%nat H0 H1 n j); lia.
Qed.

(** The bound is attained: an impulse at node 3 of a 7-node grid, s = 1/2, two
    steps — node 1 (distance 2) is reached, node 0 (distance 3) is not. *)
Definition wimp3 : grid_fn := fun j => match j with S (S (S O)) => 1 | _ => 0 end.

Lemma wave_two_steps_reach :
  snd (wave_iter (1#2) 7%nat wzero wimp3 2%nat) 1%nat == 1#4 /\
  snd (wave_iter (1#2) 7%nat wzero wimp3 2%nat) 0%nat == 0.
Proof. split; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(*  4. Full periodicity is preserved                                       *)
(* ===================================================================== *)

Lemma wave_step_gperiodic : forall s N (a b : grid_fn), (0 < N)%nat ->
  gperiodic N a -> gperiodic N b -> gperiodic N (wave_step s N a b).
Proof.
  intros s N a b HN Ha Hb k. unfold wave_step.
  rewrite (gperiodic_ppred N b k HN Hb).
  change (S (k + N)) with (S k + N)%nat.
  rewrite (Hb (S k)), (Hb k), (Ha k). reflexivity.
Qed.

Lemma wave_iter_gperiodic : forall s N (u0 u1 : grid_fn) n, (0 < N)%nat ->
  gperiodic N u0 -> gperiodic N u1 ->
  gperiodic N (fst (wave_iter s N u0 u1 n)) /\ gperiodic N (snd (wave_iter s N u0 u1 n)).
Proof.
  intros s N u0 u1 n HN H0 H1. induction n as [|n [IHa IHb]].
  - cbn [wave_iter fst snd]. split; assumption.
  - cbn [wave_iter fst snd]. split; [ exact IHb | apply wave_step_gperiodic; assumption ].
Qed.

(* ===================================================================== *)
(*  5. The Courant number 1: travelling profiles                           *)
(* ===================================================================== *)

Lemma wave_step_courant_one : forall N (a b : grid_fn) j,
  wave_step 1 N a b j == b (S j) + b (ppred N j) - a j.
Proof. intros. unfold wave_step. ring. Qed.

(** One step: the levels F(j), F(j+1) give the next level F(j+2) — at every node
    of a periodic profile. *)
Lemma wave_travelling_step : forall N (F : grid_fn) j, (0 < N)%nat -> gperiodic N F ->
  wave_step 1 N F (fun k => F (S k)) j == F (S (S j)).
Proof.
  intros N F j HN HF. rewrite wave_step_courant_one. cbv beta.
  destruct j as [|k].
  - destruct N as [|m]; [ lia | ]. cbn [ppred Nat.pred].
    pose proof (HF 0%nat) as H. cbn [Nat.add] in H. rewrite H. ring.
  - cbn [ppred]. ring.
Qed.

(** The whole process: after n steps the two levels are F(n + j) and F(n + j + 1). *)
Theorem wave_travelling_n : forall N (F : grid_fn) n, (0 < N)%nat -> gperiodic N F ->
  forall j,
    fst (wave_iter 1 N F (fun k => F (S k)) n) j == F (n + j)%nat /\
    snd (wave_iter 1 N F (fun k => F (S k)) n) j == F (S (n + j)).
Proof.
  intros N F n HN HF. induction n as [|n IH]; intro j.
  - cbn [wave_iter fst snd Nat.add]. split; reflexivity.
  - cbn [wave_iter fst snd Nat.add]. split.
    + apply (IH j).
    + set (G := fun k : nat => F (n + k)%nat).
      assert (HG : gperiodic N G).
      { intro k. unfold G. replace (n + (k + N))%nat with ((n + k) + N)%nat by lia.
        apply HF. }
      rewrite (wave_step_ext 1 N _ _ G (fun k => G (S k))).
      * rewrite (wave_travelling_step N G j HN HG). unfold G.
        replace (n + S (S j))%nat with (S (S (n + j))) by lia. reflexivity.
      * intro k. unfold G. apply (IH k).
      * intro k. unfold G. replace (n + S k)%nat with (S (n + k)) by lia. apply (IH k).
Qed.

(** The profile travelling the other way, one step at an interior node: the
    levels F(j+1), F(j) give the next level F(j-1). *)
Lemma wave_travelling_right : forall N (F : grid_fn) k,
  wave_step 1 N (fun j => F (S j)) F (S k) == F k.
Proof. intros. unfold wave_step. cbn [ppred]. ring. Qed.

Print Assumptions wave_finite_speed_n.
Print Assumptions wave_dependence_cone_n.
Print Assumptions wave_travelling_n.
