(** * GameTheory.v -- Games as ToS Systems

    Theory of Systems -- Verified Standard Library (Batch 5)

    Elements: strategy profiles
    Roles:    player_i -> DecisionMaker
    Rules:    payoff function (constitution: determines game)
    Status:   nash_equilibrium | dominated | pareto_optimal | unstable

    Connection: FixedPoint.v -- Nash = fixed point of best-response
    Connection: ConditionalProbability.v -- mixed strategies = probability distributions

    STATUS: 25 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.
Open Scope Q_scope.

Definition StrategyProfile := nat -> nat.

Definition update_profile (p : StrategyProfile) (i si : nat) : StrategyProfile :=
  fun j => if Nat.eqb j i then si else p j.

Record Game := mkGame {
  gm_players : nat;
  gm_strategies : nat -> nat;
  gm_payoff : StrategyProfile -> nat -> Q;
}.

Definition is_best_response (g : Game) (profile : StrategyProfile) (i : nat) (si : nat) : Prop :=
  forall si2, (si2 < gm_strategies g i)%nat ->
    gm_payoff g (update_profile profile i si) i >= gm_payoff g (update_profile profile i si2) i.

Definition is_nash (g : Game) (profile : StrategyProfile) : Prop :=
  forall i, (i < gm_players g)%nat ->
    is_best_response g profile i (profile i).

Definition strictly_dominated (g : Game) (i : nat) (si sd : nat) : Prop :=
  forall profile : StrategyProfile,
    gm_payoff g (update_profile profile i sd) i > gm_payoff g (update_profile profile i si) i.

Definition weakly_dominated (g : Game) (i : nat) (si sd : nat) : Prop :=
  (forall profile, gm_payoff g (update_profile profile i sd) i >= gm_payoff g (update_profile profile i si) i) /\
  (exists profile, gm_payoff g (update_profile profile i sd) i > gm_payoff g (update_profile profile i si) i).

Definition pareto_optimal (g : Game) (profile : StrategyProfile) : Prop :=
  ~ exists pa,
    (forall i, (i < gm_players g)%nat -> gm_payoff g pa i >= gm_payoff g profile i) /\
    (exists j, (j < gm_players g)%nat /\ gm_payoff g pa j > gm_payoff g profile j).

Definition is_zero_sum (g : Game) : Prop :=
  gm_players g = 2%nat /\
  forall profile, gm_payoff g profile 0 + gm_payoff g profile 1 == 0.

Definition is_symmetric_2p (g : Game) : Prop :=
  gm_players g = 2%nat /\
  forall profile,
    gm_payoff g profile 0 ==
    gm_payoff g (fun j => if Nat.eqb j 0 then profile 1%nat else profile 0%nat) 1%nat.

Lemma update_profile_same : forall (p : StrategyProfile) (i si : nat),
  update_profile p i si i = si.
Proof.
  intros p i si. unfold update_profile. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma update_profile_other : forall (p : StrategyProfile) (i j si : nat),
  i <> j -> update_profile p i si j = p j.
Proof.
  intros p i j si Hneq. unfold update_profile.
  destruct (Nat.eqb_spec j i) as [Heq | _].
  - exfalso. apply Hneq. symmetry. exact Heq.
  - reflexivity.
Qed.

Lemma update_profile_overwrite : forall (p : StrategyProfile) (i si si2 : nat),
  update_profile (update_profile p i si2) i si = update_profile p i si.
Proof.
  intros p i si si2. apply functional_extensionality. intros j.
  unfold update_profile. destruct (Nat.eqb j i); reflexivity.
Qed.

Lemma update_profile_comm : forall (p : StrategyProfile) (i j si sj : nat),
  i <> j ->
  update_profile (update_profile p i si) j sj =
  update_profile (update_profile p j sj) i si.
Proof.
  intros p i j si sj Hneq. apply functional_extensionality. intros k.
  unfold update_profile.
  destruct (Nat.eqb_spec k j) as [Hkj | Hkj];
  destruct (Nat.eqb_spec k i) as [Hki | Hki]; try reflexivity.
  - exfalso. apply Hneq. rewrite <- Hki. exact Hkj.
Qed.

Lemma update_profile_id : forall (p : StrategyProfile) (i : nat),
  update_profile p i (p i) = p.
Proof.
  intros p i. apply functional_extensionality. intros j.
  unfold update_profile.
  destruct (Nat.eqb_spec j i) as [Heq | _].
  - rewrite Heq. reflexivity.
  - reflexivity.
Qed.

Lemma nash_is_best_response : forall (g : Game) (p : StrategyProfile) (i : nat),
  is_nash g p -> (i < gm_players g)%nat ->
  is_best_response g p i (p i).
Proof. intros g p i Hnash Hi. exact (Hnash i Hi). Qed.

Lemma dominated_not_best_response : forall (g : Game) (profile : StrategyProfile) (i si sd : nat),
  strictly_dominated g i si sd ->
  (sd < gm_strategies g i)%nat ->
  ~ is_best_response g profile i si.
Proof.
  intros g profile i si sd Hdom Hsd Hbest.
  unfold strictly_dominated in Hdom. unfold is_best_response in Hbest.
  specialize (Hdom profile). specialize (Hbest sd Hsd). lra.
Qed.

Lemma nash_not_dominated : forall (g : Game) (p : StrategyProfile) (i sd : nat),
  is_nash g p -> (i < gm_players g)%nat ->
  (sd < gm_strategies g i)%nat ->
  ~ strictly_dominated g i (p i) sd.
Proof.
  intros g p i sd Hnash Hi Hsd Hdom.
  apply (dominated_not_best_response g p i (p i) sd Hdom Hsd).
  exact (Hnash i Hi).
Qed.

Lemma weakly_dominated_ge : forall (g : Game) (i si sd : nat),
  weakly_dominated g i si sd ->
  forall profile, gm_payoff g (update_profile profile i sd) i >=
                  gm_payoff g (update_profile profile i si) i.
Proof. intros g i si sd [Hweak _] profile. exact (Hweak profile). Qed.

Lemma strict_implies_weak : forall (g : Game) (i si sd : nat),
  strictly_dominated g i si sd ->
  (exists profile : StrategyProfile, True) ->
  weakly_dominated g i si sd.
Proof.
  intros g i si sd Hstrict [px _]. split.
  - intros profile. specialize (Hstrict profile). lra.
  - exists px. exact (Hstrict px).
Qed.

Definition pd_payoff (profile : StrategyProfile) (player : nat) : Q :=
  let s0 := profile 0%nat in
  let s1 := profile 1%nat in
  if Nat.eqb player 0%nat then
    (if Nat.eqb s0 0%nat then
       (if Nat.eqb s1 0%nat then 3 else 0)
     else
       (if Nat.eqb s1 0%nat then 5 else 1))
  else
    (if Nat.eqb s1 0%nat then
       (if Nat.eqb s0 0%nat then 3 else 0)
     else
       (if Nat.eqb s0 0%nat then 5 else 1)).

Definition prisoners_dilemma : Game := mkGame 2%nat (fun _ => 2%nat) pd_payoff.
Definition pd_defect : StrategyProfile := fun _ => 1%nat.
Definition pd_coop : StrategyProfile := fun _ => 0%nat.

Lemma pd_payoff_compute_dd_0 : pd_payoff pd_defect 0 == 1.
Proof. unfold pd_payoff, pd_defect. simpl. lra. Qed.

Lemma pd_payoff_compute_dd_1 : pd_payoff pd_defect 1 == 1.
Proof. unfold pd_payoff, pd_defect. simpl. lra. Qed.

Lemma pd_payoff_compute_cc_0 : pd_payoff pd_coop 0 == 3.
Proof. unfold pd_payoff, pd_coop. simpl. lra. Qed.

Lemma pd_payoff_compute_cc_1 : pd_payoff pd_coop 1 == 3.
Proof. unfold pd_payoff, pd_coop. simpl. lra. Qed.

Ltac pd_player_cases i :=
  destruct i as [| i_tmp]; [| destruct i_tmp as [| i_tmp2]; [| lia]].

Ltac pd_strategy_cases si :=
  destruct si as [| si_tmp]; [| destruct si_tmp as [| si_tmp2]; [| lia]].

Theorem pd_defect_is_nash : is_nash prisoners_dilemma pd_defect.
Proof.
  unfold is_nash, is_best_response, prisoners_dilemma, pd_defect.
  simpl. intros i Hi sa Hsa.
  pd_player_cases i.
  - pd_strategy_cases sa.
    + unfold pd_payoff, update_profile. simpl. lra.
    + unfold pd_payoff, update_profile. simpl. lra.
  - pd_strategy_cases sa.
    + unfold pd_payoff, update_profile. simpl. lra.
    + unfold pd_payoff, update_profile. simpl. lra.
Qed.

Theorem pd_coop_not_nash : ~ is_nash prisoners_dilemma pd_coop.
Proof.
  unfold is_nash, is_best_response, prisoners_dilemma, pd_coop.
  simpl. intro H.
  specialize (H 0%nat ltac:(lia) 1%nat ltac:(lia)).
  unfold pd_payoff, update_profile in H. simpl in H. lra.
Qed.

Theorem pd_coop_pareto : pareto_optimal prisoners_dilemma pd_coop.
Proof.
  unfold pareto_optimal, prisoners_dilemma, pd_coop. simpl.
  intros [pa [Hall [j [Hj Hmore]]]].
  assert (H0 : pd_payoff pa 0%nat >= 3) by (apply (Hall 0%nat); lia).
  assert (H1 : pd_payoff pa 1%nat >= 3) by (apply (Hall 1%nat); lia).
  unfold pd_payoff in H0, H1, Hmore. simpl in H0, H1, Hmore.
  remember (pa 0%nat) as s0. remember (pa 1%nat) as s1.
  destruct s0 as [| [| s0']]; destruct s1 as [| [| s1']]; simpl in *;
  try lra; pd_player_cases j; lra.
Qed.

Theorem pd_defect_not_pareto : ~ pareto_optimal prisoners_dilemma pd_defect.
Proof.
  unfold pareto_optimal, prisoners_dilemma, pd_defect. simpl.
  intro H. apply H. clear H.
  exists pd_coop. split.
  - intros i Hi. pd_player_cases i;
    unfold pd_payoff, pd_coop; simpl; lra.
  - exists 0%nat. split; [lia |].
    unfold pd_payoff, pd_coop. simpl. lra.
Qed.

Theorem pd_defect_dominates_coop_p0 : strictly_dominated prisoners_dilemma 0 0 1.
Proof.
  unfold strictly_dominated, prisoners_dilemma. simpl. intros profile.
  unfold pd_payoff, update_profile. simpl.
  remember (profile 1%nat) as s1.
  destruct s1 as [| [| s1']]; simpl; lra.
Qed.

Theorem pd_defect_dominates_coop_p1 : strictly_dominated prisoners_dilemma 1 0 1.
Proof.
  unfold strictly_dominated, prisoners_dilemma. simpl. intros profile.
  unfold pd_payoff, update_profile. simpl.
  remember (profile 0%nat) as s0.
  destruct s0 as [| [| s0']]; simpl; lra.
Qed.

Theorem all_dominated_not_nash : forall (g : Game) (p : StrategyProfile),
  (forall i, (i < gm_players g)%nat ->
    exists sd, (sd < gm_strategies g i)%nat /\ strictly_dominated g i (p i) sd) ->
  (0 < gm_players g)%nat ->
  ~ is_nash g p.
Proof.
  intros g p Hdom Hpos Hnash.
  destruct (Hdom 0%nat Hpos) as [sd [Hsd Hstrict]].
  exact (nash_not_dominated g p 0%nat sd Hnash Hpos Hsd Hstrict).
Qed.

Theorem zero_sum_opposite : forall (g : Game) (p pa : StrategyProfile),
  is_zero_sum g ->
  gm_payoff g pa 0 > gm_payoff g p 0 ->
  gm_payoff g pa 1 < gm_payoff g p 1.
Proof.
  intros g p pa [_ Hzs] Hgt.
  assert (Hz1 := Hzs p). assert (Hz2 := Hzs pa). lra.
Qed.

Theorem zero_sum_equal : forall (g : Game) (p pa : StrategyProfile),
  is_zero_sum g ->
  gm_payoff g pa 0 == gm_payoff g p 0 ->
  gm_payoff g pa 1 == gm_payoff g p 1.
Proof.
  intros g p pa [_ Hzs] Heq.
  assert (Hz1 := Hzs p). assert (Hz2 := Hzs pa). lra.
Qed.

Theorem pd_is_symmetric : is_symmetric_2p prisoners_dilemma.
Proof.
  unfold is_symmetric_2p, prisoners_dilemma. simpl.
  split; [reflexivity |]. intros profile.
  unfold pd_payoff. simpl.
  remember (profile 0%nat) as s0. remember (profile 1%nat) as s1.
  destruct s0 as [| [| s0']]; destruct s1 as [| [| s1']]; simpl; lra.
Qed.

Theorem pareto_equiv : forall (g : Game) (p1 p2 : StrategyProfile),
  (forall i, (i < gm_players g)%nat -> gm_payoff g p1 i == gm_payoff g p2 i) ->
  pareto_optimal g p1 -> pareto_optimal g p2.
Proof.
  intros g p1 p2 Heq Hpar.
  unfold pareto_optimal in *. intro Hex. apply Hpar. clear Hpar.
  destruct Hex as [pa [Hall [j [Hj Hmore]]]].
  exists pa. split.
  - intros i Hi. specialize (Hall i Hi). specialize (Heq i Hi). lra.
  - exists j. split; [exact Hj |]. specialize (Heq j Hj). lra.
Qed.

(** TOTAL: 25 Qed, 0 Admitted, 0 axioms *)
