(** * MDPFoundations.v — Markov Decision Processes as ToS Systems

    Theory of Systems — Verified Standard Library (Tier 2b)

    Elements: states, actions, transitions, rewards
    Roles:    state → CurrentSituation, action → Decision, reward → Feedback
    Rules:    Bellman equation (constitution = optimality principle)
    Status:   value_known | value_estimated | policy_optimal

    Connection: FixedPoint.v (Bellman = contraction → Banach)
    Connection: ReasoningConvergence.v (pipeline ≅ value iteration)

    STATUS: 24 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qminmax.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Close Scope Z_scope.
Open Scope Q_scope.

(* ========================================================================= *)
(* AUXILIARY LEMMA                                                            *)
(* ========================================================================= *)

(** Left multiplication preserves <= (not in Rocq 9.0 stdlib) *)
Lemma Qmult_le_compat_l : forall x y z : Q,
  x <= y -> 0 <= z -> z * x <= z * y.
Proof.
  intros x y z Hxy Hz.
  setoid_replace (z * x) with (x * z) by ring.
  setoid_replace (z * y) with (y * z) by ring.
  apply Qmult_le_compat_r; assumption.
Qed.

(* ========================================================================= *)
(* SECTION 1: VALUE FUNCTIONS AND WEIGHTED SUMS                              *)
(* ========================================================================= *)

(** Value function: maps state index to Q-value *)
Definition ValueFn := nat -> Q.

(** Zero value function *)
Definition zero_vf : ValueFn := fun _ => 0.

(** Weighted sum: sum_{k=0}^{n-1} T(k) * V(k) *)
Fixpoint weighted_sum (T : nat -> Q) (V : nat -> Q) (n : nat) : Q :=
  match n with
  | O => 0
  | S k => T k * V k + weighted_sum T V k
  end.

(** Sup-norm for value functions on {0, ..., n-1} *)
Fixpoint max_diff (V1 V2 : ValueFn) (n : nat) : Q :=
  match n with
  | O => 0
  | S k => Qmax (Qabs (V1 k - V2 k)) (max_diff V1 V2 k)
  end.

(* ========================================================================= *)
(* SECTION 2: WEIGHTED SUM PROPERTIES (8 Qed)                               *)
(* ========================================================================= *)

(** Theorem 1: weighted sum with zero value function *)
Lemma weighted_sum_zero_V : forall T n,
  weighted_sum T (fun _ => 0) n == 0.
Proof.
  intros T n. induction n as [| k IHk].
  - simpl. reflexivity.
  - simpl. rewrite IHk. ring.
Qed.

(** Theorem 2: weighted sum of nonneg terms is nonneg *)
Lemma weighted_sum_nonneg : forall T V n,
  (forall k, 0 <= T k) -> (forall k, 0 <= V k) ->
  0 <= weighted_sum T V n.
Proof.
  intros T V n HT HV. induction n as [| k IHk].
  - simpl. lra.
  - simpl.
    assert (Hprod : 0 <= T k * V k).
    { apply Qmult_le_0_compat; [apply HT | apply HV]. }
    lra.
Qed.

(** Theorem 3: weighted sum scales linearly *)
Lemma weighted_sum_scale : forall T c V n,
  weighted_sum T (fun k => c * V k) n == c * weighted_sum T V n.
Proof.
  intros T c V n. induction n as [| k IHk].
  - simpl. ring.
  - simpl. rewrite IHk. ring.
Qed.

(** Theorem 4: weighted sum distributes over addition *)
Lemma weighted_sum_add : forall T V1 V2 n,
  weighted_sum T (fun k => V1 k + V2 k) n ==
  weighted_sum T V1 n + weighted_sum T V2 n.
Proof.
  intros T V1 V2 n. induction n as [| k IHk].
  - simpl. ring.
  - simpl. rewrite IHk. ring.
Qed.

(** Theorem 5: weighted sum distributes over difference *)
Lemma weighted_sum_diff : forall T V1 V2 n,
  weighted_sum T (fun k => V1 k - V2 k) n ==
  weighted_sum T V1 n - weighted_sum T V2 n.
Proof.
  intros T V1 V2 n. induction n as [| k IHk].
  - simpl. ring.
  - simpl. rewrite IHk. ring.
Qed.

(** Theorem 6: pointwise bound on values gives weighted sum bound *)
Lemma weighted_sum_le_pointwise : forall T V1 V2 n,
  (forall k, 0 <= T k) ->
  (forall k, (k < n)%nat -> V1 k <= V2 k) ->
  weighted_sum T V1 n <= weighted_sum T V2 n.
Proof.
  intros T V1 V2 n HT HV. induction n as [| k IHk].
  - simpl. lra.
  - simpl.
    assert (Hprod : T k * V1 k <= T k * V2 k).
    { apply Qmult_le_compat_l; [apply HV; lia | apply HT]. }
    assert (Htail : weighted_sum T V1 k <= weighted_sum T V2 k).
    { apply IHk. intros j Hj. apply HV. lia. }
    lra.
Qed.

(** Theorem 7: weighted sum of a constant *)
Lemma weighted_sum_const : forall T c n,
  weighted_sum T (fun _ => c) n == c * weighted_sum T (fun _ => 1) n.
Proof.
  intros T c n. induction n as [| k IHk].
  - simpl. ring.
  - simpl. rewrite IHk. ring.
Qed.

(** Theorem 8: absolute value of weighted sum bounded by weighted sum of abs *)
Lemma weighted_sum_abs_le : forall T V n,
  (forall k, 0 <= T k) ->
  Qabs (weighted_sum T V n) <= weighted_sum T (fun k => Qabs (V k)) n.
Proof.
  intros T V n HT. induction n as [| k IHk].
  - simpl. assert (Hz : Qabs 0 == 0) by (apply Qabs_pos; lra). lra.
  - simpl.
    apply Qle_trans with (Qabs (T k * V k) + Qabs (weighted_sum T V k)).
    + exact (Qabs_triangle (T k * V k) (weighted_sum T V k)).
    + assert (Hprod : Qabs (T k * V k) == T k * Qabs (V k)).
      { rewrite Qabs_Qmult. rewrite (Qabs_pos (T k)); [reflexivity | apply HT]. }
      lra.
Qed.

(* ========================================================================= *)
(* SECTION 3: SUP-NORM PROPERTIES (5 Qed)                                   *)
(* ========================================================================= *)

(** Theorem 9: max_diff is nonneg *)
Lemma max_diff_nonneg : forall V1 V2 n,
  0 <= max_diff V1 V2 n.
Proof.
  intros V1 V2 n. induction n as [| k IHk].
  - simpl. lra.
  - simpl. apply Qle_trans with (Qabs (V1 k - V2 k)).
    + apply Qabs_nonneg.
    + apply Q.le_max_l.
Qed.

(** Theorem 10: max_diff is symmetric *)
Lemma max_diff_sym : forall V1 V2 n,
  max_diff V1 V2 n == max_diff V2 V1 n.
Proof.
  intros V1 V2 n. induction n as [| k IHk].
  - simpl. reflexivity.
  - simpl.
    assert (Habs_eq : Qabs (V1 k - V2 k) == Qabs (V2 k - V1 k)).
    { assert (Hopp : V2 k - V1 k == -(V1 k - V2 k)) by ring.
      apply Qabs_wd in Hopp. rewrite Hopp. symmetry. apply Qabs_opp. }
    rewrite Habs_eq. rewrite IHk. reflexivity.
Qed.

(** Theorem 11: max_diff of identical functions is 0 *)
Lemma max_diff_zero : forall V n,
  max_diff V V n == 0.
Proof.
  intros V n. induction n as [| k IHk].
  - simpl. reflexivity.
  - simpl.
    assert (Habs0 : Qabs (V k - V k) == 0).
    { assert (Hz : V k - V k == 0) by ring.
      apply Qabs_wd in Hz. rewrite Hz. apply Qabs_pos. lra. }
    rewrite IHk.
    destruct (Q.max_dec (Qabs (V k - V k)) 0) as [Hl | Hr].
    + rewrite Hl. exact Habs0.
    + rewrite Hr. reflexivity.
Qed.

(** Theorem 12: each component is bounded by max_diff *)
Lemma max_diff_component_le : forall V1 V2 n k,
  (k < n)%nat -> Qabs (V1 k - V2 k) <= max_diff V1 V2 n.
Proof.
  intros V1 V2 n. induction n as [| n' IHn']; intros k Hlt.
  - lia.
  - simpl. destruct (Nat.eq_dec k n') as [Heq | Hneq].
    + subst k. apply Q.le_max_l.
    + apply Qle_trans with (max_diff V1 V2 n').
      * apply IHn'. lia.
      * apply Q.le_max_r.
Qed.

(** Theorem 13: max_diff satisfies triangle inequality *)
Lemma max_diff_triangle : forall V1 V2 V3 n,
  max_diff V1 V3 n <= max_diff V1 V2 n + max_diff V2 V3 n.
Proof.
  intros V1 V2 V3 n. induction n as [| k IHk].
  - simpl. lra.
  - simpl.
    assert (Hcomp : Qabs (V1 k - V3 k) <= Qabs (V1 k - V2 k) + Qabs (V2 k - V3 k)).
    { assert (Hdecomp : V1 k - V3 k == (V1 k - V2 k) + (V2 k - V3 k)) by ring.
      apply Qabs_wd in Hdecomp. rewrite Hdecomp. apply Qabs_triangle. }
    set (s := Qmax (Qabs (V1 k - V2 k)) (max_diff V1 V2 k) +
              Qmax (Qabs (V2 k - V3 k)) (max_diff V2 V3 k)).
    assert (Hcomp_le : Qabs (V1 k - V3 k) <= s).
    { unfold s.
      apply Qle_trans with (Qabs (V1 k - V2 k) + Qabs (V2 k - V3 k)); [exact Hcomp |].
      apply Qplus_le_compat; [apply Q.le_max_l | apply Q.le_max_l]. }
    assert (Htail_le : max_diff V1 V3 k <= s).
    { unfold s.
      apply Qle_trans with (max_diff V1 V2 k + max_diff V2 V3 k); [exact IHk |].
      apply Qplus_le_compat; [apply Q.le_max_r | apply Q.le_max_r]. }
    destruct (Q.max_dec (Qabs (V1 k - V3 k)) (max_diff V1 V3 k)) as [Hl | Hr].
    + rewrite Hl. exact Hcomp_le.
    + rewrite Hr. exact Htail_le.
Qed.

(* ========================================================================= *)
(* SECTION 4: MDP RECORD AND BELLMAN OPERATOR                               *)
(* ========================================================================= *)

(** Simplified MDP: fixed policy, finite state space {0, ..., n-1} *)
Record MDP := mkMDP {
  mdp_n : nat;
  mdp_reward : nat -> Q;
  mdp_transition : nat -> nat -> Q;
  mdp_gamma : Q;
  mdp_gamma_pos : 0 < mdp_gamma;
  mdp_gamma_lt1 : mdp_gamma < 1;
  mdp_trans_nonneg : forall s s', 0 <= mdp_transition s s';
  mdp_trans_sum_le1 : forall s,
    weighted_sum (mdp_transition s) (fun _ => 1) (mdp_n) <= 1
}.

(** Bellman operator for a fixed policy *)
Definition bellman (m : MDP) (V : ValueFn) (s : nat) : Q :=
  mdp_reward m s + mdp_gamma m * weighted_sum (mdp_transition m s) V (mdp_n m).

(** Value iteration: iterate the Bellman operator *)
Fixpoint value_iter (m : MDP) (V0 : ValueFn) (steps : nat) : ValueFn :=
  match steps with
  | O => V0
  | S k => bellman m (value_iter m V0 k)
  end.

(* ========================================================================= *)
(* SECTION 5: BELLMAN PROPERTIES (3 Qed)                                     *)
(* ========================================================================= *)

(** Theorem 14: Bellman of zero_vf gives the immediate reward *)
Lemma bellman_zero_vf : forall m s,
  bellman m zero_vf s == mdp_reward m s.
Proof.
  intros m s. unfold bellman, zero_vf.
  rewrite weighted_sum_zero_V. ring.
Qed.

(** Theorem 15: value_iter at step 0 is the initial value function *)
Lemma value_iter_zero : forall m V0,
  value_iter m V0 0 = V0.
Proof.
  intros m V0. simpl. reflexivity.
Qed.

(** Theorem 16: value_iter unfolds one step *)
Lemma value_iter_succ : forall m V0 n,
  value_iter m V0 (S n) = bellman m (value_iter m V0 n).
Proof.
  intros m V0 n. simpl. reflexivity.
Qed.

(* ========================================================================= *)
(* SECTION 6: BELLMAN CONTRACTION (2 Qed)                                    *)
(* ========================================================================= *)

(** Theorem 17 (KEY): Bellman contraction per state.
    |B(V1)(s) - B(V2)(s)| <= gamma * max_diff V1 V2 n *)
Lemma bellman_contraction_state : forall m V1 V2 s,
  Qabs (bellman m V1 s - bellman m V2 s) <=
  mdp_gamma m * max_diff V1 V2 (mdp_n m).
Proof.
  intros m V1 V2 s.
  assert (Hgpos : 0 < mdp_gamma m) by apply (mdp_gamma_pos m).
  (* Rewrite difference *)
  assert (Hdiff : bellman m V1 s - bellman m V2 s ==
    mdp_gamma m * weighted_sum (mdp_transition m s)
      (fun k => V1 k - V2 k) (mdp_n m)).
  { unfold bellman. rewrite weighted_sum_diff. ring. }
  apply Qabs_wd in Hdiff. rewrite Hdiff.
  (* Factor gamma out of abs *)
  rewrite Qabs_Qmult.
  rewrite (Qabs_pos (mdp_gamma m)); [| lra].
  apply Qmult_le_compat_l; [| lra].
  (* |ws T (V1-V2) n| <= ws T |V1-V2| n *)
  apply Qle_trans with
    (weighted_sum (mdp_transition m s) (fun k => Qabs (V1 k - V2 k)) (mdp_n m)).
  { apply weighted_sum_abs_le. apply (mdp_trans_nonneg m s). }
  (* ws T |V1-V2| n <= ws T (fun _ => max_diff) n *)
  apply Qle_trans with
    (weighted_sum (mdp_transition m s)
      (fun _ => max_diff V1 V2 (mdp_n m)) (mdp_n m)).
  { apply weighted_sum_le_pointwise.
    - apply (mdp_trans_nonneg m s).
    - intros k Hk. apply max_diff_component_le. exact Hk. }
  (* ws T c n = c * ws T 1 n <= c * 1 <= c *)
  rewrite weighted_sum_const.
  apply Qle_trans with (max_diff V1 V2 (mdp_n m) * 1).
  { apply Qmult_le_compat_l;
    [apply (mdp_trans_sum_le1 m s) | apply max_diff_nonneg]. }
  lra.
Qed.

(** Theorem 18: Global contraction —
    max_diff (B V1) (B V2) n <= gamma * max_diff V1 V2 (mdp_n m) *)
Lemma bellman_contraction : forall m V1 V2 n,
  (n <= mdp_n m)%nat ->
  max_diff (bellman m V1) (bellman m V2) n <=
  mdp_gamma m * max_diff V1 V2 (mdp_n m).
Proof.
  intros m V1 V2 n Hle.
  assert (Hgpos : 0 < mdp_gamma m) by apply (mdp_gamma_pos m).
  induction n as [| k IHk].
  - simpl. apply Qmult_le_0_compat; [lra | apply max_diff_nonneg].
  - simpl.
    assert (Hk_le : (k <= mdp_n m)%nat) by lia.
    specialize (IHk Hk_le).
    destruct (Q.max_dec (Qabs (bellman m V1 k - bellman m V2 k))
                        (max_diff (bellman m V1) (bellman m V2) k)) as [Hl | Hr].
    + rewrite Hl. apply bellman_contraction_state.
    + rewrite Hr. exact IHk.
Qed.

(* ========================================================================= *)
(* SECTION 7: BELLMAN MONOTONICITY (1 Qed)                                  *)
(* ========================================================================= *)

(** Theorem 19: Bellman is monotone —
    if V1 <= V2 pointwise, then B(V1) <= B(V2) *)
Lemma bellman_monotone : forall m V1 V2,
  (forall s, V1 s <= V2 s) ->
  forall s, bellman m V1 s <= bellman m V2 s.
Proof.
  intros m V1 V2 HV s.
  unfold bellman.
  assert (Hgpos : 0 < mdp_gamma m) by apply (mdp_gamma_pos m).
  assert (Hws : weighted_sum (mdp_transition m s) V1 (mdp_n m) <=
                weighted_sum (mdp_transition m s) V2 (mdp_n m)).
  { apply weighted_sum_le_pointwise.
    - apply (mdp_trans_nonneg m s).
    - intros k _. apply HV. }
  assert (Hgws : mdp_gamma m * weighted_sum (mdp_transition m s) V1 (mdp_n m) <=
                 mdp_gamma m * weighted_sum (mdp_transition m s) V2 (mdp_n m)).
  { apply Qmult_le_compat_l; [exact Hws | lra]. }
  lra.
Qed.

(* ========================================================================= *)
(* SECTION 8: CONCRETE 2-STATE MDP EXAMPLE (4 Qed)                          *)
(* ========================================================================= *)

(**
   2-state MDP:
   - State 0: reward = 1, transitions: 1/2 to each state
   - State 1: reward = 1/2, transitions: 1/2 to each state
   - Discount factor gamma = 1/2
*)

Definition two_state_reward (s : nat) : Q :=
  if Nat.eqb s 0%nat then 1 else (1#2).

Definition two_state_gamma : Q := (1#2).

(** Bellman for 2-state: R(s) + gamma * (1/2 * V(0) + 1/2 * V(1)) *)
Definition bellman_2s (V : ValueFn) (s : nat) : Q :=
  two_state_reward s + two_state_gamma * ((1#2) * V 0%nat + (1#2) * V 1%nat).

(** Theorem 20: B(0)(0) = 1 *)
Lemma two_state_V0_s0 : bellman_2s zero_vf 0%nat == 1.
Proof.
  unfold bellman_2s, zero_vf, two_state_reward, two_state_gamma. simpl. ring.
Qed.

(** Theorem 21: B(0)(1) = 1/2 *)
Lemma two_state_V0_s1 : bellman_2s zero_vf 1%nat == (1#2).
Proof.
  unfold bellman_2s, zero_vf, two_state_reward, two_state_gamma. simpl. ring.
Qed.

(** Theorem 22: B^2(0)(0) = 11/8 *)
Lemma two_state_V1_s0 :
  bellman_2s (bellman_2s zero_vf) 0%nat == (11#8).
Proof.
  unfold bellman_2s, zero_vf, two_state_reward, two_state_gamma. simpl. ring.
Qed.

(** Theorem 23: B^2(0)(1) = 7/8 *)
Lemma two_state_V1_s1 :
  bellman_2s (bellman_2s zero_vf) 1%nat == (7#8).
Proof.
  unfold bellman_2s, zero_vf, two_state_reward, two_state_gamma. simpl. ring.
Qed.

(* ========================================================================= *)
(* THEOREM INVENTORY                                                          *)
(* ========================================================================= *)

(**
  THEOREM INVENTORY (24 Qed, 0 Admitted)
  ========================================

  Auxiliary (1 Qed):
      Qmult_le_compat_l         — left multiplication preserves <=

  Weighted sum (8 Qed):
   1. weighted_sum_zero_V        — ws with zero value = 0
   2. weighted_sum_nonneg        — ws of nonneg terms is nonneg
   3. weighted_sum_scale         — ws distributes scalar
   4. weighted_sum_add           — ws distributes over addition
   5. weighted_sum_diff          — ws distributes over difference
   6. weighted_sum_le_pointwise  — pointwise bound on ws
   7. weighted_sum_const         — ws of constant = c * ws of 1
   8. weighted_sum_abs_le        — |ws| <= ws of |.|

  Sup-norm (5 Qed):
   9. max_diff_nonneg            — sup-norm is nonneg
  10. max_diff_sym               — sup-norm is symmetric
  11. max_diff_zero              — sup-norm of V with itself is 0
  12. max_diff_component_le      — each component <= sup-norm
  13. max_diff_triangle           — triangle inequality

  Bellman abstract (6 Qed):
  14. bellman_zero_vf             — B(0) = reward
  15. value_iter_zero             — iter 0 = V0
  16. value_iter_succ             — iter (S n) = B(iter n)
  17. bellman_contraction_state   — per-state contraction (KEY)
  18. bellman_contraction         — global sup-norm contraction
  19. bellman_monotone            — V1 <= V2 => B(V1) <= B(V2)

  2-state concrete (4 Qed):
  20. two_state_V0_s0             — B(0)(0) = 1
  21. two_state_V0_s1             — B(0)(1) = 1/2
  22. two_state_V1_s0             — B^2(0)(0) = 11/8
  23. two_state_V1_s1             — B^2(0)(1) = 7/8

  Total: 24 Qed, 0 Admitted, 0 axioms
*)
