(** * InterferenceSignals.v — Signals combine like quantum amplitudes
    Elements: signals (value, timeframe), timeframe groups;
    Roles:    group_sum aggregates by timeframe, final_signal weights across;
    Rules:    destructive interference cancels, constructive reinforces.
    STATUS: 20 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================ *)
(* Core definitions                                                  *)
(* ================================================================ *)

(* A signal is a (value, timeframe) pair *)
Definition Signal := (Q * nat)%type.

(* Sum all signal values belonging to a given timeframe *)
Fixpoint group_sum (timeframe : nat) (signals : list Signal) : Q :=
  match signals with
  | [] => 0
  | (v, tf) :: rest =>
    (if Nat.eqb tf timeframe then v else 0) + group_sum timeframe rest
  end.

(* Weighted combination across timeframes *)
Definition final_signal (w1 w4 w24 : Q)
  (signals : list Signal) : Q :=
  w1 * group_sum 1 signals +
  w4 * group_sum 4 signals +
  w24 * group_sum 24 signals.

(* ================================================================ *)
(* Concrete signal sets                                              *)
(* ================================================================ *)

(* Two opposite 1hr signals: destructive interference *)
Definition destructive_1hr : list Signal :=
  [(1, 1%nat); (-(1), 1%nat)].

(* Two aligned 1hr signals: constructive interference *)
Definition constructive_1hr : list Signal :=
  [(1, 1%nat); (1, 1%nat)].

(* Signals on independent timeframes *)
Definition independent_signals : list Signal :=
  [(1, 1%nat); (1, 4%nat); (1, 24%nat)].

(* Three 1hr signals: 2 bullish, 1 bearish *)
Definition three_1hr : list Signal :=
  [(1, 1%nat); (1, 1%nat); (-(1), 1%nat)].

(* Mixed timeframe signals *)
Definition mixed_signals : list Signal :=
  [(1, 1%nat); (-(1), 1%nat); (3, 4%nat); (1, 24%nat)].

(* ================================================================ *)
(* group_sum basics                                                  *)
(* ================================================================ *)

Lemma group_sum_nil : forall tf, group_sum tf [] == 0.
Proof. intros. simpl. reflexivity. Qed.

Lemma group_sum_single : forall v tf,
  group_sum tf [(v, tf)] == v.
Proof.
  intros. simpl. rewrite Nat.eqb_refl. lra.
Qed.

Lemma group_sum_wrong_tf : forall v tf1 tf2,
  tf1 <> tf2 ->
  group_sum tf1 [(v, tf2)] == 0.
Proof.
  intros. simpl.
  destruct (Nat.eqb tf2 tf1) eqn:E.
  - apply Nat.eqb_eq in E. symmetry in E. contradiction.
  - lra.
Qed.

(* ================================================================ *)
(* Destructive interference: opposite signals cancel                *)
(* ================================================================ *)

Lemma destructive_cancel :
  group_sum 1 destructive_1hr == 0.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* Constructive interference: aligned signals reinforce             *)
(* ================================================================ *)

Lemma constructive_reinforce :
  group_sum 1 constructive_1hr == 2.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* Independent timeframes                                            *)
(* ================================================================ *)

Lemma independent_1hr :
  group_sum 1 independent_signals == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma independent_4hr :
  group_sum 4 independent_signals == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma independent_24hr :
  group_sum 24 independent_signals == 1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* Three signals on same timeframe                                   *)
(* ================================================================ *)

Lemma three_signals_1hr :
  group_sum 1 three_1hr == 1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* Mixed timeframe grouping                                          *)
(* ================================================================ *)

Lemma mixed_1hr : group_sum 1 mixed_signals == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma mixed_4hr : group_sum 4 mixed_signals == 3.
Proof. vm_compute. reflexivity. Qed.

Lemma mixed_24hr : group_sum 24 mixed_signals == 1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* Final signal computations                                         *)
(* ================================================================ *)

Lemma final_equal_weights :
  final_signal (1#3) (1#3) (1#3) independent_signals == 1.
Proof.
  unfold final_signal.
  rewrite independent_1hr, independent_4hr, independent_24hr.
  ring.
Qed.

Lemma final_destructive :
  final_signal (1#3) (1#3) (1#3) destructive_1hr == 0.
Proof.
  unfold final_signal.
  rewrite destructive_cancel.
  assert (H4 : group_sum 4 destructive_1hr == 0) by (vm_compute; reflexivity).
  assert (H24 : group_sum 24 destructive_1hr == 0) by (vm_compute; reflexivity).
  rewrite H4, H24. ring.
Qed.

Lemma final_mixed :
  final_signal (1#3) (1#3) (1#3) mixed_signals == 4#3.
Proof.
  unfold final_signal.
  rewrite mixed_1hr, mixed_4hr, mixed_24hr.
  ring.
Qed.

(* ================================================================ *)
(* Weighted final signal: 4hr dominant                               *)
(* ================================================================ *)

Lemma final_4hr_dominant :
  final_signal (1#10) (7#10) (2#10) mixed_signals == (21#10) + (2#10).
Proof.
  unfold final_signal.
  rewrite mixed_1hr, mixed_4hr, mixed_24hr. ring.
Qed.

Lemma final_constructive_weighted :
  final_signal (1#2) (1#4) (1#4) constructive_1hr == 1.
Proof.
  unfold final_signal.
  rewrite constructive_reinforce.
  assert (H4 : group_sum 4 constructive_1hr == 0) by (vm_compute; reflexivity).
  assert (H24 : group_sum 24 constructive_1hr == 0) by (vm_compute; reflexivity).
  rewrite H4, H24. ring.
Qed.

Lemma group_sum_app_nil : forall tf sigs,
  group_sum tf (sigs ++ []) == group_sum tf sigs.
Proof.
  intros. rewrite app_nil_r. reflexivity.
Qed.

(* ================================================================ *)
(* Property: interference is exact Q arithmetic                     *)
(* ================================================================ *)

Lemma interference_is_exact :
  forall sigs tf, exists q : Q, group_sum tf sigs == q.
Proof.
  intros. exists (group_sum tf sigs). reflexivity.
Qed.

(* ================================================================ *)
(* Synthesis: signal interference patterns                          *)
(* ================================================================ *)

Theorem interference_synthesis :
  (* Destructive: opposite signals cancel *)
  group_sum 1 destructive_1hr == 0 /\
  (* Constructive: aligned signals reinforce *)
  group_sum 1 constructive_1hr == 2 /\
  (* Independent timeframes don't cross *)
  group_sum 1 independent_signals == 1 /\
  group_sum 4 independent_signals == 1 /\
  (* Mixed: 1hr cancels, 4hr and 24hr survive *)
  group_sum 1 mixed_signals == 0 /\
  group_sum 4 mixed_signals == 3.
Proof.
  split. { exact destructive_cancel. }
  split. { exact constructive_reinforce. }
  split. { exact independent_1hr. }
  split. { exact independent_4hr. }
  split. { exact mixed_1hr. }
  exact mixed_4hr.
Qed.
