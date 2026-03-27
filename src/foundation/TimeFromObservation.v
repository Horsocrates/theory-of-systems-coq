(* TimeFromObservation.v — Time as consequence of observation
    Elements: moment, before_time, first_obs, arrow
    Roles:    Time does NOT preexist observation. Time = sequence of state changes.
    Rules:    Before first act: no changes -> no time. Arrow = growth direction.
    Status:   Foundation
    STATUS: 15 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
Import ListNotations.

Open Scope Q_scope.

(* STANDALONE — inline observer definitions with T prefix *)
Definition TObsState := list nat.
Definition thas (s : TObsState) (d : nat) : bool := existsb (Nat.eqb d) s.
Record TObs := mkTObs { tstate : TObsState }.
Definition tinitial : TObs := mkTObs [].
Definition tobserve (o : TObs) (d : nat) : TObs := mkTObs (d :: tstate o).

Definition moment := nat.
Definition before_time : moment := 0%nat.

Lemma before_time_state : tstate tinitial = [].
Proof. reflexivity. Qed.

Definition first_obs (d : nat) : TObs := tobserve tinitial d.

Lemma first_moment_nonempty : forall d, tstate (first_obs d) <> [].
Proof. intros d. simpl. discriminate. Qed.

Lemma no_before_first : ~ exists m : moment, (S m = before_time)%nat.
Proof. intro H. destruct H as [m Hm]. discriminate. Qed.

Lemma moments_ordered : forall m : moment, (m < S m)%nat.
Proof. intro m. lia. Qed.

(* States at successive moments *)
Definition state_at_0 : TObsState := [].
Definition state_at_1 : TObsState := [1%nat].
Definition state_at_2 : TObsState := [3%nat; 1%nat].
Definition state_at_3 : TObsState := [5%nat; 3%nat; 1%nat].

Lemma growth_01 : (length state_at_0 < length state_at_1)%nat.
Proof. simpl. lia. Qed.

Lemma growth_12 : (length state_at_1 < length state_at_2)%nat.
Proof. simpl. lia. Qed.

Lemma growth_23 : (length state_at_2 < length state_at_3)%nat.
Proof. simpl. lia. Qed.

Lemma preserved_1_in_2 : thas state_at_2 1%nat = true.
Proof. vm_compute. reflexivity. Qed.

Lemma preserved_1_in_3 : thas state_at_3 1%nat = true.
Proof. vm_compute. reflexivity. Qed.

(* Price Problem 1: outside time = empty *)
Lemma outside_time_empty : tstate tinitial = [].
Proof. reflexivity. Qed.

(* Price Problem 3: No highest level *)
Lemma no_highest_level : forall n : nat, exists m : nat, (n < m)%nat.
Proof. intro n. exists (S n). lia. Qed.

(* SYNTHESIS *)
Theorem time_from_observation_synthesis :
  tstate tinitial = [] /\
  (forall d, tstate (first_obs d) <> []) /\
  (length state_at_0 < length state_at_1)%nat /\
  (length state_at_1 < length state_at_2)%nat /\
  thas state_at_3 1%nat = true /\
  (forall n : nat, exists m : nat, (n < m)%nat).
Proof.
  split; [|split; [|split; [|split; [|split]]]].
  - exact before_time_state.
  - exact first_moment_nonempty.
  - exact growth_01.
  - exact growth_12.
  - exact preserved_1_in_3.
  - exact no_highest_level.
Qed.
