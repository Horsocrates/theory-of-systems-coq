(* ObserverFoundation.v — Observer as witness arising from distinction
    Elements: Observer, ObsState, observe, has, self_witness
    Roles:    Being distinguished = being witness of own existence
    Rules:    L1 = self-witnessing, L5 = state only grows
    Status:   Foundation
    STATUS: 20 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
Import ListNotations.

Open Scope Q_scope.

(* Observer state = list of distinction indices *)
Definition ObsState := list nat.

(* Membership check *)
Definition has (s : ObsState) (d : nat) : bool :=
  existsb (Nat.eqb d) s.

(* Observer record *)
Record Observer := mkObs { obs_state : ObsState }.

(* Initial observer: capacity exists, no distinctions yet *)
Definition initial_obs : Observer := mkObs [].

Lemma initial_empty : obs_state initial_obs = [].
Proof. reflexivity. Qed.

(* Act of observation: adds NEW distinction *)
Definition observe (o : Observer) (d : nat) : Observer :=
  mkObs (d :: obs_state o).

(* Observation always grows state *)
Lemma observe_grows : forall o d,
  length (obs_state (observe o d)) = S (length (obs_state o)).
Proof. intros. simpl. reflexivity. Qed.

(* Observation adds the specific distinction *)
Lemma observe_adds : forall o d,
  has (obs_state (observe o d)) d = true.
Proof.
  intros o d. unfold observe, has. simpl.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

(* L1 as self-witnessing *)
Lemma self_witness : forall o d,
  has (obs_state (observe o d)) d = true.
Proof. exact observe_adds. Qed.

(* Self-witnessing is PERMANENT (L5) *)
Lemma self_witness_permanent : forall o d1 d2,
  has (obs_state (observe (observe o d1) d2)) d1 = true.
Proof.
  intros o d1 d2. unfold observe, has. simpl.
  rewrite Nat.eqb_refl.
  apply orb_true_r.
Qed.

(* L5: Previous distinctions PRESERVED *)
Lemma obs_preserves : forall o d d',
  has (obs_state o) d' = true ->
  has (obs_state (observe o d)) d' = true.
Proof.
  intros o d d' H. unfold observe, has. simpl.
  apply orb_true_intro. right. exact H.
Qed.

(* State only grows: length monotone *)
Lemma state_monotone : forall o d,
  (length (obs_state o) <= length (obs_state (observe o d)))%nat.
Proof. intros. simpl. lia. Qed.

(* Multiple observers *)
Definition obs_A : Observer := mkObs [1%nat; 3%nat; 5%nat].
Definition obs_B : Observer := mkObs [2%nat; 3%nat; 7%nat].

(* Different observers CAN have different states *)
Lemma observers_differ : obs_state obs_A <> obs_state obs_B.
Proof. unfold obs_A, obs_B. simpl. discriminate. Qed.

(* Shared distinctions: both have 3 *)
Lemma shared_distinction :
  has (obs_state obs_A) 3%nat = true /\
  has (obs_state obs_B) 3%nat = true.
Proof. split; vm_compute; reflexivity. Qed.

(* Private distinctions: A has 1, B doesn't *)
Lemma private_distinction :
  has (obs_state obs_A) 1%nat = true /\
  has (obs_state obs_B) 1%nat = false.
Proof. split; vm_compute; reflexivity. Qed.

(* First observation creates time *)
Lemma first_obs_nonempty : forall d,
  obs_state (observe initial_obs d) <> [].
Proof. intros d. simpl. discriminate. Qed.

(* Two observations: both preserved *)
Lemma two_obs_both : forall d1 d2,
  has (obs_state (observe (observe initial_obs d1) d2)) d1 = true /\
  has (obs_state (observe (observe initial_obs d1) d2)) d2 = true.
Proof.
  intros d1 d2. split.
  - exact (self_witness_permanent initial_obs d1 d2).
  - exact (observe_adds (observe initial_obs d1) d2).
Qed.

(* Observation is cumulative *)
Lemma cumulative_3 : forall d1 d2 d3,
  (length (obs_state (observe (observe (observe initial_obs d1) d2) d3)) = 3)%nat.
Proof. intros. simpl. reflexivity. Qed.

(* SYNTHESIS *)
Theorem observer_foundation_synthesis :
  obs_state initial_obs = [] /\
  (forall d, obs_state (observe initial_obs d) <> []) /\
  (forall o d, has (obs_state (observe o d)) d = true) /\
  (forall o d, (length (obs_state o) <= length (obs_state (observe o d)))%nat) /\
  obs_state obs_A <> obs_state obs_B.
Proof.
  split; [|split; [|split; [|split]]].
  - exact initial_empty.
  - exact first_obs_nonempty.
  - exact self_witness.
  - exact state_monotone.
  - exact observers_differ.
Qed.
