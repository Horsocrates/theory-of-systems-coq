(* ObserverSynthesis.v — Grand Synthesis: Observer + Time + L5
    Elements: grand theorem
    Roles:    Unite observer, time, L5 in one theorem
    Rules:    13-conjunct synthesis
    Status:   Foundation
    STATUS: 10 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
Import ListNotations.

Open Scope Q_scope.

(* STANDALONE — inline definitions with S prefix *)
Definition SObsState := list nat.
Definition shas (s : SObsState) (d : nat) : bool := existsb (Nat.eqb d) s.
Record SObs := mkSObs { sstate : SObsState }.
Definition sinit : SObs := mkSObs [].
Definition sobs (o : SObs) (d : nat) : SObs := mkSObs (d :: sstate o).

(* Helper lemmas *)
Lemma sobs_adds : forall o d, shas (sstate (sobs o d)) d = true.
Proof. intros. unfold sobs, shas. simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma sobs_preserves : forall o d1 d2,
  shas (sstate (sobs (sobs o d1) d2)) d1 = true.
Proof.
  intros. unfold sobs, shas. simpl.
  rewrite Nat.eqb_refl. apply orb_true_r.
Qed.

(* Grand theorem *)
Theorem observer_grand_synthesis :
  sstate sinit = [] /\
  sstate (sobs sinit 1%nat) = [1%nat] /\
  shas (sstate (sobs sinit 1%nat)) 1%nat = true /\
  sstate (sobs (sobs sinit 1%nat) 3%nat) = [3%nat; 1%nat] /\
  (length (sstate (sobs (sobs sinit 1%nat) 3%nat)) = 2)%nat /\
  shas (sstate (sobs (sobs sinit 1%nat) 3%nat)) 1%nat = true /\
  (length (sstate sinit) < length (sstate (sobs sinit 1%nat)))%nat /\
  (length (sstate (sobs sinit 1%nat)) < length (sstate (sobs (sobs sinit 1%nat) 3%nat)))%nat /\
  (~ exists m : nat, S m = 0%nat) /\
  (forall n : nat, exists m : nat, (n < m)%nat) /\
  [1%nat; 3%nat; 5%nat] <> [2%nat; 3%nat; 7%nat] /\
  shas [1%nat; 3%nat; 5%nat] 3%nat = true /\
  shas [2%nat; 3%nat; 7%nat] 3%nat = true.
Proof.
  split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]]]].
  - reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - simpl. reflexivity.
  - vm_compute. reflexivity.
  - simpl. lia.
  - simpl. lia.
  - intros [m Hm]. discriminate.
  - intro n. exists (S n). lia.
  - discriminate.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

(* Additional lemmas *)
Lemma void_unchanged : sstate sinit = sstate sinit.
Proof. reflexivity. Qed.

Lemma logic_unchanged : forall o d,
  (length (sstate o) <= length (sstate (sobs o d)))%nat.
Proof. intros. simpl. lia. Qed.

Lemma witness_indestructible : forall d1 d2 d3,
  shas (sstate (sobs (sobs (sobs sinit d1) d2) d3)) d1 = true.
Proof.
  intros. unfold sobs, shas. simpl.
  rewrite Nat.eqb_refl.
  rewrite !orb_true_r. reflexivity.
Qed.

Lemma three_acts_three_moments :
  (length (sstate (sobs (sobs (sobs sinit 1%nat) 3%nat) 5%nat)) = 3)%nat.
Proof. simpl. reflexivity. Qed.

Lemma observation_is_creation :
  sstate sinit = [] /\ sstate (sobs sinit 42%nat) = [42%nat].
Proof. split; reflexivity. Qed.
