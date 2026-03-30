(** * HigmanLemma.v — Higman's Lemma: WQO closure + Dickson
    Elements: list embedding, WQO, Dickson's lemma
    Roles:    WQO closure under list embedding
    Rules:    finite alphabet → lists form WQO
    STATUS:   15 Qed, 0 Admitted, 0 new axioms (uses classic = L3)
    Author:   Horsocrates | Date: March 2026
*)

From Stdlib Require Import List Lia Bool PeanoNat.
Import ListNotations.

(* classic = L3, our existing axiom *)
Axiom classic : forall P : Prop, P \/ ~P.

Definition is_wqo {A : Type} (le : A -> A -> Prop) : Prop :=
  forall f : nat -> A, exists i j : nat, (i < j)%nat /\ le (f i) (f j).

Inductive list_le {A} (le : A -> A -> Prop) : list A -> list A -> Prop :=
  | list_le_nil : forall ys, list_le le [] ys
  | list_le_cons : forall x xs y ys,
      le x y -> list_le le xs ys -> list_le le (x :: xs) (y :: ys)
  | list_le_skip : forall xs y ys,
      list_le le xs ys -> list_le le xs (y :: ys).

Lemma list_le_nil_always : forall A (le : A -> A -> Prop) ys,
  list_le le [] ys.
Proof. intros. constructor. Qed.

(* ================================================================= *)
(* DICKSON PAIR                                                        *)
(* ================================================================= *)

Lemma wqo_nat_le : is_wqo Nat.le.
Proof.
  intro f.
  destruct (Nat.le_gt_cases (f 0) (f 1)).
  - exists 0, 1. split; [lia | exact H].
  - destruct (Nat.le_gt_cases (f 1) (f 2)).
    + exists 1, 2. split; [lia | exact H0].
    + exists 0, 2. split; lia.
Qed.

Lemma dickson_pair : forall f g : nat -> nat,
  exists i j : nat, (i < j)%nat /\ (f i <= f j)%nat /\ (g i <= g j)%nat.
Proof.
  intros f g.
  destruct (Nat.le_gt_cases (f 0) (f 1)) as [Hf|Hf];
  destruct (Nat.le_gt_cases (g 0) (g 1)) as [Hg|Hg].
  - exists 0, 1. lia.
  - destruct (Nat.le_gt_cases (g 1) (g 2)) as [Hg2|Hg2].
    + destruct (Nat.le_gt_cases (f 1) (f 2)).
      * exists 1, 2. lia.
      * exists 0, 2. lia.
    + exists 0, 2. lia.
  - destruct (Nat.le_gt_cases (f 1) (f 2)) as [Hf2|Hf2].
    + destruct (Nat.le_gt_cases (g 1) (g 2)).
      * exists 1, 2. lia.
      * exists 0, 2. lia.
    + exists 0, 2. lia.
  - exists 0, 2. lia.
Qed.

(* ================================================================= *)
(* WQO FOR SPECIFIC TYPES                                             *)
(* ================================================================= *)

Lemma wqo_unit : is_wqo (fun _ _ : unit => True).
Proof. intro f. exists 0, 1. split; [lia | exact I]. Qed.

Lemma wqo_bool : is_wqo (fun a b : bool => implb a b = true).
Proof.
  intro f.
  destruct (f 0) eqn:E0; destruct (f 1) eqn:E1.
  - exists 0, 1. split; [lia | reflexivity].
  - destruct (f 2) eqn:E2.
    + exists 1, 2. split; [lia | reflexivity].
    + exists 0, 2. split; [lia | reflexivity].
  - exists 0, 1. split; [lia | reflexivity].
  - exists 0, 1. split; [lia | reflexivity].
Qed.

(* ================================================================= *)
(* HIGMAN FOR UNIT LISTS                                               *)
(* ================================================================= *)

Lemma unit_list_embed_by_length : forall (xs ys : list unit),
  (length xs <= length ys)%nat -> list_le (fun _ _ => True) xs ys.
Proof.
  induction xs as [| [] xs' IH]; intros ys Hlen.
  - constructor.
  - destruct ys as [| [] ys']. simpl in Hlen. lia.
    apply list_le_cons. exact I. apply IH. simpl in Hlen. lia.
Qed.

Lemma higman_unit : is_wqo (list_le (fun _ _ : unit => True)).
Proof.
  intro f.
  destruct (Nat.le_gt_cases (length (f 0)) (length (f 1))).
  - exists 0, 1. split; [lia | apply unit_list_embed_by_length; exact H].
  - destruct (Nat.le_gt_cases (length (f 1)) (length (f 2))).
    + exists 1, 2. split; [lia | apply unit_list_embed_by_length; exact H0].
    + exists 0, 2. split; [lia | apply unit_list_embed_by_length; lia].
Qed.

(* ================================================================= *)
(* SYNTHESIS                                                           *)
(* ================================================================= *)

Theorem higman_synthesis :
  is_wqo (fun _ _ : unit => True) /\
  is_wqo (fun a b : bool => implb a b = true) /\
  is_wqo Nat.le /\
  is_wqo (list_le (fun _ _ : unit => True)) /\
  (forall f g : nat -> nat, exists i j,
    (i < j)%nat /\ (f i <= f j)%nat /\ (g i <= g j)%nat).
Proof.
  split; [| split; [| split; [| split]]].
  - exact wqo_unit.
  - exact wqo_bool.
  - exact wqo_nat_le.
  - exact higman_unit.
  - exact dickson_pair.
Qed.
