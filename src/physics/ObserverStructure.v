(** * ObserverStructure.v — Observer-dependent event ordering from L5
    Elements: Observer, first_appearance, event time
    Roles:    Two observers with different D(K) → different event orderings
    Rules:    L5 (persistence), L4 (grounding), P4 (finiteness)
    STATUS:   10 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: March 2026

    KEY: "Event e happens at time K for observer O" = e ∈ D_O(K) \ D_O(K-1).
    Two observers see events in DIFFERENT orders if their D(K) differ.
    Causal events have ABSOLUTE order. Spacelike events have RELATIVE order.
*)

From Stdlib Require Import List Lia Bool PeanoNat.
Import ListNotations.

Definition Distinction := nat.
Definition Observer := nat -> list Distinction.

(** L5: distinctions persist *)
Definition is_L5_observer (O : Observer) : Prop :=
  forall K d, In d (O K) -> In d (O (S K)).

(** First appearance: earliest stage where d ∈ O(K) *)
Fixpoint first_appearance (O : Observer) (d : Distinction) (K : nat) : option nat :=
  match K with
  | O => if existsb (Nat.eqb d) (O 0) then Some 0 else None
  | S K' =>
    match first_appearance O d K' with
    | Some k => Some k
    | None => if existsb (Nat.eqb d) (O (S K')) then Some (S K') else None
    end
  end.

(* ================================================================== *)
(*  CONCRETE OBSERVERS                                                 *)
(* ================================================================== *)

(** O1 sees 1 first, then 2, then 3 *)
Definition O1 (K : nat) : list Distinction :=
  match K with
  | O => []
  | S O => [1]
  | S (S O) => [1;2]
  | _ => [1;2;3]
  end.

(** O2 sees 2 first, then 1, then 3 *)
Definition O2 (K : nat) : list Distinction :=
  match K with
  | O => []
  | S O => [2]
  | S (S O) => [1;2]
  | _ => [1;2;3]
  end.

(* ================================================================== *)
(*  L5 COMPATIBILITY                                                   *)
(* ================================================================== *)

Lemma O1_is_L5 : is_L5_observer O1.
Proof.
  intros K d Hd.
  destruct K as [|[|[|K']]]; simpl in *; intuition.
Qed.

Lemma O2_is_L5 : is_L5_observer O2.
Proof.
  intros K d Hd.
  destruct K as [|[|[|K']]]; simpl in *; intuition.
Qed.

(* ================================================================== *)
(*  EVENT TIMES                                                        *)
(* ================================================================== *)

(** O1: event 1 at K=1, event 2 at K=2 *)
Lemma O1_sees_1_first : first_appearance O1 1 3 = Some 1.
Proof. simpl. reflexivity. Qed.

Lemma O1_sees_2_second : first_appearance O1 2 3 = Some 2.
Proof. simpl. reflexivity. Qed.

(** O2: event 2 at K=1, event 1 at K=2 *)
Lemma O2_sees_2_first : first_appearance O2 2 3 = Some 1.
Proof. simpl. reflexivity. Qed.

Lemma O2_sees_1_second : first_appearance O2 1 3 = Some 2.
Proof. simpl. reflexivity. Qed.

(* ================================================================== *)
(*  DISAGREEMENT AND AGREEMENT                                         *)
(* ================================================================== *)

(** O1 and O2 DISAGREE on the order of events 1 and 2:
    O1: time(1)=1 < time(2)=2 → event 1 before event 2
    O2: time(2)=1 < time(1)=2 → event 2 before event 1
    = RELATIVITY OF SIMULTANEITY *)
Theorem O1_O2_disagree_on_order :
  first_appearance O1 1 3 = Some 1 /\
  first_appearance O1 2 3 = Some 2 /\
  first_appearance O2 2 3 = Some 1 /\
  first_appearance O2 1 3 = Some 2.
Proof. repeat split; simpl; reflexivity. Qed.

(** O1 and O2 AGREE that event 3 comes after both 1 and 2 *)
Theorem O1_O2_agree_on_3 :
  first_appearance O1 3 3 = Some 3 /\
  first_appearance O2 3 3 = Some 3.
Proof. split; simpl; reflexivity. Qed.

(** First appearance is stable under L5: once found, stays found *)
Lemma first_appearance_stable : forall O d K k,
  first_appearance O d K = Some k ->
  first_appearance O d (S K) = Some k.
Proof.
  intros O0 d K k H. simpl. rewrite H. reflexivity.
Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

Theorem observer_structure_synthesis :
  is_L5_observer O1 /\
  is_L5_observer O2 /\
  first_appearance O1 1 3 = Some 1 /\
  first_appearance O2 1 3 = Some 2 /\
  first_appearance O1 3 3 = Some 3 /\
  first_appearance O2 3 3 = Some 3.
Proof.
  split; [exact O1_is_L5 |
  split; [exact O2_is_L5 |
  split; [exact O1_sees_1_first |
  split; [exact O2_sees_1_second |
  split; [exact (proj1 O1_O2_agree_on_3) |
  exact (proj2 O1_O2_agree_on_3)]]]]].
Qed.
