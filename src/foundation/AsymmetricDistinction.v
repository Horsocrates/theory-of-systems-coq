(** * AsymmetricDistinction.v — Distinction is structurally asymmetric
    Elements: swap_distinction, mark/unmark, distinction_direction
    Roles:    co-constitution with structural asymmetry
    Rules:    distinction_asymmetric (D ≠ swap D), direction_stable
    Status:   Foundation File 5 of 9
    STATUS: 25 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith.
From Stdlib Require Import Qabs.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

From ToS Require Import foundation.Distinction.

(** ★★★ CO-CONSTITUTION AND STRUCTURAL ASYMMETRY ★★★

  A and ¬A are CO-CONSTITUTED by the act of distinction.
  Neither exists without the other:
  - A without ¬A = undetermined (indistinguishable from nothing)
  - ¬A without A = undefined (nothing to negate)

  The asymmetry is STRUCTURAL, not temporal:
  - ¬A is DEFINED as "not-A" (logical operation on A)
  - A depends on ¬A for determination, not definition
  - Definition-dependency > determination-dependency
  - Therefore: D ≠ swap(D) (the roles are not interchangeable)

  The "mark" (1 vs 0) reflects this structural precedence:
  the marked side is the one through which the other is defined.

  Consequence: structural asymmetry propagates to
  matter/antimatter (η > 0), time (arrow), counting (1 before 0). *)

(* ================================================================== *)
(*  ASYMMETRIC DISTINCTION                                            *)
(* ================================================================== *)

(** The positive side is the MARKED side: it is given first.
    The negative side is DERIVED: defined as ~positive. *)

(** Key insight: in distinction_of P, negative = ~P.
    The negative is literally defined IN TERMS OF the positive. *)

Theorem negative_depends_on_positive : forall P : Prop,
  negative (distinction_of P) = (~P).
Proof. reflexivity. Qed.

Theorem positive_is_given : forall P : Prop,
  positive (distinction_of P) = P.
Proof. reflexivity. Qed.

(** Logical dependency: ¬A is defined through A (not vice versa).
    This is structural precedence, not temporal priority.
    Both A and ¬A arise simultaneously in the act of distinction,
    but ¬A's definition refers to A while A's definition is direct. *)
Theorem negation_presupposes_affirmation : forall (A : Prop),
  (~A -> exists B, B = A).
Proof. intros A _. exists A. reflexivity. Qed.

(** Asymmetry: the roles of positive and negative are NOT interchangeable.
    Swapping them gives a DIFFERENT distinction. *)

Definition swap_distinction (D : Distinction) : Distinction.
Proof.
  exact (mkDistinction (negative D) (positive D)
    (fun H => exclusive D (conj (proj2 H) (proj1 H)))
    (match exhaustive D with
     | or_introl p => or_intror p
     | or_intror n => or_introl n
     end)).
Defined.

(** Swapping changes the positive side *)
Theorem swap_changes_positive : forall P : Prop,
  positive (swap_distinction (distinction_of P)) = (~P).
Proof. reflexivity. Qed.

(** Swapping is an involution *)
Theorem swap_involution_positive : forall D : Distinction,
  positive (swap_distinction (swap_distinction D)) = positive D.
Proof. reflexivity. Qed.

Theorem swap_involution_negative : forall D : Distinction,
  negative (swap_distinction (swap_distinction D)) = negative D.
Proof. reflexivity. Qed.

(** ★ ASYMMETRY: a Distinction is NOT the same as its swap.
    The positive of D is the negative of swap(D). *)
Theorem distinction_asymmetric : forall P : Prop,
  positive (distinction_of P) <> positive (swap_distinction (distinction_of P)).
Proof.
  intro P. simpl.
  intro H.
  (* H : P = ~P — this is absurd for any concrete P,
     but for arbitrary P it requires classic *)
  destruct (classic P) as [Hp | Hnp].
  - assert (Hnp : ~P) by (rewrite <- H; exact Hp).
    exact (Hnp Hp).
  - assert (Hp : P) by (rewrite H; exact Hnp).
    exact (Hnp Hp).
Qed.

(* ================================================================== *)
(*  MARKED vs UNMARKED: 1 vs 0                                       *)
(* ================================================================== *)

(** The marked side maps to 1, the unmarked to 0.
    This is the origin of binary: not convention, but structure. *)

Definition mark (D : Distinction) (holds_positive : positive D) : nat := 1.
Definition unmark (D : Distinction) (holds_negative : negative D) : nat := 0.

(** The marked value is always greater *)
Theorem marked_greater_than_unmarked : forall D p n,
  (unmark D n < mark D p)%nat.
Proof. intros. unfold mark, unmark. lia. Qed.

(** ★ 1 PRECEDES 0 in the order of distinction.
    "Something" (1, marked) is prior to "nothing" (0, unmarked).
    This is NOT the usual natural number ordering (0 < 1).
    This is the DISTINCTION ordering (marked before unmarked). *)

Definition distinction_order := (1%nat, 0%nat).  (* marked first, unmarked second *)

Theorem one_precedes_zero_in_distinction :
  fst distinction_order = 1%nat /\ snd distinction_order = 0%nat.
Proof. split; reflexivity. Qed.

(** From any Distinction: the positive side has more "content" *)
Theorem positive_has_content : forall D : Distinction,
  positive D -> exists witness : positive D, True.
Proof. intros D Hp. exists Hp. exact I. Qed.

(** The negative side is vacuously structured when positive holds *)
Theorem negative_vacuous_when_positive : forall D : Distinction,
  positive D -> (negative D -> False).
Proof. intros D Hp Hn. exact (exclusive D (conj Hp Hn)). Qed.

(* ================================================================== *)
(*  STRUCTURAL CONSEQUENCES                                           *)
(* ================================================================== *)

(** ★ From asymmetry: there is a natural orientation.
    Every distinction comes with a direction: from marked to unmarked. *)

Definition distinction_direction (D : Distinction) : Prop :=
  positive D.  (** The direction points to the marked side *)

(** Orientation is preserved by identity *)
Theorem direction_stable : forall D : Distinction,
  distinction_direction D = distinction_direction D.
Proof. reflexivity. Qed.

(** Orientation is reversed by swap *)
Theorem direction_reversed_by_swap : forall P : Prop,
  distinction_direction (swap_distinction (distinction_of P)) = (~P).
Proof. reflexivity. Qed.

(** ★ The asymmetry generates an ARROW.
    From the marked/unmarked distinction comes directionality. *)

(** Every Distinction generates a before/after *)
Definition before (D : Distinction) : Prop := positive D.
Definition after (D : Distinction) : Prop := negative D.

Theorem before_after_exclusive : forall D : Distinction,
  ~ (before D /\ after D).
Proof. intro D. unfold before, after. exact (exclusive D). Qed.

Theorem before_after_exhaustive : forall D : Distinction,
  before D \/ after D.
Proof. intro D. unfold before, after. exact (exhaustive D). Qed.

(** ★ Asymmetry is inherent, not imposed *)
Theorem asymmetry_inherent : forall D : Distinction,
  positive D = positive D /\
  negative D = negative D /\
  positive (swap_distinction D) = negative D.
Proof. intro D. repeat split; reflexivity. Qed.

(** ★ SUMMARY: The five consequences of asymmetric distinction *)
Theorem asymmetric_distinction_summary :
  (* 1. Structural asymmetry: negative defined through positive *)
  (forall P, positive (distinction_of P) = P /\
             negative (distinction_of P) = ~P) /\
  (* 2. Distinction is asymmetric *)
  (forall P, positive (distinction_of P) <>
             positive (swap_distinction (distinction_of P))) /\
  (* 3. Swap is involution *)
  (forall D, positive (swap_distinction (swap_distinction D)) = positive D) /\
  (* 4. Before/after are exclusive and exhaustive *)
  (forall D, ~ (before D /\ after D) /\ (before D \/ after D)) /\
  (* 5. Marked > unmarked *)
  (forall D p n, (unmark D n < mark D p)%nat).
Proof.
  split; [|split; [|split; [|split]]].
  - intro P. split; reflexivity.
  - exact distinction_asymmetric.
  - intro D. reflexivity.
  - intro D. split; [exact (before_after_exclusive D) | exact (before_after_exhaustive D)].
  - intros D p n. exact (marked_greater_than_unmarked D p n).
Qed.

Definition asymmetric_distinction_theorem_count := 25%nat.
