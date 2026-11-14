(** * DistinctionSideRole.v — The side of a distinction as a ROLE:
      marked 1, unmarked 0, and which of the two roles holds

    E/R/R reading (done before coding; audit of Part II of the Mathematics
    volume, chapter II.1, the block proposed on the page and its footnote 3,
    2026-11-13):

    Elements: a distinction D; its two sides.
    Roles:    Marked and Unmarked — the two values of the type of sides
              (Side, Binarity.v); here read as the roles of the sides of D.
    Rules:    the marked role carries 1, the unmarked role carries 0; of the
              two roles of a distinction exactly one holds.
    Proved:   (1) the role-level statement of the chapter: the value of the
                  unmarked role is less than the value of the marked role —
                  two ROLES are compared, not two proofs;
              (2) the proof-level functions mark / unmark of
                  AsymmetricDistinction.v return exactly these role values,
                  and their premises (a proof of each side of one
                  distinction) are never available together;
              (3) of the two roles of any distinction exactly one holds —
                  existence from the rule `exhaustive`, uniqueness from the
                  rule `exclusive`; this ties the type of sides to the
                  record Distinction;
              (4) swapping the sides exchanges the roles;
              (5) the pair distinction_order is the pair of the two role
                  values.
    P4 diagnostic ("could it be otherwise?"): a two-element type and the
              two rules of the record. Forced: (1)-(5). NOT claimed: that
              the assignment "marked -> 1, unmarked -> 0" is derived — it is
              the definition side_value, a registration of the reading;
              that the order of grounding is a theorem.

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import PeanoNat Lia.

From ToS Require Import foundation.Distinction.
From ToS Require Import foundation.Binarity.
From ToS Require Import foundation.AsymmetricDistinction.

Local Open Scope nat_scope.

(* ========================================================================= *)
(*  1. The role-level statement                                              *)
(* ========================================================================= *)

(** The side of a distinction as a role. The type of sides already exists in
    the repository: Side := Marked | Unmarked (Binarity.v). *)
Definition DistinctionSide : Set := Side.

Definition side_value (s : DistinctionSide) : nat :=
  match s with Marked => 1 | Unmarked => 0 end.

Theorem marked_role_gt_unmarked_role :
  side_value Unmarked < side_value Marked.
Proof. simpl. lia. Qed.

(* ========================================================================= *)
(*  2. The proof-level functions return the role values                      *)
(* ========================================================================= *)

Theorem mark_is_marked_value : forall (D : Distinction) (p : positive D),
  mark D p = side_value Marked.
Proof. reflexivity. Qed.

Theorem unmark_is_unmarked_value : forall (D : Distinction) (n : negative D),
  unmark D n = side_value Unmarked.
Proof. reflexivity. Qed.

(** The premises of marked_greater_than_unmarked — a proof of each side of
    one distinction — are never available together. *)
Theorem mark_unmark_premises_incompatible :
  forall D : Distinction, positive D -> negative D -> False.
Proof. intros D p n. exact (exclusive D (conj p n)). Qed.

(* ========================================================================= *)
(*  3. Exactly one of the two roles holds                                    *)
(* ========================================================================= *)

(** The role s holds in the distinction D. *)
Definition side_holds (D : Distinction) (s : DistinctionSide) : Prop :=
  match s with Marked => positive D | Unmarked => negative D end.

Theorem exactly_one_side_holds : forall D : Distinction,
  exists s : DistinctionSide,
    side_holds D s /\ (forall s', side_holds D s' -> s' = s).
Proof.
  intro D. destruct (exhaustive D) as [p | n].
  - exists Marked. split; [exact p | ].
    intros s' H. destruct s'; [reflexivity | ].
    exfalso. exact (exclusive D (conj p H)).
  - exists Unmarked. split; [exact n | ].
    intros s' H. destruct s'; [ | reflexivity].
    exfalso. exact (exclusive D (conj H n)).
Qed.

(* ========================================================================= *)
(*  4. Swapping the sides exchanges the roles                                *)
(* ========================================================================= *)

Definition other_side (s : DistinctionSide) : DistinctionSide :=
  match s with Marked => Unmarked | Unmarked => Marked end.

Theorem swap_exchanges_roles : forall (D : Distinction) (s : DistinctionSide),
  side_holds (swap_distinction D) s <-> side_holds D (other_side s).
Proof. intros D s. destruct s; simpl; tauto. Qed.

Theorem other_side_involutive : forall s : DistinctionSide,
  other_side (other_side s) = s.
Proof. intro s. destruct s; reflexivity. Qed.

(* ========================================================================= *)
(*  5. The pair of the order of distinction is the pair of the role values   *)
(* ========================================================================= *)

Theorem distinction_order_from_roles :
  distinction_order = (side_value Marked, side_value Unmarked).
Proof. reflexivity. Qed.
