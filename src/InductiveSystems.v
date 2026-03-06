(* ========================================================================= *)
(*              INDUCTIVE SYSTEMS: CONSTRUCTOR-DEFINED SYSTEMS              *)
(*                                                                          *)
(*  Part of: Theory of Systems -- Coq Formalization                        *)
(*  Formalizes systems defined by constructors (nat, list, tree).           *)
(*  P4: every element is reachable in finite steps.                        *)
(*  Depends on: TheoryOfSystems_Core_ERR.v                                 *)
(*  STATUS: 26 Qed, 0 Admitted                                             *)
(*  Author: Horsocrates | Date: March 2026                                  *)
(* ========================================================================= *)

From Stdlib Require Import Init.Nat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import micromega.Lia.
Import ListNotations.

From ToS Require Import TheoryOfSystems_Core_ERR.

(* ========================================================================= *)
(*                   PART I: FINITELY GENERATED SYSTEMS (P4)                *)
(* ========================================================================= *)

(** A system is finitely generated when every element has a finite depth,
    i.e., reachable from base constructors in finitely many steps.
    This is P4 of the Theory of Systems. *)

Record FinitelyGenerated (A : Type) := mkFinitelyGenerated {
  fg_depth : A -> nat;
}.

(* ========================================================================= *)
(*               PART II: NAT AS FINITELY GENERATED                        *)
(* ========================================================================= *)

(** Constructors: O (base), S (step). Depth: depth(n) = n. *)

Definition nat_depth (n : nat) : nat := n.

Definition nat_fg : FinitelyGenerated nat :=
  mkFinitelyGenerated nat nat_depth.

(** Lemma 1: nat satisfies FinitelyGenerated *)
Lemma nat_finitely_generated :
  exists (fg : FinitelyGenerated nat), fg_depth nat fg = nat_depth.
Proof. exists nat_fg. reflexivity. Qed.

(** Lemma 2: depth of n equals n *)
Lemma nat_depth_eq_id : forall n, nat_depth n = n.
Proof. intros n. reflexivity. Qed.

(** Lemma 3: depth of 0 is 0 *)
Lemma nat_zero_depth_zero : nat_depth 0 = 0.
Proof. reflexivity. Qed.

(** Lemma 4: depth of S n is S (depth n) *)
Lemma nat_succ_depth : forall n, nat_depth (S n) = S (nat_depth n).
Proof. intros n. reflexivity. Qed.

(** Lemma 5: nat has no infinite depth *)
Lemma nat_no_infinite_depth :
  forall n, exists k, nat_depth n = k.
Proof. intros n. exists n. reflexivity. Qed.

(** Lemma 6: nat induction reaches all elements (Constitution = induction) *)
Lemma nat_induction_complete :
  forall (P : nat -> Prop),
    P 0 -> (forall n, P n -> P (S n)) -> forall n, P n.
Proof.
  intros P H0 HS n. induction n as [| n' IH].
  - exact H0.
  - exact (HS n' IH).
Qed.

(** Lemma 7: O and S n are disjoint constructors *)
Lemma nat_constructors_disjoint : forall n, O <> S n.
Proof. intros n. discriminate. Qed.

(* ========================================================================= *)
(*               PART III: LIST AS FINITELY GENERATED                      *)
(* ========================================================================= *)

(** Constructors: nil (base), cons (step). Depth: depth(l) = length(l). *)

Definition list_depth (A : Type) (l : list A) : nat := length l.

Definition list_fg (A : Type) : FinitelyGenerated (list A) :=
  mkFinitelyGenerated (list A) (list_depth A).

(** Lemma 8: list satisfies FinitelyGenerated *)
Lemma list_finitely_generated :
  forall A, exists (fg : FinitelyGenerated (list A)),
    fg_depth (list A) fg = list_depth A.
Proof. intros A. exists (list_fg A). reflexivity. Qed.

(** Lemma 9: depth of list equals length *)
Lemma list_depth_eq_length :
  forall (A : Type) (l : list A), list_depth A l = length l.
Proof. intros A l. reflexivity. Qed.

(** Lemma 10: depth of nil is 0 *)
Lemma list_nil_depth_zero :
  forall (A : Type), list_depth A nil = 0.
Proof. intros A. reflexivity. Qed.

(** Lemma 11: depth of cons a l is S (depth l) *)
Lemma list_cons_depth :
  forall (A : Type) (a : A) (l : list A),
    list_depth A (a :: l) = S (list_depth A l).
Proof. intros A a l. reflexivity. Qed.

(** Lemma 12: list induction reaches all elements *)
Lemma list_induction_complete :
  forall (A : Type) (P : list A -> Prop),
    P nil -> (forall a l, P l -> P (a :: l)) -> forall l, P l.
Proof.
  intros A P Hnil Hcons l. induction l as [| a l' IH].
  - exact Hnil.
  - exact (Hcons a l' IH).
Qed.

(** Lemma 13: nil and cons are disjoint constructors *)
Lemma list_constructors_disjoint :
  forall (A : Type) (a : A) (l : list A), nil <> a :: l.
Proof. intros A a l. discriminate. Qed.

(* ========================================================================= *)
(*               PART IV: BINARY TREE AS FINITELY GENERATED               *)
(* ========================================================================= *)

(** Constructors: BLeaf (base), BNode (step with two subtrees).
    Depth = tree height: depth(BLeaf a) = 0,
    depth(BNode l r) = 1 + max(depth l, depth r). *)

Inductive BTree (A : Type) : Type :=
  | BLeaf : A -> BTree A
  | BNode : BTree A -> BTree A -> BTree A.

Arguments BLeaf {A}.
Arguments BNode {A}.

Fixpoint btree_depth {A : Type} (t : BTree A) : nat :=
  match t with
  | BLeaf _ => 0
  | BNode l r => S (Nat.max (btree_depth l) (btree_depth r))
  end.

Definition btree_fg (A : Type) : FinitelyGenerated (BTree A) :=
  mkFinitelyGenerated (BTree A) (@btree_depth A).

(** Lemma 14: BTree satisfies FinitelyGenerated *)
Lemma btree_finitely_generated :
  forall A, exists (fg : FinitelyGenerated (BTree A)),
    fg_depth (BTree A) fg = @btree_depth A.
Proof. intros A. exists (btree_fg A). reflexivity. Qed.

(** Lemma 15: depth of BLeaf is 0 *)
Lemma btree_leaf_depth :
  forall (A : Type) (a : A), btree_depth (BLeaf a) = 0.
Proof. intros A a. reflexivity. Qed.

(** Lemma 16: depth of BNode is 1 + max(depth l, depth r) *)
Lemma btree_node_depth :
  forall (A : Type) (l r : BTree A),
    btree_depth (BNode l r) = S (Nat.max (btree_depth l) (btree_depth r)).
Proof. intros A l r. reflexivity. Qed.

(** Lemma 17: BTree induction reaches all elements *)
Lemma btree_induction_complete :
  forall (A : Type) (P : BTree A -> Prop),
    (forall a, P (BLeaf a)) ->
    (forall l r, P l -> P r -> P (BNode l r)) ->
    forall t, P t.
Proof.
  intros A P Hleaf Hnode t. induction t as [a | l IHl r IHr].
  - exact (Hleaf a).
  - exact (Hnode l r IHl IHr).
Qed.

(* ========================================================================= *)
(*       PART V: CONSTRUCTORS AS ELEMENTS (Connection to E/R/R)            *)
(* ========================================================================= *)

(** In ToS, every constructor of an inductive type is an Element (L1).
    The constructor PRODUCES inhabitants -- it is the mechanism by which
    elements come into existence. *)

(** Lemma 18: base constructors produce elements *)
Lemma base_case_is_element_nat : exists (n : nat), n = 0.
Proof. exists 0. reflexivity. Qed.

(** Lemma 19: step constructors produce elements *)
Lemma step_case_is_element_nat :
  forall n : nat, exists (m : nat), m = S n.
Proof. intros n. exists (S n). reflexivity. Qed.

(** Lemma 20: every element is produced by some constructor
    (exhaustiveness -- constructors cover the entire system) *)
Lemma constructors_are_elements_nat :
  forall n : nat, n = 0 \/ exists m, n = S m.
Proof.
  intros n. destruct n.
  - left. reflexivity.
  - right. exists n. reflexivity.
Qed.

(* ========================================================================= *)
(*            PART VI: DEPTH MONOTONICITY AND WELL-FOUNDEDNESS             *)
(* ========================================================================= *)

(** Subterms have strictly smaller depth. This ensures termination of
    recursive functions and is the computational content of P4:
    there is no infinite descending chain of constructors. *)

(** Lemma 21: nat predecessor has smaller depth *)
Lemma nat_depth_pred_lt :
  forall n, nat_depth n < nat_depth (S n).
Proof. intros n. unfold nat_depth. lia. Qed.

(** Lemma 22: list tail has smaller depth *)
Lemma list_depth_tail_lt :
  forall (A : Type) (a : A) (l : list A),
    list_depth A l < list_depth A (a :: l).
Proof. intros A a l. unfold list_depth. simpl. lia. Qed.

(** Lemma 23: BTree left subtree has smaller depth *)
Lemma btree_depth_left_lt :
  forall (A : Type) (l r : BTree A),
    btree_depth l < btree_depth (BNode l r).
Proof. intros A l r. simpl. lia. Qed.

(** Lemma 24: BTree right subtree has smaller depth *)
Lemma btree_depth_right_lt :
  forall (A : Type) (l r : BTree A),
    btree_depth r < btree_depth (BNode l r).
Proof. intros A l r. simpl. lia. Qed.

(** Lemma 25: depth 0 implies base constructor (nat) *)
Lemma nat_depth_zero_is_base :
  forall n, nat_depth n = 0 -> n = 0.
Proof. intros n H. unfold nat_depth in H. lia. Qed.

(** Lemma 26: depth 0 implies leaf (BTree) *)
Lemma btree_depth_zero_is_leaf :
  forall (A : Type) (t : BTree A),
    btree_depth t = 0 -> exists a, t = BLeaf a.
Proof.
  intros A t H. destruct t as [a | l r].
  - exists a. reflexivity.
  - simpl in H. lia.
Qed.

(** SUMMARY: 26 Qed, 0 Admitted.
    Nat(7) + List(6) + BTree(4) + E/R/R(3) + Monotonicity(6) = 26.
    P4 = every element has finite depth.
    Constructors = Elements (L1), Induction = Constitution.
    AXIOMS: classic (inherited via Core_ERR). *)
