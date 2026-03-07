(* TTree: Binary Search Tree as ToS System *)
(* STATUS: 22 Qed, 0 Admitted, 0 axioms *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import L5Resolution.
From ToS Require Import InductiveSystems.

Section BST.
Context {A : Type} `{DTO : DecTotalOrder A}.

Inductive TTree : Type :=
  | TLeaf : TTree
  | TNode : TTree -> A -> TTree -> TTree.

Fixpoint tree_all (p : A -> Prop) (t : TTree) : Prop :=
  match t with
  | TLeaf => True
  | TNode l v r => p v /\ tree_all p l /\ tree_all p r
  end.

Fixpoint is_bst (t : TTree) : Prop :=
  match t with
  | TLeaf => True
  | TNode l v r =>
    tree_all (fun x => dto_le x v) l /\
    tree_all (fun x => dto_le v x) r /\
    is_bst l /\ is_bst r
  end.

Definition tree_empty : TTree := TLeaf.

Fixpoint tree_member (x : A) (t : TTree) : bool :=
  match t with
  | TLeaf => false
  | TNode l v r =>
    match dto_le_dec x v, dto_le_dec v x with
    | left _, left _ => true
    | left _, right _ => tree_member x l
    | right _, _ => tree_member x r
    end
  end.

Fixpoint tree_insert (x : A) (t : TTree) : TTree :=
  match t with
  | TLeaf => TNode TLeaf x TLeaf
  | TNode l v r =>
    match dto_le_dec x v, dto_le_dec v x with
    | left _, left _ => TNode l v r
    | left _, right _ => TNode (tree_insert x l) v r
    | right _, _ => TNode l v (tree_insert x r)
    end
  end.

Fixpoint tree_height (t : TTree) : nat :=
  match t with
  | TLeaf => 0
  | TNode l _ r => S (Nat.max (tree_height l) (tree_height r))
  end.

Fixpoint tree_size (t : TTree) : nat :=
  match t with
  | TLeaf => 0
  | TNode l _ r => S (tree_size l + tree_size r)
  end.

Fixpoint tree_inorder (t : TTree) : list A :=
  match t with
  | TLeaf => []
  | TNode l v r => tree_inorder l ++ [v] ++ tree_inorder r
  end.

Fixpoint tree_elements (t : TTree) : list A :=
  match t with
  | TLeaf => []
  | TNode l v r => v :: tree_elements l ++ tree_elements r
  end.

Lemma tree_empty_valid : is_bst tree_empty.
Proof. simpl. exact I. Qed.

Lemma tree_member_empty : forall x, tree_member x tree_empty = false.
Proof. intros x. simpl. reflexivity. Qed.

Lemma tree_size_empty : tree_size tree_empty = 0.
Proof. simpl. reflexivity. Qed.

Lemma tree_height_empty : tree_height tree_empty = 0.
Proof. simpl. reflexivity. Qed.

Lemma tree_inorder_empty : tree_inorder tree_empty = [].
Proof. simpl. reflexivity. Qed.

Lemma tree_size_nonneg : forall t, 0 <= tree_size t.
Proof. intros t. lia. Qed.

Lemma tree_height_le_size : forall t : TTree, tree_height t <= tree_size t.
Proof.
  induction t as [| l IHl v r IHr].
  - simpl. lia.
  - simpl. lia.
Qed.

Lemma tree_inorder_length : forall t : TTree,
  length (tree_inorder t) = tree_size t.
Proof.
  induction t as [| l IHl v r IHr].
  - simpl. reflexivity.
  - simpl. rewrite !length_app. simpl.
    rewrite IHl. rewrite IHr. lia.
Qed.

Lemma tree_elements_length : forall t : TTree,
  length (tree_elements t) = tree_size t.
Proof.
  induction t as [| l IHl v r IHr].
  - simpl. reflexivity.
  - simpl. rewrite length_app. simpl. rewrite IHl. rewrite IHr. lia.
Qed.

Lemma tree_insert_empty : forall x,
  tree_insert x tree_empty = TNode TLeaf x TLeaf.
Proof. intros x. simpl. reflexivity. Qed.

Lemma tree_size_singleton : forall x,
  tree_size (TNode TLeaf x TLeaf) = 1.
Proof. intros x. simpl. reflexivity. Qed.

Lemma tree_height_singleton : forall x,
  tree_height (TNode TLeaf x TLeaf) = 1.
Proof. intros x. simpl. reflexivity. Qed.

Lemma tree_all_insert : forall (p : A -> Prop) (x : A) (t : TTree),
  p x -> tree_all p t -> tree_all p (tree_insert x t).
Proof.
  intros p0 x t Hpx.
  induction t as [| l IHl v r IHr].
  - simpl. intros _. auto.
  - simpl. intros [Hpv [Hal Har]].
    destruct (dto_le_dec x v) as [Hxv | Hxv].
    + destruct (dto_le_dec v x) as [Hvx | Hvx].
      * simpl. auto.
      * simpl. auto.
    + simpl. auto.
Qed.

Lemma tree_insert_bst : forall (x : A) (t : TTree),
  is_bst t -> is_bst (tree_insert x t).
Proof.
  intros x t.
  induction t as [| l IHl v r IHr].
  - simpl. intros _.
    repeat split; try exact I; apply dto_le_refl.
  - simpl. intros [Hal [Har [Hbl Hbr]]].
    destruct (dto_le_dec x v) as [Hxv | Hxv].
    + destruct (dto_le_dec v x) as [Hvx | Hvx].
      * simpl. auto.
      * simpl. repeat split; auto.
        apply tree_all_insert; auto.
    + simpl. repeat split; auto.
      apply tree_all_insert; auto.
      destruct (dto_le_total x v) as [Hle | Hle].
      -- contradiction.
      -- exact Hle.
Qed.

Lemma tree_insert_member : forall (x : A) (t : TTree),
  is_bst t -> tree_member x (tree_insert x t) = true.
Proof.
  intros x t.
  induction t as [| l IHl v r IHr].
  - simpl. intros _.
    destruct (dto_le_dec x x) as [Hxx | Hnxx].
    + destruct (dto_le_dec x x) as [_ | Hn].
      * reflexivity.
      * exfalso. apply Hn. apply dto_le_refl.
    + exfalso. apply Hnxx. apply dto_le_refl.
  - simpl. intros [Hal [Har [Hbl Hbr]]].
    destruct (dto_le_dec x v) as [Hxv | Hxv].
    + destruct (dto_le_dec v x) as [Hvx | Hvx].
      * simpl.
        destruct (dto_le_dec x v) as [_ | Hn]; [| exfalso; auto].
        destruct (dto_le_dec v x) as [_ | Hn]; [| exfalso; auto].
        reflexivity.
      * simpl.
        destruct (dto_le_dec x v) as [_ | Hn]; [| contradiction].
        destruct (dto_le_dec v x) as [Hvx2 | _].
        -- exfalso. auto.
        -- apply IHl. exact Hbl.
    + simpl.
      destruct (dto_le_dec x v) as [Hxv2 | _].
      * exfalso. auto.
      * apply IHr. exact Hbr.
Qed.

Lemma tree_size_insert : forall (x : A) (t : TTree),
  tree_size t <= tree_size (tree_insert x t).
Proof.
  intros x t.
  induction t as [| l IHl v r IHr].
  - simpl. lia.
  - simpl.
    destruct (dto_le_dec x v) as [Hxv | Hxv].
    + destruct (dto_le_dec v x) as [Hvx | Hvx].
      * simpl. lia.
      * simpl. lia.
    + simpl. lia.
Qed.

Lemma tree_size_insert_upper : forall (x : A) (t : TTree),
  tree_size (tree_insert x t) <= S (tree_size t).
Proof.
  intros x t.
  induction t as [| l IHl v r IHr].
  - simpl. lia.
  - simpl.
    destruct (dto_le_dec x v) as [Hxv | Hxv].
    + destruct (dto_le_dec v x) as [Hvx | Hvx].
      * simpl. lia.
      * simpl. lia.
    + simpl. lia.
Qed.

Lemma tree_all_leaf : forall (p : A -> Prop), tree_all p TLeaf.
Proof. intros p0. simpl. exact I. Qed.

Lemma tree_all_root : forall (p : A -> Prop) (l : TTree) (v : A) (r : TTree),
  tree_all p (TNode l v r) -> p v.
Proof.
  intros p0 l v r H. simpl in H. destruct H as [Hv _]. exact Hv.
Qed.

Lemma tree_all_left : forall (p : A -> Prop) (l : TTree) (v : A) (r : TTree),
  tree_all p (TNode l v r) -> tree_all p l.
Proof.
  intros p0 l v r H. simpl in H. destruct H as [_ [Hl _]]. exact Hl.
Qed.

Lemma tree_all_right : forall (p : A -> Prop) (l : TTree) (v : A) (r : TTree),
  tree_all p (TNode l v r) -> tree_all p r.
Proof.
  intros p0 l v r H. simpl in H. destruct H as [_ [_ Hr]]. exact Hr.
Qed.

Definition ttree_depth (t : TTree) : nat := tree_height t.

End BST.


Definition ttree_fg (A : Type) `{DecTotalOrder A} : FinitelyGenerated (@TTree A) :=
  mkFinitelyGenerated (@TTree A) (@ttree_depth A).

Lemma ttree_fg_exists : forall (A : Type) `{DecTotalOrder A},
  exists (fg : FinitelyGenerated (@TTree A)),
    fg_depth (@TTree A) fg = @ttree_depth A.
Proof. intros A DTO. exists (ttree_fg A). reflexivity. Qed.

Example nat_bst_example :
  let t := tree_insert (A:=nat) 5 (tree_empty (A:=nat)) in
  let t := tree_insert 1 t in
  let t := tree_insert 3 t in
  tree_member 3 t = true.
Proof.
  simpl. reflexivity.
Qed.

(* END OF TTree.v: 22 Qed, 0 Admitted, 0 axioms *)
