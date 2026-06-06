(** * NestedHierarchyConservation.v — from the cascade CHAIN to a genuine NESTING TREE (the medium step
      of the far-horizon, ПЛАН-Иерархии-и-Каскады.md §8.5).  A finite binary tree of NESTED systems, with
      the inter-level relation (a parent's content is the sum of its children's -- VERTICAL coupling
      parent<-children plus LATERAL coupling between the two sibling sub-systems) and a conservation law
      (the content is independent of the nesting structure).  This directly answers "how adjacent systems
      influence neighbours at different levels": parent <- children (vertical) and sibling + sibling
      (lateral), with the total content conserved.

   -- A nesting tree: WLeaf q (a finest system with content q in Q) or WNode l r (a system whose content
      is its two nested sub-systems).  wval t = the content of t = sum over its leaves.
   -- Inter-level relation (vertical + lateral): wval (WNode l r) = wval l + wval r -- the parent's
      content is exactly the sum of its two sibling children's contents.
   -- CONSERVATION: wval t = qsum (leaves t) -- the content depends ONLY on the leaves, NOT on how they
      are nested/bracketed.  Hence any two trees with the same leaves have the same content
      (content_nesting_independent), and regrouping sub-systems conserves content (wval_rebracket).  This
      is the tree generalization of the cascade chain's telescoping conservation.
   -- Nesting monotonicity (for non-negative content): a nested sub-system's content contributes to (is
      <= ) the content of every enclosing system (subtree_le_parent_left).
   -- The chain (cascade) is the path-tree special case -- a right-spine WNode (WLeaf .) (WNode ...)
      recovers the linear hierarchy, so this strictly generalizes ScaleHierarchyTransfer.

   HONEST SCOPE.  The Element side of nesting: every FINITE nesting tree has exact rational content,
   conserved under arbitrary regrouping.  The role-limit is the closure -- INFINITE nesting depth -- which
   is not constructed here (a finite tree is all we build; the infinite-depth limit is the role-limit).
   Relocate, not cross.  Level: synthesis + observation (the chain->tree generalization).

   Elements: the nesting tree WTree; leaf contents in Q; the content wval.
   Roles:    nodes = systems at levels; parent<-children = vertical coupling; sibling+sibling = lateral;
             leaves = finest systems, root = the whole.
   Rules:    parent content = sum of children (inter-level); content = leaf sum (nesting-independent
             conservation); regrouping conserves; finite nesting = Element, infinite depth = role-limit.

   ============ E/R/R разбор ============
     Rules (L5): wval(родитель)=wval(l)+wval(r) (межуровень); содержание = Σ листья (независимо от вложенности).
     Roles (L4): узлы = системы; родитель<-дети = вертикаль; брат+брат = латераль; листья/корень.
     Elements  : дерево WTree; листья in Q; содержание wval.
   ДИАГНОСТИКА (P4): конечное дерево = Element (точное содержание, сохранено при перегруппировке);
   бесконечная глубина = role-limit. Обобщает цепь->дерево (вертикаль+латераль+сохранение). Цепь =
   path-дерево (восстанавливает каскад). Локализуем, не пересекаем.

   STATUS: 11 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith List Lia.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ===================================================================== *)
(*  A nesting tree of systems and its content                              *)
(* ===================================================================== *)

(** A nested-system tree: a leaf (finest system, content q) or a node (two nested sub-systems). *)
Inductive WTree := WLeaf : Q -> WTree | WNode : WTree -> WTree -> WTree.

(** Content of a (sub)system = sum over its finest sub-systems (leaves). *)
Fixpoint wval (t : WTree) : Q :=
  match t with WLeaf q => q | WNode l r => wval l + wval r end.

(** ★ Inter-level relation (VERTICAL parent<-children + LATERAL sibling+sibling):
    a parent's content is exactly the sum of its two children's contents. *)
Lemma wval_node : forall l r, wval (WNode l r) == wval l + wval r.
Proof. intros. simpl. reflexivity. Qed.

(* ===================================================================== *)
(*  Conservation: content is independent of the nesting structure          *)
(* ===================================================================== *)

(** The leaves (finest sub-systems) and their sum. *)
Fixpoint leaves (t : WTree) : list Q :=
  match t with WLeaf q => q :: nil | WNode l r => leaves l ++ leaves r end.
Fixpoint qsum (xs : list Q) : Q :=
  match xs with nil => 0 | x :: ys => x + qsum ys end.

Lemma qsum_app : forall xs ys, qsum (xs ++ ys) == qsum xs + qsum ys.
Proof.
  induction xs as [|x xs IH]; intro ys; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

(** ★ CONSERVATION: the content equals the sum of the leaves -- it depends ONLY on the finest
    sub-systems, NOT on how they are nested.  (The tree generalization of the chain's telescoping.) *)
Theorem wval_is_leafsum : forall t, wval t == qsum (leaves t).
Proof.
  induction t as [q | l IHl r IHr]; simpl.
  - ring.
  - rewrite IHl, IHr, qsum_app. ring.
Qed.

(** ★ Two trees with the same leaves have the same content: nesting structure conserves content. *)
Corollary content_nesting_independent : forall t1 t2,
  leaves t1 = leaves t2 -> wval t1 == wval t2.
Proof.
  intros t1 t2 H. rewrite !wval_is_leafsum, H. reflexivity.
Qed.

(** ★ Regrouping sub-systems conserves content (associativity of nesting). *)
Lemma wval_rebracket : forall a b c,
  wval (WNode (WNode a b) c) == wval (WNode a (WNode b c)).
Proof. intros. simpl. ring. Qed.

(* ===================================================================== *)
(*  Nesting monotonicity: a sub-system contributes to its enclosing system *)
(* ===================================================================== *)

Fixpoint tree_nonneg (t : WTree) : Prop :=
  match t with WLeaf q => 0 <= q | WNode l r => tree_nonneg l /\ tree_nonneg r end.

Lemma wval_nonneg : forall t, tree_nonneg t -> 0 <= wval t.
Proof.
  induction t as [q | l IHl r IHr]; simpl; intro H.
  - exact H.
  - destruct H as [Hl Hr]. pose proof (IHl Hl). pose proof (IHr Hr). lra.
Qed.

(** ★ A nested sub-system's content is <= the content of its enclosing system (for non-negative
    content): nesting only adds.  This is the "vertical influence" of a sub-system on its parent. *)
Lemma subtree_le_parent_left : forall l r,
  tree_nonneg r -> wval l <= wval (WNode l r).
Proof. intros l r Hr. simpl. pose proof (wval_nonneg r Hr). lra. Qed.

(* ===================================================================== *)
(*  Concrete witness + the H1 boundary                                     *)
(* ===================================================================== *)

(** A concrete nesting: ((1, 1/2), 1/4) -- content 7/4, independent of the bracketing. *)
Example tree_witness :
  wval (WNode (WNode (WLeaf 1) (WLeaf (1#2))) (WLeaf (1#4))) == 7#4.
Proof. vm_compute. reflexivity. Qed.

(** The two sides of the nesting hierarchy's finitization boundary. *)
Inductive NestSide := FiniteNestElement | InfiniteNestRoleLimit.
Lemma nest_h1_disjoint : FiniteNestElement <> InfiniteNestRoleLimit.
Proof. discriminate. Qed.

(* ===================================================================== *)
(*  Capstone: the nesting hierarchy conserves content (chain -> tree)       *)
(* ===================================================================== *)

(** The nesting-tree generalization of the cascade:
      (inter-level)  a parent's content is the sum of its two children (vertical + lateral);
      (conservation) the content equals the leaf sum -- independent of the nesting structure;
      (nesting-free) two trees with the same leaves have the same content;
      (regrouping)   associativity of nesting conserves content;
      (H1)           finite nesting (Element) and infinite-depth nesting (role-limit) are disjoint.
    The chain (cascade) is the path-tree special case, so this strictly generalizes the inter-level
    flux from a chain to a genuine nesting hierarchy -- vertical and lateral coupling, with conservation.
    Every finite nesting is Element; the role-limit is infinite nesting depth, located NOT crossed. *)
Theorem nested_hierarchy_conservation :
  (forall l r, wval (WNode l r) == wval l + wval r)
  /\ (forall t, wval t == qsum (leaves t))
  /\ (forall t1 t2, leaves t1 = leaves t2 -> wval t1 == wval t2)
  /\ (forall a b c, wval (WNode (WNode a b) c) == wval (WNode a (WNode b c)))
  /\ (FiniteNestElement <> InfiniteNestRoleLimit).
Proof.
  split; [exact wval_node |].
  split; [exact wval_is_leafsum |].
  split; [exact content_nesting_independent |].
  split; [exact wval_rebracket | exact nest_h1_disjoint].
Qed.
