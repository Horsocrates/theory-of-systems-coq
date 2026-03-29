(** FiniteTreeEmbedding.v
    Finite rooted trees and homeomorphic embedding.

    Theory of Systems — E/R/R framework:
    - Elements: FTree (finite rooted trees), tree_embed, list_embed
    - Roles: embedding witnesses structural containment
    - Rules: reflexivity, monotonicity, chain/fork sequences
*)

From Stdlib Require Import List Lia.
Import ListNotations.

(** Finite rooted tree *)
Inductive FTree : Set :=
  | FLeaf : FTree
  | FNode : list FTree -> FTree.

(** Homeomorphic embedding *)
Inductive tree_embed : FTree -> FTree -> Prop :=
  | embed_leaf : forall s, tree_embed FLeaf s
  | embed_node_match : forall ts ss,
      list_embed ts ss -> tree_embed (FNode ts) (FNode ss)
  | embed_node_skip : forall t s ss,
      In s ss -> tree_embed t s -> tree_embed t (FNode ss)
with list_embed : list FTree -> list FTree -> Prop :=
  | lembed_nil : forall ss, list_embed [] ss
  | lembed_cons : forall t ts s ss,
      tree_embed t s -> list_embed ts ss ->
      list_embed (t :: ts) (s :: ss)
  | lembed_skip : forall ts s ss,
      list_embed ts ss -> list_embed ts (s :: ss).

(** Concrete trees *)
Definition t_leaf := FLeaf.
Definition t_1 := FNode [FLeaf].
Definition t_2 := FNode [FLeaf; FLeaf].
Definition t_chain2 := FNode [FNode [FLeaf]].
Definition t_chain3 := FNode [FNode [FNode [FLeaf]]].
Definition t_fork := FNode [FNode [FLeaf]; FNode [FLeaf]].

(** 1. Leaf embeds in anything *)
Lemma embed_leaf_anything : forall s, tree_embed FLeaf s.
Proof. constructor. Qed.

(** 2-3. Reflexivity (mutual via fix) *)
Lemma tree_embed_refl : forall t, tree_embed t t.
Proof.
  fix IH 1. intro t. destruct t.
  - constructor.
  - apply embed_node_match. induction l.
    + constructor.
    + constructor. apply IH. exact IHl.
Qed.

Lemma list_embed_refl : forall ts, list_embed ts ts.
Proof.
  induction ts.
  - constructor.
  - constructor. apply tree_embed_refl. exact IHts.
Qed.

(** 4. t_1 embeds in t_2 *)
Lemma embed_1_in_2 : tree_embed t_1 t_2.
Proof.
  apply embed_node_match.
  apply lembed_cons. constructor. constructor.
Qed.

(** 5. chain2 embeds in chain3 *)
Lemma embed_chain2_in_chain3 : tree_embed t_chain2 t_chain3.
Proof.
  apply embed_node_match.
  apply lembed_cons.
  - apply embed_node_match.
    apply lembed_cons. constructor. constructor.
  - constructor.
Qed.

(** Helper: FNode cannot embed in FLeaf *)
Lemma no_node_in_leaf : forall ts, ~ tree_embed (FNode ts) FLeaf.
Proof.
  intros ts H. inversion H.
Qed.

(** Helper: list_embed requires target at least as long *)
Lemma list_embed_nil_inv : forall t ts,
  ~ list_embed (t :: ts) [].
Proof.
  intros t ts H. inversion H.
Qed.

(** Helper: list_embed of two-element list into singleton is impossible *)
Lemma list_embed_2_1_false : forall a b c,
  ~ list_embed [a; b] [c].
Proof.
  intros a b c H.
  inversion H as [| ? ? ? ? ? Hle | ? ? ? Hle]; subst.
  - inversion Hle as [| ? ? ? ? ? Hle2 | ? ? ? Hle2]; subst;
    inversion Hle2.
  - inversion Hle.
Qed.

(** 6. t_2 does not embed in t_1 *)
Lemma not_embed_2_in_1 : ~ tree_embed t_2 t_1.
Proof.
  unfold t_2, t_1. intro H.
  inversion H as [| ? ? Hle | ? ? ? Hin Hemb]; subst.
  - (* embed_node_match *)
    exact (list_embed_2_1_false FLeaf FLeaf FLeaf Hle).
  - (* embed_node_skip *)
    simpl in Hin. destruct Hin as [Hin | Hin]; [| contradiction].
    subst. exact (no_node_in_leaf [FLeaf; FLeaf] Hemb).
Qed.

(** 7. Tree size *)
Fixpoint tree_size (t : FTree) : nat :=
  match t with
  | FLeaf => 1
  | FNode ch => S (fold_left (fun acc c => acc + tree_size c) ch 0)
  end.

Lemma tree_size_leaf : tree_size FLeaf = 1.
Proof. reflexivity. Qed.

Lemma tree_size_1 : tree_size t_1 = 2.
Proof. reflexivity. Qed.

Lemma tree_size_2 : tree_size t_2 = 3.
Proof. reflexivity. Qed.

(** 8. Tree depth *)
Fixpoint tree_depth (t : FTree) : nat :=
  match t with
  | FLeaf => 0
  | FNode ch => S (fold_left (fun acc c => Nat.max acc (tree_depth c)) ch 0)
  end.

Lemma tree_depth_leaf : tree_depth FLeaf = 0.
Proof. reflexivity. Qed.

Lemma tree_depth_1 : tree_depth t_1 = 1.
Proof. reflexivity. Qed.

Lemma tree_depth_chain3 : tree_depth t_chain3 = 3.
Proof. reflexivity. Qed.

(** 9. Chain sequence *)
Fixpoint chain (n : nat) : FTree :=
  match n with
  | O => FLeaf
  | S n' => FNode [chain n']
  end.

Lemma chain_0 : chain 0 = FLeaf.
Proof. reflexivity. Qed.

Lemma chain_embed_succ : forall n, tree_embed (chain n) (chain (S n)).
Proof.
  intro n. simpl.
  apply embed_node_skip with (s := chain n).
  - simpl. left. reflexivity.
  - apply tree_embed_refl.
Qed.

(** 10. Fork sequence: FNode with n leaves *)
Definition fork (n : nat) : FTree := FNode (repeat FLeaf n).

Lemma fork_embed_succ : forall n,
  tree_embed (FNode (repeat FLeaf n)) (FNode (repeat FLeaf (S n))).
Proof.
  intro n. apply embed_node_match.
  simpl. apply lembed_skip.
  apply list_embed_refl.
Qed.
