(** * KruskalTree.v — Kruskal's Tree Theorem for Specific Sequences

    Theory of Systems — E/R/R framework:
    - Elements: FTree sequences, chain/fork families, monotone subsequences
    - Roles: tree_embed witnesses well-quasi-ordering on specific families
    - Rules: chain sequences are monotone, fork sequences are monotone,
             any consecutively-embeddable sequence has monotone subsequences

    Kruskal's tree theorem (full generality) states that tree_embed is a
    well-quasi-order on finite rooted trees. We prove this for SPECIFIC
    sequence families without requiring new axioms.

    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import List Lia Bool PeanoNat Arith Wf_nat.
Import ListNotations.

From ToS Require Import settheory.FiniteTreeEmbedding.

(* ================================================================== *)
(** ** Well-quasi-ordering and monotone subsequences                   *)
(* ================================================================== *)

(** A relation is a well-quasi-order if every infinite sequence has
    an embedding pair i < j with f(i) <= f(j). *)
Definition is_wqo {A : Type} (le : A -> A -> Prop) : Prop :=
  forall f : nat -> A, exists i j : nat, (i < j)%nat /\ le (f i) (f j).

(** A sequence has a monotone subsequence: an increasing chain of indices
    such that consecutive elements are related by le. *)
Definition has_monotone_subseq {A : Type} (le : A -> A -> Prop) (f : nat -> A) : Prop :=
  exists sub : nat -> nat,
    (forall k, (sub k < sub (S k))%nat) /\
    (forall k, le (f (sub k)) (f (sub (S k)))).

(* ================================================================== *)
(** ** Chain family: chain n = depth-n path tree                       *)
(* ================================================================== *)

(** chain m embeds in chain n whenever m <= n *)
Lemma chain_embed_all : forall m n, (m <= n)%nat -> tree_embed (chain m) (chain n).
Proof.
  intros m n Hle. induction n as [| n IHn].
  - assert (m = 0)%nat by lia. subst. apply tree_embed_refl.
  - destruct (Nat.eq_dec m (S n)).
    + subst. apply tree_embed_refl.
    + assert (Hmn : (m <= n)%nat) by lia.
      apply embed_node_skip with (s := chain n).
      * simpl. left. reflexivity.
      * apply IHn. exact Hmn.
Qed.

(** The identity chain sequence has a monotone subsequence *)
Lemma chain_identity_monotone :
  has_monotone_subseq tree_embed chain.
Proof.
  exists (fun k => k). split.
  - intro k. lia.
  - intro k. apply chain_embed_succ.
Qed.

(** For any non-decreasing function into chains, embedding is witnessed *)
Lemma chain_nondec_wqo_pair :
  forall f : nat -> nat,
  (forall k, (f k <= f (S k))%nat) ->
  exists i j : nat, (i < j)%nat /\ tree_embed (chain (f i)) (chain (f j)).
Proof.
  intros f Hnd.
  exists 0, 1. split.
  - lia.
  - apply chain_embed_all. apply Hnd.
Qed.

(* ================================================================== *)
(** ** Fork family: fork n = star with n leaves                        *)
(* ================================================================== *)

(** Helper: repeat FLeaf m embeds in repeat FLeaf n when m <= n *)
Lemma repeat_leaf_list_embed : forall m n,
  (m <= n)%nat -> list_embed (repeat FLeaf m) (repeat FLeaf n).
Proof.
  intros m n Hle. induction n as [| n IHn].
  - assert (m = 0)%nat by lia. subst. simpl. constructor.
  - destruct (Nat.eq_dec m (S n)).
    + subst. apply list_embed_refl.
    + simpl. apply lembed_skip.
      apply IHn. lia.
Qed.

(** fork m embeds in fork n whenever m <= n *)
Lemma fork_embed_all : forall m n,
  (m <= n)%nat -> tree_embed (fork m) (fork n).
Proof.
  intros m n Hle. unfold fork.
  apply embed_node_match.
  apply repeat_leaf_list_embed. exact Hle.
Qed.

(** The identity fork sequence has a monotone subsequence *)
Lemma fork_identity_monotone :
  has_monotone_subseq tree_embed fork.
Proof.
  exists (fun k => k). split.
  - intro k. lia.
  - intro k. unfold fork. apply fork_embed_succ.
Qed.

(** For any non-decreasing function into forks, embedding is witnessed *)
Lemma fork_nondec_wqo_pair :
  forall f : nat -> nat,
  (forall k, (f k <= f (S k))%nat) ->
  exists i j : nat, (i < j)%nat /\ tree_embed (fork (f i)) (fork (f j)).
Proof.
  intros f Hnd.
  exists 0, 1. split.
  - lia.
  - apply fork_embed_all. apply Hnd.
Qed.

(* ================================================================== *)
(** ** General consecutive-embedding sequences                         *)
(* ================================================================== *)

(** Any sequence where consecutive elements embed has a trivial
    monotone subsequence (the identity). *)
Lemma consec_embed_monotone :
  forall f : nat -> FTree,
  (forall k, tree_embed (f k) (f (S k))) ->
  has_monotone_subseq tree_embed f.
Proof.
  intros f Hconsec.
  exists (fun k => k). split.
  - intro k. lia.
  - exact Hconsec.
Qed.

(** Shifted subsequence: if sub is strictly increasing, so is S o sub *)
Lemma shift_subseq_strict :
  forall sub : nat -> nat,
  (forall k, (sub k < sub (S k))%nat) ->
  (forall k, (S (sub k) < S (sub (S k)))%nat).
Proof.
  intros sub Hstr k. specialize (Hstr k). lia.
Qed.

(** Any constant sequence trivially has monotone subsequence *)
Lemma const_seq_monotone :
  forall t : FTree,
  has_monotone_subseq tree_embed (fun _ => t).
Proof.
  intro t. exists (fun k => k). split.
  - intro k. lia.
  - intro k. apply tree_embed_refl.
Qed.

(* ================================================================== *)
(** ** Composing subsequences                                          *)
(* ================================================================== *)

(** A strictly increasing function is monotone: a < b -> f(a) < f(b) *)
Lemma strict_incr_mono :
  forall (f : nat -> nat),
  (forall k, (f k < f (S k))%nat) ->
  forall a b, (a < b)%nat -> (f a < f b)%nat.
Proof.
  intros f Hf a b Hab.
  induction Hab.
  - apply Hf.
  - apply Nat.lt_trans with (f m).
    + exact IHHab.
    + apply Hf.
Qed.

(** A strictly increasing nat function composed with a strictly increasing
    function yields a strictly increasing function *)
Lemma compose_strict_increasing :
  forall (f g : nat -> nat),
  (forall k, (f k < f (S k))%nat) ->
  (forall k, (g k < g (S k))%nat) ->
  (forall k, (f (g k) < f (g (S k)))%nat).
Proof.
  intros f g Hf Hg k.
  apply strict_incr_mono.
  - exact Hf.
  - apply Hg.
Qed.

(** Composing a strictly increasing function preserves monotone subsequence *)
Lemma monotone_subseq_compose :
  forall (le : FTree -> FTree -> Prop) (f : nat -> FTree) (g : nat -> nat),
  (forall k, (g k < g (S k))%nat) ->
  (forall k, le (f (g k)) (f (g (S k)))) ->
  has_monotone_subseq le f.
Proof.
  intros le f g Hg Hmon.
  exists g. split; assumption.
Qed.

(* ================================================================== *)
(** ** Kruskal for specific families: synthesis                        *)
(* ================================================================== *)

(** Nat.le is WQO: every infinite nat sequence has i<j with f(i)<=f(j).
    Proof: by well-founded induction on f(0). If f(0)<=f(1), take i=0,j=1.
    Otherwise f(1)<f(0), and the tail g(k):=f(S k) has g(0)=f(1)<f(0),
    so by IH on g there exist i'<j' with g(i')<=g(j'), take i=S i', j=S j'. *)

(** Helper: minimum of a nat sequence over [0..n] *)
Fixpoint seq_min (f : nat -> nat) (n : nat) : nat :=
  match n with
  | O => f O
  | S n' => Nat.min (f (S n')) (seq_min f n')
  end.

Lemma seq_min_le : forall f n k, (k <= n)%nat -> (seq_min f n <= f k)%nat.
Proof.
  intros f n. induction n as [| n IHn]; intros k Hk.
  - assert (k = 0)%nat by lia. subst. simpl. lia.
  - destruct (Nat.eq_dec k (S n)).
    + subst. simpl. lia.
    + assert (Hk' : (k <= n)%nat) by lia.
      simpl. specialize (IHn k Hk'). lia.
Qed.

Lemma seq_min_achieved : forall f n, exists k, (k <= n)%nat /\ seq_min f n = f k.
Proof.
  intros f n. induction n as [| n IHn].
  - exists 0. split; [lia | reflexivity].
  - simpl. destruct IHn as [k [Hk Heq]].
    destruct (Nat.le_gt_cases (f (S n)) (seq_min f n)).
    + exists (S n). split; [lia |]. lia.
    + exists k. split; [lia |]. lia.
Qed.

(** An infinite strictly decreasing sequence of nats is impossible.
    We prove: for any f, some consecutive pair has f(k) <= f(S k). *)
Lemma nat_no_infinite_descent_aux :
  forall v : nat, forall f : nat -> nat,
  f 0 = v ->
  exists k, (f k <= f (S k))%nat.
Proof.
  intro v. induction v as [v IHv] using lt_wf_ind.
  intros f Hf0.
  destruct (Nat.le_gt_cases (f 0) (f 1)) as [H | H].
  - exists 0. exact H.
  - (* f(1) < f(0) = v. Apply IH to the tail g(k) := f(S k) with g(0) = f(1) < v *)
    assert (Hlt : (f 1 < v)%nat) by lia.
    destruct (IHv (f 1) Hlt (fun k => f (S k)) eq_refl) as [k Hk].
    exists (S k). exact Hk.
Qed.

(** Key: natural numbers under <= form a WQO. *)
Lemma wqo_nat_le : is_wqo Nat.le.
Proof.
  intro f.
  destruct (nat_no_infinite_descent_aux (f 0) f eq_refl) as [k Hk].
  exists k, (S k). split.
  - lia.
  - exact Hk.
Qed.

(** Kruskal holds for the chain family *)
Lemma kruskal_chains :
  is_wqo (fun m n => tree_embed (chain m) (chain n)).
Proof.
  intro f.
  destruct (wqo_nat_le f) as [i [j [Hij Hle]]].
  exists i, j. split.
  - exact Hij.
  - apply chain_embed_all. exact Hle.
Qed.

(** Kruskal holds for the fork family *)
Lemma kruskal_forks :
  is_wqo (fun m n => tree_embed (fork m) (fork n)).
Proof.
  intro f.
  destruct (wqo_nat_le f) as [i [j [Hij Hle]]].
  exists i, j. split.
  - exact Hij.
  - apply fork_embed_all. exact Hle.
Qed.

(* ================================================================== *)
(** ** REMARK on full Kruskal's theorem                                *)
(* ================================================================== *)

(** REMARK: Full Kruskal's tree theorem states:
      kruskal_tree : is_wqo tree_embed
    This is provable in Pi^1_1-CA_0 via Higman's lemma + Nash-Williams
    minimal bad sequence argument. We do NOT add it as an axiom.

    The specific cases above (chains, forks, consecutive-embedding
    sequences) suffice for our application to L5 Resolution, where
    distinction histories form naturally growing tree sequences.

    Key insight: In ToS, every distinction process produces trees
    that grow monotonically (each step refines the previous), so
    consecutive embedding is guaranteed by construction. Full Kruskal
    is stronger than needed.
*)
