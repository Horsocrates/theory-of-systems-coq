(* ========================================================================= *)
(*                                                                           *)
(*                   BINARY PROCESS TYPES & COLLECTIONS                      *)
(*           Cantor Space 2^N, Trees, and Structural Properties              *)
(*                                                                           *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)         *)
(*                                                                           *)
(*  E/R/R INTERPRETATION:                                                    *)
(*  =====================                                                    *)
(*    Elements: BinProcess (nat -> bool), binary sequences in Cantor space   *)
(*    Roles:    bp_eq, bp_agree (equivalence and prefix agreement)           *)
(*    Rules:    Enumeration, tree structure, splitting, isolation             *)
(*                                                                           *)
(*  STATUS: 29 Qed, 0 Admitted, 0 axioms (except classic for 1 lemma)       *)
(*  P4 REFACTORING: PrunedTree is now list bool -> bool (decidable)         *)
(*  Author: Horsocrates | Date: March 2026                                   *)
(*                                                                           *)
(* ========================================================================= *)

Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
From ToS Require Import ToS_Axioms.
Import ListNotations.

(* ========================================================================= *)
(*                  PART I: BINARY PROCESS DEFINITIONS                       *)
(* ========================================================================= *)

(** A binary process is a function from natural numbers to booleans.
    This is the Cantor space 2^N. *)
Definition BinProcess := nat -> bool.

(** Pointwise equality of binary processes. *)
Definition bp_eq (p q : BinProcess) : Prop := forall n, p n = q n.

(** The first n values of a process, collected into a list. *)
Definition bp_prefix (p : BinProcess) (n : nat) : list bool := map p (seq 0 n).

(** Two processes agree on the first n positions. *)
Definition bp_agree (p q : BinProcess) (n : nat) : Prop :=
  forall k, (k < n)%nat -> p k = q k.

(* ========================================================================= *)
(*                  PART II: COLLECTIONS & ENUMERABILITY                     *)
(* ========================================================================= *)

(** A collection of binary processes (a subset of Cantor space). *)
Definition BinCollection := BinProcess -> Prop.

(** A collection is enumerable if there is a surjection from nat. *)
Definition is_enumerable (C : BinCollection) : Prop :=
  exists f : nat -> BinProcess, forall p, C p -> exists n, bp_eq (f n) p.

(** A collection is empty if it contains no process. *)
Definition is_empty (C : BinCollection) : Prop := forall p, ~ C p.

(* ========================================================================= *)
(*                  PART III: PRUNED TREES                                   *)
(* ========================================================================= *)

(** A pruned tree is a decidable predicate on finite binary strings.
    By P4 (Finite Actuality), membership is a finite operation
    that must terminate with a definite answer: bool, not Prop. *)
Definition PrunedTree := list bool -> bool.

(** A valid tree contains the root and is prefix-closed. *)
Definition is_tree (T : PrunedTree) : Prop :=
  T [] = true /\ forall sigma, T sigma = true -> T (removelast sigma) = true.

(** Node has a left child. *)
Definition has_left (T : PrunedTree) (sigma : list bool) : Prop :=
  T (sigma ++ [false]) = true.

(** Node has a right child. *)
Definition has_right (T : PrunedTree) (sigma : list bool) : Prop :=
  T (sigma ++ [true]) = true.

(** A node is splitting if it has both children. *)
Definition is_splitting (T : PrunedTree) (sigma : list bool) : Prop :=
  has_left T sigma /\ has_right T sigma.

(** An infinite path through the tree. *)
Definition is_path (T : PrunedTree) (p : BinProcess) : Prop :=
  forall n, T (bp_prefix p n) = true.

(** A perfect tree: every node extends to a splitting node. *)
Definition is_perfect (T : PrunedTree) : Prop :=
  is_tree T /\
  forall sigma, T sigma = true ->
    exists tau, T (sigma ++ tau) = true /\ is_splitting T (sigma ++ tau).

(** A collection has a perfect subset if some perfect tree's paths lie in it.
    The witness tree is Prop-valued (list bool -> Prop) to accommodate
    non-decidable witnesses like the Cantor-Bendixson kernel.
    A decidable tree T : PrunedTree can always be lifted via (fun s => T s = true). *)
Definition has_perfect_subset (C : BinCollection) : Prop :=
  exists (mem : list bool -> Prop),
    (* tree: root + prefix-closed *)
    mem [] /\
    (forall sigma, mem sigma -> mem (removelast sigma)) /\
    (* perfect: every node extends to a splitting node *)
    (forall sigma, mem sigma ->
       exists tau, mem (sigma ++ tau) /\
                   mem (sigma ++ tau ++ [false]) /\ mem (sigma ++ tau ++ [true])) /\
    (* paths lie in C *)
    (forall p, (forall n, mem (bp_prefix p n)) -> C p).

(** A point is isolated if some prefix separates it from all other members. *)
Definition is_isolated (C : BinCollection) (p : BinProcess) : Prop :=
  C p /\ exists n, forall q, C q -> bp_agree p q n -> bp_eq p q.

(* ========================================================================= *)
(*                  PART IV: AUXILIARY DEFINITIONS                           *)
(* ========================================================================= *)

(** A process extends a prefix if its values match the list entries. *)
Definition extends_prefix (p : BinProcess) (sigma : list bool) : Prop :=
  forall k, (k < length sigma)%nat -> p k = nth k sigma false.

(** The subcollection of paths through T that extend a given prefix. *)
Definition paths_extending (T : PrunedTree) (sigma : list bool) : BinCollection :=
  fun p => is_path T p /\ extends_prefix p sigma.

(* ========================================================================= *)
(*                  PART V: LEMMAS ON bp_eq                                  *)
(* ========================================================================= *)

Lemma bp_eq_refl : forall p, bp_eq p p.
Proof.
  unfold bp_eq. intros p n. reflexivity.
Qed.

Lemma bp_eq_sym : forall p q, bp_eq p q -> bp_eq q p.
Proof.
  unfold bp_eq. intros p q H n. symmetry. apply H.
Qed.

Lemma bp_eq_trans : forall p q r, bp_eq p q -> bp_eq q r -> bp_eq p r.
Proof.
  unfold bp_eq. intros p q r Hpq Hqr n.
  rewrite Hpq. apply Hqr.
Qed.

(* ========================================================================= *)
(*                  PART VI: LEMMAS ON bp_agree                              *)
(* ========================================================================= *)

Lemma bp_agree_0 : forall p q, bp_agree p q 0.
Proof.
  unfold bp_agree. intros p q k Hk. lia.
Qed.

Lemma bp_agree_refl : forall p n, bp_agree p p n.
Proof.
  unfold bp_agree. intros p n k Hk. reflexivity.
Qed.

Lemma bp_agree_mono : forall p q n m,
  (n <= m)%nat -> bp_agree p q m -> bp_agree p q n.
Proof.
  unfold bp_agree. intros p q n m Hnm Hm k Hk.
  apply Hm. lia.
Qed.

Lemma bp_agree_S : forall p q n,
  bp_agree p q (S n) -> bp_agree p q n /\ p n = q n.
Proof.
  unfold bp_agree. intros p q n H. split.
  - intros k Hk. apply H. lia.
  - apply H. lia.
Qed.

Lemma bp_agree_ext : forall p q n,
  bp_agree p q n -> p n = q n -> bp_agree p q (S n).
Proof.
  unfold bp_agree. intros p q n Hagree Heq k Hk.
  destruct (Nat.eq_dec k n) as [-> | Hne].
  - exact Heq.
  - apply Hagree. lia.
Qed.

Lemma bp_agree_eq_iff : forall p q,
  bp_eq p q <-> forall n, bp_agree p q n.
Proof.
  unfold bp_eq, bp_agree. split.
  - intros H n k Hk. apply H.
  - intros H n. specialize (H (S n) n). apply H. lia.
Qed.

(* ========================================================================= *)
(*                  PART VII: LEMMAS ON bp_prefix                            *)
(* ========================================================================= *)

Lemma bp_prefix_length : forall p n, length (bp_prefix p n) = n.
Proof.
  unfold bp_prefix. intros p n.
  rewrite map_length. rewrite seq_length. reflexivity.
Qed.

Lemma bp_prefix_O : forall p, bp_prefix p 0 = [].
Proof.
  unfold bp_prefix. intros p. simpl. reflexivity.
Qed.

(** Helper: the k-th element of bp_prefix p n is p k, when k < n. *)
Lemma bp_prefix_nth : forall p n k,
  (k < n)%nat -> nth k (bp_prefix p n) false = p k.
Proof.
  unfold bp_prefix. intros p n k Hk.
  rewrite (nth_indep _ false (p 0)).
  2: { rewrite map_length, seq_length. lia. }
  rewrite map_nth.
  rewrite seq_nth by lia.
  simpl. reflexivity.
Qed.

Lemma bp_prefix_S : forall p n,
  bp_prefix p (S n) = bp_prefix p n ++ [p n].
Proof.
  intros p n.
  apply nth_ext with (d := false) (d' := false).
  - rewrite bp_prefix_length. rewrite app_length. rewrite bp_prefix_length. simpl. lia.
  - intros i Hi. rewrite bp_prefix_length in Hi.
    rewrite bp_prefix_nth by lia.
    destruct (Nat.lt_ge_cases i n) as [Hlt | Hge].
    + rewrite app_nth1 by (rewrite bp_prefix_length; lia).
      rewrite bp_prefix_nth by lia. reflexivity.
    + assert (i = n) by lia. subst.
      rewrite app_nth2 by (rewrite bp_prefix_length; lia).
      rewrite bp_prefix_length. replace (n - n)%nat with 0 by lia.
      simpl. reflexivity.
Qed.

(** Two processes agree on first n iff their prefixes match. *)
Lemma bp_prefix_agree : forall p q n,
  bp_agree p q n <-> bp_prefix p n = bp_prefix q n.
Proof.
  split.
  - (* Forward: agreement implies equal prefixes *)
    intros Hagree.
    apply nth_ext with (d := false) (d' := false).
    + repeat rewrite bp_prefix_length. reflexivity.
    + intros i Hi.
      rewrite bp_prefix_length in Hi.
      rewrite bp_prefix_nth by lia.
      rewrite bp_prefix_nth by lia.
      apply Hagree. lia.
  - (* Backward: equal prefixes implies agreement *)
    intros Hpfx.
    unfold bp_agree. intros k Hk.
    assert (H1 : nth k (bp_prefix p n) false = p k) by (apply bp_prefix_nth; lia).
    assert (H2 : nth k (bp_prefix q n) false = q k) by (apply bp_prefix_nth; lia).
    rewrite <- H1, <- H2.
    rewrite Hpfx. reflexivity.
Qed.

(* ========================================================================= *)
(*                  PART VIII: DECIDABILITY                                  *)
(* ========================================================================= *)

Lemma bool_eq_dec : forall b1 b2 : bool, {b1 = b2} + {b1 <> b2}.
Proof.
  destruct b1; destruct b2.
  - left. reflexivity.
  - right. discriminate.
  - right. discriminate.
  - left. reflexivity.
Qed.

Lemma bp_eq_dec_at_n : forall (p q : BinProcess) (n : nat), {p n = q n} + {p n <> q n}.
Proof.
  intros p q n. apply bool_eq_dec.
Qed.

(** P4 decidability: tree membership is decidable (free from bool). *)
Lemma tree_mem_dec : forall (T : PrunedTree) sigma,
  {T sigma = true} + {T sigma = false}.
Proof.
  intros. destruct (T sigma); [left|right]; reflexivity.
Qed.

Lemma has_left_dec : forall T sigma,
  {has_left T sigma} + {~ has_left T sigma}.
Proof.
  intros. unfold has_left. destruct (T (sigma ++ [false])).
  - left. reflexivity.
  - right. discriminate.
Qed.

Lemma has_right_dec : forall T sigma,
  {has_right T sigma} + {~ has_right T sigma}.
Proof.
  intros. unfold has_right. destruct (T (sigma ++ [true])).
  - left. reflexivity.
  - right. discriminate.
Qed.

Lemma is_splitting_dec : forall T sigma,
  {is_splitting T sigma} + {~ is_splitting T sigma}.
Proof.
  intros. destruct (has_left_dec T sigma); destruct (has_right_dec T sigma);
  [left|right|right|right]; unfold is_splitting; tauto.
Qed.

(* ========================================================================= *)
(*                  PART IX: ENUMERABILITY LEMMAS                            *)
(* ========================================================================= *)

Lemma enumerable_empty : forall C, is_empty C -> is_enumerable C.
Proof.
  unfold is_empty, is_enumerable. intros C Hempty.
  exists (fun _ => fun _ => false). (* arbitrary enumeration *)
  intros p Hp. exfalso. apply (Hempty p). exact Hp.
Qed.

Lemma singleton_enumerable : forall p, is_enumerable (fun q => bp_eq q p).
Proof.
  unfold is_enumerable. intros p.
  exists (fun _ => p).
  intros q Hq. exists 0.
  apply bp_eq_sym. exact Hq.
Qed.

(* ========================================================================= *)
(*                  PART X: TREE LEMMAS                                      *)
(* ========================================================================= *)

Lemma tree_root : forall T, is_tree T -> T [] = true.
Proof.
  intros T [Hroot _]. exact Hroot.
Qed.

Lemma path_prefix_in_tree : forall T p,
  is_path T p -> forall n, T (bp_prefix p n) = true.
Proof.
  unfold is_path. intros T p Hpath n. apply Hpath.
Qed.

(* ========================================================================= *)
(*                  PART XI: EXTENDS PREFIX LEMMAS                           *)
(* ========================================================================= *)

Lemma extends_prefix_nil : forall p, extends_prefix p [].
Proof.
  unfold extends_prefix. intros p k Hk. simpl in Hk. lia.
Qed.

Lemma extends_prefix_bp_prefix : forall p n, extends_prefix p (bp_prefix p n).
Proof.
  unfold extends_prefix. intros p n k Hk.
  rewrite bp_prefix_length in Hk.
  symmetry. apply bp_prefix_nth. exact Hk.
Qed.

Lemma paths_extending_nil : forall T p,
  is_path T p -> paths_extending T [] p.
Proof.
  unfold paths_extending. intros T p Hpath. split.
  - exact Hpath.
  - apply extends_prefix_nil.
Qed.

(* ========================================================================= *)
(*                  PART XII: UNION ENUMERABILITY                            *)
(* ========================================================================= *)

Lemma enum_union_enum : forall A B : BinCollection,
  is_enumerable A -> is_enumerable B ->
  is_enumerable (fun p => A p \/ B p).
Proof.
  unfold is_enumerable. intros A B [fA HA] [fB HB].
  (* Interleave: even indices -> fA, odd indices -> fB *)
  exists (fun n =>
    if Nat.even n then fA (Nat.div2 n)
    else fB (Nat.div2 n)).
  intros p [HpA | HpB].
  - (* p in A *)
    destruct (HA p HpA) as [nA HnA].
    exists (2 * nA)%nat.
    replace (Nat.even (2 * nA)) with true.
    2: { symmetry. rewrite Nat.even_mul. simpl. reflexivity. }
    replace (Nat.div2 (2 * nA)) with nA.
    2: { rewrite Nat.div2_double. reflexivity. }
    exact HnA.
  - (* p in B *)
    destruct (HB p HpB) as [nB HnB].
    exists (2 * nB + 1)%nat.
    replace (Nat.even (2 * nB + 1)) with false.
    2: { symmetry. rewrite Nat.even_add, Nat.even_mul. simpl. reflexivity. }
    replace (Nat.div2 (2 * nB + 1)) with nB.
    2: { symmetry. apply Nat.div2_odd'. }
    exact HnB.
Qed.

Lemma not_enum_union : forall A B,
  ~is_enumerable (fun p => A p \/ B p) ->
  ~is_enumerable A \/ ~is_enumerable B.
Proof.
  intros A B Hnot.
  destruct (classic (is_enumerable A)) as [HA | HnA].
  - destruct (classic (is_enumerable B)) as [HB | HnB].
    + exfalso. apply Hnot. apply enum_union_enum; assumption.
    + right. exact HnB.
  - left. exact HnA.
Qed.

(* ========================================================================= *)
(*                           SUMMARY                                         *)
(* ========================================================================= *)
(*                                                                           *)
(*  DEFINITIONS:                                                             *)
(*    BinProcess, bp_eq, bp_prefix, bp_agree                                 *)
(*    BinCollection, is_enumerable, is_empty                                 *)
(*    PrunedTree, is_tree, has_left, has_right, is_splitting                  *)
(*    is_path, is_perfect, has_perfect_subset, is_isolated                    *)
(*    extends_prefix, paths_extending                                        *)
(*                                                                           *)
(*  LEMMAS (29 Qed, 0 Admitted):                                             *)
(*    bp_eq:      refl, sym, trans                                            *)
(*    bp_agree:   0, refl, mono, S, ext, eq_iff                              *)
(*    bp_prefix:  length, O, nth, S, agree                                    *)
(*    decidability: bool_eq_dec, bp_eq_dec_at_n,                              *)
(*                  tree_mem_dec, has_left_dec, has_right_dec,                *)
(*                  is_splitting_dec  (P4 — no axioms!)                       *)
(*    enumeration: enumerable_empty, singleton_enumerable,                   *)
(*                 enum_union_enum, not_enum_union                            *)
(*    trees:      tree_root, path_prefix_in_tree                              *)
(*    extends:    extends_prefix_nil, extends_prefix_bp_prefix,              *)
(*                paths_extending_nil                                         *)
(*                                                                           *)
(*  AXIOMS USED: classic (only for not_enum_union)                           *)
(*  NOTE: PrunedTree is list bool -> bool (P4 decidability), all tree        *)
(*        decidability lemmas are axiom-free.                                 *)
(*                                                                           *)
(* ========================================================================= *)

(** Check axiom usage for a key constructive lemma: *)
Print Assumptions bp_agree_eq_iff.
(* Expected: Closed under the global context *)
