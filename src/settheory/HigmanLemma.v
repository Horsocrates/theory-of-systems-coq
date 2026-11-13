(** * HigmanLemma.v — Higman's lemma for the one-letter alphabet + Dickson's lemma for pairs
    Elements: list embedding (list_le); WQO in the sequential form (is_wqo); chains (FChain)
    Roles:    a WQO is an order with no bad infinite sequence; Nat.le is the base WQO;
              a chain FChain f k i is k steps from i along which f does not decrease
    Rules:    nat is well-founded => Nat.le is a WQO (constructive, strong induction on the
              first value); one-letter lists embed by length => Higman for the one-letter
              alphabet (constructive, reduces to Nat.le); Dickson for pairs: constructive since
              Nov 2026 (along a chain on which f does not decrease, g cannot strictly
              decrease more than g(start) times)
    STATUS:   16 Qed, 0 Admitted; no axioms: every statement is closed under the global
              context (Print Assumptions at the end)
    SCOPE:    Higman's lemma for an ARBITRARY finite alphabet is NOT proved here: only the
              one-letter case (lists of unit), which is Nat.le on lengths.
    REPAIR (2026-10-17): the March version never compiled.  wqo_nat_le, wqo_bool,
              dickson_pair and higman_unit inspected only the first three terms of the
              sequence and, in branches such as f 0 > f 1 > f 2, tried to prove false goals
              (first failure: line 40, "Cannot find witness").  The statements are unchanged;
              the proofs are new.  The file declares no `classic` of its own, and since
              November 2026 uses none: the classical route to Dickson's lemma was removed.
    Author:   Horsocrates | Date: March 2026 (proofs repaired October 2026)
*)

From Stdlib Require Import List Lia Bool PeanoNat.
Import ListNotations.

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
(* NAT.LE IS A WQO (constructive)                                      *)
(* ================================================================= *)

(** Strong induction on the first value: either f 0 <= f 1, or the shifted
    sequence starts strictly lower and the bound drops by one. *)
Lemma wqo_nat_le_bounded : forall m (f : nat -> nat),
  (f 0 <= m)%nat -> exists i j : nat, (i < j)%nat /\ (f i <= f j)%nat.
Proof.
  induction m as [| m IH]; intros f Hm.
  - exists 0, 1. split; lia.
  - destruct (Nat.le_gt_cases (f 0) (f 1)) as [H01 | H10].
    + exists 0, 1. split; [lia | exact H01].
    + destruct (IH (fun n => f (S n))) as [i [j [Hij Hle]]].
      * simpl. lia.
      * exists (S i), (S j). split; [lia | exact Hle].
Qed.

Lemma wqo_nat_le : is_wqo Nat.le.
Proof.
  intro f. exact (wqo_nat_le_bounded (f 0) f (Nat.le_refl _)).
Qed.

(* ================================================================= *)
(* DICKSON PAIR, CONSTRUCTIVELY (Nov 2026)                             *)
(* ================================================================= *)

(* Idea: along a chain of indices on which f does not decrease, g cannot
   strictly decrease more than g(start) times; a chain whose length is given
   by a function of its start is built by induction on f 0.  No case split
   over an infinite tail is needed. *)

(* a chain of k steps starting at i: i < j1 < ... < jk with f weakly increasing
   on neighbours *)
Fixpoint FChain (f : nat -> nat) (k i : nat) : Prop :=
  match k with
  | O => True
  | S k' => exists j, (i < j)%nat /\ (f i <= f j)%nat /\ FChain f k' j
  end.

Lemma fchain_shift : forall f c k i,
  FChain (fun n => f (n + c)) k i -> FChain f k (i + c).
Proof.
  intros f c k. induction k as [| k IH]; intros i H.
  - exact I.
  - simpl in H. destruct H as [j [Hij [Hle Hc]]].
    simpl. exists (j + c). split; [lia | split; [exact Hle | apply IH; exact Hc]].
Qed.

Lemma fchain_exists_bounded : forall k,
  (forall f : nat -> nat, exists i, FChain f k i) ->
  forall m (f : nat -> nat), (f 0 <= m)%nat -> exists i, FChain f (S k) i.
Proof.
  intros k IHk. induction m as [| m IHm]; intros f Hf0.
  - destruct (IHk (fun n => f (n + 1))) as [i' Hi'].
    apply fchain_shift in Hi'.
    exists 0. simpl. exists (i' + 1). split; [lia | split; [lia | exact Hi']].
  - destruct (IHk (fun n => f (n + 1))) as [i' Hi'].
    apply fchain_shift in Hi'.
    destruct (Nat.le_gt_cases (f 0) (f (i' + 1))) as [Hle | Hgt].
    + exists 0. simpl. exists (i' + 1). split; [lia | split; [exact Hle | exact Hi']].
    + destruct (IHm (fun n => f (n + (i' + 1)))) as [i'' Hi''].
      * simpl. lia.
      * apply fchain_shift in Hi''. exists (i'' + (i' + 1)). exact Hi''.
Qed.

Lemma fchain_exists : forall k (f : nat -> nat), exists i, FChain f k i.
Proof.
  induction k as [| k IHk]; intro f.
  - exists 0. exact I.
  - exact (fchain_exists_bounded k IHk (f 0) f (Nat.le_refl _)).
Qed.

(* the length of the chain may depend on its starting index *)
Lemma fchain_dep_bounded : forall m (f h : nat -> nat),
  (f 0 <= m)%nat -> exists i, FChain f (h i) i.
Proof.
  induction m as [| m IHm]; intros f h Hf0.
  - destruct (h 0) as [| k] eqn:Eh.
    + exists 0. rewrite Eh. exact I.
    + destruct (fchain_exists k (fun n => f (n + 1))) as [i' Hi'].
      apply fchain_shift in Hi'.
      exists 0. rewrite Eh. simpl. exists (i' + 1).
      split; [lia | split; [lia | exact Hi']].
  - destruct (h 0) as [| k] eqn:Eh.
    + exists 0. rewrite Eh. exact I.
    + destruct (fchain_exists k (fun n => f (n + 1))) as [i' Hi'].
      apply fchain_shift in Hi'.
      destruct (Nat.le_gt_cases (f 0) (f (i' + 1))) as [Hle | Hgt].
      * exists 0. rewrite Eh. simpl. exists (i' + 1).
        split; [lia | split; [exact Hle | exact Hi']].
      * destruct (IHm (fun n => f (n + (i' + 1))) (fun n => h (n + (i' + 1))))
          as [i'' Hi''].
        -- simpl. lia.
        -- cbv beta in Hi''. apply fchain_shift in Hi''.
           exists (i'' + (i' + 1)). exact Hi''.
Qed.

(* on a chain longer than g at its start, two neighbours are good for g too *)
Lemma fchain_good_pair : forall (f g : nat -> nat) k i,
  FChain f k i -> (g i < k)%nat ->
  exists p q, (p < q)%nat /\ (f p <= f q)%nat /\ (g p <= g q)%nat.
Proof.
  intros f g k. induction k as [| k IH]; intros i Hc Hg.
  - lia.
  - simpl in Hc. destruct Hc as [j [Hij [Hle Hc]]].
    destruct (Nat.le_gt_cases (g i) (g j)) as [Hgle | Hggt].
    + exists i, j. split; [exact Hij | split; [exact Hle | exact Hgle]].
    + apply (IH j Hc). lia.
Qed.

Theorem dickson_pair_constructive : forall f g : nat -> nat,
  exists i j : nat, (i < j)%nat /\ (f i <= f j)%nat /\ (g i <= g j)%nat.
Proof.
  intros f g.
  destruct (fchain_dep_bounded (f 0) f (fun i => S (g i)) (Nat.le_refl _)) as [i Hi].
  cbv beta in Hi.
  exact (fchain_good_pair f g (S (g i)) i Hi (Nat.lt_succ_diag_r _)).
Qed.

(* the product order on nat * nat is a wqo *)
Theorem wqo_nat_pair :
  is_wqo (fun p q : nat * nat => (fst p <= fst q)%nat /\ (snd p <= snd q)%nat).
Proof.
  intro s.
  destruct (dickson_pair_constructive (fun n => fst (s n)) (fun n => snd (s n)))
    as [i [j [Hij [Hf Hg]]]].
  exists i, j. split; [exact Hij | split; [exact Hf | exact Hg]].
Qed.

(** Dickson's lemma for pairs — the statement under its original name.  Since
    Nov 2026 it is proved by dickson_pair_constructive above, with no classic. *)
Lemma dickson_pair : forall f g : nat -> nat,
  exists i j : nat, (i < j)%nat /\ (f i <= f j)%nat /\ (g i <= g j)%nat.
Proof. exact dickson_pair_constructive. Qed.

(* ================================================================= *)
(* WQO FOR SPECIFIC TYPES                                             *)
(* ================================================================= *)

Lemma wqo_unit : is_wqo (fun _ _ : unit => True).
Proof. intro f. exists 0, 1. split; [lia | exact I]. Qed.

(** false <= anything; true <= true only. *)
Lemma wqo_bool : is_wqo (fun a b : bool => implb a b = true).
Proof.
  intro f.
  destruct (f 0) eqn:E0.
  - destruct (f 1) eqn:E1.
    + exists 0, 1. split; [lia | rewrite E0, E1; reflexivity].
    + exists 1, 2. split; [lia | rewrite E1; reflexivity].
  - exists 0, 1. split; [lia | rewrite E0; reflexivity].
Qed.

(* ================================================================= *)
(* HIGMAN FOR UNIT LISTS (constructive)                                *)
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
  destruct (wqo_nat_le (fun n => length (f n))) as [i [j [Hij Hle]]].
  exists i, j. split; [exact Hij | apply unit_list_embed_by_length; exact Hle].
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

(* Axiom audit: closed under the global context — wqo_nat_le, wqo_unit,
   wqo_bool, higman_unit, dickson_pair, wqo_nat_pair, higman_synthesis. *)
Print Assumptions wqo_nat_le.
Print Assumptions wqo_bool.
Print Assumptions higman_unit.
Print Assumptions dickson_pair.
Print Assumptions higman_synthesis.
