(* ========================================================================= *)
(*                                                                           *)
(*            PROCESS CONTINUUM HYPOTHESIS (Cantor-Bendixson)                *)
(*     Every closed collection of binary processes is either                  *)
(*              enumerable or has a perfect subset.                           *)
(*                                                                           *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)         *)
(*                                                                           *)
(*  E/R/R INTERPRETATION:                                                    *)
(*  =====================                                                    *)
(*    Elements: Binary processes (Cantor space 2^N)                          *)
(*    Roles:    Closed collections, perfect subtrees, paths                  *)
(*    Rules:    Continuum hypothesis dichotomy, Cantor-Bendixson              *)
(*                                                                           *)
(*  STATUS: 41 Qed, 0 Admitted                                              *)
(*  Axioms: classic, constructive_indefinite_description (CID)               *)
(*          (CID for countable_union_enum; EMI derived from classic+CID)     *)
(*  Author: Horsocrates | Date: March 2026                                   *)
(*                                                                           *)
(* ========================================================================= *)

Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Cantor.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.IndefiniteDescription.

(* Derive excluded_middle_informative from classic + CID.
   This avoids importing ClassicalDescription (which adds CDD as a separate axiom).
   The trick: encode the P/~P disjunction as a boolean via CID. *)
Lemma excluded_middle_informative : forall P : Prop, {P} + {~P}.
Proof.
  intro P.
  assert (Hex : exists b : bool, if b then P else ~P).
  { destruct (classic P) as [HP | HnP].
    - exists true. exact HP.
    - exists false. exact HnP. }
  destruct (constructive_indefinite_description _ Hex) as [b Hb].
  destruct b.
  - left. exact Hb.
  - right. exact Hb.
Defined.
Import ListNotations.

From ToS Require Import ProcessTypes.
From ToS Require Import ProcessDiagonal.

(* ========================================================================= *)
(*         PART I: CLOSED COLLECTIONS                                        *)
(* ========================================================================= *)

Definition is_closed (C : BinCollection) : Prop :=
  exists T : PrunedTree, is_tree T /\ forall p, C p <-> is_path T p.

Lemma closed_has_tree : forall C,
  is_closed C ->
  exists T, is_tree T /\ forall p, C p <-> is_path T p.
Proof.
  intros C [T [HT Hiff]]. exists T. split; assumption.
Qed.

(* ========================================================================= *)
(*         PART II: COUNTABLE UNION                                          *)
(* ========================================================================= *)

Lemma countable_union_from_fam :
  forall (fam : nat -> nat -> BinProcess) (F : nat -> BinCollection),
    (forall n p, F n p -> exists m, bp_eq (fam n m) p) ->
    is_enumerable (fun p => exists n, F n p).
Proof.
  intros fam F Hcov.
  exists (fun k => let '(a, b) := Cantor.of_nat k in fam a b).
  intros p [n Hn].
  destruct (Hcov n p Hn) as [m Hm].
  exists (Cantor.to_nat (n, m)).
  rewrite Cantor.cancel_of_to. exact Hm.
Qed.

Lemma countable_union_enum :
  forall (F : nat -> BinCollection),
    (forall n, is_enumerable (F n)) ->
    is_enumerable (fun p => exists n, F n p).
Proof.
  intros F HF.
  assert (Hfam : forall n,
    {f : nat -> BinProcess | forall p, F n p -> exists m, bp_eq (f m) p}).
  { intros n. apply constructive_indefinite_description. exact (HF n). }
  apply (countable_union_from_fam (fun n => proj1_sig (Hfam n)) F).
  intros n p Hn. exact (proj2_sig (Hfam n) p Hn).
Qed.

Lemma enum_add_one : forall (C : BinCollection) (p0 : BinProcess),
  is_enumerable C ->
  is_enumerable (fun p => C p \/ bp_eq p p0).
Proof.
  intros C p0 [f Hf].
  exists (fun n => match n with O => p0 | S k => f k end).
  intros p [Hp | Hp].
  - destruct (Hf p Hp) as [n Hn]. exists (S n). exact Hn.
  - exists 0. apply bp_eq_sym. exact Hp.
Qed.

Lemma not_enum_superset : forall (C D : BinCollection),
  (forall p, C p -> D p) ->
  ~ is_enumerable C ->
  ~ is_enumerable D.
Proof.
  intros C D Hsub HnC HD.
  apply HnC. destruct HD as [f Hf].
  exists f. intros p Hp. apply Hf. apply Hsub. exact Hp.
Qed.

(* ========================================================================= *)
(*         PART III: PATH EXTENSION PROPERTIES                               *)
(* ========================================================================= *)

Lemma extends_prefix_app_cons : forall p sigma (b : bool),
  extends_prefix p (sigma ++ [b]) -> extends_prefix p sigma.
Proof.
  unfold extends_prefix. intros p sigma b Hext k Hk.
  specialize (Hext k). rewrite app_nth1 in Hext by lia.
  apply Hext. rewrite length_app. simpl. lia.
Qed.

Lemma extends_prefix_app_val : forall p sigma (b : bool),
  extends_prefix p (sigma ++ [b]) -> p (length sigma) = b.
Proof.
  unfold extends_prefix. intros p sigma b Hext.
  specialize (Hext (length sigma)).
  rewrite app_nth2 in Hext by lia.
  replace (length sigma - length sigma)%nat with 0%nat in Hext by lia.
  simpl in Hext. apply Hext. rewrite length_app. simpl. lia.
Qed.

Lemma extends_prefix_to_bp_prefix : forall p sigma,
  extends_prefix p sigma ->
  bp_prefix p (length sigma) = sigma.
Proof.
  intros p sigma Hext.
  apply nth_ext with (d := false) (d' := false).
  - rewrite bp_prefix_length. reflexivity.
  - intros i Hi. rewrite bp_prefix_length in Hi.
    rewrite bp_prefix_nth by lia. apply Hext. lia.
Qed.

Lemma paths_extending_parent : forall T sigma b,
  forall p, paths_extending T (sigma ++ [b]) p -> paths_extending T sigma p.
Proof.
  unfold paths_extending. intros T sigma b p [Hp Hext]. split.
  - exact Hp.
  - eapply extends_prefix_app_cons. exact Hext.
Qed.

Lemma paths_split_lr : forall T sigma p,
  is_tree T -> T sigma ->
  paths_extending T sigma p ->
  paths_extending T (sigma ++ [false]) p \/
  paths_extending T (sigma ++ [true]) p.
Proof.
  intros T sigma p HT Hsig [Hpath Hext].
  unfold paths_extending, extends_prefix.
  destruct (p (length sigma)) eqn:Hb.
  - right. split.
    + exact Hpath.
    + intros k Hk. rewrite length_app in Hk. simpl in Hk.
      destruct (Nat.lt_ge_cases k (length sigma)) as [Hlt | Hge].
      * rewrite app_nth1 by lia. apply Hext. lia.
      * assert (k = length sigma) by lia. subst k.
        rewrite app_nth2 by lia.
        replace (length sigma - length sigma)%nat with 0%nat by lia.
        simpl. exact Hb.
  - left. split.
    + exact Hpath.
    + intros k Hk. rewrite length_app in Hk. simpl in Hk.
      destruct (Nat.lt_ge_cases k (length sigma)) as [Hlt | Hge].
      * rewrite app_nth1 by lia. apply Hext. lia.
      * assert (k = length sigma) by lia. subst k.
        rewrite app_nth2 by lia.
        replace (length sigma - length sigma)%nat with 0%nat by lia.
        simpl. exact Hb.
Qed.

Lemma not_enum_paths_child : forall T sigma,
  is_tree T -> T sigma ->
  ~ is_enumerable (paths_extending T sigma) ->
  ~ is_enumerable (paths_extending T (sigma ++ [false])) \/
  ~ is_enumerable (paths_extending T (sigma ++ [true])).
Proof.
  intros T sigma HT Hsig Hne.
  apply not_enum_union.
  intro Henum. apply Hne.
  destruct Henum as [f Hf].
  exists f. intros p Hp. apply Hf. apply paths_split_lr; assumption.
Qed.

Lemma paths_extending_empty_if_not_in_tree : forall T sigma,
  ~ T sigma -> is_enumerable (paths_extending T sigma).
Proof.
  intros T sigma HnT.
  apply enumerable_empty. unfold is_empty, paths_extending.
  intros p [Hpath Hext]. apply HnT.
  assert (Hpref : bp_prefix p (length sigma) = sigma).
  { apply extends_prefix_to_bp_prefix. exact Hext. }
  rewrite <- Hpref. apply Hpath.
Qed.

(* ========================================================================= *)
(*         PART IV: THE PERFECT SUBTREE                                      *)
(* ========================================================================= *)

Definition perf_subtree (T : PrunedTree) : PrunedTree :=
  fun sigma => T sigma /\ ~ is_enumerable (paths_extending T sigma).

Lemma perf_subtree_in_tree : forall T sigma,
  perf_subtree T sigma -> T sigma.
Proof. intros T sigma [HT _]. exact HT. Qed.

Lemma perf_subtree_not_enum : forall T sigma,
  perf_subtree T sigma -> ~ is_enumerable (paths_extending T sigma).
Proof. intros T sigma [_ Hne]. exact Hne. Qed.

Lemma perf_subtree_nonempty : forall T sigma,
  perf_subtree T sigma -> exists p, paths_extending T sigma p.
Proof.
  intros T sigma Hperf.
  apply NNPP. intro Hall.
  apply (perf_subtree_not_enum T sigma Hperf).
  apply enumerable_empty. unfold is_empty.
  intros p Hp. apply Hall. exists p. exact Hp.
Qed.

Lemma perf_subtree_root : forall T,
  is_tree T -> ~ is_enumerable (fun p => is_path T p) ->
  perf_subtree T [].
Proof.
  intros T HT Hne. split.
  - apply tree_root. exact HT.
  - intro Henum. apply Hne.
    destruct Henum as [f Hf].
    exists f. intros p Hp. apply Hf.
    split; [exact Hp | apply extends_prefix_nil].
Qed.

Lemma perf_subtree_prefix_closed : forall T sigma (b : bool),
  is_tree T ->
  perf_subtree T (sigma ++ [b]) -> perf_subtree T sigma.
Proof.
  intros T sigma b HT [Hchild Hne_child]. split.
  - destruct HT as [_ Hpre].
    specialize (Hpre (sigma ++ [b]) Hchild).
    rewrite removelast_last in Hpre. exact Hpre.
  - intro Henum. apply Hne_child.
    destruct Henum as [f Hf].
    exists f. intros p Hp.
    apply Hf. eapply paths_extending_parent. exact Hp.
Qed.

Lemma perf_subtree_has_child : forall T sigma,
  is_tree T ->
  perf_subtree T sigma ->
  perf_subtree T (sigma ++ [false]) \/ perf_subtree T (sigma ++ [true]).
Proof.
  intros T sigma HT [Hsig Hne].
  destruct (not_enum_paths_child T sigma HT Hsig Hne) as [Hnf | Hnt].
  - left. split.
    + destruct (classic (T (sigma ++ [false]))) as [HT' | HnT'].
      * exact HT'.
      * exfalso. apply Hnf. apply paths_extending_empty_if_not_in_tree. exact HnT'.
    + exact Hnf.
  - right. split.
    + destruct (classic (T (sigma ++ [true]))) as [HT' | HnT'].
      * exact HT'.
      * exfalso. apply Hnt. apply paths_extending_empty_if_not_in_tree. exact HnT'.
    + exact Hnt.
Qed.

(* ========================================================================= *)
(*         PART V: CHAIN CONSTRUCTION                                        *)
(* ========================================================================= *)

Definition pick_dir (T : PrunedTree) (sigma : list bool) : bool :=
  if excluded_middle_informative (perf_subtree T (sigma ++ [false]))
  then false
  else true.

Fixpoint chain (T : PrunedTree) (sigma : list bool) (n : nat) : list bool :=
  match n with
  | O => sigma
  | S k => chain T sigma k ++ [pick_dir T (chain T sigma k)]
  end.

Lemma chain_length : forall T sigma n,
  length (chain T sigma n) = (length sigma + n)%nat.
Proof.
  intros T sigma n. revert sigma. induction n as [|n IH]; intros sigma.
  - simpl. lia.
  - simpl. rewrite length_app. simpl. rewrite IH. lia.
Qed.

Lemma chain_in_perf : forall T sigma,
  is_tree T ->
  perf_subtree T sigma ->
  (forall n, ~ (perf_subtree T (chain T sigma n ++ [false]) /\
                perf_subtree T (chain T sigma n ++ [true]))) ->
  forall n, perf_subtree T (chain T sigma n).
Proof.
  intros T sigma HT Hperf Hnosplit n.
  induction n as [|n IH].
  - simpl. exact Hperf.
  - simpl. unfold pick_dir.
    destruct (excluded_middle_informative (perf_subtree T (chain T sigma n ++ [false])))
      as [Hf | Hnf].
    + exact Hf.
    + destruct (perf_subtree_has_child T (chain T sigma n) HT IH) as [Hf2 | Ht2].
      * contradiction.
      * exact Ht2.
Qed.

Lemma chain_other_enum : forall T sigma,
  is_tree T ->
  perf_subtree T sigma ->
  (forall n, ~ (perf_subtree T (chain T sigma n ++ [false]) /\
                perf_subtree T (chain T sigma n ++ [true]))) ->
  forall n, is_enumerable
    (paths_extending T (chain T sigma n ++ [negb (pick_dir T (chain T sigma n))])).
Proof.
  intros T sigma HT Hperf Hnosplit n.
  assert (Hn : perf_subtree T (chain T sigma n)).
  { apply chain_in_perf; assumption. }
  set (s := chain T sigma n) in *.
  unfold pick_dir.
  destruct (excluded_middle_informative (perf_subtree T (s ++ [false]))) as [Hf | Hnf].
  + destruct (classic (perf_subtree T (s ++ [true]))) as [Ht | Hnt].
    * exfalso. apply (Hnosplit n). split; assumption.
    * destruct (classic (T (s ++ [true]))) as [Hin | Hnin].
      -- apply NNPP. intro Habs. apply Hnt. split; assumption.
      -- apply paths_extending_empty_if_not_in_tree. exact Hnin.
  + destruct (classic (perf_subtree T (s ++ [false]))) as [Hf2 | Hnf2].
    * contradiction.
    * destruct (classic (T (s ++ [false]))) as [Hin | Hnin].
      -- apply NNPP. intro Habs. apply Hnf2. split; assumption.
      -- apply paths_extending_empty_if_not_in_tree. exact Hnin.
Qed.

Lemma chain_nth_sigma : forall T sigma n i,
  (i < length sigma)%nat ->
  nth i (chain T sigma n) false = nth i sigma false.
Proof.
  intros T sigma n. revert sigma. induction n as [|n IH]; intros sigma i Hi.
  - simpl. reflexivity.
  - simpl. rewrite app_nth1 by (rewrite chain_length; lia). apply IH. lia.
Qed.

Lemma chain_nth_pick : forall T sigma n j,
  (j < n)%nat ->
  nth (length sigma + j) (chain T sigma n) false = pick_dir T (chain T sigma j).
Proof.
  intros T sigma n. induction n as [|n IH]; intros j Hj.
  - lia.
  - simpl. destruct (Nat.eq_dec j n) as [-> | Hne].
    + rewrite app_nth2 by (rewrite chain_length; lia).
      rewrite chain_length.
      replace (length sigma + n - (length sigma + n))%nat with 0%nat by lia.
      simpl. reflexivity.
    + rewrite app_nth1 by (rewrite chain_length; lia).
      apply IH. lia.
Qed.

(* ========================================================================= *)
(*         PART VI: NO-SPLITTING IMPLIES ENUMERABLE                          *)
(* ========================================================================= *)

(** The chain-following process: determined by sigma and the chain directions. *)
Definition chain_process (T : PrunedTree) (sigma : list bool) : BinProcess :=
  fun n =>
    if lt_dec n (length sigma) then
      nth n sigma false
    else
      pick_dir T (chain T sigma (n - length sigma)).

(** Two paths extending sigma that both follow the chain are equal. *)
Lemma chain_followers_eq : forall T sigma p q,
  extends_prefix p sigma ->
  extends_prefix q sigma ->
  (forall k, p (length sigma + k) = pick_dir T (chain T sigma k)) ->
  (forall k, q (length sigma + k) = pick_dir T (chain T sigma k)) ->
  bp_eq p q.
Proof.
  intros T sigma p q Hep Heq Hfp Hfq.
  unfold bp_eq. intro n.
  destruct (Nat.lt_ge_cases n (length sigma)) as [Hlt | Hge].
  - transitivity (nth n sigma false).
    + apply Hep. lia.
    + symmetry. apply Heq. lia.
  - replace n with (length sigma + (n - length sigma))%nat by lia.
    rewrite Hfp, Hfq. reflexivity.
Qed.

(** Any path extending sigma that follows the chain is bp_eq to chain_process. *)
Lemma follows_chain_eq : forall T sigma p,
  extends_prefix p sigma ->
  (forall k, p (length sigma + k) = pick_dir T (chain T sigma k)) ->
  bp_eq (chain_process T sigma) p.
Proof.
  intros T sigma p Hext Hfollow.
  unfold bp_eq, chain_process. intro n.
  destruct (lt_dec n (length sigma)) as [Hlt | Hnlt].
  - symmetry. apply Hext. lia.
  - assert (Hge : (n >= length sigma)%nat) by lia.
    set (k := (n - length sigma)%nat).
    assert (Hk : n = (length sigma + k)%nat) by lia.
    rewrite Hk. rewrite Hfollow. reflexivity.
Qed.

(** Core classification of paths. *)
Lemma path_classification : forall T sigma p,
  is_tree T ->
  perf_subtree T sigma ->
  (forall n, ~ (perf_subtree T (chain T sigma n ++ [false]) /\
                perf_subtree T (chain T sigma n ++ [true]))) ->
  paths_extending T sigma p ->
  (forall k, p (length sigma + k) = pick_dir T (chain T sigma k)) \/
  exists k, paths_extending T (chain T sigma k ++ [negb (pick_dir T (chain T sigma k))]) p.
Proof.
  intros T sigma p HT Hperf Hnosplit [Hpath Hext].
  destruct (classic (forall k, p (length sigma + k) = pick_dir T (chain T sigma k)))
    as [Hall | Hnall].
  - left. exact Hall.
  - right.
    assert (Hex : exists k, p (length sigma + k) <> pick_dir T (chain T sigma k)).
    { apply NNPP. intro H. apply Hnall.
      intro k. apply NNPP. intro Hk. apply H. exists k. exact Hk. }
    assert (Hmin : exists k, p (length sigma + k) <> pick_dir T (chain T sigma k) /\
                   forall j, (j < k)%nat -> p (length sigma + j) = pick_dir T (chain T sigma j)).
    { destruct Hex as [k0 Hk0].
      induction k0 as [k0 IH] using (well_founded_ind lt_wf).
      destruct (classic (forall j, (j < k0)%nat ->
                p (length sigma + j) = pick_dir T (chain T sigma j))) as [Hall2 | Hnall2].
      - exists k0. split; assumption.
      - assert (Hex2 : exists j, (j < k0)%nat /\ p (length sigma + j) <> pick_dir T (chain T sigma j)).
        { apply NNPP. intro H. apply Hnall2. intros j Hj.
          apply NNPP. intro Hj2. apply H. exists j. split; assumption. }
        destruct Hex2 as [j [Hj Hdj]].
        apply (IH j Hj Hdj). }
    destruct Hmin as [k [Hkdiff Hkmin]].
    exists k.
    unfold paths_extending. split.
    + exact Hpath.
    + unfold extends_prefix. intros i Hi.
      rewrite length_app in Hi. simpl in Hi.
      rewrite chain_length in Hi.
      destruct (Nat.lt_ge_cases i (length sigma)) as [Hlt | Hge].
      * rewrite app_nth1 by (rewrite chain_length; lia).
        rewrite chain_nth_sigma by lia. apply Hext. lia.
      * destruct (Nat.eq_dec i (length sigma + k)) as [Heqi | Hneqi].
        -- subst i.
           rewrite app_nth2 by (rewrite chain_length; lia).
           rewrite chain_length.
           replace (length sigma + k - (length sigma + k))%nat with 0%nat by lia.
           simpl.
           destruct (p (length sigma + k)) eqn:Hpk, (pick_dir T (chain T sigma k)) eqn:Hdk;
             simpl; try reflexivity; exfalso; apply Hkdiff; congruence.
        -- assert (Hi2 : (i < length sigma + k)%nat) by lia.
           set (j := (i - length sigma)%nat).
           assert (Hj : (j < k)%nat) by lia.
           assert (Heqi : i = (length sigma + j)%nat) by lia.
           rewrite app_nth1 by (rewrite chain_length; lia).
           rewrite Heqi.
           rewrite chain_nth_pick by lia.
           apply Hkmin. lia.
Qed.

(** The key lemma: if no both-children splitting, paths are enumerable. *)
Lemma no_split_implies_enum : forall T sigma,
  is_tree T ->
  perf_subtree T sigma ->
  (forall n, ~ (perf_subtree T (chain T sigma n ++ [false]) /\
                perf_subtree T (chain T sigma n ++ [true]))) ->
  is_enumerable (paths_extending T sigma).
Proof.
  intros T sigma HT Hperf Hnosplit.
  set (Fn := fun n => paths_extending T
    (chain T sigma n ++ [negb (pick_dir T (chain T sigma n))])).
  assert (HFn : forall n, is_enumerable (Fn n)).
  { intro n. apply chain_other_enum; assumption. }
  assert (Hunion : is_enumerable (fun p => exists n, Fn n p)).
  { apply countable_union_enum. exact HFn. }
  (* Enumeration = chain_process at 0 + union at S k *)
  set (cp := chain_process T sigma).
  destruct Hunion as [g Hg].
  exists (fun n => match n with O => cp | S k => g k end).
  intros p Hp.
  destruct (path_classification T sigma p HT Hperf Hnosplit Hp) as [Hfollow | [k Hk]].
  - (* p follows the chain => bp_eq to cp *)
    exists 0. apply follows_chain_eq.
    + destruct Hp as [_ Hext]. exact Hext.
    + exact Hfollow.
  - (* p diverges at step k => in Fn k *)
    assert (Hex : exists n, Fn n p) by (exists k; exact Hk).
    destruct (Hg p Hex) as [m Hm].
    exists (S m). exact Hm.
Qed.

(* ========================================================================= *)
(*         PART VII: SPLITTING ARGUMENT                                      *)
(* ========================================================================= *)

(** chain T sigma n starts with sigma. *)
Lemma chain_starts_with_sigma : forall T sigma n,
  firstn (length sigma) (chain T sigma n) = sigma.
Proof.
  intros T sigma n. revert sigma. induction n as [|n IH]; intros sigma.
  - simpl. rewrite firstn_all. reflexivity.
  - simpl. rewrite firstn_app.
    rewrite chain_length.
    replace (length sigma - (length sigma + n))%nat with 0%nat by lia.
    simpl. rewrite app_nil_r. apply IH.
Qed.

(** Recovering chain T sigma n = sigma ++ suffix. *)
Lemma chain_is_sigma_app : forall T sigma n,
  chain T sigma n = sigma ++ skipn (length sigma) (chain T sigma n).
Proof.
  intros T sigma n.
  rewrite <- (firstn_skipn (length sigma) (chain T sigma n)) at 1.
  rewrite chain_starts_with_sigma. reflexivity.
Qed.

Lemma perf_subtree_has_splitting : forall T sigma,
  is_tree T ->
  perf_subtree T sigma ->
  exists tau, perf_subtree T (sigma ++ tau) /\
              is_splitting (perf_subtree T) (sigma ++ tau).
Proof.
  intros T sigma HT Hperf.
  destruct (classic (exists tau, perf_subtree T (sigma ++ tau) /\
              perf_subtree T (sigma ++ tau ++ [false]) /\
              perf_subtree T (sigma ++ tau ++ [true]))) as [Hex | Hnex].
  - destruct Hex as [tau [Htau [Hf Ht]]].
    exists tau. split.
    + exact Htau.
    + unfold is_splitting, has_left, has_right.
      rewrite <- app_assoc. rewrite <- app_assoc. split; assumption.
  - exfalso.
    assert (Hnosplit : forall n, ~ (perf_subtree T (chain T sigma n ++ [false]) /\
                                    perf_subtree T (chain T sigma n ++ [true]))).
    { intros n Hboth. apply Hnex.
      set (tau := skipn (length sigma) (chain T sigma n)).
      exists tau.
      assert (Hrewrite : chain T sigma n = sigma ++ tau).
      { apply chain_is_sigma_app. }
      destruct Hboth as [Hf Ht].
      rewrite Hrewrite in Hf, Ht.
      rewrite <- app_assoc in Hf. rewrite <- app_assoc in Ht.
      assert (Hnode : perf_subtree T (sigma ++ tau)).
      { assert (Hf' : perf_subtree T ((sigma ++ tau) ++ [false])).
        { rewrite <- app_assoc. exact Hf. }
        eapply perf_subtree_prefix_closed. exact HT. exact Hf'. }
      split; [exact Hnode | split; [exact Hf | exact Ht] ]. }
    apply (perf_subtree_not_enum T sigma Hperf).
    apply no_split_implies_enum; assumption.
Qed.

(* ========================================================================= *)
(*         PART VIII: PERF_SUBTREE IS PERFECT                                *)
(* ========================================================================= *)

Lemma perf_subtree_is_tree : forall T,
  is_tree T -> ~ is_enumerable (fun p => is_path T p) ->
  is_tree (perf_subtree T).
Proof.
  intros T HT Hne. split.
  - apply perf_subtree_root; assumption.
  - intros sigma Hsig.
    destruct sigma as [| b sigma'] using rev_ind.
    + simpl. apply perf_subtree_root; assumption.
    + rewrite removelast_last.
      eapply perf_subtree_prefix_closed; [exact HT | exact Hsig].
Qed.

Lemma perf_subtree_is_perfect : forall T,
  is_tree T -> ~ is_enumerable (fun p => is_path T p) ->
  is_perfect (perf_subtree T).
Proof.
  intros T HT Hne. split.
  - apply perf_subtree_is_tree; assumption.
  - intros sigma Hsig.
    destruct (perf_subtree_has_splitting T sigma HT Hsig) as [tau [Htau Hsplit]].
    exists tau. split.
    + exact Htau.
    + exact Hsplit.
Qed.

(* ========================================================================= *)
(*         PART IX: PATHS IN PERF_SUBTREE                                    *)
(* ========================================================================= *)

Lemma perf_path_is_T_path : forall T p,
  is_path (perf_subtree T) p -> is_path T p.
Proof.
  unfold is_path. intros T p Hp n.
  apply perf_subtree_in_tree. apply Hp.
Qed.

(* ========================================================================= *)
(*         PART X: MAIN THEOREMS                                             *)
(* ========================================================================= *)

Theorem not_enum_has_perfect_subset : forall T,
  is_tree T -> ~ is_enumerable (fun p => is_path T p) ->
  has_perfect_subset (fun p => is_path T p).
Proof.
  intros T HT Hne.
  exists (perf_subtree T). split.
  - apply perf_subtree_is_perfect; assumption.
  - intros p Hp. apply perf_path_is_T_path. exact Hp.
Qed.

Theorem process_continuum_hypothesis :
  forall C : BinCollection,
    is_closed C ->
    is_enumerable C \/ has_perfect_subset C.
Proof.
  intros C [T [HT Hiff]].
  destruct (classic (is_enumerable C)) as [Henum | Hnenum].
  - left. exact Henum.
  - right.
    assert (Hne : ~ is_enumerable (fun p => is_path T p)).
    { intro Henum. apply Hnenum.
      destruct Henum as [f Hf].
      exists f. intros p Hp. apply Hf. apply Hiff. exact Hp. }
    destruct (not_enum_has_perfect_subset T HT Hne) as [S [Hperf HS]].
    exists S. split.
    + exact Hperf.
    + intros p Hp. apply Hiff. apply HS. exact Hp.
Qed.

Theorem no_intermediate_process_type :
  forall C : BinCollection,
    is_closed C ->
    is_enumerable C \/ has_perfect_subset C.
Proof. exact process_continuum_hypothesis. Qed.

Theorem PCH_structural_dichotomy :
  forall C : BinCollection,
    is_closed C ->
    ~ is_enumerable C ->
    has_perfect_subset C.
Proof.
  intros C Hclosed Hnenum.
  destruct (process_continuum_hypothesis C Hclosed) as [Henum | Hperf].
  - contradiction.
  - exact Hperf.
Qed.

(* ========================================================================= *)
(*         PART XI: ADDITIONAL RESULTS                                       *)
(* ========================================================================= *)

Lemma full_not_enum_restated : ~ is_enumerable (fun _ : BinProcess => True).
Proof. exact full_collection_not_enumerable. Qed.

Lemma full_collection_closed : is_closed (fun _ : BinProcess => True).
Proof.
  exists (fun _ : list bool => True). split.
  - split; [exact I | intros; exact I].
  - intros p. split.
    + intros _. unfold is_path. intros n. exact I.
    + intros _. exact I.
Qed.

Theorem full_has_perfect : has_perfect_subset (fun _ : BinProcess => True).
Proof.
  apply PCH_structural_dichotomy.
  - exact full_collection_closed.
  - exact full_not_enum_restated.
Qed.

Lemma empty_closed_enum : is_closed (fun _ => False) /\ is_enumerable (fun _ => False).
Proof.
  split.
  - exists (fun sigma => sigma = []). split.
    + split.
      * reflexivity.
      * intros sigma Hsig. subst. simpl. reflexivity.
    + intros p. split.
      * intro Habs. contradiction.
      * intro Hpath. unfold is_path in Hpath.
        specialize (Hpath 1). simpl in Hpath. discriminate.
  - apply enumerable_empty. unfold is_empty. intros p Hp. exact Hp.
Qed.

(* ========================================================================= *)
(*         SUMMARY AND AXIOM CHECK                                           *)
(* ========================================================================= *)

Print Assumptions process_continuum_hypothesis.

(* ========================================================================= *)
(*                                                                           *)
(*  PROVEN (41 Qed, 0 Admitted):                                             *)
(*                                                                           *)
(*  Part I   - Closed collections (1):                                       *)
(*    closed_has_tree                                                        *)
(*                                                                           *)
(*  Part II  - Countable union (4):                                          *)
(*    countable_union_from_fam, countable_union_enum,                        *)
(*    enum_add_one, not_enum_superset                                        *)
(*                                                                           *)
(*  Part III - Path extension properties (7):                                *)
(*    extends_prefix_app_cons, extends_prefix_app_val,                       *)
(*    extends_prefix_to_bp_prefix, paths_extending_parent,                   *)
(*    paths_split_lr, not_enum_paths_child,                                  *)
(*    paths_extending_empty_if_not_in_tree                                   *)
(*                                                                           *)
(*  Part IV  - Perfect subtree (6):                                          *)
(*    perf_subtree_in_tree, perf_subtree_not_enum,                           *)
(*    perf_subtree_nonempty, perf_subtree_root,                              *)
(*    perf_subtree_prefix_closed, perf_subtree_has_child                     *)
(*                                                                           *)
(*  Part V   - Chain construction (5):                                       *)
(*    chain_length, chain_in_perf, chain_other_enum,                         *)
(*    chain_nth_sigma, chain_nth_pick                                        *)
(*                                                                           *)
(*  Part VI  - No-splitting implies enumerable (4):                          *)
(*    chain_followers_eq, follows_chain_eq,                                  *)
(*    path_classification, no_split_implies_enum                             *)
(*                                                                           *)
(*  Part VII - Splitting argument (3):                                       *)
(*    chain_starts_with_sigma, chain_is_sigma_app,                           *)
(*    perf_subtree_has_splitting                                             *)
(*                                                                           *)
(*  Part VIII - perf_subtree is perfect (2):                                 *)
(*    perf_subtree_is_tree, perf_subtree_is_perfect                          *)
(*                                                                           *)
(*  Part IX  - Paths (1):                                                    *)
(*    perf_path_is_T_path                                                    *)
(*                                                                           *)
(*  Part X   - Main theorems (4):                                            *)
(*    not_enum_has_perfect_subset, process_continuum_hypothesis,             *)
(*    no_intermediate_process_type, PCH_structural_dichotomy                 *)
(*                                                                           *)
(*  Part XI  - Additional (4):                                               *)
(*    full_not_enum_restated, full_collection_closed,                        *)
(*    full_has_perfect, empty_closed_enum                                    *)
(*                                                                           *)
(* ========================================================================= *)
