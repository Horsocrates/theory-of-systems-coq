(* TMap: Key-Value Map as ToS System *)
(* STATUS: 31 Qed, 0 Admitted, 0 axioms *)
(* Author: Horsocrates | Date: 2026 *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import L5Resolution.
From ToS Require Import InductiveSystems.
From ToS Require Import ConstitutionChecking.

Section Sorted.
  Context {A : Type} `{DTO : DecTotalOrder A}.

  Inductive Sorted : list A -> Prop :=
    | Sorted_nil : Sorted []
    | Sorted_one : forall x, Sorted [x]
    | Sorted_cons : forall x y l,
        dto_le x y -> Sorted (y :: l) -> Sorted (x :: y :: l).

  Lemma Sorted_inv_le : forall x y l,
    Sorted (x :: y :: l) -> dto_le x y.
  Proof. intros x y l H. inversion H; subst. assumption. Qed.

  Lemma Sorted_inv_tail : forall x y l,
    Sorted (x :: y :: l) -> Sorted (y :: l).
  Proof. intros x y l H. inversion H; subst. assumption. Qed.

  Lemma Sorted_inv_cons : forall x l,
    Sorted (x :: l) -> Sorted l.
  Proof.
    intros x l H. destruct l as [| y l'].
    - constructor.
    - inversion H; subst. assumption.
  Qed.

  Lemma Sorted_head_le_all : forall x l,
    Sorted (x :: l) -> forall y, In y l -> dto_le x y.
  Proof.
    intros x l. revert x. induction l as [| z l' IH]; intros x Hs y Hy.
    - destruct Hy.
    - destruct Hy as [Heq | Hin].
      + subst z. apply Sorted_inv_le in Hs. exact Hs.
      + pose proof (Sorted_inv_le _ _ _ Hs) as Hle.
        pose proof (Sorted_inv_cons _ _ Hs) as Htail.
        specialize (IH z Htail y Hin).
        eapply dto_le_trans; eauto.
  Qed.
End Sorted.

Arguments Sorted {A} {DTO}.
Arguments Sorted_nil {A} {DTO}.
Arguments Sorted_one {A} {DTO}.
Arguments Sorted_cons {A} {DTO}.

Section MapOps.
  Context {K V : Type} `{DTO : DecTotalOrder K}.

  Definition key_eq_dec (k1 k2 : K) : {k1 = k2} + {k1 <> k2}.
  Proof.
    destruct (dto_le_dec k1 k2); destruct (dto_le_dec k2 k1).
    - left. apply dto_le_antisym; assumption.
    - right. intro Heq. subst. apply n. apply dto_le_refl.
    - right. intro Heq. subst. apply n. apply dto_le_refl.
    - right. intro Heq. subst. apply n. apply dto_le_refl.
  Defined.

  Definition entry := (K * V)%type.
  Definition tm_empty : list entry := [].

  Fixpoint tm_lookup (k : K) (m : list entry) : option V :=
    match m with
    | [] => None
    | (k', v') :: rest =>
        if key_eq_dec k k' then Some v' else tm_lookup k rest
    end.

  Definition tm_mem (k : K) (m : list entry) : bool :=
    match tm_lookup k m with Some _ => true | None => false end.

  Definition tm_size (m : list entry) : nat := length m.
  Definition tm_keys (m : list entry) : list K := map fst m.

  Fixpoint tm_insert (k : K) (v : V) (m : list entry) : list entry :=
    match m with
    | [] => [(k, v)]
    | (k', v') :: rest =>
        if key_eq_dec k k' then (k, v) :: rest
        else if dto_le_dec k k' then (k, v) :: (k', v') :: rest
        else (k', v') :: tm_insert k v rest
    end.

  Fixpoint tm_remove (k : K) (m : list entry) : list entry :=
    match m with
    | [] => []
    | (k', v') :: rest =>
        if key_eq_dec k k' then rest
        else (k', v') :: tm_remove k rest
    end.

  Lemma tm_lookup_empty : forall k, tm_lookup k tm_empty = None.
  Proof. intros k. reflexivity. Qed.

  Lemma tm_size_empty : tm_size tm_empty = 0.
  Proof. reflexivity. Qed.

  Lemma tm_keys_empty : tm_keys tm_empty = [].
  Proof. reflexivity. Qed.

  Lemma tm_mem_empty : forall k, tm_mem k tm_empty = false.
  Proof. intros k. reflexivity. Qed.

  Lemma tm_remove_empty : forall k, tm_remove k tm_empty = tm_empty.
  Proof. intros k. reflexivity. Qed.

  Lemma tm_lookup_insert_eq : forall k v m,
    tm_lookup k (tm_insert k v m) = Some v.
  Proof.
    intros k v m. induction m as [| [k' v'] rest IH].
    - simpl. destruct (key_eq_dec k k) as [_ | Hne].
      + reflexivity.
      + exfalso. apply Hne. reflexivity.
    - simpl. destruct (key_eq_dec k k') as [Heq | Hne].
      + simpl. destruct (key_eq_dec k k) as [_ | Hne2].
        * reflexivity.
        * exfalso. apply Hne2. reflexivity.
      + destruct (dto_le_dec k k') as [Hle | Hnle].
        * simpl. destruct (key_eq_dec k k) as [_ | Hne2].
          -- reflexivity.
          -- exfalso. apply Hne2. reflexivity.
        * simpl. destruct (key_eq_dec k k') as [Heq2 | _].
          -- exfalso. apply Hne. exact Heq2.
          -- exact IH.
  Qed.

  Lemma tm_lookup_insert_neq : forall k1 k2 v m,
    k1 <> k2 -> tm_lookup k1 (tm_insert k2 v m) = tm_lookup k1 m.
  Proof.
    intros k1 k2 v m Hne. induction m as [| [k' v'] rest IH].
    - simpl. destruct (key_eq_dec k1 k2) as [Heq | _].
      + exfalso. apply Hne. exact Heq.
      + reflexivity.
    - simpl.
      destruct (key_eq_dec k2 k') as [Heq2 | Hne2].
      + simpl. destruct (key_eq_dec k1 k2) as [Heq12 | _].
        * exfalso. apply Hne. exact Heq12.
        * destruct (key_eq_dec k1 k') as [Heq1k | _].
          -- rewrite Heq1k in Hne. exfalso. apply Hne. symmetry. exact Heq2.
          -- reflexivity.
      + destruct (dto_le_dec k2 k') as [Hle | Hnle].
        * simpl. destruct (key_eq_dec k1 k2) as [Heq12 | _].
          -- exfalso. apply Hne. exact Heq12.
          -- reflexivity.
        * simpl. destruct (key_eq_dec k1 k') as [Heq1k | _].
          -- reflexivity.
          -- exact IH.
  Qed.

  Lemma lookup_not_in : forall k (m : list (K * V)),
    ~ In k (tm_keys m) -> tm_lookup k m = None.
  Proof.
    intros k m. induction m as [| [k1 v1] rest IH]; intro Hni.
    - reflexivity.
    - simpl. destruct (key_eq_dec k k1) as [Heq | Hne].
      + exfalso. apply Hni. simpl. left. symmetry. exact Heq.
      + apply IH. intro Hin. apply Hni. simpl. right. exact Hin.
  Qed.

  Lemma tm_lookup_remove_eq : forall k m,
    NoDup (tm_keys m) ->
    tm_lookup k (tm_remove k m) = None.
  Proof.
    intros k m Hnd. induction m as [| [k1 v1] rest IH].
    - reflexivity.
    - simpl. destruct (key_eq_dec k k1) as [Heq | Hne].
      + subst k1. apply lookup_not_in.
        simpl in Hnd. inversion Hnd; subst. assumption.
      + simpl. destruct (key_eq_dec k k1) as [Heq | _].
        * exfalso. apply Hne. exact Heq.
        * apply IH. simpl in Hnd. inversion Hnd; subst. assumption.
  Qed.

  Lemma tm_mem_true_iff : forall k m,
    tm_mem k m = true <-> exists v, tm_lookup k m = Some v.
  Proof.
    intros k m. unfold tm_mem. split.
    - intro H. destruct (tm_lookup k m) as [v |].
      + exists v. reflexivity.
      + discriminate.
    - intros [v Hv]. rewrite Hv. reflexivity.
  Qed.

  Lemma tm_mem_false_iff : forall k m,
    tm_mem k m = false <-> tm_lookup k m = None.
  Proof.
    intros k m. unfold tm_mem. split.
    - intro H. destruct (tm_lookup k m) as [v |].
      + discriminate.
      + reflexivity.
    - intro H. rewrite H. reflexivity.
  Qed.

  Lemma tm_sorted_empty : Sorted (tm_keys tm_empty).
  Proof. simpl. constructor. Qed.

  Lemma tm_nodup_empty : NoDup (tm_keys tm_empty).
  Proof. simpl. constructor. Qed.

  Lemma tm_insert_sorted : forall k v m,
    Sorted (tm_keys m) ->
    NoDup (tm_keys m) ->
    Sorted (tm_keys (tm_insert k v m)).
  Proof.
    intros k v m. induction m as [| [k' v'] rest IH]; intros Hs Hnd.
    - simpl. constructor.
    - simpl.
      destruct (key_eq_dec k k') as [Heq | Hne].
      + subst k'. simpl. simpl in Hs.
        destruct rest as [| [k2 v2] rest2].
        * constructor.
        * constructor.
          -- apply Sorted_inv_le in Hs. exact Hs.
          -- apply Sorted_inv_tail in Hs. exact Hs.
      + destruct (dto_le_dec k k') as [Hle | Hnle].
        * simpl. constructor; [exact Hle | simpl in Hs; exact Hs].
        * simpl. simpl in Hs. simpl in Hnd.
          assert (Htail_s : Sorted (tm_keys rest)).
          { apply Sorted_inv_cons in Hs. exact Hs. }
          assert (Htail_nd : NoDup (tm_keys rest)).
          { inversion Hnd; subst. assumption. }
          specialize (IH Htail_s Htail_nd).
          destruct rest as [| [k2 v2] rest2].
          -- simpl in *. constructor.
             ++ destruct (dto_le_total k' k) as [Hle2 | Hle2].
                ** exact Hle2.
                ** exfalso. apply Hnle. exact Hle2.
             ++ constructor.
          -- simpl in *.
             destruct (key_eq_dec k k2) as [Heqk2 | Hnek2].
             ++ subst k2. constructor.
                ** destruct (dto_le_total k' k) as [H1 | H1].
                   --- exact H1.
                   --- exfalso. apply Hnle. exact H1.
                ** exact IH.
             ++ destruct (dto_le_dec k k2) as [Hlek2 | Hnlek2].
                ** constructor.
                   --- destruct (dto_le_total k' k) as [H1 | H1].
                       +++ exact H1.
                       +++ exfalso. apply Hnle. exact H1.
                   --- exact IH.
                ** constructor.
                   --- apply Sorted_inv_le in Hs. exact Hs.
                   --- exact IH.
  Qed.

  Lemma tm_insert_nodup : forall k v m,
    Sorted (tm_keys m) ->
    NoDup (tm_keys m) ->
    NoDup (tm_keys (tm_insert k v m)).
  Proof.
    intros k v m. induction m as [| [k' v'] rest IH]; intros Hs Hnd.
    - simpl. constructor; [intro H; destruct H | constructor].
    - simpl. destruct (key_eq_dec k k') as [Heq | Hne].
      + subst k'. simpl. simpl in Hnd.
        inversion Hnd; subst. constructor; assumption.
      + destruct (dto_le_dec k k') as [Hle | Hnle].
        * simpl. simpl in Hnd. inversion Hnd; subst.
          constructor.
          -- simpl. intro Hin. destruct Hin as [Heq2 | Hin2].
             ++ apply Hne. symmetry. exact Heq2.
             ++ assert (dto_le k' k).
                { apply Sorted_head_le_all with (l := tm_keys rest); assumption. }
                apply Hne. apply dto_le_antisym; assumption.
          -- constructor; assumption.
        * simpl. simpl in Hnd. simpl in Hs.
          inversion Hnd; subst.
          assert (Htail_s : Sorted (tm_keys rest)) by (apply Sorted_inv_cons in Hs; exact Hs).
          constructor.
          -- intro Hin.
             assert (Hfact : forall kx vx l,
               In kx (tm_keys (tm_insert k vx l)) -> kx = k \/ In kx (tm_keys l)).
             { clear. intros kx vx l. induction l as [| [ka va] la IHa].
               - simpl. intros [Heq | F]. left; auto. destruct F.
               - simpl. destruct (key_eq_dec k ka) as [Heka | Hnka].
                 + simpl. intros [Heq | Hin2]. left; auto. right. simpl. right; auto.
                 + destruct (dto_le_dec k ka) as [Hleka | _].
                   * simpl. intros [Heq | [Heq2 | Hin2]].
                     left; auto. right; simpl; left; auto. right; simpl; right; auto.
                   * simpl. intros [Heq | Hin2].
                     right. simpl. left; auto.
                     destruct (IHa Hin2) as [Hl | Hr].
                     left; auto. right. simpl. right; auto.
             }
             destruct (Hfact k' v rest Hin) as [Heqk' | Hin2].
             ++ apply Hne. symmetry. exact Heqk'.
             ++ apply H1. exact Hin2.
          -- apply IH; assumption.
  Qed.

  Lemma tm_remove_In_keys : forall k k0 m,
    In k0 (tm_keys (tm_remove k m)) -> In k0 (tm_keys m).
  Proof.
    intros k k0 m. induction m as [| [k1 v1] rest IH].
    - simpl. auto.
    - simpl. destruct (key_eq_dec k k1).
      + intro H. right. exact H.
      + simpl. intros [Heq | Hin].
        * left. exact Heq.
        * right. apply IH. exact Hin.
  Qed.

  Lemma tm_remove_sorted : forall k m,
    Sorted (tm_keys m) -> Sorted (tm_keys (tm_remove k m)).
  Proof.
    intros k m Hs. induction m as [| [k1 v1] rest IH].
    - simpl. constructor.
    - simpl. destruct (key_eq_dec k k1) as [Heq | Hne].
      + apply Sorted_inv_cons in Hs. exact Hs.
      + simpl. simpl in Hs.
        assert (Htail : Sorted (tm_keys rest)).
        { apply Sorted_inv_cons in Hs. exact Hs. }
        specialize (IH Htail).
        destruct (tm_keys (tm_remove k rest)) as [| c rest_keys] eqn:Heqr.
        * constructor.
        * constructor.
          -- assert (Hinc : In c (tm_keys rest)).
             { apply tm_remove_In_keys with (k := k).
               rewrite Heqr. left. reflexivity. }
             apply Sorted_head_le_all with (l := tm_keys rest).
             exact Hs. exact Hinc.
          -- exact IH.
  Qed.

  Lemma tm_remove_nodup : forall k m,
    NoDup (tm_keys m) -> NoDup (tm_keys (tm_remove k m)).
  Proof.
    intros k m Hnd. induction m as [| [k1 v1] rest IH].
    - simpl. constructor.
    - simpl. simpl in Hnd. inversion Hnd as [| a l Hnotin Hnd_rest]; subst.
      destruct (key_eq_dec k k1) as [Heq | Hne].
      + exact Hnd_rest.
      + simpl. constructor.
        * intro Hin. apply Hnotin.
          apply tm_remove_In_keys with (k := k). exact Hin.
        * apply IH. exact Hnd_rest.
  Qed.

  Lemma tm_size_insert_le : forall k v m,
    tm_size (tm_insert k v m) <= tm_size m + 1.
  Proof.
    intros k v m. induction m as [| [k' v'] rest IH].
    - simpl. lia.
    - simpl. destruct (key_eq_dec k k') as [Heq | Hne].
      + simpl. lia.
      + destruct (dto_le_dec k k') as [Hle | Hnle].
        * simpl. lia.
        * simpl. lia.
  Qed.

  Lemma tm_size_remove_le : forall k m,
    tm_size (tm_remove k m) <= tm_size m.
  Proof.
    intros k m. induction m as [| [k' v'] rest IH].
    - simpl. lia.
    - simpl. destruct (key_eq_dec k k') as [Heq | Hne].
      + simpl. lia.
      + simpl. lia.
  Qed.

  Lemma tm_lookup_remove_neq : forall k1 k2 m,
    k1 <> k2 -> tm_lookup k1 (tm_remove k2 m) = tm_lookup k1 m.
  Proof.
    intros k1 k2 m Hne. induction m as [| [k' v'] rest IH].
    - reflexivity.
    - simpl. destruct (key_eq_dec k2 k') as [Heq2 | Hne2].
      + subst k'. destruct (key_eq_dec k1 k2) as [Heq12 | Hne12].
        * exfalso. apply Hne. exact Heq12.
        * reflexivity.
      + simpl. destruct (key_eq_dec k1 k') as [Heq1 | Hne1].
        * reflexivity.
        * exact IH.
  Qed.

  Lemma tm_mem_insert : forall k v m,
    tm_mem k (tm_insert k v m) = true.
  Proof.
    intros k v m. unfold tm_mem. rewrite tm_lookup_insert_eq. reflexivity.
  Qed.

End MapOps.

Section NatMap.

  Lemma tm_example_empty_nat :
    @tm_lookup nat nat nat_dto 42 tm_empty = None.
  Proof. reflexivity. Qed.

  Lemma tm_example_insert_lookup :
    @tm_lookup nat nat nat_dto 1
      (tm_insert 1 100 (tm_insert 2 200 tm_empty)) = Some 100.
  Proof. reflexivity. Qed.

  Lemma tm_example_lookup_absent :
    @tm_lookup nat nat nat_dto 3
      (tm_insert 1 100 (tm_insert 2 200 tm_empty)) = None.
  Proof. reflexivity. Qed.

  Lemma tm_example_mem :
    @tm_mem nat nat nat_dto 2
      (tm_insert 1 100 (tm_insert 2 200 tm_empty)) = true.
  Proof. reflexivity. Qed.

  Lemma tm_example_size :
    @tm_size nat nat
      (tm_insert 1 100 (tm_insert 2 200 tm_empty)) = 2.
  Proof. reflexivity. Qed.

End NatMap.
