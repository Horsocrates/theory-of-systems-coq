(* TSet: Sorted Set as ToS System *)
(* STATUS: 30 Qed, 0 Admitted, 0 axioms *)
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
From ToS Require Import stdlib.TMap.

Section SetOps.
  Context {A : Type} `{DTO : DecTotalOrder A}.

  Definition set_eq_dec (x y : A) : {x = y} + {x <> y}.
  Proof.
    destruct (dto_le_dec x y); destruct (dto_le_dec y x).
    - left. apply dto_le_antisym; assumption.
    - right. intro Heq. subst. apply n. apply dto_le_refl.
    - right. intro Heq. subst. apply n. apply dto_le_refl.
    - right. intro Heq. subst. apply n. apply dto_le_refl.
  Defined.

  Definition ts_empty : list A := [].

  Fixpoint ts_member (x : A) (s : list A) : bool :=
    match s with
    | [] => false
    | y :: rest =>
        if set_eq_dec x y then true else ts_member x rest
    end.

  Fixpoint ts_add (x : A) (s : list A) : list A :=
    match s with
    | [] => [x]
    | y :: rest =>
        if set_eq_dec x y then s
        else if dto_le_dec x y then x :: s
        else y :: ts_add x rest
    end.

  Fixpoint ts_remove (x : A) (s : list A) : list A :=
    match s with
    | [] => []
    | y :: rest =>
        if set_eq_dec x y then rest
        else y :: ts_remove x rest
    end.

  Definition ts_size (s : list A) : nat := length s.

  Fixpoint ts_subset (s1 s2 : list A) : bool :=
    match s1 with
    | [] => true
    | x :: rest => ts_member x s2 && ts_subset rest s2
    end.

  Fixpoint ts_union (s1 s2 : list A) : list A :=
    match s1 with
    | [] => s2
    | x :: rest => ts_union rest (ts_add x s2)
    end.

  Fixpoint ts_inter (s1 s2 : list A) : list A :=
    match s1 with
    | [] => []
    | x :: rest =>
        if ts_member x s2 then x :: ts_inter rest s2
        else ts_inter rest s2
    end.

  Fixpoint ts_diff (s1 s2 : list A) : list A :=
    match s1 with
    | [] => []
    | x :: rest =>
        if ts_member x s2 then ts_diff rest s2
        else x :: ts_diff rest s2
    end.

  Lemma ts_member_empty : forall x, ts_member x ts_empty = false.
  Proof. intros x. reflexivity. Qed.

  Lemma ts_size_empty : ts_size ts_empty = 0.
  Proof. reflexivity. Qed.

  Lemma ts_remove_empty : forall x, ts_remove x ts_empty = ts_empty.
  Proof. intros x. reflexivity. Qed.

  Lemma ts_subset_empty_l : forall s, ts_subset ts_empty s = true.
  Proof. intros s. reflexivity. Qed.

  Lemma ts_union_empty_l : forall s, ts_union ts_empty s = s.
  Proof. intros s. reflexivity. Qed.

  Lemma ts_inter_empty_l : forall s, ts_inter ts_empty s = [].
  Proof. intros s. reflexivity. Qed.

  Lemma ts_diff_empty_l : forall s, ts_diff ts_empty s = [].
  Proof. intros s. reflexivity. Qed.

  Lemma ts_member_add_eq : forall x s,
    ts_member x (ts_add x s) = true.
  Proof.
    intros x s. induction s as [| y rest IH].
    - simpl. destruct (set_eq_dec x x) as [_ | Hne].
      + reflexivity.
      + exfalso. apply Hne. reflexivity.
    - simpl. destruct (set_eq_dec x y) as [Heq | Hne].
      + simpl. destruct (set_eq_dec x y) as [_ | Hne2].
        * reflexivity.
        * exfalso. apply Hne2. exact Heq.
      + destruct (dto_le_dec x y) as [Hle | Hnle].
        * simpl. destruct (set_eq_dec x x) as [_ | Hne2].
          -- reflexivity.
          -- exfalso. apply Hne2. reflexivity.
        * simpl. destruct (set_eq_dec x y) as [Heq2 | _].
          -- exfalso. apply Hne. exact Heq2.
          -- exact IH.
  Qed.

  Lemma ts_member_add_neq : forall x y s,
    x <> y -> ts_member x (ts_add y s) = ts_member x s.
  Proof.
    intros x y s Hne. induction s as [| z rest IH].
    - simpl. destruct (set_eq_dec x y) as [Heq | _].
      + exfalso. apply Hne. exact Heq.
      + reflexivity.
    - simpl.
      destruct (set_eq_dec y z) as [Heqyz | Hneyz].
      + (* y = z, no change *) reflexivity.
      + destruct (dto_le_dec y z) as [Hle | Hnle].
        * simpl. destruct (set_eq_dec x y) as [Heqxy | _].
          -- exfalso. apply Hne. exact Heqxy.
          -- reflexivity.
        * simpl. destruct (set_eq_dec x z) as [Heqxz | _].
          -- reflexivity.
          -- exact IH.
  Qed.

  Lemma member_not_In : forall x s,
    ~ In x s -> ts_member x s = false.
  Proof.
    intros x s. induction s as [| y rest IH]; intro Hni.
    - reflexivity.
    - simpl. destruct (set_eq_dec x y) as [Heq | Hne].
      + exfalso. apply Hni. left. symmetry. exact Heq.
      + apply IH. intro Hin. apply Hni. right. exact Hin.
  Qed.

  Lemma ts_member_remove_eq : forall x s,
    NoDup s ->
    ts_member x (ts_remove x s) = false.
  Proof.
    intros x s Hnd. induction s as [| y rest IH].
    - reflexivity.
    - simpl. destruct (set_eq_dec x y) as [Heq | Hne].
      + subst y. apply member_not_In.
        inversion Hnd; subst. assumption.
      + simpl. destruct (set_eq_dec x y) as [Heq2 | _].
        * exfalso. apply Hne. exact Heq2.
        * apply IH. inversion Hnd; subst. assumption.
  Qed.

  Lemma ts_member_remove_neq : forall x y s,
    x <> y -> ts_member x (ts_remove y s) = ts_member x s.
  Proof.
    intros x y s Hne. induction s as [| z rest IH].
    - reflexivity.
    - simpl. destruct (set_eq_dec y z) as [Heqyz | Hneyz].
      + subst z. destruct (set_eq_dec x y) as [Heqxy | _].
        * exfalso. apply Hne. exact Heqxy.
        * reflexivity.
      + simpl. destruct (set_eq_dec x z) as [Heqxz | _].
        * reflexivity.
        * exact IH.
  Qed.

  Lemma ts_add_sorted : forall x s,
    Sorted s -> Sorted (ts_add x s).
  Proof.
    intros x s. induction s as [| y rest IH]; intro Hs.
    - simpl. constructor.
    - simpl. destruct (set_eq_dec x y) as [Heq | Hne].
      + exact Hs.
      + destruct (dto_le_dec x y) as [Hle | Hnle].
        * constructor; assumption.
        * simpl.
          assert (Htail : Sorted rest) by (apply Sorted_inv_cons in Hs; exact Hs).
          specialize (IH Htail).
          destruct rest as [| z rest'].
          -- simpl in *. constructor.
             ++ destruct (dto_le_total y x) as [H1 | H1].
                ** exact H1.
                ** exfalso. apply Hnle. exact H1.
             ++ constructor.
          -- simpl in *.
             destruct (set_eq_dec x z) as [Heqxz | Hnexz].
             ++ subst z. constructor.
                ** destruct (dto_le_total y x) as [H1 | H1].
                   --- exact H1.
                   --- exfalso. apply Hnle. exact H1.
                ** exact IH.
             ++ destruct (dto_le_dec x z) as [Hlexz | Hnlexz].
                ** constructor.
                   --- destruct (dto_le_total y x) as [H1 | H1].
                       +++ exact H1.
                       +++ exfalso. apply Hnle. exact H1.
                   --- exact IH.
                ** constructor.
                   --- apply Sorted_inv_le in Hs. exact Hs.
                   --- exact IH.
  Qed.

  Lemma ts_remove_In : forall x y s,
    In y (ts_remove x s) -> In y s.
  Proof.
    intros x y s. induction s as [| z rest IH].
    - simpl. auto.
    - simpl. destruct (set_eq_dec x z).
      + intro H. right. exact H.
      + simpl. intros [Heq | Hin].
        * left. exact Heq.
        * right. apply IH. exact Hin.
  Qed.

  Lemma ts_remove_sorted : forall x s,
    Sorted s -> Sorted (ts_remove x s).
  Proof.
    intros x s Hs. induction s as [| a rest IH].
    - simpl. constructor.
    - simpl. destruct (set_eq_dec x a) as [Heq | Hne].
      + apply Sorted_inv_cons in Hs. exact Hs.
      + assert (Htail : Sorted rest) by (apply Sorted_inv_cons in Hs; exact Hs).
        specialize (IH Htail).
        destruct (ts_remove x rest) as [| c rest2] eqn:Heqr.
        * constructor.
        * constructor.
          -- assert (Hinc : In c rest).
             { apply ts_remove_In with (x := x).
               rewrite Heqr. left. reflexivity. }
             apply Sorted_head_le_all with (l := rest); assumption.
          -- exact IH.
  Qed.

  Lemma ts_size_add_le : forall x s,
    ts_size (ts_add x s) <= ts_size s + 1.
  Proof.
    intros x s. induction s as [| y rest IH].
    - simpl. lia.
    - simpl. destruct (set_eq_dec x y).
      + simpl. lia.
      + destruct (dto_le_dec x y).
        * simpl. lia.
        * simpl. lia.
  Qed.

  Lemma ts_size_remove_le : forall x s,
    ts_size (ts_remove x s) <= ts_size s.
  Proof.
    intros x s. induction s as [| y rest IH].
    - simpl. lia.
    - simpl. destruct (set_eq_dec x y).
      + simpl. lia.
      + simpl. lia.
  Qed.

  Lemma ts_member_cons : forall x y s,
    ts_member x s = true -> ts_member x (y :: s) = true.
  Proof.
    intros x y s H. simpl. destruct (set_eq_dec x y).
    - reflexivity.
    - exact H.
  Qed.

  Lemma ts_subset_cons : forall s1 x s2,
    ts_subset s1 s2 = true -> ts_subset s1 (x :: s2) = true.
  Proof.
    induction s1 as [| a rest IH]; intros x s2 H.
    - reflexivity.
    - simpl in *. apply andb_true_iff in H. destruct H as [Hmem Hsub].
      apply andb_true_iff. split.
      + apply ts_member_cons. exact Hmem.
      + apply IH. exact Hsub.
  Qed.

  Lemma ts_subset_refl : forall s,
    ts_subset s s = true.
  Proof.
    induction s as [| x rest IH].
    - reflexivity.
    - simpl. destruct (set_eq_dec x x) as [_ | Hne].
      + simpl. apply ts_subset_cons. exact IH.
      + exfalso. apply Hne. reflexivity.
  Qed.

  Lemma ts_diff_empty_r : forall s,
    ts_diff s [] = s.
  Proof.
    induction s as [| x rest IH].
    - reflexivity.
    - simpl. f_equal. exact IH.
  Qed.

  Lemma ts_inter_empty_r : forall s,
    ts_inter s [] = [].
  Proof.
    induction s as [| x rest IH].
    - reflexivity.
    - simpl. exact IH.
  Qed.

  Lemma ts_member_In : forall x s,
    ts_member x s = true <-> In x s.
  Proof.
    intros x s. induction s as [| y rest IH].
    - simpl. split; intro H; [discriminate | destruct H].
    - simpl. destruct (set_eq_dec x y) as [Heq | Hne].
      + split; intro H.
        * left. symmetry. exact Heq.
        * reflexivity.
      + split; intro H.
        * right. apply IH. exact H.
        * destruct H as [Heq2 | Hin].
          -- exfalso. apply Hne. symmetry. exact Heq2.
          -- apply IH. exact Hin.
  Qed.

  Lemma ts_add_In : forall x s,
    In x (ts_add x s).
  Proof.
    intros x s. apply ts_member_In. apply ts_member_add_eq.
  Qed.

  Lemma ts_add_In_other : forall x y s,
    In y s -> In y (ts_add x s).
  Proof.
    intros x y s Hin. induction s as [| z rest IH].
    - destruct Hin.
    - simpl. destruct (set_eq_dec x z) as [Heq | Hne].
      + exact Hin.
      + destruct (dto_le_dec x z) as [Hle | Hnle].
        * right. exact Hin.
        * simpl in Hin. destruct Hin as [Heqyz | Hinr].
          -- left. exact Heqyz.
          -- right. apply IH. exact Hinr.
  Qed.

  Lemma ts_remove_not_In : forall x s,
    NoDup s -> ~ In x (ts_remove x s).
  Proof.
    intros x s Hnd. intro Hin.
    assert (Hf : ts_member x (ts_remove x s) = false).
    { apply ts_member_remove_eq. exact Hnd. }
    apply ts_member_In in Hin. rewrite Hin in Hf. discriminate.
  Qed.

End SetOps.

Section NatSet.

  Lemma ts_example_empty :
    @ts_member nat nat_dto 1 ts_empty = false.
  Proof. reflexivity. Qed.

  Lemma ts_example_add_member :
    @ts_member nat nat_dto 2 (ts_add 2 (ts_add 1 ts_empty)) = true.
  Proof. reflexivity. Qed.

  Lemma ts_example_add_size :
    @ts_size nat (ts_add 1 (ts_add 2 (ts_add 3 ts_empty))) = 3.
  Proof. reflexivity. Qed.

  Lemma ts_example_subset :
    @ts_subset nat nat_dto
      (ts_add 1 ts_empty)
      (ts_add 1 (ts_add 2 ts_empty)) = true.
  Proof. reflexivity. Qed.

End NatSet.
