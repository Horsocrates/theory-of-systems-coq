(* THEORY OF SYSTEMS: TYPING RELATION FOR EXPRESSION LANGUAGE *)
(* STATUS: >=15 Qed, 0 Admitted  |  Author: Horsocrates | Date: 2026-03-06 *)

From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Lists.List.
Import ListNotations.

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import UniversePolymorphism.
From ToS Require Import Expressions.

Inductive Ty : Type :=
  | TyNat     : Ty
  | TySystem  : Level -> Ty
  | TyArrow   : Ty -> Ty -> Ty
  | TyPair    : Ty -> Ty -> Ty
  | TyProcess : Ty -> Ty
  | TyLayer   : Ty -> Ty
  .

Definition TyCtx := list Ty.

Inductive expr_has_type : TyCtx -> Expr -> Ty -> Prop :=
  | T_Var : forall Gamma x T,
      nth_error Gamma x = Some T ->
      expr_has_type Gamma (EVar x) T
  | T_Const : forall Gamma n,
      expr_has_type Gamma (EConst n) TyNat
  | T_Lam : forall Gamma body T1 T2,
      expr_has_type (T1 :: Gamma) body T2 ->
      expr_has_type Gamma (ELam body) (TyArrow T1 T2)
  | T_App : forall Gamma f a T1 T2,
      expr_has_type Gamma f (TyArrow T1 T2) ->
      expr_has_type Gamma a T1 ->
      expr_has_type Gamma (EApp f a) T2
  | T_Pair : forall Gamma e1 e2 T1 T2,
      expr_has_type Gamma e1 T1 ->
      expr_has_type Gamma e2 T2 ->
      expr_has_type Gamma (EPair e1 e2) (TyPair T1 T2)
  | T_Fst : forall Gamma e T1 T2,
      expr_has_type Gamma e (TyPair T1 T2) ->
      expr_has_type Gamma (EFst e) T1
  | T_Snd : forall Gamma e T1 T2,
      expr_has_type Gamma e (TyPair T1 T2) ->
      expr_has_type Gamma (ESnd e) T2
  | T_Observe : forall Gamma e T n,
      expr_has_type Gamma e (TyProcess T) ->
      expr_has_type Gamma (EObserve e n) T
  | T_Resolve : forall Gamma e T,
      expr_has_type Gamma e T ->
      expr_has_type Gamma (EResolve e) T
  | T_System : forall Gamma L,
      expr_has_type Gamma (ESystem L) (TySystem L)
  .

Lemma ty_eq_dec : forall (T1 T2 : Ty), {T1 = T2} + {T1 <> T2}.
Proof.
  induction T1; destruct T2;
    try (right; discriminate).
  - left; reflexivity.
  - destruct (level_eq_dec l l0) as [Heq | Hneq].
    + left; subst; reflexivity.
    + right; intro H; inversion H; contradiction.
  - destruct (IHT1_1 T2_1) as [H1 | H1];
    destruct (IHT1_2 T2_2) as [H2 | H2].
    + left; subst; reflexivity.
    + right; intro H; inversion H; contradiction.
    + right; intro H; inversion H; contradiction.
    + right; intro H; inversion H; contradiction.
  - destruct (IHT1_1 T2_1) as [H1 | H1];
    destruct (IHT1_2 T2_2) as [H2 | H2].
    + left; subst; reflexivity.
    + right; intro H; inversion H; contradiction.
    + right; intro H; inversion H; contradiction.
    + right; intro H; inversion H; contradiction.
  - destruct (IHT1 T2) as [H | H].
    + left; subst; reflexivity.
    + right; intro Heq; inversion Heq; contradiction.
  - destruct (IHT1 T2) as [H | H].
    + left; subst; reflexivity.
    + right; intro Heq; inversion Heq; contradiction.
Defined.  (* Defined, not Qed — must be transparent for Eval compute *)

Lemma const_has_type_nat : forall Gamma n T,
    expr_has_type Gamma (EConst n) T -> T = TyNat.
Proof.
  intros Gamma n T H.
  inversion H. reflexivity.
Qed.

Lemma lam_has_type_arrow : forall Gamma body T,
    expr_has_type Gamma (ELam body) T ->
    exists T1 T2, T = TyArrow T1 T2.
Proof.
  intros Gamma body T H.
  inversion H; subst.
  exists T1, T2. reflexivity.
Qed.

Lemma system_has_type_system : forall Gamma L T,
    expr_has_type Gamma (ESystem L) T -> T = TySystem L.
Proof.
  intros Gamma L T H.
  inversion H; subst. reflexivity.
Qed.

Lemma var_type_unique : forall Gamma x T1 T2,
    expr_has_type Gamma (EVar x) T1 ->
    expr_has_type Gamma (EVar x) T2 ->
    T1 = T2.
Proof.
  intros Gamma x T1 T2 H1 H2.
  inversion H1; subst.
  inversion H2; subst.
  congruence.
Qed.



Lemma canonical_arrow : forall Gamma v T1 T2,
    is_value v ->
    expr_has_type Gamma v (TyArrow T1 T2) ->
    exists body, v = ELam body.
Proof.
  intros Gamma v T1 T2 Hval Htype.
  inversion Hval; subst; inversion Htype; subst.
  exists body. reflexivity.
Qed.

Lemma canonical_pair : forall Gamma v T1 T2,
    is_value v ->
    expr_has_type Gamma v (TyPair T1 T2) ->
    exists v1 v2, v = EPair v1 v2 /\ is_value v1 /\ is_value v2.
Proof.
  intros Gamma v T1 T2 Hval Htype.
  inversion Hval; subst; inversion Htype; subst.
  exists v1, v2. split; [reflexivity | split; assumption].
Qed.

Lemma canonical_nat : forall Gamma v,
    is_value v ->
    expr_has_type Gamma v TyNat ->
    exists n, v = EConst n.
Proof.
  intros Gamma v Hval Htype.
  inversion Hval; subst; inversion Htype; subst.
  exists n. reflexivity.
Qed.

Lemma canonical_system : forall Gamma v L,
    is_value v ->
    expr_has_type Gamma v (TySystem L) ->
    v = ESystem L.
Proof.
  intros Gamma v L Hval Htype.
  inversion Hval; subst; inversion Htype; subst.
  reflexivity.
Qed.

Lemma empty_ctx_no_var : forall x,
    ~ exists T, expr_has_type [] (EVar x) T.
Proof.
  intros x [T H].
  inversion H; subst.
  rewrite nth_error_nil in H2.
  discriminate.
Qed.

Lemma typing_in_empty_ctx : forall n,
    expr_has_type [] (EConst n) TyNat.
Proof.
  intros n. apply T_Const.
Qed.

Lemma nth_error_app_split : forall (A : Type) (l1 l2 : list A) (n : nat),
    nth_error (l1 ++ l2) n =
    if n <? length l1
    then nth_error l1 n
    else nth_error l2 (n - length l1).
Proof.
  intros A l1. induction l1; intros l2 n; simpl.
  - rewrite Nat.sub_0_r. reflexivity.
  - destruct n; simpl.
    + reflexivity.
    + apply IHl1.
Qed.

Lemma weakening_general : forall e Gamma1 Gamma2 S T,
    expr_has_type (Gamma1 ++ Gamma2) e T ->
    expr_has_type (Gamma1 ++ S :: Gamma2) (shift (length Gamma1) e) T.
Proof.
  induction e; intros Gamma1 Gamma2 S T H; simpl; inversion H; subst; simpl.
  - (* EVar *)
    destruct (Nat.ltb_spec v (length Gamma1)) as [Hlt | Hge]; simpl.
    + (* v < length Gamma1: EVar v in Gamma1 *)
      apply T_Var.
      rewrite nth_error_app1 by exact Hlt.
      rewrite nth_error_app1 in H2 by exact Hlt.
      exact H2.
    + (* v >= length Gamma1: EVar (v+1) in Gamma2 of extended context *)
      apply T_Var.
      rewrite nth_error_app2 by lia.
      rewrite nth_error_app2 in H2 by exact Hge.
      assert (Heq: v + 1 - length Gamma1 = Nat.succ (v - length Gamma1)).
      { rewrite Nat.add_comm. simpl. apply Nat.sub_succ_l. exact Hge. }
      rewrite Heq. simpl. exact H2.
  - (* ESystem *)
    apply T_System.
  - (* EApp *)
    apply T_App with T1.
    + apply IHe1. exact H3.
    + apply IHe2. exact H5.
  - (* ELam *)
    apply T_Lam.
    assert (IH := IHe (T1 :: Gamma1) Gamma2 S T2 H2).
    simpl in IH.
    rewrite Nat.add_1_r.
    exact IH.
  - (* EPair *)
    apply T_Pair.
    + apply IHe1. exact H3.
    + apply IHe2. exact H5.
  - (* EFst *)
    apply T_Fst with T2.
    apply IHe. exact H2.
  - (* ESnd *)
    apply T_Snd with T1.
    apply IHe. exact H2.
  - (* EObserve *)
    apply T_Observe.
    apply IHe. assumption.
  - (* EResolve *)
    apply T_Resolve.
    apply IHe. exact H2.
  - (* EConst *)
    apply T_Const.
Qed.


Lemma weakening_expr : forall Gamma e T S,
    expr_has_type Gamma e T ->
    expr_has_type (S :: Gamma) (shift 0 e) T.
Proof.
  intros Gamma e T S H.
  apply (weakening_general e [] Gamma S T H).
Qed.

Lemma substitution_preserves_typing_general :
  forall Gamma1 Gamma2 e T1 T2 s,
    expr_has_type (Gamma1 ++ T1 :: Gamma2) e T2 ->
    expr_has_type (Gamma1 ++ Gamma2) s T1 ->
    expr_has_type (Gamma1 ++ Gamma2) (subst (length Gamma1) s e) T2.
Proof.
  intros Gamma1 Gamma2 e.
  revert Gamma1 Gamma2.
  induction e; intros Gamma1 Gamma2 T1 T2 s He Hs.
  - { (* EVar v: subst (length Gamma1) s (EVar v) *)
    assert (Hnth : nth_error (Gamma1 ++ T1 :: Gamma2) v = Some T2) by (inversion He; assumption).
    destruct (Nat.eqb_spec v (length Gamma1)) as [Heq | Hne].
    + (* v = length Gamma1: subst yields s *)
      subst. simpl.
      rewrite nth_error_app2 in Hnth by lia.
      rewrite Nat.sub_diag in Hnth. simpl in Hnth.
      inversion Hnth; subst.
      rewrite Nat.eqb_refl. simpl. exact Hs.
    + (* v <> length Gamma1 *)
      assert (Hneq : v =? length Gamma1 = false) by (apply Nat.eqb_neq; exact Hne).
      cbn [subst]. rewrite Hneq.
      destruct (Nat.ltb_spec (length Gamma1) v) as [Hlt | Hge]; simpl.
      -- (* length Gamma1 < v: subst yields EVar (v-1) *)
        apply T_Var.
        rewrite nth_error_app_split.
        destruct (Nat.ltb_spec (v - 1) (length Gamma1)) as [Hlt2 | Hge2].
        { lia. }
        replace (v - 1 - length Gamma1) with (v - length Gamma1 - 1) by lia.
        rewrite nth_error_app_split in Hnth.
        destruct (Nat.ltb_spec v (length Gamma1)) as [Hlt3 | Hge3].
        { lia. }
        destruct (v - length Gamma1) as [| k] eqn:Hk.
        { lia. }
        simpl in Hnth. simpl. rewrite Nat.sub_0_r. exact Hnth.
      -- (* v < length Gamma1: subst yields EVar v *)
        assert (Hlt2 : v < length Gamma1) by lia.
        apply T_Var.
        rewrite nth_error_app_split.
        destruct (Nat.ltb_spec v (length Gamma1)) as [Hvlt | Hvge].
        { rewrite nth_error_app_split in Hnth.
          destruct (Nat.ltb_spec v (length Gamma1)) as [Hx | Hx].
          - exact Hnth.
          - lia. }
        { lia. }
  }
  - (* ESystem *)
    inversion He; subst. simpl. apply T_System.
  - (* EElem: no typing rule, inversion closes *)
    inversion He.
  - (* EApp e1 e2 *)
    inversion He; subst. simpl.
    apply T_App with T0.
    + apply IHe1 with (T1 := T1). assumption. exact Hs.
    + apply IHe2 with (T1 := T1). assumption. exact Hs.
  - (* ELam body *)
    inversion He; subst. simpl.
    apply T_Lam.
    (* Apply IHe with explicit context (T0::Gamma1)++Gamma2 *)
    assert (IH := IHe (T0 :: Gamma1) Gamma2 T1 T3 (shift 0 s) H1
                      (weakening_expr (Gamma1 ++ Gamma2) s T1 T0 Hs)).
    simpl in IH.
    rewrite Nat.add_1_r.
    exact IH.
  - (* EPair e1 e2 *)
    inversion He; subst. simpl.
    apply T_Pair.
    + apply IHe1 with (T1 := T1). assumption. exact Hs.
    + apply IHe2 with (T1 := T1). assumption. exact Hs.
  - (* EFst e0 *)
    inversion He; subst. simpl.
    apply T_Fst with T3.
    apply IHe with (T1 := T1). assumption. exact Hs.
  - (* ESnd e0 *)
    inversion He; subst. simpl.
    apply T_Snd with T0.
    apply IHe with (T1 := T1). assumption. exact Hs.
  - (* EObserve e0 n *)
    inversion He; subst. simpl.
    apply T_Observe.
    apply IHe with (T1 := T1). assumption. exact Hs.
  - (* EResolve e0 *)
    inversion He; subst. simpl.
    apply T_Resolve.
    apply IHe with (T1 := T1). assumption. exact Hs.
  - (* ELayerProject: no typing rule, inversion closes *)
    inversion He.
  - (* EConst n *)
    inversion He; subst. simpl. apply T_Const.
Qed.

Lemma substitution_preserves_typing :
  forall Gamma e T1 T2 s,
    expr_has_type (T1 :: Gamma) e T2 ->
    expr_has_type Gamma s T1 ->
    expr_has_type Gamma (subst 0 s e) T2.
Proof.
  intros Gamma e T1 T2 s He Hs.
  apply (substitution_preserves_typing_general [] Gamma e T1 T2 s He Hs).
Qed.

Lemma value_has_type_inv : forall Gamma v T,
    is_value v ->
    expr_has_type Gamma v T ->
    (exists n, v = EConst n /\ T = TyNat) \/
    (exists body T1 T2, v = ELam body /\ T = TyArrow T1 T2) \/
    (exists v1 v2 T1 T2, v = EPair v1 v2 /\ T = TyPair T1 T2
                          /\ is_value v1 /\ is_value v2) \/
    (exists L, v = ESystem L /\ T = TySystem L).
Proof.
  intros Gamma v T Hval Htype.
  inversion Hval; subst; inversion Htype; subst.
  - left. exists n. split; reflexivity.
  - right. left. exists body, T1, T2. split; reflexivity.
  - right. right. left.
    exists v1, v2, T1, T2.
    split; [reflexivity | split; [reflexivity | split; assumption]].
  - right. right. right.
    exists L. split; reflexivity.
Qed.

Lemma identity_well_typed :
    expr_has_type [] (ELam (EVar 0)) (TyArrow TyNat TyNat).
Proof.
  apply T_Lam.
  apply T_Var.
  simpl. reflexivity.
Qed.

Lemma resolve_preserves_type : forall Gamma e T,
    expr_has_type Gamma e T ->
    expr_has_type Gamma (EResolve e) T.
Proof.
  intros Gamma e T H.
  apply T_Resolve. exact H.
Qed.

Lemma fst_type_consistent : forall Gamma e T1 T2,
    expr_has_type Gamma e (TyPair T1 T2) ->
    expr_has_type Gamma (EFst e) T1.
Proof.
  intros Gamma e T1 T2 H.
  apply T_Fst with T2. exact H.
Qed.

Lemma snd_type_consistent : forall Gamma e T1 T2,
    expr_has_type Gamma e (TyPair T1 T2) ->
    expr_has_type Gamma (ESnd e) T2.
Proof.
  intros Gamma e T1 T2 H.
  apply T_Snd with T1. exact H.
Qed.

Lemma app_type_arrow : forall Gamma f a T1 T2,
    expr_has_type Gamma f (TyArrow T1 T2) ->
    expr_has_type Gamma a T1 ->
    expr_has_type Gamma (EApp f a) T2.
Proof.
  intros Gamma f a T1 T2 Hf Ha.
  apply T_App with T1. exact Hf. exact Ha.
Qed.

Lemma observe_type : forall Gamma e T n,
    expr_has_type Gamma e (TyProcess T) ->
    expr_has_type Gamma (EObserve e n) T.
Proof.
  intros Gamma e T n H.
  apply T_Observe. exact H.
Qed.
