(* ========================================================================= *)
(*       THEORY OF SYSTEMS: EXPRESSION LANGUAGE (DEEP EMBEDDING)            *)
(*                                                                           *)
(*  Status: >=15 Qed, 0 Admitted | Author: Horsocrates | Date: 2026-03-06   *)
(* ========================================================================= *)

From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Lists.List.
From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import UniversePolymorphism.

Import ListNotations.

Definition Var := nat.

Inductive Expr : Type :=
  | EVar          : Var -> Expr
  | ESystem       : Level -> Expr
  | EElem         : Expr -> Expr
  | EApp          : Expr -> Expr -> Expr
  | ELam          : Expr -> Expr
  | EPair         : Expr -> Expr -> Expr
  | EFst          : Expr -> Expr
  | ESnd          : Expr -> Expr
  | EObserve      : Expr -> nat -> Expr
  | EResolve      : Expr -> Expr
  | ELayerProject : Expr -> Expr -> Expr
  | EConst        : nat -> Expr
  .

Inductive is_value : Expr -> Prop :=
  | VConst  : forall n, is_value (EConst n)
  | VLam    : forall body, is_value (ELam body)
  | VPair   : forall v1 v2,
                is_value v1 ->
                is_value v2 ->
                is_value (EPair v1 v2)
  | VSystem : forall L, is_value (ESystem L)
  .

Fixpoint expr_size (e : Expr) : nat :=
  match e with
  | EVar _             => 1
  | EConst _           => 1
  | ESystem _          => 1
  | EElem e1           => 1 + expr_size e1
  | EApp f a           => 1 + expr_size f + expr_size a
  | ELam body          => 1 + expr_size body
  | EPair a b          => 1 + expr_size a + expr_size b
  | EFst e1            => 1 + expr_size e1
  | ESnd e1            => 1 + expr_size e1
  | EObserve e1 _      => 1 + expr_size e1
  | EResolve e1        => 1 + expr_size e1
  | ELayerProject e1 l => 1 + expr_size e1 + expr_size l
  end.

Fixpoint shift (c : nat) (e : Expr) : Expr :=
  match e with
  | EVar n             => if n <? c then EVar n else EVar (n + 1)
  | EConst n           => EConst n
  | ESystem L          => ESystem L
  | EElem e1           => EElem (shift c e1)
  | EApp f a           => EApp (shift c f) (shift c a)
  | ELam body          => ELam (shift (c + 1) body)
  | EPair a b          => EPair (shift c a) (shift c b)
  | EFst e1            => EFst (shift c e1)
  | ESnd e1            => ESnd (shift c e1)
  | EObserve e1 n      => EObserve (shift c e1) n
  | EResolve e1        => EResolve (shift c e1)
  | ELayerProject e1 l => ELayerProject (shift c e1) (shift c l)
  end.

Fixpoint subst (k : Var) (s : Expr) (e : Expr) : Expr :=
  match e with
  | EVar n =>
      if n =? k then s
      else if k <? n then EVar (n - 1)
      else EVar n
  | EConst n           => EConst n
  | ESystem L          => ESystem L
  | EElem e1           => EElem (subst k s e1)
  | EApp f a           => EApp (subst k s f) (subst k s a)
  | ELam body          => ELam (subst (k + 1) (shift 0 s) body)
  | EPair a b          => EPair (subst k s a) (subst k s b)
  | EFst e1            => EFst (subst k s e1)
  | ESnd e1            => ESnd (subst k s e1)
  | EObserve e1 n      => EObserve (subst k s e1) n
  | EResolve e1        => EResolve (subst k s e1)
  | ELayerProject e1 l => ELayerProject (subst k s e1) (subst k s l)
  end.

Lemma expr_eq_dec : forall (e1 e2 : Expr), {e1 = e2} + {e1 <> e2}.
Proof.
  induction e1; destruct e2; try (right; discriminate).
  - destruct (Nat.eq_dec v v0) as [Heq | Hneq].
    + left. subst. reflexivity.
    + right. intro H. inversion H. contradiction.
  - destruct (level_eq_dec l l0) as [Heq | Hneq].
    + left. subst. reflexivity.
    + right. intro H. inversion H. contradiction.
  - destruct (IHe1 e2) as [Heq | Hneq].
    + left. subst. reflexivity.
    + right. intro H. inversion H. contradiction.
  - destruct (IHe1_1 e2_1) as [Heq1 | Hneq1];
    destruct (IHe1_2 e2_2) as [Heq2 | Hneq2].
    + left. subst. reflexivity.
    + right. intro H. inversion H. contradiction.
    + right. intro H. inversion H. contradiction.
    + right. intro H. inversion H. contradiction.
  - destruct (IHe1 e2) as [Heq | Hneq].
    + left. subst. reflexivity.
    + right. intro H. inversion H. contradiction.
  - destruct (IHe1_1 e2_1) as [Heq1 | Hneq1];
    destruct (IHe1_2 e2_2) as [Heq2 | Hneq2].
    + left. subst. reflexivity.
    + right. intro H. inversion H. contradiction.
    + right. intro H. inversion H. contradiction.
    + right. intro H. inversion H. contradiction.
  - destruct (IHe1 e2) as [Heq | Hneq].
    + left. subst. reflexivity.
    + right. intro H. inversion H. contradiction.
  - destruct (IHe1 e2) as [Heq | Hneq].
    + left. subst. reflexivity.
    + right. intro H. inversion H. contradiction.
  - destruct (IHe1 e2) as [Heq | Hneq];
    destruct (Nat.eq_dec n n0) as [Heqn | Hneqn].
    + left. subst. reflexivity.
    + right. intro H. inversion H. contradiction.
    + right. intro H. inversion H. contradiction.
    + right. intro H. inversion H. contradiction.
  - destruct (IHe1 e2) as [Heq | Hneq].
    + left. subst. reflexivity.
    + right. intro H. inversion H. contradiction.
  - destruct (IHe1_1 e2_1) as [Heq1 | Hneq1];
    destruct (IHe1_2 e2_2) as [Heq2 | Hneq2].
    + left. subst. reflexivity.
    + right. intro H. inversion H. contradiction.
    + right. intro H. inversion H. contradiction.
    + right. intro H. inversion H. contradiction.
  - destruct (Nat.eq_dec n n0) as [Heq | Hneq].
    + left. subst. reflexivity.
    + right. intro H. inversion H. contradiction.
Qed.

Lemma value_not_var : forall x, ~ is_value (EVar x).
Proof.
  intros x H. inversion H.
Qed.

Lemma value_not_app : forall e1 e2, ~ is_value (EApp e1 e2).
Proof.
  intros e1 e2 H. inversion H.
Qed.

Lemma value_not_fst : forall e, ~ is_value (EFst e).
Proof.
  intros e H. inversion H.
Qed.

Lemma value_not_snd : forall e, ~ is_value (ESnd e).
Proof.
  intros e H. inversion H.
Qed.

Lemma value_not_elem : forall e, ~ is_value (EElem e).
Proof.
  intros e H. inversion H.
Qed.

Lemma value_not_observe : forall e n, ~ is_value (EObserve e n).
Proof.
  intros e n H. inversion H.
Qed.

Lemma is_value_dec : forall e, {is_value e} + {~ is_value e}.
Proof.
  induction e.
  - right. apply value_not_var.
  - left. apply VSystem.
  - right. apply value_not_elem.
  - right. apply value_not_app.
  - left. apply VLam.
  - destruct IHe1 as [Hv1 | Hnv1]; destruct IHe2 as [Hv2 | Hnv2].
    + left. apply VPair; assumption.
    + right. intros H. inversion H. contradiction.
    + right. intros H. inversion H. contradiction.
    + right. intros H. inversion H. contradiction.
  - right. apply value_not_fst.
  - right. apply value_not_snd.
  - right. apply value_not_observe.
  - right. intros H. inversion H.
  - right. intros H. inversion H.
  - left. apply VConst.
Defined.  (* Defined, not Qed — must be transparent for Eval compute *)

Lemma expr_size_positive : forall e, expr_size e > 0.
Proof.
  induction e; simpl; lia.
Qed.

Lemma app_fun_smaller : forall f a, expr_size f < expr_size (EApp f a).
Proof.
  intros f a. simpl.
  pose proof (expr_size_positive a). lia.
Qed.

Lemma app_arg_smaller : forall f a, expr_size a < expr_size (EApp f a).
Proof.
  intros f a. simpl.
  pose proof (expr_size_positive f). lia.
Qed.

Lemma lam_body_smaller : forall body, expr_size body < expr_size (ELam body).
Proof.
  intros body. simpl. lia.
Qed.

Lemma pair_fst_smaller : forall e1 e2, expr_size e1 < expr_size (EPair e1 e2).
Proof.
  intros e1 e2. simpl.
  pose proof (expr_size_positive e2). lia.
Qed.

Lemma pair_snd_smaller : forall e1 e2, expr_size e2 < expr_size (EPair e1 e2).
Proof.
  intros e1 e2. simpl.
  pose proof (expr_size_positive e1). lia.
Qed.

Lemma fst_subterm_smaller : forall e, expr_size e < expr_size (EFst e).
Proof.
  intros e. simpl. lia.
Qed.

Lemma snd_subterm_smaller : forall e, expr_size e < expr_size (ESnd e).
Proof.
  intros e. simpl. lia.
Qed.

Lemma resolve_subterm_smaller : forall e, expr_size e < expr_size (EResolve e).
Proof.
  intros e. simpl. lia.
Qed.

Lemma elem_subterm_smaller : forall e, expr_size e < expr_size (EElem e).
Proof.
  intros e. simpl. lia.
Qed.

Lemma subst_const : forall k s n, subst k s (EConst n) = EConst n.
Proof.
  intros k s n. simpl. reflexivity.
Qed.

Lemma subst_system : forall k s L, subst k s (ESystem L) = ESystem L.
Proof.
  intros k s L. simpl. reflexivity.
Qed.

Lemma subst_pair : forall k s a b,
  subst k s (EPair a b) = EPair (subst k s a) (subst k s b).
Proof.
  intros k s a b. simpl. reflexivity.
Qed.

Lemma subst_app : forall k s f a,
  subst k s (EApp f a) = EApp (subst k s f) (subst k s a).
Proof.
  intros k s f a. simpl. reflexivity.
Qed.

Lemma expr_finite : forall e, exists n, expr_size e = n.
Proof.
  intros e. exists (expr_size e). reflexivity.
Qed.

Lemma expr_induction_size :
  forall (P : Expr -> Prop),
    (forall e, (forall e', expr_size e' < expr_size e -> P e') -> P e) ->
    forall e, P e.
Proof.
  intros P IH e.
  assert (H : forall n e, expr_size e <= n -> P e).
  { induction n as [| n' IHn]; intros e0 Hle.
    - pose proof (expr_size_positive e0). lia.
    - apply IH. intros e' He'.
      apply IHn. lia.
  }
  apply (H (expr_size e) e). lia.
Qed.

Lemma value_const_inv : forall n, is_value (EConst n).
Proof.
  intros n. apply VConst.
Qed.

Lemma shift_zero_var : forall n, shift 0 (EVar n) = EVar (n + 1).
Proof.
  intros n. simpl.
  replace (n <? 0) with false by (symmetry; apply Nat.ltb_nlt; lia).
  reflexivity.
Qed.

Lemma shift_preserves_size : forall c e, expr_size (shift c e) = expr_size e.
Proof.
  intros c e. revert c.
  induction e; intros c; simpl;
  try reflexivity;
  try (rewrite IHe; reflexivity);
  try (rewrite IHe1, IHe2; reflexivity).
  - destruct (v <? c); simpl; reflexivity.
Qed.

Lemma lam_is_value : forall body, is_value (ELam body).
Proof.
  intros body. apply VLam.
Qed.

Lemma system_is_value : forall L, is_value (ESystem L).
Proof.
  intros L. apply VSystem.
Qed.
