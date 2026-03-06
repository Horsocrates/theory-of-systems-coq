(* ================================================================= *)
(*  THEORY OF SYSTEMS: VERIFIED TYPE CHECKER                         *)
(*                                                                    *)
(*  A decision procedure for expr_has_type.                          *)
(*  Returns (Some T) if expression has type T in context Gamma.      *)
(*                                                                    *)
(*  PROVEN SOUND: typecheck G e = Some T -> expr_has_type G e T      *)
(*  COMPUTABLE: extracts to OCaml via Extraction                      *)
(*                                                                    *)
(*  Status: >=20 Qed, 0 Admitted | Author: Horsocrates | 2026-03-06  *)
(* ================================================================= *)

From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
Import ListNotations.
From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import UniversePolymorphism.
From ToS Require Import Expressions.
From ToS Require Import Typing_Expr.

(** ================================================================= *)
(** ** 1. The Type Checker (Curry-style — bare lambdas return None)    *)
(** ================================================================= *)

(** The type checker is a total function: always returns Some T or None.
    For Curry-style ELam (no annotation), returns None.
    See typecheck_ann below for Church-style (annotated) lambdas. *)

Fixpoint typecheck (Gamma : TyCtx) (e : Expr) : option Ty :=
  match e with
  | EVar x       => nth_error Gamma x
  | EConst _     => Some TyNat
  | ESystem L    => Some (TySystem L)
  | ELam _       => None
  | EApp f a     =>
      match typecheck Gamma f with
      | Some (TyArrow T1 T2) =>
          match typecheck Gamma a with
          | Some T1' => if ty_eq_dec T1 T1' then Some T2 else None
          | None     => None
          end
      | _ => None
      end
  | EPair e1 e2  =>
      match typecheck Gamma e1 with
      | Some T1 =>
          match typecheck Gamma e2 with
          | Some T2 => Some (TyPair T1 T2)
          | None    => None
          end
      | None => None
      end
  | EFst e0      =>
      match typecheck Gamma e0 with
      | Some (TyPair T1 _) => Some T1
      | _                  => None
      end
  | ESnd e0      =>
      match typecheck Gamma e0 with
      | Some (TyPair _ T2) => Some T2
      | _                  => None
      end
  | EObserve e0 _ =>
      match typecheck Gamma e0 with
      | Some (TyProcess T) => Some T
      | _                  => None
      end
  | EResolve e0   => typecheck Gamma e0
  | ELayerProject _ _ => None
  | EElem _       => None
  end.

(** ================================================================= *)
(** ** 2. Soundness: typecheck G e = Some T -> expr_has_type G e T    *)
(** ================================================================= *)

Theorem typecheck_sound : forall Gamma e T,
  typecheck Gamma e = Some T ->
  expr_has_type Gamma e T.
Proof.
  intros Gamma e. revert Gamma.
  induction e; intros Gamma T H; simpl in H.
  (* EVar *)
  - apply T_Var. exact H.
  (* ESystem *)
  - injection H as <-. apply T_System.
  (* EElem — no typing rule *)
  - discriminate.
  (* EApp *)
  - destruct (typecheck Gamma e1) as [Tf |] eqn:E1; [| discriminate].
    destruct Tf; try discriminate.
    destruct (typecheck Gamma e2) as [Ta |] eqn:E2; [| discriminate].
    destruct (ty_eq_dec Tf1 Ta) as [Heq | Hneq]; [| discriminate].
    subst Ta. injection H as <-.
    eapply T_App.
    + apply IHe1. exact E1.
    + apply IHe2. exact E2.
  (* ELam — returns None *)
  - discriminate.
  (* EPair *)
  - destruct (typecheck Gamma e1) as [T1 |] eqn:E1; [| discriminate].
    destruct (typecheck Gamma e2) as [T2 |] eqn:E2; [| discriminate].
    injection H as <-.
    apply T_Pair.
    + apply IHe1. exact E1.
    + apply IHe2. exact E2.
  (* EFst *)
  - destruct (typecheck Gamma e) as [Te |] eqn:Ee; [| discriminate].
    destruct Te; try discriminate.
    injection H as <-.
    eapply T_Fst. apply IHe. exact Ee.
  (* ESnd *)
  - destruct (typecheck Gamma e) as [Te |] eqn:Ee; [| discriminate].
    destruct Te; try discriminate.
    injection H as <-.
    eapply T_Snd. apply IHe. exact Ee.
  (* EObserve *)
  - destruct (typecheck Gamma e) as [Te |] eqn:Ee; [| discriminate].
    destruct Te; try discriminate.
    injection H as <-.
    apply T_Observe. apply IHe. exact Ee.
  (* EResolve *)
  - apply T_Resolve. apply IHe. exact H.
  (* ELayerProject — no typing rule *)
  - discriminate.
  (* EConst *)
  - injection H as <-. apply T_Const.
Qed.

(** ================================================================= *)
(** ** 3. Equation Lemmas                                              *)
(** ================================================================= *)

Lemma typecheck_var : forall Gamma x,
  typecheck Gamma (EVar x) = nth_error Gamma x.
Proof. intros. reflexivity. Qed.

Lemma typecheck_const : forall Gamma n,
  typecheck Gamma (EConst n) = Some TyNat.
Proof. intros. reflexivity. Qed.

Lemma typecheck_system : forall Gamma L,
  typecheck Gamma (ESystem L) = Some (TySystem L).
Proof. intros. reflexivity. Qed.

Lemma typecheck_lam_none : forall Gamma body,
  typecheck Gamma (ELam body) = None.
Proof. intros. reflexivity. Qed.

Lemma typecheck_elem_none : forall Gamma e,
  typecheck Gamma (EElem e) = None.
Proof. intros. reflexivity. Qed.

Lemma typecheck_layer_none : forall Gamma e1 e2,
  typecheck Gamma (ELayerProject e1 e2) = None.
Proof. intros. reflexivity. Qed.

Lemma typecheck_resolve : forall Gamma e,
  typecheck Gamma (EResolve e) = typecheck Gamma e.
Proof. intros. reflexivity. Qed.

(** ================================================================= *)
(** ** 4. Inversion Lemmas                                             *)
(** ================================================================= *)

Lemma typecheck_app_inversion : forall Gamma e1 e2 T,
  typecheck Gamma (EApp e1 e2) = Some T ->
  exists T1, typecheck Gamma e1 = Some (TyArrow T1 T) /\
             typecheck Gamma e2 = Some T1.
Proof.
  intros Gamma e1 e2 T H. simpl in H.
  destruct (typecheck Gamma e1) as [Tf |] eqn:E1; [| discriminate].
  destruct Tf; try discriminate.
  destruct (typecheck Gamma e2) as [Ta |] eqn:E2; [| discriminate].
  destruct (ty_eq_dec Tf1 Ta) as [Heq | Hneq]; [| discriminate].
  subst Ta. injection H as <-.
  exists Tf1. split; reflexivity.
Qed.

Lemma typecheck_pair_inversion : forall Gamma e1 e2 T,
  typecheck Gamma (EPair e1 e2) = Some T ->
  exists T1 T2, T = TyPair T1 T2 /\
                typecheck Gamma e1 = Some T1 /\
                typecheck Gamma e2 = Some T2.
Proof.
  intros Gamma e1 e2 T H. simpl in H.
  destruct (typecheck Gamma e1) as [T1 |] eqn:E1; [| discriminate].
  destruct (typecheck Gamma e2) as [T2 |] eqn:E2; [| discriminate].
  injection H as <-.
  exists T1, T2. repeat split; reflexivity.
Qed.

Lemma typecheck_fst_inversion : forall Gamma e T,
  typecheck Gamma (EFst e) = Some T ->
  exists T2, typecheck Gamma e = Some (TyPair T T2).
Proof.
  intros Gamma e T H. simpl in H.
  destruct (typecheck Gamma e) as [Te |] eqn:Ee; [| discriminate].
  destruct Te; try discriminate.
  injection H as <-.
  exists Te2. reflexivity.
Qed.

Lemma typecheck_snd_inversion : forall Gamma e T,
  typecheck Gamma (ESnd e) = Some T ->
  exists T1, typecheck Gamma e = Some (TyPair T1 T).
Proof.
  intros Gamma e T H. simpl in H.
  destruct (typecheck Gamma e) as [Te |] eqn:Ee; [| discriminate].
  destruct Te; try discriminate.
  injection H as <-.
  exists Te1. reflexivity.
Qed.

Lemma typecheck_observe_inversion : forall Gamma e n T,
  typecheck Gamma (EObserve e n) = Some T ->
  typecheck Gamma e = Some (TyProcess T).
Proof.
  intros Gamma e n T H. simpl in H.
  destruct (typecheck Gamma e) as [Te |]; [| discriminate].
  destruct Te; try discriminate.
  injection H as <-. reflexivity.
Qed.

(** ================================================================= *)
(** ** 5. Determinism                                                  *)
(** ================================================================= *)

Lemma typecheck_deterministic : forall Gamma e T1 T2,
  typecheck Gamma e = Some T1 ->
  typecheck Gamma e = Some T2 ->
  T1 = T2.
Proof.
  intros Gamma e T1 T2 H1 H2. congruence.
Qed.

(** ================================================================= *)
(** ** 6. Annotated Expressions (Church-style lambdas)                 *)
(** ================================================================= *)

(** Annotated expressions carry type annotations on lambdas,
    enabling complete type checking without inference.
    EALamAnn T body corresponds to lambda(x : T). body *)

Inductive ExprAnn : Type :=
  | EAVar      : Var -> ExprAnn
  | EAConst    : nat -> ExprAnn
  | EASystem   : Level -> ExprAnn
  | EALamAnn   : Ty -> ExprAnn -> ExprAnn
  | EAApp      : ExprAnn -> ExprAnn -> ExprAnn
  | EAPair     : ExprAnn -> ExprAnn -> ExprAnn
  | EAFst      : ExprAnn -> ExprAnn
  | EASnd      : ExprAnn -> ExprAnn
  | EAObserve  : ExprAnn -> nat -> ExprAnn
  | EAResolve  : ExprAnn -> ExprAnn
  .

(** Erase annotations back to plain Expr *)
Fixpoint erase_ann (ea : ExprAnn) : Expr :=
  match ea with
  | EAVar x         => EVar x
  | EAConst n       => EConst n
  | EASystem L      => ESystem L
  | EALamAnn _ body => ELam (erase_ann body)
  | EAApp f a       => EApp (erase_ann f) (erase_ann a)
  | EAPair e1 e2    => EPair (erase_ann e1) (erase_ann e2)
  | EAFst e         => EFst (erase_ann e)
  | EASnd e         => ESnd (erase_ann e)
  | EAObserve e n   => EObserve (erase_ann e) n
  | EAResolve e     => EResolve (erase_ann e)
  end.

(** Type checker for annotated expressions — handles lambdas *)
Fixpoint typecheck_ann (Gamma : TyCtx) (ea : ExprAnn) : option Ty :=
  match ea with
  | EAVar x       => nth_error Gamma x
  | EAConst _     => Some TyNat
  | EASystem L    => Some (TySystem L)
  | EALamAnn T1 body =>
      match typecheck_ann (T1 :: Gamma) body with
      | Some T2 => Some (TyArrow T1 T2)
      | None    => None
      end
  | EAApp f a     =>
      match typecheck_ann Gamma f with
      | Some (TyArrow T1 T2) =>
          match typecheck_ann Gamma a with
          | Some T1' => if ty_eq_dec T1 T1' then Some T2 else None
          | None     => None
          end
      | _ => None
      end
  | EAPair e1 e2  =>
      match typecheck_ann Gamma e1 with
      | Some T1 =>
          match typecheck_ann Gamma e2 with
          | Some T2 => Some (TyPair T1 T2)
          | None    => None
          end
      | None => None
      end
  | EAFst e       =>
      match typecheck_ann Gamma e with
      | Some (TyPair T1 _) => Some T1
      | _                  => None
      end
  | EASnd e       =>
      match typecheck_ann Gamma e with
      | Some (TyPair _ T2) => Some T2
      | _                  => None
      end
  | EAObserve e _ =>
      match typecheck_ann Gamma e with
      | Some (TyProcess T) => Some T
      | _                  => None
      end
  | EAResolve e   => typecheck_ann Gamma e
  end.

(** ================================================================= *)
(** ** 7. Annotated Soundness                                          *)
(** ================================================================= *)

(** THE key theorem for annotated expressions:
    if typecheck_ann succeeds, the erased expression is well-typed. *)
Theorem typecheck_ann_sound : forall Gamma ea T,
  typecheck_ann Gamma ea = Some T ->
  expr_has_type Gamma (erase_ann ea) T.
Proof.
  intros Gamma ea. revert Gamma.
  induction ea; intros Gamma T H; simpl in H; simpl.
  (* EAVar *)
  - apply T_Var. exact H.
  (* EAConst *)
  - injection H as <-. apply T_Const.
  (* EASystem *)
  - injection H as <-. apply T_System.
  (* EALamAnn *)
  - destruct (typecheck_ann (t :: Gamma) ea) as [T2 |] eqn:E; [| discriminate].
    injection H as <-.
    apply T_Lam. apply IHea. exact E.
  (* EAApp *)
  - destruct (typecheck_ann Gamma ea1) as [Tf |] eqn:E1; [| discriminate].
    destruct Tf; try discriminate.
    destruct (typecheck_ann Gamma ea2) as [Ta |] eqn:E2; [| discriminate].
    destruct (ty_eq_dec Tf1 Ta) as [Heq | Hneq]; [| discriminate].
    subst Ta. injection H as <-.
    eapply T_App.
    + apply IHea1. exact E1.
    + apply IHea2. exact E2.
  (* EAPair *)
  - destruct (typecheck_ann Gamma ea1) as [T1 |] eqn:E1; [| discriminate].
    destruct (typecheck_ann Gamma ea2) as [T2 |] eqn:E2; [| discriminate].
    injection H as <-.
    apply T_Pair.
    + apply IHea1. exact E1.
    + apply IHea2. exact E2.
  (* EAFst *)
  - destruct (typecheck_ann Gamma ea) as [Te |] eqn:Ee; [| discriminate].
    destruct Te; try discriminate.
    injection H as <-.
    eapply T_Fst. apply IHea. exact Ee.
  (* EASnd *)
  - destruct (typecheck_ann Gamma ea) as [Te |] eqn:Ee; [| discriminate].
    destruct Te; try discriminate.
    injection H as <-.
    eapply T_Snd. apply IHea. exact Ee.
  (* EAObserve *)
  - destruct (typecheck_ann Gamma ea) as [Te |] eqn:Ee; [| discriminate].
    destruct Te; try discriminate.
    injection H as <-.
    apply T_Observe. apply IHea. exact Ee.
  (* EAResolve *)
  - apply T_Resolve. apply IHea. exact H.
Qed.

(** ================================================================= *)
(** ** 8. Annotated Equation Lemmas                                    *)
(** ================================================================= *)

Lemma typecheck_ann_var : forall Gamma x,
  typecheck_ann Gamma (EAVar x) = nth_error Gamma x.
Proof. intros. reflexivity. Qed.

Lemma typecheck_ann_const : forall Gamma n,
  typecheck_ann Gamma (EAConst n) = Some TyNat.
Proof. intros. reflexivity. Qed.

Lemma typecheck_ann_system : forall Gamma L,
  typecheck_ann Gamma (EASystem L) = Some (TySystem L).
Proof. intros. reflexivity. Qed.

Lemma typecheck_ann_lam : forall Gamma T1 body T2,
  typecheck_ann (T1 :: Gamma) body = Some T2 ->
  typecheck_ann Gamma (EALamAnn T1 body) = Some (TyArrow T1 T2).
Proof.
  intros Gamma T1 body T2 H. simpl. rewrite H. reflexivity.
Qed.

Lemma typecheck_ann_deterministic : forall Gamma ea T1 T2,
  typecheck_ann Gamma ea = Some T1 ->
  typecheck_ann Gamma ea = Some T2 ->
  T1 = T2.
Proof.
  intros Gamma ea T1 T2 H1 H2. congruence.
Qed.

(** ================================================================= *)
(** ** 9. Concrete Examples                                            *)
(** ================================================================= *)

(** Identity function: lambda(x:Nat). x : Nat -> Nat *)
Example typecheck_identity :
  typecheck_ann [] (EALamAnn TyNat (EAVar 0)) = Some (TyArrow TyNat TyNat).
Proof. reflexivity. Qed.

(** Application: (lambda(x:Nat). x) 42 : Nat *)
Example typecheck_app_identity :
  typecheck_ann [] (EAApp (EALamAnn TyNat (EAVar 0)) (EAConst 42)) = Some TyNat.
Proof.
  simpl. destruct (ty_eq_dec TyNat TyNat) as [_ | H];
  [reflexivity | exfalso; apply H; reflexivity].
Qed.

(** Pair: (42, 7) : Nat * Nat *)
Example typecheck_pair_example :
  typecheck_ann [] (EAPair (EAConst 42) (EAConst 7)) = Some (TyPair TyNat TyNat).
Proof. reflexivity. Qed.

(** Fst (42, 7) : Nat *)
Example typecheck_fst_example :
  typecheck_ann [] (EAFst (EAPair (EAConst 42) (EAConst 7))) = Some TyNat.
Proof. reflexivity. Qed.

(** Nested: lambda(f:Nat->Nat). lambda(x:Nat). f x *)
Example typecheck_nested_lam :
  typecheck_ann []
    (EALamAnn (TyArrow TyNat TyNat)
      (EALamAnn TyNat
        (EAApp (EAVar 1) (EAVar 0))))
  = Some (TyArrow (TyArrow TyNat TyNat) (TyArrow TyNat TyNat)).
Proof.
  simpl. destruct (ty_eq_dec TyNat TyNat) as [_ | H];
  [reflexivity | exfalso; apply H; reflexivity].
Qed.

(** Resolve preserves type *)
Example typecheck_resolve_example :
  typecheck_ann [] (EAResolve (EAConst 42)) = Some TyNat.
Proof. reflexivity. Qed.
