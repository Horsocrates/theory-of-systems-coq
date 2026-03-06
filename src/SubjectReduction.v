(* ======================================================================= *)
(*  THEORY OF SYSTEMS: SUBJECT REDUCTION                                    *)
(*  Status: >=12 Qed, 0 Admitted | Author: Horsocrates | Date: 2026-03-06  *)
(* ======================================================================= *)

From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Lists.List.
Import ListNotations.

From ToS Require Import Expressions.
From ToS Require Import Reduction.
From ToS Require Import Typing_Expr.

(** Beta reduction preserves typing.
    Inversion on T_App gives f-typing and arg-typing.
    Inversion on T_Lam gives body-typing.
    We use eassumption to avoid H-numbering fragility. *)
Lemma step_beta_type : forall Gamma body arg T,
    is_value arg ->
    expr_has_type Gamma (EApp (ELam body) arg) T ->
    expr_has_type Gamma (subst 0 arg body) T.
Proof.
  intros Gamma body arg T Hval Htype.
  inversion Htype; subst.
  (* H2 : expr_has_type Gamma (ELam body) (TyArrow T1 T2) *)
  (* H4 : expr_has_type Gamma arg T1 *)
  inversion H2; subst.
  (* Now: expr_has_type (T0 :: Gamma) body T2, where T0 = T1 *)
  eapply substitution_preserves_typing; eassumption.
Qed.

(** Fst reduction preserves typing. *)
Lemma step_fst_type : forall Gamma v1 v2 T,
    is_value v1 -> is_value v2 ->
    expr_has_type Gamma (EFst (EPair v1 v2)) T ->
    expr_has_type Gamma v1 T.
Proof.
  intros Gamma v1 v2 T Hv1 Hv2 Htype.
  inversion Htype; subst.
  inversion H1; subst.
  assumption.
Qed.

(** Snd reduction preserves typing. *)
Lemma step_snd_type : forall Gamma v1 v2 T,
    is_value v1 -> is_value v2 ->
    expr_has_type Gamma (ESnd (EPair v1 v2)) T ->
    expr_has_type Gamma v2 T.
Proof.
  intros Gamma v1 v2 T Hv1 Hv2 Htype.
  inversion Htype; subst.
  inversion H1; subst.
  assumption.
Qed.

(** Resolve-const reduction preserves typing. *)
Lemma step_resolve_type : forall Gamma n T,
    expr_has_type Gamma (EResolve (EConst n)) T ->
    expr_has_type Gamma (EConst n) T.
Proof.
  intros Gamma n T Htype.
  inversion Htype; subst.
  assumption.
Qed.

(** Observe reduction restricted to the nat case. *)
Lemma step_observe_nat_type : forall Gamma v n,
    is_value v ->
    expr_has_type Gamma (EObserve v n) TyNat ->
    expr_has_type Gamma (EConst n) TyNat.
Proof.
  intros Gamma v n Hval Htype.
  apply T_Const.
Qed.

(** Layer projection: ELayerProject has no typing rule, vacuously false. *)
Lemma step_layer_type : forall Gamma v l T,
    is_value v -> is_value l ->
    expr_has_type Gamma (ELayerProject v l) T ->
    expr_has_type Gamma v T.
Proof.
  intros Gamma v l T Hv Hl Htype.
  inversion Htype.
Qed.

(** Congruence in EApp function position preserves typing. *)
Lemma xi_app_fun_type : forall Gamma e1 e1p e2 T,
    expr_has_type Gamma (EApp e1 e2) T ->
    (forall T2, expr_has_type Gamma e1 T2 -> expr_has_type Gamma e1p T2) ->
    expr_has_type Gamma (EApp e1p e2) T.
Proof.
  intros Gamma e1 e1p e2 T Htype IH.
  inversion Htype; subst.
  eapply T_App.
  - apply IH. eassumption.
  - eassumption.
Qed.

(** Congruence in EApp arg position preserves typing. *)
Lemma xi_app_arg_type : forall Gamma v e2 e2p T,
    is_value v ->
    expr_has_type Gamma (EApp v e2) T ->
    (forall T2, expr_has_type Gamma e2 T2 -> expr_has_type Gamma e2p T2) ->
    expr_has_type Gamma (EApp v e2p) T.
Proof.
  intros Gamma v e2 e2p T Hval Htype IH.
  inversion Htype; subst.
  eapply T_App.
  - eassumption.
  - apply IH. eassumption.
Qed.

(** THE MAIN THEOREM: Subject Reduction.
    Well-typed expressions preserve their type under small-step reduction.

    Note on step_observe: T_Observe gives Gamma |- EObserve e n : T when
    Gamma |- e : TyProcess T. When v is a value with Gamma |- v : TyProcess T,
    inversion on is_value gives VConst/VLam/VPair/VSystem. Each case:
    inversion on the value typing at TyProcess T fails (no rule applies),
    giving False vacuously.

    Note on step_layer and step_layer_inner: ELayerProject has no typing rule,
    so inversion on any typing judgment for ELayerProject closes the goal. *)
Theorem subject_reduction : forall Gamma e ep T,
    expr_has_type Gamma e T ->
    step e ep ->
    expr_has_type Gamma ep T.
Proof.
  intros Gamma e ep T Htype Hstep.
  revert Gamma T Htype.
  induction Hstep; intros Gamma T Htype.
  - (* step_beta: EApp (ELam body) arg -> subst 0 arg body *)
    eapply step_beta_type; eassumption.
  - (* step_fst: EFst (EPair v1 v2) -> v1 *)
    eapply step_fst_type. exact H. exact H0. exact Htype.
  - (* step_snd: ESnd (EPair v1 v2) -> v2 *)
    eapply step_snd_type. exact H. exact H0. exact Htype.
  - (* step_resolve_const: EResolve (EConst n) -> EConst n *)
    apply step_resolve_type. assumption.
  - (* step_observe: EObserve v n -> EConst n.
       Inversion on T_Observe gives Hproc : Gamma |- v : TyProcess T.
       v is a value (H : is_value v); inversion on H gives the value form,
       then inversion on Hproc at TyProcess T gives False. *)
    inversion Htype; subst.
    (* After T_Observe inversion: H0 : expr_has_type Gamma v (TyProcess T) *)
    inversion H; subst; match goal with
      | Hx : expr_has_type _ _ (TyProcess _) |- _ => inversion Hx
    end.
  - (* step_layer: ELayerProject v l -> v. No typing rule: inversion closes. *)
    inversion Htype.
  - (* step_app_fun: EApp e1 e2 -> EApp e1p e2 *)
    inversion Htype; subst.
    eapply T_App.
    + apply IHHstep. eassumption.
    + eassumption.
  - (* step_app_arg: EApp v e2 -> EApp v e2p *)
    inversion Htype; subst.
    eapply T_App.
    + eassumption.
    + apply IHHstep. eassumption.
  - (* step_fst_inner: EFst e -> EFst ep *)
    inversion Htype; subst.
    eapply T_Fst.
    apply IHHstep. eassumption.
  - (* step_snd_inner: ESnd e -> ESnd ep *)
    inversion Htype; subst.
    eapply T_Snd.
    apply IHHstep. eassumption.
  - (* step_pair_left: EPair e1 e2 -> EPair e1p e2 *)
    inversion Htype; subst.
    apply T_Pair.
    + apply IHHstep. eassumption.
    + eassumption.
  - (* step_pair_right: EPair v1 e2 -> EPair v1 e2p *)
    inversion Htype; subst.
    apply T_Pair.
    + eassumption.
    + apply IHHstep. eassumption.
  - (* step_resolve_inner: EResolve e -> EResolve ep *)
    inversion Htype; subst.
    apply T_Resolve.
    apply IHHstep. eassumption.
  - (* step_observe_inner: EObserve e n -> EObserve ep n *)
    inversion Htype; subst.
    apply T_Observe.
    apply IHHstep. eassumption.
  - (* step_layer_inner: ELayerProject e l -> ELayerProject ep l.
       No typing rule for ELayerProject: inversion closes. *)
    inversion Htype.
Qed.

(** Multi-step preservation: type is preserved across zero or more steps. *)
Lemma multi_step_preservation : forall Gamma e e2 T,
    expr_has_type Gamma e T ->
    multi_step e e2 ->
    expr_has_type Gamma e2 T.
Proof.
  intros Gamma e e2 T Htype Hms.
  induction Hms as [| e1 e3 e4 Hstep Hms IH].
  - exact Htype.
  - apply IH.
    apply subject_reduction with e1.
    + exact Htype.
    + exact Hstep.
Qed.

(** Fuel-based evaluation preserves typing. *)
Lemma eval_fuel_preservation : forall fuel Gamma e T,
    expr_has_type Gamma e T ->
    expr_has_type Gamma (eval_fuel fuel e) T.
Proof.
  induction fuel as [| fuel2 IH].
  - intros Gamma e T Htype. simpl. exact Htype.
  - intros Gamma e T Htype.
    simpl.
    destruct (try_step e) as [epp |] eqn:Htry.
    + apply IH.
      apply subject_reduction with e.
      * exact Htype.
      * apply try_step_some_step. exact Htry.
    + exact Htype.
Qed.

(** Subject reduction for empty context (closed terms). *)
Lemma preservation_closed : forall e e2 T,
    expr_has_type [] e T ->
    step e e2 ->
    expr_has_type [] e2 T.
Proof.
  intros e e2 T Htype Hstep.
  apply subject_reduction with e.
  - exact Htype.
  - exact Hstep.
Qed.

(** A well-typed value cannot step. *)
Lemma well_typed_value_no_step : forall Gamma v T,
    is_value v ->
    expr_has_type Gamma v T ->
    forall epp, ~ step v epp.
Proof.
  intros Gamma v T Hval Htype epp Hstep.
  exact (value_no_step_rel v epp Hval Hstep).
Qed.

(** Const always has type TyNat. *)
Lemma const_type_nat : forall Gamma n T,
    expr_has_type Gamma (EConst n) T ->
    T = TyNat.
Proof.
  intros Gamma n T H.
  inversion H. reflexivity.
Qed.

(** Multi-step preserves type for closed terms. *)
Lemma multi_step_preservation_closed : forall e e2 T,
    expr_has_type [] e T ->
    multi_step e e2 ->
    expr_has_type [] e2 T.
Proof.
  intros e e2 T Htype Hms.
  exact (multi_step_preservation [] e e2 T Htype Hms).
Qed.

(** If e is well-typed and reduces to a value, the value has the same type. *)
Lemma reduces_to_value_preserves_type : forall Gamma e v T,
    expr_has_type Gamma e T ->
    multi_step e v ->
    is_value v ->
    expr_has_type Gamma v T.
Proof.
  intros Gamma e v T Htype Hms Hval.
  apply multi_step_preservation with e.
  - exact Htype.
  - exact Hms.
Qed.

(** Two chained steps preserve type. *)
Lemma subject_reduction_chain : forall Gamma e1 e2 e3 T,
    expr_has_type Gamma e1 T ->
    step e1 e2 ->
    step e2 e3 ->
    expr_has_type Gamma e3 T.
Proof.
  intros Gamma e1 e2 e3 T Htype H12 H23.
  apply subject_reduction with e2.
  - apply subject_reduction with e1.
    + exact Htype.
    + exact H12.
  - exact H23.
Qed.
