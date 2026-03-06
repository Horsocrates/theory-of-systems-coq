From Stdlib Require Import Init.Nat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
Import ListNotations.
From ToS Require Import Expressions.
From ToS Require Import Reduction.
From ToS Require Import Typing_Expr.

Inductive is_benign_stuck : Expr -> Prop :=
  | BS_Resolve : forall v,
      is_value v ->
      (forall n, v <> EConst n) ->
      is_benign_stuck (EResolve v)
  | BS_AppFun : forall f a,
      is_benign_stuck f ->
      is_benign_stuck (EApp f a)
  | BS_AppArg : forall v a,
      is_value v ->
      is_benign_stuck a ->
      is_benign_stuck (EApp v a)
  | BS_Fst : forall e,
      is_benign_stuck e ->
      is_benign_stuck (EFst e)
  | BS_Snd : forall e,
      is_benign_stuck e ->
      is_benign_stuck (ESnd e)
  | BS_PairLeft : forall e1 e2,
      is_benign_stuck e1 ->
      is_benign_stuck (EPair e1 e2)
  | BS_PairRight : forall v1 e2,
      is_value v1 ->
      is_benign_stuck e2 ->
      is_benign_stuck (EPair v1 e2)
  | BS_ResolveInner : forall e,
      is_benign_stuck e ->
      is_benign_stuck (EResolve e)
  | BS_ObserveInner : forall e n,
      is_benign_stuck e ->
      is_benign_stuck (EObserve e n)
  .

Definition progress_result (e : Expr) : Prop :=
  is_value e \/ (exists ep, step e ep) \/ is_benign_stuck e.

Lemma empty_ctx_var_impossible : forall x T,
  expr_has_type [] (EVar x) T -> False.
Proof.
  intros x T H.
  inversion H; subst.
  rewrite nth_error_nil in H2.
  discriminate.
Qed.

Lemma no_value_has_process_type : forall Gamma v T,
  is_value v ->
  expr_has_type Gamma v (TyProcess T) ->
  False.
Proof.
  intros Gamma v T Hval Htype.
  inversion Hval; subst; inversion Htype.
Qed.

Lemma no_value_has_layer_type : forall Gamma v T,
  is_value v ->
  expr_has_type Gamma v (TyLayer T) ->
  False.
Proof.
  intros Gamma v T Hval Htype.
  inversion Hval; subst; inversion Htype.
Qed.

Lemma benign_stuck_not_value : forall e,
  is_benign_stuck e ->
  ~ is_value e.
Proof.
  intros e Hbs.
  induction Hbs; intros Hval.
  - inversion Hval.
  - inversion Hval.
  - inversion Hval.
  - inversion Hval.
  - inversion Hval.
  - inversion Hval; subst. apply IHHbs. assumption.
  - inversion Hval; subst. apply IHHbs. assumption.
  - inversion Hval.
  - inversion Hval.
Qed.

Lemma benign_stuck_no_step : forall e ep,
  is_benign_stuck e ->
  ~ step e ep.
Proof.
  intros e ep Hbs Hstep.
  revert ep Hstep.
  induction Hbs; intros ep Hstep; inversion Hstep; subst.
  (* BS_Resolve v: two step cases - step_resolve_const and step_resolve_inner *)
  - (* step_resolve_const: v = EConst n *)
    exact (H0 n eq_refl).
  - (* step_resolve_inner: step v vp -> contradiction (v is value) *)
    eapply value_no_step_rel; eassumption.
  (* BS_AppFun f a: step cases on EApp f a *)
  - (* step_beta: f = ELam body, is_value a, but f is benign_stuck *)
    apply (benign_stuck_not_value _ Hbs (VLam body)).
  - (* step_app_fun: step f fp -> IH *)
    eapply IHHbs; eassumption.
  - (* step_app_arg: is_value f, but f is benign_stuck *)
    eapply benign_stuck_not_value; eassumption.
  (* BS_AppArg v a: step cases on EApp v a *)
  - (* step_beta: is_value a, but a is benign_stuck *)
    eapply benign_stuck_not_value; eassumption.
  - (* step_app_fun: step v vp, but v is_value *)
    eapply value_no_step_rel. exact H. eassumption.
  - (* step_app_arg: step a ap -> IH *)
    eapply IHHbs; eassumption.
  (* BS_Fst e: step cases on EFst e *)
  - (* step_fst: e = EPair v1 v2, both values, but e is benign_stuck *)
    (* After subst, Hbs : is_benign_stuck (EPair v1 v2) *)
    (* step_fst gives us H2 : is_value v1, H3 : is_value v2, and H1 : e = EPair v1 v2 *)
    (* Actually after inversion Hstep for step_fst, we get the equalities subst-ed *)
    (* Hbs : is_benign_stuck e, and e was unified with EPair v1 v2 *)
    (* So Hbs : is_benign_stuck (EPair v1 v2) *)
    inversion Hbs; subst.
    + (* BS_PairLeft: e1 benign_stuck, is_value e1 (=v1) contradiction *)
      eapply benign_stuck_not_value; eassumption.
    + (* BS_PairRight: e2 benign_stuck, is_value e2 (=v2) contradiction *)
      eapply benign_stuck_not_value; eassumption.
  - (* step_fst_inner: step e ep -> IH *)
    eapply IHHbs; eassumption.
  (* BS_Snd e: step cases on ESnd e *)
  - (* step_snd: e = EPair v1 v2 *)
    inversion Hbs; subst.
    + eapply benign_stuck_not_value; eassumption.
    + eapply benign_stuck_not_value; eassumption.
  - (* step_snd_inner: step e ep -> IH *)
    eapply IHHbs; eassumption.
  (* BS_PairLeft e1 e2: step cases on EPair e1 e2 *)
  - (* step_pair_left: step e1 e1p -> IH *)
    eapply IHHbs; eassumption.
  - (* step_pair_right: is_value e1, but e1 benign_stuck *)
    eapply benign_stuck_not_value; eassumption.
  (* BS_PairRight v1 e2: step cases on EPair v1 e2 *)
  - (* step_pair_left: step v1 e1p, but v1 is_value *)
    eapply value_no_step_rel. exact H. eassumption.
  - (* step_pair_right: step e2 e2p -> IH *)
    eapply IHHbs; eassumption.
  (* BS_ResolveInner e: step cases on EResolve e *)
  - (* step_resolve_const: e = EConst n, but EConst n is value and e is benign_stuck *)
    apply (benign_stuck_not_value _ Hbs (VConst n)).
  - (* step_resolve_inner: step e ep -> IH *)
    eapply IHHbs; eassumption.
  (* BS_ObserveInner e n: step cases on EObserve e n *)
  - (* step_observe: is_value e, but e is benign_stuck *)
    eapply benign_stuck_not_value; eassumption.
  - (* step_observe_inner: step e ep -> IH *)
    eapply IHHbs; eassumption.
Qed.


(* Helper: progress for any empty-context derivation, proved by induction
   on the typing derivation with Gamma as a free variable that we then
   specialize to []. *)
Lemma progress_general : forall Gamma e T,
  Gamma = [] ->
  expr_has_type Gamma e T ->
  progress_result e.
Proof.
  intros Gamma e T HGamma Htype.
  induction Htype.
  (* T_Var: Gamma = [], nth_error [] x = None -- contradiction *)
  - subst Gamma. rewrite nth_error_nil in H. discriminate.
  (* T_Const *)
  - left. apply VConst.
  (* T_Lam *)
  - left. apply VLam.
  (* T_App *)
  - unfold progress_result in *.
    pose proof (IHHtype1 HGamma) as PR1.
    pose proof (IHHtype2 HGamma) as PR2.
    destruct PR1 as [Hfv | [[fp Hfstep] | Hfbs]].
    + destruct (canonical_arrow Gamma f T1 T2 Hfv Htype1) as [body Hbody].
      subst f.
      destruct PR2 as [Hav | [[ap Hastep] | Habs]].
      * right. left. exists (subst 0 a body). apply step_beta. exact Hav.
      * right. left. exists (EApp (ELam body) ap).
        apply step_app_arg. apply VLam. exact Hastep.
      * right. right. apply BS_AppArg. apply VLam. exact Habs.
    + right. left. exists (EApp fp a). apply step_app_fun. exact Hfstep.
    + right. right. apply BS_AppFun. exact Hfbs.
  (* T_Pair *)
  - unfold progress_result in *.
    pose proof (IHHtype1 HGamma) as PR1.
    pose proof (IHHtype2 HGamma) as PR2.
    destruct PR1 as [Hv1 | [[e1p Hstep1] | Hbs1]].
    + destruct PR2 as [Hv2 | [[e2p Hstep2] | Hbs2]].
      * left. apply VPair; assumption.
      * right. left. exists (EPair e1 e2p). apply step_pair_right; assumption.
      * right. right. apply BS_PairRight; assumption.
    + right. left. exists (EPair e1p e2). apply step_pair_left. exact Hstep1.
    + right. right. apply BS_PairLeft. exact Hbs1.
  (* T_Fst *)
  - unfold progress_result in *.
    pose proof (IHHtype HGamma) as PR.
    destruct PR as [Hv | [[ep Hstep] | Hbs]].
    + destruct (canonical_pair Gamma e T1 T2 Hv Htype) as [v1 [v2 [Heq [Hv1 Hv2]]]].
      subst e. right. left. exists v1. apply step_fst; assumption.
    + right. left. exists (EFst ep). apply step_fst_inner. exact Hstep.
    + right. right. apply BS_Fst. exact Hbs.
  (* T_Snd *)
  - unfold progress_result in *.
    pose proof (IHHtype HGamma) as PR.
    destruct PR as [Hv | [[ep Hstep] | Hbs]].
    + destruct (canonical_pair Gamma e T1 T2 Hv Htype) as [v1 [v2 [Heq [Hv1 Hv2]]]].
      subst e. right. left. exists v2. apply step_snd; assumption.
    + right. left. exists (ESnd ep). apply step_snd_inner. exact Hstep.
    + right. right. apply BS_Snd. exact Hbs.
  (* T_Observe *)
  - unfold progress_result in *.
    pose proof (IHHtype HGamma) as PR.
    destruct PR as [Hv | [[ep Hstep] | Hbs]].
    + right. left. exists (EConst n). apply step_observe. exact Hv.
    + right. left. exists (EObserve ep n). apply step_observe_inner. exact Hstep.
    + right. right. apply BS_ObserveInner. exact Hbs.
  (* T_Resolve *)
  - unfold progress_result in *.
    pose proof (IHHtype HGamma) as PR.
    destruct PR as [Hv | [[ep Hstep] | Hbs]].
    + destruct T as [| L | T1 T2 | T1 T2 | Tp | Tl].
      * destruct (canonical_nat Gamma e Hv Htype) as [n Hn]. subst e.
        right. left. exists (EConst n). apply step_resolve_const.
      * right. right. apply BS_Resolve. exact Hv.
        intros n. inversion Hv; subst; inversion Htype; subst; discriminate.
      * right. right. apply BS_Resolve. exact Hv.
        intros n. inversion Hv; subst; inversion Htype; subst; discriminate.
      * right. right. apply BS_Resolve. exact Hv.
        intros n. inversion Hv; subst; inversion Htype; subst; discriminate.
      * exfalso. eapply no_value_has_process_type. exact Hv. exact Htype.
      * exfalso. eapply no_value_has_layer_type. exact Hv. exact Htype.
    + right. left. exists (EResolve ep). apply step_resolve_inner. exact Hstep.
    + right. right. apply BS_ResolveInner. exact Hbs.
  (* T_System *)
  - left. apply VSystem.
Qed.

Theorem progress : forall e T,
  expr_has_type [] e T ->
  progress_result e.
Proof.
  intros e T Htype.
  exact (progress_general [] e T eq_refl Htype).
Qed.

Theorem no_unexpected_stuck : forall e T,
  expr_has_type [] e T ->
  ~ is_value e ->
  ~ (exists ep, step e ep) ->
  is_benign_stuck e.
Proof.
  intros e T Htype Hnval Hnstep.
  destruct (progress e T Htype) as [Hval | [Hstep | Hbs]].
  - contradiction.
  - exfalso. apply Hnstep. exact Hstep.
  - exact Hbs.
Qed.

Lemma progress_const_ok : forall n, progress_result (EConst n).
Proof. intros n. left. apply VConst. Qed.

Lemma progress_system_ok : forall L, progress_result (ESystem L).
Proof. intros L. left. apply VSystem. Qed.

Lemma progress_lam_ok : forall body, progress_result (ELam body).
Proof. intros body. left. apply VLam. Qed.

Lemma progress_observe_value : forall v n,
  is_value v -> exists ep, step (EObserve v n) ep.
Proof.
  intros v n Hval. exists (EConst n). apply step_observe. exact Hval.
Qed.

Lemma progress_resolve_const : forall n,
  exists ep, step (EResolve (EConst n)) ep.
Proof. intros n. exists (EConst n). apply step_resolve_const. Qed.

Lemma progress_fst_pair : forall v1 v2,
  is_value v1 -> is_value v2 ->
  exists ep, step (EFst (EPair v1 v2)) ep.
Proof.
  intros v1 v2 Hv1 Hv2. exists v1. apply step_fst; assumption.
Qed.

Lemma progress_snd_pair : forall v1 v2,
  is_value v1 -> is_value v2 ->
  exists ep, step (ESnd (EPair v1 v2)) ep.
Proof.
  intros v1 v2 Hv1 Hv2. exists v2. apply step_snd; assumption.
Qed.

Lemma progress_beta : forall body v,
  is_value v -> exists ep, step (EApp (ELam body) v) ep.
Proof.
  intros body v Hval.
  exists (subst 0 v body). apply step_beta. exact Hval.
Qed.

Theorem progress_exclusive : forall e T,
  expr_has_type [] e T ->
  (is_value e -> ~ (exists ep, step e ep)) /\
  (is_value e -> ~ is_benign_stuck e) /\
  ((exists ep, step e ep) -> ~ is_benign_stuck e).
Proof.
  intros e T _Htype. repeat split.
  - intros Hval [ep Hstep]. exact (value_no_step_rel e ep Hval Hstep).
  - intros Hval Hbs. exact (benign_stuck_not_value e Hbs Hval).
  - intros [ep Hstep] Hbs. exact (benign_stuck_no_step e ep Hbs Hstep).
Qed.
