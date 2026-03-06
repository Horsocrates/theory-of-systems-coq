(* =================================================================== *)
(*  THEORY OF SYSTEMS: SMALL-STEP OPERATIONAL SEMANTICS FOR ToS-LANG   *)
(*  Status: >=18 Qed, 0 Admitted | Author: Horsocrates | 2026-03-06    *)
(* =================================================================== *)

From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import micromega.Lia.
From ToS Require Import Expressions.

Inductive step : Expr -> Expr -> Prop :=
  | step_beta : forall body arg,
      is_value arg ->
      step (EApp (ELam body) arg) (subst 0 arg body)
  | step_fst : forall v1 v2,
      is_value v1 -> is_value v2 ->
      step (EFst (EPair v1 v2)) v1
  | step_snd : forall v1 v2,
      is_value v1 -> is_value v2 ->
      step (ESnd (EPair v1 v2)) v2
  | step_resolve_const : forall n,
      step (EResolve (EConst n)) (EConst n)
  | step_observe : forall v n,
      is_value v ->
      step (EObserve v n) (EConst n)
  | step_layer : forall v l,
      is_value v -> is_value l ->
      step (ELayerProject v l) v
  | step_app_fun : forall e1 e1p e2,
      step e1 e1p ->
      step (EApp e1 e2) (EApp e1p e2)
  | step_app_arg : forall v e2 e2p,
      is_value v -> step e2 e2p ->
      step (EApp v e2) (EApp v e2p)
  | step_fst_inner : forall e ep,
      step e ep ->
      step (EFst e) (EFst ep)
  | step_snd_inner : forall e ep,
      step e ep ->
      step (ESnd e) (ESnd ep)
  | step_pair_left : forall e1 e1p e2,
      step e1 e1p ->
      step (EPair e1 e2) (EPair e1p e2)
  | step_pair_right : forall v1 e2 e2p,
      is_value v1 -> step e2 e2p ->
      step (EPair v1 e2) (EPair v1 e2p)
  | step_resolve_inner : forall e ep,
      step e ep ->
      step (EResolve e) (EResolve ep)
  | step_observe_inner : forall e ep n,
      step e ep ->
      step (EObserve e n) (EObserve ep n)
  | step_layer_inner : forall e ep l,
      step e ep ->
      step (ELayerProject e l) (ELayerProject ep l)
  .

Inductive multi_step : Expr -> Expr -> Prop :=
  | ms_refl : forall e, multi_step e e
  | ms_step : forall e1 e2 e3,
      step e1 e2 -> multi_step e2 e3 -> multi_step e1 e3.

Fixpoint try_step (e : Expr) : option Expr :=
  match e with
  | EConst _  => None
  | ELam _    => None
  | ESystem _ => None
  | EPair e1 e2 =>
      match is_value_dec e1 with
      | left  _  =>
          match is_value_dec e2 with
          | left  _  => None
          | right _  =>
              match try_step e2 with
              | Some e2p => Some (EPair e1 e2p)
              | None     => None
              end
          end
      | right _ =>
          match try_step e1 with
          | Some e1p => Some (EPair e1p e2)
          | None     => None
          end
      end
  | EApp e1 e2 =>
      match is_value_dec e1 with
      | left Hv1 =>
          match e1 with
          | ELam body =>
              match is_value_dec e2 with
              | left _   => Some (subst 0 e2 body)
              | right _  =>
                  match try_step e2 with
                  | Some e2p => Some (EApp e1 e2p)
                  | None     => None
                  end
              end
          | _ =>
              match try_step e2 with
              | Some e2p => Some (EApp e1 e2p)
              | None     => None
              end
          end
      | right _ =>
          match try_step e1 with
          | Some e1p => Some (EApp e1p e2)
          | None     => None
          end
      end
  | EFst inner =>
      match inner with
      | EPair v1 v2 =>
          match is_value_dec v1, is_value_dec v2 with
          | left _, left _ => Some v1
          | _, _           =>
              match try_step inner with
              | Some innerp => Some (EFst innerp)
              | None        => None
              end
          end
      | _ =>
          match try_step inner with
          | Some innerp => Some (EFst innerp)
          | None        => None
          end
      end
  | ESnd inner =>
      match inner with
      | EPair v1 v2 =>
          match is_value_dec v1, is_value_dec v2 with
          | left _, left _ => Some v2
          | _, _           =>
              match try_step inner with
              | Some innerp => Some (ESnd innerp)
              | None        => None
              end
          end
      | _ =>
          match try_step inner with
          | Some innerp => Some (ESnd innerp)
          | None        => None
          end
      end
  | EResolve inner =>
      match inner with
      | EConst n => Some (EConst n)
      | _ =>
          match try_step inner with
          | Some innerp => Some (EResolve innerp)
          | None        => None
          end
      end
  | EObserve inner n =>
      match is_value_dec inner with
      | left  _ => Some (EConst n)
      | right _ =>
          match try_step inner with
          | Some innerp => Some (EObserve innerp n)
          | None        => None
          end
      end
  | ELayerProject e1 l =>
      match is_value_dec e1, is_value_dec l with
      | left _, left _ => Some e1
      | _, _           =>
          match try_step e1 with
          | Some e1p => Some (ELayerProject e1p l)
          | None     => None
          end
      end
  | EVar _  => None
  | EElem _ => None
  end.

Fixpoint eval_fuel (fuel : nat) (e : Expr) : Expr :=
  match fuel with
  | O => e
  | S fuelp =>
      match try_step e with
      | Some ep => eval_fuel fuelp ep
      | None    => e
      end
  end.


(* === Helpers for try_step (EApp ...) proofs === *)
(* The key: 'change X with Y' works when X and Y are definitionally equal. *)
(* This lets us replace try_step (EApp ...) with the explicit match form. *)

(* Template for change: try_step (EApp (ELam body) e2) *)
Definition try_step_app_lam_rhs (body e2 : Expr) :=
  match is_value_dec (ELam body) with
  | left _ => match is_value_dec e2 with
      | left _  => Some (subst 0 e2 body)
      | right _ => match try_step e2 with
          | Some e2p => Some (EApp (ELam body) e2p) | None => None end
      end
  | right _ => match try_step (ELam body) with
      | Some e1p => Some (EApp e1p e2) | None => None end
  end.

Lemma try_step_app_lam_eq : forall body e2,
  try_step (EApp (ELam body) e2) = try_step_app_lam_rhs body e2.
Proof. intros body e2. unfold try_step_app_lam_rhs. simpl. reflexivity. Qed.

Lemma try_step_app_lam_val : forall body e2,
  is_value e2 ->
  try_step (EApp (ELam body) e2) = Some (subst 0 e2 body).
Proof.
  intros body e2 Hv.
  rewrite try_step_app_lam_eq. unfold try_step_app_lam_rhs.
  destruct (is_value_dec (ELam body)) as [Hvl|HnvL] eqn:Heql; simpl.
  - destruct (is_value_dec e2) as [Hv2|Hnv2] eqn:Heq2; simpl.
    + reflexivity.
    + exfalso. apply Hnv2. exact Hv.
  - exfalso. apply HnvL. apply VLam.
Qed.

Lemma try_step_app_lam_step : forall body e2 e2p,
  ~ is_value e2 ->
  try_step e2 = Some e2p ->
  try_step (EApp (ELam body) e2) = Some (EApp (ELam body) e2p).
Proof.
  intros body e2 e2p Hnv Hstep.
  rewrite try_step_app_lam_eq. unfold try_step_app_lam_rhs.
  destruct (is_value_dec (ELam body)) as [Hvl|HnvL] eqn:Heql; simpl.
  - destruct (is_value_dec e2) as [Hv2|Hnv2] eqn:Heq2; simpl.
    + exfalso. apply Hnv. exact Hv2.
    + rewrite Hstep. reflexivity.
  - exfalso. apply HnvL. apply VLam.
Qed.

Lemma try_step_app_lam_stuck : forall body e2,
  ~ is_value e2 ->
  try_step e2 = None ->
  try_step (EApp (ELam body) e2) = None.
Proof.
  intros body e2 Hnv Hstuck.
  rewrite try_step_app_lam_eq. unfold try_step_app_lam_rhs.
  destruct (is_value_dec (ELam body)) as [Hvl|HnvL] eqn:Heql; simpl.
  - destruct (is_value_dec e2) as [Hv2|Hnv2] eqn:Heq2; simpl.
    + exfalso. apply Hnv. exact Hv2.
    + rewrite Hstuck. reflexivity.
  - exfalso. apply HnvL. apply VLam.
Qed.


(* Equations for non-ELam e1 forms, used in try_step_some_step *)
(* For non-value e1 forms: try_step (EApp e1 e2) depends on try_step e1 *)
(* For value e1 (ESystem/EPair/EConst): try_step (EApp v e2) = match try_step e2 with ... *)

Definition try_step_app_nval_rhs (e1 e2 : Expr) :=
  match try_step e1 with
  | Some e1p => Some (EApp e1p e2)
  | None     => None
  end.

Lemma try_step_value_none : forall v,
  is_value v -> try_step v = None.
Proof.
  intros v Hv.
  inversion Hv; subst; simpl.
  - reflexivity.
  - reflexivity.
  - destruct (is_value_dec v1) as [Hv1p | Hnv1].
    + destruct (is_value_dec v2) as [Hv2p | Hnv2].
      * reflexivity.
      * contradiction.
    + contradiction.
  - reflexivity.
Qed.

Lemma eval_fuel_zero : forall e, eval_fuel 0 e = e.
Proof. intros e. simpl. reflexivity. Qed.

Lemma eval_fuel_value : forall fuel v,
  is_value v -> eval_fuel fuel v = v.
Proof.
  intros fuel v Hv.
  destruct fuel as [| fuelp].
  - simpl. reflexivity.
  - simpl. rewrite try_step_value_none. reflexivity. exact Hv.
Qed.

Lemma eval_fuel_terminates : forall e fuel,
  exists v, eval_fuel fuel e = v.
Proof.
  intros e fuel. exists (eval_fuel fuel e). reflexivity.
Qed.

(* Transparent definition for try_step on EFst (EPair ...) *)
Definition try_step_fst_pair_rhs (e1 e2 : Expr) : option Expr :=
  match is_value_dec e1, is_value_dec e2 with
  | left _, left _ => Some e1
  | _, _ => match try_step (EPair e1 e2) with
             | Some ip => Some (EFst ip)
             | None    => None
             end
  end.

Lemma try_step_fst_pair_eq : forall e1 e2,
  try_step (EFst (EPair e1 e2)) = try_step_fst_pair_rhs e1 e2.
Proof. intros. unfold try_step_fst_pair_rhs. simpl. reflexivity. Qed.

Lemma try_step_fst_pair : forall e1 e2 ep,
  try_step (EFst (EPair e1 e2)) = Some ep ->
  (is_value e1 /\ is_value e2 /\ ep = e1) \/
  (exists ip, try_step (EPair e1 e2) = Some ip /\ ep = EFst ip).
Proof.
  intros e1 e2 ep H.
  rewrite try_step_fst_pair_eq in H.
  unfold try_step_fst_pair_rhs in H.
  cbv beta in H.
  destruct (is_value_dec e1) as [Hv1|Hnv1];
  destruct (is_value_dec e2) as [Hv2|Hnv2];
  cbv beta iota in H.
  - left. split. exact Hv1. split. exact Hv2. congruence.
  - destruct (try_step (EPair e1 e2)) as [ip|] eqn:Hip;
    cbv beta iota in H;
    [ right; exists ip; split; [reflexivity | congruence] | discriminate ].
  - destruct (try_step (EPair e1 e2)) as [ip|] eqn:Hip;
    cbv beta iota in H;
    [ right; exists ip; split; [reflexivity | congruence] | discriminate ].
  - destruct (try_step (EPair e1 e2)) as [ip|] eqn:Hip;
    cbv beta iota in H;
    [ right; exists ip; split; [reflexivity | congruence] | discriminate ].
Qed.

Definition try_step_snd_pair_rhs (e1 e2 : Expr) : option Expr :=
  match is_value_dec e1, is_value_dec e2 with
  | left _, left _ => Some e2
  | _, _ => match try_step (EPair e1 e2) with
             | Some ip => Some (ESnd ip)
             | None    => None
             end
  end.

Lemma try_step_snd_pair_eq : forall e1 e2,
  try_step (ESnd (EPair e1 e2)) = try_step_snd_pair_rhs e1 e2.
Proof. intros. unfold try_step_snd_pair_rhs. simpl. reflexivity. Qed.

Lemma try_step_snd_pair : forall e1 e2 ep,
  try_step (ESnd (EPair e1 e2)) = Some ep ->
  (is_value e1 /\ is_value e2 /\ ep = e2) \/
  (exists ip, try_step (EPair e1 e2) = Some ip /\ ep = ESnd ip).
Proof.
  intros e1 e2 ep H.
  rewrite try_step_snd_pair_eq in H.
  unfold try_step_snd_pair_rhs in H.
  cbv beta in H.
  destruct (is_value_dec e1) as [Hv1|Hnv1];
  destruct (is_value_dec e2) as [Hv2|Hnv2];
  cbv beta iota in H.
  - left. split. exact Hv1. split. exact Hv2. congruence.
  - destruct (try_step (EPair e1 e2)) as [ip|] eqn:Hip;
    cbv beta iota in H;
    [ right; exists ip; split; [reflexivity | congruence] | discriminate ].
  - destruct (try_step (EPair e1 e2)) as [ip|] eqn:Hip;
    cbv beta iota in H;
    [ right; exists ip; split; [reflexivity | congruence] | discriminate ].
  - destruct (try_step (EPair e1 e2)) as [ip|] eqn:Hip;
    cbv beta iota in H;
    [ right; exists ip; split; [reflexivity | congruence] | discriminate ].
Qed.

Lemma try_step_some_step : forall e ep,
  try_step e = Some ep -> step e ep.
Proof.
  induction e; intros ep H; try (simpl in H; discriminate).
  (* EApp e1 e2 *)
  - simpl in H.
    destruct (is_value_dec e1) as [Hv1|Hnv1].
    + simpl in H.
      destruct e1 as [n1 | Lv1 | e1a | f1 aa1 | body1 | p1a p1b | ef1 | es1 | eobs1 nn1 | er1 | elp1 el1 | cn1];
      try (exfalso; inversion Hv1; fail).
      * destruct (try_step e2) as [e2r|] eqn:He2r.
        -- injection H as <-. apply step_app_arg. exact Hv1. apply IHe2. reflexivity.
        -- discriminate.
      * destruct (is_value_dec e2) as [Hv2|Hnv2].
        -- simpl in H. injection H as <-. apply step_beta. exact Hv2.
        -- simpl in H.
           destruct (try_step e2) as [e2r|] eqn:He2r.
           ++ injection H as <-. apply step_app_arg. apply VLam. apply IHe2. reflexivity.
           ++ discriminate.
      * destruct (try_step e2) as [e2r|] eqn:He2r.
        -- injection H as <-. apply step_app_arg. exact Hv1. apply IHe2. reflexivity.
        -- discriminate.
      * destruct (try_step e2) as [e2r|] eqn:He2r.
        -- injection H as <-. apply step_app_arg. exact Hv1. apply IHe2. reflexivity.
        -- discriminate.
    + destruct (try_step e1) as [e1r|] eqn:He1r.
      * injection H as <-. apply step_app_fun. apply IHe1. reflexivity.
      * discriminate.
  (* EPair e1 e2 *)
  - simpl in H.
    destruct (is_value_dec e1) as [Hv1 | Hnv1].
    + simpl in H.
      destruct (is_value_dec e2) as [Hv2 | Hnv2].
      * simpl in H. discriminate.
      * simpl in H.
        destruct (try_step e2) as [e2a|] eqn:He2.
        -- injection H as <-.
           apply step_pair_right. exact Hv1. apply IHe2. reflexivity.
        -- discriminate.
    + simpl in H.
      destruct (try_step e1) as [e1a|] eqn:He1.
      * injection H as <-. apply step_pair_left. apply IHe1. reflexivity.
      * discriminate.
  (* EFst e *)
  - simpl in H.
    destruct e as [v | Lv | e1a | f aa | body | ef1 ef2 | ei1 | ei2 | eobs nobn | er | el1 el2 | cn].
    all: try discriminate.
    + (* EApp f aa *)
      destruct (try_step (EApp f aa)) as [ip|] eqn:Hinner; cbv beta iota in H;
      [ injection H as <-; apply step_fst_inner; apply IHe; reflexivity | discriminate ].
    + (* EPair ef1 ef2 *)
      case_eq (is_value_dec ef1); [intros Hv1 Heq1 | intros Hnv1 Heq1];
      rewrite Heq1 in H; cbv beta iota in H.
      * (* ef1 is value: H has is_value_dec ef2 *)
        case_eq (is_value_dec ef2); [intros Hv2 Heq2 | intros Hnv2 Heq2];
        rewrite Heq2 in H; cbv beta iota in H.
        -- (* both values: H = Some ef1 = Some ep *) injection H as <-. apply step_fst; assumption.
        -- (* Hv1, not Hv2: H = match try_step (EPair ef1 ef2) with ... end *)
           destruct (try_step (EPair ef1 ef2)) as [pp|] eqn:Hp; cbv beta iota in H;
           [ injection H as <-; apply step_fst_inner; apply IHe; reflexivity | discriminate ].
      * (* ef1 not value: H = match try_step (EPair ef1 ef2) with ... end already *)
        destruct (try_step (EPair ef1 ef2)) as [pp|] eqn:Hp; cbv beta iota in H;
        [ injection H as <-; apply step_fst_inner; apply IHe; reflexivity | discriminate ].
    + (* EFst ei1 *)
      destruct (try_step (EFst ei1)) as [ip|] eqn:Hinner; cbv beta iota in H;
      [ injection H as <-; apply step_fst_inner; apply IHe; reflexivity | discriminate ].
    + (* ESnd ei2 *)
      destruct (try_step (ESnd ei2)) as [ip|] eqn:Hinner; cbv beta iota in H;
      [ injection H as <-; apply step_fst_inner; apply IHe; reflexivity | discriminate ].
    + (* EObserve eobs nobn *)
      destruct (try_step (EObserve eobs nobn)) as [ip|] eqn:Hinner; cbv beta iota in H;
      [ injection H as <-; apply step_fst_inner; apply IHe; reflexivity | discriminate ].
    + (* EResolve er *)
      destruct (try_step (EResolve er)) as [ip|] eqn:Hinner; cbv beta iota in H;
      [ injection H as <-; apply step_fst_inner; apply IHe; reflexivity | discriminate ].
    + (* ELayerProject el1 el2 *)
      destruct (try_step (ELayerProject el1 el2)) as [ip|] eqn:Hinner; cbv beta iota in H;
      [ injection H as <-; apply step_fst_inner; apply IHe; reflexivity | discriminate ].
  (* ESnd e *)
  - simpl in H.
    destruct e as [v | Lv | e1a | f aa | body | ef1 ef2 | ei1 | ei2 | eobs nobn | er | el1 el2 | cn].
    all: try discriminate.
    + (* EApp f aa *)
      destruct (try_step (EApp f aa)) as [ip|] eqn:Hinner; cbv beta iota in H;
      [ injection H as <-; apply step_snd_inner; apply IHe; reflexivity | discriminate ].
    + (* EPair ef1 ef2 *)
      case_eq (is_value_dec ef1); [intros Hv1 Heq1 | intros Hnv1 Heq1];
      rewrite Heq1 in H; cbv beta iota in H.
      * (* ef1 is value: H has is_value_dec ef2 *)
        case_eq (is_value_dec ef2); [intros Hv2 Heq2 | intros Hnv2 Heq2];
        rewrite Heq2 in H; cbv beta iota in H.
        -- (* both values: H = Some ef1 = Some ep *) injection H as <-. apply step_snd; assumption.
        -- (* Hv1, not Hv2: H = match try_step (EPair ef1 ef2) with ... end *)
           destruct (try_step (EPair ef1 ef2)) as [pp|] eqn:Hp; cbv beta iota in H;
           [ injection H as <-; apply step_snd_inner; apply IHe; reflexivity | discriminate ].
      * (* ef1 not value: H = match try_step (EPair ef1 ef2) with ... end already *)
        destruct (try_step (EPair ef1 ef2)) as [pp|] eqn:Hp; cbv beta iota in H;
        [ injection H as <-; apply step_snd_inner; apply IHe; reflexivity | discriminate ].
    + (* EFst ei1 *)
      destruct (try_step (EFst ei1)) as [ip|] eqn:Hinner; cbv beta iota in H;
      [ injection H as <-; apply step_snd_inner; apply IHe; reflexivity | discriminate ].
    + (* ESnd ei2 *)
      destruct (try_step (ESnd ei2)) as [ip|] eqn:Hinner; cbv beta iota in H;
      [ injection H as <-; apply step_snd_inner; apply IHe; reflexivity | discriminate ].
    + (* EObserve eobs nobn *)
      destruct (try_step (EObserve eobs nobn)) as [ip|] eqn:Hinner; cbv beta iota in H;
      [ injection H as <-; apply step_snd_inner; apply IHe; reflexivity | discriminate ].
    + (* EResolve er *)
      destruct (try_step (EResolve er)) as [ip|] eqn:Hinner; cbv beta iota in H;
      [ injection H as <-; apply step_snd_inner; apply IHe; reflexivity | discriminate ].
    + (* ELayerProject el1 el2 *)
      destruct (try_step (ELayerProject el1 el2)) as [ip|] eqn:Hinner; cbv beta iota in H;
      [ injection H as <-; apply step_snd_inner; apply IHe; reflexivity | discriminate ].
  (* EObserve e n *)
  - simpl in H.
    destruct (is_value_dec e) as [Hv | Hnv].
    + simpl in H. injection H as <-. apply step_observe. exact Hv.
    + simpl in H.
      destruct (try_step e) as [e_inner|] eqn:Hinner.
      * injection H as <-. apply step_observe_inner. apply IHe. reflexivity.
      * discriminate.
  (* EResolve e *)
  - simpl in H.
    destruct e as [v | Lv | e1a | f aa | body | e1 e2 | e1 | e1 | e1 n | e1 | e1 l | n].
    all: try discriminate.
    (* EApp f aa *)
    + destruct (try_step (EApp f aa)) as [ip|] eqn:Hinner; cbv beta iota in H;
      [ injection H as <-; apply step_resolve_inner; apply IHe; reflexivity | discriminate ].
    (* EPair e1 e2 *)
    + destruct (try_step (EPair e1 e2)) as [ip|] eqn:Hinner; cbv beta iota in H;
      [ injection H as <-; apply step_resolve_inner; apply IHe; reflexivity | discriminate ].
    (* EFst e1 *)
    + destruct (try_step (EFst e1)) as [ip|] eqn:Hinner; cbv beta iota in H;
      [ injection H as <-; apply step_resolve_inner; apply IHe; reflexivity | discriminate ].
    (* ESnd e1 *)
    + destruct (try_step (ESnd e1)) as [ip|] eqn:Hinner; cbv beta iota in H;
      [ injection H as <-; apply step_resolve_inner; apply IHe; reflexivity | discriminate ].
    (* EObserve e1 n *)
    + destruct (try_step (EObserve e1 n)) as [ip|] eqn:Hinner; cbv beta iota in H;
      [ injection H as <-; apply step_resolve_inner; apply IHe; reflexivity | discriminate ].
    (* EResolve e1 *)
    + destruct (try_step (EResolve e1)) as [ip|] eqn:Hinner; cbv beta iota in H;
      [ injection H as <-; apply step_resolve_inner; apply IHe; reflexivity | discriminate ].
    (* ELayerProject e1 l *)
    + destruct (try_step (ELayerProject e1 l)) as [ip|] eqn:Hinner; cbv beta iota in H;
      [ injection H as <-; apply step_resolve_inner; apply IHe; reflexivity | discriminate ].
    (* EConst n: try_step (EResolve (EConst n)) = Some (EConst n) *)
    + cbv beta iota in H. injection H as <-. apply step_resolve_const.
  (* ELayerProject e1 e2 *)
  - simpl in H.
    destruct (is_value_dec e1) as [Hv1 | Hnv1].
    + cbv beta iota in H.
      destruct (is_value_dec e2) as [Hv2 | Hnv2].
      * cbv beta iota in H. injection H as <-. apply step_layer; assumption.
      * cbv beta iota in H.
        destruct (try_step e1) as [e1i|] eqn:Hinner; cbv beta iota in H;
        [ injection H as <-; apply step_layer_inner; apply IHe1; reflexivity | discriminate ].
    + cbv beta iota in H.
      destruct (try_step e1) as [e1i|] eqn:Hinner; cbv beta iota in H;
      [ injection H as <-; apply step_layer_inner; apply IHe1; reflexivity | discriminate ].
Qed.

Lemma value_no_step_rel : forall v ep,
  is_value v -> ~ step v ep.
Proof.
  intros v ep Hv Hstep.
  revert Hv.
  induction Hstep; intros Hv; inversion Hv; subst.
  all: (apply IHHstep; assumption) + assumption.
Qed.

(* Macro: derive False from a step on a value found in context *)
Local Ltac step_val_contra :=
  exfalso;
  match goal with
  | Hs : step ?v _, Hv : is_value ?v |- _ =>
    exact (value_no_step_rel _ _ Hv Hs)
  | Hs : step (ELam _) _ |- _ =>
    apply (value_no_step_rel _ _ (VLam _) Hs)
  | Hs : step (EConst _) _ |- _ =>
    apply (value_no_step_rel _ _ (VConst _) Hs)
  | Hs : step (ESystem _) _ |- _ =>
    apply (value_no_step_rel _ _ (VSystem _) Hs)
  | Hs : step (EPair ?e1 ?e2) _, Hv1 : is_value ?e1, Hv2 : is_value ?e2 |- _ =>
    apply (value_no_step_rel _ _ (VPair e1 e2 Hv1 Hv2) Hs)
  end.

(* Apply the induction hypothesis: rewrite ep1 to ep2 using IH *)
Local Ltac use_ih :=
  match goal with
  | IH : forall ep2, step ?e ep2 -> ?ep1 = ep2, H : step ?e _ |- _ =>
    rewrite (IH _ H); reflexivity
  end.

Lemma step_deterministic : forall e ep1 ep2,
  step e ep1 -> step e ep2 -> ep1 = ep2.
Proof.
  intros e ep1 ep2 H1 H2.
  revert ep2 H2.
  induction H1; intros ep2 H2; inversion H2; subst.
  all: try reflexivity.
  all: try step_val_contra.
  all: use_ih.
Qed.

Lemma try_step_none_value : forall v,
  is_value v -> try_step v = None.
Proof. exact try_step_value_none. Qed.


Lemma resolve_const_step : forall n,
  step (EResolve (EConst n)) (EConst n).
Proof. intros n. apply step_resolve_const. Qed.

Lemma l5_step_deterministic : forall m n1 n2,
  step (EResolve (EConst m)) (EConst n1) ->
  step (EResolve (EConst m)) (EConst n2) ->
  n1 = n2.
Proof.
  intros m n1 n2 H1 H2.
  inversion H1; subst. inversion H2; subst. reflexivity.
Qed.

Lemma multi_step_app_fun : forall e1 e1p e2,
  multi_step e1 e1p -> multi_step (EApp e1 e2) (EApp e1p e2).
Proof.
  intros e1 e1p e2 Hm.
  induction Hm as [| e1 e1a e1p Hs Hm IH].
  - apply ms_refl.
  - apply ms_step with (EApp e1a e2).
    apply step_app_fun. exact Hs. exact IH.
Qed.

Lemma multi_step_app_arg : forall v e2 e2p,
  is_value v -> multi_step e2 e2p -> multi_step (EApp v e2) (EApp v e2p).
Proof.
  intros v e2 e2p Hv Hm.
  induction Hm as [| e2 e2a e2p Hs Hm IH].
  - apply ms_refl.
  - apply ms_step with (EApp v e2a).
    apply step_app_arg. exact Hv. exact Hs. exact IH.
Qed.

Lemma multi_step_pair_left : forall e1 e1p e2,
  multi_step e1 e1p -> multi_step (EPair e1 e2) (EPair e1p e2).
Proof.
  intros e1 e1p e2 Hm.
  induction Hm as [| e1 e1a e1p Hs Hm IH].
  - apply ms_refl.
  - apply ms_step with (EPair e1a e2).
    apply step_pair_left. exact Hs. exact IH.
Qed.

Lemma multi_step_fst : forall e ep,
  multi_step e ep -> multi_step (EFst e) (EFst ep).
Proof.
  intros e ep Hm.
  induction Hm as [| e ea ep Hs Hm IH].
  - apply ms_refl.
  - apply ms_step with (EFst ea).
    apply step_fst_inner. exact Hs. exact IH.
Qed.

Lemma multi_step_snd : forall e ep,
  multi_step e ep -> multi_step (ESnd e) (ESnd ep).
Proof.
  intros e ep Hm.
  induction Hm as [| e ea ep Hs Hm IH].
  - apply ms_refl.
  - apply ms_step with (ESnd ea).
    apply step_snd_inner. exact Hs. exact IH.
Qed.

Lemma multi_step_pair_right : forall v1 e2 e2p,
  is_value v1 -> multi_step e2 e2p ->
  multi_step (EPair v1 e2) (EPair v1 e2p).
Proof.
  intros v1 e2 e2p Hv Hm.
  induction Hm as [| e2 e2a e2p Hs Hm IH].
  - apply ms_refl.
  - apply ms_step with (EPair v1 e2a).
    apply step_pair_right. exact Hv. exact Hs. exact IH.
Qed.

Lemma step_implies_not_value : forall e ep,
  step e ep -> ~ is_value e.
Proof.
  intros e ep Hstep Hv.
  eapply value_no_step_rel. exact Hv. exact Hstep.
Qed.
