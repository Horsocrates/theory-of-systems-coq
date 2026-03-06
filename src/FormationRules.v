From Stdlib Require Import Init.Nat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import micromega.Lia.
Import ListNotations.

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import UniversePolymorphism.
From ToS Require Import IntensionalIdentity.
From ToS Require Import Judgments.
From ToS Require Import DependentSystems.
From ToS Require Import L5Resolution.
From ToS Require Import InfoLayer.
From ToS Require Import CoinductiveSystems.

Section FormationRulesCore.
Variable L : Level.

Lemma sys_form : forall (G : Context) (S : System L),
  ctx_well_formed G ->
  crit_level_witness L (sys_criterion L S) << L ->
  HasType L G S.
Proof.
  intros G S Hwf Hlevel.
  unfold HasType. split; assumption.
Qed.
Lemma p1_check : forall (G : Context) (S : System L),
  HasType L G S ->
  crit_level_witness L (sys_criterion L S) << L.
Proof.
  intros G S Htype.
  exact (has_type_implies_P1 L G S Htype).
Qed.

Lemma l4_role_principle : forall (G : Context) (S : System L),
  HasType L G S ->
  P2_valid L (sys_criterion L S).
Proof.
  intros G S Htype.
  exact (has_type_P2 L G S Htype).
Qed.

Lemma wf4_check : forall (G : Context) (S : System L),
  HasType L G S ->
  ctx_well_formed G /\
  crit_level_witness L (sys_criterion L S) << L.
Proof.
  intros G S [Hwf Hlev].
  split; assumption.
Qed.

End FormationRulesCore.
Section FormationRulesPiSigma.
Variable L : Level.

Lemma pi_form : forall (G : Context) (A : System L)
  (B : ElemOf L A -> System L),
  HasType L G A ->
  (forall a : ElemOf L A, HasType L G (B a)) ->
  ctx_well_formed G /\
  crit_level_witness L (sys_criterion L A) << L /\
  (forall a, crit_level_witness L (sys_criterion L (B a)) << L).
Proof.
  intros G A B [HwfA HlevA] HB.
  split; [exact HwfA | split; [exact HlevA |]].
  intro a. exact (proj2 (wf4_check L G (B a) (HB a))).
Qed.

Lemma sigma_form : forall (G : Context) (A : System L)
  (B : ElemOf L A -> System L),
  HasType L G A ->
  (forall a : ElemOf L A, HasType L G (B a)) ->
  ctx_well_formed G /\
  (forall a : ElemOf L A,
     crit_level_witness L (sys_criterion L (B a)) << L).
Proof.
  intros G A B HtypeA HB.
  split.
  - exact (proj1 (wf4_check L G A HtypeA)).
  - intro a. exact (proj2 (wf4_check L G (B a) (HB a))).
Qed.
Lemma pi_app_rule : forall (G : Context) (A : System L)
  (B : ElemOf L A -> System L)
  (f : PiSystem L A B)
  (a : ElemOf L A),
  HasType L G A ->
  HasElem L G A a ->
  crit_predicate L (sys_criterion L (B a)) (pi_app L A B f a) ->
  HasElem L G (B a) (pi_app L A B f a).
Proof.
  intros G A B f a _HtypeA [HwfE _Hcrit] Hpred.
  unfold HasElem.
  split.
  - exact HwfE.
  - exact Hpred.
Qed.

Lemma sigma_pair_rule : forall (G : Context) (A : System L)
  (B : ElemOf L A -> System L)
  (a : ElemOf L A)
  (b : ElemOf L (B a)),
  HasElem L G A a ->
  HasElem L G (B a) b ->
  exists (p : SigmaElem L A B), sigma_fst L A B p = a.
Proof.
  intros G A B a b _HA _HB.
  exists (mkSigmaElem L A B a b).
  simpl. reflexivity.
Qed.

Lemma sigma_proj_fst_rule : forall (G : Context) (A : System L)
  (B : ElemOf L A -> System L)
  (p : SigmaElem L A B),
  HasType L G A ->
  HasType L G A.
Proof.
  intros G A B p Htype.
  exact Htype.
Qed.

Lemma sigma_proj_snd_rule : forall (G : Context) (A : System L)
  (B : ElemOf L A -> System L)
  (p : SigmaElem L A B),
  ctx_well_formed G ->
  (forall a, HasType L G (B a)) ->
  HasType L G (B (sigma_fst L A B p)).
Proof.
  intros G A B p Hwf HB.
  exact (HB (sigma_fst L A B p)).
Qed.

End FormationRulesPiSigma.
Section FormationRulesProcess.
Variable A : Type.

Lemma p4_observe : forall (o : Observable A) (n : nat),
  obs_at o n = obs_at o n.
Proof.
  intros o n. reflexivity.
Qed.

Lemma p4_no_collect : forall (o : Observable A) (l : list A),
  exists (n : nat), ~ (length (obs_prefix o n) <= length l)%nat.
Proof.
  intros o l.
  exists (S (length l)).
  rewrite obs_prefix_length.
  lia.
Qed.

End FormationRulesProcess.

Section FormationRulesLayer.
Variable D : Type.
Variable L : Level.

Lemma layer_form : forall (c : CriterionOver L D) (R : Prop) (proof : R),
  exists (layer : InfoLayer D L),
    il_criterion D L layer = c /\ il_reason D L layer = R.
Proof.
  intros c R proof.
  exists (mkInfoLayer D L c R proof).
  simpl. split; reflexivity.
Qed.

Lemma layer_project_rule : forall (layer : InfoLayer D L) (e : D),
  in_layer D L e layer ->
  co_predicate L D (il_criterion D L layer) e.
Proof.
  intros layer e Hin.
  unfold in_layer in Hin. exact Hin.
Qed.

End FormationRulesLayer.
Section FormationRulesL5.

Lemma l5_res_rule : forall (T : Type) (HO : DecTotalOrder T) (l : list T),
  l <> [] ->
  exists v, @l5_resolve_gen T HO l = Some v.
Proof.
  intros T HO l Hne.
  exact (l5_resolve_gen_some l Hne).
Qed.

End FormationRulesL5.

Section FormationRulesStructural.
Variable L : Level.

Lemma weakening : forall (G : Context) (S : System L) (e : CtxEntry),
  HasType L G S ->
  ~ In (ce_name e) (map ce_name G) ->
  HasType L (e :: G) S.
Proof.
  intros G S e Htype Hfresh.
  exact (has_type_weakening L G S e Htype Hfresh).
Qed.

Lemma substitution_type : forall (G : Context) (S T : System L),
  HasType L G S ->
  HasType L G T ->
  ctx_well_formed G /\
  crit_level_witness L (sys_criterion L S) << L /\
  crit_level_witness L (sys_criterion L T) << L.
Proof.
  intros G S T [HwfS HlevS] [_ HlevT].
  split; [exact HwfS | split; assumption].
Qed.

Lemma formation_preserves_equiv : forall (G : Context) (S1 S2 : System L),
  HasType L G S1 ->
  SystemEquiv L S1 S2 ->
  crit_level_witness L (sys_criterion L S2) << L ->
  HasType L G S2.
Proof.
  intros G S1 S2 HtypeS1 Hequiv HlevS2.
  exact (system_equiv_preserves_has_type L G S1 S2 HtypeS1 Hequiv HlevS2).
Qed.

End FormationRulesStructural.
