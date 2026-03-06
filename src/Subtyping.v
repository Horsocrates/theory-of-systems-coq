From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import micromega.Lia.
Import ListNotations.

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import SystemMorphism.
From ToS Require Import Judgments.
From ToS Require Import DependentSystems.

Section Subtyping.
Variable L : Level.

Definition is_subsystem (S1 S2 : System L) : Prop :=
  exists (f : SystemMorphism L S1 S2), is_embedding L f.

Lemma id_is_embedding : forall (S : System L),
  is_embedding L (id_morphism L S).
Proof.
  intros S. unfold is_embedding, id_morphism. simpl.
  intros e1 e2 Heq. exact Heq.
Qed.

Lemma subsystem_refl : forall (S : System L),
  is_subsystem S S.
Proof.
  intros S. unfold is_subsystem.
  exists (id_morphism L S). apply id_is_embedding.
Qed.

Lemma compose_embedding : forall (S1 S2 S3 : System L)
  (f : SystemMorphism L S1 S2) (g : SystemMorphism L S2 S3),
  is_embedding L f ->
  is_embedding L g ->
  is_embedding L (compose_morphism L f g).
Proof.
  intros S1 S2 S3 f g Hf Hg.
  unfold is_embedding, compose_morphism. simpl.
  intros e1 e2 Heq.
  apply Hf. apply Hg. exact Heq.
Qed.

Lemma subsystem_trans : forall (S1 S2 S3 : System L),
  is_subsystem S1 S2 ->
  is_subsystem S2 S3 ->
  is_subsystem S1 S3.
Proof.
  intros S1 S2 S3 [f Hf] [g Hg].
  unfold is_subsystem.
  exists (compose_morphism L f g).
  exact (compose_embedding S1 S2 S3 f g Hf Hg).
Qed.
Lemma subsumption : forall (G : Context) (S1 S2 : System L)
  (e : ElemOf L S1),
  HasElem L G S1 e ->
  is_subsystem S1 S2 ->
  exists (e2 : ElemOf L S2), HasElem L G S2 e2.
Proof.
  intros G S1 S2 e [Hwf Hpred] [f Hf].
  exists (sm_map L S1 S2 f e).
  unfold HasElem. split.
  - exact Hwf.
  - apply (sm_preserves L S1 S2 f e Hpred).
Qed.

Lemma embedding_preserves_criterion : forall (S1 S2 : System L)
  (f : SystemMorphism L S1 S2)
  (e : ElemOf L S1),
  is_embedding L f ->
  crit_predicate L (sys_criterion L S1) e ->
  crit_predicate L (sys_criterion L S2) (sm_map L S1 S2 f e).
Proof.
  intros S1 S2 f e _Hemb Hpred.
  exact (sm_preserves L S1 S2 f e Hpred).
Qed.

Lemma subsystem_respects_has_type : forall (G : Context) (S1 S2 : System L),
  HasType L G S1 ->
  HasType L G S2 ->
  is_subsystem S1 S2 ->
  HasType L G S2.
Proof.
  intros G S1 S2 _Ht1 Ht2 _Hsub. exact Ht2.
Qed.

Lemma subsystem_preserves_level : forall (S1 S2 : System L),
  is_subsystem S1 S2 ->
  crit_level_witness L (sys_criterion L S1) << L ->
  crit_level_witness L (sys_criterion L S2) << L.
Proof.
  intros S1 S2 _Hsub _HL1.
  exact (crit_level_valid L (sys_criterion L S2)).
Qed.

Lemma iso_implies_subsystem : forall (S1 S2 : System L)
  (f : SystemMorphism L S1 S2) (g : SystemMorphism L S2 S1),
  is_iso_pair L f g ->
  is_subsystem S1 S2.
Proof.
  intros S1 S2 f g Hiso.
  unfold is_subsystem. exists f.
  exact (iso_pair_implies_embedding L f g Hiso).
Qed.

Lemma iso_implies_mutual_subsystem : forall (S1 S2 : System L)
  (f : SystemMorphism L S1 S2) (g : SystemMorphism L S2 S1),
  is_iso_pair L f g ->
  is_subsystem S1 S2 /\ is_subsystem S2 S1.
Proof.
  intros S1 S2 f g Hiso. split.
  - exact (iso_implies_subsystem S1 S2 f g Hiso).
  - apply (iso_implies_subsystem S2 S1 g f).
    exact (iso_pair_symmetric L f g Hiso).
Qed.
Lemma subsystem_antisym_weak : forall (S1 S2 : System L)
  (f : SystemMorphism L S1 S2) (g : SystemMorphism L S2 S1),
  is_iso_pair L f g ->
  forall e : ElemOf L S1,
    crit_predicate L (sys_criterion L S1) e <->
    crit_predicate L (sys_criterion L S2) (sm_map L S1 S2 f e).
Proof.
  intros S1 S2 f g Hiso e.
  exact (iso_pair_predicate_equiv L f g Hiso e).
Qed.

Lemma subsystem_via_id : forall (S : System L),
  exists (f : SystemMorphism L S S),
    is_embedding L f /\
    forall e, sm_map L S S f e = e.
Proof.
  intros S. exists (id_morphism L S). split.
  - apply id_is_embedding.
  - intros e. unfold id_morphism. simpl. reflexivity.
Qed.

Lemma embedding_injective_elems : forall (S1 S2 : System L)
  (f : SystemMorphism L S1 S2),
  is_embedding L f ->
  forall e1 e2 : ElemOf L S1,
    sm_map L S1 S2 f e1 = sm_map L S1 S2 f e2 ->
    e1 = e2.
Proof.
  intros S1 S2 f Hemb e1 e2 Heq.
  exact (Hemb e1 e2 Heq).
Qed.

Lemma has_elem_subsystem_transfer : forall (G : Context) (S1 S2 : System L)
  (f : SystemMorphism L S1 S2)
  (e : ElemOf L S1),
  is_embedding L f ->
  HasElem L G S1 e ->
  HasElem L G S2 (sm_map L S1 S2 f e).
Proof.
  intros G S1 S2 f e _Hemb [Hwf Hpred].
  unfold HasElem. split.
  - exact Hwf.
  - apply (sm_preserves L S1 S2 f e Hpred).
Qed.

Lemma subsystem_compose_explicit : forall (S1 S2 S3 : System L)
  (f : SystemMorphism L S1 S2) (g : SystemMorphism L S2 S3),
  is_embedding L f ->
  is_embedding L g ->
  is_subsystem S1 S3.
Proof.
  intros S1 S2 S3 f g Hf Hg.
  unfold is_subsystem.
  exists (compose_morphism L f g).
  exact (compose_embedding S1 S2 S3 f g Hf Hg).
Qed.

End Subtyping.
Section PiSigmaVariance.
Variable L : Level.

Lemma pi_contravariant_domain :
  forall (A A2 : System L) (B : ElemOf L A -> System L)
    (h : SystemMorphism L A2 A),
  PiSystem L A B ->
  PiSystem L A2 (fun a2 => B (sm_map L A2 A h a2)).
Proof.
  intros A A2 B h f.
  apply mkPiSystem.
  intro a2.
  exact (pi_app L A B f (sm_map L A2 A h a2)).
Qed.

Lemma sigma_covariant :
  forall (A : System L)
    (B C : ElemOf L A -> System L)
    (phi : forall (a : ElemOf L A), SystemMorphism L (B a) (C a)),
  SigmaElem L A B ->
  SigmaElem L A C.
Proof.
  intros A B C phi p.
  apply (mkSigmaElem L A C (sigma_fst L A B p)).
  exact (sm_map L (B (sigma_fst L A B p)) (C (sigma_fst L A B p))
           (phi (sigma_fst L A B p))
           (sigma_snd L A B p)).
Qed.

End PiSigmaVariance.
Section SubtypingExamples.

Definition nat_gt5 : System L2 := {|
  sys_criterion := {|
    crit_domain := nat;
    crit_predicate := fun n => n > 5;
    crit_level_witness := L1;
    crit_level_valid := L1_lt_L2;
  |};
  sys_pos_bound := Unbounded;
  sys_uniqueness := MultiplePerRole;
|}.

Definition nat_gt10 : System L2 := {|
  sys_criterion := {|
    crit_domain := nat;
    crit_predicate := fun n => n > 10;
    crit_level_witness := L1;
    crit_level_valid := L1_lt_L2;
  |};
  sys_pos_bound := Unbounded;
  sys_uniqueness := MultiplePerRole;
|}.

Definition gt10_to_gt5_map (e : ElemOf L2 nat_gt10) : ElemOf L2 nat_gt5 := e.

Lemma gt10_to_gt5_preserves : forall e : ElemOf L2 nat_gt10,
  crit_predicate L2 (sys_criterion L2 nat_gt10) e ->
  crit_predicate L2 (sys_criterion L2 nat_gt5) (gt10_to_gt5_map e).
Proof.
  intros e Hpred.
  unfold gt10_to_gt5_map.
  unfold crit_predicate, sys_criterion, nat_gt10, nat_gt5 in *.
  simpl in *. lia.
Qed.

Definition gt10_to_gt5 : SystemMorphism L2 nat_gt10 nat_gt5 :=
  mkSystemMorphism L2 nat_gt10 nat_gt5 gt10_to_gt5_map gt10_to_gt5_preserves.

Lemma gt10_embeds_in_gt5 : is_embedding L2 gt10_to_gt5.
Proof.
  unfold is_embedding, gt10_to_gt5. simpl.
  intros e1 e2 Heq. exact Heq.
Qed.

Lemma nat_gt10_subsystem_nat_gt5 : is_subsystem L2 nat_gt10 nat_gt5.
Proof.
  unfold is_subsystem.
  exists gt10_to_gt5.
  exact gt10_embeds_in_gt5.
Qed.

End SubtypingExamples.
