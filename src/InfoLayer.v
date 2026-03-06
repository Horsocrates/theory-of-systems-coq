(**
  InfoLayer.v — Information Layers Formalized
  =============================================

  Phase 3, Task 3.

  Information Layers = different E/R/R systems over the SAME substrate.
  One substrate (domain D) can be viewed through multiple "lenses"
  (criteria), each selecting different elements as significant.

  KEY DESIGN (per P3):
  layer_equiv = Leibniz equality on il_criterion (INTENSIONAL).
  Two layers with the same elements but different criteria are DIFFERENT.
  This is the formal separation between "what" and "why".

  Uses CriterionOver from IntensionalIdentity.v — IMPORTED, not redefined.

  E/R/R Analysis:
  - Element: Substrate elements viewed through a layer
  - Role: The layer's criterion determining membership
  - Rule: L4 grounding (every layer must have il_reason_proof)

  Depends on: IntensionalIdentity.v (which imports Core_ERR.v)
  Qed: 17, Admitted: 0
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import IntensionalIdentity.
Require Import List Lia.
Import ListNotations.

(* ================================================================= *)
(** * InfoLayer — A Criterion Over a Fixed Substrate                *)
(* ================================================================= *)

Section InfoLayerTheory.

Variable D : Type.
Variable L : Level.

(**
  An Information Layer consists of:
  - A criterion over fixed substrate D at level L (from IntensionalIdentity.v)
  - An L4 grounding: a reason (Prop) and its proof

  The L4 grounding ensures every layer has a "why":
  not just WHAT it selects, but WHY this selection matters.
  This is enforced at the type level via the dependent field
  il_reason_proof : il_reason.
*)
Record InfoLayer := mkInfoLayer {
  il_criterion : CriterionOver L D;
  il_reason : Prop;
  il_reason_proof : il_reason;
}.

(* ================================================================= *)
(** * Layer Equivalence (P3 — Intensional)                          *)
(* ================================================================= *)

(**
  layer_equiv is LEIBNIZ EQUALITY on il_criterion.
  This is the P3 identity principle applied to layers:

  Two layers are equivalent iff they have the SAME criterion —
  same predicate, same level witness, same validity proof.

  In particular: two layers with identical element sets but
  different level witnesses are NOT equivalent. The "why"
  (at which level the criterion is grounded) matters.
*)
Definition layer_equiv (l1 l2 : InfoLayer) : Prop :=
  il_criterion l1 = il_criterion l2.

(** Reflexivity *)
Lemma layer_equiv_refl : forall l : InfoLayer, layer_equiv l l.
Proof. intro l. unfold layer_equiv. reflexivity. Qed.

(** Symmetry *)
Lemma layer_equiv_sym : forall l1 l2 : InfoLayer,
  layer_equiv l1 l2 -> layer_equiv l2 l1.
Proof. intros l1 l2 H. unfold layer_equiv in *. symmetry. exact H. Qed.

(** Transitivity *)
Lemma layer_equiv_trans : forall l1 l2 l3 : InfoLayer,
  layer_equiv l1 l2 -> layer_equiv l2 l3 -> layer_equiv l1 l3.
Proof.
  intros l1 l2 l3 H12 H23. unfold layer_equiv in *.
  transitivity (il_criterion l2); assumption.
Qed.

(** P3 distinctness: different level witnesses → different layers *)
Theorem layer_P3_distinct : forall (l1 l2 : InfoLayer),
  co_level_witness L D (il_criterion l1) <>
  co_level_witness L D (il_criterion l2) ->
  ~ layer_equiv l1 l2.
Proof.
  intros l1 l2 Hne Heq. apply Hne.
  unfold layer_equiv in Heq.
  rewrite Heq. reflexivity.
Qed.

(* ================================================================= *)
(** * Element Membership and Layer Operations                       *)
(* ================================================================= *)

(** Element projection through a layer:
    "e is in layer" iff e satisfies the layer's criterion predicate. *)
Definition in_layer (e : D) (layer : InfoLayer) : Prop :=
  co_predicate L D (il_criterion layer) e.

(** Layer membership decidability: if the criterion predicate is
    decidable, then layer membership is decidable. *)
Theorem in_layer_decidable : forall (layer : InfoLayer),
  (forall e : D, {co_predicate L D (il_criterion layer) e} +
                  {~ co_predicate L D (il_criterion layer) e}) ->
  forall e : D, {in_layer e layer} + {~ in_layer e layer}.
Proof.
  intros layer Hdec e. exact (Hdec e).
Qed.

(** One element can be in multiple layers simultaneously.
    This is the fundamental property of Information Layers:
    the same substrate element can be significant in DIFFERENT ways. *)
Theorem element_multi_layer : forall (l1 l2 : InfoLayer) (e : D),
  in_layer e l1 -> in_layer e l2 ->
  in_layer e l1 /\ in_layer e l2.
Proof.
  intros l1 l2 e H1 H2. split; assumption.
Qed.

(* ================================================================= *)
(** * Layer Composition (Conjunction)                                *)
(* ================================================================= *)

(**
  compose_layers creates a new layer whose elements must satisfy
  BOTH input layers. The conjunction criterion inherits the level
  witness from the first layer.

  The reason for composition is provided externally — the caller
  must explain WHY the composed layer exists (L4 grounding).
*)
Definition compose_layers (l1 l2 : InfoLayer)
  (reason : Prop) (proof : reason) : InfoLayer :=
  mkInfoLayer
    (mkCriterionOver L D
      (fun e => co_predicate L D (il_criterion l1) e /\
                co_predicate L D (il_criterion l2) e)
      (co_level_witness L D (il_criterion l1))
      (co_level_valid L D (il_criterion l1)))
    reason
    proof.

(** Characterization: membership in composed layer ↔ both layers *)
Theorem compose_in_layer_iff : forall (l1 l2 : InfoLayer)
  (r : Prop) (p : r) (e : D),
  in_layer e (compose_layers l1 l2 r p) <->
  (in_layer e l1 /\ in_layer e l2).
Proof.
  intros. unfold in_layer, compose_layers. simpl. tauto.
Qed.

(** Membership in composed → membership in first layer *)
Theorem in_layer_compose_left : forall (l1 l2 : InfoLayer)
  (r : Prop) (p : r) (e : D),
  in_layer e (compose_layers l1 l2 r p) -> in_layer e l1.
Proof.
  intros. apply compose_in_layer_iff in H. destruct H; assumption.
Qed.

(** Membership in composed → membership in second layer *)
Theorem in_layer_compose_right : forall (l1 l2 : InfoLayer)
  (r : Prop) (p : r) (e : D),
  in_layer e (compose_layers l1 l2 r p) -> in_layer e l2.
Proof.
  intros. apply compose_in_layer_iff in H. destruct H; assumption.
Qed.

(** Commutativity of composition (element-level):
    l1 ∧ l2 and l2 ∧ l1 have the same members.
    NOTE: NOT layer_equiv — the criteria differ intensionally
    (different level witnesses if l1, l2 have different witnesses). *)
Theorem compose_layers_comm : forall (l1 l2 : InfoLayer)
  (r1 r2 : Prop) (p1 : r1) (p2 : r2) (e : D),
  in_layer e (compose_layers l1 l2 r1 p1) <->
  in_layer e (compose_layers l2 l1 r2 p2).
Proof.
  intros. unfold in_layer, compose_layers. simpl. tauto.
Qed.

(** Associativity of composition (element-level):
    (l1 ∧ l2) ∧ l3 and l1 ∧ (l2 ∧ l3) have the same members. *)
Theorem compose_layers_assoc : forall (l1 l2 l3 : InfoLayer)
  (r12 r123a r23 r123b : Prop)
  (p12 : r12) (p123a : r123a) (p23 : r23) (p123b : r123b)
  (e : D),
  in_layer e (compose_layers (compose_layers l1 l2 r12 p12) l3 r123a p123a) <->
  in_layer e (compose_layers l1 (compose_layers l2 l3 r23 p23) r123b p123b).
Proof.
  intros. unfold in_layer, compose_layers. simpl. tauto.
Qed.

(** Idempotence of composition (element-level):
    l ∧ l has the same members as l. *)
Theorem compose_layers_idempotent : forall (l : InfoLayer)
  (r : Prop) (p : r) (e : D),
  in_layer e (compose_layers l l r p) <-> in_layer e l.
Proof.
  intros. unfold in_layer, compose_layers. simpl. tauto.
Qed.

(** Decidability of composed layers from decidability of components *)
Theorem compose_layers_decidable : forall (l1 l2 : InfoLayer)
  (r : Prop) (p : r),
  (forall e : D, {in_layer e l1} + {~ in_layer e l1}) ->
  (forall e : D, {in_layer e l2} + {~ in_layer e l2}) ->
  forall e : D,
    {in_layer e (compose_layers l1 l2 r p)} +
    {~ in_layer e (compose_layers l1 l2 r p)}.
Proof.
  intros l1 l2 r p Hdec1 Hdec2 e.
  destruct (Hdec1 e) as [H1 | H1]; destruct (Hdec2 e) as [H2 | H2].
  - left. apply compose_in_layer_iff. split; assumption.
  - right. intro Hc. apply H2. apply compose_in_layer_iff in Hc.
    destruct Hc; assumption.
  - right. intro Hc. apply H1. apply compose_in_layer_iff in Hc.
    destruct Hc; assumption.
  - right. intro Hc. apply H1. apply compose_in_layer_iff in Hc.
    destruct Hc; assumption.
Qed.

(* ================================================================= *)
(** * Layered Objects                                                *)
(* ================================================================= *)

(** A Layered Object: substrate D viewed through multiple layers.
    The nonemptiness constraint ensures every layered object has
    at least one way of being viewed (P4: finite, grounded). *)
Record LayeredObject := mkLayeredObject {
  lo_layers : list InfoLayer;
  lo_nonempty : lo_layers <> [];
}.

(** Every LayeredObject has at least one layer *)
Theorem layer_count_positive : forall (obj : LayeredObject),
  (length (lo_layers obj) > 0)%nat.
Proof.
  intros obj.
  destruct (lo_layers obj) as [| x xs] eqn:Heq.
  - exfalso. exact (lo_nonempty obj Heq).
  - simpl. lia.
Qed.

End InfoLayerTheory.

(* ================================================================= *)
(** * Concrete Example: P3 Separation for Layers                    *)
(* ================================================================= *)

(**
  CONCRETE DEMONSTRATION OF P3 FOR INFORMATION LAYERS
  =====================================================

  We construct two layers over nat at level L3:
  - layer_all_L1: accepts ALL naturals, grounded at L1
  - layer_all_L2: accepts ALL naturals, grounded at L2

  These layers have IDENTICAL element sets (all of nat).
  But they are NOT layer_equiv because their criteria differ:
  different level witnesses (L1 vs L2).

  This is the Information Layers version of the Separation Theorem:
  same elements, different layers — because P3 is INTENSIONAL.

  Analogy: a geographic region can be viewed through a "transport"
  layer (grounded in infrastructure) and an "ecology" layer
  (grounded in biology). Same points, different criteria, different
  layers — even if both accept all points in the region.
*)

Definition layer_all_L1 : InfoLayer nat L3 := {|
  il_criterion := mkCriterionOver L3 nat (fun _ => True) L1 L1_lt_L3;
  il_reason := True;
  il_reason_proof := I;
|}.

Definition layer_all_L2 : InfoLayer nat L3 := {|
  il_criterion := mkCriterionOver L3 nat (fun _ => True) L2 L2_lt_L3;
  il_reason := True;
  il_reason_proof := I;
|}.

(** These layers are NOT equivalent by P3: different level witnesses *)
Theorem same_substrate_different_layers :
  ~ layer_equiv nat L3 layer_all_L1 layer_all_L2.
Proof.
  unfold layer_equiv. intro H.
  assert (Hw := f_equal (co_level_witness L3 nat) H).
  simpl in Hw. discriminate.
Qed.

(** But they ARE extensionally equivalent: same elements *)
Theorem same_substrate_ext_equiv :
  ext_equiv L3 nat
    (il_criterion nat L3 layer_all_L1)
    (il_criterion nat L3 layer_all_L2).
Proof.
  unfold ext_equiv. intro e. simpl. tauto.
Qed.

(** Combined P3 theorem for layers: there EXIST layers over the
    same substrate that are extensionally equivalent but NOT
    intensionally (layer-)equivalent. *)
Theorem P3_layers_separation :
  exists (l1 l2 : InfoLayer nat L3),
    (forall e : nat, in_layer nat L3 e l1 <-> in_layer nat L3 e l2) /\
    ~ layer_equiv nat L3 l1 l2.
Proof.
  exists layer_all_L1, layer_all_L2. split.
  - intro e. unfold in_layer. simpl. tauto.
  - exact same_substrate_different_layers.
Qed.
