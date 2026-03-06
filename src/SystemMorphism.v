(**
  SystemMorphism.v — Structure-Preserving Maps Between Systems
  =============================================================

  Phase 3, Task 2.

  Defines morphisms between systems at the same Level, establishing
  categorical structure: identity, composition, and isomorphism.

  Key design decisions:
  - Morphisms between SAME Level only (cross-level = future work)
  - Isomorphism defined constructively via inverse pairs (no choice axiom)
  - Morphism equality is pointwise (avoids proof irrelevance issues)

  E/R/R Analysis:
  - Element: Systems and their elements
  - Role: Morphisms as structure-preserving maps
  - Rule: Criterion preservation, categorical laws (identity, associativity)

  Depends on: TheoryOfSystems_Core_ERR.v
  Qed: 17, Admitted: 0
*)

From ToS Require Import TheoryOfSystems_Core_ERR.

Section Morphisms.

Variable L : Level.

(** Element type of a system: the domain of its criterion.
    Equivalent to ElemOf in Roles.v — redefined here to avoid
    adding Roles.v as a dependency. *)
Definition ElemOf (S : System L) : Type :=
  crit_domain L (sys_criterion L S).

(* ================================================================= *)
(** * SystemMorphism — Structure-Preserving Map                     *)
(* ================================================================= *)

(**
  A morphism between systems at the same level L consists of:
  - A function mapping elements of S1 to elements of S2
  - A proof that the function preserves the criterion predicate

  This is the ToS analogue of a morphism in a category:
  it preserves the "what is actually here" (D1 recognition).
  The predicate preservation ensures that elements satisfying
  S1's criterion map to elements satisfying S2's criterion.
*)
Record SystemMorphism (S1 S2 : System L) : Type := mkSystemMorphism {
  sm_map : ElemOf S1 -> ElemOf S2;
  sm_preserves : forall e : ElemOf S1,
    crit_predicate L (sys_criterion L S1) e ->
    crit_predicate L (sys_criterion L S2) (sm_map e);
}.

(* ================================================================= *)
(** * Identity and Composition                                      *)
(* ================================================================= *)

(** Identity morphism: map = id, preservation trivial *)
Definition id_morphism (S : System L) : SystemMorphism S S :=
  mkSystemMorphism S S (fun e => e) (fun e H => H).

(** Composition of morphisms: g after f *)
Definition compose_morphism {S1 S2 S3 : System L}
  (f : SystemMorphism S1 S2) (g : SystemMorphism S2 S3)
  : SystemMorphism S1 S3 :=
  mkSystemMorphism S1 S3
    (fun e => sm_map S2 S3 g (sm_map S1 S2 f e))
    (fun e H => sm_preserves S2 S3 g _ (sm_preserves S1 S2 f e H)).

(** Morphism equality: pointwise agreement of map functions.
    We use pointwise equality rather than Leibniz equality to avoid
    proof-irrelevance requirements on the sm_preserves field. *)
Definition morphism_eq {S1 S2 : System L}
  (f g : SystemMorphism S1 S2) : Prop :=
  forall e : ElemOf S1, sm_map S1 S2 f e = sm_map S1 S2 g e.

(* ================================================================= *)
(** * morphism_eq is an Equivalence Relation                        *)
(* ================================================================= *)

Lemma morphism_eq_refl : forall {S1 S2 : System L}
  (f : SystemMorphism S1 S2),
  morphism_eq f f.
Proof. intros S1 S2 f e. reflexivity. Qed.

Lemma morphism_eq_sym : forall {S1 S2 : System L}
  (f g : SystemMorphism S1 S2),
  morphism_eq f g -> morphism_eq g f.
Proof. intros S1 S2 f g Heq e. symmetry. apply Heq. Qed.

Lemma morphism_eq_trans : forall {S1 S2 : System L}
  (f g h : SystemMorphism S1 S2),
  morphism_eq f g -> morphism_eq g h -> morphism_eq f h.
Proof.
  intros S1 S2 f g h Hfg Hgh e.
  transitivity (sm_map S1 S2 g e).
  - apply Hfg.
  - apply Hgh.
Qed.

(* ================================================================= *)
(** * Categorical Laws                                               *)
(* ================================================================= *)

(** Composition is associative: (h ∘ g) ∘ f = h ∘ (g ∘ f) *)
Theorem compose_assoc : forall {S1 S2 S3 S4 : System L}
  (f : SystemMorphism S1 S2) (g : SystemMorphism S2 S3)
  (h : SystemMorphism S3 S4),
  morphism_eq (compose_morphism (compose_morphism f g) h)
              (compose_morphism f (compose_morphism g h)).
Proof. intros. intro e. reflexivity. Qed.

(** Left identity: f ∘ id = f *)
Theorem compose_id_left : forall {S1 S2 : System L}
  (f : SystemMorphism S1 S2),
  morphism_eq (compose_morphism (id_morphism S1) f) f.
Proof. intros. intro e. reflexivity. Qed.

(** Right identity: id ∘ f = f *)
Theorem compose_id_right : forall {S1 S2 : System L}
  (f : SystemMorphism S1 S2),
  morphism_eq (compose_morphism f (id_morphism S2)) f.
Proof. intros. intro e. reflexivity. Qed.

(* ================================================================= *)
(** * Embeddings and Surjections                                     *)
(* ================================================================= *)

(** Embedding = injective morphism *)
Definition is_embedding {S1 S2 : System L}
  (f : SystemMorphism S1 S2) : Prop :=
  forall e1 e2 : ElemOf S1,
    sm_map S1 S2 f e1 = sm_map S1 S2 f e2 -> e1 = e2.

(** Surjection = surjective morphism *)
Definition is_surjection {S1 S2 : System L}
  (f : SystemMorphism S1 S2) : Prop :=
  forall e2 : ElemOf S2,
    exists e1 : ElemOf S1, sm_map S1 S2 f e1 = e2.

(** Embedding unfolds to injectivity *)
Theorem embedding_injective : forall {S1 S2 : System L}
  (f : SystemMorphism S1 S2),
  is_embedding f ->
  forall e1 e2, sm_map S1 S2 f e1 = sm_map S1 S2 f e2 -> e1 = e2.
Proof. intros S1 S2 f Hemb. exact Hemb. Qed.

(** Composition preserves embedding *)
Theorem embedding_compose : forall {S1 S2 S3 : System L}
  (f : SystemMorphism S1 S2) (g : SystemMorphism S2 S3),
  is_embedding f -> is_embedding g ->
  is_embedding (compose_morphism f g).
Proof.
  intros S1 S2 S3 f g Hf Hg e1 e2 Heq.
  apply Hf. apply Hg. exact Heq.
Qed.

(** Composition preserves surjection *)
Theorem surjection_compose : forall {S1 S2 S3 : System L}
  (f : SystemMorphism S1 S2) (g : SystemMorphism S2 S3),
  is_surjection f -> is_surjection g ->
  is_surjection (compose_morphism f g).
Proof.
  intros S1 S2 S3 f g Hf Hg e3.
  destruct (Hg e3) as [e2 He2].
  destruct (Hf e2) as [e1 He1].
  exists e1. simpl. rewrite He1. exact He2.
Qed.

(** Identity is an embedding *)
Theorem id_embedding : forall (S : System L),
  is_embedding (id_morphism S).
Proof. intros S e1 e2 Heq. exact Heq. Qed.

(** Identity is a surjection *)
Theorem id_surjection : forall (S : System L),
  is_surjection (id_morphism S).
Proof. intros S e2. exists e2. reflexivity. Qed.

(* ================================================================= *)
(** * Isomorphism via Invertible Pairs                              *)
(* ================================================================= *)

(**
  We define isomorphism constructively as a PAIR of morphisms that
  are mutual inverses. This avoids the need for the Axiom of Choice
  (extracting an inverse from an existential surjection would need
  choice). The repository maintains 0 axioms.

  This is the standard categorical definition:
  iso = pair of morphisms whose compositions are identity.
*)

Definition is_iso_pair {S1 S2 : System L}
  (f : SystemMorphism S1 S2) (g : SystemMorphism S2 S1) : Prop :=
  (forall e, sm_map S2 S1 g (sm_map S1 S2 f e) = e) /\
  (forall e, sm_map S1 S2 f (sm_map S2 S1 g e) = e).

(** A system is isomorphic to another if there exists an inverse *)
Definition is_isomorphism {S1 S2 : System L}
  (f : SystemMorphism S1 S2) : Prop :=
  exists g : SystemMorphism S2 S1, is_iso_pair f g.

(** Symmetry of iso pairs: if (f, g) is an iso pair, so is (g, f) *)
Theorem iso_pair_symmetric : forall {S1 S2 : System L}
  (f : SystemMorphism S1 S2) (g : SystemMorphism S2 S1),
  is_iso_pair f g -> is_iso_pair g f.
Proof.
  intros S1 S2 f g [Hgf Hfg]. split; assumption.
Qed.

(** Isomorphism is symmetric: if f : S1 -> S2 is iso, its inverse
    is an iso S2 -> S1 *)
Theorem iso_symmetric : forall {S1 S2 : System L}
  (f : SystemMorphism S1 S2),
  is_isomorphism f ->
  exists g : SystemMorphism S2 S1, is_isomorphism g.
Proof.
  intros S1 S2 f [g Hpair].
  exists g. exists f. exact (iso_pair_symmetric f g Hpair).
Qed.

(** An iso pair implies the first morphism is an embedding *)
Theorem iso_pair_implies_embedding : forall {S1 S2 : System L}
  (f : SystemMorphism S1 S2) (g : SystemMorphism S2 S1),
  is_iso_pair f g -> is_embedding f.
Proof.
  intros S1 S2 f g [Hgf _] e1 e2 Heq.
  assert (Hc : sm_map S2 S1 g (sm_map S1 S2 f e1) =
               sm_map S2 S1 g (sm_map S1 S2 f e2))
    by (rewrite Heq; reflexivity).
  rewrite (Hgf e1) in Hc. rewrite (Hgf e2) in Hc. exact Hc.
Qed.

(** An iso pair implies the first morphism is a surjection *)
Theorem iso_pair_implies_surjection : forall {S1 S2 : System L}
  (f : SystemMorphism S1 S2) (g : SystemMorphism S2 S1),
  is_iso_pair f g -> is_surjection f.
Proof.
  intros S1 S2 f g [_ Hfg] e2.
  exists (sm_map S2 S1 g e2). apply Hfg.
Qed.

(** Identity forms an iso pair with itself *)
Theorem id_iso_pair : forall (S : System L),
  is_iso_pair (id_morphism S) (id_morphism S).
Proof. intros S. split; intro e; reflexivity. Qed.

(* ================================================================= *)
(** * P3 Connection: Isomorphism and Predicate Equivalence          *)
(* ================================================================= *)

(**
  An iso pair gives extensional equivalence of criteria:
  e satisfies S1's predicate iff f(e) satisfies S2's predicate.

  This is the P3 (Identity) connection: isomorphic systems have
  "the same elements" modulo the isomorphism.

  IMPORTANT: This does NOT imply intensional (Leibniz) equality
  of criteria. By the Separation Theorem (IntensionalIdentity.v),
  extensional equivalence is strictly weaker than intensional identity.
  Two systems can be isomorphic yet intensionally distinct (e.g.,
  "even numbers" and "multiples of 2" viewed as different criteria).
*)
Theorem iso_pair_predicate_equiv : forall {S1 S2 : System L}
  (f : SystemMorphism S1 S2) (g : SystemMorphism S2 S1),
  is_iso_pair f g ->
  forall e : ElemOf S1,
    crit_predicate L (sys_criterion L S1) e <->
    crit_predicate L (sys_criterion L S2) (sm_map S1 S2 f e).
Proof.
  intros S1 S2 f g [Hgf Hfg] e. split.
  - apply (sm_preserves S1 S2 f).
  - intro Hsat.
    pose proof (sm_preserves S2 S1 g _ Hsat) as Hg.
    rewrite (Hgf e) in Hg. exact Hg.
Qed.

End Morphisms.
