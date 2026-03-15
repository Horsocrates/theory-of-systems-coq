(** * ProcessCategory.v — Categories as Processes of Finite Diagrams
    Elements: finite subcategories, process functors, natural transformations
    Roles:    SystemCat as process, functors as process maps
    Rules:    finite approximation, P4 colimit interpretation
    Status:   complete
    STATUS: 20 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        PROCESS CATEGORY — Categories as Processes of Finite Diagrams      *)
(*                                                                           *)
(*  Under P4: a category is NOT a completed collection of objects/morphisms.*)
(*  It is a PROCESS of finite subcategories at each level n.                *)
(*                                                                           *)
(*  At level n: finitely many objects and morphisms.                        *)
(*  The category IS the process {C_n} of finite subcategories.              *)
(*                                                                           *)
(*  STATUS: 20 Qed, 0 Admitted                                              *)
(*  AXIOMS: classic (inherited from ProcessNoetherian)                       *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import Classical.
From Stdlib Require Import List.
Import ListNotations.

Open Scope Q_scope.

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import UniversePolymorphism.
From ToS Require Import SystemMorphism.
From ToS Require Import SystemCategory.
From ToS Require Import LevelFunctors.
From ToS Require Import LevelAdjunction.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.

(* ================================================================== *)
(*  Part I: Finite Subcategory Process  (~10 lemmas)                   *)
(* ================================================================== *)

(** A system is "bounded" if its PosBound says Finite n for some n *)
Definition is_finite_system (L : Level) (S : System L) : Prop :=
  exists n, sys_pos_bound L S = Finite n.

(** A system is level-bounded at n if its bound is ≤ n *)
Definition level_bounded (L : Level) (n : nat) (S : System L) : Prop :=
  match sys_pos_bound L S with
  | Finite k => (k <= n)%nat
  | Unbounded => False
  end.

(** Unbounded systems are not level-bounded *)
Lemma unbounded_not_level_bounded : forall L n S,
  sys_pos_bound L S = Unbounded ->
  ~ level_bounded L n S.
Proof.
  intros L n S Hu Hlb. unfold level_bounded in Hlb.
  rewrite Hu in Hlb. exact Hlb.
Qed.

(** Finite systems are level-bounded at their bound *)
Lemma finite_is_level_bounded : forall L k S,
  sys_pos_bound L S = Finite k ->
  level_bounded L k S.
Proof.
  intros L k S Hf. unfold level_bounded. rewrite Hf. lia.
Qed.

(** Level-bounding is monotone: bounded at n implies bounded at m ≥ n *)
Lemma level_bounded_monotone : forall L n m S,
  level_bounded L n S -> (n <= m)%nat -> level_bounded L m S.
Proof.
  intros L n m S Hlb Hnm. unfold level_bounded in *.
  destruct (sys_pos_bound L S).
  - lia.
  - exact Hlb.
Qed.

(** The unit system is level-bounded at 1 *)
Lemma unit_level_bounded : forall L w (Hw : w << L),
  level_bounded L 1 (unit_system L w Hw).
Proof.
  intros L w Hw. unfold level_bounded, unit_system. simpl. lia.
Qed.

(** Finite 0 systems are level-bounded at 0 *)
Lemma finite_zero_bounded : forall L S,
  sys_pos_bound L S = Finite 0 -> level_bounded L 0 S.
Proof.
  intros L S Hf. unfold level_bounded. rewrite Hf. lia.
Qed.

(** At LS levels, bounded systems exist *)
Lemma LS_has_bounded_systems : forall L,
  exists S, level_bounded (LS L) 1 S.
Proof.
  intros L.
  exists (unit_system (LS L) L (level_lt_LS L)).
  apply unit_level_bounded.
Qed.

(** Subcategory at level n: all systems with bound ≤ n *)
(** Under P4: at each finite stage n, we see finitely-bounded systems *)
Definition at_stage (L : Level) (n : nat) (S : System L) : Prop :=
  level_bounded L n S.

(** Stage monotonicity: at_stage n ⊂ at_stage (n+1) *)
Lemma stage_monotone : forall L n sys,
  at_stage L n sys -> at_stage L (Datatypes.S n) sys.
Proof.
  intros L n sys H. unfold at_stage. apply level_bounded_monotone with n. exact H. lia.
Qed.

(** Embedding preserves finiteness: embed_obj preserves PosBound *)
Lemma embed_preserves_bound : forall L S,
  sys_pos_bound (LS L) (embed_obj L S) = sys_pos_bound L S.
Proof.
  intros L S. unfold embed_obj. simpl. reflexivity.
Qed.

(** Embedding preserves level-boundedness *)
Lemma embed_preserves_level_bounded : forall L n S,
  level_bounded L n S -> level_bounded (LS L) n (embed_obj L S).
Proof.
  intros L n S Hlb. unfold level_bounded in *.
  rewrite embed_preserves_bound. exact Hlb.
Qed.

(* ================================================================== *)
(*  Part II: Functors as Process Maps  (~10 lemmas)                   *)
(* ================================================================== *)

(** A process functor maps systems to systems at each level *)
Definition ProcessFunctor := forall L : Level, System L -> System L.

(** Identity process functor *)
Definition id_process_functor : ProcessFunctor := fun L S => S.

(** Identity preserves level-boundedness *)
Lemma id_functor_preserves_bound : forall L n S,
  level_bounded L n S -> level_bounded L n (id_process_functor L S).
Proof.
  intros L n S H. exact H.
Qed.

(** Composition of process functors *)
Definition compose_process_functor (F G : ProcessFunctor) : ProcessFunctor :=
  fun L S => F L (G L S).

(** Composition preserves level-boundedness if both components do *)
Lemma compose_preserves_bound : forall F G L n S,
  (forall L' m S', level_bounded L' m S' -> level_bounded L' m (G L' S')) ->
  (forall L' m S', level_bounded L' m S' -> level_bounded L' m (F L' S')) ->
  level_bounded L n S ->
  level_bounded L n (compose_process_functor F G L S).
Proof.
  intros F G L n S HG HF Hlb.
  unfold compose_process_functor. apply HF. apply HG. exact Hlb.
Qed.

(** Composition is associative *)
Lemma process_functor_assoc : forall (F G H : ProcessFunctor) L S,
  compose_process_functor F (compose_process_functor G H) L S =
  compose_process_functor (compose_process_functor F G) H L S.
Proof.
  intros. unfold compose_process_functor. reflexivity.
Qed.

(** Identity is left unit *)
Lemma process_functor_id_left : forall F L S,
  compose_process_functor id_process_functor F L S = F L S.
Proof.
  intros. unfold compose_process_functor, id_process_functor. reflexivity.
Qed.

(** Identity is right unit *)
Lemma process_functor_id_right : forall F L S,
  compose_process_functor F id_process_functor L S = F L S.
Proof.
  intros. unfold compose_process_functor, id_process_functor. reflexivity.
Qed.

(** EmbedFunctor as ProcessFunctor-like map: preserves finiteness *)
Lemma embed_is_process_map : forall L n S,
  level_bounded L n S ->
  level_bounded (LS L) n (embed_obj L S).
Proof.
  exact embed_preserves_level_bounded.
Qed.

(* ================================================================== *)
(*  Part III: Natural Transformations as Process Families  (~10 lemmas)*)
(* ================================================================== *)

(** A process natural transformation: family of morphisms indexed by level *)
(** At each level L, for each system S, provides a morphism *)
Definition ProcessNatTransComponent (L : Level) :=
  forall (S : System L), SystemMorphism L S S.

(** Identity natural transformation *)
Definition id_nat_trans (L : Level) : ProcessNatTransComponent L :=
  fun S => id_morphism L S.

(** The adjunction unit as natural transformation component *)
Definition unit_component (L : Level) (S : System L)
  : SystemMorphism L S (forget_obj L (embed_obj L S) (embed_is_forgettable L S)) :=
  adjunction_unit_component L S.

(** Unit component acts as identity on elements *)
Lemma unit_component_identity : forall L S (e : ElemOf L S),
  sm_map L S _ (unit_component L S) e = e.
Proof.
  intros L S e. reflexivity.
Qed.

(** Composition of nat trans components *)
Definition compose_nat_trans (L : Level)
  (alpha beta : ProcessNatTransComponent L) : ProcessNatTransComponent L :=
  fun S => compose_morphism L (alpha S) (beta S).

(** Composition with identity is identity (left) *)
Lemma nat_trans_id_left : forall L (alpha : ProcessNatTransComponent L) S,
  morphism_eq L (compose_nat_trans L (id_nat_trans L) alpha S) (alpha S).
Proof.
  intros L alpha S e. simpl.
  unfold compose_nat_trans, id_nat_trans, compose_morphism. simpl.
  reflexivity.
Qed.

(** Composition with identity is identity (right) *)
Lemma nat_trans_id_right : forall L (alpha : ProcessNatTransComponent L) S,
  morphism_eq L (compose_nat_trans L alpha (id_nat_trans L) S) (alpha S).
Proof.
  intros L alpha S e. simpl.
  unfold compose_nat_trans, id_nat_trans, compose_morphism. simpl.
  reflexivity.
Qed.

(** Composition is associative *)
Lemma nat_trans_assoc : forall L
  (alpha beta gamma : ProcessNatTransComponent L) S,
  morphism_eq L
    (compose_nat_trans L alpha (compose_nat_trans L beta gamma) S)
    (compose_nat_trans L (compose_nat_trans L alpha beta) gamma S).
Proof.
  intros L alpha beta gamma S e. simpl.
  unfold compose_nat_trans, compose_morphism. simpl.
  reflexivity.
Qed.

(** Morphism equality respects nat trans composition *)
Lemma nat_trans_compose_compat : forall L
  (a1 a2 b1 b2 : ProcessNatTransComponent L) S,
  (forall S', morphism_eq L (a1 S') (a2 S')) ->
  (forall S', morphism_eq L (b1 S') (b2 S')) ->
  morphism_eq L (compose_nat_trans L a1 b1 S) (compose_nat_trans L a2 b2 S).
Proof.
  intros L a1 a2 b1 b2 S Ha Hb e.
  unfold compose_nat_trans, compose_morphism. simpl.
  rewrite (Ha S e). rewrite (Hb S (sm_map L S S (a2 S) e)). reflexivity.
Qed.

(* ================================================================== *)
(*  Checks                                                              *)
(* ================================================================== *)

Check is_finite_system. Check level_bounded.
Check unbounded_not_level_bounded. Check finite_is_level_bounded.
Check level_bounded_monotone.
Check unit_level_bounded. Check finite_zero_bounded. Check LS_has_bounded_systems.
Check at_stage. Check stage_monotone.
Check embed_preserves_bound. Check embed_preserves_level_bounded.
Check ProcessFunctor. Check id_process_functor.
Check id_functor_preserves_bound. Check compose_process_functor.
Check compose_preserves_bound. Check process_functor_assoc.
Check process_functor_id_left. Check process_functor_id_right.
Check embed_is_process_map.
Check ProcessNatTransComponent. Check id_nat_trans.
Check unit_component. Check unit_component_identity.
Check compose_nat_trans.
Check nat_trans_id_left. Check nat_trans_id_right. Check nat_trans_assoc.
Check nat_trans_compose_compat.
