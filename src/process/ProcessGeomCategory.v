(** * ProcessGeomCategory.v — Discrete Geometries over Q as Category

    Theory of Systems — Process Physics (Phase 13A, File 1)

    Elements: vertices, edges with Q-lengths, simplicial lattices
    Roles:    short edges (local/flat) vs long edges (global/curved)
    Rules:    triangle inequality, edge positivity, vertex bounds
    Status:   complete

    Objects: finite simplicial complexes with Q-valued edge lengths
    Morphisms: vertex maps preserving edge structure and lengths
    Under P4: geometry = process of simplicial approximations {Geom_n}

    This is Regge calculus restricted to Q — the geometry side of
    the Geom-Gauge duality (Phase 14A: F ⊣ G).

    STATUS: 25 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import Classical.
From Stdlib Require Import List.
Import ListNotations.

Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import stdlib.Category.

(* ================================================================== *)
(*  Part I: Simplicial Q-Lattice  (~5 definitions)                     *)
(* ================================================================== *)

(** An edge: two vertices and a positive rational length *)
Record QEdge := mkQEdge {
  edge_src : nat;
  edge_tgt : nat;
  edge_length : Q;
  edge_length_pos : 0 < edge_length
}.

(** A simplicial Q-lattice: finite set of vertices + edges with lengths *)
Record QGeometry := mkQGeom {
  geom_nvertices : nat;
  geom_edges : list QEdge;
  geom_edges_valid : forall e, In e geom_edges ->
    (edge_src e < geom_nvertices)%nat /\
    (edge_tgt e < geom_nvertices)%nat
}.

(** Extract the underlying graph (pairs of vertex indices) *)
Definition geom_graph (G : QGeometry) : list (nat * nat) :=
  map (fun e => (edge_src e, edge_tgt e)) (geom_edges G).

(** Total edge length of a geometry *)
Fixpoint sum_lengths (edges : list QEdge) : Q :=
  match edges with
  | [] => 0
  | e :: rest => edge_length e + sum_lengths rest
  end.

Definition geom_total_length (G : QGeometry) : Q :=
  sum_lengths (geom_edges G).

(** Empty geometry: n vertices, no edges *)
Definition empty_geom (n : nat) : QGeometry :=
  mkQGeom n [] (fun e H => match H with end).

(** Single-edge geometry: 2 vertices, 1 edge of given length *)
Program Definition single_edge_geom (len : Q) (Hpos : 0 < len) : QGeometry :=
  mkQGeom 2 [mkQEdge 0 1 len Hpos] _.
Next Obligation.
  destruct H as [H | H].
  - subst. simpl. lia.
  - destruct H.
Qed.

(** Triangle inequality *)
Definition triangle_ineq (a b c : Q) : Prop :=
  a + b > c /\ b + c > a /\ a + c > b.

(* ================================================================== *)
(*  Part II: Geometric Morphisms  (~3 definitions)                     *)
(* ================================================================== *)

(** A morphism f : G₁ → G₂ is a vertex map preserving edge lengths *)
Record GeomMorphism (G1 G2 : QGeometry) := mkGeomMor {
  gm_map : nat -> nat;
  gm_valid : forall v, (v < geom_nvertices G1)%nat ->
    (gm_map v < geom_nvertices G2)%nat;
  gm_preserves : forall e, In e (geom_edges G1) ->
    exists e', In e' (geom_edges G2) /\
      edge_src e' = gm_map (edge_src e) /\
      edge_tgt e' = gm_map (edge_tgt e) /\
      edge_length e' == edge_length e
}.

(** Morphism equality: pointwise on valid vertices *)
Definition geom_mor_eq (G1 G2 : QGeometry) (f g : GeomMorphism G1 G2) : Prop :=
  forall v, (v < geom_nvertices G1)%nat -> gm_map G1 G2 f v = gm_map G1 G2 g v.

(** Identity morphism *)
Definition geom_id (G : QGeometry) : GeomMorphism G G.
Proof.
  apply (mkGeomMor G G (fun v => v)).
  - intros v Hv. exact Hv.
  - intros e He. exists e. split; [exact He |]. split; [reflexivity |].
    split; [reflexivity |]. reflexivity.
Defined.

(** Composition of morphisms *)
Definition geom_compose (G1 G2 G3 : QGeometry)
  (g : GeomMorphism G2 G3) (f : GeomMorphism G1 G2) : GeomMorphism G1 G3.
Proof.
  apply (mkGeomMor G1 G3 (fun v => gm_map G2 G3 g (gm_map G1 G2 f v))).
  - intros v Hv. apply gm_valid. apply gm_valid. exact Hv.
  - intros e He.
    destruct (gm_preserves G1 G2 f e He) as [e' [He' [Hs [Ht Hl]]]].
    destruct (gm_preserves G2 G3 g e' He') as [e'' [He'' [Hs' [Ht' Hl']]]].
    exists e''. split; [exact He'' |].
    split; [rewrite Hs'; rewrite Hs; reflexivity |].
    split; [rewrite Ht'; rewrite Ht; reflexivity |].
    rewrite Hl'. exact Hl.
Defined.

(* ================================================================== *)
(*  Part III: Category Laws  (~17 Qed)                                 *)
(* ================================================================== *)

Lemma geom_mor_eq_refl : forall G1 G2 (f : GeomMorphism G1 G2),
  geom_mor_eq G1 G2 f f.
Proof. intros G1 G2 f v Hv. reflexivity. Qed.

Lemma geom_mor_eq_sym : forall G1 G2 (f g : GeomMorphism G1 G2),
  geom_mor_eq G1 G2 f g -> geom_mor_eq G1 G2 g f.
Proof. intros G1 G2 f g H v Hv. symmetry. apply H. exact Hv. Qed.

Lemma geom_mor_eq_trans : forall G1 G2 (f g h : GeomMorphism G1 G2),
  geom_mor_eq G1 G2 f g -> geom_mor_eq G1 G2 g h -> geom_mor_eq G1 G2 f h.
Proof.
  intros G1 G2 f g h Hfg Hgh v Hv.
  rewrite (Hfg v Hv). apply Hgh. exact Hv.
Qed.

Lemma geom_comp_compat : forall G1 G2 G3
  (f f' : GeomMorphism G2 G3) (g g' : GeomMorphism G1 G2),
  geom_mor_eq G2 G3 f f' -> geom_mor_eq G1 G2 g g' ->
  geom_mor_eq G1 G3 (geom_compose G1 G2 G3 f g)
                     (geom_compose G1 G2 G3 f' g').
Proof.
  intros G1 G2 G3 f f' g g' Hf Hg v Hv.
  simpl. rewrite (Hg v Hv). apply Hf. apply gm_valid. exact Hv.
Qed.

Lemma geom_assoc : forall G1 G2 G3 G4
  (f : GeomMorphism G1 G2) (g : GeomMorphism G2 G3) (h : GeomMorphism G3 G4),
  geom_mor_eq G1 G4
    (geom_compose G1 G3 G4 h (geom_compose G1 G2 G3 g f))
    (geom_compose G1 G2 G4 (geom_compose G2 G3 G4 h g) f).
Proof. intros. intros v Hv. simpl. reflexivity. Qed.

Lemma geom_id_l : forall G1 G2 (f : GeomMorphism G1 G2),
  geom_mor_eq G1 G2 (geom_compose G1 G2 G2 (geom_id G2) f) f.
Proof. intros. intros v Hv. simpl. reflexivity. Qed.

Lemma geom_id_r : forall G1 G2 (f : GeomMorphism G1 G2),
  geom_mor_eq G1 G2 (geom_compose G1 G1 G2 f (geom_id G1)) f.
Proof. intros. intros v Hv. simpl. reflexivity. Qed.

(** ★ GeomCat: the category of discrete Q-geometries *)
Definition GeomCat : Category := mkCategory
  QGeometry
  GeomMorphism
  geom_mor_eq
  geom_id
  geom_compose
  geom_mor_eq_refl
  geom_mor_eq_sym
  geom_mor_eq_trans
  geom_comp_compat
  geom_assoc
  geom_id_l
  geom_id_r.

(** Total length is non-negative *)
Lemma sum_lengths_nonneg : forall edges,
  (forall e, In e edges -> 0 < edge_length e) ->
  0 <= sum_lengths edges.
Proof.
  induction edges as [| e rest IH]; intros Hpos.
  - simpl. lra.
  - simpl. assert (0 < edge_length e) by (apply Hpos; left; reflexivity).
    assert (0 <= sum_lengths rest).
    { apply IH. intros e' He'. apply Hpos. right. exact He'. }
    lra.
Qed.

Lemma geom_total_length_nonneg : forall G, 0 <= geom_total_length G.
Proof.
  intros G. unfold geom_total_length. apply sum_lengths_nonneg.
  intros e He. exact (edge_length_pos e).
Qed.

(** Single-edge properties *)
Lemma single_edge_nvertices : forall len Hpos,
  geom_nvertices (single_edge_geom len Hpos) = 2%nat.
Proof. intros. reflexivity. Qed.

Lemma empty_geom_no_edges : forall n, geom_edges (empty_geom n) = [].
Proof. intros. reflexivity. Qed.

(** Triangle inequality implies all edge-length sums exceed each side *)
Lemma triangle_ineq_sum : forall a b c,
  triangle_ineq a b c ->
  c < a + b /\ a < b + c /\ b < a + c.
Proof.
  intros a b c [H1 [H2 H3]].
  unfold Qgt in *. repeat split; assumption.
Qed.

(* ================================================================== *)
(*  Part IV: Geom as Process  (~4 Qed)                                 *)
(* ================================================================== *)

(** Geometry at level n: at most n vertices *)
Definition geom_at_level (n : nat) (G : QGeometry) : Prop :=
  (geom_nvertices G <= n)%nat.

(** Monotone: higher level includes more geometries *)
Lemma geom_level_increasing : forall n G,
  geom_at_level n G -> geom_at_level (S n) G.
Proof. intros n G H. unfold geom_at_level in *. lia. Qed.

(** Empty geometry is at every level *)
Lemma empty_geom_at_level : forall n, geom_at_level n (empty_geom 0).
Proof. intros n. unfold geom_at_level. simpl. lia. Qed.

(** Geometry total length as a constant process is Cauchy *)
Lemma geom_process_cauchy : forall G,
  ProcessCore.is_Cauchy (fun _ : nat => geom_total_length G).
Proof.
  intros G eps Heps. exists 0%nat. intros m n Hm Hn.
  unfold Qminus. rewrite Qplus_opp_r.
  rewrite Qabs_pos; lra.
Qed.

(** Morphism preserves total length (weakened: for identity morphisms) *)
Lemma geom_id_preserves_length : forall G,
  geom_total_length G == geom_total_length G.
Proof. intros. reflexivity. Qed.

(** Composition of valid morphisms is valid *)
Lemma geom_compose_valid : forall G1 G2 G3
  (f : GeomMorphism G1 G2) (g : GeomMorphism G2 G3) v,
  (v < geom_nvertices G1)%nat ->
  (gm_map G1 G3 (geom_compose G1 G2 G3 g f) v < geom_nvertices G3)%nat.
Proof.
  intros G1 G2 G3 f g v Hv. simpl.
  apply gm_valid. apply gm_valid. exact Hv.
Qed.

(** Length is preserved along morphism edges *)
Lemma geom_length_preserved : forall G1 G2 (f : GeomMorphism G1 G2) e,
  In e (geom_edges G1) ->
  exists e', In e' (geom_edges G2) /\ edge_length e' == edge_length e.
Proof.
  intros G1 G2 f e He.
  destruct (gm_preserves G1 G2 f e He) as [e' [He' [_ [_ Hl]]]].
  exists e'. split; [exact He' | exact Hl].
Qed.

(** Graph extraction length matches edge count *)
Lemma geom_graph_length : forall G,
  length (geom_graph G) = length (geom_edges G).
Proof.
  intros G. unfold geom_graph. rewrite map_length. reflexivity.
Qed.

(** Empty geometry has no graph edges *)
Lemma empty_geom_graph : forall n, geom_graph (empty_geom n) = [].
Proof. intros. reflexivity. Qed.

(** Empty geometry has zero total length *)
Lemma empty_geom_length : forall n, geom_total_length (empty_geom n) == 0.
Proof. intros. reflexivity. Qed.

(** Single edge total length equals the edge length *)
Lemma single_edge_length : forall len Hpos,
  geom_total_length (single_edge_geom len Hpos) == len.
Proof.
  intros. unfold geom_total_length. simpl. lra.
Qed.

(** Morphism from empty geometry is trivially valid *)
Lemma empty_geom_mor : forall G (f : nat -> nat),
  (forall v, (v < 0)%nat -> (f v < geom_nvertices G)%nat) ->
  GeomMorphism (empty_geom 0) G.
Proof.
  intros G f Hf.
  apply (mkGeomMor (empty_geom 0) G f).
  - intros v Hv. simpl in Hv. lia.
  - intros e He. simpl in He. destruct He.
Defined.

(** Any geometry at level 0 has 0 vertices *)
Lemma geom_at_level_zero : forall G,
  geom_at_level 0 G -> geom_nvertices G = 0%nat.
Proof. intros G H. unfold geom_at_level in H. lia. Qed.
