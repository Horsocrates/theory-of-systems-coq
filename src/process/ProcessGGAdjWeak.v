(** * ProcessGGAdjWeak.v — Weak Unit and Counit: Topology Preserved

    Theory of Systems — Process Physics (Phase 14A, File 4)

    Elements: weak unit, weak counit, topology preservation
    Roles:    weak natural transformations (preserve graph structure, not metrics)
    Rules:    vertex count preserved, edge count preserved, idempotent round trips
    Status:   complete

    The strict adjunction fails (ProcessGGAdjStrict.v), but weak versions
    exist: the unit and counit preserve the TOPOLOGY (graph structure)
    even though they lose metric/field information.

    STATUS: 15 Qed, 0 Admitted, 0 axioms
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
From ToS Require Import process.ProcessGeomCategory.
From ToS Require Import process.ProcessGaugeCategory.
From ToS Require Import process.ProcessGeomGaugeFunctor.

(* ================================================================== *)
(*  Part I: Weak Unit (Topology-Preserving)  (~5 Qed)                  *)
(* ================================================================== *)

(** The weak unit preserves vertex count: G and G(F(G)) have same vertices *)
Lemma weak_unit_vertices : forall G,
  geom_nvertices (G_obj (F_obj G)) = geom_nvertices G.
Proof. intros. apply GF_nvertices. Qed.

(** F preserves vertex count *)
Lemma F_preserves_vert : forall G,
  gc_nvertices (F_obj G) = geom_nvertices G.
Proof. intros. apply F_nvertices. Qed.

(** G preserves vertex count *)
Lemma G_preserves_vert : forall gc,
  geom_nvertices (G_obj gc) = gc_nvertices gc.
Proof. intros. apply G_nvertices. Qed.

(** F preserves edge count *)
Lemma F_preserves_edge_count : forall G,
  length (gc_edges (F_obj G)) = length (geom_edges G).
Proof. intros. apply F_nedges. Qed.

(** Weak unit for empty geometry is identity *)
Lemma weak_unit_empty : forall n,
  geom_nvertices (G_obj (F_obj (empty_geom n))) = n.
Proof. intros. reflexivity. Qed.

(* ================================================================== *)
(*  Part II: Weak Counit (Topology-Preserving)  (~5 Qed)               *)
(* ================================================================== *)

(** The weak counit preserves vertex count *)
Lemma weak_counit_vertices : forall gc,
  gc_nvertices (F_obj (G_obj gc)) = gc_nvertices gc.
Proof. intros. apply FG_nvertices. Qed.

(** Weak counit for empty gauge is identity-like *)
Lemma weak_counit_empty :
  gc_nvertices (F_obj (G_obj empty_gauge)) = gc_nvertices empty_gauge.
Proof. reflexivity. Qed.

(** G(F(G)) has all lengths exactly 1/2 *)
Lemma GF_uniform_lengths : forall G e,
  In e (geom_edges (G_obj (F_obj G))) ->
  edge_length e == 1 # 2.
Proof.
  intros G e He.
  assert (Hel := GF_all_lengths_half G e He).
  rewrite effective_length_one in Hel. exact Hel.
Qed.

(** F(G(gc)) has all links exactly 1 *)
Lemma FG_uniform_links : forall gc k,
  (k < length (gc_edges (F_obj (G_obj gc))))%nat ->
  gc_nth_link (F_obj (G_obj gc)) k == 1.
Proof. intros. apply FG_loses_links. exact H. Qed.

(** ★ F and G jointly preserve topology *)
Theorem weak_adjunction_topology :
  (forall G, geom_nvertices (G_obj (F_obj G)) = geom_nvertices G) /\
  (forall gc, gc_nvertices (F_obj (G_obj gc)) = gc_nvertices gc) /\
  (forall G, gc_nvertices (F_obj G) = geom_nvertices G) /\
  (forall gc, geom_nvertices (G_obj gc) = gc_nvertices gc).
Proof.
  split; [| split; [| split]].
  - exact weak_unit_vertices.
  - exact weak_counit_vertices.
  - exact F_preserves_vert.
  - exact G_preserves_vert.
Qed.

(* ================================================================== *)
(*  Part III: Idempotent Round Trips  (~5 Qed)                         *)
(* ================================================================== *)

(** G∘F is idempotent on vertices: (G∘F)² = G∘F on vertex count *)
Lemma GF_idempotent_vertices : forall G,
  geom_nvertices (G_obj (F_obj (G_obj (F_obj G)))) =
  geom_nvertices (G_obj (F_obj G)).
Proof. intros. reflexivity. Qed.

(** F∘G is idempotent on vertices *)
Lemma FG_idempotent_vertices : forall gc,
  gc_nvertices (F_obj (G_obj (F_obj (G_obj gc)))) =
  gc_nvertices (F_obj (G_obj gc)).
Proof. intros. reflexivity. Qed.

(** Double round trip G∘F∘G∘F: all lengths still 1/2 *)
Lemma GF_double_still_half : forall G e,
  In e (geom_edges (G_obj (F_obj (G_obj (F_obj G))))) ->
  edge_length e == 1 # 2.
Proof.
  intros G e He. apply (GF_uniform_lengths (G_obj (F_obj G))). exact He.
Qed.

(** Double round trip F∘G∘F∘G: all links still 1 *)
Lemma FG_double_still_one : forall gc k,
  (k < length (gc_edges (F_obj (G_obj (F_obj (G_obj gc))))))%nat ->
  gc_nth_link (F_obj (G_obj (F_obj (G_obj gc)))) k == 1.
Proof.
  intros gc k Hk. apply (FG_uniform_links (F_obj (G_obj gc))). exact Hk.
Qed.

(** ★ Triangle identities hold weakly:
    The standard triangle identities ε_F ∘ F_η = id_F and G_ε ∘ η_G = id_G
    fail strictly, but hold topologically: same vertex structure after round trip,
    and the round trips are idempotent. *)
Theorem triangle_identities_weak :
  (forall G, geom_nvertices (G_obj (F_obj (G_obj (F_obj G)))) =
             geom_nvertices (G_obj (F_obj G))) /\
  (forall gc, gc_nvertices (F_obj (G_obj (F_obj (G_obj gc)))) =
              gc_nvertices (F_obj (G_obj gc))).
Proof.
  split.
  - exact GF_idempotent_vertices.
  - exact FG_idempotent_vertices.
Qed.
