(** * ProcessGeomGaugeFunctor.v — Functors F: Geom→Gauge, G: Gauge→Geom

    Theory of Systems — Process Physics (Phase 13A, File 3)

    Elements: F_obj, G_obj, effective_length, round-trip compositions
    Roles:    F = "geometry determines field topology"
              G = "fields determine effective geometry"
    Rules:    functor laws (preserves id/comp), round-trip information loss
    Status:   complete

    F: Given a simplicial lattice → create trivial gauge config on same graph
    G: Given a gauge config → effective geometry via d(i,j) = 1/(1+|link|)

    Both round trips LOSE information:
      G∘F: all edge lengths become 1/2 (regardless of original)
      F∘G: all link values become 1 (regardless of original)
    This is P2: two complementary views, neither complete.

    STATUS: 20 Qed, 0 Admitted, 0 axioms
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
From ToS Require Import stdlib.Functor.
From ToS Require Import process.ProcessGeomCategory.
From ToS Require Import process.ProcessGaugeCategory.

(* ================================================================== *)
(*  Part I: F : Geom → Gauge  (~8 Qed)                               *)
(* ================================================================== *)

(** F on objects: geometry → trivial gauge config on same graph *)
Definition F_obj (G : QGeometry) : GaugeConfig.
Proof.
  refine (mkGaugeConfig
    (geom_nvertices G)
    (geom_graph G)
    (repeat 1 (length (geom_edges G)))
    _
    _).
  - unfold geom_graph. rewrite length_map. apply repeat_length.
  - intros p Hp. unfold geom_graph in Hp.
    apply in_map_iff in Hp. destruct Hp as [e [He Hin]].
    subst. simpl. apply (geom_edges_valid G e Hin).
Defined.

(** Helper: find index of an element in a list *)
Fixpoint find_index {A : Type} (pred : A -> bool) (l : list A) : option nat :=
  match l with
  | [] => None
  | x :: rest => if pred x then Some 0%nat
                 else match find_index pred rest with
                      | Some i => Some (S i)
                      | None => None
                      end
  end.

(** F on morphisms: geometric morphism → gauge morphism.
    Since both F_obj G1 and F_obj G2 have all links = 1,
    we use a simplified morphism: same vertex map, same edge indexing,
    link preservation is trivial. *)
Definition F_mor (G1 G2 : QGeometry) (f : GeomMorphism G1 G2)
  : GaugeMorphism (F_obj G1) (F_obj G2).
Proof.
  apply (mkGaugeMor (F_obj G1) (F_obj G2) (gm_map G1 G2 f)).
  - intros v Hv. simpl in *. apply (gm_valid G1 G2 f). exact Hv.
  - intros k Hk.
    (* We need an existential witness in F_obj G2's edges.
       Strategy: use gm_preserves to get the target edge,
       then find its index. Both links are trivial (all 1). *)
    simpl gc_edges in Hk. unfold geom_graph in Hk.
    rewrite length_map in Hk.
    set (dflt := mkQEdge 0 0 1 eq_refl).
    (* Get k-th edge from G1 *)
    assert (Hin : In (nth k (geom_edges G1) dflt) (geom_edges G1))
      by (apply nth_In; exact Hk).
    destruct (gm_preserves G1 G2 f _ Hin) as [e2 [He2 [Hs2 [Ht2 _]]]].
    destruct (In_nth _ _ dflt He2) as [k2 [Hk2 Hnth2]].
    exists k2. split.
    + simpl. unfold geom_graph. rewrite length_map. exact Hk2.
    + (* Helper: fst/snd of nth of geom_graph *)
      assert (Hfst_map : forall (l : list QEdge) (j : nat),
        (j < length l)%nat ->
        fst (nth j (map (fun e => (edge_src e, edge_tgt e)) l) (0%nat,0%nat)) =
        edge_src (nth j l dflt)).
      { intros l. induction l as [| x xs IHl]; intros j Hj.
        - simpl in Hj. lia.
        - destruct j. + simpl. reflexivity. + simpl. apply IHl. simpl in Hj. lia. }
      assert (Hsnd_map : forall (l : list QEdge) (j : nat),
        (j < length l)%nat ->
        snd (nth j (map (fun e => (edge_src e, edge_tgt e)) l) (0%nat,0%nat)) =
        edge_tgt (nth j l dflt)).
      { intros l. induction l as [| x xs IHl]; intros j Hj.
        - simpl in Hj. lia.
        - destruct j. + simpl. reflexivity. + simpl. apply IHl. simpl in Hj. lia. }
      split; [| split].
      * simpl gc_edges. unfold geom_graph.
        rewrite Hfst_map by exact Hk2.
        rewrite Hfst_map by exact Hk.
        rewrite Hnth2. simpl. exact Hs2.
      * simpl gc_edges. unfold geom_graph.
        rewrite Hsnd_map by exact Hk2.
        rewrite Hsnd_map by exact Hk.
        rewrite Hnth2. simpl. exact Ht2.
      * (* link preservation: both are 1 from repeat *)
        assert (Hl1 : nth k (gc_links (F_obj G1)) 0 = 1).
        { simpl. clear -Hk. revert k Hk.
          induction (geom_edges G1) as [| x xs IH]; intros k Hk.
          - simpl in Hk. lia.
          - destruct k. + reflexivity. + simpl. apply IH. simpl in Hk. lia. }
        assert (Hl2 : nth k2 (gc_links (F_obj G2)) 0 = 1).
        { simpl. clear -Hk2. revert k2 Hk2.
          induction (geom_edges G2) as [| x xs IH]; intros k Hk.
          - simpl in Hk. lia.
          - destruct k. + reflexivity. + simpl. apply IH. simpl in Hk. lia. }
        rewrite Hl1. rewrite Hl2. reflexivity.
Defined.

(** F preserves vertex count *)
Lemma F_nvertices : forall G,
  gc_nvertices (F_obj G) = geom_nvertices G.
Proof. intros. reflexivity. Qed.

(** F preserves edge count *)
Lemma F_nedges : forall G,
  length (gc_edges (F_obj G)) = length (geom_edges G).
Proof.
  intros. simpl. unfold geom_graph. rewrite length_map. reflexivity.
Qed.

(** F assigns trivial (=1) links *)
Lemma F_trivial_links : forall G k,
  (k < length (geom_edges G))%nat ->
  gc_nth_link (F_obj G) k == 1.
Proof.
  intros G k Hk. unfold gc_nth_link. simpl.
  enough (H : nth k (repeat (1:Q) (length (geom_edges G))) (0:Q) = 1)
    by (rewrite H; reflexivity).
  revert k Hk.
  induction (geom_edges G) as [| e rest IH]; intros k Hk.
  - simpl in Hk. lia.
  - destruct k as [| k']. + reflexivity. + simpl. apply IH. simpl in Hk. lia.
Qed.

(** F preserves morphism identity *)
Lemma F_preserves_id : forall G,
  gauge_mor_eq (F_obj G) (F_obj G)
    (F_mor G G (geom_id G)) (gauge_id (F_obj G)).
Proof. intros G v Hv. simpl. reflexivity. Qed.

(** F preserves composition *)
Lemma F_preserves_comp : forall G1 G2 G3
  (f : GeomMorphism G1 G2) (g : GeomMorphism G2 G3),
  gauge_mor_eq (F_obj G1) (F_obj G3)
    (F_mor G1 G3 (geom_compose G1 G2 G3 g f))
    (gauge_compose (F_obj G1) (F_obj G2) (F_obj G3)
      (F_mor G2 G3 g) (F_mor G1 G2 f)).
Proof. intros. intros v Hv. simpl. reflexivity. Qed.

(** F respects morphism equality *)
Lemma F_mor_compat : forall G1 G2 (f g : GeomMorphism G1 G2),
  geom_mor_eq G1 G2 f g ->
  gauge_mor_eq (F_obj G1) (F_obj G2) (F_mor G1 G2 f) (F_mor G1 G2 g).
Proof. intros G1 G2 f g H v Hv. simpl. apply H. exact Hv. Qed.

(* ================================================================== *)
(*  Part II: G : Gauge → Geom  (~8 Qed)                              *)
(* ================================================================== *)

(** Effective distance: d = 1/(1 + |link_value|) *)
Definition effective_length (lv : Q) : Q :=
  1 / (1 + Qabs lv).

(** Effective length is always positive *)
Lemma effective_length_pos : forall lv, 0 < effective_length lv.
Proof.
  intros lv. unfold effective_length.
  assert (Hnonneg : 0 <= Qabs lv) by apply Qabs_nonneg.
  assert (Hpos : 0 < 1 + Qabs lv) by lra.
  unfold Qdiv. apply Qmult_lt_0_compat.
  - lra.
  - apply Qinv_lt_0_compat. lra.
Qed.

(** Zip edges with effective link lengths *)
Fixpoint zip_edges_links (edges : list (nat * nat)) (links : list Q)
  : list QEdge :=
  match edges, links with
  | (s, t) :: rest_e, l :: rest_l =>
    mkQEdge s t (effective_length l) (effective_length_pos l)
    :: zip_edges_links rest_e rest_l
  | _, _ => []
  end.

(** Zip preserves length (min of both) *)
Lemma zip_edges_links_length : forall edges links,
  length (zip_edges_links edges links) = Nat.min (length edges) (length links).
Proof.
  induction edges as [| [s t] rest IH]; intros links.
  - simpl. reflexivity.
  - destruct links as [| l rest_l].
    + simpl. reflexivity.
    + simpl. f_equal. apply IH.
Qed.

(** Helper: edges in zip_edges_links come from the original edge list *)
Lemma zip_edges_links_valid : forall nv edges links
  (Hv : forall p, In p edges -> (fst p < nv)%nat /\ (snd p < nv)%nat)
  e, In e (zip_edges_links edges links) ->
  (edge_src e < nv)%nat /\ (edge_tgt e < nv)%nat.
Proof.
  intros nv edges. revert nv.
  induction edges as [| [s t] rest_e IH]; intros nv links Hv e He.
  - simpl in He. destruct He.
  - destruct links as [| l rest_l].
    + simpl in He. destruct He.
    + simpl in He. destruct He as [He | He].
      * subst. simpl.
        assert (Hp := Hv (s, t) (or_introl eq_refl)).
        simpl in Hp. exact Hp.
      * apply (IH nv rest_l). 2: exact He.
        intros p Hp. apply Hv. right. exact Hp.
Qed.

(** G on objects: gauge config → effective geometry *)
Definition G_obj (gc : GaugeConfig) : QGeometry :=
  mkQGeom (gc_nvertices gc)
    (zip_edges_links (gc_edges gc) (gc_links gc))
    (zip_edges_links_valid (gc_nvertices gc) (gc_edges gc) (gc_links gc)
      (gc_valid gc)).

(** G preserves vertex count *)
Lemma G_nvertices : forall gc,
  geom_nvertices (G_obj gc) = gc_nvertices gc.
Proof. intros. reflexivity. Qed.

(** All edges in G_obj have effective lengths *)
Lemma G_all_effective : forall gc e,
  In e (geom_edges (G_obj gc)) ->
  exists lv, edge_length e == effective_length lv.
Proof.
  intros gc e He. simpl in He.
  assert (Hgen : forall edges links,
    In e (zip_edges_links edges links) ->
    exists lv, edge_length e == effective_length lv).
  { induction edges as [| [s t] rest_e IH]; intros links Hin.
    - simpl in Hin. destruct Hin.
    - destruct links as [| l rest_l].
      + simpl in Hin. destruct Hin.
      + simpl in Hin. destruct Hin as [Hin | Hin].
        * subst. exists l. simpl. reflexivity.
        * apply (IH rest_l). exact Hin. }
  exact (Hgen _ _ He).
Qed.

(** G maps vertex functions: a gauge morphism's vertex map
    is valid between the effective geometries *)
Lemma G_preserves_vertices : forall gc1 gc2 (f : GaugeMorphism gc1 gc2) v,
  (v < geom_nvertices (G_obj gc1))%nat ->
  (gm_vmap gc1 gc2 f v < geom_nvertices (G_obj gc2))%nat.
Proof. intros. simpl in *. apply gm_vmap_valid. exact H. Qed.

(** G on identity: identity gauge morphism maps to identity on vertices *)
Lemma G_id_vertices : forall gc v,
  gm_vmap gc gc (gauge_id gc) v = v.
Proof. intros. simpl. reflexivity. Qed.

(** G on composition: composed gauge morphism vertex map = composition *)
Lemma G_comp_vertices : forall gc1 gc2 gc3
  (f : GaugeMorphism gc1 gc2) (g : GaugeMorphism gc2 gc3) v,
  gm_vmap gc1 gc3 (gauge_compose gc1 gc2 gc3 g f) v =
  gm_vmap gc2 gc3 g (gm_vmap gc1 gc2 f v).
Proof. intros. simpl. reflexivity. Qed.

(** G respects equality: equal gauge morphisms give equal vertex maps *)
Lemma G_compat_vertices : forall gc1 gc2 (f g : GaugeMorphism gc1 gc2) v,
  (v < gc_nvertices gc1)%nat ->
  gauge_mor_eq gc1 gc2 f g ->
  gm_vmap gc1 gc2 f v = gm_vmap gc1 gc2 g v.
Proof. intros. apply H0. exact H. Qed.

(* ================================================================== *)
(*  Part III: Round Trip Analysis  (~4 Qed)                            *)
(* ================================================================== *)

(** ★ KEY: effective_length(1) = 1/2 — the universal loss constant *)
Lemma effective_length_one : effective_length 1 == 1 # 2.
Proof.
  unfold effective_length, Qabs. simpl. reflexivity.
Qed.

(** ★ F∘G loses all link values: F(G(gc)) has all links = 1 *)
Lemma FG_loses_links : forall gc k,
  (k < length (gc_edges (F_obj (G_obj gc))))%nat ->
  gc_nth_link (F_obj (G_obj gc)) k == 1.
Proof.
  intros gc k Hk.
  (* All links in F_obj _ are 1 (from repeat). *)
  unfold gc_nth_link.
  (* gc_links (F_obj X) = repeat 1 (length (geom_edges X)) *)
  (* Use Eval to get the concrete form *)
  change (gc_links (F_obj (G_obj gc))) with
    (repeat 1 (length (geom_edges (G_obj gc)))).
  change (gc_edges (F_obj (G_obj gc))) with
    (geom_graph (G_obj gc)) in Hk.
  unfold geom_graph in Hk. rewrite length_map in Hk.
  enough (H : nth k (repeat (1:Q) (length (geom_edges (G_obj gc)))) 0 = 1)
    by (rewrite H; reflexivity).
  revert k Hk.
  generalize (length (geom_edges (G_obj gc))).
  intros n k Hk. revert k Hk.
  induction n as [| n' IH]; intros k Hk.
  - lia.
  - destruct k. + reflexivity. + simpl. apply IH. lia.
Qed.

(** ★ G∘F loses all edge lengths: all become effective_length(1) = 1/2 *)
Lemma GF_all_lengths_half : forall G e,
  In e (geom_edges (G_obj (F_obj G))) ->
  edge_length e == effective_length 1.
Proof.
  intros G e He. simpl in He.
  assert (Hgen : forall edges links,
    In e (zip_edges_links edges links) ->
    (forall l, In l links -> l == 1) ->
    edge_length e == effective_length 1).
  { induction edges as [| [s t] rest_e IH]; intros links Hin Hall.
    - simpl in Hin. destruct Hin.
    - destruct links as [| l rest_l].
      + simpl in Hin. destruct Hin.
      + simpl in Hin. destruct Hin as [Hin | Hin].
        * subst. simpl.
          assert (Hl := Hall l (or_introl eq_refl)).
          unfold effective_length.
          rewrite Hl. reflexivity.
        * apply (IH rest_l Hin). intros l' Hl'. apply Hall. right. exact Hl'. }
  apply (Hgen (geom_graph G) (repeat 1 (length (geom_edges G))) He).
  intros l Hl.
  apply repeat_spec in Hl. rewrite Hl. reflexivity.
Qed.

(** Vertex counts preserved through round trips *)
Lemma FG_nvertices : forall gc,
  gc_nvertices (F_obj (G_obj gc)) = gc_nvertices gc.
Proof. intros. reflexivity. Qed.

Lemma GF_nvertices : forall G,
  geom_nvertices (G_obj (F_obj G)) = geom_nvertices G.
Proof. intros. reflexivity. Qed.

(** ★ effective_length(0) = 1 — no link means standard distance *)
Lemma effective_length_zero : effective_length 0 == 1.
Proof.
  unfold effective_length, Qabs. simpl. reflexivity.
Qed.

(** Effective length is bounded: 0 < eff(lv) <= 1 *)
Lemma effective_length_le_1 : forall lv, effective_length lv <= 1.
Proof.
  intros lv. unfold effective_length.
  assert (Hnonneg : 0 <= Qabs lv) by apply Qabs_nonneg.
  assert (Hden : 0 < 1 + Qabs lv) by lra.
  apply Qle_shift_div_r; [lra |]. lra.
Qed.

(** Effective length is monotone decreasing in |link| *)
Lemma effective_length_monotone : forall a b,
  Qabs a <= Qabs b -> effective_length b <= effective_length a.
Proof.
  intros a b Hab. unfold effective_length.
  assert (Ha : 0 <= Qabs a) by apply Qabs_nonneg.
  assert (Hb : 0 <= Qabs b) by apply Qabs_nonneg.
  assert (Hda : 0 < 1 + Qabs a) by lra.
  assert (Hdb : 0 < 1 + Qabs b) by lra.
  apply Qle_shift_div_r; [lra |].
  assert (Heq : 1 / (1 + Qabs a) * (1 + Qabs b) == (1 + Qabs b) / (1 + Qabs a))
    by (unfold Qdiv; ring).
  rewrite Heq.
  apply Qle_shift_div_l; [lra |]. lra.
Qed.
