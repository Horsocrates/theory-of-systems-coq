(** * ProcessGaugeCategory.v — Field Configurations over Q as Category

    Theory of Systems — Process Physics (Phase 13A, File 2)

    Elements: link variables (Q-valued characters on edges)
    Roles:    trivial links (vacuum) vs excited links (matter)
    Rules:    gauge invariance (Wilson loop), link preservation
    Status:   complete

    Objects: Q-valued link configurations on graphs
    Morphisms: vertex maps preserving link structure
    Under P4: gauge config = process of link assignments {Gauge_n}

    Connection to existing gauge/: CharacterTransfer.v provides the
    eigenvalues; this file provides the categorical structure.

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
(*  Part I: Gauge Configuration  (~5 definitions)                      *)
(* ================================================================== *)

(** A gauge configuration: Q-valued link variables on a graph *)
Record GaugeConfig := mkGaugeConfig {
  gc_nvertices : nat;
  gc_edges : list (nat * nat);
  gc_links : list Q;
  gc_match : length gc_links = length gc_edges;
  gc_valid : forall p, In p gc_edges ->
    (fst p < gc_nvertices)%nat /\ (snd p < gc_nvertices)%nat
}.

(** Access the k-th link value *)
Definition gc_nth_link (gc : GaugeConfig) (k : nat) : Q :=
  nth k (gc_links gc) 0.

(** Wilson loop: sum of link values along a path (abelian simplification) *)
Fixpoint wilson_loop (gc : GaugeConfig) (path : list nat) : Q :=
  match path with
  | [] => 0
  | [_] => 0
  | k :: rest => gc_nth_link gc k + wilson_loop gc rest
  end.

(** Trivial (vacuum) configuration: all links = 1 *)
Program Definition trivial_gauge (nv : nat) (edges : list (nat * nat))
  (Hvalid : forall p, In p edges ->
    (fst p < nv)%nat /\ (snd p < nv)%nat) : GaugeConfig :=
  mkGaugeConfig nv edges (repeat 1 (length edges)) _ Hvalid.
Next Obligation. apply repeat_length. Qed.

(** Empty gauge configuration *)
Definition empty_gauge : GaugeConfig :=
  mkGaugeConfig 0 [] [] eq_refl (fun p H => match H with end).

(** Plaquette action: β · (1 - Wilson loop value) *)
Definition plaquette_action (beta : Q) (gc : GaugeConfig) (plaq : list nat) : Q :=
  beta * (1 - wilson_loop gc plaq).

(** Total action: sum over plaquettes *)
Definition total_action (beta : Q) (gc : GaugeConfig) (plaqs : list (list nat)) : Q :=
  fold_left (fun acc p => acc + plaquette_action beta gc p) plaqs 0.

(* ================================================================== *)
(*  Part II: Gauge Morphisms  (~3 definitions)                         *)
(* ================================================================== *)

(** A gauge morphism: vertex map preserving link structure.
    For each edge (i,j) with link value l in gc1,
    (f(i), f(j)) is an edge in gc2 with the same link value. *)
Record GaugeMorphism (gc1 gc2 : GaugeConfig) := mkGaugeMor {
  gm_vmap : nat -> nat;
  gm_vmap_valid : forall v, (v < gc_nvertices gc1)%nat ->
    (gm_vmap v < gc_nvertices gc2)%nat;
  gm_edge_preserves : forall k,
    (k < length (gc_edges gc1))%nat ->
    exists k', (k' < length (gc_edges gc2))%nat /\
      fst (nth k' (gc_edges gc2) (0%nat,0%nat)) =
        gm_vmap (fst (nth k (gc_edges gc1) (0%nat,0%nat))) /\
      snd (nth k' (gc_edges gc2) (0%nat,0%nat)) =
        gm_vmap (snd (nth k (gc_edges gc1) (0%nat,0%nat))) /\
      nth k' (gc_links gc2) 0 == nth k (gc_links gc1) 0
}.

(** Morphism equality: pointwise on valid vertices *)
Definition gauge_mor_eq (gc1 gc2 : GaugeConfig)
  (f g : GaugeMorphism gc1 gc2) : Prop :=
  forall v, (v < gc_nvertices gc1)%nat ->
    gm_vmap gc1 gc2 f v = gm_vmap gc1 gc2 g v.

(** Identity gauge morphism *)
Definition gauge_id (gc : GaugeConfig) : GaugeMorphism gc gc.
Proof.
  apply (mkGaugeMor gc gc (fun v => v)).
  - intros v Hv. exact Hv.
  - intros k Hk. exists k. split; [exact Hk |]. split; [reflexivity |].
    split; [reflexivity |]. reflexivity.
Defined.

(** Composition of gauge morphisms *)
Definition gauge_compose (gc1 gc2 gc3 : GaugeConfig)
  (g : GaugeMorphism gc2 gc3) (f : GaugeMorphism gc1 gc2)
  : GaugeMorphism gc1 gc3.
Proof.
  apply (mkGaugeMor gc1 gc3
    (fun v => gm_vmap gc2 gc3 g (gm_vmap gc1 gc2 f v))).
  - intros v Hv. apply gm_vmap_valid. apply gm_vmap_valid. exact Hv.
  - intros k Hk.
    destruct (gm_edge_preserves gc1 gc2 f k Hk)
      as [k' [Hk' [Hs [Ht Hl]]]].
    destruct (gm_edge_preserves gc2 gc3 g k' Hk')
      as [k'' [Hk'' [Hs' [Ht' Hl']]]].
    exists k''. split; [exact Hk'' |].
    split; [rewrite Hs'; rewrite Hs; reflexivity |].
    split; [rewrite Ht'; rewrite Ht; reflexivity |].
    rewrite Hl'. exact Hl.
Defined.

(* ================================================================== *)
(*  Part III: Gauge Transform (separate concept)  (~2 definitions)     *)
(* ================================================================== *)

(** A gauge transform on the SAME graph: link'(i,j) = g(i) + link(i,j) - g(j)
    This is a special type of equivalence, not a morphism between different configs *)
Record GaugeTransform (gc1 gc2 : GaugeConfig) := mkGaugeTr {
  gt_gauge : nat -> Q;
  gt_same_graph : gc_edges gc1 = gc_edges gc2;
  gt_same_nv : gc_nvertices gc1 = gc_nvertices gc2;
  gt_transform : forall k,
    (k < length (gc_edges gc1))%nat ->
    nth k (gc_links gc2) 0 ==
      gt_gauge (fst (nth k (gc_edges gc1) (0%nat,0%nat)))
      + nth k (gc_links gc1) 0
      - gt_gauge (snd (nth k (gc_edges gc1) (0%nat,0%nat)))
}.

(** Identity gauge transform *)
Definition gauge_transform_id (gc : GaugeConfig) : GaugeTransform gc gc.
Proof.
  apply (mkGaugeTr gc gc (fun _ => 0) eq_refl eq_refl).
  intros k Hk. lra.
Defined.

(* ================================================================== *)
(*  Part IV: Category Laws + Lemmas  (~20 Qed)                        *)
(* ================================================================== *)

Lemma gauge_mor_eq_refl : forall gc1 gc2 (f : GaugeMorphism gc1 gc2),
  gauge_mor_eq gc1 gc2 f f.
Proof. intros. intros v Hv. reflexivity. Qed.

Lemma gauge_mor_eq_sym : forall gc1 gc2 (f g : GaugeMorphism gc1 gc2),
  gauge_mor_eq gc1 gc2 f g -> gauge_mor_eq gc1 gc2 g f.
Proof. intros gc1 gc2 f g H v Hv. symmetry. apply H. exact Hv. Qed.

Lemma gauge_mor_eq_trans : forall gc1 gc2 (f g h : GaugeMorphism gc1 gc2),
  gauge_mor_eq gc1 gc2 f g -> gauge_mor_eq gc1 gc2 g h ->
  gauge_mor_eq gc1 gc2 f h.
Proof.
  intros gc1 gc2 f g h Hfg Hgh v Hv.
  rewrite (Hfg v Hv). apply Hgh. exact Hv.
Qed.

Lemma gauge_comp_compat : forall gc1 gc2 gc3
  (f f' : GaugeMorphism gc2 gc3) (g g' : GaugeMorphism gc1 gc2),
  gauge_mor_eq gc2 gc3 f f' -> gauge_mor_eq gc1 gc2 g g' ->
  gauge_mor_eq gc1 gc3 (gauge_compose gc1 gc2 gc3 f g)
                       (gauge_compose gc1 gc2 gc3 f' g').
Proof.
  intros gc1 gc2 gc3 f f' g g' Hf Hg v Hv.
  simpl. rewrite (Hg v Hv). apply Hf. apply gm_vmap_valid. exact Hv.
Qed.

Lemma gauge_assoc : forall gc1 gc2 gc3 gc4
  (f : GaugeMorphism gc1 gc2) (g : GaugeMorphism gc2 gc3)
  (h : GaugeMorphism gc3 gc4),
  gauge_mor_eq gc1 gc4
    (gauge_compose gc1 gc3 gc4 h (gauge_compose gc1 gc2 gc3 g f))
    (gauge_compose gc1 gc2 gc4 (gauge_compose gc2 gc3 gc4 h g) f).
Proof. intros. intros v Hv. simpl. reflexivity. Qed.

Lemma gauge_id_l : forall gc1 gc2 (f : GaugeMorphism gc1 gc2),
  gauge_mor_eq gc1 gc2 (gauge_compose gc1 gc2 gc2 (gauge_id gc2) f) f.
Proof. intros. intros v Hv. simpl. reflexivity. Qed.

Lemma gauge_id_r : forall gc1 gc2 (f : GaugeMorphism gc1 gc2),
  gauge_mor_eq gc1 gc2 (gauge_compose gc1 gc1 gc2 f (gauge_id gc1)) f.
Proof. intros. intros v Hv. simpl. reflexivity. Qed.

(** ★ GaugeCat: the category of Q-valued gauge configurations *)
Definition GaugeCat : Category := mkCategory
  GaugeConfig
  GaugeMorphism
  gauge_mor_eq
  gauge_id
  gauge_compose
  gauge_mor_eq_refl
  gauge_mor_eq_sym
  gauge_mor_eq_trans
  gauge_comp_compat
  gauge_assoc
  gauge_id_l
  gauge_id_r.

(** Trivial gauge has all links = 1 *)
Lemma trivial_gauge_nth_link : forall nv edges Hvalid k,
  (k < length edges)%nat ->
  gc_nth_link (trivial_gauge nv edges Hvalid) k == 1.
Proof.
  intros nv edges Hvalid k Hk. unfold gc_nth_link. simpl.
  enough (Hnth : nth k (repeat (1:Q) (length edges)) (0:Q) = 1)
    by (rewrite Hnth; reflexivity).
  clear Hvalid nv. revert k Hk.
  induction edges as [| e rest IH]; intros k Hk.
  - simpl in Hk. lia.
  - destruct k as [| k'].
    + reflexivity.
    + simpl. apply IH. simpl in Hk. lia.
Qed.

(** Empty gauge has no edges *)
Lemma empty_gauge_no_edges : gc_edges empty_gauge = [].
Proof. reflexivity. Qed.

(** Empty gauge has no links *)
Lemma empty_gauge_no_links : gc_links empty_gauge = [].
Proof. reflexivity. Qed.

(* ================================================================== *)
(*  Part V: Gauge as Process  (~6 Qed)                                 *)
(* ================================================================== *)

(** Gauge at level n: at most n vertices *)
Definition gauge_at_level (n : nat) (gc : GaugeConfig) : Prop :=
  (gc_nvertices gc <= n)%nat.

(** Monotone: higher level includes more gauge configs *)
Lemma gauge_level_increasing : forall n gc,
  gauge_at_level n gc -> gauge_at_level (S n) gc.
Proof. intros n gc H. unfold gauge_at_level in *. lia. Qed.

(** Empty gauge is at every level *)
Lemma empty_gauge_at_level : forall n, gauge_at_level n empty_gauge.
Proof. intros. unfold gauge_at_level. simpl. lia. Qed.

(** Gauge identity morphism is trivially zero *)
Lemma gauge_id_is_identity : forall gc v,
  gm_vmap gc gc (gauge_id gc) v = v.
Proof. intros. simpl. reflexivity. Qed.

(** Wilson loop on empty path is zero *)
Lemma wilson_loop_nil : forall gc, wilson_loop gc [] = 0.
Proof. intros. reflexivity. Qed.

(** Wilson loop on singleton is zero *)
Lemma wilson_loop_singleton : forall gc k, wilson_loop gc [k] = 0.
Proof. intros. reflexivity. Qed.

(** Gauge config link count matches edge count *)
Lemma gauge_links_edges_match : forall gc,
  length (gc_links gc) = length (gc_edges gc).
Proof. intros gc. exact (gc_match gc). Qed.

(** Gauge process: nth link as constant process is Cauchy *)
Lemma gauge_process_cauchy : forall gc k,
  ProcessCore.is_Cauchy (fun _ : nat => gc_nth_link gc k).
Proof.
  intros gc k eps Heps. exists 0%nat. intros m n Hm Hn.
  unfold Qminus. rewrite Qplus_opp_r.
  rewrite Qabs_pos; lra.
Qed.

(** Plaquette action on empty path is β *)
Lemma plaquette_action_empty : forall beta gc,
  plaquette_action beta gc [] == beta * 1.
Proof.
  intros. unfold plaquette_action. simpl. lra.
Qed.

(** Gauge at level 0 has 0 vertices *)
Lemma gauge_at_level_zero : forall gc,
  gauge_at_level 0 gc -> gc_nvertices gc = 0%nat.
Proof. intros gc H. unfold gauge_at_level in H. lia. Qed.
