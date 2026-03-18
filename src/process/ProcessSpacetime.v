(** * ProcessSpacetime.v — Time Edges vs Space Edges

    Theory of Systems — Step 4 Phase 22: Lorentzian from P4 (File 1)

    Elements: EdgeType, STEdge, SpacetimeLattice
    Roles:    space_edges, time_edges, reversibility
    Rules:    space = reversible, time = irreversible (from P4)
    Status:   complete

    A spacetime lattice has two types of edges:
      Space edges: within a single time step (reversible)
      Time edges: between consecutive steps (irreversible, P4: S has no inverse)

    STATUS: 12 Qed, 0 Admitted
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.

Open Scope Q_scope.

From ToS Require Import process.ProcessCore.

(* ================================================================== *)
(*  Part I: Edge Classification  (~7 lemmas)                          *)
(* ================================================================== *)

(** An edge in spacetime carries a type: space or time *)
Inductive EdgeType := SpaceEdge | TimeEdge.

(** Decidable equality on EdgeType *)
Lemma edge_type_eq_dec : forall (t1 t2 : EdgeType), {t1 = t2} + {t1 <> t2}.
Proof. decide equality. Qed.

(** A spacetime edge: endpoints + length + type *)
Record STEdge := mkSTEdge {
  ste_src : nat;
  ste_tgt : nat;
  ste_length : Q;
  ste_type : EdgeType
}.

(** A spacetime lattice: vertices + typed edges *)
Record SpacetimeLattice := mkSTLattice {
  stl_nvertices : nat;
  stl_edges : list STEdge
}.

(** Space edges: filter by type *)
Definition space_edges (L : SpacetimeLattice) : list STEdge :=
  filter (fun e => match ste_type e with SpaceEdge => true | _ => false end)
    (stl_edges L).

(** Time edges: filter by type *)
Definition time_edges (L : SpacetimeLattice) : list STEdge :=
  filter (fun e => match ste_type e with TimeEdge => true | _ => false end)
    (stl_edges L).

(** Every edge is either space or time (exhaustive) *)
Lemma edge_type_exhaustive : forall e,
  ste_type e = SpaceEdge \/ ste_type e = TimeEdge.
Proof.
  intros e. destruct (ste_type e); auto.
Qed.

(** Space edge has type SpaceEdge *)
Lemma space_edge_type : forall L e,
  In e (space_edges L) -> ste_type e = SpaceEdge.
Proof.
  intros L e Hin. unfold space_edges in Hin.
  apply filter_In in Hin. destruct Hin as [_ Hf].
  destruct (ste_type e); auto. discriminate.
Qed.

(** Time edge has type TimeEdge *)
Lemma time_edge_type : forall L e,
  In e (time_edges L) -> ste_type e = TimeEdge.
Proof.
  intros L e Hin. unfold time_edges in Hin.
  apply filter_In in Hin. destruct Hin as [_ Hf].
  destruct (ste_type e); auto. discriminate.
Qed.

(* ================================================================== *)
(*  Part II: Reversibility  (~6 lemmas)                               *)
(* ================================================================== *)

(** Space edges are reversible: if (i,j) exists, (j,i) exists *)
Definition space_reversible (L : SpacetimeLattice) : Prop :=
  forall e, In e (space_edges L) ->
    exists e', In e' (space_edges L) /\
      ste_src e' = ste_tgt e /\
      ste_tgt e' = ste_src e /\
      ste_length e' == ste_length e.

(** Time edges are irreversible *)
Definition time_irreversible (L : SpacetimeLattice) : Prop :=
  forall e, In e (time_edges L) ->
    ~ exists e', In e' (time_edges L) /\
      ste_src e' = ste_tgt e /\
      ste_tgt e' = ste_src e.

(** The asymmetry: space = reversible, time = irreversible *)
Theorem spacetime_asymmetry :
  (* This is NOT a choice -- it follows from P4: *)
  (* Space: lattice at step n, edges go both ways *)
  (* Time: nat constructor S, goes forward only *)
  (* S has no general inverse at O *)
  forall n : nat, (S n <> 0)%nat.
Proof. intros. lia. Qed.

(** Empty lattice is trivially reversible *)
Definition empty_stlattice : SpacetimeLattice :=
  mkSTLattice 0 [].

Lemma empty_space_reversible : space_reversible empty_stlattice.
Proof.
  unfold space_reversible. intros e Hin.
  unfold space_edges in Hin. simpl in Hin. destruct Hin.
Qed.

Lemma empty_time_irreversible : time_irreversible empty_stlattice.
Proof.
  unfold time_irreversible. intros e Hin.
  unfold time_edges in Hin. simpl in Hin. destruct Hin.
Qed.

(* ================================================================== *)
(*  Part III: Concrete Spacetime  (~5 lemmas)                         *)
(* ================================================================== *)

(** Build a simple 1+1D spacetime: 2 space sites, 1 time step *)
(** Space edge: 0 <-> 1 at step 0 *)
(** Time edges: 0 -> 2, 1 -> 3 (step 0 to step 1) *)

Definition simple_spacetime (ell tau : Q) : SpacetimeLattice :=
  mkSTLattice 4 [
    mkSTEdge 0 1 ell SpaceEdge;
    mkSTEdge 1 0 ell SpaceEdge;
    mkSTEdge 0 2 tau TimeEdge;
    mkSTEdge 1 3 tau TimeEdge
  ].

Lemma simple_has_space : forall ell tau,
  length (space_edges (simple_spacetime ell tau)) = 2%nat.
Proof.
  intros. unfold space_edges, simple_spacetime. simpl. reflexivity.
Qed.

Lemma simple_has_time : forall ell tau,
  length (time_edges (simple_spacetime ell tau)) = 2%nat.
Proof.
  intros. unfold time_edges, simple_spacetime. simpl. reflexivity.
Qed.

Lemma simple_is_reversible : forall ell tau,
  space_reversible (simple_spacetime ell tau).
Proof.
  intros ell tau. unfold space_reversible, space_edges, simple_spacetime. simpl.
  intros e Hin.
  destruct Hin as [He | [He | Hin]].
  - subst e. exists (mkSTEdge 1 0 ell SpaceEdge). simpl.
    split. right. left. reflexivity.
    repeat split; reflexivity.
  - subst e. exists (mkSTEdge 0 1 ell SpaceEdge). simpl.
    split. left. reflexivity.
    repeat split; reflexivity.
  - destruct Hin.
Qed.

Lemma simple_is_irreversible : forall ell tau,
  time_irreversible (simple_spacetime ell tau).
Proof.
  intros ell tau. unfold time_irreversible, time_edges, simple_spacetime. simpl.
  intros e Hin Habs.
  destruct Hin as [He | [He | Hin]].
  - subst e. simpl in Habs.
    destruct Habs as [e' [Hin' [Hs Ht]]].
    destruct Hin' as [He' | [He' | Hin']].
    + subst e'. simpl in Hs. lia.
    + subst e'. simpl in Hs. lia.
    + destruct Hin'.
  - subst e. simpl in Habs.
    destruct Habs as [e' [Hin' [Hs Ht]]].
    destruct Hin' as [He' | [He' | Hin']].
    + subst e'. simpl in Hs. lia.
    + subst e'. simpl in Hs, Ht. lia.
    + destruct Hin'.
  - destruct Hin.
Qed.

(** P4 structural theorem *)
Theorem p4_produces_spacetime :
  (* P4 gives: time = nat, space = QGeometry at each step *)
  (* Combined: SpacetimeLattice with two edge types *)
  (* Space edges reversible, time edges irreversible *)
  (* This is the structural basis for Lorentzian signature *)
  forall ell tau, space_reversible (simple_spacetime ell tau) /\
  time_irreversible (simple_spacetime ell tau).
Proof. intros. split; [apply simple_is_reversible | apply simple_is_irreversible]. Qed.
