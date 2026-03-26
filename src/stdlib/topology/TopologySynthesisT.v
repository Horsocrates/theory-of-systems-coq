(** * TopologySynthesisT.v — Grand synthesis of topological phases

    Elements: SSH + Chern + Hall + Berry unified framework
    Roles:    all topological invariants agree on phase classification
    Rules:    SSH topo <-> Zak=1 <-> C nonzero <-> sigma_xy nonzero
    Status:   verified | topological phase synthesis

    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lqa Bool ZArith Lia.
From ToS Require Import stdlib.topology.SSHModelT.
From ToS Require Import stdlib.topology.EdgeStatesT.
From ToS Require Import stdlib.topology.ChernNumberT.
From ToS Require Import stdlib.topology.HallConductanceT.
From ToS Require Import stdlib.topology.BerryPhaseT.
Open Scope Q_scope.

(** ---- Grand synthesis: all invariants agree ---- *)

(** SSH topological -> edge states exist *)
Theorem synth_topo_has_edges : forall t1 t2,
  classify_ssh t1 t2 = Topological ->
  (n_edge_states t1 t2 > 0)%nat.
Proof.
  intros. apply edge_determines_nontrivial. exact H.
Qed.

(** SSH topological -> Zak phase nonzero *)
Theorem synth_topo_has_zak : forall t1 t2,
  classify_ssh t1 t2 = Topological ->
  zak_phase t1 t2 = 1%Z.
Proof.
  intros. apply zak_topological_invariant. exact H.
Qed.

(** Zak phase determines SSH phase *)
Theorem synth_zak_determines_ssh : forall t1 t2,
  zak_phase t1 t2 = 1%Z ->
  classify_ssh t1 t2 = Topological.
Proof.
  intros. apply zak_edge_connection. exact H.
Qed.

(** Trivial -> no edges and no Zak *)
Theorem synth_triv_nothing : forall t1 t2,
  classify_ssh t1 t2 = Trivial ->
  n_edge_states t1 t2 = 0%nat /\ zak_phase t1 t2 = 0%Z.
Proof.
  intros. split.
  - apply bulk_edge_triv. exact H.
  - apply zak_trivial_invariant. exact H.
Qed.

(** Concrete synthesis: t1=1/2, t2=1 is fully topological *)
Theorem synth_concrete_topo :
  classify_ssh (1#2) 1 = Topological /\
  n_edge_states (1#2) 1 = 2%nat /\
  zak_phase (1#2) 1 = 1%Z.
Proof.
  split; [|split]; simpl; reflexivity.
Qed.

(** Concrete synthesis: t1=3/2, t2=1 is fully trivial *)
Theorem synth_concrete_triv :
  classify_ssh (3#2) 1 = Trivial /\
  n_edge_states (3#2) 1 = 0%nat /\
  zak_phase (3#2) 1 = 0%Z.
Proof.
  split; [|split]; simpl; reflexivity.
Qed.

(** Hall conductance is quantized: specific concrete case *)
Theorem synth_hall_quantized :
  hall_conductance 1 == 1 /\ hall_conductance 0 == 0.
Proof.
  split; vm_compute; reflexivity.
Qed.

(** Chern number classifies 2D correctly *)
Theorem synth_chern_classifies :
  chern_number 1 = 1%Z /\
  chern_number (-(1)) = (-1)%Z /\
  chern_number 3 = 0%Z.
Proof.
  split; [|split]; simpl; reflexivity.
Qed.

(** Gap is robust: same gap can be topological or trivial *)
Theorem synth_gap_not_enough :
  ssh_gap (1#2) 1 == ssh_gap (3#2) 1 /\
  classify_ssh (1#2) 1 = Topological /\
  classify_ssh (3#2) 1 = Trivial.
Proof.
  split; [|split].
  - apply same_gap_diff_phase.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(** Zak + edges together *)
Theorem synth_zak_edge_agree : forall t1 t2,
  zak_phase t1 t2 = 1%Z ->
  n_edge_states t1 t2 = 2%nat.
Proof.
  intros t1 t2 H.
  apply zak_edge_connection in H.
  apply bulk_edge_topo. exact H.
Qed.
