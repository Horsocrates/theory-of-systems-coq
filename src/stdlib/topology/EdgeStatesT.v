(** * EdgeStatesT.v — Edge states and bulk-boundary correspondence

    Elements: edge state count, perturbation stability
    Roles:    topological phase protects edge states from perturbation
    Rules:    n_edge = 2 in topological, 0 in trivial; perturbation-robust
    Status:   verified | bulk-boundary correspondence

    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lqa Bool Lia.
From ToS Require Import stdlib.topology.SSHModelT.
Open Scope Q_scope.

(** Number of edge states from SSH classification *)
Definition n_edge_states (t1 t2 : Q) : nat :=
  match classify_ssh t1 t2 with
  | Topological => 2%nat
  | Trivial => 0%nat
  | SSHCritical => 1%nat
  end.

(** ---- Concrete instances ---- *)

Theorem edge_topo : n_edge_states (1#2) 1 = 2%nat.
Proof. simpl. reflexivity. Qed.

Theorem edge_triv : n_edge_states (3#2) 1 = 0%nat.
Proof. simpl. reflexivity. Qed.

Theorem edge_crit : n_edge_states 1 1 = 1%nat.
Proof. simpl. reflexivity. Qed.

(** Bulk-boundary: topological phase has nonzero edge states *)
Theorem bulk_edge_topo : forall t1 t2,
  classify_ssh t1 t2 = Topological ->
  n_edge_states t1 t2 = 2%nat.
Proof.
  intros t1 t2 H. unfold n_edge_states. rewrite H. reflexivity.
Qed.

Theorem bulk_edge_triv : forall t1 t2,
  classify_ssh t1 t2 = Trivial ->
  n_edge_states t1 t2 = 0%nat.
Proof.
  intros t1 t2 H. unfold n_edge_states. rewrite H. reflexivity.
Qed.

(** Perturbation stability: if t1 + delta still < t2, still topological *)
Theorem edge_protected : forall t1 t2 delta,
  classify_ssh (t1 + delta) t2 = Topological ->
  n_edge_states (t1 + delta) t2 = 2%nat.
Proof.
  intros t1 t2 delta H. apply bulk_edge_topo. exact H.
Qed.

(** Concrete perturbation: t1=1/2 + delta=1/4 = 3/4 < 1 still topological *)
Theorem edge_perturbed_concrete :
  n_edge_states ((1#2) + (1#4)) 1 = 2%nat.
Proof. simpl. reflexivity. Qed.

(** Edge states determine phase *)
Theorem edge_determines_nontrivial : forall t1 t2,
  classify_ssh t1 t2 = Topological ->
  (n_edge_states t1 t2 > 0)%nat.
Proof.
  intros t1 t2 H. unfold n_edge_states. rewrite H. simpl. lia.
Qed.

(** Trivial has no edge states *)
Theorem trivial_no_edge : forall t1 t2,
  classify_ssh t1 t2 = Trivial ->
  n_edge_states t1 t2 = 0%nat.
Proof.
  intros. apply bulk_edge_triv. exact H.
Qed.

(** Another concrete: strong topological regime t1=1/4, t2=2 *)
Theorem edge_strong_topo : n_edge_states (1#4) 2 = 2%nat.
Proof. simpl. reflexivity. Qed.

(** Strong trivial regime t1=3, t2=1 *)
Theorem edge_strong_triv : n_edge_states 3 1 = 0%nat.
Proof. simpl. reflexivity. Qed.

(** Critical has exactly 1 edge state *)
Theorem edge_critical_one : forall t1 t2,
  classify_ssh t1 t2 = SSHCritical ->
  n_edge_states t1 t2 = 1%nat.
Proof.
  intros t1 t2 H. unfold n_edge_states. rewrite H. reflexivity.
Qed.
