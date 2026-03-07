(** * Graph.v — Graph Data Structures as ToS System

    Theory of Systems — Verified Standard Library (Batch 3)

    Elements: nodes (nat), edges (nat * nat)
    Roles:    node -> Vertex, edge -> Connection, path -> Route
    Rules:    well-formedness (edges reference valid nodes)
    Status:   connected | disconnected | acyclic | cyclic

    Connection: L5Resolution.v (topological ordering = L5-compatible)
    Connection: ERR_WellFormed (acyclic deps = is_dag)

    STATUS: 22 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* ================================================================= *)
(** ** Core Graph Type                                                *)
(* ================================================================= *)

Record Graph := mkGraph {
  g_nodes : list nat;
  g_edges : list (nat * nat);
}.

Definition empty_graph : Graph := mkGraph [] [].

Definition add_node (v : nat) (g : Graph) : Graph :=
  mkGraph (v :: g_nodes g) (g_edges g).

Definition add_edge (u v : nat) (g : Graph) : Graph :=
  mkGraph (g_nodes g) ((u, v) :: g_edges g).

Definition has_node (v : nat) (g : Graph) : bool :=
  existsb (Nat.eqb v) (g_nodes g).

Definition has_edge (u v : nat) (g : Graph) : bool :=
  existsb (fun e => Nat.eqb (fst e) u && Nat.eqb (snd e) v) (g_edges g).

Definition neighbors (v : nat) (g : Graph) : list nat :=
  map snd (filter (fun e => Nat.eqb (fst e) v) (g_edges g)).

Definition out_degree (v : nat) (g : Graph) : nat :=
  length (neighbors v g).

Definition in_degree (v : nat) (g : Graph) : nat :=
  length (filter (fun e => Nat.eqb (snd e) v) (g_edges g)).

Definition num_nodes (g : Graph) : nat := length (g_nodes g).
Definition num_edges (g : Graph) : nat := length (g_edges g).

(* ================================================================= *)
(** ** Well-Formedness                                                *)
(* ================================================================= *)

(** Every edge endpoint must be a node in the graph. *)
Definition well_formed (g : Graph) : Prop :=
  forall u v, In (u, v) (g_edges g) ->
    In u (g_nodes g) /\ In v (g_nodes g).

(* ================================================================= *)
(** ** Reachability (fuel-bounded search)                             *)
(* ================================================================= *)

Fixpoint reachable_fuel (fuel : nat) (g : Graph) (visited : list nat)
         (current target : nat) : bool :=
  match fuel with
  | O => Nat.eqb current target
  | S f' =>
    if Nat.eqb current target then true
    else if existsb (Nat.eqb current) visited then false
    else existsb (fun next =>
           reachable_fuel f' g (current :: visited) next target)
         (neighbors current g)
  end.

Definition is_reachable (g : Graph) (u v : nat) : bool :=
  reachable_fuel (num_nodes g) g [] u v.

(* ================================================================= *)
(** ** Acyclicity                                                     *)
(* ================================================================= *)

(** A graph is acyclic if no node can reach itself through its edges. *)
Definition is_acyclic_bool (g : Graph) : bool :=
  forallb (fun v =>
    negb (existsb (fun next =>
      reachable_fuel (num_nodes g) g [v] next v)
      (neighbors v g)))
    (g_nodes g).

(* ================================================================= *)
(** ** Subgraph and Reverse                                           *)
(* ================================================================= *)

Definition remove_node (v : nat) (g : Graph) : Graph :=
  mkGraph (filter (fun n => negb (Nat.eqb n v)) (g_nodes g))
          (filter (fun e => negb (Nat.eqb (fst e) v) &&
                            negb (Nat.eqb (snd e) v)) (g_edges g)).

Definition reverse_graph (g : Graph) : Graph :=
  mkGraph (g_nodes g) (map (fun e => (snd e, fst e)) (g_edges g)).

(* ================================================================= *)
(** ** Theorems                                                       *)
(* ================================================================= *)

(** 1. Empty graph has no nodes *)
Lemma empty_no_nodes : g_nodes empty_graph = [].
Proof. reflexivity. Qed.

(** 2. Empty graph has no edges *)
Lemma empty_no_edges : g_edges empty_graph = [].
Proof. reflexivity. Qed.

(** 3. Number of nodes in empty graph is 0 *)
Lemma num_nodes_empty : num_nodes empty_graph = 0.
Proof. reflexivity. Qed.

(** 4. Number of edges in empty graph is 0 *)
Lemma num_edges_empty : num_edges empty_graph = 0.
Proof. reflexivity. Qed.

(** 5. Adding a node makes it findable *)
Lemma has_node_add : forall v g, has_node v (add_node v g) = true.
Proof.
  intros v g.
  unfold has_node, add_node. simpl.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

(** 6. Empty graph has no node *)
Lemma has_node_empty : forall v, has_node v empty_graph = false.
Proof. reflexivity. Qed.

(** 7. Adding an edge makes it findable *)
Lemma has_edge_add : forall u v g, has_edge u v (add_edge u v g) = true.
Proof.
  intros u v g.
  unfold has_edge, add_edge. simpl.
  rewrite !Nat.eqb_refl. reflexivity.
Qed.

(** 8. Empty graph has no edge *)
Lemma has_edge_empty : forall u v, has_edge u v empty_graph = false.
Proof. reflexivity. Qed.

(** 9. Neighbors of any node in empty graph is nil *)
Lemma neighbors_empty : forall v, neighbors v empty_graph = [].
Proof. reflexivity. Qed.

(** 10. Out-degree of any node in empty graph is 0 *)
Lemma out_degree_empty : forall v, out_degree v empty_graph = 0.
Proof. reflexivity. Qed.

(** 11. Adding a node preserves edges *)
Lemma add_node_preserves_edges : forall v g,
  g_edges (add_node v g) = g_edges g.
Proof. reflexivity. Qed.

(** 12. Adding an edge preserves nodes *)
Lemma add_edge_preserves_nodes : forall u v g,
  g_nodes (add_edge u v g) = g_nodes g.
Proof. reflexivity. Qed.

(** 13. Adding a node increments node count *)
Lemma num_nodes_add : forall v g,
  num_nodes (add_node v g) = S (num_nodes g).
Proof.
  intros v g. unfold num_nodes, add_node. simpl. reflexivity.
Qed.

(** 14. Adding an edge increments edge count *)
Lemma num_edges_add : forall u v g,
  num_edges (add_edge u v g) = S (num_edges g).
Proof.
  intros u v g. unfold num_edges, add_edge. simpl. reflexivity.
Qed.

(** 15. Empty graph is well-formed *)
Lemma well_formed_empty : well_formed empty_graph.
Proof.
  unfold well_formed. intros u v H. simpl in H. contradiction.
Qed.

(** 16. Adding a different node doesn't affect has_node for other nodes *)
Lemma has_node_add_other : forall v w g,
  v <> w -> has_node w (add_node v g) = has_node w g.
Proof.
  intros v w g Hne.
  unfold has_node, add_node. simpl.
  assert (Hwv: Nat.eqb w v = false).
  { apply Nat.eqb_neq. lia. }
  rewrite Hwv. reflexivity.
Qed.

(** 17. Adding an edge from a different source doesn't affect neighbors *)
Lemma neighbors_add_edge_other : forall u v w g,
  u <> w -> neighbors w (add_edge u v g) = neighbors w g.
Proof.
  intros u v w g Hne.
  unfold neighbors, add_edge. simpl.
  assert (Huw: Nat.eqb u w = false).
  { apply Nat.eqb_neq. auto. }
  rewrite Huw. simpl. reflexivity.
Qed.

(** 18. Adding an edge from u increases out-degree of u by 1 *)
Lemma out_degree_add_edge : forall u v g,
  out_degree u (add_edge u v g) = S (out_degree u g).
Proof.
  intros u v g.
  unfold out_degree, neighbors, add_edge. simpl.
  rewrite Nat.eqb_refl. simpl. reflexivity.
Qed.

(** 19. Every node is reachable from itself *)
Lemma is_reachable_self : forall g v,
  is_reachable g v v = true.
Proof.
  intros g v.
  unfold is_reachable, reachable_fuel.
  destruct (num_nodes g); simpl; rewrite Nat.eqb_refl; reflexivity.
Qed.

(** 20. Empty graph is acyclic *)
Lemma is_acyclic_empty : is_acyclic_bool empty_graph = true.
Proof. reflexivity. Qed.

(** 21. Concrete example: triangle graph has edge 0->1 *)
Definition graph_triangle : Graph :=
  add_edge 0 1 (add_edge 1 2 (add_edge 2 0
    (add_node 0 (add_node 1 (add_node 2 empty_graph))))).

Lemma triangle_has_edge_01 : has_edge 0 1 graph_triangle = true.
Proof. reflexivity. Qed.

(** 22. Concrete example: line graph reachability 0 -> 1 -> 2 *)
Definition graph_line : Graph :=
  add_edge 0 1 (add_edge 1 2
    (add_node 0 (add_node 1 (add_node 2 empty_graph)))).

Lemma line_reachable_0_2 : is_reachable graph_line 0 2 = true.
Proof. reflexivity. Qed.

(** 23. Reverse graph preserves nodes *)
Lemma reverse_preserves_nodes : forall g,
  g_nodes (reverse_graph g) = g_nodes g.
Proof. intros g. unfold reverse_graph. simpl. reflexivity. Qed.

(** 24. Reverse graph preserves edge count *)
Lemma reverse_preserves_num_edges : forall g,
  num_edges (reverse_graph g) = num_edges g.
Proof.
  intros g. unfold num_edges, reverse_graph. simpl.
  rewrite map_length. reflexivity.
Qed.

(** 25. Double-reverse of edges is identity *)
Lemma reverse_edge_involutive : forall e : nat * nat,
  let r := (snd e, fst e) in (snd r, fst r) = e.
Proof.
  intros [a b]. simpl. reflexivity.
Qed.

(** 26. Reverse graph is involutive *)
Lemma reverse_graph_involutive : forall g,
  reverse_graph (reverse_graph g) = g.
Proof.
  intros g. unfold reverse_graph. simpl.
  rewrite map_map. simpl.
  destruct g as [ns es]. simpl.
  f_equal.
  induction es as [| [a b] es' IH].
  - simpl. reflexivity.
  - simpl. f_equal. exact IH.
Qed.

(** 27. In-degree in empty graph is 0 *)
Lemma in_degree_empty : forall v, in_degree v empty_graph = 0.
Proof. reflexivity. Qed.

(** 28. remove_node removes the node *)
Lemma remove_node_has_node : forall v g,
  has_node v (remove_node v g) = false.
Proof.
  intros v g. unfold has_node, remove_node. simpl.
  induction (g_nodes g) as [| n ns IH].
  - simpl. reflexivity.
  - simpl. destruct (Nat.eqb n v) eqn:Env.
    + simpl. exact IH.
    + simpl.
      destruct (Nat.eqb v n) eqn:Evn.
      * apply Nat.eqb_eq in Evn. apply Nat.eqb_neq in Env. lia.
      * exact IH.
Qed.

(** 29. Well-formed graph with one node and no edges *)
Lemma well_formed_single_node : forall v,
  well_formed (add_node v empty_graph).
Proof.
  intros v. unfold well_formed. intros u w H.
  simpl in H. contradiction.
Qed.

(** 30. Neighbors of a node after adding an edge from it *)
Lemma neighbors_add_edge_same : forall u v g,
  neighbors u (add_edge u v g) = v :: neighbors u g.
Proof.
  intros u v g.
  unfold neighbors, add_edge. simpl.
  rewrite Nat.eqb_refl. simpl. reflexivity.
Qed.

(** Summary: 30 Qed, 0 Admitted, 0 axioms *)
