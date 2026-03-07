(** * GraphAlgorithms.v — Graph Algorithms as ToS System

    Theory of Systems — Verified Standard Library (Batch 3)

    Elements: graphs, traversal orderings
    Roles:    bfs -> BreadthFirst, dfs -> DepthFirst, topo -> LinearOrder
    Rules:    fuel-bounded traversal (constitution: visit each node at most once)
    Status:   visited | unvisited | ordered

    Connection: Graph.v (graph data structure)

    STATUS: 20 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.

From ToS Require Import stdlib.Graph.

(* ================================================================= *)
(** ** Helper: find_index                                             *)
(* ================================================================= *)

Fixpoint find_index {A : Type} (f : A -> bool) (l : list A) : option nat :=
  match l with
  | [] => None
  | x :: rest => if f x then Some O else option_map S (find_index f rest)
  end.

(* ================================================================= *)
(** ** BFS (Breadth-First Search, fuel-bounded)                       *)
(* ================================================================= *)

Fixpoint bfs_fuel (fuel : nat) (g : Graph) (queue visited : list nat) : list nat :=
  match fuel with
  | O => visited
  | S f' =>
    match queue with
    | [] => visited
    | v :: rest =>
      if existsb (Nat.eqb v) visited then
        bfs_fuel f' g rest visited
      else
        bfs_fuel f' g (rest ++ neighbors v g) (visited ++ [v])
    end
  end.

Definition bfs (g : Graph) (start : nat) : list nat :=
  bfs_fuel (num_nodes g * num_nodes g + num_nodes g) g [start] [].

(* ================================================================= *)
(** ** DFS (Depth-First Search, fuel-bounded)                         *)
(* ================================================================= *)

Fixpoint dfs_fuel (fuel : nat) (g : Graph) (stack visited : list nat) : list nat :=
  match fuel with
  | O => visited
  | S f' =>
    match stack with
    | [] => visited
    | v :: rest =>
      if existsb (Nat.eqb v) visited then
        dfs_fuel f' g rest visited
      else
        dfs_fuel f' g (neighbors v g ++ rest) (visited ++ [v])
    end
  end.

Definition dfs (g : Graph) (start : nat) : list nat :=
  dfs_fuel (num_nodes g * num_nodes g + num_nodes g) g [start] [].

(* ================================================================= *)
(** ** Topological Ordering Check                                     *)
(* ================================================================= *)

Definition is_topo_order (g : Graph) (order : list nat) : bool :=
  forallb (fun e =>
    let src_pos := find_index (Nat.eqb (fst e)) order in
    let dst_pos := find_index (Nat.eqb (snd e)) order in
    match src_pos, dst_pos with
    | Some i, Some j => i <? j
    | _, _ => false
    end) (g_edges g).

(* ================================================================= *)
(** ** Concrete Test Graphs                                           *)
(* ================================================================= *)

(** Simple DAG: 0 -> 1 -> 2 (same as graph_line from Graph.v) *)
Definition graph_dag_simple : Graph :=
  add_edge 0 1 (add_edge 1 2
    (add_node 0 (add_node 1 (add_node 2 empty_graph)))).

(** Single-node graph *)
Definition graph_single : Graph := add_node 0 empty_graph.

(** Diamond DAG: 0 -> 1, 0 -> 2, 1 -> 3, 2 -> 3 *)
Definition graph_diamond : Graph :=
  add_edge 0 1 (add_edge 0 2 (add_edge 1 3 (add_edge 2 3
    (add_node 0 (add_node 1 (add_node 2 (add_node 3 empty_graph))))))).

(* ================================================================= *)
(** ** Theorems                                                       *)
(* ================================================================= *)

(** 1. BFS with zero fuel returns visited unchanged *)
Lemma bfs_fuel_0 : forall g q v, bfs_fuel O g q v = v.
Proof. intros g q v. simpl. reflexivity. Qed.

(** 2. DFS with zero fuel returns visited unchanged *)
Lemma dfs_fuel_0 : forall g s v, dfs_fuel O g s v = v.
Proof. intros g s v. simpl. reflexivity. Qed.

(** 3. BFS with empty queue returns visited unchanged *)
Lemma bfs_empty_queue : forall f g v, bfs_fuel (S f) g [] v = v.
Proof. intros f g v. simpl. reflexivity. Qed.

(** 4. DFS with empty stack returns visited unchanged *)
Lemma dfs_empty_stack : forall f g v, dfs_fuel (S f) g [] v = v.
Proof. intros f g v. simpl. reflexivity. Qed.

(** 5. BFS on line graph from 0 visits [0;1;2] *)
Lemma bfs_line_from_0 : bfs graph_line 0 = [0; 1; 2].
Proof. reflexivity. Qed.

(** 6. BFS on line graph from 1 visits [1;2] (only forward edges) *)
Lemma bfs_line_from_1 : bfs graph_line 1 = [1; 2].
Proof. reflexivity. Qed.

(** 7. DFS on line graph from 0 visits [0;1;2] *)
Lemma dfs_line_from_0 : dfs graph_line 0 = [0; 1; 2].
Proof. reflexivity. Qed.

(** 8. DFS on line graph from 1 visits [1;2] *)
Lemma dfs_line_from_1 : dfs graph_line 1 = [1; 2].
Proof. reflexivity. Qed.

(** 9. BFS on empty graph yields [] — zero fuel means no processing *)
Lemma bfs_empty_graph : bfs empty_graph 0 = [].
Proof. reflexivity. Qed.

(** 10. DFS on empty graph yields [] — zero fuel means no processing *)
Lemma dfs_empty_graph : dfs empty_graph 0 = [].
Proof. reflexivity. Qed.

(** 11. BFS on triangle graph from 0 *)
Lemma bfs_triangle_from_0 : bfs graph_triangle 0 = [0; 1; 2].
Proof. reflexivity. Qed.

(** 12. DFS on triangle graph from 0 *)
Lemma dfs_triangle_from_0 : dfs graph_triangle 0 = [0; 1; 2].
Proof. reflexivity. Qed.

(** 13. Topological order check on empty graph with empty order is true *)
Lemma topo_order_empty : is_topo_order empty_graph [] = true.
Proof. reflexivity. Qed.

(** 14. Topological order check on empty graph with any order is true *)
Lemma topo_order_empty_any : forall order, is_topo_order empty_graph order = true.
Proof. intros order. reflexivity. Qed.

(** 15. Valid topological order for simple DAG: [0;1;2] *)
Lemma topo_order_dag_simple :
  is_topo_order graph_dag_simple [0; 1; 2] = true.
Proof. reflexivity. Qed.

(** 16. find_index on nil is None *)
Lemma find_index_nil : forall {A : Type} (f : A -> bool),
  find_index f [] = None.
Proof. intros A f. simpl. reflexivity. Qed.

(** 17. find_index finds the head when predicate matches *)
Lemma find_index_head : forall {A : Type} (f : A -> bool) (x : A) (l : list A),
  f x = true -> find_index f (x :: l) = Some O.
Proof. intros A f x l Hfx. simpl. rewrite Hfx. reflexivity. Qed.

(** 18. BFS on single-node graph *)
Lemma bfs_single_node : bfs graph_single 0 = [0].
Proof. reflexivity. Qed.

(** 19. DFS on single-node graph *)
Lemma dfs_single_node : dfs graph_single 0 = [0].
Proof. reflexivity. Qed.

(** 20. Diamond DAG has valid topological order [0;1;2;3] *)
Lemma topo_order_diamond :
  is_topo_order graph_diamond [0; 1; 2; 3] = true.
Proof. reflexivity. Qed.

(** Summary: 20 Qed, 0 Admitted, 0 axioms *)
