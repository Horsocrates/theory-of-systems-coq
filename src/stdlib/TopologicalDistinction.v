(** * TopologicalDistinction.v — Topology as Distinction
    Elements: Topological vs trivial phases, boundary detection
    Roles:    Connect Chern classification to distinction structure
    Rules:    Phase change = new distinction; boundary at parity flip
    Status:   Stdlib
    STATUS: 7 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
From Stdlib Require Import Bool.
From ToS Require Import stdlib.ChernNumber.
Open Scope Q_scope.

(* ================================================================== *)
(*  TOPOLOGICAL DISTINCTION                                            *)
(*  Two phases are distinct iff their Chern parity differs             *)
(* ================================================================== *)

Definition phases_distinct (m1 m2 : Q) : bool :=
  negb (Bool.eqb (is_topological m1) (is_topological m2)).

(* m=1 (topological) vs m=5 (trivial): distinct *)
Lemma distinct_1_5 : phases_distinct 1 5 = true.
Proof. reflexivity. Qed.

(* m=1 vs m=3: both topological, not distinct *)
Lemma same_1_3 : phases_distinct 1 3 = false.
Proof. reflexivity. Qed.

(* m=-1 vs m=5: both trivial *)
Lemma same_n1_5 : phases_distinct (-(1)) 5 = false.
Proof. reflexivity. Qed.

(* ================================================================== *)
(*  BOUNDARY DETECTION                                                 *)
(*  Phase boundary exists between m values where parity changes        *)
(* ================================================================== *)

Definition has_boundary (m1 m2 : Q) : Prop :=
  is_topological m1 <> is_topological m2.

Lemma boundary_1_5 : has_boundary 1 5.
Proof.
  unfold has_boundary. simpl. discriminate.
Qed.

Lemma no_boundary_1_3 : ~ has_boundary 1 3.
Proof.
  unfold has_boundary. simpl. intro H. apply H. reflexivity.
Qed.

(* ================================================================== *)
(*  TOPOLOGICAL IS DISTINCTION                                         *)
(*  The phase classification IS a distinction structure:               *)
(*  Every mass value is classified, and the classification is binary   *)
(* ================================================================== *)

Lemma classification_complete :
  forall m, is_topological m = true \/ is_topological m = false.
Proof.
  intro m. destruct (is_topological m); [left|right]; reflexivity.
Qed.

Theorem topological_is_distinction :
  (* Two example phases are distinguishable *)
  phases_distinct 1 5 = true /\
  (* Same-phase pairs are not *)
  phases_distinct 1 3 = false /\
  (* Classification is complete *)
  (forall m, is_topological m = true \/ is_topological m = false).
Proof.
  split; [exact distinct_1_5|].
  split; [exact same_1_3|].
  exact classification_complete.
Qed.
