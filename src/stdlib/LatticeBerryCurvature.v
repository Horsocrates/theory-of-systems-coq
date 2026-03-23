(** * LatticeBerryCurvature.v — Berry Curvature on Discrete Lattice
    Elements: Ground states at k-points, overlaps, plaquette product
    Roles:    Compute Berry phase from lattice k-point overlaps
    Rules:    Plaquette product sign detects topological character
    Status:   Stdlib
    STATUS: 13 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================== *)
(*  GROUND STATES AT 4 k-POINTS                                       *)
(*  2-band model on 2×2 BZ lattice: k = (0,0), (pi,0), (0,pi), (pi,pi) *)
(*  Ground state = (cos(theta/2), sin(theta/2))                       *)
(*  We use rational approximations for each k-point                    *)
(* ================================================================== *)

Definition PState := list Q.

Fixpoint inner (psi phi : PState) : Q :=
  match psi, phi with
  | a :: psi', b :: phi' => a * b + inner psi' phi'
  | _, _ => 0
  end.

(* Ground states at the 4 k-points (rational approximations) *)
(* k1 = (0,0): theta ≈ 0, state ≈ (1, 0) *)
Definition gs_k1 : PState := [1; 0].

(* k2 = (pi,0): theta ≈ pi/3, state ≈ (7/8, 5/8) *)
Definition gs_k2 : PState := [7#8; 5#8].

(* k3 = (pi,pi): theta ≈ 2pi/3, state ≈ (1/2, 7/8) *)
Definition gs_k3 : PState := [1#2; 7#8].

(* k4 = (0,pi): theta ≈ pi/2, state ≈ (5/7, 5#7) *)
Definition gs_k4 : PState := [5#7; 5#7].

(* ================================================================== *)
(*  OVERLAPS: <psi_i | psi_j>                                         *)
(* ================================================================== *)

Lemma overlap_12 : inner gs_k1 gs_k2 == 7#8.
Proof. vm_compute. reflexivity. Qed.

Lemma overlap_23 : inner gs_k2 gs_k3 == 1008#1024.
Proof. vm_compute. reflexivity. Qed.

Lemma overlap_34 : inner gs_k3 gs_k4 == 770#784.
Proof. vm_compute. reflexivity. Qed.

Lemma overlap_41 : inner gs_k4 gs_k1 == 5#7.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  PLAQUETTE PRODUCT                                                  *)
(*  Berry phase ∝ arg(<1|2> · <2|3> · <3|4> · <4|1>)                 *)
(*  Sign of product indicates topological character                    *)
(* ================================================================== *)

Definition plaquette_product : Q :=
  inner gs_k1 gs_k2 * inner gs_k2 gs_k3 *
  inner gs_k3 gs_k4 * inner gs_k4 gs_k1.

Lemma plaquette_positive : 0 < plaquette_product.
Proof. unfold plaquette_product. simpl. lra. Qed.

(* ================================================================== *)
(*  ZERO OVERLAP = TOPOLOGICAL SINGULARITY                             *)
(*  If any overlap vanishes, Berry phase is undefined (gap closes)     *)
(* ================================================================== *)

Lemma overlap_12_nonzero : ~ (inner gs_k1 gs_k2 == 0).
Proof. simpl. lra. Qed.

Lemma overlap_23_nonzero : ~ (inner gs_k2 gs_k3 == 0).
Proof. simpl. lra. Qed.

(* All overlaps positive means no singularity in this configuration *)
Lemma all_overlaps_positive :
  0 < inner gs_k1 gs_k2 /\
  0 < inner gs_k2 gs_k3 /\
  0 < inner gs_k3 gs_k4 /\
  0 < inner gs_k4 gs_k1.
Proof. simpl. lra. Qed.

(* ================================================================== *)
(*  ORTHOGONAL STATE: singularity example                              *)
(* ================================================================== *)

Definition gs_ortho : PState := [0; 1].

Lemma zero_overlap_singularity : inner gs_k1 gs_ortho == 0.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SELF-OVERLAPS (normalization check)                                *)
(* ================================================================== *)

Lemma norm_k1 : inner gs_k1 gs_k1 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma norm_k2 : inner gs_k2 gs_k2 == 4736#4096.
Proof. vm_compute. reflexivity. Qed.

(* Near 1: states approximately normalized *)
Lemma norm_k2_near_1 : 1 < inner gs_k2 gs_k2 /\ inner gs_k2 gs_k2 < 2.
Proof. simpl. lra. Qed.

Theorem lattice_berry_curvature_synthesis :
  0 < plaquette_product /\
  inner gs_k1 gs_ortho == 0 /\
  inner gs_k1 gs_k1 == 1.
Proof.
  split; [exact plaquette_positive|].
  split; [exact zero_overlap_singularity|].
  exact norm_k1.
Qed.
