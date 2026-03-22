(** * GreenPathIntegral.v -- Path integral interpretation of Green's functions
    Elements: Path, path_weight, hadamard_like
    Roles:    G_{ij}(K) = sum over all K-step paths from i to j
    Rules:    Interference = path weight cancellation (destructive/constructive)
    Status:   Stdlib
    STATUS: 20 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.GreenFunction.

Import ListNotations.
Open Scope Q_scope.

(* ================================================================== *)
(*  PATH TYPE AND WEIGHT                                               *)
(* ================================================================== *)

(** A path is a sequence of sites visited *)
Definition Path := list nat.

(** Weight of a single edge *)
Definition edge_weight (M : Mat2) (i j : nat) : Q := M i j.

(** Weight of a path = product of edge weights *)
Fixpoint path_weight (M : Mat2) (p : Path) : Q :=
  match p with
  | [] => 1
  | [_] => 1
  | x :: ((y :: _) as rest) => M x y * path_weight M rest
  end.

(* ================================================================== *)
(*  CONCRETE PATH WEIGHTS FOR GOLDEN                                   *)
(* ================================================================== *)

(** K=1 paths from 0 to 0: just [0,0] with weight golden(0,0)=1 *)
Lemma golden_path_00 : path_weight golden [0%nat; 0%nat] == 1.
Proof. vm_compute. reflexivity. Qed.

(** K=1 path from 0 to 1: [0,1] with weight golden(0,1)=1 *)
Lemma golden_path_01 : path_weight golden [0%nat; 1%nat] == 1.
Proof. vm_compute. reflexivity. Qed.

(** K=2 paths from 0 to 0: [0,0,0] and [0,1,0] *)
Lemma golden_path_000 : path_weight golden [0%nat; 0%nat; 0%nat] == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma golden_path_010 : path_weight golden [0%nat; 1%nat; 0%nat] == 1.
Proof. vm_compute. reflexivity. Qed.

(** Sum of K=2 paths 0→0 = G(0,0,2) = 2 *)
Lemma golden_path_sum_K2 :
  path_weight golden [0%nat; 0%nat; 0%nat] +
  path_weight golden [0%nat; 1%nat; 0%nat] == green golden 0%nat 0%nat 2.
Proof. vm_compute. reflexivity. Qed.

(** K=2 path from 0 to 1: [0,0,1] and [0,1,1] *)
Lemma golden_path_001 : path_weight golden [0%nat; 0%nat; 1%nat] == 1.
Proof. vm_compute. reflexivity. Qed.

(** [0,1,1] has weight golden(0,1)*golden(1,1) = 1*0 = 0 *)
Lemma golden_path_011 : path_weight golden [0%nat; 1%nat; 1%nat] == 0.
Proof. vm_compute. reflexivity. Qed.

(** Sum of K=2 paths 0→1 = G(0,1,2) = 1 *)
Lemma golden_path_sum_01_K2 :
  path_weight golden [0%nat; 0%nat; 1%nat] +
  path_weight golden [0%nat; 1%nat; 1%nat] == green golden 0%nat 1%nat 2.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  HADAMARD-LIKE MATRIX: INTERFERENCE                                 *)
(* ================================================================== *)

Definition hadamard_like : Mat2 := fun i j =>
  match i, j with
  | O, O => 1   | O, S O => 1
  | S O, O => 1 | S O, S O => -(1)
  | _, _ => 0
  end.

(** Destructive interference: G(0,1,2) = 0 *)
Lemma hadamard_destructive :
  green hadamard_like 0%nat 1%nat 2 == 0.
Proof. vm_compute. reflexivity. Qed.

(** Constructive interference: G(0,0,2) = 2 *)
Lemma hadamard_constructive :
  green hadamard_like 0%nat 0%nat 2 == 2.
Proof. vm_compute. reflexivity. Qed.

(** Path explanation: [0,0,1] has weight 1, [0,1,1] has weight -1, sum=0 *)
Lemma hadamard_path_001 : path_weight hadamard_like [0%nat; 0%nat; 1%nat] == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma hadamard_path_011 : path_weight hadamard_like [0%nat; 1%nat; 1%nat] == -(1).
Proof. vm_compute. reflexivity. Qed.

Lemma hadamard_interference_paths :
  path_weight hadamard_like [0%nat; 0%nat; 1%nat] +
  path_weight hadamard_like [0%nat; 1%nat; 1%nat] == 0.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  K=3 PATHS FOR GOLDEN                                               *)
(* ================================================================== *)

(** Three-step paths 0→0: [0,0,0,0], [0,0,1,0], [0,1,0,0] *)
Lemma golden_path_0000 : path_weight golden [0%nat; 0%nat; 0%nat; 0%nat] == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma golden_path_0010 : path_weight golden [0%nat; 0%nat; 1%nat; 0%nat] == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma golden_path_0100 : path_weight golden [0%nat; 1%nat; 0%nat; 0%nat] == 1.
Proof. vm_compute. reflexivity. Qed.

(** Sum of K=3 paths 0→0 = G(0,0,3) = 3 *)
Lemma golden_path_sum_K3 :
  path_weight golden [0%nat; 0%nat; 0%nat; 0%nat] +
  path_weight golden [0%nat; 0%nat; 1%nat; 0%nat] +
  path_weight golden [0%nat; 1%nat; 0%nat; 0%nat] == green golden 0%nat 0%nat 3.
Proof. vm_compute. reflexivity. Qed.

(** Hadamard K=1 Green values *)
Lemma hadamard_green_00_1 : green hadamard_like 0%nat 0%nat 1 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma hadamard_green_11_1 : green hadamard_like 1%nat 1%nat 1 == -(1).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

Theorem path_integral_synthesis :
  (* Path sum = Green's function *)
  path_weight golden [0%nat; 0%nat; 0%nat] +
  path_weight golden [0%nat; 1%nat; 0%nat] == green golden 0%nat 0%nat 2 /\
  (* Destructive interference in Hadamard *)
  green hadamard_like 0%nat 1%nat 2 == 0 /\
  (* Constructive interference in Hadamard *)
  green hadamard_like 0%nat 0%nat 2 == 2 /\
  (* Path weights cancel *)
  path_weight hadamard_like [0%nat; 0%nat; 1%nat] +
  path_weight hadamard_like [0%nat; 1%nat; 1%nat] == 0.
Proof.
  split; [exact golden_path_sum_K2|].
  split; [exact hadamard_destructive|].
  split; [exact hadamard_constructive|exact hadamard_interference_paths].
Qed.
