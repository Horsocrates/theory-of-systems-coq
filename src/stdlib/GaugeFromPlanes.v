(** * GaugeFromPlanes.v -- Gauge Group Generators from Rotation Planes as ToS System
    Elements: su_generators, su_planes, su_off_diag, su_diagonal
    Roles:    SU(n) has n^2-1 generators = 2*C(n,2) off-diagonal + (n-1) diagonal
    Rules:    Generator counting from rotation plane decomposition
    Status:   Stdlib -- Six Directions Phase 2, Section D4
    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import Lia Arith.

(* ================================================================== *)
(*  GENERATOR COUNTING FOR SU(n)                                        *)
(*  SU(n): n^2-1 generators                                            *)
(*  Decompose: n(n-1)/2 rotation planes, each gives 2 generators       *)
(*             plus n-1 diagonal generators                             *)
(* ================================================================== *)

Definition su_generators (n : nat) : nat := n * n - 1.

Definition su_planes (n : nat) : nat := n * (n - 1) / 2.

Definition su_off_diag (n : nat) : nat := 2 * su_planes n.

Definition su_diagonal (n : nat) : nat := n - 1.

(* ================================================================== *)
(*  SU(2) CHECK: 3 generators                                          *)
(* ================================================================== *)

Lemma su2_generators : su_generators 2 = 3.
Proof. vm_compute. reflexivity. Qed.

Lemma su2_planes : su_planes 2 = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma su2_off_diag : su_off_diag 2 = 2.
Proof. vm_compute. reflexivity. Qed.

Lemma su2_diagonal : su_diagonal 2 = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma su2_decomposition : su_off_diag 2 + su_diagonal 2 = su_generators 2.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SU(3) CHECK: 8 generators (Gell-Mann matrices)                     *)
(* ================================================================== *)

Lemma su3_generators : su_generators 3 = 8.
Proof. vm_compute. reflexivity. Qed.

Lemma su3_planes : su_planes 3 = 3.
Proof. vm_compute. reflexivity. Qed.

Lemma su3_off_diag : su_off_diag 3 = 6.
Proof. vm_compute. reflexivity. Qed.

Lemma su3_diagonal : su_diagonal 3 = 2.
Proof. vm_compute. reflexivity. Qed.

Lemma su3_decomposition : su_off_diag 3 + su_diagonal 3 = su_generators 3.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SU(4) CHECK: 15 generators                                         *)
(* ================================================================== *)

Lemma su4_generators : su_generators 4 = 15.
Proof. vm_compute. reflexivity. Qed.

Lemma su4_decomposition : su_off_diag 4 + su_diagonal 4 = su_generators 4.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SU(5) CHECK: 24 generators (GUT group)                             *)
(* ================================================================== *)

Lemma su5_generators : su_generators 5 = 24.
Proof. vm_compute. reflexivity. Qed.

Lemma su5_decomposition : su_off_diag 5 + su_diagonal 5 = su_generators 5.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                           *)
(* ================================================================== *)

Theorem gauge_planes_synthesis :
  (su_generators 2 = 3) /\
  (su_generators 3 = 8) /\
  (su_generators 5 = 24) /\
  (su_off_diag 3 + su_diagonal 3 = su_generators 3).
Proof.
  split. { exact su2_generators. }
  split. { exact su3_generators. }
  split. { exact su5_generators. }
  exact su3_decomposition.
Qed.
