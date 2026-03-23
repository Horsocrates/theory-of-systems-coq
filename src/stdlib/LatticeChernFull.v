(** * LatticeChernFull.v — Full Chern Number from Lattice d-vector
    Elements: d_z component at BZ points, sign counting on 4x4 grid
    Roles:    Classify topological phases by negative-count on discretized BZ
    Rules:    Count sign flips → Chern number; phase diagram from mass parameter
    Status:   Stdlib — Six Directions Phase 2, Section E5
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
From Stdlib Require Import List Bool PeanoNat.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================== *)
(*  D-VECTOR Z-COMPONENT                                               *)
(*  d_z m kx_idx ky_idx : Q                                           *)
(*  cx = cos(kx): idx 0->1, 1->0, 2->(-1), 3->0                      *)
(*  cy = cos(ky): same mapping                                        *)
(* ================================================================== *)

Definition cos_bz (idx : nat) : Q :=
  match idx with
  | O => 1
  | S O => 0
  | S (S O) => -(1)
  | _ => 0
  end.

Definition d_z (m : Q) (kx_idx ky_idx : nat) : Q :=
  m + cos_bz kx_idx + cos_bz ky_idx.

(* ================================================================== *)
(*  CONCRETE d_z VALUES                                                *)
(* ================================================================== *)

Lemma d_z_m1_00 : d_z 1 O O == 3.
Proof. vm_compute. reflexivity. Qed.

Lemma d_z_m1_22 : d_z 1 (S (S O)) (S (S O)) == -(1).
Proof. vm_compute. reflexivity. Qed.

Lemma d_z_m3_00 : d_z 3 O O == 5.
Proof. vm_compute. reflexivity. Qed.

Lemma d_z_m3_22 : d_z 3 (S (S O)) (S (S O)) == 1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SIGN DETECTION (using Qnum, fully computable)                      *)
(* ================================================================== *)

Definition sign_negative (x : Q) : bool :=
  match Qnum x with
  | Zneg _ => true
  | _ => false
  end.

Lemma sign_neg_positive : sign_negative 3 = false.
Proof. reflexivity. Qed.

Lemma sign_neg_negative : sign_negative (-(1)) = true.
Proof. reflexivity. Qed.

Lemma sign_neg_zero : sign_negative 0 = false.
Proof. reflexivity. Qed.

(* ================================================================== *)
(*  COUNTING NEGATIVES ON 4x4 BZ GRID                                 *)
(* ================================================================== *)

Definition bz_points : list nat := 0%nat :: 1%nat :: 2%nat :: 3%nat :: nil.

Definition sign_count_negative_4x4 (m : Q) : nat :=
  fold_left (fun acc kx =>
    fold_left (fun acc2 ky =>
      if sign_negative (d_z m kx ky) then S acc2 else acc2)
      bz_points acc)
    bz_points 0%nat.

(* m=1: only (2,2) gives d_z = -1, so 1 negative *)
Lemma chern_m1 : sign_count_negative_4x4 1 = 1%nat.
Proof. vm_compute. reflexivity. Qed.

(* m=3: all d_z >= 1, no negatives *)
Lemma chern_m3 : sign_count_negative_4x4 3 = 0%nat.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  CHERN PARITY                                                       *)
(*  Odd count → topological, Even count → trivial                     *)
(* ================================================================== *)

Definition is_topological (m : Q) : bool :=
  Nat.odd (sign_count_negative_4x4 m).

Lemma topological_m1 : is_topological 1 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma trivial_m3 : is_topological 3 = false.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                           *)
(* ================================================================== *)

Theorem lattice_chern_full_synthesis :
  d_z 1 O O == 3 /\
  d_z 1 (S (S O)) (S (S O)) == -(1) /\
  d_z 3 O O == 5 /\
  d_z 3 (S (S O)) (S (S O)) == 1 /\
  sign_count_negative_4x4 1 = 1%nat /\
  sign_count_negative_4x4 3 = 0%nat.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.
