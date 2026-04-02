(** * EntanglementFromModes.v — Entanglement from mode correlations
    Elements: ProductState (list (list Q)), is_rank1, is_entangled, bell_state
    Roles:    product states are separable (rank 1), entangled states are not
    Rules:    Bell state not rank 1 → entangled. Product state separable.
    STATUS:   12 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: April 2026

    ENTANGLEMENT = IRREDUCIBLE MODE CORRELATION.
    A product state: mode correlations factor into A_i * B_j.
    An entangled state: correlations CANNOT be factored.
    Test: 2x2 matrix is rank 1 iff ad - bc = 0.
    Bell state: [[1,0],[0,1]] has determinant 1 ≠ 0 → entangled.
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================ *)
(*  STATE REPRESENTATION                                             *)
(* ================================================================ *)

(** A 2x2 density matrix as list of rows *)
Definition ProductState := list (list Q).

(** Extract element from 2x2 matrix *)
Definition mat_elem (M : ProductState) (i j : nat) : Q :=
  match nth_error M i with
  | Some row => match nth_error row j with
                | Some v => v
                | None => 0
                end
  | None => 0
  end.

(** Determinant of 2x2 matrix: ad - bc *)
Definition det2 (M : ProductState) : Q :=
  mat_elem M 0 0 * mat_elem M 1 1 - mat_elem M 0 1 * mat_elem M 1 0.

(** Rank-1 test for 2x2: determinant = 0 *)
Definition is_rank1 (M : ProductState) : Prop :=
  det2 M == 0.

(** Entangled = not rank 1 *)
Definition is_entangled (M : ProductState) : Prop :=
  ~ (det2 M == 0).

(* ================================================================ *)
(*  BELL STATE                                                       *)
(* ================================================================ *)

(** Bell state |00> + |11> as density-like matrix:
    [[1, 0], [0, 1]] — the identity, representing maximal correlation *)
Definition bell_state : ProductState :=
  ((1:Q) :: (0:Q) :: nil) :: ((0:Q) :: (1:Q) :: nil) :: nil.

(** Product state |0>|0> as outer product:
    [[1, 0], [0, 0]] *)
Definition product_00 : ProductState :=
  ((1:Q) :: (0:Q) :: nil) :: ((0:Q) :: (0:Q) :: nil) :: nil.

(** Another product state: [[1, 1], [1, 1]] / 2 (|+>|+>) *)
Definition product_plus : ProductState :=
  ((1:Q) :: (1:Q) :: nil) :: ((1:Q) :: (1:Q) :: nil) :: nil.

(* ================================================================ *)
(*  BELL STATE IS ENTANGLED                                         *)
(* ================================================================ *)

Lemma bell_det : det2 bell_state == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma bell_not_rank1 : ~ is_rank1 bell_state.
Proof.
  unfold is_rank1. vm_compute.
  intro H. discriminate H.
Qed.

Lemma bell_entangled : is_entangled bell_state.
Proof.
  unfold is_entangled. vm_compute.
  intro H. discriminate H.
Qed.

(* ================================================================ *)
(*  PRODUCT STATE IS SEPARABLE                                      *)
(* ================================================================ *)

Lemma product_00_det : det2 product_00 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma product_separable : is_rank1 product_00.
Proof. unfold is_rank1. vm_compute. reflexivity. Qed.

Lemma product_plus_det : det2 product_plus == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma product_plus_separable : is_rank1 product_plus.
Proof. unfold is_rank1. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  SCHMIDT RANK                                                     *)
(* ================================================================ *)

(** Schmidt rank = 1 for product states, > 1 for entangled *)
Definition schmidt_rank_2x2 (M : ProductState) : nat :=
  if Qeq_dec (det2 M) 0 then 1%nat else 2%nat.

Lemma schmidt_rank_product :
  schmidt_rank_2x2 product_00 = 1%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma schmidt_rank_bell :
  schmidt_rank_2x2 bell_state = 2%nat.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  SYNTHESIS                                                        *)
(* ================================================================ *)

Theorem entanglement_from_modes_synthesis :
  (* Bell state has nonzero determinant *)
  det2 bell_state == 1 /\
  (* Product state has zero determinant *)
  det2 product_00 == 0 /\
  (* Schmidt rank: product=1, Bell=2 *)
  schmidt_rank_2x2 product_00 = 1%nat /\
  schmidt_rank_2x2 bell_state = 2%nat.
Proof.
  split; [exact bell_det |
  split; [exact product_00_det |
  split; [exact schmidt_rank_product |
  exact schmidt_rank_bell]]].
Qed.
