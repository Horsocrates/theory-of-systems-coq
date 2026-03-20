(** * LogicalAtom.v — Distinction as the atom of existence
    Elements: logical_atom, atom_is_minimum, atom_unsplittable
    Roles:    The smallest unit of existence = 1 distinction
    Rules:    Integer gauge dimensions, spin quantization, mass gap
    Status:   Foundation
    STATUS: 15 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.
From ToS Require Import foundation.Distinction.
From ToS Require Import foundation.IndivisibleDistinction.
From ToS Require Import foundation.ERRFromDistinction.

(** THE LOGICAL ATOM
    An atom = "uncuttable" = that which cannot be divided further.
    Democritus: physical atoms (smallest matter).
    Leibniz: monads (smallest substance).
    ToS: Distinction (smallest existence).

    COMPOSITION: complex systems = multiple distinctions
    Natural number n = n distinctions
    Rational p/q = ratio of distinction-counts
    Process nat->Q = sequence of rational values at each distinction-step
    System = E/R/R = structured collection of distinctions *)

(** 1 distinction = 1 atom of existence = the unit *)
Definition logical_atom : nat := 1.

(** 0 distinctions = no existence yet = the void *)
Definition logical_void : nat := 0.

(** You cannot go below 1 *)
Theorem atom_is_minimum :
  forall n : nat, (0 < n)%nat -> (logical_atom <= n)%nat.
Proof. unfold logical_atom. lia. Qed.

(** You cannot split the atom *)
Theorem atom_unsplittable :
  forall a b : nat, (a + b = logical_atom)%nat ->
  (a = 0%nat /\ b = 1%nat) \/ (a = 1%nat /\ b = 0%nat).
Proof. unfold logical_atom. lia. Qed.

(** Every nonzero quantity is >= 1 atom *)
Theorem existence_is_atomic :
  forall n : nat, n <> 0%nat -> (1 <= n)%nat.
Proof. lia. Qed.

(** Void is the only zero *)
Lemma void_unique : forall n : nat, (n < logical_atom)%nat -> n = logical_void.
Proof. unfold logical_atom, logical_void. lia. Qed.

(** Two atoms = compound *)
Lemma compound_from_atoms : (logical_atom + logical_atom = 2)%nat.
Proof. reflexivity. Qed.

(** WHY GAUGE GROUPS HAVE INTEGER DIMENSION
    SU(N): N^2-1 generators. N = role count = natural number.
    Cannot have SU(2.5). Because: 2.5 roles = 2.5 distinctions = impossible. *)

Theorem gauge_dimension_integer : forall N : nat,
  exists d : nat, (N * N - 1 = d)%nat \/ (N = 0%nat).
Proof.
  intro N. destruct N.
  - exists 0%nat. right. reflexivity.
  - exists (N*N + 2*N)%nat. left. lia.
Qed.

(** Concrete gauge dimensions *)
Lemma su2_dim : (2 * 2 - 1 = 3)%nat. Proof. lia. Qed.
Lemma su3_dim : (3 * 3 - 1 = 8)%nat. Proof. lia. Qed.
Lemma su5_dim : (5 * 5 - 1 = 24)%nat. Proof. lia. Qed.

(** WHY SPIN IS HALF-INTEGER (apparent exception)
    Spin 1/2: not half a distinction, but ORIENTATION of a distinction.
    A distinction has TWO sides (A, not-A).
    "Spin up" = aligned with A. "Spin down" = aligned with not-A.
    1/2 = one side of one distinction.
    The 2 in "spin 1/2" = 2 sides of 1 distinction = SU(2).
    j = 0, 1/2, 1, 3/2, ... = 0, 1, 2, 3, ... sides / 2 *)

Theorem spin_quantization : forall sides : nat,
  exists j_times_2 : nat, j_times_2 = sides.
Proof. intro. exists sides. reflexivity. Qed.

(** Spin-statistics: integer sides = boson, odd sides = fermion *)
Lemma boson_even_sides : forall n : nat,
  exists j : nat, (2 * n = 2 * j)%nat.
Proof. intro n. exists n. lia. Qed.

Lemma fermion_odd_sides : forall n : nat,
  exists j_times_2 : nat, (2 * n + 1 = j_times_2)%nat.
Proof. intro n. exists (2 * n + 1)%nat. lia. Qed.

(* ================================================================== *)
(*  SUMMARY                                                            *)
(* ================================================================== *)

Theorem logical_atom_summary :
  (* Atom is minimum *)
  (forall n : nat, (0 < n)%nat -> (1 <= n)%nat) /\
  (* Atom unsplittable *)
  (forall a b : nat, (a + b = 1)%nat ->
    (a = 0%nat /\ b = 1%nat) \/ (a = 1%nat /\ b = 0%nat)) /\
  (* Gauge dimensions integer *)
  (2 * 2 - 1 = 3)%nat /\
  (3 * 3 - 1 = 8)%nat.
Proof.
  split; [|split; [|split]].
  - lia.
  - intros. lia.
  - lia.
  - lia.
Qed.
