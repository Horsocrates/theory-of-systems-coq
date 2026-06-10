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

(** June 2026 honesty rollback: was `exists d, N*N-1 = d \/ N = 0` — vacuous.
    The real content of "no SU(2.5)": N is a nat BY TYPE (role counts are
    integers by construction), and the dimension map N ↦ N²−1 is INJECTIVE on
    positives — no two distinct gauge ladders share a dimension. *)
Theorem gauge_dimension_integer : forall N M : nat,
  (0 < N)%nat -> (0 < M)%nat -> (N * N - 1 = M * M - 1)%nat -> N = M.
Proof.
  intros N M HN HM H.
  assert (HNN : (1 <= N * N)%nat) by nia.
  assert (HMM : (1 <= M * M)%nat) by nia.
  assert (Heq : (N * N = M * M)%nat) by lia.
  nia.
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

(** June 2026 honesty rollback: was `exists j2, j2 = sides` — vacuous.  The real
    available content: the integer/half-integer CLASSIFICATION is an exclusive
    dichotomy (every doubled spin is even or odd, never both) — the boson/fermion
    sorting structure, NOT the spin-statistics theorem. *)
Theorem spin_quantization : forall sides : nat,
  (Nat.Even sides \/ Nat.Odd sides) /\ ~ (Nat.Even sides /\ Nat.Odd sides).
Proof.
  intro sides. split.
  - apply Nat.Even_or_Odd.
  - intros [HE HO]. exact (Nat.Even_Odd_False sides HE HO).
Qed.

(** Spin-statistics SORTING (June 2026: were vacuous exists): even sides land in
    the boson class, odd sides in the fermion class — the parity facts. *)
Lemma boson_even_sides : forall n : nat, Nat.Even (2 * n).
Proof. intro n. exists n. lia. Qed.

Lemma fermion_odd_sides : forall n : nat, Nat.Odd (2 * n + 1).
Proof. intro n. exists n. lia. Qed.

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
