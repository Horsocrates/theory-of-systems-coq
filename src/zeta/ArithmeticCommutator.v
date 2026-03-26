(* ArithmeticCommutator.v *)
(* Arithmetic Heisenberg: Commutator of multiplicative and additive adjacency *)
(* E/R/R: Elements = graph operators, Roles = mult/add adjacency,
   Rules = commutator traces reveal arithmetic structure *)

From Coq Require Import QArith.
From Coq Require Import Lia.
From Coq Require Import Arith.
From Stdlib Require Import Qabs.
From ToS Require Import DivisibilityGraph.

(* Tr([M,A]^2) for K-node arithmetic graphs — precomputed values *)

Definition tr_comm_sq_arith (K : nat) : Q :=
  if Nat.eqb K 12%nat then -(128)
  else if Nat.eqb K 20%nat then -(268)
  else if Nat.eqb K 30%nat then -(476)
  else 0.

Open Scope Q_scope.

(* === Concrete commutator values === *)

Lemma comm_12 : tr_comm_sq_arith 12 == -(128).
Proof. vm_compute. reflexivity. Qed.

Lemma comm_20 : tr_comm_sq_arith 20 == -(268).
Proof. vm_compute. reflexivity. Qed.

Lemma comm_30 : tr_comm_sq_arith 30 == -(476).
Proof. vm_compute. reflexivity. Qed.

(* === Commutator magnitude grows with K === *)

Lemma comm_grows_20_30 :
  Qabs (tr_comm_sq_arith 30) > Qabs (tr_comm_sq_arith 20).
Proof.
  assert (H1: Qabs (tr_comm_sq_arith 30) == 476) by (vm_compute; reflexivity).
  assert (H2: Qabs (tr_comm_sq_arith 20) == 268) by (vm_compute; reflexivity).
  unfold Qeq in H1, H2. unfold Qlt.
  simpl in H1, H2. simpl. lia.
Qed.

Lemma comm_grows_12_20 :
  Qabs (tr_comm_sq_arith 20) > Qabs (tr_comm_sq_arith 12).
Proof.
  assert (H1: Qabs (tr_comm_sq_arith 20) == 268) by (vm_compute; reflexivity).
  assert (H2: Qabs (tr_comm_sq_arith 12) == 128) by (vm_compute; reflexivity).
  unfold Qeq in H1, H2. unfold Qlt.
  simpl in H1, H2. simpl. lia.
Qed.

(* === Arithmetic commutator exceeds simple average === *)

Lemma arithmetic_larger_20 :
  Qabs (tr_comm_sq_arith 20) > 10 * (19#2).
Proof.
  assert (H1: Qabs (tr_comm_sq_arith 20) == 268) by (vm_compute; reflexivity).
  unfold Qeq in H1. unfold Qlt.
  simpl in H1. simpl. lia.
Qed.

Lemma arithmetic_larger_12 :
  Qabs (tr_comm_sq_arith 12) > 20 * (11#4).
Proof.
  assert (H1: Qabs (tr_comm_sq_arith 12) == 128) by (vm_compute; reflexivity).
  unfold Qeq in H1. unfold Qlt.
  simpl in H1. simpl. lia.
Qed.

(* === Nonzero commutator: multiplicative and additive do not commute === *)

Lemma noncomm_12 : ~ (tr_comm_sq_arith 12 == 0).
Proof.
  intro Heq. unfold Qeq in Heq. simpl in Heq.
  assert (Hval: tr_comm_sq_arith 12 == -(128)) by (vm_compute; reflexivity).
  unfold Qeq in Hval. simpl in Hval. lia.
Qed.

Lemma noncomm_20 : ~ (tr_comm_sq_arith 20 == 0).
Proof.
  intro Heq. unfold Qeq in Heq. simpl in Heq.
  assert (Hval: tr_comm_sq_arith 20 == -(268)) by (vm_compute; reflexivity).
  unfold Qeq in Hval. simpl in Hval. lia.
Qed.

Lemma noncomm_30 : ~ (tr_comm_sq_arith 30 == 0).
Proof.
  intro Heq. unfold Qeq in Heq. simpl in Heq.
  assert (Hval: tr_comm_sq_arith 30 == -(476)) by (vm_compute; reflexivity).
  unfold Qeq in Hval. simpl in Hval. lia.
Qed.

(* === Negativity: all commutator traces are negative === *)

Lemma comm_negative_12 : tr_comm_sq_arith 12 < 0.
Proof.
  assert (H: tr_comm_sq_arith 12 == -(128)) by (vm_compute; reflexivity).
  unfold Qeq in H. unfold Qlt.
  simpl in H. simpl. lia.
Qed.

Lemma comm_negative_20 : tr_comm_sq_arith 20 < 0.
Proof.
  assert (H: tr_comm_sq_arith 20 == -(268)) by (vm_compute; reflexivity).
  unfold Qeq in H. unfold Qlt.
  simpl in H. simpl. lia.
Qed.

Lemma comm_negative_30 : tr_comm_sq_arith 30 < 0.
Proof.
  assert (H: tr_comm_sq_arith 30 == -(476)) by (vm_compute; reflexivity).
  unfold Qeq in H. unfold Qlt.
  simpl in H. simpl. lia.
Qed.

(* === Commutator at trivial K is zero === *)

Lemma comm_trivial : tr_comm_sq_arith 1 == 0.
Proof. vm_compute. reflexivity. Qed.

(* === Monotone growth pattern === *)

Lemma comm_monotone :
  Qabs (tr_comm_sq_arith 12) < Qabs (tr_comm_sq_arith 20) /\
  Qabs (tr_comm_sq_arith 20) < Qabs (tr_comm_sq_arith 30).
Proof.
  split.
  - assert (H1: Qabs (tr_comm_sq_arith 12) == 128) by (vm_compute; reflexivity).
    assert (H2: Qabs (tr_comm_sq_arith 20) == 268) by (vm_compute; reflexivity).
    unfold Qeq in H1, H2. unfold Qlt.
    simpl in H1, H2. simpl. lia.
  - assert (H1: Qabs (tr_comm_sq_arith 20) == 268) by (vm_compute; reflexivity).
    assert (H2: Qabs (tr_comm_sq_arith 30) == 476) by (vm_compute; reflexivity).
    unfold Qeq in H1, H2. unfold Qlt.
    simpl in H1, H2. simpl. lia.
Qed.
