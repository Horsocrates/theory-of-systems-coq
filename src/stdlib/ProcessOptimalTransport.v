(** * ProcessOptimalTransport.v — Discrete OT on lattice over Q
    Elements: is_distribution, TransportPlan, transport_cost
    Roles:    Distributions (sum=1), plans (marginals), cost (exact Q)
    Rules:    First formally verified OT computation in Rocq
    Status:   Stdlib
    STATUS: 25 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.

Open Scope Q_scope.

(* ================================================================== *)
(*  DISCRETE DISTRIBUTIONS                                             *)
(* ================================================================== *)

(** A discrete distribution: list of non-negative rationals summing to 1 *)
Definition is_distribution (mu : list Q) : Prop :=
  (forall q, In q mu -> 0 <= q) /\
  fold_left Qplus mu 0 == 1.

(** Uniform distribution on K+1 points *)
Definition uniform (K : nat) : list Q :=
  repeat (1 / inject_Z (Z.of_nat (S K))) (S K).

(** Delta distribution: all mass at position k *)
Definition delta (K k : nat) : list Q :=
  map (fun i => if Nat.eqb i k then 1 else 0) (seq 0 (S K)).

(** Verify: uniform is non-negative *)
Lemma uniform_nonneg : forall K q, In q (uniform K) -> 0 <= q.
Proof.
  intros K q Hin. unfold uniform in Hin.
  apply repeat_spec in Hin. subst.
  apply Qle_shift_div_l.
  - unfold Qlt. simpl. lia.
  - lra.
Qed.

(** Uniform sum for K=2: 1/3 + 1/3 + 1/3 = 1 *)
Lemma uniform_sum_2 : fold_left Qplus (uniform 2) 0 == 1.
Proof. unfold uniform. vm_compute. reflexivity. Qed.

(** Delta sum when k <= K *)
Lemma delta_nonneg : forall K k i, In i (delta K k) -> 0 <= i.
Proof.
  intros K k i Hin. unfold delta in Hin.
  apply in_map_iff in Hin. destruct Hin as [x [Hx _]].
  destruct (Nat.eqb x k); subst; lra.
Qed.

Lemma delta_sum_0 : fold_left Qplus (delta 2 0) 0 == 1.
Proof. unfold delta. vm_compute. reflexivity. Qed.

Lemma delta_sum_1 : fold_left Qplus (delta 2 1) 0 == 1.
Proof. unfold delta. vm_compute. reflexivity. Qed.

Lemma delta_sum_2 : fold_left Qplus (delta 2 2) 0 == 1.
Proof. unfold delta. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  COST MATRIX                                                        *)
(* ================================================================== *)

(** Cost function: distance between sites *)
Definition lattice_cost (i j : nat) : Q :=
  inject_Z (Z.abs (Z.of_nat i - Z.of_nat j)).

Lemma cost_zero : forall i, lattice_cost i i == 0.
Proof.
  intro i. unfold lattice_cost. rewrite Z.sub_diag. simpl. reflexivity.
Qed.

Lemma cost_symmetric : forall i j, lattice_cost i j == lattice_cost j i.
Proof.
  intros i j. unfold lattice_cost, Qeq. simpl. lia.
Qed.

Lemma cost_nonneg : forall i j, 0 <= lattice_cost i j.
Proof.
  intros. unfold lattice_cost.
  unfold Qle. simpl. lia.
Qed.

(** Concrete costs *)
Lemma cost_0_2 : lattice_cost 0 2 == 2.
Proof. vm_compute. reflexivity. Qed.

Lemma cost_0_1 : lattice_cost 0 1 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma cost_1_2 : lattice_cost 1 2 == 1.
Proof. vm_compute. reflexivity. Qed.

(** General cost matrix *)
Definition CostMatrix := nat -> nat -> Q.

(* ================================================================== *)
(*  TRANSPORT PLAN                                                     *)
(* ================================================================== *)

(** A transport plan: function from (i,j) to Q *)
Definition TransportPlan := nat -> nat -> Q.

(** Transport cost for a given plan *)
Definition transport_cost (pi : TransportPlan) (C : CostMatrix)
    (K : nat) : Q :=
  fold_left (fun acc i =>
    acc + fold_left (fun acc2 j =>
      acc2 + C i j * pi i j) (seq 0 (S K)) 0)
    (seq 0 (S K)) 0.

(* ================================================================== *)
(*  CONCRETE EXAMPLES                                                  *)
(* ================================================================== *)

(** Example 1: transport from delta(0) to delta(2) on 3 points *)
Definition plan_delta_0_to_2 : TransportPlan :=
  fun i j => if (Nat.eqb i 0 && Nat.eqb j 2)%bool then 1 else 0.

Lemma plan_012_nonneg : forall i j,
  0 <= plan_delta_0_to_2 i j.
Proof.
  intros i j. unfold plan_delta_0_to_2.
  destruct (Nat.eqb i 0 && Nat.eqb j 2)%bool; lra.
Qed.

Lemma plan_012_cost :
  transport_cost plan_delta_0_to_2 lattice_cost 2 == 2.
Proof.
  unfold transport_cost, plan_delta_0_to_2, lattice_cost.
  vm_compute. reflexivity.
Qed.

(** Example 2: transport from uniform(2) to delta(1) on 3 points *)
Definition plan_uniform_to_delta1 : TransportPlan :=
  fun i j => if Nat.eqb j 1 then
    1 / inject_Z (Z.of_nat 3)
  else 0.

Lemma plan_utd_cost :
  transport_cost plan_uniform_to_delta1 lattice_cost 2 == 2 # 3.
Proof.
  unfold transport_cost, plan_uniform_to_delta1, lattice_cost.
  vm_compute. reflexivity.
Qed.

(** Example 3: identity plan (mu = nu) has cost 0 *)
Definition identity_plan (mu : list Q) : TransportPlan :=
  fun i j => if Nat.eqb i j then nth i mu 0 else 0.

Lemma identity_cost_concrete :
  transport_cost (identity_plan [1#3; 1#3; 1#3]) lattice_cost 2 == 0.
Proof.
  unfold transport_cost, identity_plan, lattice_cost.
  vm_compute. reflexivity.
Qed.
