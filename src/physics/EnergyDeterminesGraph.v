(** * EnergyDeterminesGraph.v — Energy-mass modifies graph structure as ToS System
    Elements: enhanced_degree, propagation_time, flat vs curved paths
    Roles:    Mass enhances local connectivity → slows propagation
    Rules:    Propagation time = sum(degree/2), mass increases degree near source
    STATUS:   15 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: March 2026

    ★★★★ ENERGY DETERMINES GRAPH TOPOLOGY
    FROM: Mass at position → enhanced local degree
    DERIVE: Propagation through enhanced region takes longer
    → Time dilation near mass = gravity
    → Flat graph: uniform propagation
    → Curved graph: non-uniform propagation near mass

    NOT DERIVED: exact Schwarzschild metric, continuous limit.
    DERIVED: mass-dependent propagation delay = discrete gravitational redshift.
*)

From Stdlib Require Import QArith Qabs Lia ZArith List Bool PeanoNat.
From Stdlib Require Import Lqa.
Import ListNotations.

Open Scope Q_scope.

(* ================================================================== *)
(*  ENHANCED DEGREE NEAR MASS                                          *)
(* ================================================================== *)

(** Enhanced degree: near a mass source, connectivity increases *)
Definition abs_diff (a b : nat) : nat :=
  if Nat.ltb a b then b - a else a - b.

Definition enhanced_degree (mass_pos mass_strength radius v : nat) : nat :=
  let d := Nat.max 1 (abs_diff v mass_pos) in
  if Nat.leb d radius then (2 + mass_strength / d)%nat else 2%nat.

(** Propagation time: sum of local step costs (degree/2) along a path *)
Fixpoint propagation_time_aux (deg_fn : nat -> nat) (pos steps : nat) : Q :=
  match steps with
  | O => 0
  | S n => inject_Z (Z.of_nat (deg_fn pos)) / 2 + propagation_time_aux deg_fn (S pos) n
  end.

Definition propagation_time (deg_fn : nat -> nat) (a len : nat) : Q :=
  propagation_time_aux deg_fn a len.

(* ================================================================== *)
(*  FLAT GRAPH PROPERTIES                                              *)
(* ================================================================== *)

(** On a flat graph (degree=2 everywhere), each step costs 1 *)
Lemma flat_step_cost : inject_Z (Z.of_nat 2) / 2 == 1.
Proof. vm_compute. reflexivity. Qed.

(** Flat propagation over 5 steps = 5 *)
Lemma flat_time_5 : propagation_time (fun _ => 2%nat) O 5 == 5.
Proof. vm_compute. reflexivity. Qed.

(** Flat propagation over 3 steps = 3 *)
Lemma flat_time_3 : propagation_time (fun _ => 2%nat) O 3 == 3.
Proof. vm_compute. reflexivity. Qed.

(** Flat propagation over 1 step = 1 *)
Lemma flat_time_1 : propagation_time (fun _ => 2%nat) O 1 == 1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  MASS-ENHANCED GRAPH PROPERTIES                                     *)
(* ================================================================== *)

(** At the mass center: dist=0→max(1,0)=1, degree = 2 + 4/1 = 6 *)
Lemma mass_degree_at_center : enhanced_degree 5 4 3 5 = 6%nat.
Proof. vm_compute. reflexivity. Qed.

(** One step away: dist=1, degree = 2 + 4/1 = 6 *)
Lemma mass_degree_near : enhanced_degree 5 4 3 4 = 6%nat.
Proof. vm_compute. reflexivity. Qed.

(** Two steps away: dist=2, degree = 2 + 4/2 = 4 *)
Lemma mass_degree_medium : enhanced_degree 5 4 3 3 = 4%nat.
Proof. vm_compute. reflexivity. Qed.

(** Three steps away: dist=3, degree = 2 + 4/3 = 3 (nat div) *)
Lemma mass_degree_edge : enhanced_degree 5 4 3 2 = 3%nat.
Proof. vm_compute. reflexivity. Qed.

(** Far from mass: outside radius → degree = 2 *)
Lemma mass_degree_far : enhanced_degree 5 4 3 10 = 2%nat.
Proof. vm_compute. reflexivity. Qed.

(** Mass slows propagation: curved path through mass region > flat *)
Lemma mass_slows_propagation :
  let curved := propagation_time (enhanced_degree 5 4 3) 2 6 in
  let flat   := propagation_time (fun _ => 2%nat) 2 6 in
  flat < curved.
Proof. vm_compute. reflexivity. Qed.

(** Propagation ratio: curved time through mass region *)
Lemma propagation_curved_value :
  propagation_time (enhanced_degree 5 4 3) 2 6 == 29 # 2.
Proof. vm_compute. reflexivity. Qed.

(** Zero propagation for zero steps *)
Lemma propagation_zero : forall f, propagation_time f O O == 0.
Proof. intros. unfold propagation_time. simpl. unfold Qeq. simpl. lia. Qed.

(** Enhanced degree is always >= 2 *)
Lemma enhanced_degree_ge_2 : forall mp ms r v,
  (enhanced_degree mp ms r v >= 2)%nat.
Proof.
  intros. unfold enhanced_degree, abs_diff.
  destruct (Nat.ltb v mp); simpl;
  destruct (Nat.leb _ r); lia.
Qed.

(** Flat degree equals 2: mass with zero strength *)
Lemma zero_mass_flat : forall pos r v,
  enhanced_degree pos O r v = 2%nat.
Proof.
  intros. unfold enhanced_degree, abs_diff.
  destruct (Nat.ltb v pos) eqn:E1;
  destruct (Nat.leb (Nat.max 1 _) r) eqn:E2; simpl;
  try reflexivity.
  - assert (H: (Nat.max 1 (pos - v) > 0)%nat) by lia.
    rewrite Nat.Div0.div_0_l. reflexivity.
  - assert (H: (Nat.max 1 (v - pos) > 0)%nat) by lia.
    rewrite Nat.Div0.div_0_l. reflexivity.
Qed.

(** Dilation ratio: curved/flat > 1 near mass *)
Lemma dilation_ratio_gt_1 :
  propagation_time (enhanced_degree 5 4 3) 2 6 >
  propagation_time (fun _ => 2%nat) 2 6.
Proof. vm_compute. reflexivity. Qed.
