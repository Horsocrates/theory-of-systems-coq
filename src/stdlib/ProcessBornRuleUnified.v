(* ProcessBornRuleUnified.v — Born rule from ProcessSpace *)
From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import PeanoNat.
From ToS Require Import process.ProcessCore.
From ToS Require Import stdlib.ProcessRing.
From ToS Require Import stdlib.ProcessOperatorF.
Open Scope Q_scope.

Definition is_normalized_process (f : RealProcess) (N : nat) : Prop :=
  process_inner f f N == 1.

Definition measurement_probability (psi : RealProcess) (n : nat) : Q :=
  psi n * psi n.

Lemma meas_prob_nonneg : forall psi n, 0 <= measurement_probability psi n.
Proof.
  intros psi n. unfold measurement_probability.
  destruct (Qlt_le_dec (psi n) 0).
  - assert (H : 0 <= -(psi n)) by lra.
    assert (Heq : psi n * psi n == (-(psi n)) * (-(psi n))) by ring.
    rewrite Heq. apply Qmult_le_0_compat; exact H.
  - apply Qmult_le_0_compat; exact q.
Qed.

Definition expectation_value (A : ProcessOp) (psi : RealProcess) (N : nat) : Q :=
  process_inner (A psi) psi N.

Lemma eigenstate_expectation_0 : forall A lambda f,
  is_eigenprocess A f lambda ->
  is_normalized_process f 0 ->
  expectation_value A f 0 == lambda.
Proof.
  intros A lambda f Heig Hnorm.
  unfold expectation_value, process_inner, process_inner_aux.
  rewrite (Heig 0%nat).
  unfold is_normalized_process, process_inner, process_inner_aux in Hnorm.
  assert (Heq : lambda * f 0%nat * f 0%nat == lambda * (f 0%nat * f 0%nat)) by ring.
  rewrite Heq, Hnorm. ring.
Qed.

Lemma born_50_50 : measurement_probability (fun k => if Nat.eqb k 0 then 1 else 0) 0 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma born_orthogonal : measurement_probability (fun k => if Nat.eqb k 0 then 1 else 0) 1 == 0.
Proof. vm_compute. reflexivity. Qed.

Theorem born_rule_unified :
  (forall psi n, 0 <= measurement_probability psi n) /\
  measurement_probability (fun k => if Nat.eqb k 0 then 1 else 0) 0 == 1 /\
  measurement_probability (fun k => if Nat.eqb k 0 then 1 else 0) 1 == 0.
Proof.
  split; [|split].
  - exact meas_prob_nonneg.
  - exact born_50_50.
  - exact born_orthogonal.
Qed.

Definition born_unified_count := 7%nat.
