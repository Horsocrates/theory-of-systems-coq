(** * FiniteSizeComparison.v — Convergence Rate Comparison Table
    Elements: Ising rate, oscillator rate, power comparisons
    Roles:    Compare finite-size convergence across models
    Rules:    osc_rate < ising_rate; powers at K=2,3
    Status:   Stdlib
    STATUS: 8 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ================================================================== *)
(*  CONVERGENCE RATES                                                  *)
(*  Ising: tanh(1) ≈ 289/384 ≈ 0.753                                 *)
(*  Oscillator: exp(-1) ≈ 24/65 ≈ 0.369                              *)
(* ================================================================== *)

Definition ising_rate : Q := 289#384.
Definition osc_rate : Q := 24#65.

Fixpoint qpow (x : Q) (n : nat) : Q :=
  match n with
  | O => 1
  | S k => x * qpow x k
  end.

Lemma osc_less_ising : osc_rate < ising_rate.
Proof. unfold osc_rate, ising_rate. lra. Qed.

Lemma ising_rate_bound : 3#4 < ising_rate /\ ising_rate < 4#5.
Proof. unfold ising_rate. lra. Qed.

Lemma osc_rate_bound : 1#3 < osc_rate /\ osc_rate < 2#5.
Proof. unfold osc_rate. lra. Qed.

(* K=2 power comparison *)
Lemma power_K2_osc : qpow osc_rate 2 == 576#4225.
Proof. vm_compute. reflexivity. Qed.

Lemma power_K2_ising : qpow ising_rate 2 == 83521#147456.
Proof. vm_compute. reflexivity. Qed.

Lemma power_K2_comparison : qpow osc_rate 2 < qpow ising_rate 2.
Proof. unfold osc_rate, ising_rate. simpl. lra. Qed.

(* K=3 power comparison *)
Lemma power_K3_comparison : qpow osc_rate 3 < qpow ising_rate 3.
Proof. unfold osc_rate, ising_rate. simpl. lra. Qed.

Theorem finite_size_comparison_synthesis :
  osc_rate < ising_rate /\
  qpow osc_rate 2 < qpow ising_rate 2 /\
  qpow osc_rate 3 < qpow ising_rate 3.
Proof.
  split; [exact osc_less_ising|].
  split; [exact power_K2_comparison|].
  exact power_K3_comparison.
Qed.
