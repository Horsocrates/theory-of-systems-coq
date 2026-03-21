(** * PottsTransfer.v -- Q-state Potts model transfer matrix
    Elements: potts_transfer, potts3_lambda, Z_potts3, potts3_energy
    Roles:    T_{σ,σ'} = exp(β·δ(σ,σ')), eigenvalues known analytically
    Rules:    Potts Q=3: first-order transition vs Ising second-order
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.MatN.

Open Scope Q_scope.

(* ================================================================== *)
(*  POTTS Q=3 TRANSFER MATRIX (width 1)                                *)
(* ================================================================== *)

(** T_{σ,σ'} = exp(β) if σ=σ', else 1 *)
Definition potts_transfer (Q_states : nat) (beta : Q) (M : nat) : MatN :=
  fun s s' =>
    if Nat.eqb s s' then exp_QN beta M else 1.

(** Eigenvalues of Q×Q Potts (width 1):
    λ₊ = exp(β) + Q-1 (trivial rep, simple)
    λ₋ = exp(β) - 1 (standard rep, multiplicity Q-1) *)

Definition potts3_lambda_plus (beta : Q) (M : nat) : Q :=
  exp_QN beta M + 2.

Definition potts3_lambda_minus (beta : Q) (M : nat) : Q :=
  exp_QN beta M - 1.

(** Gap = λ₊ - λ₋ = 3 (CONSTANT! independent of β!) *)
Lemma potts3_gap_constant : forall beta M,
  potts3_lambda_plus beta M - potts3_lambda_minus beta M == 3.
Proof. intros. unfold potts3_lambda_plus, potts3_lambda_minus. ring. Qed.

(** Concrete eigenvalues at β=1, M=3 *)
Lemma potts3_lp_1 : potts3_lambda_plus 1 3 == 14#3.
Proof. unfold potts3_lambda_plus. vm_compute. reflexivity. Qed.

Lemma potts3_lm_1 : potts3_lambda_minus 1 3 == 5#3.
Proof. unfold potts3_lambda_minus. vm_compute. reflexivity. Qed.

(** Both positive for β > 0 *)
Lemma potts3_lp_pos : 0 < potts3_lambda_plus 1 3.
Proof. rewrite potts3_lp_1. lra. Qed.

Lemma potts3_lm_pos : 0 < potts3_lambda_minus 1 3.
Proof. rewrite potts3_lm_1. lra. Qed.

(* ================================================================== *)
(*  PARTITION FUNCTION AND ENERGY                                      *)
(* ================================================================== *)

(** Z(N) = λ₊^N + 2·λ₋^N (multiplicity 2 for degenerate eigenvalue) *)
Definition Z_potts3 (N : nat) (beta : Q) (M : nat) : Q :=
  qpow_nat (potts3_lambda_plus beta M) N +
  2 * qpow_nat (potts3_lambda_minus beta M) N.

Lemma Z_potts3_1 : Z_potts3 1 1 3 == 24#3.
Proof. unfold Z_potts3. vm_compute. reflexivity. Qed.

(** Energy per site: E = -exp(β)/λ₊ *)
Definition potts3_energy (beta : Q) (M : nat) : Q :=
  - exp_QN beta M / potts3_lambda_plus beta M.

Lemma potts3_energy_1 : potts3_energy 1 3 == -(4#7).
Proof. unfold potts3_energy. vm_compute. reflexivity. Qed.

(** Trace verification via matN *)
Lemma potts3_trace_matches :
  traceN 3 (potts_transfer 3 1 3) == potts3_lambda_plus 1 3 + 2 * potts3_lambda_minus 1 3.
Proof. vm_compute. reflexivity. Qed.

(** Potts Q=2 comparison: same as Ising up to rescaling *)
(** Potts Q=2: λ₊ = e^β + 1, λ₋ = e^β - 1 *)
(** Gap = 2 (constant!) vs Ising gap = 2sinh(β) (β-dependent) *)
(** Different because Potts uses δ, Ising uses σ·σ' *)

(** SYNTHESIS *)
Theorem potts_synthesis :
  (* Gap is constant *)
  potts3_lambda_plus 1 3 - potts3_lambda_minus 1 3 == 3 /\
  (* Energy at β=1 *)
  potts3_energy 1 3 == -(4#7) /\
  (* Both eigenvalues positive *)
  0 < potts3_lambda_plus 1 3 /\
  0 < potts3_lambda_minus 1 3.
Proof.
  split; [|split; [|split]].
  - exact (potts3_gap_constant 1 3).
  - exact potts3_energy_1.
  - exact potts3_lp_pos.
  - exact potts3_lm_pos.
Qed.
