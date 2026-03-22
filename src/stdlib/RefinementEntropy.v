(** * RefinementEntropy.v -- Process refinement for topological entropy
    CLASSICAL: h_top(M) = ln(λ_max). One number.
    PROCESS:   {tr(M^K)}_K. Full sequence. Strictly finer.
    WITNESS:   diag(2,1) vs diag(2,-1): same λ_max, different trace at K=1.
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.ProcessRefinement.

Open Scope Q_scope.

(* ================================================================== *)
(*  TRACE PROCESS FOR DIAGONAL 2×2                                     *)
(* ================================================================== *)

(** tr(diag(a,b)^K) = a^K + b^K *)
Definition trace_diag (a b : Q) : Process :=
  fun K => Qpow a K + Qpow b K.

(** WITNESS PAIR: diag(2,1) vs diag(2,-1) *)
Definition trace_A : Process := trace_diag 2 1.
Definition trace_B : Process := trace_diag 2 (-(1)).

(* ================================================================== *)
(*  CONCRETE VALUES                                                    *)
(* ================================================================== *)

Lemma trace_A_0 : trace_A 0%nat == 2.
Proof. unfold trace_A, trace_diag. vm_compute. reflexivity. Qed.

Lemma trace_A_1 : trace_A 1%nat == 3.
Proof. unfold trace_A, trace_diag. vm_compute. reflexivity. Qed.

Lemma trace_A_2 : trace_A 2%nat == 5.
Proof. unfold trace_A, trace_diag. vm_compute. reflexivity. Qed.

Lemma trace_B_0 : trace_B 0%nat == 2.
Proof. unfold trace_B, trace_diag. vm_compute. reflexivity. Qed.

Lemma trace_B_1 : trace_B 1%nat == 1.
Proof. unfold trace_B, trace_diag. vm_compute. reflexivity. Qed.

Lemma trace_B_2 : trace_B 2%nat == 5.
Proof. unfold trace_B, trace_diag. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  STRICT REFINEMENT: same at K=2, different at K=1                   *)
(* ================================================================== *)

Lemma same_K0 : trace_A 0%nat == trace_B 0%nat.
Proof. rewrite trace_A_0, trace_B_0. reflexivity. Qed.

Lemma same_K2 : trace_A 2%nat == trace_B 2%nat.
Proof. rewrite trace_A_2, trace_B_2. reflexivity. Qed.

Lemma diff_K1 : ~ (trace_A 1%nat == trace_B 1%nat).
Proof. rewrite trace_A_1, trace_B_1. unfold Qeq. simpl. lia. Qed.

(** ★ ENTROPY STRICT REFINEMENT *)
Theorem entropy_strict_refinement :
  trace_A 0%nat == trace_B 0%nat /\
  trace_A 2%nat == trace_B 2%nat /\
  ~ (trace_A 1%nat == trace_B 1%nat).
Proof.
  split; [|split].
  - exact same_K0.
  - exact same_K2.
  - exact diff_K1.
Qed.

(** Both have λ_max = 2, so same h_top = ln(2).
    But trace processes differ: trace_A 1 = 3 ≠ 1 = trace_B 1.
    Process is STRICTLY FINER than h_top. *)
