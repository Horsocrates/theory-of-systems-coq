(** * KineticCommutatorSynthesis.v — Synthesis: kinetic = commutator
    Elements: kinetic_commutator_grand, operator_summary, laplacian_structure
    Roles:    Collects all concrete verifications into grand theorems
    Rules:    [X,P] off-diagonal = 1/2; L = 2I - A; tr(L) = 2K
    Status:   complete
    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Lia.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.heisenberg.KineticCommutator.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Grand Synthesis                                            *)
(* ================================================================== *)

Theorem kinetic_commutator_grand :
  laplacian 5 0 0 == 2 /\
  laplacian 5 0 1 == -(1) /\
  laplacian 5 0 2 == 0 /\
  adj_chain 5 0 1 == 1 /\
  adj_chain 5 0 2 == 0.
Proof.
  split; [exact laplacian_00|].
  split; [exact laplacian_01|].
  split; [exact laplacian_02|].
  split; [exact adj_01|].
  exact adj_02.
Qed.

Theorem commutator_offdiag_synthesis :
  inject_Z 3 * (-(1#2)) - (-(1#2)) * inject_Z 4 == 1#2 /\
  inject_Z 4 * (-(1#2)) - (-(1#2)) * inject_Z 5 == 1#2 /\
  inject_Z 5 * (-(1#2)) - (-(1#2)) * inject_Z 6 == 1#2.
Proof.
  split; [exact comm_offdiag_m3|].
  split; [exact comm_offdiag_m4|].
  exact comm_offdiag_m5.
Qed.

Theorem laplacian_structure_synthesis :
  laplacian 5 0 0 == 2 * (if Nat.eqb 0 0 then 1 else 0) - adj_chain 5 0 0 /\
  laplacian 5 0 1 == 2 * (if Nat.eqb 0 1 then 1 else 0) - adj_chain 5 0 1 /\
  laplacian 5 1 1 == 2 * (if Nat.eqb 1 1 then 1 else 0) - adj_chain 5 1 1 /\
  laplacian 5 1 2 == 2 * (if Nat.eqb 1 2 then 1 else 0) - adj_chain 5 1 2.
Proof.
  split; [exact laplacian_is_2I_minus_adj_00|].
  split; [exact laplacian_is_2I_minus_adj_01|].
  split; [exact laplacian_is_2I_minus_adj_11|].
  exact laplacian_is_2I_minus_adj_12.
Qed.

Theorem trace_synthesis :
  laplacian 5 0 0 + laplacian 5 1 1 + laplacian 5 2 2 +
  laplacian 5 3 3 + laplacian 5 4 4 == 10.
Proof. exact tr_laplacian_K5. Qed.

(* ================================================================== *)
(*  Part II: Operator Consistency                                      *)
(* ================================================================== *)

(** X is diagonal: off-diagonal entries are 0 *)
Lemma X_offdiag_01 : X_op 5 0 1 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma X_diag_3 : X_op 5 3 3 == 3.
Proof. vm_compute. reflexivity. Qed.

(** P is antisymmetric: P_{01} = -P_{10} *)
Lemma P_antisym_01 : P_op 5 0 1 == -(P_op 5 1 0).
Proof. vm_compute. reflexivity. Qed.

(** Adjacency is symmetric: A_{01} = A_{10} *)
Lemma adj_sym_01 : adj_chain 5 0 1 == adj_chain 5 1 0.
Proof. vm_compute. reflexivity. Qed.
