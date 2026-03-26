(* CircleOpened.v *)
(* Elements: dependency chain as nat steps *)
(* Roles: linear chain L1 -> doubly_stochastic -> Schur -> second_law -> memory *)
(* Rules: acyclicity, each step depends only on previous *)

From Coq Require Import QArith Lia Lqa.
From ToS Require Import stdlib.foundations.DistinctionPrior.

Open Scope Q_scope.

(* ===== Circle Opened: Linear Dependency Chain ===== *)

(* Steps in the derivation chain *)
Definition step_L1 : nat := 1%nat.
Definition step_doubly : nat := 2%nat.
Definition step_schur : nat := 3%nat.
Definition step_second_law : nat := 4%nat.
Definition step_memory : nat := 5%nat.

(* Each step depends only on the previous *)
Definition depends_on (a b : nat) : Prop := (b + 1 = a)%nat.

Lemma chain_L1_to_doubly : depends_on step_doubly step_L1.
Proof. unfold depends_on, step_doubly, step_L1. lia. Qed.

Lemma chain_doubly_to_schur : depends_on step_schur step_doubly.
Proof. unfold depends_on, step_schur, step_doubly. lia. Qed.

Lemma chain_schur_to_second_law : depends_on step_second_law step_schur.
Proof. unfold depends_on, step_second_law, step_schur. lia. Qed.

Lemma chain_second_law_to_memory : depends_on step_memory step_second_law.
Proof. unfold depends_on, step_memory, step_second_law. lia. Qed.

(* Acyclicity: strict ordering *)
Lemma chain_acyclic_12 : (step_L1 < step_doubly)%nat.
Proof. unfold step_L1, step_doubly. lia. Qed.

Lemma chain_acyclic_23 : (step_doubly < step_schur)%nat.
Proof. unfold step_doubly, step_schur. lia. Qed.

Lemma chain_acyclic_34 : (step_schur < step_second_law)%nat.
Proof. unfold step_schur, step_second_law. lia. Qed.

Lemma chain_acyclic_45 : (step_second_law < step_memory)%nat.
Proof. unfold step_second_law, step_memory. lia. Qed.

(* Transitivity: L1 < memory *)
Lemma chain_L1_lt_memory : (step_L1 < step_memory)%nat.
Proof. unfold step_L1, step_memory. lia. Qed.

(* Connection to distinction prior: starts at S_0 *)
Lemma chain_starts_at_zero : S_0 == 0.
Proof. exact process_starts_at_zero. Qed.
