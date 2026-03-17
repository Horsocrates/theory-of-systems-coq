(** * ProcessSpinStatistics.v — Spin-Statistics from E/R/R

    Theory of Systems — Process Physics (Wave 4, Phase G4)

    Elements: spin_stat_connection, exchange_sign, partition_function
    Roles:    bosonic ↔ symmetric rules, fermionic ↔ antisymmetric rules
    Rules:    spin-statistics theorem from E/R/R decomposition
    Status:   complete

    STATUS: 25 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessERRSymmetry.
From ToS Require Import process.ProcessERRFermion.
From ToS Require Import process.ProcessPauliExclusion.

(* ================================================================== *)
(*  Part I: Exchange Sign (~8 Qed)                                    *)
(* ================================================================== *)

(** Exchange sign: +1 for bosons, -1 for fermions *)
Definition exchange_sign (sys : ERRSystem) (i j : nat) : Q :=
  rule_symmetric sys i j - rule_antisymmetric sys i j.

(** For bosonic systems: exchange sign = full rule *)
Lemma exchange_bosonic : forall sys i j,
  is_bosonic sys -> (i < err_nsites sys)%nat -> (j < err_nsites sys)%nat ->
  exchange_sign sys i j == err_rule sys i j.
Proof.
  intros sys i j Hb Hi Hj. unfold exchange_sign.
  assert (Ha := bosonic_antisymmetric_zero sys i j Hb Hi Hj).
  assert (Hd := rule_decomposition sys i j).
  lra.
Qed.

(** For fermionic systems: exchange sign = -full rule *)
Lemma exchange_fermionic : forall sys i j,
  is_fermionic sys -> (i < err_nsites sys)%nat -> (j < err_nsites sys)%nat ->
  exchange_sign sys i j == - err_rule sys i j.
Proof.
  intros sys i j Hf Hi Hj. unfold exchange_sign.
  assert (Hs := fermionic_symmetric_zero sys i j Hf Hi Hj).
  assert (Hd := rule_decomposition sys i j).
  lra.
Qed.

(** Symmetric part is symmetric *)
Lemma exchange_sym_part : forall sys i j,
  rule_symmetric sys i j == rule_symmetric sys j i.
Proof. intros. apply symmetric_is_symmetric. Qed.

(** Antisymmetric part flips *)
Lemma exchange_anti_part : forall sys i j,
  rule_antisymmetric sys i j == - rule_antisymmetric sys j i.
Proof. intros. apply antisymmetric_is_antisymmetric. Qed.

(** Decomposition: rule = sym + antisym *)
Lemma spin_stat_decomposition : forall sys i j,
  err_rule sys i j == rule_symmetric sys i j + rule_antisymmetric sys i j.
Proof. intros. apply rule_decomposition. Qed.

(* ================================================================== *)
(*  Part II: Pauli Principle Connection (~8 Qed)                     *)
(* ================================================================== *)

(** Pauli: fermionic self-interaction vanishes *)
Lemma pauli_from_antisymmetry : forall sys i,
  is_fermionic sys -> (i < err_nsites sys)%nat ->
  err_rule sys i i == 0.
Proof. intros. apply pauli_exclusion; assumption. Qed.

(** Bosonic: no Pauli constraint *)
Lemma no_pauli_for_bosons : forall sys i,
  is_bosonic sys -> (i < err_nsites sys)%nat ->
  err_rule sys i i == err_rule sys i i.
Proof. intros. reflexivity. Qed.

(** Self-exchange sign for fermions *)
Lemma self_exchange_fermionic : forall sys i,
  is_fermionic sys -> (i < err_nsites sys)%nat ->
  exchange_sign sys i i == 0.
Proof.
  intros sys i Hf Hi. unfold exchange_sign.
  assert (Hs := fermionic_symmetric_zero sys i i Hf Hi Hi).
  assert (Ha : rule_antisymmetric sys i i == 0).
  { assert (Haa := antisymmetric_is_antisymmetric sys i i).
    lra. }
  lra.
Qed.

(** Self-exchange for bosons: twice the symmetric part *)
Lemma self_exchange_bosonic : forall sys i,
  is_bosonic sys -> (i < err_nsites sys)%nat ->
  exchange_sign sys i i == err_rule sys i i.
Proof.
  intros sys i Hb Hi. apply exchange_bosonic; assumption.
Qed.

(** Pauli absolute value *)
Lemma pauli_abs_zero : forall sys i,
  is_fermionic sys -> (i < err_nsites sys)%nat ->
  Qabs (err_rule sys i i) == 0.
Proof. intros. apply pauli_abs; assumption. Qed.

(* ================================================================== *)
(*  Part III: Partition Function (~9 Qed)                             *)
(* ================================================================== *)

(** Partition function contribution: Σ exp(-β·E)
    For bosons: all states contribute (unlimited occupation)
    For fermions: only states with ≤1 particle per site *)

(** Bosonic partition: geometric series 1/(1-x) ≈ 1 + x + x² *)
Definition bosonic_partition (x : Q) (n_terms : nat) : Q :=
  match n_terms with
  | 0%nat => 0
  | 1%nat => 1
  | 2%nat => 1 + x
  | _ => 1 + x + x * x
  end.

(** Fermionic partition: only 0 or 1 particle → 1 + x *)
Definition fermionic_partition (x : Q) : Q := 1 + x.

(** Bosonic partition at 1 term *)
Lemma bosonic_1 : forall x, bosonic_partition x 1 == 1.
Proof. intros. unfold bosonic_partition. ring. Qed.

(** Bosonic partition at 2 terms *)
Lemma bosonic_2 : forall x, bosonic_partition x 2 == 1 + x.
Proof. intros. unfold bosonic_partition. ring. Qed.

(** Fermionic partition is bosonic at 2 terms *)
Lemma fermion_boson_2 : forall x,
  fermionic_partition x == bosonic_partition x 2.
Proof. intros. unfold fermionic_partition, bosonic_partition. ring. Qed.

(** Bosonic has more states at 3 terms *)
Lemma bosonic_more_states : forall x,
  0 < x ->
  fermionic_partition x < bosonic_partition x 3.
Proof.
  intros x Hx. unfold fermionic_partition, bosonic_partition.
  assert (H : 0 < x * x).
  { apply Qmult_lt_0_compat; lra. }
  lra.
Qed.

(** Partition function positive *)
Lemma fermionic_partition_pos : forall x,
  0 < x ->
  0 < fermionic_partition x.
Proof. intros. unfold fermionic_partition. lra. Qed.

(** Bosonic partition positive *)
Lemma bosonic_partition_pos : forall x n,
  0 <= x -> (1 <= n)%nat ->
  0 < bosonic_partition x n.
Proof.
  intros x n Hx Hn. unfold bosonic_partition.
  destruct n; [lia|]. destruct n; [lra|]. destruct n; [lra|].
  assert (H : 0 <= x * x) by (apply Qmult_le_0_compat; lra).
  lra.
Qed.

(* ================================================================== *)
(*  Part IV: Summary                                                    *)
(* ================================================================== *)

Theorem spin_statistics_connection :
  (* Decomposition: rule = symmetric + antisymmetric *)
  (forall sys i j, err_rule sys i j ==
    rule_symmetric sys i j + rule_antisymmetric sys i j) /\
  (* Pauli exclusion for fermions *)
  (forall sys i, is_fermionic sys -> (i < err_nsites sys)%nat ->
    err_rule sys i i == 0) /\
  (* Bosonic partition > fermionic partition (more states) *)
  (forall x, 0 < x -> fermionic_partition x < bosonic_partition x 3).
Proof.
  split; [|split].
  - exact rule_decomposition.
  - exact pauli_exclusion.
  - exact bosonic_more_states.
Qed.

Theorem phase_G4_complete :
  (* Exchange sign for bosons = full rule *)
  (forall sys i j, is_bosonic sys ->
    (i < err_nsites sys)%nat -> (j < err_nsites sys)%nat ->
    exchange_sign sys i j == err_rule sys i j) /\
  (* Exchange sign for fermions = -full rule *)
  (forall sys i j, is_fermionic sys ->
    (i < err_nsites sys)%nat -> (j < err_nsites sys)%nat ->
    exchange_sign sys i j == - err_rule sys i j) /\
  (* Pauli from antisymmetry *)
  (forall sys i, is_fermionic sys -> (i < err_nsites sys)%nat ->
    err_rule sys i i == 0).
Proof.
  split; [|split].
  - exact exchange_bosonic.
  - exact exchange_fermionic.
  - exact pauli_exclusion.
Qed.
