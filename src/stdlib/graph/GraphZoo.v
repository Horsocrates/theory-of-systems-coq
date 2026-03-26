(* GraphZoo.v *)
(* E/R/R: Elements = graph types (chain, complete, star, cycle, ladder, Petersen)
         Roles = adjacency matrices, edge counts, spectral gaps
         Rules = ordering hbar_chain < hbar_cycle < ... < hbar_complete *)

Require Import QArith.
Require Import QArith.Qabs.
Require Import Lia.
Require Import ZArith.

(* === Adjacency matrices for graph zoo === *)

Definition chain_adj (K : nat) (i j : nat) : Q :=
  if Nat.eqb (S i) j then 1
  else if Nat.eqb i (S j) then 1
  else 0.

Definition complete_adj (K : nat) (i j : nat) : Q :=
  if Nat.eqb i j then 0 else 1.

Definition star_adj (K : nat) (i j : nat) : Q :=
  if orb (Nat.eqb i 0) (Nat.eqb j 0) then
    if Nat.eqb i j then 0 else 1
  else 0.

Open Scope Q_scope.

(* === Edge counts === *)

Definition chain_edges (K : nat) : Q :=
  inject_Z (Z.of_nat K - 1).

Definition complete_edges (K : nat) : Q :=
  inject_Z (Z.of_nat K) * inject_Z (Z.of_nat K - 1) / 2.

Lemma chain_8_edges : chain_edges 8 == 7.
Proof. vm_compute. reflexivity. Qed.

Lemma complete_8_edges : complete_edges 8 == 28.
Proof. vm_compute. reflexivity. Qed.

(* === Spectral gaps (hbar) === *)

Definition hbar_chain : Q := 94#100.

Definition hbar_cycle : Q := 1.

Definition hbar_complete (K : nat) : Q :=
  (inject_Z (Z.of_nat K) - 1) / 2.

Definition hbar_star : Q := 132#100.

Definition hbar_ladder : Q := 131#100.

Definition hbar_petersen : Q := 3#2.

Lemma complete_max_hbar : hbar_complete 8 == 7#2.
Proof. vm_compute. reflexivity. Qed.

Lemma complete_gt_chain : hbar_complete 8 > hbar_chain.
Proof. unfold hbar_complete, hbar_chain. simpl. unfold Qlt. simpl. lia. Qed.

Lemma complete_gt_cycle : hbar_complete 8 > hbar_cycle.
Proof. unfold hbar_complete, hbar_cycle. simpl. unfold Qlt. simpl. lia. Qed.

Lemma hbar_ordering :
  hbar_chain < hbar_cycle /\
  hbar_cycle < hbar_ladder /\
  hbar_ladder < hbar_petersen /\
  hbar_petersen < hbar_complete 8.
Proof.
  unfold hbar_chain, hbar_cycle, hbar_ladder, hbar_petersen, hbar_complete.
  simpl. repeat split; unfold Qlt; simpl; lia.
Qed.

(* === Concrete adjacency entries === *)

Lemma chain_01 : chain_adj 8 0 1 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma chain_02 : chain_adj 8 0 2 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma complete_01 : complete_adj 8 0 1 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma star_01 : star_adj 8 0 1 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma star_12 : star_adj 8 1 2 == 0.
Proof. vm_compute. reflexivity. Qed.

(* === Additional properties === *)

Lemma chain_symmetric : forall K i j, chain_adj K i j == chain_adj K j i.
Proof.
  intros K i j. unfold chain_adj.
  destruct (Nat.eqb (S i) j) eqn:E1;
  destruct (Nat.eqb i (S j)) eqn:E2;
  destruct (Nat.eqb (S j) i) eqn:E3;
  destruct (Nat.eqb j (S i)) eqn:E4;
  try (apply Qeq_refl);
  try (apply Nat.eqb_eq in E1; apply Nat.eqb_eq in E3; lia);
  try (apply Nat.eqb_eq in E1; apply Nat.eqb_neq in E4; lia);
  try (apply Nat.eqb_neq in E1; apply Nat.eqb_eq in E4; lia);
  try (apply Nat.eqb_eq in E2; apply Nat.eqb_neq in E3; lia);
  try (apply Nat.eqb_neq in E2; apply Nat.eqb_eq in E3; lia).
Qed.

Lemma complete_symmetric : forall K i j, complete_adj K i j == complete_adj K j i.
Proof.
  intros K i j. unfold complete_adj.
  destruct (Nat.eqb i j) eqn:E1; destruct (Nat.eqb j i) eqn:E2;
  try apply Qeq_refl.
  - apply Nat.eqb_eq in E1. apply Nat.eqb_neq in E2. lia.
  - apply Nat.eqb_neq in E1. apply Nat.eqb_eq in E2. lia.
Qed.

Lemma complete_no_self_loop : forall K i, complete_adj K i i == 0.
Proof.
  intros K i. unfold complete_adj. rewrite Nat.eqb_refl. apply Qeq_refl.
Qed.

Lemma chain_no_self_loop : forall K i, chain_adj K i i == 0.
Proof.
  intros K i. unfold chain_adj.
  assert (Nat.eqb (S i) i = false) as H1 by (apply Nat.eqb_neq; lia).
  assert (Nat.eqb i (S i) = false) as H2 by (apply Nat.eqb_neq; lia).
  rewrite H1, H2. apply Qeq_refl.
Qed.

Lemma star_center_connects_all : forall K j,
  (0 < j)%nat -> star_adj K 0 j == 1.
Proof.
  intros K j Hj. unfold star_adj.
  assert (Nat.eqb 0 j = false) as Hne by (apply Nat.eqb_neq; lia).
  assert (orb true (Nat.eqb j 0) = true) as Horb by (simpl; reflexivity).
  simpl orb. rewrite Hne. apply Qeq_refl.
Qed.
