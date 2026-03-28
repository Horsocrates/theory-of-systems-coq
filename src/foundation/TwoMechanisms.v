(* TwoMechanisms.v *)
(* Two Mechanisms of Creation: Analysis and Synthesis *)
(* E: distinction energies, R: interaction (combination), R: potential > actual *)
(* All Qed, no Admitted. Standalone. *)

From Stdlib Require Import QArith Lia ZArith List Bool.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ===== Analysis: zoom into existing distinction ===== *)
Definition analysis_potential (K : nat) : nat := K.

(* ===== Synthesis: combine two distinct energies ===== *)
Definition synthesis_pairs (K : nat) : nat := (K * (K - 1) / 2)%nat.

(* Concrete pair counts *)
Lemma pairs_1 : synthesis_pairs 1 = 0%nat.
Proof. simpl. reflexivity. Qed.

Lemma pairs_2 : synthesis_pairs 2 = 1%nat.
Proof. simpl. reflexivity. Qed.

Lemma pairs_3 : synthesis_pairs 3 = 3%nat.
Proof. simpl. reflexivity. Qed.

Lemma pairs_4 : synthesis_pairs 4 = 6%nat.
Proof. simpl. reflexivity. Qed.

Lemma pairs_5 : synthesis_pairs 5 = 10%nat.
Proof. simpl. reflexivity. Qed.

Lemma pairs_10 : synthesis_pairs 10 = 45%nat.
Proof. simpl. reflexivity. Qed.

(* ===== Total potential = analysis + synthesis ===== *)
Definition total_potential (K : nat) : nat :=
  (analysis_potential K + synthesis_pairs K)%nat.

Lemma potential_3 : total_potential 3 = 6%nat.
Proof. simpl. reflexivity. Qed.

Lemma potential_4 : total_potential 4 = 10%nat.
Proof. simpl. reflexivity. Qed.

Lemma potential_5 : total_potential 5 = 15%nat.
Proof. simpl. reflexivity. Qed.

Lemma potential_10 : total_potential 10 = 55%nat.
Proof. simpl. reflexivity. Qed.

Lemma potential_20 : total_potential 20 = 210%nat.
Proof. simpl. reflexivity. Qed.

(* ===== Potential exceeds K — concrete cases ===== *)
Lemma exceeds_3 : (3 < total_potential 3)%nat.
Proof. unfold total_potential, analysis_potential, synthesis_pairs. simpl. lia. Qed.

Lemma exceeds_5 : (5 < total_potential 5)%nat.
Proof. unfold total_potential, analysis_potential, synthesis_pairs. simpl. lia. Qed.

Lemma exceeds_10 : (10 < total_potential 10)%nat.
Proof. unfold total_potential, analysis_potential, synthesis_pairs. simpl. lia. Qed.

Lemma exceeds_20 : (20 < total_potential 20)%nat.
Proof. unfold total_potential, analysis_potential, synthesis_pairs. simpl. lia. Qed.

(* ===== Witness condition: new quality from interaction ===== *)
Definition interacts (a b : nat) : bool := negb (Nat.eqb a b).

Lemma same_no_new : interacts 3 3 = false.
Proof. simpl. reflexivity. Qed.

Lemma diff_new : interacts 3 5 = true.
Proof. simpl. reflexivity. Qed.

Lemma diff_new_2 : interacts 1 7 = true.
Proof. simpl. reflexivity. Qed.
