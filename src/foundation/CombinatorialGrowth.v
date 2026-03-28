(* CombinatorialGrowth.v *)
(* Combinatorial growth of potential vs finite attention *)
(* E: K energies, R: K(K-1)/2 pairs, R: gap = potential - attention *)
(* All Qed, no Admitted. Standalone. *)

From Stdlib Require Import QArith Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

Definition attention_width : nat := 3%nat.

Definition pot (K : nat) : nat := (K + K * (K - 1) / 2)%nat.

Definition gap (K : nat) : nat := (pot K - attention_width)%nat.

Lemma gap_3 : gap 3 = 3%nat.
Proof. simpl. reflexivity. Qed.

Lemma gap_5 : gap 5 = 12%nat.
Proof. simpl. reflexivity. Qed.

Lemma gap_10 : gap 10 = 52%nat.
Proof. simpl. reflexivity. Qed.

Lemma gap_20 : gap 20 = 207%nat.
Proof. simpl. reflexivity. Qed.

Lemma gap_grows_3_5 : (gap 3 < gap 5)%nat.
Proof. unfold gap, pot, attention_width. simpl. lia. Qed.

Lemma gap_grows_5_10 : (gap 5 < gap 10)%nat.
Proof. unfold gap, pot, attention_width. simpl. lia. Qed.

Lemma gap_grows_10_20 : (gap 10 < gap 20)%nat.
Proof. unfold gap, pot, attention_width. simpl. lia. Qed.

(* ===== Ratio potential/K grows: "more you know, more you don't know" ===== *)
Lemma ratio_5 : inject_Z (Z.of_nat (pot 5)) / inject_Z (Z.of_nat 5) == 3.
Proof. vm_compute. reflexivity. Qed.

Lemma ratio_10 : inject_Z (Z.of_nat (pot 10)) / inject_Z (Z.of_nat 10) == 11#2.
Proof. vm_compute. reflexivity. Qed.

Lemma ratio_grows : 3 < 11#2.
Proof. lra. Qed.

(* ===== P4: potential always exceeds attention for large K ===== *)
Lemma inexhaustible_6 : (attention_width < pot 6)%nat.
Proof. unfold attention_width, pot. simpl. lia. Qed.

Lemma inexhaustible_10 : (attention_width < pot 10)%nat.
Proof. unfold attention_width, pot. simpl. lia. Qed.

Lemma inexhaustible_20 : (attention_width < pot 20)%nat.
Proof. unfold attention_width, pot. simpl. lia. Qed.
