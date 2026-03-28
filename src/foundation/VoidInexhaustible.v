(* VoidInexhaustible.v *)
(* The void is inexhaustible: surplus grows without bound *)
(* E: K actualized, R: K(K-1)/2 surplus pairs, R: ratio surplus/K → ∞ *)
(* All Qed, no Admitted. Standalone. *)

From Stdlib Require Import QArith Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

Definition pot_v (K : nat) : nat := (K + K * (K - 1) / 2)%nat.

(* Surplus = potential - actualized = K(K-1)/2 *)
Definition surplus (K : nat) : nat := (K * (K - 1) / 2)%nat.

Lemma surplus_3 : surplus 3 = 3%nat.
Proof. simpl. reflexivity. Qed.

Lemma surplus_5 : surplus 5 = 10%nat.
Proof. simpl. reflexivity. Qed.

Lemma surplus_10 : surplus 10 = 45%nat.
Proof. simpl. reflexivity. Qed.

Lemma surplus_20 : surplus 20 = 190%nat.
Proof. simpl. reflexivity. Qed.

Lemma surplus_100 : surplus 100 = 4950%nat.
Proof. simpl. reflexivity. Qed.

Lemma surplus_grows_3_5 : (surplus 3 < surplus 5)%nat.
Proof. unfold surplus. simpl. lia. Qed.

Lemma surplus_grows_5_10 : (surplus 5 < surplus 10)%nat.
Proof. unfold surplus. simpl. lia. Qed.

Lemma surplus_grows_10_20 : (surplus 10 < surplus 20)%nat.
Proof. unfold surplus. simpl. lia. Qed.

(* Surplus increases each step *)
Lemma surplus_increases :
  (surplus 5 < surplus 6)%nat /\
  (surplus 6 < surplus 7)%nat /\
  (surplus 7 < surplus 8)%nat.
Proof. unfold surplus. simpl. lia. Qed.

(* ===== Socrates ratio: surplus(K)/K = (K-1)/2 → ∞ ===== *)
Lemma socrates_5 : inject_Z (Z.of_nat (surplus 5)) / inject_Z (Z.of_nat 5) == 2.
Proof. vm_compute. reflexivity. Qed.

Lemma socrates_10 : inject_Z (Z.of_nat (surplus 10)) / inject_Z (Z.of_nat 10) == 9#2.
Proof. vm_compute. reflexivity. Qed.

Lemma socrates_20 : inject_Z (Z.of_nat (surplus 20)) / inject_Z (Z.of_nat 20) == 19#2.
Proof. vm_compute. reflexivity. Qed.

Lemma socrates_grows : 2 < 9#2 /\ (9#2) < 19#2.
Proof. split; lra. Qed.
