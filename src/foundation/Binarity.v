(* Binarity.v *)
(* E: Side (Marked/Unmarked), two_pow, microstates *)
(* R: L2 exclusion, L3 exhaustion, exponential growth *)
(* R: Binary = derived from distinction. Shannon bit = 1 distinction. *)

From Stdlib Require Import QArith Lia ZArith List Bool.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

Inductive Side := Marked | Unmarked.

Lemma L2_exclusive : Marked <> Unmarked.
Proof. discriminate. Qed.

Lemma L3_exhaustive : forall s : Side, s = Marked \/ s = Unmarked.
Proof. destruct s; [left|right]; reflexivity. Qed.

Lemma exactly_two_sides : forall s : Side, s = Marked \/ s = Unmarked.
Proof. exact L3_exhaustive. Qed.

(* 2^K *)
Fixpoint two_pow (K : nat) : nat :=
  match K with
  | O => 1%nat
  | S K' => (2 * two_pow K')%nat
  end.

Lemma pow_0 : two_pow 0 = 1%nat.
Proof. reflexivity. Qed.

Lemma pow_1 : two_pow 1 = 2%nat.
Proof. reflexivity. Qed.

Lemma pow_2 : two_pow 2 = 4%nat.
Proof. reflexivity. Qed.

Lemma pow_3 : two_pow 3 = 8%nat.
Proof. reflexivity. Qed.

Lemma pow_4 : two_pow 4 = 16%nat.
Proof. reflexivity. Qed.

Lemma pow_5 : two_pow 5 = 32%nat.
Proof. reflexivity. Qed.

Lemma pow_monotone : forall K, (two_pow K <= two_pow (S K))%nat.
Proof. induction K; simpl; lia. Qed.

Lemma pow_positive : forall K, (0 < two_pow K)%nat.
Proof. induction K; simpl; lia. Qed.

Definition microstates (n : nat) : nat := two_pow n.

Lemma more_dist_more_states : forall K, (microstates K <= microstates (S K))%nat.
Proof. intro K. unfold microstates. apply pow_monotone. Qed.

Lemma new_dist_doubles : forall K, microstates (S K) = (2 * microstates K)%nat.
Proof. intro K. unfold microstates. simpl. reflexivity. Qed.

(* Landauer: erasing = violating L5. Cost = k T ln(2) per bit. *)
(* Binary code DERIVED from L2+L3. Shannon bit = 1 distinction. *)

Lemma pow_10 : two_pow 10 = 1024%nat.
Proof. reflexivity. Qed.

(* 2^K grows exponentially *)
Lemma pow_double : forall K, two_pow (S K) = (2 * two_pow K)%nat.
Proof. intro. simpl. reflexivity. Qed.

(* Number of bits = number of distinctions *)
(* This is the BRIDGE: distinction count = entropy (up to k ln2) *)

Lemma pow_strict_monotone : forall K, (two_pow K < two_pow (S (S K)))%nat.
Proof.
  induction K.
  - simpl. lia.
  - simpl. simpl in IHK. lia.
Qed.

Lemma pow_6 : two_pow 6 = 64%nat.
Proof. reflexivity. Qed.
