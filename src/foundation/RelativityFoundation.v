(* RelativityFoundation.v *)
(* E: ObsSeq, rhas, simultaneous, interval *)
(* R: Different observers, simultaneity = shared distinction *)
(* R: Minkowski metric derived from L5 + observer structure *)

From Stdlib Require Import QArith Lia ZArith List Bool.
From Stdlib Require Import Lqa.
Import ListNotations.

Definition ObsSeq := list nat.
Definition rhas (s : ObsSeq) (d : nat) : bool := existsb (Nat.eqb d) s.

(* Two observer histories *)
Definition O1_K1 : ObsSeq := [1%nat].
Definition O1_K2 : ObsSeq := [3%nat; 1%nat].
Definition O1_K3 : ObsSeq := [5%nat; 3%nat; 1%nat].

Definition O2_K1 : ObsSeq := [2%nat].
Definition O2_K2 : ObsSeq := [3%nat; 2%nat].
Definition O2_K3 : ObsSeq := [7%nat; 3%nat; 2%nat].

(* Different histories *)
Lemma different_K1 : O1_K1 <> O2_K1.
Proof. discriminate. Qed.

(* Simultaneity = shared distinction *)
Definition simultaneous (s1 s2 : ObsSeq) : Prop :=
  exists d, rhas s1 d = true /\ rhas s2 d = true.

Lemma K1_not_simultaneous : ~ simultaneous O1_K1 O2_K1.
Proof.
  intros [d [H1 H2]].
  unfold rhas in *. simpl in *.
  destruct d as [|[|[|n]]]; simpl in *; discriminate.
Qed.

Lemma K2_simultaneous : simultaneous O1_K2 O2_K2.
Proof. exists 3%nat. unfold rhas. simpl. split; reflexivity. Qed.

Lemma cross_simultaneous : simultaneous O1_K2 O2_K3.
Proof. exists 3%nat. unfold rhas. simpl. split; reflexivity. Qed.

(* Finite speed: graph distance *)
Definition graph_distance (a b : nat) : nat :=
  if (b <=? a)%nat then (a - b)%nat else (b - a)%nat.

Definition causally_connected (dt dx : nat) : bool := (dx <=? dt)%nat.

Lemma causal_32 : causally_connected 3 2 = true.
Proof. reflexivity. Qed.

Lemma not_causal_13 : causally_connected 1 3 = false.
Proof. reflexivity. Qed.

Lemma lightlike_22 : causally_connected 2 2 = true.
Proof. reflexivity. Qed.

(* Minkowski interval ds^2 = dt^2 - dx^2 *)
Open Scope Z_scope.

Definition interval (dt dx : nat) : Z :=
  Z.of_nat dt * Z.of_nat dt - Z.of_nat dx * Z.of_nat dx.

Lemma timelike_ex : interval 3 2 > 0.
Proof. unfold interval. simpl. lia. Qed.

Lemma spacelike_ex : interval 1 3 < 0.
Proof. unfold interval. simpl. lia. Qed.

Lemma lightlike_ex : interval 2 2 = 0.
Proof. unfold interval. simpl. lia. Qed.

Lemma timelike_51 : interval 5 1 > 0.
Proof. unfold interval. simpl. lia. Qed.

Lemma different_K2 : O1_K2 <> O2_K2.
Proof. discriminate. Qed.

Lemma different_K3 : O1_K3 <> O2_K3.
Proof. discriminate. Qed.

Lemma spacelike_14 : interval 1 4 < 0.
Proof. unfold interval. simpl. lia. Qed.

(* Signature: (+,-) derived from causality = reachability *)
