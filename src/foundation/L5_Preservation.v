(* L5_Preservation.v *)
(* E/R/R: Elements = DistSets, Roles = L5_preservation, Rules = monotonicity laws *)
(* Standalone — only Stdlib imports *)
(* NOTE: L5-PRESERVATION (D(K)⊆D(K+1)) is now a THEOREM (see L5_as_Theorem.v).
   Chain: L5-ORDER → P4 → Kruskal → L5-PRESERVATION.
   L5-ORDER (sequence + hierarchy) remains a postulate. *)

From Stdlib Require Import List.
From Stdlib Require Import Nat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Import ListNotations.

(** * Core Definitions *)

Definition DistSet := list nat.

Definition dist_count (D : DistSet) : nat := length D.

Definition has_dist (D : DistSet) (d : nat) : bool :=
  existsb (Nat.eqb d) D.

Definition dist_subset (D1 D2 : DistSet) : Prop :=
  forall d, has_dist D1 d = true -> has_dist D2 d = true.

(** L5 preservation: at each step, distinctions are preserved *)
Definition L5_preservation (D : nat -> DistSet) : Prop :=
  forall K, dist_subset (D K) (D (S K)).

(** * Consequence 1: Distinction Permanence *)

Lemma distinction_permanent : forall D K d,
  L5_preservation D ->
  has_dist (D K) d = true ->
  forall K', (K <= K')%nat ->
  has_dist (D K') d = true.
Proof.
  intros D K d HL5 Hd K' Hle.
  induction Hle.
  - exact Hd.
  - apply HL5. exact IHHle.
Qed.

(** * Concrete Example: D0 <= D1 <= D2 <= D3 <= D4 *)

Definition D0 : DistSet := [].
Definition D1 : DistSet := [1].
Definition D2 : DistSet := [1; 3].
Definition D3 : DistSet := [1; 3; 5].
Definition D4 : DistSet := [1; 3; 5; 7].

Lemma L5_concrete_01 : dist_subset D0 D1.
Proof.
  unfold dist_subset, has_dist, D0, D1. intros d H. simpl in H. discriminate.
Qed.

Lemma L5_concrete_12 : dist_subset D1 D2.
Proof.
  unfold dist_subset, has_dist, D1, D2. intros d H.
  simpl in H. destruct (Nat.eqb d 1) eqn:E1.
  - simpl. rewrite E1. reflexivity.
  - simpl in H. discriminate.
Qed.

Lemma L5_concrete_23 : dist_subset D2 D3.
Proof.
  unfold dist_subset, has_dist, D2, D3. intros d H.
  simpl in H. destruct (Nat.eqb d 1) eqn:E1.
  - simpl. rewrite E1. reflexivity.
  - simpl in H. destruct (Nat.eqb d 3) eqn:E3.
    + simpl. rewrite E1. simpl. rewrite E3. reflexivity.
    + simpl in H. discriminate.
Qed.

Lemma L5_concrete_34 : dist_subset D3 D4.
Proof.
  unfold dist_subset, has_dist, D3, D4. intros d H.
  simpl in H. destruct (Nat.eqb d 1) eqn:E1.
  - simpl. rewrite E1. reflexivity.
  - simpl in H. destruct (Nat.eqb d 3) eqn:E3.
    + simpl. rewrite E1. simpl. rewrite E3. reflexivity.
    + simpl in H. destruct (Nat.eqb d 5) eqn:E5.
      * simpl. rewrite E1. simpl. rewrite E3. simpl. rewrite E5. reflexivity.
      * simpl in H. discriminate.
Qed.

(** * Consequence 2: Count Non-Decrease *)

Lemma count_nondecr_01 : (dist_count D0 <= dist_count D1)%nat.
Proof. simpl. lia. Qed.

Lemma count_nondecr_12 : (dist_count D1 <= dist_count D2)%nat.
Proof. simpl. lia. Qed.

Lemma count_nondecr_23 : (dist_count D2 <= dist_count D3)%nat.
Proof. simpl. lia. Qed.

Lemma count_nondecr_34 : (dist_count D3 <= dist_count D4)%nat.
Proof. simpl. lia. Qed.

(** * Consequence 3: Second Law (Q-valued entropy) *)

From Stdlib Require Import QArith.
Open Scope Q_scope.

Definition entropy (D : DistSet) : Q :=
  inject_Z (Z.of_nat (dist_count D)).

Lemma entropy_nondecr_01 : entropy D0 <= entropy D1.
Proof. unfold entropy, dist_count, D0, D1. simpl. discriminate. Qed.

Lemma entropy_nondecr_12 : entropy D1 <= entropy D2.
Proof. unfold entropy, dist_count, D1, D2. simpl. discriminate. Qed.

Lemma entropy_nondecr_23 : entropy D2 <= entropy D3.
Proof. unfold entropy, dist_count, D2, D3. simpl. discriminate. Qed.

Lemma entropy_nondecr_34 : entropy D3 <= entropy D4.
Proof. unfold entropy, dist_count, D3, D4. simpl. discriminate. Qed.

Lemma second_law_from_L5 :
  entropy D0 <= entropy D1 /\
  entropy D1 <= entropy D2 /\
  entropy D2 <= entropy D3 /\
  entropy D3 <= entropy D4.
Proof.
  split. { exact entropy_nondecr_01. }
  split. { exact entropy_nondecr_12. }
  split. { exact entropy_nondecr_23. }
  exact entropy_nondecr_34.
Qed.

Close Scope Q_scope.

(** * Consequence 4: Reliability *)

Lemma L5_implies_reliable : forall D K,
  L5_preservation D ->
  dist_subset (D K) (D (S K)).
Proof.
  intros D K HL5. unfold L5_preservation in HL5. apply HL5.
Qed.

Lemma L5_implies_reliable_forever : forall D K d,
  L5_preservation D ->
  has_dist (D K) d = true ->
  forall K', (K <= K')%nat ->
  has_dist (D K') d = true.
Proof.
  exact distinction_permanent.
Qed.

(** * Consequence 5: Information Conservation *)

Lemma info_conservation :
  (dist_count D0 <= dist_count D1)%nat /\
  (dist_count D1 <= dist_count D3)%nat /\
  (dist_count D0 <= dist_count D4)%nat.
Proof.
  unfold dist_count, D0, D1, D3, D4. simpl. lia.
Qed.

Lemma L5_all_conserved : forall D K d,
  L5_preservation D ->
  has_dist (D K) d = true ->
  forall K', (K <= K')%nat ->
  has_dist (D K') d = true.
Proof.
  intros D K d HL5 Hd K' Hle.
  apply (distinction_permanent D K d HL5 Hd K' Hle).
Qed.

(** * Subset is Reflexive and Transitive *)

Lemma dist_subset_refl : forall D, dist_subset D D.
Proof. unfold dist_subset. auto. Qed.

Lemma dist_subset_trans : forall D1 D2 D3,
  dist_subset D1 D2 -> dist_subset D2 D3 -> dist_subset D1 D3.
Proof.
  unfold dist_subset. intros D1' D2' D3' H12 H23 d Hd.
  apply H23. apply H12. exact Hd.
Qed.

(** * L5 implies multi-step subset *)

Lemma L5_multi_step : forall D K1 K2,
  L5_preservation D ->
  (K1 <= K2)%nat ->
  dist_subset (D K1) (D K2).
Proof.
  intros D K1 K2 HL5 Hle.
  unfold dist_subset. intros d Hd.
  apply (distinction_permanent D K1 d HL5 Hd K2 Hle).
Qed.

(** * Empty set is subset of everything *)

Lemma empty_subset : forall D, dist_subset [] D.
Proof. unfold dist_subset, has_dist. intros D d H. simpl in H. discriminate. Qed.

(** * Count monotone under subset for concrete sets *)

Lemma count_chain :
  (dist_count D0 <= dist_count D1)%nat /\
  (dist_count D1 <= dist_count D2)%nat /\
  (dist_count D2 <= dist_count D3)%nat /\
  (dist_count D3 <= dist_count D4)%nat.
Proof.
  unfold dist_count, D0, D1, D2, D3, D4. simpl. lia.
Qed.
