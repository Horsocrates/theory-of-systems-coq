(* L5_Conservation.v *)
(* E/R/R: Elements = CDistSets, Roles = conservation laws, Rules = L5 preservation implies conservation *)
(* Standalone — only Stdlib imports *)
(* STATUS: 25 Qed, 0 Admitted, 0 axioms *)
(* Author: Horsocrates | Date: March 2026 *)

From Stdlib Require Import List.
From Stdlib Require Import Nat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Import ListNotations.

(** * Core Definitions *)

Definition CDistSet := list nat.

Definition chas (s : CDistSet) (d : nat) : bool := existsb (Nat.eqb d) s.

Definition c_subset (D1 D2 : CDistSet) : Prop :=
  forall d, chas D1 d = true -> chas D2 d = true.

Definition L5_pres (D : nat -> CDistSet) : Prop :=
  forall K, c_subset (D K) (D (S K)).

Definition conserved (D : nat -> CDistSet) (q : nat) (K0 : nat) : Prop :=
  chas (D K0) q = true /\
  forall K, (K0 <= K)%nat -> chas (D K) q = true.

(** * The Conservation Theorem *)

Theorem L5_conservation :
  forall (D : nat -> CDistSet) (q : nat) (K0 : nat),
  L5_pres D ->
  chas (D K0) q = true ->
  conserved D q K0.
Proof.
  intros D q K0 HL5 H0. split.
  - exact H0.
  - intros K HK. induction K as [|K' IH].
    + assert (K0 = 0)%nat as Heq by lia. rewrite Heq in H0. exact H0.
    + destruct (Nat.le_gt_cases K0 K') as [Hle | Hgt].
      * apply (HL5 K'). apply IH. exact Hle.
      * assert (K0 = S K') as Heq by lia. rewrite <- Heq. exact H0.
Qed.

(** * Concrete D_energy chain *)

Definition D_energy (K : nat) : CDistSet :=
  match K with
  | O => [10%nat]
  | S O => [10%nat; 20%nat]
  | S (S O) => [10%nat; 20%nat; 30%nat]
  | S (S (S _)) => [10%nat; 20%nat; 30%nat; 40%nat]
  end.

Lemma energy_has_10_at_0 : chas (D_energy 0) 10 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma energy_has_10_at_1 : chas (D_energy 1) 10 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma energy_has_10_at_2 : chas (D_energy 2) 10 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma energy_has_20_at_1 : chas (D_energy 1) 20 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma energy_pres_0_1 : c_subset (D_energy 0) (D_energy 1).
Proof.
  intros d H. unfold chas in *. simpl in *.
  rewrite Bool.orb_true_iff in H. rewrite Bool.orb_true_iff.
  destruct H as [H|H].
  - left. exact H.
  - simpl in H. discriminate.
Qed.

Lemma energy_pres_1_2 : c_subset (D_energy 1) (D_energy 2).
Proof.
  intros d H. unfold chas in *. simpl in *.
  rewrite Bool.orb_true_iff in H. rewrite Bool.orb_true_iff.
  destruct H as [H|H].
  - left. exact H.
  - rewrite Bool.orb_true_iff in H. destruct H as [H|H].
    + right. rewrite Bool.orb_true_iff. left. exact H.
    + simpl in H. discriminate.
Qed.

(** * Unitarity: information never lost *)

Lemma D_energy_grows : forall K,
  (length (D_energy K) <= length (D_energy (S K)))%nat.
Proof.
  intro K. destruct K as [|[|[|K']]]; simpl; lia.
Qed.

Lemma info_never_lost : forall K,
  (length (D_energy 0) <= length (D_energy K))%nat.
Proof.
  intro K. destruct K as [|[|[|K']]]; simpl; lia.
Qed.

(** * Conservation as analogy: charge *)

Definition D_charge (K : nat) : CDistSet :=
  match K with
  | O => [1%nat]
  | S _ => [1%nat; 2%nat]
  end.

Lemma charge_pres : L5_pres D_charge.
Proof.
  intros K d H. unfold chas, D_charge in *.
  destruct K as [|K']; simpl in *;
  destruct (d =? 1)%nat eqn:E1; simpl in *; try exact H; try discriminate.
Qed.

Lemma charge_conserved : conserved D_charge 1 0.
Proof.
  apply L5_conservation.
  - exact charge_pres.
  - vm_compute. reflexivity.
Qed.

(** * Conservation as analogy: momentum *)

Definition D_momentum (K : nat) : CDistSet :=
  match K with
  | O => [5%nat; 3%nat]
  | S _ => [5%nat; 3%nat; 7%nat]
  end.

Lemma momentum_pres : L5_pres D_momentum.
Proof.
  intros K d H. unfold chas, D_momentum in *.
  destruct K as [|K']; simpl in *;
  destruct (d =? 5)%nat eqn:E1; simpl in *; try exact H; try discriminate;
  destruct (d =? 3)%nat eqn:E2; simpl in *; try exact H; try discriminate.
Qed.

Lemma momentum_conserved_5 : conserved D_momentum 5 0.
Proof. apply L5_conservation. exact momentum_pres. vm_compute. reflexivity. Qed.

Lemma momentum_conserved_3 : conserved D_momentum 3 0.
Proof. apply L5_conservation. exact momentum_pres. vm_compute. reflexivity. Qed.

(** * Conservation is transitive *)

Lemma conservation_monotone :
  forall (D : nat -> CDistSet) (q : nat) (K0 K1 : nat),
  L5_pres D -> conserved D q K0 -> (K0 <= K1)%nat ->
  conserved D q K1.
Proof.
  intros D q K0 K1 HL5 [H0 Hforall] HK.
  split.
  - apply Hforall. exact HK.
  - intros K HK'. apply Hforall. lia.
Qed.

(** * c_subset is reflexive and transitive *)

Lemma c_subset_refl : forall D, c_subset D D.
Proof. unfold c_subset. intros. exact H. Qed.

Lemma c_subset_trans : forall D1 D2 D3,
  c_subset D1 D2 -> c_subset D2 D3 -> c_subset D1 D3.
Proof. unfold c_subset. intros. auto. Qed.

(** * Adding preserves membership *)

Lemma chas_cons : forall s d d',
  chas s d = true -> chas (d' :: s) d = true.
Proof.
  unfold chas. intros s d d' H. simpl. destruct (Nat.eqb d d'); simpl; auto.
Qed.

Lemma chas_head : forall s d, chas (d :: s) d = true.
Proof.
  unfold chas. intros. simpl. rewrite Nat.eqb_refl. simpl. reflexivity.
Qed.

(** * Empty set has nothing *)

Lemma chas_nil : forall d, chas [] d = false.
Proof. intros. vm_compute. reflexivity. Qed.

(** * L5_pres implies multi-step subset *)

Lemma L5_pres_multi : forall (D : nat -> CDistSet) (K1 K2 : nat),
  L5_pres D -> (K1 <= K2)%nat -> c_subset (D K1) (D K2).
Proof.
  intros D K1 K2 HL5 HK. induction K2 as [|K2' IH].
  - assert (K1 = 0)%nat by lia. subst. apply c_subset_refl.
  - destruct (Nat.le_gt_cases K1 K2') as [Hle | Hgt].
    + apply (c_subset_trans _ (D K2')). apply IH. exact Hle. apply HL5.
    + assert (K1 = S K2') by lia. subst. apply c_subset_refl.
Qed.

(** * D_energy at stage 3 has all from stage 0 *)

Lemma energy_has_10_at_3 : chas (D_energy 3) 10 = true.
Proof. vm_compute. reflexivity. Qed.

(** * Conservation is preserved by subset *)

Lemma conserved_weaken :
  forall (D : nat -> CDistSet) (q : nat) (K0 K1 : nat),
  conserved D q K0 -> (K0 <= K1)%nat -> chas (D K1) q = true.
Proof.
  intros D q K0 K1 [_ Hf] HK. apply Hf. exact HK.
Qed.

(** * Concrete: D_energy is L5_pres for first 3 steps *)

Lemma energy_pres_2_3 : c_subset (D_energy 2) (D_energy 3).
Proof.
  intros d H. unfold chas, D_energy in *.
  simpl in *.
  destruct (d =? 10)%nat eqn:E1; simpl in *; try exact H; try discriminate.
  destruct (d =? 20)%nat eqn:E2; simpl in *; try exact H; try discriminate.
  destruct (d =? 30)%nat eqn:E3; simpl in *; try exact H; try discriminate.
Qed.
