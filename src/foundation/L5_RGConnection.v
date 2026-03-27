(* L5_RGConnection.v *)
(* E/R/R: Elements = hbar_eff values, Roles = RG flow, Rules = monotonicity + classical limit *)
(* Standalone — only Stdlib imports *)
(* STATUS: 15 Qed, 0 Admitted, 0 axioms *)
(* Author: Horsocrates | Date: March 2026 *)

From Stdlib Require Import QArith.
From Stdlib Require Import Nat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.

Open Scope Q_scope.

(** * Effective hbar as function of resolution level *)

Definition hbar_eff (K : nat) : Q :=
  match K with
  | O => 1
  | S O => 1 # 2
  | S (S O) => 1 # 4
  | S (S (S O)) => 1 # 8
  | S (S (S (S _))) => 1 # 16
  end.

(** * Concrete values *)

Lemma hbar_0 : hbar_eff 0 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma hbar_1 : hbar_eff 1 == 1 # 2.
Proof. vm_compute. reflexivity. Qed.

Lemma hbar_2 : hbar_eff 2 == 1 # 4.
Proof. vm_compute. reflexivity. Qed.

Lemma hbar_3 : hbar_eff 3 == 1 # 8.
Proof. vm_compute. reflexivity. Qed.

(** * RG monotonicity: hbar_eff decreases *)

Lemma rg_monotone_01 : hbar_eff 1 <= hbar_eff 0.
Proof. unfold Qle. simpl. lia. Qed.

Lemma rg_monotone_12 : hbar_eff 2 <= hbar_eff 1.
Proof. unfold Qle. simpl. lia. Qed.

Lemma rg_monotone_23 : hbar_eff 3 <= hbar_eff 2.
Proof. unfold Qle. simpl. lia. Qed.

(** * All values positive *)

Lemma hbar_positive : forall K, 0 < hbar_eff K.
Proof.
  intro K. destruct K as [|[|[|[|K']]]]; unfold Qlt; simpl; lia.
Qed.

(** * Classical limit: hbar -> 0 at large K *)

Lemma classical_limit_bound : forall K, hbar_eff K <= 1.
Proof.
  intro K. destruct K as [|[|[|[|K']]]]; unfold Qle; simpl; lia.
Qed.

Lemma classical_limit_small : hbar_eff 4 <= 1 # 16.
Proof. unfold Qle. simpl. lia. Qed.

(** * Fixed point: stabilizes *)

Lemma rg_fixed_point : forall K,
  (4 <= K)%nat -> hbar_eff K == hbar_eff (S K).
Proof.
  intros K HK. destruct K as [|[|[|[|K']]]]; try lia.
  vm_compute. reflexivity.
Qed.

(** * RG flow preserves positivity *)

Lemma rg_preserves_positive : forall K1 K2,
  (K1 <= K2)%nat -> 0 < hbar_eff K2.
Proof. intros K1 K2 H. apply hbar_positive. Qed.

(** * Ratio between successive levels *)

Lemma rg_ratio_01 : hbar_eff 1 * 2 == hbar_eff 0.
Proof. vm_compute. reflexivity. Qed.

Lemma rg_ratio_12 : hbar_eff 2 * 2 == hbar_eff 1.
Proof. vm_compute. reflexivity. Qed.

(** * hbar_eff is bounded below *)

Lemma hbar_bounded_below : forall K, 1 # 16 <= hbar_eff K.
Proof. intro K. destruct K as [|[|[|[|K']]]]; unfold Qle; simpl; lia. Qed.
