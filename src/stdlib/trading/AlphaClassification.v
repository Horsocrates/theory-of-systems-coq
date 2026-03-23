(** * AlphaClassification.v — Classification of alpha types
    Elements: AlphaType inductive, classify_alpha, decay thresholds;
    Roles:    categorize alpha sources by decay rate;
    Rules:    structural (slow), informational (medium), statistical (fast).
    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs List Bool Lia Lra Lqa.
Open Scope Q_scope.

(* ===== Alpha type classification ===== *)

Inductive AlphaType := Structural | Informational | Statistical.

(* ===== Classify by decay rate ===== *)
(* decay < 1/10: Structural (slow decay = durable alpha)
   decay < 1/2:  Informational (medium)
   else:         Statistical (fast decay = fleeting) *)

Definition classify_alpha (decay : Q) : AlphaType :=
  if Qlt_le_dec decay (1#10) then Structural
  else if Qlt_le_dec decay (1#2) then Informational
  else Statistical.

(* ===== Concrete classification ===== *)

Lemma classify_structural : classify_alpha (1#20) = Structural.
Proof.
  unfold classify_alpha.
  destruct (Qlt_le_dec (1#20) (1#10)); try lra; reflexivity.
Qed.

Lemma classify_informational : classify_alpha (1#5) = Informational.
Proof.
  unfold classify_alpha.
  destruct (Qlt_le_dec (1#5) (1#10)); try lra.
  destruct (Qlt_le_dec (1#5) (1#2)); try lra; reflexivity.
Qed.

Lemma classify_statistical : classify_alpha (3#5) = Statistical.
Proof.
  unfold classify_alpha.
  destruct (Qlt_le_dec (3#5) (1#10)); try lra.
  destruct (Qlt_le_dec (3#5) (1#2)); try lra; reflexivity.
Qed.

(* ===== Boundary cases ===== *)

Lemma classify_zero : classify_alpha 0 = Structural.
Proof.
  unfold classify_alpha.
  destruct (Qlt_le_dec 0 (1#10)); try lra; reflexivity.
Qed.

Lemma classify_one : classify_alpha 1 = Statistical.
Proof.
  unfold classify_alpha.
  destruct (Qlt_le_dec 1 (1#10)); try lra.
  destruct (Qlt_le_dec 1 (1#2)); try lra; reflexivity.
Qed.

Lemma classify_half : classify_alpha (1#2) = Statistical.
Proof.
  unfold classify_alpha.
  destruct (Qlt_le_dec (1#2) (1#10)); try lra.
  destruct (Qlt_le_dec (1#2) (1#2)); try lra; reflexivity.
Qed.

(* ===== AlphaType decidable equality ===== *)

Definition alpha_type_eqb (a b : AlphaType) : bool :=
  match a, b with
  | Structural, Structural => true
  | Informational, Informational => true
  | Statistical, Statistical => true
  | _, _ => false
  end.

Lemma alpha_type_eqb_refl : forall a, alpha_type_eqb a a = true.
Proof. destruct a; reflexivity. Qed.

Lemma alpha_type_eqb_correct : forall a b,
  alpha_type_eqb a b = true -> a = b.
Proof. destruct a, b; simpl; intros; try discriminate; reflexivity. Qed.

(* ===== Structural is the most durable ===== *)

Lemma structural_low_decay : forall d,
  d < 1#10 -> classify_alpha d = Structural.
Proof.
  intros d Hd. unfold classify_alpha.
  destruct (Qlt_le_dec d (1#10)); try lra; reflexivity.
Qed.

(* ===== Statistical is the fastest decaying ===== *)

Lemma statistical_high_decay : forall d,
  1#2 <= d -> classify_alpha d = Statistical.
Proof.
  intros d Hd. unfold classify_alpha.
  destruct (Qlt_le_dec d (1#10)); try lra.
  destruct (Qlt_le_dec d (1#2)); try lra; reflexivity.
Qed.

(* ===== Synthesis ===== *)

Theorem alpha_classification_synthesis :
  classify_alpha (1#20) = Structural /\
  classify_alpha (1#5) = Informational /\
  classify_alpha (3#5) = Statistical /\
  (forall d, d < 1#10 -> classify_alpha d = Structural) /\
  (forall d, 1#2 <= d -> classify_alpha d = Statistical).
Proof.
  split; [exact classify_structural|].
  split; [exact classify_informational|].
  split; [exact classify_statistical|].
  split; [exact structural_low_decay|].
  exact statistical_high_decay.
Qed.
