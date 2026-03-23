(** * BandGap.v — Band Gap from Perturbation
    Elements: Band gap formula, Qabs handling, concrete gaps
    Roles:    Connect perturbation strength to spectral gap size
    Rules:    gap(delta) = 4|delta|; gap(0) = 0, gap(1/4) = 1
    Status:   Stdlib
    STATUS: 8 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ================================================================== *)
(*  BAND GAP FORMULA                                                   *)
(*  For a 2-band model with alternating potential ±delta:              *)
(*  gap = 4 |delta|                                                    *)
(* ================================================================== *)

Definition band_gap (delta : Q) : Q := 4 * Qabs delta.

(* ================================================================== *)
(*  Qabs for positive values                                          *)
(* ================================================================== *)

Lemma qabs_quarter : Qabs (1#4) == 1#4.
Proof.
  unfold Qabs. simpl. reflexivity.
Qed.

Lemma qabs_half : Qabs (1#2) == 1#2.
Proof.
  unfold Qabs. simpl. reflexivity.
Qed.

Lemma qabs_neg_quarter : Qabs (-(1#4)) == 1#4.
Proof.
  unfold Qabs. simpl. reflexivity.
Qed.

(* ================================================================== *)
(*  CONCRETE GAP VALUES                                                *)
(* ================================================================== *)

Lemma gap_zero : band_gap 0 == 0.
Proof. unfold band_gap, Qabs. simpl. ring. Qed.

Lemma gap_quarter : band_gap (1#4) == 1.
Proof.
  unfold band_gap.
  assert (H : Qabs (1#4) == 1#4) by (unfold Qabs; simpl; reflexivity).
  rewrite H. ring.
Qed.

Lemma gap_half : band_gap (1#2) == 2.
Proof.
  unfold band_gap.
  assert (H : Qabs (1#2) == 1#2) by (unfold Qabs; simpl; reflexivity).
  rewrite H. ring.
Qed.

(* Negative delta gives same gap (symmetry) *)
Lemma gap_neg_quarter : band_gap (-(1#4)) == 1.
Proof.
  unfold band_gap.
  assert (H : Qabs (-(1#4)) == 1#4) by (unfold Qabs; simpl; reflexivity).
  rewrite H. ring.
Qed.

Theorem band_gap_synthesis :
  band_gap 0 == 0 /\
  band_gap (1#4) == 1 /\
  band_gap (1#2) == 2 /\
  band_gap (-(1#4)) == 1.
Proof.
  split; [exact gap_zero|].
  split; [exact gap_quarter|].
  split; [exact gap_half|].
  exact gap_neg_quarter.
Qed.
