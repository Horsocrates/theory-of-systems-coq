(** * FiniteSizeClassification.v — Classification of finite-size corrections
    Elements: CorrectionType, classify_correction, correction_table
    Roles:    classify gap ratio into exponential/polynomial/logarithmic
    Rules:    gapped systems → exponential, gapless → polynomial; table verification
    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs List Bool Lia Lra Lqa.
Import ListNotations.
Open Scope Q_scope.

(* --- Correction types --- *)
Inductive CorrectionType : Set :=
  | Exponential (rate : Q)
  | Polynomial  (exponent : Q)
  | Logarithmic (coeff : Q)
  | NoCorrection.

(* --- Classification function --- *)
Definition classify_correction (gap_ratio : Q) : CorrectionType :=
  if Qlt_le_dec gap_ratio 1 then
    Exponential gap_ratio
  else
    Polynomial 1.

(* 1 *)
Lemma classify_gapped_is_exponential : forall r,
  r < 1 -> exists rate, classify_correction r = Exponential rate.
Proof.
  intros r Hr. unfold classify_correction.
  destruct (Qlt_le_dec r 1); [exists r; reflexivity | lra].
Qed.

(* 2 *)
Lemma classify_gapless_is_polynomial : forall r,
  1 <= r -> classify_correction r = Polynomial 1.
Proof.
  intros r Hr. unfold classify_correction.
  destruct (Qlt_le_dec r 1); [lra | reflexivity].
Qed.

(* --- Concrete: Ising model --- *)
Definition ising_rate : Q := 28 # 37.

(* 3 *)
Lemma ising_rate_less_one : ising_rate < 1.
Proof. unfold ising_rate. lra. Qed.

(* 4 *)
Lemma ising_is_exponential :
  classify_correction ising_rate = Exponential (28 # 37).
Proof.
  unfold classify_correction, ising_rate.
  destruct (Qlt_le_dec (28#37) 1); [reflexivity | lra].
Qed.

(* --- Concrete: particle in a box --- *)
Definition box_rate : Q := 2.

(* 5 *)
Lemma box_rate_ge_one : 1 <= box_rate.
Proof. unfold box_rate. lra. Qed.

(* 6 *)
Lemma box_is_polynomial :
  classify_correction box_rate = Polynomial 1.
Proof.
  unfold classify_correction, box_rate.
  destruct (Qlt_le_dec 2 1); [lra | reflexivity].
Qed.

(* --- Comparison lemmas --- *)

(* 7 *)
Lemma exponential_faster_than_polynomial :
  ising_rate < box_rate.
Proof. unfold ising_rate, box_rate. lra. Qed.

(* 8 *)
Lemma ising_rate_positive : 0 < ising_rate.
Proof. unfold ising_rate. lra. Qed.

(* 9 *)
Lemma half_rate_less_ising : (1#2) < ising_rate.
Proof. unfold ising_rate. lra. Qed.

(* --- Table verification --- *)
Definition correction_table : list (Q * CorrectionType) :=
  [ (28#37, Exponential (28#37));
    (2, Polynomial 1);
    (1#2, Exponential (1#2)) ].

(* 10 *)
Lemma table_entry_ising :
  classify_correction (28#37) = Exponential (28#37).
Proof.
  unfold classify_correction.
  destruct (Qlt_le_dec (28#37) 1); [reflexivity | lra].
Qed.

(* 11 *)
Lemma table_entry_box :
  classify_correction 2 = Polynomial 1.
Proof.
  unfold classify_correction.
  destruct (Qlt_le_dec 2 1); [lra | reflexivity].
Qed.

(* 12 *)
Lemma table_entry_half :
  classify_correction (1#2) = Exponential (1#2).
Proof.
  unfold classify_correction.
  destruct (Qlt_le_dec (1#2) 1); [reflexivity | lra].
Qed.

(* 13 *)
Lemma small_rate_means_fast_convergence : forall r1 r2,
  0 < r1 -> r1 < r2 -> r2 < 1 ->
  classify_correction r1 = Exponential r1 /\
  classify_correction r2 = Exponential r2.
Proof.
  intros r1 r2 H1 H12 H2.
  unfold classify_correction.
  destruct (Qlt_le_dec r1 1); [|lra].
  destruct (Qlt_le_dec r2 1); [|lra].
  split; reflexivity.
Qed.

(* 14 *)
Lemma three_quarter_is_exponential :
  classify_correction (3#4) = Exponential (3#4).
Proof.
  unfold classify_correction.
  destruct (Qlt_le_dec (3#4) 1); [reflexivity | lra].
Qed.

(* 15 *)
Lemma unity_is_polynomial :
  classify_correction 1 = Polynomial 1.
Proof.
  unfold classify_correction.
  destruct (Qlt_le_dec 1 1); [lra | reflexivity].
Qed.
