(** CorrMatrix.v — Correlation matrix computations for market data.
    E/R/R: Elements = returns, correlation entries;
           Roles = mean, variance, covariance, stress;
           Rules = stress classification thresholds. *)

From Stdlib Require Import QArith QArith.Qabs Lia Lra List.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================ *)
(* Core definitions                                                  *)
(* ================================================================ *)

Definition sum_Q (xs : list Q) : Q :=
  fold_left Qplus xs 0.

Definition mean_return (returns : list Q) : Q :=
  sum_Q returns / inject_Z (Z.of_nat (length returns)).

Definition sq_dev (mu : Q) (x : Q) : Q :=
  (x - mu) * (x - mu).

Definition variance (returns : list Q) : Q :=
  let mu := mean_return returns in
  fold_left Qplus (map (sq_dev mu) returns) 0
    / inject_Z (Z.of_nat (length returns)).

Definition cross_dev (mu1 mu2 : Q) (xy : Q * Q) : Q :=
  (fst xy - mu1) * (snd xy - mu2).

Definition covariance (r1 r2 : list Q) : Q :=
  let mu1 := mean_return r1 in
  let mu2 := mean_return r2 in
  fold_left Qplus (map (cross_dev mu1 mu2) (combine r1 r2)) 0
    / inject_Z (Z.of_nat (length r1)).

Definition stress_index (trC2 : Q) (K : nat) : Q :=
  trC2 / inject_Z (Z.of_nat (K * K)).

Definition stress_level (s : Q) : nat :=
  if Qlt_le_dec s (1#5) then O
  else if Qlt_le_dec s (2#5) then S O
  else if Qlt_le_dec s (7#10) then S (S O)
  else S (S (S O)).

Definition correlation (r1 r2 : list Q) : Q :=
  let v1 := variance r1 in
  let v2 := variance r2 in
  covariance r1 r2 / (v1 * v2).

(* ================================================================ *)
(* Concrete example: 3 assets, 4 periods                            *)
(* ================================================================ *)

Definition example_r1 : list Q := [1; -(1); 1; -(1)].
Definition example_r2 : list Q := [1; -(1); 1; -(1)].
Definition example_r3 : list Q := [1; 1; -(1); -(1)].

(* Mean lemmas *)
Lemma mean_r1 : mean_return example_r1 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma mean_r2 : mean_return example_r2 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma mean_r3 : mean_return example_r3 == 0.
Proof. vm_compute. reflexivity. Qed.

(* Variance lemmas *)
Lemma var_r1 : variance example_r1 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma var_r2 : variance example_r2 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma var_r3 : variance example_r3 == 1.
Proof. vm_compute. reflexivity. Qed.

(* Covariance lemmas *)
Lemma cov_12 : covariance example_r1 example_r2 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma cov_13 : covariance example_r1 example_r3 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma cov_23 : covariance example_r2 example_r3 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma cov_11 : covariance example_r1 example_r1 == variance example_r1.
Proof. vm_compute. reflexivity. Qed.

Lemma cov_22 : covariance example_r2 example_r2 == variance example_r2.
Proof. vm_compute. reflexivity. Qed.

Lemma cov_33 : covariance example_r3 example_r3 == variance example_r3.
Proof. vm_compute. reflexivity. Qed.

(* Stress index *)
Lemma stress_example : stress_index 5 3 == 5#9.
Proof. vm_compute. reflexivity. Qed.

Lemma stress_level_example : stress_level (5#9) = S (S O).
Proof.
  unfold stress_level.
  destruct (Qlt_le_dec (5#9) (1#5)) as [H1|H1].
  - exfalso. unfold Qlt in H1. simpl in H1. lia.
  - destruct (Qlt_le_dec (5#9) (2#5)) as [H2|H2].
    + exfalso. unfold Qlt in H2. simpl in H2. lia.
    + destruct (Qlt_le_dec (5#9) (7#10)) as [H3|H3]. reflexivity.
      exfalso. unfold Qle in H3. simpl in H3. lia.
Qed.

Lemma stress_low : stress_level (1#10) = O.
Proof.
  unfold stress_level.
  destruct (Qlt_le_dec (1#10) (1#5)) as [H1|H1]. reflexivity.
  exfalso. unfold Qle in H1. simpl in H1. lia.
Qed.

Lemma stress_medium : stress_level (3#10) = S O.
Proof.
  unfold stress_level.
  destruct (Qlt_le_dec (3#10) (1#5)) as [H1|H1].
  - exfalso. unfold Qlt in H1. simpl in H1. lia.
  - destruct (Qlt_le_dec (3#10) (2#5)) as [H2|H2]. reflexivity.
    exfalso. unfold Qle in H2. simpl in H2. lia.
Qed.

Lemma stress_high : stress_level (4#5) = S (S (S O)).
Proof.
  unfold stress_level.
  destruct (Qlt_le_dec (4#5) (1#5)) as [H1|H1].
  - exfalso. unfold Qlt in H1. simpl in H1. lia.
  - destruct (Qlt_le_dec (4#5) (2#5)) as [H2|H2].
    + exfalso. unfold Qlt in H2. simpl in H2. lia.
    + destruct (Qlt_le_dec (4#5) (7#10)) as [H3|H3].
      * exfalso. unfold Qlt in H3. simpl in H3. lia.
      * reflexivity.
Qed.

(* Correlation *)
Lemma corr_12 : correlation example_r1 example_r2 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma corr_13 : correlation example_r1 example_r3 == 0.
Proof. vm_compute. reflexivity. Qed.

(* Additional: sum_Q *)
Lemma sum_r1 : sum_Q example_r1 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma sum_r3 : sum_Q example_r3 == 0.
Proof. vm_compute. reflexivity. Qed.

(* Stress index bounds *)
Lemma stress_index_unit : stress_index 1 1 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma stress_index_two : stress_index 4 2 == 1.
Proof. vm_compute. reflexivity. Qed.

(* Mean of empty-like *)
Definition single_return : list Q := [5].

Lemma mean_single : mean_return single_return == 5.
Proof. vm_compute. reflexivity. Qed.

Lemma var_single : variance single_return == 0.
Proof. vm_compute. reflexivity. Qed.
