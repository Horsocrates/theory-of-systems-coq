(** * Distributions.v — Probability Distributions as ToS Systems

    Theory of Systems — Verified Standard Library (Batch 4)

    Elements: outcomes with associated probabilities
    Roles:    pmf -> Measure, mean -> Expectation, variance -> Spread
    Rules:    probabilities sum to 1, non-negative (constitution)
    Status:   valid_distribution | degenerate | undefined

    Connection: Probability.v (basic probability axioms)
    Connection: Combinatorics.v (binomial coefficients)

    STATUS: 23 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lqa.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Q_scope.
From ToS Require Import TheoryOfSystems_Core_ERR.

(* ================================================================= *)
(*           PART I: HELPER — Q POWERS (3 Qed)                       *)
(* ================================================================= *)

Fixpoint Qpow (q : Q) (n : nat) : Q :=
  match n with
  | O => 1
  | S m => q * Qpow q m
  end.

(** Qpow q 0 = 1 *)
Lemma Qpow_0 : forall q, Qpow q O = 1.
Proof. reflexivity. Qed.

(** Qpow q (S n) = q * Qpow q n *)
Lemma Qpow_succ : forall q n, Qpow q (S n) = q * Qpow q n.
Proof. reflexivity. Qed.

(** Qpow q 1 == q *)
Lemma Qpow_1 : forall q, Qpow q (S O) == q.
Proof. intros. simpl. ring. Qed.

(* ================================================================= *)
(*           PART II: BERNOULLI DISTRIBUTION (11 Qed)                 *)
(* ================================================================= *)

(** Bernoulli distribution: single trial with probability p *)
Record Bernoulli := mkBernoulli {
  bern_p : Q;
  bern_valid : 0 <= bern_p /\ bern_p <= 1;
}.

Definition bern_pmf (B : Bernoulli) (k : nat) : Q :=
  match k with
  | O => 1 - bern_p B
  | S O => bern_p B
  | _ => 0
  end.

Definition bern_mean (B : Bernoulli) : Q := bern_p B.

Definition bern_var (B : Bernoulli) : Q := bern_p B * (1 - bern_p B).

(** PMF at k=0 *)
Lemma bern_pmf_0 : forall B, bern_pmf B O = 1 - bern_p B.
Proof. reflexivity. Qed.

(** PMF at k=1 *)
Lemma bern_pmf_1 : forall B, bern_pmf B (S O) = bern_p B.
Proof. reflexivity. Qed.

(** PMF at k=2 *)
Lemma bern_pmf_2 : forall B, bern_pmf B (S (S O)) = 0.
Proof. reflexivity. Qed.

(** Mean definition *)
Lemma bern_mean_def : forall B, bern_mean B = bern_p B.
Proof. reflexivity. Qed.

(** Variance definition *)
Lemma bern_var_def : forall B, bern_var B = bern_p B * (1 - bern_p B).
Proof. reflexivity. Qed.

(** PMF sums to 1 over support {0, 1} *)
Lemma bern_pmf_sum : forall B, bern_pmf B O + bern_pmf B (S O) == 1.
Proof. intros. simpl. ring. Qed.

(** PMF non-negative at k=0 *)
Lemma bern_pmf_nonneg_0 : forall B, 0 <= bern_pmf B O.
Proof.
  intros. simpl. destruct (bern_valid B) as [H0 H1]. lra.
Qed.

(** PMF non-negative at k=1 *)
Lemma bern_pmf_nonneg_1 : forall B, 0 <= bern_pmf B (S O).
Proof.
  intros. simpl. destruct (bern_valid B) as [H0 H1]. lra.
Qed.

(** Variance is non-negative *)
Lemma bern_var_nonneg : forall B, 0 <= bern_var B.
Proof.
  intros. unfold bern_var.
  destruct (bern_valid B) as [H0 H1].
  apply Qmult_le_0_compat; lra.
Qed.

(** PMF at k >= 2 is 0 *)
Lemma bern_pmf_ge2 : forall B k, (k >= 2)%nat -> bern_pmf B k = 0.
Proof.
  intros B k Hk. destruct k as [|[|k']]; simpl; try lia; reflexivity.
Qed.

(** Mean equals sum of k * pmf(k) over support *)
Lemma bern_mean_is_expectation : forall B,
  0 * bern_pmf B O + 1 * bern_pmf B (S O) == bern_mean B.
Proof.
  intros. unfold bern_mean. simpl. ring.
Qed.

(* ================================================================= *)
(*           PART III: GEOMETRIC DISTRIBUTION (3 Qed)                 *)
(* ================================================================= *)

(** Geometric distribution: number of failures before first success *)
Record Geometric := mkGeometric {
  geom_p : Q;
  geom_valid : 0 < geom_p /\ geom_p <= 1;
}.

(** geom_pmf k = p * (1-p)^k *)
Definition geom_pmf (G : Geometric) (k : nat) : Q :=
  geom_p G * Qpow (1 - geom_p G) k.

(** PMF at k=0 *)
Lemma geom_pmf_0 : forall G, geom_pmf G O == geom_p G.
Proof. intros. unfold geom_pmf. simpl. ring. Qed.

(** PMF non-negative at k=0 *)
Lemma geom_pmf_nonneg_0 : forall G, 0 <= geom_pmf G O.
Proof.
  intros. unfold geom_pmf. simpl.
  destruct (geom_valid G) as [H0 H1].
  lra.
Qed.

(** Recurrence: geom_pmf G (S k) == (1 - geom_p G) * geom_pmf G k *)
Lemma geom_pmf_succ : forall G k,
  geom_pmf G (S k) == (1 - geom_p G) * geom_pmf G k.
Proof.
  intros. unfold geom_pmf. simpl. ring.
Qed.

(* ================================================================= *)
(*           PART IV: CDF FROM PMF (2 Qed)                           *)
(* ================================================================= *)

(** CDF: sum pmf(0) + ... + pmf(k) *)
Fixpoint cdf_from_pmf (pmf : nat -> Q) (k : nat) : Q :=
  match k with
  | O => pmf O
  | S m => cdf_from_pmf pmf m + pmf (S m)
  end.

(** CDF at k=0 *)
Lemma cdf_0 : forall pmf, cdf_from_pmf pmf O = pmf O.
Proof. reflexivity. Qed.

(** CDF recursive step *)
Lemma cdf_succ : forall pmf k,
  cdf_from_pmf pmf (S k) = cdf_from_pmf pmf k + pmf (S k).
Proof. reflexivity. Qed.

(* ================================================================= *)
(*           PART V: BERNOULLI CDF (2 Qed)                           *)
(* ================================================================= *)

(** Bernoulli CDF at 0 *)
Lemma bern_cdf_0 : forall B, cdf_from_pmf (bern_pmf B) O = 1 - bern_p B.
Proof. reflexivity. Qed.

(** Bernoulli CDF at 1 reaches 1 *)
Lemma bern_cdf_1 : forall B, cdf_from_pmf (bern_pmf B) (S O) == 1.
Proof. intros. simpl. ring. Qed.

(* ================================================================= *)
(*           PART VI: QPOW PROPERTIES (2 Qed)                        *)
(* ================================================================= *)

(** Qpow of non-negative base is non-negative *)
Lemma Qpow_nonneg : forall q n, 0 <= q -> 0 <= Qpow q n.
Proof.
  intros q n Hq. induction n as [|n' IH].
  - simpl. lra.
  - simpl. apply Qmult_le_0_compat; assumption.
Qed.

(** Qpow distributes: Qpow q (S n) == q * Qpow q n (as Qeq) *)
Lemma Qpow_succ_eq : forall q n, Qpow q (S n) == q * Qpow q n.
Proof. intros. simpl. reflexivity. Qed.

(* ================================================================= *)
(*  TOTAL: 23 Qed, 0 Admitted, 0 axioms                              *)
(* ================================================================= *)
