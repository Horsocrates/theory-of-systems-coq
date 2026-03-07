(** * InformationTheory.v — Information Theory as ToS System

    Theory of Systems — Verified Standard Library (Batch 4)

    Elements: probability distributions, information measures
    Roles:    entropy -> Uncertainty, mutual_info -> Shared Information
    Rules:    non-negativity, chain rules (constitution = information axioms)
    Status:   deterministic | uncertain | maximal_entropy

    STATUS: 20 Qed, 0 Admitted, 0 axioms
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

(* ========================================================================= *)
(* SECTION: INFORMATION THEORY — Parameterized by log function               *)
(* ========================================================================= *)

Section InformationTheory.

(** We parameterize by an abstract log function on Q, avoiding axioms.
    After End Section, all theorems become universally quantified over
    any log_Q satisfying these properties. *)

Variable log_Q : Q -> Q.

(** log(1) = 0 — no information in a certain event *)
Hypothesis log_1 : log_Q 1 == 0.

(** log is non-negative for inputs >= 1 *)
Hypothesis log_nonneg : forall x, 1 <= x -> 0 <= log_Q x.

(** log is monotone on positive reals *)
Hypothesis log_mono : forall a b, 0 < a -> a <= b -> log_Q a <= log_Q b.

(** log respects Q equality *)
Hypothesis log_proper : forall a b, a == b -> log_Q a == log_Q b.

(* ========================================================================= *)
(* CORE DEFINITIONS                                                          *)
(* ========================================================================= *)

(** Information content (self-information / surprisal) of a probability *)
Definition info_content (p : Q) : Q := - log_Q p.

(** Entropy of a finite distribution (recursive sum) *)
Fixpoint entropy_sum (probs : list Q) : Q :=
  match probs with
  | [] => 0
  | p :: rest => (- p * log_Q p) + entropy_sum rest
  end.

(** Joint entropy — entropy of the joint distribution *)
Definition joint_entropy (joint_probs : list Q) : Q :=
  entropy_sum joint_probs.

(** Conditional entropy: H(Y|X) = H(X,Y) - H(X) *)
Definition cond_entropy (h_joint h_x : Q) : Q := h_joint - h_x.

(** Mutual information: I(X;Y) = H(X) + H(Y) - H(X,Y) *)
Definition mutual_info (h_x h_y h_joint : Q) : Q := h_x + h_y - h_joint.

(** KL divergence: D_KL(P || Q) = sum p_i * (log p_i - log q_i) *)
Fixpoint kl_divergence (p q : list Q) : Q :=
  match p, q with
  | pi :: ps, qi :: qs => pi * (log_Q pi - log_Q qi) + kl_divergence ps qs
  | _, _ => 0
  end.

(** Cross entropy: H(P, Q) = - sum p_i * log q_i *)
Fixpoint cross_entropy (p q : list Q) : Q :=
  match p, q with
  | pi :: ps, qi :: qs => (- pi * log_Q qi) + cross_entropy ps qs
  | _, _ => 0
  end.

(** Redundancy: R = H_max - H, where H_max = log(n) for n outcomes *)
Definition redundancy (h_max h_actual : Q) : Q := h_max - h_actual.

(** Efficiency: eta = H / H_max *)
Definition efficiency (h h_max : Q) : Q := h / h_max.

(* ========================================================================= *)
(* PART I: STRUCTURAL / COMPUTATIONAL LEMMAS                                 *)
(* ========================================================================= *)

(** 1. Entropy of empty distribution is 0 *)
Lemma entropy_sum_nil : entropy_sum [] == 0.
Proof. reflexivity. Qed.

(** 2. Entropy cons unfolding *)
Lemma entropy_sum_cons : forall p rest,
  entropy_sum (p :: rest) == (- p * log_Q p) + entropy_sum rest.
Proof. intros. simpl. ring. Qed.

(** 3. Entropy of a singleton distribution *)
Lemma entropy_sum_singleton : forall p,
  entropy_sum [p] == - p * log_Q p.
Proof. intros. simpl. ring. Qed.

(** 4. KL divergence of empty lists is 0 *)
Lemma kl_divergence_nil : kl_divergence [] [] == 0.
Proof. reflexivity. Qed.

(** 5. KL divergence cons unfolding *)
Lemma kl_divergence_cons : forall pi qi ps qs,
  kl_divergence (pi :: ps) (qi :: qs) ==
  pi * (log_Q pi - log_Q qi) + kl_divergence ps qs.
Proof. intros. simpl. ring. Qed.

(** 6. Cross entropy of empty lists is 0 *)
Lemma cross_entropy_nil : cross_entropy [] [] == 0.
Proof. reflexivity. Qed.

(** 7. Cross entropy cons unfolding *)
Lemma cross_entropy_cons : forall pi qi ps qs,
  cross_entropy (pi :: ps) (qi :: qs) ==
  (- pi * log_Q qi) + cross_entropy ps qs.
Proof. intros. simpl. ring. Qed.

(** 8. Mutual information is symmetric in X and Y *)
Lemma mutual_info_symmetric : forall h_x h_y h_joint,
  mutual_info h_x h_y h_joint == mutual_info h_y h_x h_joint.
Proof. intros. unfold mutual_info. ring. Qed.

(** 9. Mutual information definitional *)
Lemma mutual_info_def : forall h_x h_y h_joint,
  mutual_info h_x h_y h_joint == h_x + h_y - h_joint.
Proof. intros. unfold mutual_info. ring. Qed.

(** 10. Conditional entropy definitional *)
Lemma cond_entropy_def : forall h_joint h_x,
  cond_entropy h_joint h_x == h_joint - h_x.
Proof. intros. unfold cond_entropy. ring. Qed.

(** 11. Information content of a certain event is 0 *)
Lemma info_content_certain : info_content 1 == 0.
Proof.
  unfold info_content.
  assert (Heq : log_Q 1 == 0) by exact log_1.
  rewrite Heq. ring.
Qed.

(** 12. Information content definitional *)
Lemma info_content_def : forall p,
  info_content p == - log_Q p.
Proof. intros. unfold info_content. ring. Qed.

(* ========================================================================= *)
(* PART II: INDUCTIVE PROPERTIES                                             *)
(* ========================================================================= *)

(** 13. KL divergence of a distribution with itself is 0 *)
Lemma kl_divergence_self_zero : forall l,
  kl_divergence l l == 0.
Proof.
  induction l as [| p rest IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. ring.
Qed.

(** 14. Cross entropy of P with itself equals entropy *)
Lemma cross_entropy_self_eq_entropy : forall l,
  cross_entropy l l == entropy_sum l.
Proof.
  induction l as [| p rest IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. ring.
Qed.

(** 15. Entropy distributes over append *)
Lemma entropy_sum_app : forall l1 l2,
  entropy_sum (l1 ++ l2) == entropy_sum l1 + entropy_sum l2.
Proof.
  induction l1 as [| p rest IH]; intros l2.
  - simpl. ring.
  - simpl. rewrite IH. ring.
Qed.

(** 16. KL divergence distributes over append (when lists are same length) *)
Lemma kl_divergence_app : forall p1 q1 p2 q2,
  length p1 = length q1 ->
  kl_divergence (p1 ++ p2) (q1 ++ q2) ==
  kl_divergence p1 q1 + kl_divergence p2 q2.
Proof.
  induction p1 as [| pi ps IH]; intros q1 p2 q2 Hlen.
  - destruct q1 as [| qi qs].
    + simpl. ring.
    + simpl in Hlen. discriminate.
  - destruct q1 as [| qi qs].
    + simpl in Hlen. discriminate.
    + simpl. simpl in Hlen. inversion Hlen as [Hlen'].
      rewrite IH by exact Hlen'. ring.
Qed.

(** 17. Cross entropy distributes over append (when lists are same length) *)
Lemma cross_entropy_app : forall p1 q1 p2 q2,
  length p1 = length q1 ->
  cross_entropy (p1 ++ p2) (q1 ++ q2) ==
  cross_entropy p1 q1 + cross_entropy p2 q2.
Proof.
  induction p1 as [| pi ps IH]; intros q1 p2 q2 Hlen.
  - destruct q1 as [| qi qs].
    + simpl. ring.
    + simpl in Hlen. discriminate.
  - destruct q1 as [| qi qs].
    + simpl in Hlen. discriminate.
    + simpl. simpl in Hlen. inversion Hlen as [Hlen'].
      rewrite IH by exact Hlen'. ring.
Qed.

(* ========================================================================= *)
(* PART III: CHAIN RULES AND RELATIONSHIPS                                   *)
(* ========================================================================= *)

(** 18. Chain rule: H(X,Y) = H(X) + H(Y|X) *)
Lemma chain_rule_entropy : forall h_x h_y_given_x h_joint,
  h_joint == h_x + h_y_given_x ->
  cond_entropy h_joint h_x == h_y_given_x.
Proof.
  intros h_x h_y_given_x h_joint Hchain.
  unfold cond_entropy. lra.
Qed.

(** 19. Mutual information via conditional entropy:
    I(X;Y) = H(Y) - H(Y|X) *)
Lemma mutual_info_via_cond : forall h_x h_y h_joint,
  mutual_info h_x h_y h_joint ==
  h_y - cond_entropy h_joint h_x.
Proof.
  intros. unfold mutual_info, cond_entropy. ring.
Qed.

(** 20. Redundancy + actual entropy = max entropy *)
Lemma redundancy_plus_entropy : forall h_max h_actual,
  redundancy h_max h_actual + h_actual == h_max.
Proof.
  intros. unfold redundancy. ring.
Qed.

End InformationTheory.
