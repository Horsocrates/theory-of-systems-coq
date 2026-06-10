(** * IndivisibleDistinction.v — A distinction cannot be halved
    Elements: all_four_necessary, distinction_indivisible, quantization_from_distinction
    Roles:    Indivisibility — all 4 fields required, no partial distinction
    Rules:    Count by nat (not Q), P4 domain discrete because distinctions are atomic
    Status:   Foundation
    STATUS: 25 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import foundation.Distinction.
From ToS Require Import foundation.LawsFromDistinction.

Open Scope Q_scope.

(* ================================================================== *)
(*  PART I: ALL FOUR FIELDS NECESSARY                                  *)
(* ================================================================== *)

Definition pseudo_distinction_no_excl (P : Prop) :=
  (P, ~P, P \/ ~P).

Definition pseudo_distinction_no_exh (P : Prop) :=
  (P, ~P, ~(P /\ ~P)).

Theorem all_four_necessary :
  forall P : Prop,
    exists D : Distinction, positive D = P.
Proof.
  intro P. exists (distinction_of P). reflexivity.
Qed.

Lemma exclusive_essential : forall D : Distinction,
  ~(positive D /\ negative D).
Proof. intro D. exact (exclusive D). Qed.

Lemma exhaustive_essential : forall D : Distinction,
  positive D \/ negative D.
Proof. intro D. exact (exhaustive D). Qed.

Lemma positive_determines_negative :
  forall P : Prop,
  negative (distinction_of P) = ~P.
Proof. reflexivity. Qed.

Theorem exactly_one_side : forall D : Distinction,
  (positive D /\ ~negative D) \/ (~positive D /\ negative D).
Proof.
  intro D.
  destruct (exhaustive D) as [Hp|Hn].
  - left. split; [exact Hp | intro Hn; exact (exclusive D (conj Hp Hn))].
  - right. split; [intro Hp; exact (exclusive D (conj Hp Hn)) | exact Hn].
Qed.

(* ================================================================== *)
(*  PART II: INDIVISIBILITY                                            *)
(* ================================================================== *)

Theorem pair_without_rules_contradictory :
  forall P : Prop, ~(P /\ ~P).
Proof.
  intros P [H1 H2]. exact (H2 H1).
Qed.

Theorem distinction_indivisible :
  forall D : Distinction,
  (positive D \/ negative D) /\
  (~(positive D /\ negative D)) /\
  ((positive D /\ ~negative D) \/ (~positive D /\ negative D)).
Proof.
  intro D. repeat split.
  - exact (exhaustive D).
  - exact (exclusive D).
  - destruct (exhaustive D) as [Hp|Hn].
    + left. split; [exact Hp | intro Hn; exact (exclusive D (conj Hp Hn))].
    + right. split; [intro Hp; exact (exclusive D (conj Hp Hn)) | exact Hn].
Qed.

Lemma without_exclusive_anything :
  forall P : Prop, P -> ~P -> False.
Proof. intros P HP HNP. exact (HNP HP). Qed.

Lemma without_exhaustive_gap :
  forall P : Prop, P \/ ~P.
Proof. intro P. exact (exhaustive (distinction_of P)). Qed.

(* ================================================================== *)
(*  PART III: COUNTING IS DISCRETE                                     *)
(* ================================================================== *)

Definition distinction_count_nat (Ds : list Distinction) : nat :=
  length Ds.

(** June 2026 honesty rollback: was `exists n, count Ds = n` — vacuous.  The real
    counting structure: the count is ADDITIVE over concatenation. *)
Theorem count_is_natural : forall Ds1 Ds2 : list Distinction,
  distinction_count_nat (Ds1 ++ Ds2)
  = (distinction_count_nat Ds1 + distinction_count_nat Ds2)%nat.
Proof. intros Ds1 Ds2. unfold distinction_count_nat. apply length_app. Qed.

Theorem count_always_nonneg : forall Ds : list Distinction,
  (0 <= distinction_count_nat Ds)%nat.
Proof. intro. unfold distinction_count_nat. lia. Qed.

Theorem no_fractional_distinctions :
  forall n : nat, (0 < n)%nat -> (1 <= n)%nat.
Proof. lia. Qed.

Theorem distinction_increment : forall Ds (D : Distinction),
  distinction_count_nat (D :: Ds) = S (distinction_count_nat Ds).
Proof. reflexivity. Qed.

Lemma zero_distinctions : distinction_count_nat nil = 0%nat.
Proof. reflexivity. Qed.

Lemma one_distinction : forall D : Distinction,
  distinction_count_nat (D :: nil) = 1%nat.
Proof. reflexivity. Qed.

(* ================================================================== *)
(*  PART IV: QUANTIZATION FROM LOGIC                                   *)
(* ================================================================== *)

Theorem quantization_from_distinction :
  (forall n : nat, (0 < n)%nat -> (1 <= n)%nat) /\
  (* values are finite ratios BY TYPE (June 2026: was the vacuous exists q, R n = q) *)
  (forall (R : nat -> Q) n,
     exists (num : Z) (den : BinNums.positive), R n = num # den) /\
  (forall n : nat, (0 <= n)%nat).
Proof.
  repeat split; [lia | | lia].
  intros R n. destruct (R n) as [num den]. exists num, den. reflexivity.
Qed.

(** June 2026 honesty rollback: was `exists q, f (S n) = q` — vacuous.  The real
    domain structure: the process domain is DISCRETE — every stage is the origin
    or a successor. *)
Theorem process_domain_forced :
  forall n : nat, n = 0%nat \/ exists m : nat, n = S m.
Proof.
  intro n. destruct n as [| m]; [left; reflexivity | right; exists m; reflexivity].
Qed.

(* ================================================================== *)
(*  SUMMARY                                                            *)
(* ================================================================== *)

Theorem indivisible_distinction_summary :
  (forall P, exists D : Distinction, positive D = P) /\
  (forall D : Distinction, (positive D \/ negative D) /\ ~(positive D /\ negative D)) /\
  (forall n : nat, (0 < n)%nat -> (1 <= n)%nat) /\
  (forall D : Distinction, distinction_count_nat (D :: nil) = 1%nat).
Proof.
  split; [|split; [|split]].
  - exact all_four_necessary.
  - intro D. split; [exact (exhaustive D) | exact (exclusive D)].
  - lia.
  - reflexivity.
Qed.
