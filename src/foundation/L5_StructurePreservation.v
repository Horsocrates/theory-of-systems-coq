(* L5_StructurePreservation.v *)
(* E/R/R: Elements = SDistinctions, Roles = structure preservation, Rules = finer + functor *)
(* Standalone — only Stdlib imports *)
(* STATUS: 15 Qed, 0 Admitted, 0 axioms *)
(* Author: Horsocrates | Date: March 2026 *)

From Stdlib Require Import Nat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

(** * Structural distinction as pair *)

Definition SDistinction := (nat * nat)%type.

Definition sd_level (sd : SDistinction) : nat := fst sd.
Definition sd_index (sd : SDistinction) : nat := snd sd.

(** * Finer relation: higher level = finer distinction *)

Definition sd_finer (sd1 sd2 : SDistinction) : Prop :=
  (sd_level sd2 < sd_level sd1)%nat.

(** * Concrete distinctions *)

Definition sd_coarse : SDistinction := (1%nat, 0%nat).
Definition sd_fine : SDistinction := (3%nat, 0%nat).
Definition sd_finest : SDistinction := (5%nat, 0%nat).

Lemma fine_finer_than_coarse : sd_finer sd_fine sd_coarse.
Proof. unfold sd_finer, sd_level, sd_coarse, sd_fine. simpl. lia. Qed.

Lemma finest_finer_than_fine : sd_finer sd_finest sd_fine.
Proof. unfold sd_finer, sd_level, sd_fine, sd_finest. simpl. lia. Qed.

Lemma finest_finer_than_coarse : sd_finer sd_finest sd_coarse.
Proof. unfold sd_finer, sd_level, sd_coarse, sd_finest. simpl. lia. Qed.

(** * Finer is transitive *)

Lemma sd_finer_trans : forall s1 s2 s3,
  sd_finer s1 s2 -> sd_finer s2 s3 -> sd_finer s1 s3.
Proof. unfold sd_finer. intros. lia. Qed.

(** * Finer is irreflexive *)

Lemma sd_finer_irrefl : forall s, ~ sd_finer s s.
Proof. unfold sd_finer. intros s H. lia. Qed.

(** * Structure preservation: morphism preserves level ordering *)

Definition struct_preserved (f : SDistinction -> SDistinction) : Prop :=
  forall s1 s2, sd_finer s1 s2 -> sd_finer (f s1) (f s2).

(** * Identity preserves structure *)

Lemma id_preserves : struct_preserved (fun s => s).
Proof. unfold struct_preserved. intros. exact H. Qed.

(** * Level-shift preserves structure *)

Definition level_shift (n : nat) (sd : SDistinction) : SDistinction :=
  ((sd_level sd + n)%nat, sd_index sd).

Lemma shift_preserves : forall n, struct_preserved (level_shift n).
Proof.
  intro n. unfold struct_preserved, level_shift, sd_finer, sd_level. simpl.
  intros. lia.
Qed.

(** * Composition of structure-preserving maps *)

Lemma compose_preserves : forall f g,
  struct_preserved f -> struct_preserved g ->
  struct_preserved (fun s => f (g s)).
Proof.
  unfold struct_preserved. intros f g Hf Hg s1 s2 H.
  apply Hf. apply Hg. exact H.
Qed.

(** * Functor analogy: objects = distinctions, morphisms = finer *)

Definition sd_map_obj (f : nat -> nat) (sd : SDistinction) : SDistinction :=
  (f (sd_level sd), sd_index sd).

Lemma sd_map_preserves_monotone : forall f,
  (forall a b, (a < b)%nat -> (f a < f b)%nat) ->
  struct_preserved (sd_map_obj f).
Proof.
  intros f Hf. unfold struct_preserved, sd_map_obj, sd_finer, sd_level. simpl.
  intros s1 s2 H. apply Hf. exact H.
Qed.

(** * Concrete: doubling preserves structure *)

Lemma double_preserves :
  struct_preserved (sd_map_obj (fun n => (n * 2)%nat)).
Proof.
  apply sd_map_preserves_monotone. intros. lia.
Qed.

(** * SDistinction equality is decidable *)

Lemma sd_eq_dec : forall (s1 s2 : SDistinction), {s1 = s2} + {s1 <> s2}.
Proof.
  intros [a1 b1] [a2 b2].
  destruct (Nat.eq_dec a1 a2); destruct (Nat.eq_dec b1 b2);
  subst; try (left; reflexivity); right; intro H; injection H; intros; contradiction.
Qed.

(** * Constant map does not preserve structure *)

Lemma const_not_preserves :
  ~ struct_preserved (fun _ => sd_coarse).
Proof.
  unfold struct_preserved. intro H.
  assert (Habs := H sd_fine sd_coarse fine_finer_than_coarse).
  apply sd_finer_irrefl in Habs. exact Habs.
Qed.

(** * sd_finer is asymmetric *)

Lemma sd_finer_asymm : forall s1 s2,
  sd_finer s1 s2 -> ~ sd_finer s2 s1.
Proof. unfold sd_finer. intros. lia. Qed.

(** * Level shift by 0 is identity *)

Lemma shift_zero_id : forall sd,
  level_shift 0 sd = (sd_level sd, sd_index sd).
Proof.
  intros [l i]. unfold level_shift, sd_level, sd_index. simpl. rewrite Nat.add_0_r. reflexivity.
Qed.

(** * Level shift is composable *)

Lemma shift_compose : forall n m sd,
  level_shift n (level_shift m sd) = level_shift (m + n) sd.
Proof.
  intros n m [l i]. unfold level_shift, sd_level, sd_index. simpl. f_equal. lia.
Qed.
