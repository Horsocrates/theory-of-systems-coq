(** * ListModes.v — A set as a MODE of considering a list:
      list -> multiset -> set, and what each step forgets

    E/R/R reading (done before coding; audit of Part I of the Mathematics
    volume, chapter I.7, place 2, 2026-11-13):

    Elements: the members of a finite list, each at its position.
    Roles:    the position of a member (order) and its multiplicity — two
              attributes that a mode of consideration may keep or ignore.
    Rules:    the multiset mode keeps the multiplicity and ignores the order;
              the set mode keeps membership only and ignores both.
    Proved:   (1) the first step forgets EXACTLY the order: two lists are one
                  multiset iff they are permutations of each other;
              (2) the set is obtained from the multiset: a value belongs to
                  the support iff its multiplicity is positive;
              (3) the second step is well defined: one multiset — one set;
              (4) every set given by a list is given by a list without
                  repetitions;
              (5) each step really forgets something, and there is no way
                  back: a function that depends on the set only cannot see
                  the multiplicity, and one that depends on the multiset only
                  cannot see the order.
    P4 diagnostic ("could it be otherwise?"): finite lists only; nothing
              infinite. Forced: (1)-(5). NOT claimed: that the set-theory
              layer of the repository (src/settheory/) is built on lists —
              there sets are given by predicates and by types with maps;
              this file states the list -> set scheme itself.

    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import List Permutation PeanoNat Lia.
Import ListNotations.

Section ListModes.

  Variable A : Type.
  Hypothesis eq_dec : forall x y : A, {x = y} + {x <> y}.

  (** The multiset mode: how many times a value occurs in the list. *)
  Definition mult (l : list A) : A -> nat := fun x => count_occ eq_dec l x.

  (** The set mode (support): which values occur in the list. *)
  Definition support (l : list A) : A -> Prop := fun x => In x l.

  (** Two lists — one multiset / one set. *)
  Definition same_multiset (l1 l2 : list A) : Prop := forall x, mult l1 x = mult l2 x.
  Definition same_set (l1 l2 : list A) : Prop := forall x, support l1 x <-> support l2 x.

  (** The first step forgets the order, and only the order: the multisets
      coincide exactly when the lists are permutations of each other. *)
  Theorem first_step_forgets_exactly_order :
    forall l1 l2, same_multiset l1 l2 <-> Permutation l1 l2.
  Proof.
    intros l1 l2. unfold same_multiset, mult. split.
    - intro H. apply (Permutation_count_occ eq_dec). exact H.
    - intro H. apply (Permutation_count_occ eq_dec). exact H.
  Qed.

  (** The set is obtained from the multiset: a value is in the support
      exactly when its multiplicity is positive. *)
  Theorem support_from_mult :
    forall l x, support l x <-> mult l x > 0.
  Proof.
    intros l x. unfold support, mult. apply (count_occ_In eq_dec).
  Qed.

  (** The second step: one multiset — one set. *)
  Theorem second_step_well_defined :
    forall l1 l2, same_multiset l1 l2 -> same_set l1 l2.
  Proof.
    intros l1 l2 H x.
    rewrite (support_from_mult l1 x), (support_from_mult l2 x), (H x). tauto.
  Qed.

  (** A permutation of the list does not change the set; neither does the
      repetition of a member. *)
  Corollary set_ignores_order :
    forall l1 l2, Permutation l1 l2 -> same_set l1 l2.
  Proof.
    intros l1 l2 H. apply second_step_well_defined.
    apply first_step_forgets_exactly_order. exact H.
  Qed.

  Lemma set_ignores_multiplicity :
    forall (a : A) (l : list A), same_set (a :: a :: l) (a :: l).
  Proof.
    intros a l x. unfold support. simpl. tauto.
  Qed.

  (** Every set given by a list is given by a list without repetitions. *)
  Theorem set_has_duplicate_free_list :
    forall l, exists l', NoDup l' /\ same_set l l'.
  Proof.
    intro l. exists (nodup eq_dec l). split.
    - apply NoDup_nodup.
    - intro x. unfold support. symmetry. apply nodup_In.
  Qed.

End ListModes.

(** Each step really forgets something. *)

Theorem order_is_forgotten :
  [1; 2; 3] <> [3; 2; 1] /\ same_multiset nat Nat.eq_dec [1; 2; 3] [3; 2; 1].
Proof.
  split.
  - discriminate.
  - apply first_step_forgets_exactly_order.
    apply Permutation_rev with (l := [1; 2; 3]).
Qed.

Theorem multiplicity_is_forgotten :
  same_set nat [1; 1; 2; 3] [1; 2; 3] /\
  ~ same_multiset nat Nat.eq_dec [1; 1; 2; 3] [1; 2; 3].
Proof.
  split.
  - apply set_ignores_multiplicity.
  - intro H. specialize (H 1). unfold mult in H. simpl in H. discriminate.
Qed.

(** There is no way back: a function of lists that depends on the set only
    does not tell [1;1] from [1]; one that depends on the multiset only does
    not tell [1;2] from [2;1]. *)
Theorem set_mode_cannot_see_multiplicity :
  forall (B : Type) (g : list nat -> B),
    (forall l1 l2, same_set nat l1 l2 -> g l1 = g l2) ->
    g [1; 1] = g [1].
Proof.
  intros B g Hg. apply Hg. apply set_ignores_multiplicity.
Qed.

Theorem multiset_mode_cannot_see_order :
  forall (B : Type) (g : list nat -> B),
    (forall l1 l2, same_multiset nat Nat.eq_dec l1 l2 -> g l1 = g l2) ->
    g [1; 2] = g [2; 1].
Proof.
  intros B g Hg. apply Hg. apply first_step_forgets_exactly_order.
  apply perm_swap.
Qed.
