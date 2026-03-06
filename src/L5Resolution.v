(**
  L5Resolution.v — Generalized Deterministic Tie-Breaking
  =========================================================

  Phase 3, Task 1.

  Generalizes L5_resolve from Core_ERR.v (nat-specific) to any type
  with a DecTotalOrder. Provides:
  - DecTotalOrder typeclass (decidable total order)
  - l5_resolve_gen : generalized minimum selection (option-returning)
  - nat instance with specialization to existing L5_resolve

  E/R/R Analysis:
  - Element: The "winner" selected by resolution
  - Role: Minimum element in the candidate set
  - Rule: DecTotalOrder axioms (total, antisymmetric, transitive)

  Depends on: TheoryOfSystems_Core_ERR.v
  Qed: 18, Admitted: 0
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
Require Import List Arith Lia.
Import ListNotations.

Generalizable Variables A.

(* ================================================================= *)
(** * DecTotalOrder — Decidable Total Order Typeclass               *)
(* ================================================================= *)

(**
  A DecTotalOrder on type A provides:
  - A binary relation dto_le that is total, antisymmetric, transitive
  - A decision procedure dto_le_dec (sumbool)

  This is the minimal structure needed for deterministic L5-resolution:
  given any finite nonempty set, select the UNIQUE minimum.
*)
Class DecTotalOrder (A : Type) := {
  dto_le : A -> A -> Prop;
  dto_le_dec : forall x y, {dto_le x y} + {~ dto_le x y};
  dto_le_total : forall x y, dto_le x y \/ dto_le y x;
  dto_le_antisym : forall x y, dto_le x y -> dto_le y x -> x = y;
  dto_le_trans : forall x y z, dto_le x y -> dto_le y z -> dto_le x z;
}.

(** Reflexivity follows from totality *)
Lemma dto_le_refl `{DecTotalOrder A} : forall x : A, dto_le x x.
Proof.
  intros x. destruct (dto_le_total x x); assumption.
Qed.

(* ================================================================= *)
(** * Generalized L5 Resolution                                     *)
(* ================================================================= *)

Section L5_General.

  Context `{DecTotalOrder A}.

  (** Step function: keep the minimum of accumulator and new element *)
  Definition l5_min_step (acc y : A) : A :=
    if dto_le_dec y acc then y else acc.

  (** Generalized L5 resolution: select minimum from a list.
      Returns None for empty list, Some(min) otherwise.

      Design choice: fold_left (left-to-right scan) with the head
      element as initial accumulator. This mirrors the linear scan
      pattern used in L5_resolve but generalizes to any ordered type. *)
  Definition l5_resolve_gen (l : list A) : option A :=
    match l with
    | [] => None
    | x :: xs => Some (fold_left l5_min_step xs x)
    end.

  (* --------------------------------------------------------------- *)
  (** ** Helper Properties of l5_min_step                            *)
  (* --------------------------------------------------------------- *)

  (** l5_min_step result is <= the accumulator *)
  Lemma l5_min_step_le_left : forall acc y,
    dto_le (l5_min_step acc y) acc.
  Proof.
    intros acc y. unfold l5_min_step.
    destruct (dto_le_dec y acc) as [Hle | Hnle].
    - exact Hle.
    - apply dto_le_refl.
  Qed.

  (** l5_min_step result is <= the new element *)
  Lemma l5_min_step_le_right : forall acc y,
    dto_le (l5_min_step acc y) y.
  Proof.
    intros acc y. unfold l5_min_step.
    destruct (dto_le_dec y acc) as [Hle | Hnle].
    - apply dto_le_refl.
    - destruct (dto_le_total y acc) as [Hya | Hay].
      + contradiction.
      + exact Hay.
  Qed.

  (* --------------------------------------------------------------- *)
  (** ** Core fold_left Properties                                   *)
  (* --------------------------------------------------------------- *)

  (** The fold_left result is <= the initial accumulator.
      Invariant: minimum can only decrease as we scan more elements. *)
  Lemma fold_left_min_le_init : forall (l : list A) (init : A),
    dto_le (fold_left l5_min_step l init) init.
  Proof.
    induction l as [| z zs IH]; intros init; simpl.
    - apply dto_le_refl.
    - eapply dto_le_trans.
      + apply IH.
      + apply l5_min_step_le_left.
  Qed.

  (** The fold_left result is <= every element in the list.
      Key property: the computed minimum is indeed a lower bound. *)
  Lemma fold_left_min_le_elem : forall (l : list A) (init : A) (y : A),
    In y l -> dto_le (fold_left l5_min_step l init) y.
  Proof.
    induction l as [| z zs IH]; intros init y Hy; simpl.
    - destruct Hy.
    - destruct Hy as [Heq | Hin].
      + subst z.
        eapply dto_le_trans.
        * apply fold_left_min_le_init.
        * apply l5_min_step_le_right.
      + apply IH. exact Hin.
  Qed.

  (** The fold_left result is always in init :: l.
      The minimum is selected from the input, never fabricated. *)
  Lemma fold_left_min_in : forall (l : list A) (init : A),
    In (fold_left l5_min_step l init) (init :: l).
  Proof.
    induction l as [| z zs IH]; intros init; simpl.
    - left. reflexivity.
    - specialize (IH (l5_min_step init z)).
      destruct IH as [Heq | Hin].
      + rewrite <- Heq. unfold l5_min_step.
        destruct (dto_le_dec z init) as [_ | _].
        * right. left. reflexivity.
        * left. reflexivity.
      + right. right. exact Hin.
  Qed.

  (* --------------------------------------------------------------- *)
  (** ** Main Theorems                                               *)
  (* --------------------------------------------------------------- *)

  (** Theorem 1: Non-empty list always produces Some *)
  Theorem l5_resolve_gen_some : forall (l : list A),
    l <> [] -> exists v, l5_resolve_gen l = Some v.
  Proof.
    intros [| x xs] Hne.
    - contradiction Hne. reflexivity.
    - exists (fold_left l5_min_step xs x). reflexivity.
  Qed.

  (** None if and only if empty *)
  Theorem l5_resolve_gen_none_iff : forall (l : list A),
    l5_resolve_gen l = None <-> l = [].
  Proof.
    intros [| x xs]; split; intro Hx; try reflexivity; discriminate.
  Qed.

  (** Theorem 2: Result is an element of the original list *)
  Theorem l5_resolve_gen_in : forall (l : list A) (v : A),
    l5_resolve_gen l = Some v -> In v l.
  Proof.
    intros [| x xs] v Hv; simpl in *.
    - discriminate.
    - injection Hv as Hv. subst v.
      exact (fold_left_min_in xs x).
  Qed.

  (** Theorem 3: Result is minimal — dto_le to every element.
      This is the central property of L5-resolution: the selected
      element is a lower bound for all candidates. *)
  Theorem l5_resolve_gen_minimal : forall (l : list A) (v : A),
    l5_resolve_gen l = Some v ->
    forall p, In p l -> dto_le v p.
  Proof.
    intros [| x xs] v Hv p Hp; simpl in *.
    - destruct Hp.
    - injection Hv as Hv. subst v.
      destruct Hp as [Heq | Hin].
      + subst p. apply fold_left_min_le_init.
      + apply fold_left_min_le_elem. exact Hin.
  Qed.

  (** Theorem 4: Deterministic — same elements (as set) give same result.

      Proof strategy: both results are mutual minima.
      a is minimal in l1, b is in l1 (via set-equality) ⟹ a ≤ b.
      Symmetrically b ≤ a. By antisymmetry: a = b.

      This is the L5 DETERMINISM guarantee: the resolution outcome
      depends only on WHICH elements are present, not their ordering. *)
  Theorem l5_resolve_gen_deterministic :
    forall (l1 l2 : list A) (a b : A),
    l5_resolve_gen l1 = Some a ->
    l5_resolve_gen l2 = Some b ->
    (forall x, In x l1 <-> In x l2) ->
    a = b.
  Proof.
    intros l1 l2 a b Ha Hb Hset.
    apply dto_le_antisym.
    - apply (l5_resolve_gen_minimal l1 a Ha).
      apply Hset. exact (l5_resolve_gen_in l2 b Hb).
    - apply (l5_resolve_gen_minimal l2 b Hb).
      apply Hset. exact (l5_resolve_gen_in l1 a Ha).
  Qed.

  (** Singleton list resolves to its sole element *)
  Theorem l5_resolve_gen_singleton : forall (x : A),
    l5_resolve_gen [x] = Some x.
  Proof. reflexivity. Qed.

End L5_General.

(* ================================================================= *)
(** * Nat Instance: DecTotalOrder nat                               *)
(* ================================================================= *)

(**
  The canonical instance for Position = nat.
  Uses standard Peano ≤ ordering.
*)

Lemma nat_le_total : forall x y : nat, (x <= y)%nat \/ (y <= x)%nat.
Proof. intros; lia. Qed.

Lemma nat_le_antisym : forall x y : nat,
  (x <= y)%nat -> (y <= x)%nat -> x = y.
Proof. intros; lia. Qed.

Lemma nat_le_trans : forall x y z : nat,
  (x <= y)%nat -> (y <= z)%nat -> (x <= z)%nat.
Proof. intros; lia. Qed.

Instance nat_dto : DecTotalOrder nat := {
  dto_le := le;
  dto_le_dec := le_dec;
  dto_le_total := nat_le_total;
  dto_le_antisym := nat_le_antisym;
  dto_le_trans := nat_le_trans;
}.

(** Confirm that dto_le on nat is standard le *)
Lemma nat_dto_le_is_le : forall x y : nat,
  @dto_le nat nat_dto x y <-> (x <= y)%nat.
Proof.
  intros. simpl. tauto.
Qed.

(* ================================================================= *)
(** * Specialization: l5_resolve_gen agrees with L5_resolve         *)
(* ================================================================= *)

(**
  L5_resolve from Core_ERR.v uses fold_right Nat.min with a default.
  l5_resolve_gen uses fold_left l5_min_step without a default.

  Agreement: when the default is >= all candidates (i.e., the minimum
  comes from the list, not the default), both compute the same value.
  Concretely: L5_resolve l v = v when v is the minimum of l.
*)

(** Helper: fold_right Nat.min d l = d when d <= all elements *)
Lemma fold_right_min_eq_default : forall (l : list nat) (d : nat),
  (forall p, In p l -> (d <= p)%nat) ->
  fold_right Nat.min d l = d.
Proof.
  induction l as [| a l' IH]; intros d Hle.
  - reflexivity.
  - simpl.
    assert (Hside : forall p, In p l' -> (d <= p)%nat)
      by (intros p Hp; apply Hle; right; exact Hp).
    rewrite (IH d Hside).
    apply Nat.min_r. apply Hle. left. reflexivity.
Qed.

(** Main specialization: l5_resolve_gen and L5_resolve agree.
    When l5_resolve_gen selects v as the minimum, using v as the
    default for L5_resolve yields v back — proving both functions
    compute the same minimum over the same list. *)
Theorem l5_resolve_gen_specializes : forall (l : list nat) (v : nat),
  l5_resolve_gen l = Some v ->
  L5_resolve l v = v.
Proof.
  intros l v Hv.
  unfold L5_resolve.
  apply fold_right_min_eq_default.
  intros p Hp.
  exact (l5_resolve_gen_minimal l v Hv p Hp).
Qed.
