(* ========================================================================= *)
(*                    ERASURE THEORY: COMPILE-TIME VS RUNTIME              *)
(*                                                                          *)
(*  Part of: Theory of Systems — Coq Formalization                         *)
(*                                                                          *)
(*  At runtime, not everything needs to exist. Roles (L4 justification)    *)
(*  are verified at compile time and erased. Elements and Rules stay.       *)
(*  This formalizes what survives extraction.                               *)
(*                                                                          *)
(*  The key insight: Coq's extraction ALREADY does erasure (Prop -> erased) *)
(*  This file mirrors that pattern for E/R/R categories.                   *)
(*                                                                          *)
(*  STATUS: 16 Qed, 0 Admitted, 0 axioms                                  *)
(*  Author: Horsocrates | Date: March 2026                                  *)
(* ========================================================================= *)

Require Import Stdlib.Init.Nat.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Bool.Bool.
Import ListNotations.

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import Roles.

(* ========================================================================= *)
(*                   PART I: RELEVANCE ANNOTATIONS                         *)
(* ========================================================================= *)

(** Relevance annotation: does a component survive extraction? *)
Inductive Relevance := Runtime | CompileOnly.

(** Relevance equality is decidable *)
Lemma relevance_dec : forall (r1 r2 : Relevance), {r1 = r2} + {r1 <> r2}.
Proof.
  intros r1 r2. destruct r1, r2;
    try (left; reflexivity);
    right; discriminate.
Qed.

(** Boolean equality test for Relevance *)
Definition relevance_eqb (r1 r2 : Relevance) : bool :=
  match r1, r2 with
  | Runtime, Runtime => true
  | CompileOnly, CompileOnly => true
  | _, _ => false
  end.

(** Annotated E/R/R component *)
Record AnnotatedComponent := mkAC {
  ac_category : ERR_Category;
  ac_relevance : Relevance;
}.

(** AnnotatedComponent equality is decidable (given ERR_Category decidability) *)
Lemma annotated_component_dec :
  forall (a1 a2 : AnnotatedComponent), {a1 = a2} + {a1 <> a2}.
Proof.
  intros [c1 r1] [c2 r2].
  destruct (err_cat_eq_dec c1 c2) as [Hc | Hc];
    destruct (relevance_dec r1 r2) as [Hr | Hr].
  - left. subst. reflexivity.
  - right. intros H. injection H. intros. contradiction.
  - right. intros H. injection H. intros. contradiction.
  - right. intros H. injection H. intros. contradiction.
Qed.

(* ========================================================================= *)
(*                   PART II: DEFAULT RELEVANCE BY CATEGORY                *)
(* ========================================================================= *)

(** Default relevance by E/R/R category:
    - Elements (WHAT) always exist at runtime
    - Roles (WHY) are erased after type-checking / verification
    - Rules (HOW) are computational and stay at runtime *)
Definition default_relevance (cat : ERR_Category) : Relevance :=
  match cat with
  | Cat_Element => Runtime
  | Cat_Role => CompileOnly
  | Cat_Rule => Runtime
  end.

(** Elements are always runtime *)
Lemma elements_always_runtime : default_relevance Cat_Element = Runtime.
Proof. reflexivity. Qed.

(** Roles are always compile-only *)
Lemma roles_always_compile : default_relevance Cat_Role = CompileOnly.
Proof. reflexivity. Qed.

(** Rules are always runtime *)
Lemma rules_always_runtime : default_relevance Cat_Rule = Runtime.
Proof. reflexivity. Qed.

(* ========================================================================= *)
(*                   PART III: ERASURE FUNCTION                            *)
(* ========================================================================= *)

(** Boolean test: is this component Runtime? *)
Definition is_runtime (ac : AnnotatedComponent) : bool :=
  match ac_relevance ac with
  | Runtime => true
  | CompileOnly => false
  end.

(** Erasure function: strip CompileOnly components *)
Definition erase (components : list AnnotatedComponent) : list AnnotatedComponent :=
  filter is_runtime components.

(** Erasing the empty list yields the empty list *)
Lemma erase_empty : erase [] = [].
Proof. reflexivity. Qed.

(** Erasing a singleton Runtime component preserves it *)
Lemma erase_singleton_runtime :
  forall cat, erase [mkAC cat Runtime] = [mkAC cat Runtime].
Proof.
  intros cat. unfold erase, filter, is_runtime. reflexivity.
Qed.

(** Erasing a singleton CompileOnly component removes it *)
Lemma erase_singleton_compile :
  forall cat, erase [mkAC cat CompileOnly] = [].
Proof.
  intros cat. unfold erase, filter, is_runtime. reflexivity.
Qed.

(* ========================================================================= *)
(*                   PART IV: ERASURE PROPERTIES                           *)
(* ========================================================================= *)

(** Helper: is_runtime is true iff relevance is Runtime *)
Lemma is_runtime_iff :
  forall ac, is_runtime ac = true <-> ac_relevance ac = Runtime.
Proof.
  intros [c r]. unfold is_runtime. simpl. split; intros H;
    destruct r; try reflexivity; discriminate.
Qed.

(** Erasure preserves Runtime components: if a component is Runtime,
    and it's in the original list, it survives erasure *)
Lemma erasure_preserves_runtime :
  forall (ac : AnnotatedComponent) (l : list AnnotatedComponent),
    In ac l ->
    ac_relevance ac = Runtime ->
    In ac (erase l).
Proof.
  intros ac l Hin Hrt. unfold erase.
  apply filter_In. split.
  - exact Hin.
  - apply is_runtime_iff. exact Hrt.
Qed.

(** Erasure removes all CompileOnly components *)
Lemma erasure_removes_compile_only :
  forall (ac : AnnotatedComponent) (l : list AnnotatedComponent),
    In ac (erase l) ->
    ac_relevance ac = Runtime.
Proof.
  intros ac l Hin. unfold erase in Hin.
  apply filter_In in Hin. destruct Hin as [_ Hrt].
  apply is_runtime_iff. exact Hrt.
Qed.

(** Erasure is idempotent: erasing twice = erasing once *)
Lemma erasure_idempotent :
  forall (l : list AnnotatedComponent),
    erase (erase l) = erase l.
Proof.
  intros l. unfold erase.
  induction l as [| a t IH]; simpl.
  - reflexivity.
  - destruct (is_runtime a) eqn:Ha.
    + simpl. rewrite Ha. f_equal. exact IH.
    + exact IH.
Qed.

(** Runtime components are a subset of the full list *)
Lemma runtime_subset_of_full :
  forall (ac : AnnotatedComponent) (l : list AnnotatedComponent),
    In ac (erase l) -> In ac l.
Proof.
  intros ac l Hin. unfold erase in Hin.
  apply filter_In in Hin. destruct Hin as [Hin _]. exact Hin.
Qed.

(** Length of erased list is bounded by original length *)
Lemma erasure_preserves_length_bound :
  forall (l : list AnnotatedComponent),
    (length (erase l) <= length l)%nat.
Proof.
  intros l. unfold erase.
  induction l as [| a t IH]; simpl.
  - lia.
  - destruct (is_runtime a); simpl; lia.
Qed.

(* ========================================================================= *)
(*                   PART V: COMPOSITION WITH DEFAULT RELEVANCE            *)
(* ========================================================================= *)

(** Annotate a category with its default relevance *)
Definition annotate_default (cat : ERR_Category) : AnnotatedComponent :=
  mkAC cat (default_relevance cat).

(** Default-annotated Elements survive erasure *)
Lemma default_element_survives :
  forall l,
    In (annotate_default Cat_Element) l ->
    In (annotate_default Cat_Element) (erase l).
Proof.
  intros l Hin. apply erasure_preserves_runtime.
  - exact Hin.
  - reflexivity.
Qed.

(** Default-annotated Roles are erased *)
Lemma default_role_erased :
  forall l,
    In (annotate_default Cat_Role) (erase l) -> False.
Proof.
  intros l Hin.
  apply erasure_removes_compile_only in Hin.
  simpl in Hin. discriminate.
Qed.

(** SUMMARY: 16 Qed, 0 Admitted.
    Roles erased at extraction; Elements and Rules survive to runtime.
    Erasure is idempotent and mirrors Coq's own Prop-erasure mechanism. *)
