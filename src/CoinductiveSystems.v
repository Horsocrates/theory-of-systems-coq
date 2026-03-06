(* ========================================================================= *)
(*                  COINDUCTIVE / OBSERVABLE SYSTEMS (P4)                   *)
(*                                                                          *)
(*  Part of: Theory of Systems -- Coq Formalization                        *)
(*                                                                          *)
(*  Observable systems: defined by observations, not constructors.          *)
(*  Each observation is finite (P4), but the system itself is potentially   *)
(*  infinite.  Built on GenProcess A = nat -> A from ProcessGeneral.v.      *)
(*                                                                          *)
(*  STATUS: 16 Qed, 0 Admitted, 0 axioms                                   *)
(*  Author: Horsocrates | Date: March 2026                                  *)
(* ========================================================================= *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

From ToS Require Import ProcessGeneral.

(* ========================================================================= *)
(*                   PART I: OBSERVABLE SYSTEMS                             *)
(* ========================================================================= *)

Section Observables.
Variable A : Type.

(** Observable: a process with an observation criterion *)
Record Observable := mkObservable {
  obs_process : GenProcess A;
  obs_criterion : A -> Prop;
}.

(** Observation at step n *)
Definition obs_at (o : Observable) (n : nat) : A :=
  observe (obs_process o) n.

(** Finite prefix of observations *)
Definition obs_prefix (o : Observable) (n : nat) : list A :=
  prefix (obs_process o) n.

(** Two observables are equivalent if all observations match *)
Definition obs_equiv (o1 o2 : Observable) : Prop :=
  process_equiv eq (obs_process o1) (obs_process o2).

End Observables.

Arguments mkObservable {A} _ _.
Arguments obs_process {A} _.
Arguments obs_criterion {A} _.
Arguments obs_at {A} _ _.
Arguments obs_prefix {A} _ _.
Arguments obs_equiv {A} _ _.

(** Observable map: transform observations into a new type *)
Definition obs_map {A B : Type} (f : A -> B) (o : Observable A)
    : Observable B :=
  mkObservable (process_map f (obs_process o)) (fun b => exists a, obs_criterion o a /\ f a = b).

(* ========================================================================= *)
(*                   PART II: OBSERVATION PROPERTIES                        *)
(* ========================================================================= *)

(** 1. obs_at always returns a value (trivially true by definition) *)
Lemma obs_at_well_defined :
  forall (A : Type) (o : Observable A) (n : nat),
    obs_at o n = observe (obs_process o) n.
Proof.
  intros. unfold obs_at. reflexivity.
Qed.

(** 2. length (obs_prefix o n) = n *)
Lemma obs_prefix_length :
  forall (A : Type) (o : Observable A) (n : nat),
    length (obs_prefix o n) = n.
Proof.
  intros. unfold obs_prefix. apply prefix_length.
Qed.

(** 3. nth element of prefix = obs_at (when in range) *)
Lemma obs_prefix_nth :
  forall (A : Type) (o : Observable A) (n k : nat) (d : A),
    (k < n)%nat ->
    nth k (obs_prefix o n) d = obs_at o k.
Proof.
  intros A o n k d Hk.
  unfold obs_prefix, obs_at, observe.
  apply prefix_nth. exact Hk.
Qed.

(** 4. prefix (S n) = prefix n ++ [obs_at o n] *)
Lemma obs_prefix_snoc :
  forall (A : Type) (o : Observable A) (n : nat),
    obs_prefix o (S n) = obs_prefix o n ++ [obs_at o n].
Proof.
  intros A o n.
  unfold obs_prefix, obs_at, observe.
  simpl. reflexivity.
Qed.

(* ========================================================================= *)
(*                   PART III: EQUIVALENCE PROPERTIES                       *)
(* ========================================================================= *)

(** 5. Reflexivity of obs_equiv *)
Lemma obs_equiv_refl :
  forall (A : Type) (o : Observable A),
    obs_equiv o o.
Proof.
  intros A o. unfold obs_equiv.
  apply process_equiv_refl. intro; reflexivity.
Qed.

(** 6. Symmetry of obs_equiv *)
Lemma obs_equiv_sym :
  forall (A : Type) (o1 o2 : Observable A),
    obs_equiv o1 o2 -> obs_equiv o2 o1.
Proof.
  intros A o1 o2 H. unfold obs_equiv in *.
  apply process_equiv_sym with (eq_A := eq).
  - intros a b Hab. symmetry. exact Hab.
  - exact H.
Qed.

(** 7. Transitivity of obs_equiv *)
Lemma obs_equiv_trans :
  forall (A : Type) (o1 o2 o3 : Observable A),
    obs_equiv o1 o2 -> obs_equiv o2 o3 -> obs_equiv o1 o3.
Proof.
  intros A o1 o2 o3 H12 H23. unfold obs_equiv in *.
  apply process_equiv_trans with (eq_A := eq) (p2 := obs_process o2).
  - intros a b c Hab Hbc. transitivity b; assumption.
  - exact H12.
  - exact H23.
Qed.

(* ========================================================================= *)
(*                   PART IV: MAP PROPERTIES                                *)
(* ========================================================================= *)

(** 8. Mapping preserves equivalence *)
Lemma obs_map_preserves_equiv :
  forall (A B : Type) (f : A -> B) (o1 o2 : Observable A),
    obs_equiv o1 o2 ->
    obs_equiv (obs_map f o1) (obs_map f o2).
Proof.
  intros A B f o1 o2 Heq.
  unfold obs_equiv, obs_map in *. simpl.
  apply process_map_equiv with (eq_A := eq).
  - intros a1 a2 Ha. subst. reflexivity.
  - exact Heq.
Qed.

(** 9. obs_at (obs_map f o) n = f (obs_at o n) *)
Lemma obs_map_at :
  forall (A B : Type) (f : A -> B) (o : Observable A) (n : nat),
    obs_at (obs_map f o) n = f (obs_at o n).
Proof.
  intros A B f o n.
  unfold obs_at, obs_map, observe, process_map. simpl.
  reflexivity.
Qed.

(* ========================================================================= *)
(*                   PART V: P4 — NO COMPLETE OBSERVATION                   *)
(* ========================================================================= *)

(**
  P4: FINITENESS OF OBSERVATION
  ===============================

  A key principle of P4 is that any finite collection of observations
  cannot exhaust all possible observation indices.  For any list of
  length n, there exists an observation at index n that is beyond
  the list.
*)

(** 10. For any finite list, there exists an observation index beyond it *)
Lemma no_complete_observation :
  forall (A : Type) (o : Observable A) (l : list A),
    exists n : nat, (n >= length l)%nat.
Proof.
  intros A o l.
  exists (length l). lia.
Qed.

(** 11. For any n, obs_prefix o n exists with length n *)
Lemma obs_finite_prefix_exists :
  forall (A : Type) (o : Observable A) (n : nat),
    length (obs_prefix o n) = n.
Proof.
  intros. apply obs_prefix_length.
Qed.

(** A stronger P4 statement: any proposed "collection of all observations"
    given as a list has strictly fewer entries than there are indices *)
Lemma observation_inexhaustibility :
  forall (A : Type) (o : Observable A) (l : list A) (n : nat),
    (n > length l)%nat ->
    length (obs_prefix o n) > length l.
Proof.
  intros A o l n Hgt.
  rewrite obs_prefix_length. lia.
Qed.

(* ========================================================================= *)
(*                   PART VI: CONSTRUCTION LEMMAS                           *)
(* ========================================================================= *)

(** 12. Any function nat -> A gives an Observable *)
Definition obs_from_function {A : Type} (f : nat -> A) (P : A -> Prop)
    : Observable A :=
  mkObservable f P.

Lemma obs_from_function_at :
  forall (A : Type) (f : nat -> A) (P : A -> Prop) (n : nat),
    obs_at (obs_from_function f P) n = f n.
Proof.
  intros. unfold obs_at, obs_from_function, observe. simpl.
  reflexivity.
Qed.

(** 13. Constant observable: all observations are the same value *)
Definition obs_constant {A : Type} (a : A) (P : A -> Prop)
    : Observable A :=
  mkObservable (const_process a) P.

Lemma obs_constant_at :
  forall (A : Type) (a : A) (P : A -> Prop) (n : nat),
    obs_at (obs_constant a P) n = a.
Proof.
  intros. unfold obs_at, obs_constant, observe, const_process. simpl.
  reflexivity.
Qed.

(** 14. Two constant observables with same value are equivalent *)
Lemma obs_constant_equiv :
  forall (A : Type) (a : A) (P Q : A -> Prop),
    obs_equiv (obs_constant a P) (obs_constant a Q).
Proof.
  intros A a P Q.
  unfold obs_equiv, obs_constant. simpl.
  unfold process_equiv, const_process.
  intro n. reflexivity.
Qed.

(** 15. Map of a constant observable is constant *)
Lemma obs_map_constant :
  forall (A B : Type) (f : A -> B) (a : A) (P : A -> Prop) (n : nat),
    obs_at (obs_map f (obs_constant a P)) n = f a.
Proof.
  intros.
  rewrite obs_map_at. rewrite obs_constant_at.
  reflexivity.
Qed.

(* ========================================================================= *)
(*                   SUMMARY                                                *)
(* ========================================================================= *)

(**
  PROVEN (16 Qed):

  Part II  -- Observation properties:
    obs_at_well_defined, obs_prefix_length, obs_prefix_nth,
    obs_prefix_snoc

  Part III -- Equivalence:
    obs_equiv_refl, obs_equiv_sym, obs_equiv_trans

  Part IV  -- Map properties:
    obs_map_preserves_equiv, obs_map_at

  Part V   -- P4 (no complete observation):
    no_complete_observation, obs_finite_prefix_exists,
    observation_inexhaustibility   (3 lemmas)

  Part VI  -- Constructions:
    obs_from_function_at, obs_constant_at, obs_constant_equiv,
    obs_map_constant              (4 lemmas)

  KEY INSIGHTS:
  1. Observable = GenProcess + criterion (no CoInductive needed)
  2. P4: any finite prefix has length n, but observations extend to all nat
  3. Equivalence is just pointwise Leibniz equality on underlying process
  4. Map lifts to observables and preserves equivalence
  5. All proofs are fully constructive (0 axioms, 0 Admitted)

  AXIOMS: 0
*)

Print Assumptions obs_prefix_nth.
Print Assumptions obs_equiv_trans.
Print Assumptions obs_map_preserves_equiv.
