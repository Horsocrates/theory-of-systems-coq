(* ========================================================================= *)
(*              CONSTITUTION CHECKING: DECIDABLE MEMBERSHIP                *)
(*                                                                         *)
(*  Part of: Theory of Systems -- Coq Formalization                       *)
(*                                                                         *)
(*  Decidable constitution satisfaction: sumbool-based decidability,       *)
(*  boolean checking, closure properties, concrete instances, and          *)
(*  integration with L5-resolution.                                        *)
(*                                                                         *)
(*  STATUS: 16 Qed, 0 Admitted, 0 axioms                                 *)
(*  Author: Horsocrates | Date: March 2026                                *)
(* ========================================================================= *)

Require Import Stdlib.Init.Nat.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Arith.Compare_dec.
Require Import Stdlib.QArith.QArith.
Import ListNotations.

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import IntensionalIdentity.
From ToS Require Import L5Resolution.

(* ========================================================================= *)
(*                   PART I: DECIDABLE CONSTITUTION                        *)
(* ========================================================================= *)

Section DecConstitution.

Variable D : Type.

(** Decidable constitution: sumbool witness for membership *)
Class DecidableConstitution (pred : D -> Prop) := {
  dc_decide : forall e : D, {pred e} + {~ pred e};
}.

(** Boolean constitution: computational checker with correctness *)
Class BoolConstitution (pred : D -> Prop) := {
  bc_check : D -> bool;
  bc_correct : forall e, bc_check e = true <-> pred e;
}.

(* ========================================================================= *)
(*                   PART II: CLOSURE PROPERTIES                           *)
(* ========================================================================= *)

(** Lemma 1: Conjunction closure *)
Lemma dec_conjunction :
  forall (p1 p2 : D -> Prop),
    DecidableConstitution p1 ->
    DecidableConstitution p2 ->
    DecidableConstitution (fun e => p1 e /\ p2 e).
Proof.
  intros p1 p2 [d1] [d2].
  constructor. intro e.
  destruct (d1 e) as [H1 | H1]; destruct (d2 e) as [H2 | H2].
  - left. split; assumption.
  - right. intros [_ H]. contradiction.
  - right. intros [H _]. contradiction.
  - right. intros [H _]. contradiction.
Qed.

(** Lemma 2: Disjunction closure *)
Lemma dec_disjunction :
  forall (p1 p2 : D -> Prop),
    DecidableConstitution p1 ->
    DecidableConstitution p2 ->
    DecidableConstitution (fun e => p1 e \/ p2 e).
Proof.
  intros p1 p2 [d1] [d2].
  constructor. intro e.
  destruct (d1 e) as [H1 | H1]; destruct (d2 e) as [H2 | H2].
  - left. left. exact H1.
  - left. left. exact H1.
  - left. right. exact H2.
  - right. intros [H | H]; contradiction.
Qed.

(** Lemma 3: Negation closure *)
Lemma dec_negation :
  forall (p : D -> Prop),
    DecidableConstitution p ->
    DecidableConstitution (fun e => ~ p e).
Proof.
  intros p [d].
  constructor. intro e.
  destruct (d e) as [H | H].
  - right. intro Hn. apply Hn. exact H.
  - left. exact H.
Qed.

(* ========================================================================= *)
(*                   PART III: DEC <-> BOOL EQUIVALENCE                    *)
(* ========================================================================= *)

(** Lemma 4: Decidable implies Bool *)
Lemma dec_implies_bool :
  forall (p : D -> Prop),
    DecidableConstitution p -> BoolConstitution p.
Proof.
  intros p [d].
  refine ({| bc_check := fun e => if d e then true else false |}).
  intro e. destruct (d e) as [H | H]; split; intro Hx.
  - exact H.
  - reflexivity.
  - discriminate.
  - contradiction.
Qed.

(** Lemma 5: Bool implies Decidable *)
Lemma bool_implies_dec :
  forall (p : D -> Prop),
    BoolConstitution p -> DecidableConstitution p.
Proof.
  intros p [chk corr].
  constructor. intro e.
  destruct (chk e) eqn:Hb.
  - left. apply corr. exact Hb.
  - right. intro H. apply corr in H. rewrite H in Hb. discriminate.
Qed.

(* ========================================================================= *)
(*                   PART IV: TRIVIAL CONSTITUTIONS                        *)
(* ========================================================================= *)

(** Lemma 6: Always-true constitution is decidable *)
Lemma dec_true_trivial :
  DecidableConstitution (fun _ : D => True).
Proof. constructor. intro e. left. exact I. Qed.

(** Lemma 7: Always-false constitution is decidable *)
Lemma dec_false_trivial :
  DecidableConstitution (fun _ : D => False).
Proof. constructor. intro e. right. intro H. exact H. Qed.

End DecConstitution.

(* ========================================================================= *)
(*                   PART V: CONCRETE INSTANCES                            *)
(* ========================================================================= *)

(** Lemma 8: Equality on nat is decidable *)
Lemma nat_eq_dec_constitution :
  forall (n : nat), DecidableConstitution nat (fun m => m = n).
Proof.
  intro n. constructor. intro e.
  destruct (Nat.eq_dec e n) as [H | H]; [left | right]; exact H.
Qed.

(** Lemma 9: <= on nat is decidable *)
Lemma nat_le_dec_constitution :
  forall (n : nat), DecidableConstitution nat (fun m => (m <= n)%nat).
Proof.
  intro n. constructor. intro e.
  destruct (le_dec e n) as [H | H]; [left | right]; exact H.
Qed.

(** Lemma 10: <= on Q is decidable *)
Lemma Q_le_dec_constitution :
  forall (q : Q), DecidableConstitution Q (fun x => Qle x q).
Proof.
  intro q. constructor. intro e.
  destruct (Qle_bool e q) eqn:Hb.
  - left. apply Qle_bool_iff. exact Hb.
  - right. intro H. apply Qle_bool_iff in H. rewrite H in Hb. discriminate.
Qed.

(* ========================================================================= *)
(*                   PART VI: SYSTEM-LEVEL INTEGRATION                     *)
(* ========================================================================= *)

(** A decidable system: the criterion's predicate is decidable *)
Definition decidable_system (L : Level) (sys : System L) : Type :=
  forall e : crit_domain L (sys_criterion L sys),
    {crit_predicate L (sys_criterion L sys) e} +
    {~ crit_predicate L (sys_criterion L sys) e}.

(** Lemma 11: Decidable systems can be checked for well-formedness (P2). *)
Lemma decidable_system_well_formed :
  forall (L : Level) (sys : System L),
    decidable_system L sys ->
    {crit_level_witness L (sys_criterion L sys) << L} +
    {~ crit_level_witness L (sys_criterion L sys) << L}.
Proof.
  intros L sys _.
  left. exact (crit_level_valid L (sys_criterion L sys)).
Qed.

(** Lemma 12: L5-resolution selects from decidable candidate lists. *)
Lemma l5_resolve_on_decidable :
  forall (candidates : list nat) (v : nat),
    candidates <> [] ->
    l5_resolve_gen candidates = Some v ->
    In v candidates.
Proof.
  intros candidates v Hne Hres.
  exact (l5_resolve_gen_in candidates v Hres).
Qed.

(* ========================================================================= *)
(*                   PART VII: FILTER AND DECIDABLE MEMBERSHIP             *)
(* ========================================================================= *)

Section FilterDecidable.

Variable D : Type.
Variable pred : D -> Prop.
Variable dc : forall e : D, {pred e} + {~ pred e}.

Definition dec_filter (l : list D) : list D :=
  filter (fun e => if dc e then true else false) l.

(** Lemma 13: Filtered elements satisfy the predicate (soundness) *)
Lemma dec_filter_sound :
  forall (l : list D) (e : D), In e (dec_filter l) -> pred e.
Proof.
  intros l e Hin. unfold dec_filter in Hin.
  apply filter_In in Hin. destruct Hin as [_ Hchk].
  destruct (dc e) as [H | H]; [exact H | discriminate].
Qed.

(** Lemma 14: Satisfying elements are in filtered list (completeness) *)
Lemma dec_filter_complete :
  forall (l : list D) (e : D), In e l -> pred e -> In e (dec_filter l).
Proof.
  intros l e Hin Hpred. unfold dec_filter. apply filter_In. split.
  - exact Hin.
  - destruct (dc e) as [H | H]; [reflexivity | contradiction].
Qed.

End FilterDecidable.

(* ========================================================================= *)
(*                   PART VIII: DECIDABLE IMPLICATION & IFF                 *)
(* ========================================================================= *)

(** Lemma 15: Implication closure *)
Lemma dec_implication :
  forall (D : Type) (p1 p2 : D -> Prop),
    DecidableConstitution D p1 ->
    DecidableConstitution D p2 ->
    DecidableConstitution D (fun e => p1 e -> p2 e).
Proof.
  intros Dt p1 p2 [d1] [d2].
  constructor. intro e.
  destruct (d1 e) as [H1 | H1]; destruct (d2 e) as [H2 | H2].
  - left. intro Hign. exact H2.
  - right. intro H. apply H2. apply H. exact H1.
  - left. intro H. contradiction.
  - left. intro H. contradiction.
Qed.

(** Lemma 16: Decidable equivalence (iff) *)
Lemma dec_iff :
  forall (D : Type) (p1 p2 : D -> Prop),
    DecidableConstitution D p1 ->
    DecidableConstitution D p2 ->
    DecidableConstitution D (fun e => p1 e <-> p2 e).
Proof.
  intros Dt p1 p2 [d1] [d2].
  constructor. intro e.
  destruct (d1 e) as [H1 | H1]; destruct (d2 e) as [H2 | H2].
  - left. split; intro Hign; assumption.
  - right. intro H. apply H2. apply H. exact H1.
  - right. intro H. apply H1. apply H. exact H2.
  - left. split; intro H; contradiction.
Qed.

(* ========================================================================= *)
(*                   SUMMARY                                                *)
(* ========================================================================= *)

(**
  16 Qed, 0 Admitted, 0 axioms.

  Closure: conjunction, disjunction, negation, implication, iff.
  Equivalence: DecidableConstitution <-> BoolConstitution.
  Trivial: True, False always decidable.
  Instances: nat =, nat <=, Q <=.
  System: well-formedness decidable, L5 resolution on decidable lists.
  Filter: soundness and completeness of dec_filter.
*)

Print Assumptions dec_conjunction.
Print Assumptions dec_implies_bool.
Print Assumptions Q_le_dec_constitution.
Print Assumptions dec_filter_sound.
Print Assumptions dec_iff.
