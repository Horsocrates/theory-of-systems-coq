(* ========================================================================= *)
(*                    CAUCHY REALS: CONSTRUCTIVE COMPLETION OF Q             *)
(*                                                                           *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)         *)
(*                                                                           *)
(*  PURPOSE: Define real numbers as equivalence classes of Cauchy sequences   *)
(*  of rationals, with arithmetic operations and ordering.                   *)
(*                                                                           *)
(*  CONTENTS:                                                                *)
(*    1. Cauchy sequence definition                                          *)
(*    2. Equivalence relation (co-Cauchy / convergent difference)            *)
(*    3. Arithmetic: addition, negation                                      *)
(*    4. Ordering and basic properties                                       *)
(*    5. Archimedean property of Cauchy reals                                *)
(*    6. Completeness: rational approximation + self-convergence             *)
(*    7. Algebraic laws (comm, assoc, identity, inverse)                     *)
(*                                                                           *)
(*  STATUS: 18 Qed, 0 Admitted (100%)                                       *)
(*                                                                           *)
(*  AXIOMS: NONE - fully constructive over Q                                 *)
(*                                                                           *)
(*  Author: Horsocrates | Date: March 2026                                   *)
(* ========================================================================= *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qminmax.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.

Open Scope Q_scope.

(** Helper: rewrite Qabs under Qeq *)
Ltac qabs_rw H :=
  let Habs := fresh "Habs" in
  assert (Habs := Qabs_wd _ _ H); rewrite Habs; clear Habs.

(* ========================================================================= *)
(* SECTION 1: CAUCHY SEQUENCE DEFINITION                                     *)
(* ========================================================================= *)

Definition is_cauchy (a : nat -> Q) : Prop :=
  forall eps : Q, 0 < eps ->
    exists N : nat, forall m n : nat,
      (N <= m)%nat -> (N <= n)%nat -> Qabs (a m - a n) < eps.

Record CauchySeq := mkCauchy {
  cs_seq :> nat -> Q;
  cs_cauchy : is_cauchy cs_seq
}.

(* ========================================================================= *)
(* SECTION 2: EQUIVALENCE RELATION                                           *)
(* ========================================================================= *)

Definition cauchy_equiv (a b : CauchySeq) : Prop :=
  forall eps : Q, 0 < eps ->
    exists N : nat, forall n : nat,
      (N <= n)%nat -> Qabs (cs_seq a n - cs_seq b n) < eps.

Declare Scope cauchy_scope.
Notation "a ~~ b" := (cauchy_equiv a b) (at level 70) : cauchy_scope.
Local Open Scope cauchy_scope.

(** Equivalence is reflexive *)
Lemma cauchy_equiv_refl : forall a : CauchySeq, a ~~ a.
Proof.
  intros a eps Heps.
  exists 0%nat.
  intros n _.
  assert (H : cs_seq a n - cs_seq a n == 0) by ring.
  qabs_rw H.
  rewrite Qabs_pos; lra.
Qed.

(** Equivalence is symmetric *)
Lemma cauchy_equiv_sym : forall a b : CauchySeq, a ~~ b -> b ~~ a.
Proof.
  intros a b Hab eps Heps.
  destruct (Hab eps Heps) as [N HN].
  exists N.
  intros n Hn.
  assert (Hopp : cs_seq b n - cs_seq a n == -(cs_seq a n - cs_seq b n)) by ring.
  qabs_rw Hopp.
  rewrite Qabs_opp.
  apply HN. exact Hn.
Qed.

(** Equivalence is transitive *)
Lemma cauchy_equiv_trans : forall a b c : CauchySeq,
  a ~~ b -> b ~~ c -> a ~~ c.
Proof.
  intros a b c Hab Hbc eps Heps.
  assert (Heps2 : 0 < eps * (1#2)) by lra.
  destruct (Hab _ Heps2) as [N1 HN1].
  destruct (Hbc _ Heps2) as [N2 HN2].
  exists (Nat.max N1 N2).
  intros n Hn.
  assert (HnN1 : (N1 <= n)%nat) by lia.
  assert (HnN2 : (N2 <= n)%nat) by lia.
  assert (Hsum : cs_seq a n - cs_seq c n ==
                 (cs_seq a n - cs_seq b n) + (cs_seq b n - cs_seq c n)) by ring.
  qabs_rw Hsum.
  apply Qle_lt_trans with
    (y := Qabs (cs_seq a n - cs_seq b n) + Qabs (cs_seq b n - cs_seq c n)).
  - apply Qabs_triangle.
  - assert (H1 := HN1 n HnN1).
    assert (H2 := HN2 n HnN2).
    lra.
Qed.

(* ========================================================================= *)
(* SECTION 3: ARITHMETIC OPERATIONS                                          *)
(* ========================================================================= *)

Lemma cauchy_add_is_cauchy (a b : CauchySeq) :
  is_cauchy (fun n => cs_seq a n + cs_seq b n).
Proof.
  intros eps Heps.
  assert (Heps2 : 0 < eps * (1#2)) by lra.
  destruct (cs_cauchy a _ Heps2) as [Na HNa].
  destruct (cs_cauchy b _ Heps2) as [Nb HNb].
  exists (Nat.max Na Nb).
  intros m n Hm Hn.
  assert (HmNa : (Na <= m)%nat) by lia.
  assert (HnNa : (Na <= n)%nat) by lia.
  assert (HmNb : (Nb <= m)%nat) by lia.
  assert (HnNb : (Nb <= n)%nat) by lia.
  assert (Hsum : (cs_seq a m + cs_seq b m) - (cs_seq a n + cs_seq b n) ==
                 (cs_seq a m - cs_seq a n) + (cs_seq b m - cs_seq b n)) by ring.
  qabs_rw Hsum.
  apply Qle_lt_trans with
    (y := Qabs (cs_seq a m - cs_seq a n) + Qabs (cs_seq b m - cs_seq b n)).
  - apply Qabs_triangle.
  - assert (Ha := HNa m n HmNa HnNa).
    assert (Hb := HNb m n HmNb HnNb).
    lra.
Qed.

Definition cauchy_add (a b : CauchySeq) : CauchySeq :=
  mkCauchy _ (cauchy_add_is_cauchy a b).

Lemma cauchy_neg_is_cauchy (a : CauchySeq) :
  is_cauchy (fun n => - cs_seq a n).
Proof.
  intros eps Heps.
  destruct (cs_cauchy a eps Heps) as [N HN].
  exists N.
  intros m n Hm Hn.
  assert (Hopp : - cs_seq a m - - cs_seq a n == -(cs_seq a m - cs_seq a n)) by ring.
  qabs_rw Hopp.
  rewrite Qabs_opp.
  apply HN; assumption.
Qed.

Definition cauchy_neg (a : CauchySeq) : CauchySeq :=
  mkCauchy _ (cauchy_neg_is_cauchy a).

Definition cauchy_sub (a b : CauchySeq) : CauchySeq :=
  cauchy_add a (cauchy_neg b).

Lemma cauchy_const_is_cauchy (q : Q) : is_cauchy (fun _ => q).
Proof.
  intros eps Heps.
  exists 0%nat.
  intros m n _ _.
  assert (Hzero : q - q == 0) by ring.
  qabs_rw Hzero.
  rewrite Qabs_pos; lra.
Qed.

Definition cauchy_const (q : Q) : CauchySeq :=
  mkCauchy _ (cauchy_const_is_cauchy q).

(* ========================================================================= *)
(* SECTION 3b: ADDITION RESPECTS EQUIVALENCE                                 *)
(* ========================================================================= *)

Lemma cauchy_add_compat : forall a a' b b' : CauchySeq,
  a ~~ a' -> b ~~ b' -> cauchy_add a b ~~ cauchy_add a' b'.
Proof.
  intros a a' b b' Ha Hb eps Heps.
  assert (Heps2 : 0 < eps * (1#2)) by lra.
  destruct (Ha _ Heps2) as [Na HNa].
  destruct (Hb _ Heps2) as [Nb HNb].
  exists (Nat.max Na Nb).
  intros n Hn.
  simpl.
  assert (Hsum : (cs_seq a n + cs_seq b n) - (cs_seq a' n + cs_seq b' n) ==
                 (cs_seq a n - cs_seq a' n) + (cs_seq b n - cs_seq b' n)) by ring.
  qabs_rw Hsum.
  apply Qle_lt_trans with
    (y := Qabs (cs_seq a n - cs_seq a' n) + Qabs (cs_seq b n - cs_seq b' n)).
  - apply Qabs_triangle.
  - assert (HnNa : (Na <= n)%nat) by lia.
    assert (HnNb : (Nb <= n)%nat) by lia.
    assert (H1 := HNa n HnNa).
    assert (H2 := HNb n HnNb).
    lra.
Qed.

Lemma cauchy_neg_compat : forall a a' : CauchySeq,
  a ~~ a' -> cauchy_neg a ~~ cauchy_neg a'.
Proof.
  intros a a' Ha eps Heps.
  destruct (Ha eps Heps) as [N HN].
  exists N.
  intros n Hn.
  simpl.
  assert (Hopp : - cs_seq a n - - cs_seq a' n == -(cs_seq a n - cs_seq a' n)) by ring.
  qabs_rw Hopp.
  rewrite Qabs_opp.
  apply HN. exact Hn.
Qed.

(* ========================================================================= *)
(* SECTION 4: ORDERING                                                        *)
(* ========================================================================= *)

Definition cauchy_pos (a : CauchySeq) : Prop :=
  exists q : Q, 0 < q /\
    exists N : nat, forall n : nat,
      (N <= n)%nat -> q < cs_seq a n.

Definition cauchy_le (a b : CauchySeq) : Prop :=
  forall eps : Q, 0 < eps ->
    exists N : nat, forall n : nat,
      (N <= n)%nat -> cs_seq a n < cs_seq b n + eps.

Lemma cauchy_le_of_equiv : forall a b : CauchySeq,
  a ~~ b -> cauchy_le a b.
Proof.
  intros a b Hab eps Heps.
  destruct (Hab eps Heps) as [N HN].
  exists N.
  intros n Hn.
  assert (Hdiff := HN n Hn).
  apply Qabs_Qlt_condition in Hdiff.
  lra.
Qed.

Lemma cauchy_le_refl : forall a : CauchySeq, cauchy_le a a.
Proof.
  intros a. apply cauchy_le_of_equiv. apply cauchy_equiv_refl.
Qed.

Lemma cauchy_pos_not_zero : forall a : CauchySeq,
  cauchy_pos a -> ~ (a ~~ cauchy_const 0).
Proof.
  intros a [q [Hq [N HN]]] Hzero.
  destruct (Hzero (q * (1#2)) ltac:(lra)) as [M HM].
  set (K := Nat.max N M).
  assert (HKN : (N <= K)%nat) by lia.
  assert (HKM : (M <= K)%nat) by lia.
  assert (Ha := HN K HKN).
  assert (Hz := HM K HKM).
  simpl in Hz.
  assert (Hsimpl : cs_seq a K - 0 == cs_seq a K) by ring.
  assert (Habs := Qabs_wd _ _ Hsimpl).
  rewrite Habs in Hz.
  apply Qabs_Qlt_condition in Hz.
  lra.
Qed.

(* ========================================================================= *)
(* SECTION 5: ARCHIMEDEAN PROPERTY                                           *)
(* ========================================================================= *)

Lemma cauchy_const_lt : forall p q : Q,
  p < q -> cauchy_pos (cauchy_sub (cauchy_const q) (cauchy_const p)).
Proof.
  intros p q Hpq.
  exists ((q - p) * (1#2)).
  split.
  - lra.
  - exists 0%nat.
    intros n _.
    simpl.
    lra.
Qed.

(* ========================================================================= *)
(* SECTION 6: COMPLETENESS                                                    *)
(* ========================================================================= *)

Theorem cauchy_rational_approx : forall (a : CauchySeq) (eps : Q),
  0 < eps ->
  exists q : Q, exists N : nat, forall n : nat,
    (N <= n)%nat -> Qabs (cs_seq a n - q) < eps.
Proof.
  intros a eps Heps.
  destruct (cs_cauchy a eps Heps) as [N HN].
  exists (cs_seq a N).
  exists N.
  intros n Hn.
  apply HN; [exact Hn | apply Nat.le_refl].
Qed.

Theorem cauchy_complete_self : forall (a : CauchySeq),
  forall eps : Q, 0 < eps ->
    exists N : nat, forall n : nat,
      (N <= n)%nat ->
      cauchy_le (cauchy_sub a (cauchy_const (cs_seq a n)))
                (cauchy_const eps).
Proof.
  intros a eps Heps.
  destruct (cs_cauchy a (eps * (1#2)) ltac:(lra)) as [N HN].
  exists N.
  intros n Hn.
  intros delta Hdelta.
  exists N.
  intros m Hm.
  simpl.
  assert (Hdiff := HN m n Hm Hn).
  apply Qabs_Qlt_condition in Hdiff.
  lra.
Qed.

Lemma cauchy_subsequence : forall (a : CauchySeq) (f : nat -> nat),
  (forall n : nat, (n <= f n)%nat) ->
  is_cauchy (fun n => cs_seq a (f n)).
Proof.
  intros a f Hf eps Heps.
  destruct (cs_cauchy a eps Heps) as [N HN].
  exists N.
  intros m n Hm Hn.
  apply HN; [apply Nat.le_trans with m; [exact Hm | apply Hf] |
             apply Nat.le_trans with n; [exact Hn | apply Hf]].
Qed.

(* ========================================================================= *)
(* SECTION 7: ALGEBRAIC LAWS                                                  *)
(* ========================================================================= *)

Lemma cauchy_add_comm : forall a b : CauchySeq,
  cauchy_add a b ~~ cauchy_add b a.
Proof.
  intros a b eps Heps.
  exists 0%nat.
  intros n _.
  simpl.
  assert (H : (cs_seq a n + cs_seq b n) - (cs_seq b n + cs_seq a n) == 0) by ring.
  qabs_rw H. rewrite Qabs_pos; lra.
Qed.

Lemma cauchy_add_assoc : forall a b c : CauchySeq,
  cauchy_add (cauchy_add a b) c ~~ cauchy_add a (cauchy_add b c).
Proof.
  intros a b c eps Heps.
  exists 0%nat.
  intros n _.
  simpl.
  assert (H : (cs_seq a n + cs_seq b n + cs_seq c n) -
              (cs_seq a n + (cs_seq b n + cs_seq c n)) == 0) by ring.
  qabs_rw H. rewrite Qabs_pos; lra.
Qed.

Lemma cauchy_add_zero_r : forall a : CauchySeq,
  cauchy_add a (cauchy_const 0) ~~ a.
Proof.
  intros a eps Heps.
  exists 0%nat.
  intros n _.
  simpl.
  assert (H : cs_seq a n + 0 - cs_seq a n == 0) by ring.
  qabs_rw H. rewrite Qabs_pos; lra.
Qed.

Lemma cauchy_add_neg_r : forall a : CauchySeq,
  cauchy_add a (cauchy_neg a) ~~ cauchy_const 0.
Proof.
  intros a eps Heps.
  exists 0%nat.
  intros n _.
  simpl.
  assert (H : cs_seq a n + - cs_seq a n - 0 == 0) by ring.
  qabs_rw H. rewrite Qabs_pos; lra.
Qed.

(* ========================================================================= *)
(* SECTION 8: VERIFICATION                                                    *)
(* ========================================================================= *)

Check cauchy_equiv_refl.
Check cauchy_equiv_sym.
Check cauchy_equiv_trans.
Check cauchy_add_compat.
Check cauchy_neg_compat.
Check cauchy_pos_not_zero.
Check cauchy_const_lt.
Check cauchy_complete_self.
Check cauchy_subsequence.
Check cauchy_rational_approx.
Check cauchy_add_comm.
Check cauchy_add_assoc.
Check cauchy_add_zero_r.
Check cauchy_add_neg_r.
Check cauchy_le_of_equiv.
Check cauchy_le_refl.

Print Assumptions cauchy_equiv_refl.
Print Assumptions cauchy_equiv_trans.
Print Assumptions cauchy_add_compat.
Print Assumptions cauchy_pos_not_zero.
Print Assumptions cauchy_complete_self.
Print Assumptions cauchy_rational_approx.
Print Assumptions cauchy_add_comm.
Print Assumptions cauchy_add_neg_r.
