(* ========================================================================= *)
(*       DISCRETE BOLZANO–WEIERSTRASS VIA L5                                *)
(*                                                                          *)
(*  CLASSICAL BW: every bounded sequence of reals has a convergent          *)
(*  subsequence.                                                            *)
(*                                                                          *)
(*  THIS FILE'S DISCRETE VERSION:                                           *)
(*    Any bounded sequence of natural numbers admits repeats — i.e., the   *)
(*    pigeonhole guarantees that M+2 indices into M+1 buckets collide.     *)
(*    The L5/μ-search finds the SMALLEST such collision (smallest j with  *)
(*    a previous index i < j of equal value).                             *)
(*                                                                          *)
(*  THE UNIFICATION (with existing project compactness work):              *)
(*    [ShrinkingIntervals_ERR.v]: smallest index where interval shrinks.   *)
(*    [EVT_ERR.v]: largest value achieved by a function.                  *)
(*    [HeineBorel_ERR.v]: smallest finite subcover.                       *)
(*    [ErdosSzekeres.v]: pigeonhole via μ-search.                          *)
(*    THIS file: bounded sequences have constant pairs via μ-search.      *)
(*                                                                          *)
(*  All are the same L5/μ pattern: bounded range + decidable predicate +  *)
(*  μ-search = constructive extraction.                                    *)
(*                                                                          *)
(*  WHAT THIS FILE PROVES:                                                  *)
(*                                                                          *)
(*    [count_occurrences]          — count hits of a value in [0, N).     *)
(*    [count_occurrences_bound]    — count ≤ N.                           *)
(*    [count_occurrences_monotone] — monotone in N.                       *)
(*    [injection_bound]            — injection [0, n) → [0, m) ⟹ n ≤ m.   *)
(*    [bounded_seq_const_pair]     — bounded nat seq has equal pair via L5.*)
(*    [find_next_occurrence]       — L5 next-occurrence extraction.       *)
(*    [find_next_occurrence_some]  — its correctness.                    *)
(*                                                                          *)
(*  E/R/R DECOMPOSITION:                                                    *)
(*    Elements (L1):  natural-number values bounded by M.                 *)
(*    Roles (L1):     value-indexed bucket assignment.                   *)
(*    Rules (L2):     decidability of (a n = v) for any n, v.            *)
(*    Order (L5):     smallest collision index, smallest next occurrence.*)
(*    Process (P4):   subseq built incrementally, no actual ∞.            *)
(*                                                                          *)
(*  CONTENT: 0 Admitted, 0 axioms.                                          *)
(* ========================================================================= *)

From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From ToS Require Import cs.MuRecursion.
Import ListNotations.

Open Scope nat_scope.

(* ========================================================================= *)
(*               PART I: COUNTING OCCURRENCES                               *)
(* ========================================================================= *)

(** Count how many i ∈ [0, N) have a i = v. *)
Fixpoint count_occurrences (a : nat -> nat) (v N : nat) : nat :=
  match N with
  | 0 => 0
  | S k =>
      let prev := count_occurrences a v k in
      if Nat.eqb (a k) v then S prev else prev
  end.

(** count_occurrences ≤ N. *)
Lemma count_occurrences_bound : forall a v N,
  count_occurrences a v N <= N.
Proof.
  intros a v. induction N as [|k IH]; cbn; [lia|].
  destruct (Nat.eqb (a k) v); lia.
Qed.

(** count_occurrences is monotone in N. *)
Lemma count_occurrences_monotone : forall a v N1 N2,
  N1 <= N2 -> count_occurrences a v N1 <= count_occurrences a v N2.
Proof.
  intros a v N1 N2 Hle.
  induction Hle as [|N2 Hle IH]; [lia|].
  cbn. destruct (Nat.eqb (a N2) v); lia.
Qed.

(** Numerical examples. *)
Example count_const_seq : count_occurrences (fun _ => 3) 3 5 = 5.
Proof. reflexivity. Qed.

Example count_alternating : count_occurrences (fun n => n mod 2) 0 10 = 5.
Proof. reflexivity. Qed.

(* ========================================================================= *)
(*               PART II: INJECTION BOUND (PIGEONHOLE HELPER)                *)
(* ========================================================================= *)

(** Helper: every element of a list bounded by m is in seq 0 m. *)
Lemma incl_bounded_seq : forall (l : list nat) (m : nat),
  (forall x, In x l -> x < m) -> incl l (seq 0 m).
Proof.
  intros l m Hbnd x Hx. apply in_seq.
  split; [lia|]. simpl. apply Hbnd. exact Hx.
Qed.

(** Map of an injective function over seq is NoDup. *)
Lemma NoDup_map_seq : forall (f : nat -> nat) (n : nat),
  (forall i j, i < n -> j < n -> f i = f j -> i = j) ->
  NoDup (map f (seq 0 n)).
Proof.
  intros f n Hinj.
  assert (H : forall start cnt,
            start + cnt <= n ->
            NoDup (map f (seq start cnt))).
  { intros start cnt. revert start.
    induction cnt as [|c IH]; intros start Hbnd; cbn; [constructor|].
    constructor.
    - intros Hin. apply in_map_iff in Hin.
      destruct Hin as [j [Hfj Hj_in]].
      apply in_seq in Hj_in.
      assert (Heq : start = j) by (apply Hinj; [lia|lia|symmetry; exact Hfj]).
      lia.
    - apply IH. lia. }
  specialize (H 0 n ltac:(lia)). exact H.
Qed.

(** Injection [0, n) → [0, m) implies n ≤ m. *)
Theorem injection_bound : forall (f : nat -> nat) (n m : nat),
  (forall i, i < n -> f i < m) ->
  (forall i j, i < n -> j < n -> f i = f j -> i = j) ->
  n <= m.
Proof.
  intros f n m Hbnd Hinj.
  set (l := map f (seq 0 n)).
  assert (Hlen : length l = n).
  { unfold l. rewrite length_map, length_seq. reflexivity. }
  assert (Hnd : NoDup l).
  { unfold l. apply NoDup_map_seq. exact Hinj. }
  assert (Hincl : incl l (seq 0 m)).
  { unfold l. apply incl_bounded_seq.
    intros x Hin. apply in_map_iff in Hin.
    destruct Hin as [i [Heq Hi_in]]. apply in_seq in Hi_in.
    rewrite <- Heq. apply Hbnd. lia. }
  pose proof (NoDup_incl_length Hnd Hincl) as Hle.
  rewrite Hlen, length_seq in Hle. exact Hle.
Qed.

(* ========================================================================= *)
(*               PART III: PIGEONHOLE PAIR — L5/μ FORM                       *)
(* ========================================================================= *)

(** From bounded nat sequence (values ≤ M), with M+2 indices, find a collision
    via L5/μ-search. *)
Theorem bounded_seq_const_pair : forall (a : nat -> nat) (M : nat),
  (forall n, n <= S M -> a n <= M) ->
  exists i j, i < j /\ j <= S M /\ a i = a j.
Proof.
  intros a M Hbnd.
  (* For j = S k, search i ∈ [0, k] for a match. j = 0 has no predecessor. *)
  set (has_match := fun j =>
    match j with
    | 0 => false
    | S k =>
        match mu_le (fun i => Nat.eqb (a i) (a (S k))) k with
        | Some _ => true
        | None => false
        end
    end).
  destruct (mu_le_dec has_match (S M)) as [[j [Hj_le [Hj_p _]]] | Hno].
  - (* Found smallest j with a match. j must be ≥ 1. *)
    unfold has_match in Hj_p.
    destruct j as [|j']; [discriminate|].
    destruct (mu_le _ _) as [i|] eqn:Hmu; [|discriminate].
    apply mu_le_some_iff in Hmu.
    destruct Hmu as [Hi_le [Hi_eq _]].
    apply Nat.eqb_eq in Hi_eq.
    exists i, (S j'). split; [lia|]. split; [exact Hj_le|exact Hi_eq].
  - (* No j has a match. Show contradiction via injection_bound. *)
    exfalso.
    assert (Hinj : forall i k, i <= S M -> k <= S M -> i <> k -> a i <> a k).
    { intros i k Hi Hk Hne Heq.
      destruct (Nat.lt_total i k) as [Hlt|[Heq2|Hgt]].
      - specialize (Hno k Hk).
        unfold has_match in Hno.
        destruct k as [|k']; [lia|].
        destruct (mu_le _ _) as [w|] eqn:Hmu; [discriminate|].
        pose proof (mu_le_none_iff (fun i => Nat.eqb (a i) (a (S k'))) k') as [Hfwd _].
        specialize (Hfwd Hmu i ltac:(lia)).
        apply Nat.eqb_neq in Hfwd. congruence.
      - lia.
      - specialize (Hno i Hi).
        unfold has_match in Hno.
        destruct i as [|i']; [lia|].
        destruct (mu_le _ _) as [w|] eqn:Hmu; [discriminate|].
        pose proof (mu_le_none_iff (fun j => Nat.eqb (a j) (a (S i'))) i') as [Hfwd _].
        specialize (Hfwd Hmu k ltac:(lia)).
        apply Nat.eqb_neq in Hfwd. congruence. }
    assert (Hbnd' : forall i, i < S (S M) -> a i < S M).
    { intros i Hi. apply Nat.lt_succ_r. apply Hbnd. lia. }
    assert (Hinj' : forall i k, i < S (S M) -> k < S (S M) -> a i = a k -> i = k).
    { intros i k Hi Hk Hf.
      destruct (Nat.eq_dec i k); [assumption|].
      exfalso. apply (Hinj i k); try lia. }
    pose proof (injection_bound a (S (S M)) (S M) Hbnd' Hinj') as Hcontra. lia.
Qed.

(* ========================================================================= *)
(*               PART IV: FINDING NEXT OCCURRENCE VIA L5                     *)
(* ========================================================================= *)

(** Find the smallest index n ≥ start with a n = v, up to bound. *)
Definition find_next_occurrence (a : nat -> nat) (v start bound : nat) : option nat :=
  match mu_le (fun k => Nat.eqb (a (start + k)) v) (bound - start) with
  | Some k => Some (start + k)
  | None => None
  end.

Lemma find_next_occurrence_some : forall a v start bound n,
  find_next_occurrence a v start bound = Some n ->
  start <= n /\ a n = v.
Proof.
  intros a v start bound n Hf. unfold find_next_occurrence in Hf.
  destruct (mu_le _ _) as [k|] eqn:Hmu; [|discriminate].
  inversion Hf. subst n.
  apply mu_le_some_iff in Hmu.
  destruct Hmu as [Hk_le [Heqv _]].
  apply Nat.eqb_eq in Heqv.
  split; [lia|exact Heqv].
Qed.

(** Numerical examples. *)
Example find_next_const :
  find_next_occurrence (fun n => n mod 3) 0 1 10 = Some 3.
Proof. vm_compute. reflexivity. Qed.

Example find_next_none :
  find_next_occurrence (fun _ => 5) 0 1 10 = None.
Proof. vm_compute. reflexivity. Qed.

(* ========================================================================= *)
(*               PART V: SEQUENTIAL COMPACTNESS — DISCRETE BW                *)
(* ========================================================================= *)

(** Discrete BW (sequential form): a bounded sequence has a value that
    occurs at TWO indices within the first M+2 positions. This is the
    most basic form of "compactness" for discrete sequences. *)
Corollary discrete_BW_pair : forall (a : nat -> nat) (M : nat),
  (forall n, a n <= M) ->
  exists v i j, i < j /\ j <= S M /\ a i = v /\ a j = v.
Proof.
  intros a M Hbnd.
  assert (Hbnd' : forall n, n <= S M -> a n <= M) by (intros n _; apply Hbnd).
  pose proof (bounded_seq_const_pair a M Hbnd') as [i [j [Hij [Hj Hieq]]]].
  exists (a i), i, j. split; [exact Hij|].
  split; [exact Hj|]. split; [reflexivity|symmetry; exact Hieq].
Qed.

(* ========================================================================= *)
(*               PART VI: ERR + COMMENTARY                                   *)
(* ========================================================================= *)

(**
  THE L5 STRUCTURE OF DISCRETE BW:

  Classical BW: every bounded real sequence has a convergent subsequence.

  Discrete BW (this file): every bounded nat sequence has a 2-element
  constant subsequence within its first M+2 indices. The proof is direct
  pigeonhole + L5/μ-search for the SMALLEST collision index j.

  L5/μ ROLES IN THE PROOF:

  (1) [bounded_seq_const_pair]: μ over (has_match j) finds the smallest j
      with a previous index of equal value. Inside, μ over (Nat.eqb (a i) (a j))
      finds the smallest such i.

  (2) [find_next_occurrence]: L5/μ finds the smallest index ≥ start with
      a given value. This is the canonical "next occurrence" extraction
      — would be the building block for K-element subseq construction.

  (3) [injection_bound]: classical pigeonhole, proved via NoDup_incl_length
      (no μ-search needed for the bound itself).

  CONNECTION TO COMPACTNESS PILLAR:

  This file's L5 structure is the SAME as those in the existing
  compactness files:
    - [ShrinkingIntervals_ERR.v]: smallest index where the interval
      shrinks below ε.
    - [EVT_ERR.v]: largest value achieved by the function.
    - [HeineBorel_ERR.v]: smallest finite subcover.
    - [ErdosSzekeres.v]: smallest collision in pair-encoded sequence.

  All are L5/μ over a bounded space, with a decidable predicate. The
  COMPACTNESS PILLAR is unified: every constructive compactness result
  is an L5/μ extraction.

  WHY THIS UNIFIES THINGS:

  Classical proofs of BW, EVT, IVT, Heine–Borel use different techniques:
  nested intervals, sup/inf existence, open-cover arguments, sequential
  compactness equivalences. In our framework, they are all the SAME
  PATTERN:

    decidable predicate + bounded range + L5/μ-search
    = constructive extraction of the desired witness.

  This is the project thesis at its sharpest: P4 (bounded range as
  process) + L5 (smallest selection) = real analysis without ZFC.

  WHAT THIS OPENS NEXT:

  - [BW_K_subseq.v]: K-element constant subsequence via iterated
    find_next_occurrence; the smallest value v with ≥ K occurrences
    in [0, K * (M+1)) is the L5-choice.
  - [BW_RealSeq.v]: lift discrete BW to Cauchy-real sequences via
    ε-quantization. Each ε defines a finite quantized range.
  - [SequentialCompactness.v]: equivalence of BW and sequential
    compactness in our setting.
  - [Compact_Pillar.v]: unifying theorem stating all compactness
    notions coincide via L5/μ.

  In each, the L5/μ pattern is the canonical extraction mechanism.
*)
