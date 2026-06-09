(* ========================================================================= *)
(*           ERDŐS–SZEKERES THEOREM VIA L5                                  *)
(*                                                                          *)
(*  Classical statement: any sequence of n distinct elements of length      *)
(*  > r * s contains a strictly increasing subsequence of length r + 1 OR   *)
(*  a strictly decreasing subsequence of length s + 1.                     *)
(*                                                                          *)
(*  Standard proof: label each position i with the pair                    *)
(*    (a_i, d_i) := (longest inc subseq ending at i,                       *)
(*                   longest dec subseq ending at i).                       *)
(*  These pairs are pairwise distinct (the order at positions i < j        *)
(*  forces strict increase in either a or d). With r * s + 1 positions     *)
(*  but only r * s pairs in [1, r] × [1, s], some pair exceeds bounds.    *)
(*                                                                          *)
(*  THIS FILE'S STRATEGY:                                                   *)
(*    (1) Prove FINITE PIGEONHOLE via L5 (the constructive core).         *)
(*    (2) Prove ABSTRACT Erdős–Szekeres: assuming labels a, d satisfy      *)
(*        the strict-distinct-pair property, the bound holds.              *)
(*  The CONCRETE inc/dec-length DP is referenced in commentary as the      *)
(*  bridge to the classical statement — this is the L5-canonical form.    *)
(*                                                                          *)
(*  E/R/R DECOMPOSITION:                                                    *)
(*    Elements (L1):  positions in a sequence (finite indexed nat range). *)
(*    Roles (L1):     pair-label (a_i, d_i) ∈ ℕ × ℕ.                      *)
(*    Rules (L2):     strict-distinct-pair: i ≠ j ⇒ (a_i,d_i) ≠ (a_j,d_j).*)
(*    Order (L5):     smallest position where a label exceeds its bound.  *)
(*    Process (P4):   finite range, no completed infinity.                *)
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
(*               PART I: NoDup HELPERS                                      *)
(* ========================================================================= *)

(** A list whose elements are all bounded by [m] is a subset of seq 0 m. *)
Lemma incl_bounded_seq : forall (l : list nat) (m : nat),
  (forall x, In x l -> x < m) -> incl l (seq 0 m).
Proof.
  intros l m Hbnd x Hx. apply in_seq. split; [lia|]. simpl. apply Hbnd. exact Hx.
Qed.

(** NoDup of map f (seq 0 n) when f is injective on [0, n). *)
Lemma NoDup_map_seq : forall (f : nat -> nat) (n : nat),
  (forall i j, i < n -> j < n -> f i = f j -> i = j) ->
  NoDup (map f (seq 0 n)).
Proof.
  intros f n Hinj.
  assert (H : forall start cnt,
    start + cnt <= n ->
    NoDup (map f (seq start cnt))).
  { intros start cnt. revert start.
    induction cnt as [|c IH]; intros start Hbnd.
    - simpl. constructor.
    - simpl. constructor.
      + intros Hin. apply in_map_iff in Hin.
        destruct Hin as [j [Hfj Hj_in]].
        apply in_seq in Hj_in.
        assert (Heq : start = j).
        { apply Hinj; [lia|lia|symmetry; exact Hfj]. }
        lia.
      + apply IH. lia. }
  specialize (H 0 n ltac:(lia)). exact H.
Qed.

(* ========================================================================= *)
(*               PART II: FINITE PIGEONHOLE VIA L5                          *)
(* ========================================================================= *)

(** THE CORE THEOREM: an injective function f : [0, n) → [0, m) implies n ≤ m. *)
Theorem injective_bound : forall (n m : nat) (f : nat -> nat),
  (forall i, i < n -> f i < m) ->
  (forall i j, i < n -> j < n -> f i = f j -> i = j) ->
  n <= m.
Proof.
  intros n m f Hbnd Hinj.
  set (l := map f (seq 0 n)).
  assert (Hlen : length l = n).
  { unfold l. rewrite length_map, length_seq. reflexivity. }
  assert (Hnd : NoDup l).
  { unfold l. apply NoDup_map_seq.
    intros i j Hi Hj Hf. apply Hinj; assumption. }
  assert (Hincl : incl l (seq 0 m)).
  { unfold l. apply incl_bounded_seq.
    intros x Hin. apply in_map_iff in Hin.
    destruct Hin as [i [Heq Hin_i]]. apply in_seq in Hin_i.
    rewrite <- Heq. apply Hbnd. lia. }
  pose proof (NoDup_incl_length Hnd Hincl) as Hle.
  rewrite Hlen, length_seq in Hle. exact Hle.
Qed.

(** Constructive pigeonhole via L5/μ-search. We search for the smallest
    pair (i, j) with i < j < n and f i = f j. *)

(** Given j, has there been a collision at some i < j? *)
Definition has_prev_collision (f : nat -> nat) (j : nat) : bool :=
  match j with
  | 0 => false
  | S k => match mu_le (fun i => Nat.eqb (f i) (f j)) k with
           | Some _ => true
           | None => false
           end
  end.

(** has_prev_collision is correct. *)
Lemma has_prev_collision_iff : forall f j,
  has_prev_collision f j = true <-> exists i, i < j /\ f i = f j.
Proof.
  intros f j. destruct j as [|k]; cbn.
  - split; [discriminate|]. intros [i [Hi _]]. lia.
  - destruct (mu_le (fun i => Nat.eqb (f i) (f (S k))) k) as [i0|] eqn:Hmu.
    + split.
      * intros _.
        apply mu_le_some_iff in Hmu. destruct Hmu as [Hi0 [Hf0 _]].
        apply Nat.eqb_eq in Hf0. exists i0. split; [lia|exact Hf0].
      * reflexivity.
    + split.
      * discriminate.
      * intros [i [Hi Hf]].
        pose proof (mu_le_none_iff (fun i => Nat.eqb (f i) (f (S k))) k) as [Hfwd _].
        specialize (Hfwd Hmu i ltac:(lia)).
        apply Nat.eqb_neq in Hfwd. congruence.
Qed.

(** First collision position j: smallest j < n with has_prev_collision f j. *)
Definition first_collision_j (f : nat -> nat) (n : nat) : option nat :=
  match n with
  | 0 => None
  | S k => mu_le (has_prev_collision f) k
  end.

(** When n > m and f bounded by m, first_collision_j returns Some witness.
    This is the constructive pigeonhole. *)
Theorem first_collision_j_some : forall n m (f : nat -> nat),
  (forall i, i < n -> f i < m) -> m < n ->
  exists j, first_collision_j f n = Some j /\ j < n /\
            exists i, i < j /\ f i = f j.
Proof.
  intros n m f Hbnd Hlt.
  destruct n as [|k]; [lia|].
  cbn [first_collision_j].
  (* Show that some position in [0, k] has a collision. *)
  assert (Hex : exists j, j <= k /\ has_prev_collision f j = true).
  { (* Suppose not. Then no position has a prev collision, so f|[0, S k] is injective.
       By injective_bound, S k <= m. But m < S k = n. Contradiction. *)
    destruct (mu_le_dec (has_prev_collision f) k) as [[j Hj]|Hno].
    - exists j. destruct Hj as [Hjle [Hjp _]]. split; [exact Hjle|exact Hjp].
    - exfalso.
      assert (Hinj : forall i j, i < S k -> j < S k -> f i = f j -> i = j).
      { intros i j Hi Hj Hf.
        destruct (Nat.lt_trichotomy i j) as [Hij | [Heq | Hij]].
        - exfalso. specialize (Hno j ltac:(lia)).
          assert (Hpc : has_prev_collision f j = true).
          { apply has_prev_collision_iff. exists i. split; assumption. }
          congruence.
        - exact Heq.
        - exfalso. specialize (Hno i ltac:(lia)).
          assert (Hpc : has_prev_collision f i = true).
          { apply has_prev_collision_iff. exists j. split; [lia|symmetry; exact Hf]. }
          congruence. }
      pose proof (injective_bound (S k) m f Hbnd Hinj) as Hsk_le_m. lia. }
  destruct Hex as [j_ex [Hj_ex_le Hj_ex_pc]].
  (* Now mu_le finds the smallest such j. *)
  pose proof (mu_process_finds_smallest (has_prev_collision f) j_ex Hj_ex_pc)
    as [j_min [Hj_min_le [Hj_min_mu [Hj_min_pc _]]]].
  pose proof (mu_le_monotone (has_prev_collision f) j_ex k j_min ltac:(lia) Hj_min_mu) as Hmu_k.
  exists j_min. split; [exact Hmu_k|].
  split; [lia|].
  apply has_prev_collision_iff. exact Hj_min_pc.
Qed.

(** Final pigeonhole statement. *)
Theorem pigeonhole_via_L5 : forall (n m : nat) (f : nat -> nat),
  (forall i, i < n -> f i < m) -> m < n ->
  exists i j, i < j /\ j < n /\ f i = f j.
Proof.
  intros n m f Hbnd Hlt.
  pose proof (first_collision_j_some n m f Hbnd Hlt) as [j [_ [Hjn [i [Hij Hfij]]]]].
  exists i, j. repeat split; assumption.
Qed.

(* ========================================================================= *)
(*               PART III: ABSTRACT ERDŐS–SZEKERES                          *)
(* ========================================================================= *)

(** Encoding pairs (a, b) ∈ [0, r) × [0, s) into [0, r * s). *)
Definition pair_encode (s a b : nat) : nat := a * s + b.

Lemma pair_encode_bound : forall r s a b,
  a < r -> b < s -> pair_encode s a b < r * s.
Proof.
  intros r s a b Ha Hb. unfold pair_encode. nia.
Qed.

Lemma pair_encode_inj : forall s a1 b1 a2 b2,
  b1 < s -> b2 < s ->
  pair_encode s a1 b1 = pair_encode s a2 b2 -> a1 = a2 /\ b1 = b2.
Proof.
  intros s a1 b1 a2 b2 Hb1 Hb2 Heq.
  unfold pair_encode in Heq.
  destruct (Nat.lt_trichotomy a1 a2) as [Hlt | [Heq2 | Hgt]].
  - exfalso. nia.
  - split; [exact Heq2|]. nia.
  - exfalso. nia.
Qed.

(** ABSTRACT ERDŐS–SZEKERES (the central result).

    Given any labeling [a, d : nat → nat] of positions in [0, n) such that
    (a i, d i) ∈ [1, r] × [1, s] and the pair is pair-injective on positions,
    we get n ≤ r * s.

    The CLASSICAL ES theorem is the contrapositive: if n > r * s, then
    NOT both (forall i, a i ≤ r) and (forall i, d i ≤ s), i.e., there's
    a position with a > r (giving inc subseq of length r+1) or d > s
    (giving dec subseq of length s+1). *)
Theorem abstract_erdos_szekeres : forall (n r s : nat) (a d : nat -> nat),
  (forall i, i < n -> 1 <= a i <= r) ->
  (forall i, i < n -> 1 <= d i <= s) ->
  (forall i j, i < n -> j < n -> i <> j -> a i <> a j \/ d i <> d j) ->
  n <= r * s.
Proof.
  intros n r s a d Habnd Hdbnd Hdistinct.
  set (f := fun i => pair_encode s (a i - 1) (d i - 1)).
  apply (injective_bound n (r * s) f).
  - intros i Hi. unfold f. apply pair_encode_bound.
    + pose proof (Habnd i Hi). lia.
    + pose proof (Hdbnd i Hi). lia.
  - intros i j Hi Hj Hf. unfold f in Hf.
    apply pair_encode_inj in Hf.
    + destruct Hf as [Ha Hd].
      destruct (Nat.eq_dec i j) as [Heq|Hne]; [exact Heq|].
      exfalso. specialize (Hdistinct i j Hi Hj Hne).
      pose proof (Habnd i Hi). pose proof (Habnd j Hj).
      pose proof (Hdbnd i Hi). pose proof (Hdbnd j Hj).
      destruct Hdistinct as [Hcontra|Hcontra]; [|lia].
      assert (a i = a j) by lia. congruence.
    + pose proof (Hdbnd i Hi). lia.
    + pose proof (Hdbnd j Hj). lia.
Qed.

(** CONTRAPOSITIVE FORM (classical Erdős–Szekeres):
    if n > r * s then either some i has a i > r or some i has d i > s. *)
Theorem erdos_szekeres_contrapositive : forall (n r s : nat) (a d : nat -> nat),
  n > r * s ->
  (forall i j, i < n -> j < n -> i <> j -> a i <> a j \/ d i <> d j) ->
  (forall i, i < n -> 1 <= a i) ->
  (forall i, i < n -> 1 <= d i) ->
  (exists i, i < n /\ a i > r) \/ (exists i, i < n /\ d i > s).
Proof.
  intros n r s a d Hn_gt Hdistinct Ha_pos Hd_pos.
  destruct (mu_le_dec (fun i => Nat.ltb r (a i)) (n - 1)) as [[i [Hi_le [Hi_p _]]] |Hno_a].
  - left. exists i. split; [lia|]. apply Nat.ltb_lt in Hi_p. lia.
  - destruct (mu_le_dec (fun i => Nat.ltb s (d i)) (n - 1)) as [[j [Hj_le [Hj_p _]]] |Hno_d].
    + right. exists j. split; [lia|]. apply Nat.ltb_lt in Hj_p. lia.
    + exfalso.
      assert (Habnd : forall i, i < n -> 1 <= a i <= r).
      { intros i Hi. specialize (Hno_a i ltac:(lia)). apply Nat.ltb_ge in Hno_a.
        split; [apply Ha_pos; exact Hi | exact Hno_a]. }
      assert (Hdbnd : forall i, i < n -> 1 <= d i <= s).
      { intros i Hi. specialize (Hno_d i ltac:(lia)). apply Nat.ltb_ge in Hno_d.
        split; [apply Hd_pos; exact Hi | exact Hno_d]. }
      pose proof (abstract_erdos_szekeres n r s a d Habnd Hdbnd Hdistinct) as Hle. lia.
Qed.

(* ========================================================================= *)
(*               PART IV: NUMERICAL VERIFICATION                            *)
(* ========================================================================= *)

(** Example: any sequence labeled with (a, d) where labels are bounded by
    (2, 2) and the distinct-pair property holds, has at most 4 positions. *)
Example abstract_es_22 :
  forall (a d : nat -> nat) (n : nat),
    (forall i, i < n -> 1 <= a i <= 2) ->
    (forall i, i < n -> 1 <= d i <= 2) ->
    (forall i j, i < n -> j < n -> i <> j -> a i <> a j \/ d i <> d j) ->
    n <= 4.
Proof.
  intros. pose proof (abstract_erdos_szekeres n 2 2 a d H H0 H1). lia.
Qed.

(** Example: any sequence with > 4 positions labeled with (a, d) ∈ [1,2] x [1,2]
    must have a > 2 or d > 2 (i.e., monotone subseq of length 3). *)
Example es_22_contrapositive :
  forall (a d : nat -> nat) (n : nat),
    n > 4 ->
    (forall i j, i < n -> j < n -> i <> j -> a i <> a j \/ d i <> d j) ->
    (forall i, i < n -> 1 <= a i) ->
    (forall i, i < n -> 1 <= d i) ->
    (exists i, i < n /\ a i > 2) \/ (exists i, i < n /\ d i > 2).
Proof.
  intros. apply erdos_szekeres_contrapositive with (r := 2) (s := 2); assumption.
Qed.

(* ========================================================================= *)
(*               PART V: ERR + COMMENTARY                                   *)
(* ========================================================================= *)

(**
  THE L5 PATTERN VISIBLE IN ES:

  Two distinct uses of L5 in this proof:

  (1) PIGEONHOLE — the constructive core.
      mu_le applied to has_prev_collision finds the SMALLEST position j
      where a value collides with a previous one. This is the L5 witness
      for "such a collision exists" — classical proofs leave the collision
      unspecified; here, it has a canonical position.

  (2) CONTRAPOSITIVE — extracting from violation.
      mu_le applied to "a i > r" finds the SMALLEST position where a label
      exceeds its bound. Similarly for d. This converts the abstract
      "exists i with property" into a CONCRETE constructive witness.

  WHY THIS PROOF IS CONSTRUCTIVE BUT THE CLASSICAL ONE OFTEN ISN'T:

  Classical ES uses LEM in "either there is or there isn't a position with
  a > r". Our L5 version DECIDES which case via mu_le_dec (bool-level),
  so we never invoke classical excluded middle. The witness is constructively
  extracted.

  CONNECTION TO THE CONCRETE INC/DEC LENGTHS:

  The classical statement of ES applies to sequences with the labeling
    a_i := length of longest STRICTLY INC subseq of seq[0..i] ending at i
    d_i := length of longest STRICTLY DEC subseq of seq[0..i] ending at i.

  The KEY PROPERTY is the STRICT-DISTINCT-PAIR claim: for i ≠ j (say i < j),
  (a_i, d_i) ≠ (a_j, d_j). Proof: if seq[i] < seq[j], then a subseq of length
  a_i ending at i can be extended by seq[j], giving a_j ≥ a_i + 1, so a_i ≠ a_j.
  Similarly if seq[i] > seq[j] then d_j ≥ d_i + 1.

  Thus the ABSTRACT ES we proved DIRECTLY APPLIES to (inc_length, dec_length)
  labelings of concrete sequences. The classical statement follows.

  WHY WE LEFT THE CONCRETE inc/dec DP OUT:

  The DP computation of inc_length / dec_length is straightforward (an O(n²)
  fold) but the inductive PROOFS of strict monotonicity are tedious. They
  are MECHANICAL given the abstract theorem above — no new mathematical
  content. The L5 ≡ μ structure of the result is fully visible in the
  abstract theorem.

  WHAT THIS FILE OPENS (next combinatorial steps via L5):

  - DILWORTH (decomposition into antichains via L5 on chain levels).
  - MIRSKY (dual: decomposition into chains via L5 on antichain levels).
  - HALL'S MARRIAGE (smallest unmatched-element selection).
  - GALE–SHAPLEY (L5-iteration on proposal preferences).
  - RAMSEY (R(s, t) — L5 on coloring extensions).
*)
