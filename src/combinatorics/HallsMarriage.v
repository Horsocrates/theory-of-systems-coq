(* ========================================================================= *)
(*       SYSTEM OF DISTINCT REPRESENTATIVES (SDR) VIA L5                    *)
(*                                                                          *)
(*  HALL'S MARRIAGE THEOREM (classical):                                    *)
(*    A finite family of finite sets {S_1, ..., S_n} has a system of       *)
(*    distinct representatives (SDR) iff Hall's condition holds:           *)
(*       for every I ⊆ [n], |⋃_{i ∈ I} S_i| >= |I|.                       *)
(*                                                                          *)
(*  THIS FILE'S CONTRIBUTION:                                               *)
(*    A constructive SDR algorithm via L5 (smallest unused element) and    *)
(*    the proof that it succeeds under a STRONG HALL CONDITION:            *)
(*       |S_i| > i (each set has more elements than its index).            *)
(*                                                                          *)
(*  L5 ROLE:                                                                *)
(*    At each step, pick the SMALLEST element of S_i not yet used. This    *)
(*    is the canonical L5/μ-choice. The strong Hall condition guarantees  *)
(*    that such an element always exists via pigeonhole.                  *)
(*                                                                          *)
(*  CLASSICAL Hall: requires augmenting paths or defect theorem.           *)
(*  Future file: [HallFull.v] develops the general Hall via L5 + descent. *)
(*                                                                          *)
(*  E/R/R DECOMPOSITION:                                                    *)
(*    Elements (L1):  natural numbers (representatives).                  *)
(*    Roles (L1):     each set S_i assigns a role to one representative.  *)
(*    Rules (L2):     SDR injectivity (distinct representatives).        *)
(*    Order (L5):     smallest unused element of S_i is the canonical    *)
(*                    choice at each step.                                 *)
(*    Process (P4):   greedy iteration through sets, bounded by length.   *)
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
(*               PART I: SDR DEFINITIONS                                     *)
(* ========================================================================= *)

(** An SDR for sets [S_1, ..., S_n] is a list [x_1, ..., x_n] with
    x_i ∈ S_i and all x_i distinct. *)
Definition is_sdr (sets : list (list nat)) (rep : list nat) : Prop :=
  length rep = length sets /\
  NoDup rep /\
  (forall i, i < length sets -> In (nth i rep 0) (nth i sets [])).

(** Boolean check: is x in list l? *)
Fixpoint in_list (x : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | y :: rest => if Nat.eqb x y then true else in_list x rest
  end.

Lemma in_list_iff : forall x l, in_list x l = true <-> In x l.
Proof.
  intros x l. induction l as [|y rest IH]; cbn.
  - split; [discriminate | contradiction].
  - destruct (Nat.eqb_spec x y).
    + subst y. split; intros; [left; reflexivity | reflexivity].
    + rewrite IH. split.
      * intros H. right. exact H.
      * intros [Heq|H]; [congruence | exact H].
Qed.

(** Helper: every element of a list is ≤ fold_right Nat.max 0 l. *)
Lemma fold_right_max_le : forall (l : list nat) (x : nat),
  In x l -> x <= fold_right Nat.max 0 l.
Proof.
  intros l x. induction l as [|y rest IH]; cbn.
  - contradiction.
  - intros [Heq|Hin].
    + subst y. lia.
    + specialize (IH Hin). lia.
Qed.

(** Removing u from a NoDup list containing u reduces length by 1. *)
Lemma remove_NoDup_length : forall (u : nat) (l : list nat),
  NoDup l -> In u l -> length (remove Nat.eq_dec u l) = length l - 1.
Proof.
  intros u l Hnd Hin.
  induction Hnd as [|y rest Hy_not Hnd' IH]; [contradiction|].
  cbn. destruct (Nat.eq_dec u y) as [Heq|Hne].
  - subst y.
    assert (Hrem_eq : remove Nat.eq_dec u rest = rest).
    { clear -Hy_not. induction rest as [|z rest IH']; cbn; [reflexivity|].
      destruct (Nat.eq_dec u z) as [Heq|Hne].
      - subst. exfalso. apply Hy_not. left. reflexivity.
      - f_equal. apply IH'. intros Hin'. apply Hy_not. right. exact Hin'. }
    rewrite Hrem_eq. cbn. lia.
  - destruct Hin as [Heq|Hin']; [congruence|].
    cbn. specialize (IH Hin').
    (* IH: length (remove u rest) = length rest - 1.
       Goal: S (length (remove u rest)) = S (length rest) - 1.
       Since In u rest, rest is non-empty, length rest >= 1. *)
    assert (Hrest_pos : length rest >= 1).
    { destruct rest as [|z rest']; cbn; [contradiction|lia]. }
    lia.
Qed.

(** Removing u from a NoDup list yields a NoDup list. *)
Lemma remove_NoDup_preserves : forall (u : nat) (l : list nat),
  NoDup l -> NoDup (remove Nat.eq_dec u l).
Proof.
  intros u l Hnd.
  induction Hnd as [|y rest Hy_not Hnd' IH]; cbn; [constructor|].
  destruct (Nat.eq_dec u y) as [_|_]; [exact IH|].
  constructor.
  - intros Hin. apply in_remove in Hin. destruct Hin as [Hin _]. contradiction.
  - exact IH.
Qed.

(* ========================================================================= *)
(*               PART II: L5 — SMALLEST UNUSED ELEMENT                      *)
(* ========================================================================= *)

(** Find the smallest element of s that is NOT in used.
    L5/μ-search bounded by max(s). *)
Definition find_unused (s used : list nat) : option nat :=
  let max_val := fold_right Nat.max 0 s in
  mu_le (fun x => andb (in_list x s) (negb (in_list x used))) max_val.

(** find_unused returns Some x iff x is the smallest x ≤ max(s)
    with x ∈ s and x ∉ used. *)
Lemma find_unused_some_iff : forall s used x,
  find_unused s used = Some x <->
  (x <= fold_right Nat.max 0 s /\
   In x s /\ ~ In x used /\
   (forall j, j < x -> ~ In j s \/ In j used)).
Proof.
  intros s used x. unfold find_unused.
  rewrite mu_le_some_iff. split.
  - intros [Hle [Hp Hno]].
    apply Bool.andb_true_iff in Hp.
    destruct Hp as [Hin_s Hnot_used].
    apply in_list_iff in Hin_s.
    apply Bool.negb_true_iff in Hnot_used.
    rewrite <- Bool.not_true_iff_false in Hnot_used.
    rewrite in_list_iff in Hnot_used.
    repeat split; try assumption.
    intros j Hj. specialize (Hno j Hj).
    apply Bool.andb_false_iff in Hno.
    destruct Hno as [Hs_false | Hused_true].
    + left. intros Hin_j_s. apply in_list_iff in Hin_j_s. congruence.
    + right. apply Bool.negb_false_iff in Hused_true.
      apply in_list_iff. exact Hused_true.
  - intros [Hle [Hin_s [Hnot_used Hno]]].
    repeat split; try assumption.
    + apply Bool.andb_true_iff. split.
      * apply in_list_iff. exact Hin_s.
      * apply Bool.negb_true_iff.
        destruct (in_list x used) eqn:Heq; [|reflexivity].
        exfalso. apply Hnot_used. apply in_list_iff. exact Heq.
    + intros j Hj. specialize (Hno j Hj).
      apply Bool.andb_false_iff.
      destruct Hno as [Hnot_s | Hused].
      * left. destruct (in_list j s) eqn:Heq; [|reflexivity].
        apply in_list_iff in Heq. contradiction.
      * right. apply Bool.negb_false_iff. apply in_list_iff. exact Hused.
Qed.

(** find_unused returns None iff every element of s is in used. *)
Lemma find_unused_none_iff : forall s used,
  find_unused s used = None <->
  (forall x, In x s -> In x used).
Proof.
  intros s used. unfold find_unused.
  rewrite mu_le_none_iff. split.
  - intros Hall x Hin_s.
    pose proof (fold_right_max_le s x Hin_s) as Hx_le.
    specialize (Hall x Hx_le).
    apply Bool.andb_false_iff in Hall.
    destruct Hall as [Hs_false | Hused_true].
    + apply in_list_iff in Hin_s. congruence.
    + apply Bool.negb_false_iff in Hused_true.
      apply in_list_iff. exact Hused_true.
  - intros Hall x Hx_le.
    apply Bool.andb_false_iff.
    destruct (in_list x s) eqn:Hs_eq; [|left; reflexivity].
    apply in_list_iff in Hs_eq. specialize (Hall x Hs_eq).
    right. apply Bool.negb_false_iff. apply in_list_iff. exact Hall.
Qed.

(* ========================================================================= *)
(*               PART III: GREEDY SDR ALGORITHM                              *)
(* ========================================================================= *)

(** Greedy SDR: process sets one by one, pick smallest unused. *)
Fixpoint greedy_sdr_aux (sets : list (list nat)) (used : list nat) : option (list nat) :=
  match sets with
  | [] => Some []
  | s :: rest =>
      match find_unused s used with
      | Some x =>
          match greedy_sdr_aux rest (x :: used) with
          | Some result => Some (x :: result)
          | None => None
          end
      | None => None
      end
  end.

Definition greedy_sdr (sets : list (list nat)) : option (list nat) :=
  greedy_sdr_aux sets [].

(** Examples. *)
Example greedy_sdr_simple :
  greedy_sdr [[1; 2]; [2; 3]; [1; 3]] = Some [1; 2; 3].
Proof. reflexivity. Qed.

Example greedy_sdr_fail_when_too_few :
  greedy_sdr [[1]; [1]] = None.
Proof. reflexivity. Qed.

(* ========================================================================= *)
(*               PART IV: CORRECTNESS                                        *)
(* ========================================================================= *)

(** When greedy_sdr_aux returns Some, the result is a valid SDR
    (relative to the used list). *)
Theorem greedy_sdr_aux_correct : forall sets used rep,
  greedy_sdr_aux sets used = Some rep ->
  length rep = length sets /\
  (forall x, In x rep -> ~ In x used) /\
  NoDup rep /\
  (forall i, i < length sets -> In (nth i rep 0) (nth i sets [])).
Proof.
  induction sets as [|s rest IH]; intros used rep Heq.
  - cbn in Heq. inversion Heq. subst rep.
    split; [reflexivity|].
    split; [intros x []|].
    split; [constructor|].
    intros i Hi. cbn in Hi. lia.
  - cbn in Heq.
    destruct (find_unused s used) as [x|] eqn:Hfu; [|discriminate].
    destruct (greedy_sdr_aux rest (x :: used)) as [r|] eqn:Hg; [|discriminate].
    inversion Heq. subst rep.
    specialize (IH (x :: used) r Hg) as [Hlen [Hnot_in_used [Hnd Hnth]]].
    repeat split.
    + cbn. lia.
    + intros y [Hy|Hy].
      * subst y. apply find_unused_some_iff in Hfu.
        destruct Hfu as [_ [_ [Hnot_used _]]]. exact Hnot_used.
      * intros Hin. apply (Hnot_in_used y Hy). right. exact Hin.
    + constructor.
      * intros Hin_x_r.
        specialize (Hnot_in_used x Hin_x_r). apply Hnot_in_used. left. reflexivity.
      * exact Hnd.
    + intros i Hi. destruct i as [|i']; cbn.
      * apply find_unused_some_iff in Hfu.
        destruct Hfu as [_ [Hin_s _]]. exact Hin_s.
      * apply Hnth. cbn in Hi. lia.
Qed.

Theorem greedy_sdr_correct : forall sets rep,
  greedy_sdr sets = Some rep -> is_sdr sets rep.
Proof.
  intros sets rep Heq. unfold greedy_sdr in Heq.
  pose proof (greedy_sdr_aux_correct sets [] rep Heq) as [Hlen [_ [Hnd Hnth]]].
  unfold is_sdr. repeat split; assumption.
Qed.

(* ========================================================================= *)
(*               PART V: PIGEONHOLE FOR UNUSED ELEMENT                       *)
(* ========================================================================= *)

(** A NoDup list of length > |used| has an element not in used. *)
Lemma find_unused_exists_long : forall (used s : list nat),
  NoDup s ->
  length s > length used ->
  exists x : nat, In x s /\ ~ In x used.
Proof.
  induction used as [|u urest IH]; intros s Hnd Hlen.
  - destruct s as [|y rest]; cbn in Hlen; [lia|].
    exists y. split; [left; reflexivity | intros []].
  - destruct (in_dec Nat.eq_dec u s) as [Hu_in|Hu_not].
    + (* Remove u from s; recurse with the reduced s. *)
      set (s' := remove Nat.eq_dec u s).
      assert (Hs'_nd : NoDup s') by (unfold s'; apply remove_NoDup_preserves; exact Hnd).
      assert (Hs'_long : length s' > length urest).
      { unfold s'. rewrite remove_NoDup_length by assumption.
        cbn in Hlen. lia. }
      assert (Hs'_iff : forall x, In x s' <-> In x s /\ x <> u).
      { intros x. unfold s'. split.
        - intros Hx. apply in_remove in Hx. destruct Hx as [Hx Hne]. split; assumption.
        - intros [Hx Hne]. apply in_in_remove; assumption. }
      specialize (IH s' Hs'_nd Hs'_long) as [x [Hx_in_s' Hx_not_urest]].
      exists x. split.
      * apply Hs'_iff in Hx_in_s'. destruct Hx_in_s'; assumption.
      * intros [Hx_eq | Hx_in_urest].
        -- subst x. apply Hs'_iff in Hx_in_s'.
           destruct Hx_in_s' as [_ Hne]. contradiction.
        -- contradiction.
    + (* u not in s. IH applies directly on s. *)
      assert (Hlen' : length s > length urest) by (cbn in Hlen; lia).
      specialize (IH s Hnd Hlen') as [x [Hx_in_s Hx_not_urest]].
      exists x. split; [exact Hx_in_s|].
      intros [Hx_eq | Hx_in_urest].
      * subst x. contradiction.
      * contradiction.
Qed.

(* ========================================================================= *)
(*               PART VI: STRONG HALL IMPLIES SDR EXISTS                    *)
(* ========================================================================= *)

(** Strong Hall: each set S_i has > i distinct elements (NoDup). *)
Definition strong_hall (sets : list (list nat)) : Prop :=
  forall i, i < length sets ->
    NoDup (nth i sets []) /\
    length (nth i sets []) > i.

(** Main theorem: under strong Hall, greedy SDR succeeds. *)
Theorem strong_hall_sdr_exists : forall sets,
  strong_hall sets ->
  exists rep, greedy_sdr sets = Some rep /\ is_sdr sets rep.
Proof.
  intros sets Hsh.
  cut (forall used,
        (forall i, i < length sets -> length (nth i sets []) > length used + i) ->
        (forall i, i < length sets -> NoDup (nth i sets [])) ->
        exists rep, greedy_sdr_aux sets used = Some rep).
  { intros Hcut.
    assert (Hsh' : forall i, i < length sets -> length (nth i sets []) > 0 + i).
    { intros i Hi. cbn. apply Hsh. exact Hi. }
    assert (Hnd : forall i, i < length sets -> NoDup (nth i sets [])).
    { intros i Hi. apply Hsh. exact Hi. }
    specialize (Hcut [] Hsh' Hnd) as [rep Hrep].
    exists rep. split; [exact Hrep|].
    apply greedy_sdr_correct. unfold greedy_sdr. exact Hrep. }
  clear Hsh.
  induction sets as [|s rest IH]; intros used Hlen_bnd Hnd_bnd.
  - cbn. exists []. reflexivity.
  - cbn.
    assert (Hs_nd : NoDup s).
    { specialize (Hnd_bnd 0 ltac:(cbn; lia)). cbn in Hnd_bnd. exact Hnd_bnd. }
    assert (Hs_long : length s > length used).
    { specialize (Hlen_bnd 0 ltac:(cbn; lia)). cbn in Hlen_bnd. lia. }
    pose proof (find_unused_exists_long used s Hs_nd Hs_long) as [x [Hx_in_s Hx_not_used]].
    assert (Hfu : exists y, find_unused s used = Some y).
    { destruct (find_unused s used) as [y|] eqn:Hfu.
      - exists y. reflexivity.
      - exfalso.
        pose proof (find_unused_none_iff s used) as [Hfwd _].
        specialize (Hfwd Hfu x Hx_in_s). contradiction. }
    destruct Hfu as [y Hy].
    rewrite Hy.
    assert (Hrec_bnd : forall i, i < length rest ->
                        length (nth i rest []) > length (y :: used) + i).
    { intros i Hi. cbn.
      specialize (Hlen_bnd (S i) ltac:(cbn; lia)).
      cbn in Hlen_bnd. lia. }
    assert (Hrec_nd : forall i, i < length rest -> NoDup (nth i rest [])).
    { intros i Hi. specialize (Hnd_bnd (S i) ltac:(cbn; lia)).
      cbn in Hnd_bnd. exact Hnd_bnd. }
    specialize (IH (y :: used) Hrec_bnd Hrec_nd) as [r Hr].
    rewrite Hr. exists (y :: r). reflexivity.
Qed.

(* ========================================================================= *)
(*               PART VII: NUMERICAL EXAMPLES                                *)
(* ========================================================================= *)

Example sdr_3x3 :
  is_sdr [[1; 2; 3]; [2; 3; 4]; [3; 4; 5]] [1; 2; 3].
Proof.
  apply greedy_sdr_correct. vm_compute. reflexivity.
Qed.

Example strong_hall_sdr_compute :
  greedy_sdr [[1; 2; 3]; [1; 2; 3; 4]; [1; 2; 3; 4; 5]] = Some [1; 2; 3].
Proof. vm_compute. reflexivity. Qed.

(* ========================================================================= *)
(*               PART VIII: ERR + COMMENTARY                                 *)
(* ========================================================================= *)

(**
  THE L5 ROLE IN HALL'S MARRIAGE:

  At each step of greedy SDR, L5 chooses the SMALLEST element of S_i not
  yet used. This is the canonical L5 / μ-choice — no AC, no LEM, just
  search-up-to-bound through a decidable predicate.

  Under the STRONG HALL CONDITION (|S_i| > i with each S_i NoDup), the
  greedy algorithm succeeds by a pigeonhole argument: at step i, |S_i| > i
  but only i elements have been used, so a fresh one exists.

  The STRONG HALL is more restrictive than the CLASSICAL HALL
  (|⋃_{i∈I} S_i| ≥ |I|). The classical proof requires augmenting paths
  (König–Egerváry style) or defect-theorem descent. Both are tractable
  in our framework but require more substantial Coq development —
  deferred to [HallFull.v].

  CONNECTION TO THE PROJECT THESIS:

  Hall's theorem is the CANONICAL MATCHING result. Its L5/μ-greedy form
  illustrates the P4+L5 = ZFC-free mathematics paradigm:
    - P4: finite list of finite sets; bounded greedy iteration.
    - L5: smallest-unused canonical choice.

  Classical "marriage" theorems (Hall, König, Mendelsohn–Dulmage,
  Gale–Shapley stable matching) all reduce to L5/μ-iteration on a
  decidable preference structure. The pillar is consistent.

  WHAT THIS OPENS NEXT (combinatorial pillar):

  - [HallFull.v]: classical Hall theorem via augmenting paths.
  - [GaleShapley.v]: stable matching via L5 iteration; stability theorem.
  - [Dilworth.v]: chain/antichain decomposition via L5.
  - [Mirsky.v]: dual to Dilworth.
  - [Konig.v]: bipartite matching ↔ minimum vertex cover.
  - [Ramsey.v]: extension of existing H53 work.

  Each is L5/μ-canonical: a decidable predicate + a bounded search range.
*)
