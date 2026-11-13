(** * StatusMechanism.v — The status mechanism of chapter I.6 as an automaton;
      a process is never completed

    E/R/R reading (done before coding; audit of Part I of the Mathematics
    volume, chapter I.6, places 13 and 14, 2026-11-13):

    Elements: the values of a process p : nat -> nat passed so far; the state
              of a stage — the position that holds the status of the maximum,
              its value, the positions of the repeated maxima.
    Roles:    the status of a position at a stage: Maximum / RepeatMaximum /
              BaseOnly. The status is a ROLE: it is held by a position at a
              stage and can be lost at a later stage.
    Rules:    Rule 1 — a strict excess passes the status to the new position
              and resets the repeats; Rule 2 — equality adds the position to
              the repeats; otherwise the state is unchanged; step 0 is the
              undeployed system. The state after n steps is determined by the
              state after n-1 steps and the current element.
    Proved:   (1) only step 0 is undeployed; (2) the invariant: the holder's
              value is the greatest of the values passed, held by the first
              position where it is attained; the repeats are exactly the
              later positions with that value; (3) the repeats are reset
              when the maximum changes; (4) the status passes on only at a
              strict excess; (5) the status of the maximum has exactly one
              holder at every stage; (6) the example of the chapter, nine
              stages, by computation; (7) a process of general form is never
              completed: every stage is extended by the next, and no finite
              list holds all the stages.
    P4 diagnostic ("could it be otherwise?"): nothing infinite is used — every
              state is finite and depends on the passed values only; the
              process may continue. Forced: uniqueness of the holder and the
              invariant. NOT forced: the carrier of the values — here nat, as
              in the chapter's example; an arbitrary decidable order is a
              generalization not made here.

    STATUS: 20 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import List Arith Lia PeanoNat.
Import ListNotations.
From ToS Require Import foundation.ProcessP4Synthesis.

(* ========================================================================= *)
(*  1. THE AUTOMATON                                                         *)
(* ========================================================================= *)

(** The state of a stage: the position that holds the status of the maximum,
    its value, and the positions of the repeated maxima (in order of
    appearance). *)
Record StatusState := mkStatusState {
  st_max_pos : nat;
  st_max_val : nat;
  st_repeats : list nat;
}.

(** One step. Rule 1: strict excess — the status passes to the new position
    and the repeats are reset. Rule 2: equality — the position joins the
    repeats. Otherwise the state is unchanged. [None] is step 0: the system
    is not deployed yet. *)
Definition status_step (s : option StatusState) (pos val : nat) : option StatusState :=
  match s with
  | None => Some (mkStatusState pos val [])
  | Some st =>
      if st_max_val st <? val then Some (mkStatusState pos val [])
      else if val =? st_max_val st
           then Some (mkStatusState (st_max_pos st) (st_max_val st) (st_repeats st ++ [pos]))
           else Some st
  end.

(** A process p : nat -> nat; positions are counted from 1, the value at
    position k is p (k-1). The state after n steps is determined by the state
    after n-1 steps and the current element: no completed list of all the
    elements is needed. *)
Fixpoint status_run (p : nat -> nat) (n : nat) : option StatusState :=
  match n with
  | O => None
  | S k => status_step (status_run p k) (S k) (p k)
  end.

Lemma status_step_some : forall s pos val, exists st, status_step s pos val = Some st.
Proof.
  intros [st |] pos val; simpl.
  - destruct (st_max_val st <? val); [eexists; reflexivity |].
    destruct (val =? st_max_val st); eexists; reflexivity.
  - eexists; reflexivity.
Qed.

(** Step 0, and only step 0, is the undeployed system. *)
Theorem status_run_none_iff : forall p n, status_run p n = None <-> n = 0.
Proof.
  intros p n. split.
  - destruct n as [| k]; [reflexivity |]. simpl.
    destruct (status_step_some (status_run p k) (S k) (p k)) as [st Hst].
    rewrite Hst. discriminate.
  - intro H. subst. reflexivity.
Qed.

Definition status_inv (p : nat -> nat) (n : nat) (st : StatusState) : Prop :=
  (1 <= st_max_pos st <= n) /\
  p (st_max_pos st - 1) = st_max_val st /\
  (forall k, k < n -> p k <= st_max_val st) /\
  (forall k, k < st_max_pos st - 1 -> p k < st_max_val st) /\
  (forall j, In j (st_repeats st) <->
             (st_max_pos st < j <= n /\ p (j - 1) = st_max_val st)).

Theorem status_run_inv : forall p n st, status_run p n = Some st -> status_inv p n st.
Proof.
  intros p n. induction n as [| n IH]; intros st Hrun.
  - discriminate.
  - simpl in Hrun. destruct (status_run p n) as [st0 |] eqn:Hprev.
    + specialize (IH st0 eq_refl).
      destruct IH as [Hpos [Hval [Hmax [Hfirst Hrep]]]].
      simpl in Hrun.
      destruct (st_max_val st0 <? p n) eqn:Hlt.
      * (* Rule 1 *)
        apply Nat.ltb_lt in Hlt. injection Hrun as Hrun. subst st.
        unfold status_inv. simpl.
        replace (n - 0) with n by lia.
        split; [lia |]. split; [reflexivity |]. split; [| split].
        -- intros k Hk. destruct (Nat.eq_dec k n) as [-> | Hne]; [lia |].
           assert (k < n) by lia. specialize (Hmax k H). lia.
        -- intros k Hk. specialize (Hmax k Hk). lia.
        -- intro j. split; [intros [] | intros [Hj _]; lia].
      * apply Nat.ltb_ge in Hlt.
        destruct (p n =? st_max_val st0) eqn:Heq.
        -- (* Rule 2 *)
           apply Nat.eqb_eq in Heq. injection Hrun as Hrun. subst st.
           unfold status_inv. simpl.
           split; [lia |]. split; [exact Hval |]. split; [| split].
           ++ intros k Hk. destruct (Nat.eq_dec k n) as [-> | Hne]; [lia |].
              apply Hmax. lia.
           ++ exact Hfirst.
           ++ intro j. rewrite in_app_iff. split.
              ** intros [Hin | [Hj | []]].
                 --- apply Hrep in Hin. destruct Hin as [Hb Hv]. split; [lia | exact Hv].
                 --- subst j. split; [lia |].
                     replace (S n - 1) with n by lia. exact Heq.
              ** intros [Hb Hv]. destruct (Nat.eq_dec j (S n)) as [-> | Hne].
                 --- right. left. reflexivity.
                 --- left. apply Hrep. split; [lia | exact Hv].
        -- (* neither rule fires *)
           apply Nat.eqb_neq in Heq. injection Hrun as Hrun. subst st.
           unfold status_inv.
           split; [lia |]. split; [exact Hval |]. split; [| split].
           ++ intros k Hk. destruct (Nat.eq_dec k n) as [-> | Hne]; [lia |].
              apply Hmax. lia.
           ++ exact Hfirst.
           ++ intro j. split.
              ** intro Hin. apply Hrep in Hin. destruct Hin as [Hb Hv]. split; [lia | exact Hv].
              ** intros [Hb Hv]. destruct (Nat.eq_dec j (S n)) as [-> | Hne].
                 --- exfalso. replace (S n - 1) with n in Hv by lia. contradiction.
                 --- apply Hrep. split; [lia | exact Hv].
    + (* the previous state is step 0 *)
      apply status_run_none_iff in Hprev. subst n.
      simpl in Hrun. injection Hrun as Hrun. subst st.
      unfold status_inv. simpl.
      split; [lia |]. split; [reflexivity |]. split; [| split].
      * intros k Hk. assert (k = 0) by lia. subst. lia.
      * intros k Hk. lia.
      * intro j. split; [intros [] | intros [Hj _]; lia].
Qed.

(** The current maximum is the greatest of the values passed so far, and it is
    held by the FIRST position at which it is attained. *)
Corollary status_max_is_maximum : forall p n st, status_run p n = Some st ->
  (forall k, k < n -> p k <= st_max_val st) /\
  p (st_max_pos st - 1) = st_max_val st /\
  (forall k, k < st_max_pos st - 1 -> p k < st_max_val st).
Proof.
  intros p n st H. destruct (status_run_inv p n st H) as [_ [Hv [Hm [Hf _]]]].
  split; [exact Hm | split; [exact Hv | exact Hf]].
Qed.

(** The repeated maxima are exactly the positions after the holder whose value
    equals the current maximum. *)
Corollary status_repeats_exact : forall p n st, status_run p n = Some st ->
  forall j, In j (st_repeats st) <->
            (st_max_pos st < j <= n /\ p (j - 1) = st_max_val st).
Proof.
  intros p n st H. destruct (status_run_inv p n st H) as [_ [_ [_ [_ Hr]]]]. exact Hr.
Qed.

(** The repeats are reset when the maximum changes. *)
Theorem status_reset_on_new_max : forall p n st,
  status_run p n = Some st -> st_max_val st < p n ->
  status_run p (S n) = Some (mkStatusState (S n) (p n) []).
Proof.
  intros p n st H Hlt. simpl. rewrite H. simpl.
  apply Nat.ltb_lt in Hlt. rewrite Hlt. reflexivity.
Qed.

(** The status passes on only at a strict excess. *)
Theorem status_holder_changes_only_on_strict_excess : forall p n st st',
  status_run p n = Some st -> status_run p (S n) = Some st' ->
  st_max_pos st' <> st_max_pos st -> st_max_val st < p n.
Proof.
  intros p n st st' H H' Hne. simpl in H'. rewrite H in H'. simpl in H'.
  destruct (st_max_val st <? p n) eqn:Hlt.
  - apply Nat.ltb_lt. exact Hlt.
  - exfalso. destruct (p n =? st_max_val st); injection H' as H'; subst st';
      simpl in Hne; apply Hne; reflexivity.
Qed.

(** The status of a position at a stage. *)
Inductive StatusRole := RoleMaximum | RoleRepeatMaximum | RoleBaseOnly.

Definition status_of (st : StatusState) (j : nat) : StatusRole :=
  if j =? st_max_pos st then RoleMaximum
  else if existsb (Nat.eqb j) (st_repeats st) then RoleRepeatMaximum
  else RoleBaseOnly.

(** At every stage the status of the maximum has exactly one holder. *)
Theorem status_maximum_unique : forall st j,
  status_of st j = RoleMaximum <-> j = st_max_pos st.
Proof.
  intros st j. unfold status_of. split.
  - destruct (j =? st_max_pos st) eqn:E.
    + intros _. apply Nat.eqb_eq. exact E.
    + destruct (existsb (Nat.eqb j) (st_repeats st)); discriminate.
  - intro H. subst. rewrite Nat.eqb_refl. reflexivity.
Qed.

(** The example of chapter I.6: 1, 3, 2, 5, 4, 5, 7, 7 — nine stages. *)
Definition chapter_example (k : nat) : nat := nth k [1; 3; 2; 5; 4; 5; 7; 7] 0.

Lemma example_stage_0 : status_run chapter_example 0 = None.
Proof. reflexivity. Qed.
Lemma example_stage_1 : status_run chapter_example 1 = Some (mkStatusState 1 1 []).
Proof. reflexivity. Qed.
Lemma example_stage_2 : status_run chapter_example 2 = Some (mkStatusState 2 3 []).
Proof. reflexivity. Qed.
Lemma example_stage_3 : status_run chapter_example 3 = Some (mkStatusState 2 3 []).
Proof. reflexivity. Qed.
Lemma example_stage_4 : status_run chapter_example 4 = Some (mkStatusState 4 5 []).
Proof. reflexivity. Qed.
Lemma example_stage_5 : status_run chapter_example 5 = Some (mkStatusState 4 5 []).
Proof. reflexivity. Qed.
Lemma example_stage_6 : status_run chapter_example 6 = Some (mkStatusState 4 5 [6]).
Proof. reflexivity. Qed.
Lemma example_stage_7 : status_run chapter_example 7 = Some (mkStatusState 7 7 []).
Proof. reflexivity. Qed.
Lemma example_stage_8 : status_run chapter_example 8 = Some (mkStatusState 7 7 [8]).
Proof. reflexivity. Qed.

(** The sixth element: a repeated maximum at step 6, the status lost at step 7. *)
Lemma example_sixth_gains_and_loses :
  (exists st6, status_run chapter_example 6 = Some st6 /\ status_of st6 6 = RoleRepeatMaximum) /\
  (exists st7, status_run chapter_example 7 = Some st7 /\ status_of st7 6 = RoleBaseOnly).
Proof.
  split; eexists; (split; [reflexivity | reflexivity]).
Qed.

(* ========================================================================= *)
(*  2. A PROCESS IS NEVER COMPLETED                                          *)
(* ========================================================================= *)

(** Every stage of a process of general form is extended by the next one. *)
Theorem gen_process_stage_extends : forall (A : Type) (p : GenProcess A) (n : nat),
  gp_prefix p (S n) = gp_prefix p n ++ [gp_observe p n].
Proof. intros. reflexivity. Qed.

(** No finite list holds all the stages: for every list there is a stage
    longer than it. "Infinity is a process, not an object" as a theorem
    about [GenProcess]. *)
Theorem gen_process_never_completed : forall (A : Type) (p : GenProcess A) (l : list A),
  exists n, length l < length (gp_prefix p n).
Proof.
  intros A p l. exists (S (length l)). rewrite gp_prefix_length. lia.
Qed.
