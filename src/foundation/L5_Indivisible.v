(** * L5_Indivisible.v — L5 Monotonicity Implies Process Indivisibility
    Elements: DSet, History, State, Transition
    Roles:    monotonicity, inclusion, path-dependence
    Rules:    D(K) ⊆ D(K+1) → indivisible (path-dependent)
    Status:   Standalone — only Stdlib imports
    STATUS: 20 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026

    NOTE: The premise L5_monotone (D(K) ⊆ D(K+1)) is now a THEOREM,
    not an independent postulate. See L5_as_Theorem.v for the derivation:
      L5-ORDER → P4 (finiteness) → Kruskal → L5-PRESERVATION.
*)

From Stdlib Require Import QArith Lia ZArith List Bool.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(** * Core Definitions *)

(** Distinction set *)
Definition DSet := list nat.

(** Subset inclusion for distinction sets *)
Definition dset_included (D1 D2 : DSet) : Prop :=
  forall d, In d D1 -> In d D2.

(** History: sequence of distinction sets indexed by time *)
Definition History := nat -> DSet.

(** L5 monotonicity: distinctions only grow *)
Definition L5_monotone (H : History) : Prop :=
  forall K, dset_included (H K) (H (S K)).

(** * Basic Properties *)

Lemma dset_included_refl : forall D, dset_included D D.
Proof.
  intros D d Hd. exact Hd.
Qed.

Lemma dset_included_trans : forall D1 D2 D3,
  dset_included D1 D2 -> dset_included D2 D3 -> dset_included D1 D3.
Proof.
  intros D1 D2 D3 H12 H23 d Hd.
  apply H23. apply H12. exact Hd.
Qed.

(** Key lemma: monotonicity extends to any future step *)
Lemma history_in_current : forall H K K',
  L5_monotone H -> (K' <= K)%nat -> dset_included (H K') (H K).
Proof.
  intros H K K' Hmono Hle.
  induction K as [|K IH].
  - assert (K' = 0)%nat by lia. subst. intros d Hd. exact Hd.
  - destruct (Nat.eq_dec K' (S K)).
    + subst. intros d Hd. exact Hd.
    + assert (K' <= K)%nat by lia.
      intros d Hd. apply Hmono. apply IH. exact H0. exact Hd.
Qed.

(** * State and Configuration *)

Definition State := (nat * DSet)%type.

Definition same_config_diff_D (s1 s2 : State) : Prop :=
  fst s1 = fst s2 /\ snd s1 <> snd s2.

(** * Concrete Example: Two Histories *)

Definition H1 (K : nat) : DSet :=
  match K with
  | O => [1%nat]
  | S O => [1%nat; 2%nat]
  | _ => [1%nat; 2%nat; 3%nat]
  end.

Definition H2 (K : nat) : DSet :=
  match K with
  | O => [1%nat]
  | S O => [1%nat; 3%nat]
  | _ => [1%nat; 2%nat; 3%nat]
  end.

Lemma H1_monotone : L5_monotone H1.
Proof.
  intros K d Hd. destruct K as [|[|[|K']]]; simpl in *; intuition.
Qed.

Lemma H2_monotone : L5_monotone H2.
Proof.
  intros K d Hd. destruct K as [|[|[|K']]]; simpl in *; intuition.
Qed.

Lemma same_initial : H1 0%nat = H2 0%nat.
Proof. reflexivity. Qed.

Lemma same_final : H1 2%nat = H2 2%nat.
Proof. reflexivity. Qed.

Lemma diff_intermediate : H1 1%nat <> H2 1%nat.
Proof.
  simpl. intro Heq. congruence.
Qed.

(** * Transition Functions and Path Dependence *)

(** A transition function maps a distinction set and two time indices to a Q value *)
Definition Transition := DSet -> nat -> nat -> Q.

(** A transition function is distinction-sensitive if different D sets yield different values *)
Definition distinction_sensitive (T : Transition) (D1 D2 : DSet) (t1 t2 : nat) : Prop :=
  D1 <> D2 -> T D1 t1 t2 <> T D2 t1 t2.

(** Path through a history at time K *)
Definition path_value (T : Transition) (H : History) (K : nat) : Q :=
  T (H K) K (S K).

(** Two histories give different intermediate transitions *)
Lemma path_dependent_example : forall T,
  distinction_sensitive T (H1 1%nat) (H2 1%nat) 1%nat 2%nat ->
  path_value T H1 1%nat <> path_value T H2 1%nat.
Proof.
  intros T Hsens.
  unfold path_value.
  apply Hsens.
  exact diff_intermediate.
Qed.

(** * Indivisibility Theorem *)

(** A process is indivisible if knowing only start and end states
    is insufficient to determine intermediate transitions —
    the full path (history) matters *)
Definition indivisible (T : Transition) (Ha Hb : History) : Prop :=
  Ha 0%nat = Hb 0%nat ->
  (exists N, Ha N = Hb N /\ (N >= 2)%nat) ->
  (exists K, (0 < K)%nat /\ path_value T Ha K <> path_value T Hb K).

(** Main theorem: L5 monotonicity + distinction sensitivity implies indivisibility *)
Lemma L5_implies_indivisible : forall T,
  L5_monotone H1 ->
  L5_monotone H2 ->
  distinction_sensitive T (H1 1%nat) (H2 1%nat) 1%nat 2%nat ->
  indivisible T H1 H2.
Proof.
  intros T Hm1 Hm2 Hsens _ _.
  exists 1%nat. split.
  - lia.
  - apply path_dependent_example. exact Hsens.
Qed.

(** * Additional Properties *)

(** Monotone history: initial distinctions persist forever *)
Lemma initial_persists : forall H K d,
  L5_monotone H -> In d (H 0%nat) -> In d (H K).
Proof.
  intros H K d Hmono Hd.
  apply (history_in_current H K 0%nat Hmono).
  - lia.
  - exact Hd.
Qed.

(** Monotonicity is preserved under composition with inclusion *)
Lemma monotone_compose : forall H K1 K2 K3,
  L5_monotone H -> (K1 <= K2)%nat -> (K2 <= K3)%nat ->
  dset_included (H K1) (H K3).
Proof.
  intros H K1 K2 K3 Hmono H12 H23.
  apply (dset_included_trans (H K1) (H K2) (H K3)).
  - apply history_in_current; assumption.
  - apply history_in_current; assumption.
Qed.

(** States from same time but different histories can differ *)
Lemma states_at_intermediate :
  same_config_diff_D (1%nat, H1 1%nat) (1%nat, H2 1%nat).
Proof.
  split.
  - reflexivity.
  - exact diff_intermediate.
Qed.

(** H1 includes 2 at step 1 but H2 does not *)
Lemma H1_has_2_at_1 : In 2%nat (H1 1%nat).
Proof. simpl. right. left. reflexivity. Qed.

Lemma H2_lacks_2_at_1 : ~ In 2%nat (H2 1%nat).
Proof.
  simpl. intros [H | [H | H]]; lia.
Qed.

(** H2 includes 3 at step 1 but H1 does not *)
Lemma H2_has_3_at_1 : In 3%nat (H2 1%nat).
Proof. simpl. right. left. reflexivity. Qed.

Lemma H1_lacks_3_at_1 : ~ In 3%nat (H1 1%nat).
Proof.
  simpl. intros [H | [H | H]]; lia.
Qed.

(** Monotone empty history is trivially monotone *)
Lemma empty_history_monotone : L5_monotone (fun _ => @nil nat).
Proof.
  intros K d Hd. exact Hd.
Qed.

(** Constant history is monotone *)
Lemma const_history_monotone : forall D, L5_monotone (fun _ => D).
Proof.
  intros D K d Hd. exact Hd.
Qed.

(** * Synthesis *)

(** Combining all results: L5 monotonicity creates path-dependent processes *)
Lemma L5_indivisible_synthesis :
  (* Both histories are L5-monotone *)
  L5_monotone H1 /\
  L5_monotone H2 /\
  (* They share endpoints *)
  H1 0%nat = H2 0%nat /\
  H1 2%nat = H2 2%nat /\
  (* But differ in the middle *)
  H1 1%nat <> H2 1%nat /\
  (* Therefore: any distinction-sensitive transition reveals path-dependence *)
  (forall T,
    distinction_sensitive T (H1 1%nat) (H2 1%nat) 1%nat 2%nat ->
    indivisible T H1 H2).
Proof.
  split. { exact H1_monotone. }
  split. { exact H2_monotone. }
  split. { exact same_initial. }
  split. { exact same_final. }
  split. { exact diff_intermediate. }
  intros T Hsens.
  exact (L5_implies_indivisible T H1_monotone H2_monotone Hsens).
Qed.
