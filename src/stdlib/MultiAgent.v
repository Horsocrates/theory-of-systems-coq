(** * MultiAgent.v -- Multi-Agent Systems and Consensus

    Theory of Systems -- Verified Standard Library (Batch 5)

    Elements: agent states (nat -> Q), communication graph
    Roles:    agent_i -> Participant, graph -> CommunicationTopology
    Rules:    consensus protocol (averaging over neighbors)
    Status:   consensus_reached | converging | disconnected

    Connection: Graph.v -- communication topology
    Connection: GameTheory.v -- agents as strategic players
    Connection: FixedPoint.v -- consensus = fixed point of averaging

    STATUS: 18 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qminmax.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Q_scope.
From ToS Require Import Graph.

(* ================================================================= *)
(** ** Core Definitions                                               *)
(* ================================================================= *)

(** Agent state maps each agent index to a rational value. *)
Definition AgentState := nat -> Q.

(** All agents in a list share the same value. *)
Definition is_consensus (s : AgentState) (agents : list nat) : Prop :=
  forall i j, In i agents -> In j agents -> s i == s j.

(** The consensus value is the state of the first agent. *)
Definition consensus_value (s : AgentState) (agents : list nat) : Q :=
  s (hd 0%nat agents).

(** Two-agent averaging update: agents 0 and 1 each get the average. *)
Definition two_agent_avg (s : AgentState) : AgentState :=
  fun i =>
    if Nat.eqb i 0 then (s 0%nat + s 1%nat) * (1#2)
    else if Nat.eqb i 1 then (s 0%nat + s 1%nat) * (1#2)
    else s i.

(** Maximum state value over a list of agents. *)
Fixpoint max_state (s : AgentState) (agents : list nat) : Q :=
  match agents with
  | [] => 0
  | [a] => s a
  | a :: rest => Qmax (s a) (max_state s rest)
  end.

(** Minimum state value over a list of agents. *)
Fixpoint min_state (s : AgentState) (agents : list nat) : Q :=
  match agents with
  | [] => 0
  | [a] => s a
  | a :: rest => Qmin (s a) (min_state s rest)
  end.

(** Range = max - min. *)
Definition state_range (s : AgentState) (agents : list nat) : Q :=
  max_state s agents - min_state s agents.

(** Uniform state: every agent has the same value c. *)
Definition uniform_state (c : Q) : AgentState := fun _ => c.

(** A multi-agent system bundles a communication graph with an initial state. *)
Record MultiAgentSystem := mkMAS {
  mas_graph : Graph;
  mas_init  : AgentState;
  mas_agents : list nat;
}.

(* ================================================================= *)
(** ** Theorems                                                       *)
(* ================================================================= *)

(** 1. Uniform state always achieves consensus. *)
Lemma uniform_is_consensus : forall (c : Q) (agents : list nat),
  is_consensus (uniform_state c) agents.
Proof.
  intros c agents. unfold is_consensus, uniform_state.
  intros i j _ _. lra.
Qed.

(** 2. Consensus value of uniform state equals the constant. *)
Lemma consensus_value_uniform : forall (c : Q) (agents : list nat),
  agents <> [] ->
  consensus_value (uniform_state c) agents == c.
Proof.
  intros c agents Hne. unfold consensus_value, uniform_state.
  destruct agents.
  - exfalso. apply Hne. reflexivity.
  - simpl. lra.
Qed.

(** 3. Two-agent averaging produces consensus between agents 0 and 1. *)
Lemma two_agent_avg_consensus : forall (s : AgentState),
  is_consensus (two_agent_avg s) [0%nat; 1%nat].
Proof.
  intros s. unfold is_consensus. intros i j Hi Hj.
  unfold two_agent_avg.
  simpl in Hi. destruct Hi as [Hi | [Hi | []]].
  - subst i. simpl in Hj. destruct Hj as [Hj | [Hj | []]].
    + subst j. lra.
    + subst j. simpl. lra.
  - subst i. simpl. simpl in Hj. destruct Hj as [Hj | [Hj | []]].
    + subst j. simpl. lra.
    + subst j. simpl. lra.
Qed.

(** 4. Two-agent averaging preserves the sum of states. *)
Lemma two_agent_avg_preserves_sum : forall (s : AgentState),
  two_agent_avg s 0%nat + two_agent_avg s 1%nat == s 0%nat + s 1%nat.
Proof.
  intros s. unfold two_agent_avg. simpl. lra.
Qed.

(** 5. The averaged value for agent 0. *)
Lemma two_agent_avg_value : forall (s : AgentState),
  two_agent_avg s 0%nat == (s 0%nat + s 1%nat) * (1#2).
Proof.
  intros s. unfold two_agent_avg. simpl. lra.
Qed.

(** 6. If already at consensus, two_agent_avg is idempotent. *)
Lemma two_agent_avg_idempotent : forall (s : AgentState),
  s 0%nat == s 1%nat ->
  two_agent_avg s 0%nat == s 0%nat.
Proof.
  intros s Heq. unfold two_agent_avg. simpl. lra.
Qed.

(** 7. Consensus is symmetric: permuting the agent list preserves consensus. *)
Lemma consensus_symmetric : forall (s : AgentState) (i j : nat),
  is_consensus s [i; j] -> is_consensus s [j; i].
Proof.
  intros s i j Hcon.
  unfold is_consensus in *. intros a b Ha Hb.
  apply Hcon.
  - simpl in Ha. simpl. destruct Ha as [Ha | [Ha | []]]; auto.
  - simpl in Hb. simpl. destruct Hb as [Hb | [Hb | []]]; auto.
Qed.

(** 8. A single agent always forms a consensus. *)
Lemma consensus_singleton : forall (s : AgentState) (a : nat),
  is_consensus s [a].
Proof.
  intros s a. unfold is_consensus.
  intros i j Hi Hj.
  simpl in Hi. destruct Hi as [Hi | []].
  simpl in Hj. destruct Hj as [Hj | []].
  subst. lra.
Qed.

(** 9. State range is nonneg when max >= min. *)
Lemma state_range_nonneg : forall (s : AgentState) (agents : list nat),
  max_state s agents >= min_state s agents ->
  state_range s agents >= 0.
Proof.
  intros s agents Hge. unfold state_range. lra.
Qed.

(** 10. Range of uniform state is 0 for a singleton list. *)
Lemma uniform_range_zero_singleton : forall (c : Q) (a : nat),
  state_range (uniform_state c) [a] == 0.
Proof.
  intros c a. unfold state_range, uniform_state. simpl. lra.
Qed.

(** 11. Range of uniform state is 0 for a two-element list. *)
Lemma uniform_range_zero_pair : forall (c : Q) (a b : nat),
  state_range (uniform_state c) [a; b] == 0.
Proof.
  intros c a b. unfold state_range, uniform_state. simpl.
  destruct (Q.max_spec c c) as [[H1 H2] | [H1 H2]]; rewrite H2;
  destruct (Q.min_spec c c) as [[H3 H4] | [H3 H4]]; rewrite H4; lra.
Qed.

(** 12. Two-agent avg produces zero range (agents 0 and 1). *)
Lemma two_agent_avg_range_zero : forall (s : AgentState),
  state_range (two_agent_avg s) [0%nat; 1%nat] == 0.
Proof.
  intros s. unfold state_range, two_agent_avg. simpl.
  set (v := (s 0%nat + s 1%nat) * (1 # 2)).
  destruct (Q.max_spec v v) as [[H1 H2] | [H1 H2]]; rewrite H2;
  destruct (Q.min_spec v v) as [[H3 H4] | [H3 H4]]; rewrite H4; lra.
Qed.

(** 13. If already consensus, two_agent_avg preserves it. *)
Lemma consensus_fixpoint : forall (s : AgentState),
  is_consensus s [0%nat; 1%nat] ->
  is_consensus (two_agent_avg s) [0%nat; 1%nat].
Proof.
  intros s _. apply two_agent_avg_consensus.
Qed.

(** 14. Consensus implies any two agents in the list have equal state. *)
Lemma consensus_implies_equal : forall (s : AgentState) (agents : list nat)
  (i j : nat),
  is_consensus s agents -> In i agents -> In j agents ->
  s i == s j.
Proof.
  intros s agents i j Hcon Hi Hj.
  apply Hcon; assumption.
Qed.

(** 15. Concrete example: two agents with states 2 and 4, avg is 3. *)
Lemma mul_agent_example_2agents :
  let s := fun i : nat => if Nat.eqb i 0 then 2 else 4 in
  two_agent_avg s 0%nat == 3 /\ two_agent_avg s 1%nat == 3.
Proof.
  simpl. unfold two_agent_avg. simpl. split; lra.
Qed.

(** 16. The empty list is trivially at consensus. *)
Lemma consensus_empty : forall (s : AgentState),
  is_consensus s [].
Proof.
  intros s. unfold is_consensus. intros i j Hi Hj.
  simpl in Hi. contradiction.
Qed.

(** 17. Two-agent avg of a uniform state is the same uniform state. *)
Lemma two_agent_avg_uniform : forall (c : Q),
  two_agent_avg (uniform_state c) 0%nat == c /\
  two_agent_avg (uniform_state c) 1%nat == c.
Proof.
  intros c. unfold two_agent_avg, uniform_state. simpl.
  split; lra.
Qed.

(** 18. Idempotent for agent 1 as well. *)
Lemma two_agent_avg_idempotent_1 : forall (s : AgentState),
  s 0%nat == s 1%nat ->
  two_agent_avg s 1%nat == s 1%nat.
Proof.
  intros s Heq. unfold two_agent_avg. simpl. lra.
Qed.

(** TOTAL: 18 Qed, 0 Admitted, 0 axioms *)
