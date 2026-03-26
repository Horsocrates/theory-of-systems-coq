(* CircleOpenedSynthesis.v *)
(* Elements: grand synthesis of nailed sets + distinction prior + dependency chain *)
(* Roles: combining Occam, zero-start, and acyclic chain *)
(* Rules: synthesis theorems *)

From Coq Require Import QArith Lia Lqa.
From ToS Require Import stdlib.foundations.NailedSets.
From ToS Require Import stdlib.foundations.DistinctionPrior.
From ToS Require Import stdlib.foundations.CircleOpened.

Open Scope Q_scope.

(* ===== Circle Opened Synthesis ===== *)

(* PH is natural + minimal *)
Lemma ph_natural_and_minimal :
  natural_nail = PH_nail /\ PH_extra_assumptions = 0%nat.
Proof.
  split; reflexivity.
Qed.

(* Chain is fully ordered *)
Lemma chain_fully_ordered :
  (step_L1 < step_doubly)%nat /\
  (step_doubly < step_schur)%nat /\
  (step_schur < step_second_law)%nat /\
  (step_second_law < step_memory)%nat.
Proof.
  unfold step_L1, step_doubly, step_schur, step_second_law, step_memory.
  lia.
Qed.

(* Chain has exactly 5 steps *)
Lemma chain_length : step_memory = 5%nat.
Proof. reflexivity. Qed.

(* Process starts at zero and PH is simplest *)
Lemma zero_start_ph_simplest :
  S_0 == 0 /\ (extra_assumptions PH_nail <= extra_assumptions BB_nail)%nat.
Proof.
  split.
  - vm_compute. reflexivity.
  - simpl. lia.
Qed.

(* No circularity: step 5 does not depend on step 1 in reverse *)
Lemma no_circularity : ~ depends_on step_L1 step_memory.
Proof.
  unfold depends_on, step_L1, step_memory. lia.
Qed.

(* Grand synthesis: PH + zero start + acyclic chain *)
Theorem circle_opened_grand_synthesis :
  natural_nail = PH_nail /\
  S_0 == 0 /\
  (step_L1 < step_memory)%nat.
Proof.
  split; [reflexivity | split; [vm_compute; reflexivity | ]].
  exact chain_L1_lt_memory.
Qed.

(* Three nailed sets, one chain, one winner *)
Lemma three_nails_one_chain :
  BB_nail <> PH_nail /\ PH_nail <> TwoNail /\
  natural_nail = PH_nail.
Proof.
  split; [discriminate | split; [discriminate | reflexivity]].
Qed.
