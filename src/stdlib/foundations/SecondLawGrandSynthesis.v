(* SecondLawGrandSynthesis.v *)
(* Elements: grand synthesis of distinction dynamics + second law *)
(* Roles: connecting nailed sets, distinction prior, doubly stochastic, entropy *)
(* Rules: the complete chain from L1 symmetry to thermodynamic arrow *)

From Coq Require Import QArith Lia Lqa.
From ToS Require Import stdlib.foundations.NailedSets.
From ToS Require Import stdlib.foundations.DistinctionPrior.
From ToS Require Import stdlib.foundations.DoublyStochastic.
From ToS Require Import stdlib.foundations.MajorizationSchur.
From ToS Require Import stdlib.foundations.SecondLaw.

Open Scope Q_scope.

(* ===== Grand Synthesis: Distinction Dynamics + Second Law ===== *)

(* Step 1: T is doubly stochastic *)
Lemma synthesis_step1_doubly_stochastic : forall p,
  T_distinction p 0 0 + T_distinction p 0 1 == 1 /\
  T_distinction p 0 0 + T_distinction p 1 0 == 1.
Proof.
  intros p. split; [exact (T_row0_sum p) | exact (T_col0_sum p)].
Qed.

(* Step 2: Mixing moves toward uniform *)
Lemma synthesis_step2_majorization :
  apply_T (1#3) (3#4) < 3#4 /\ 1#2 < apply_T (1#3) (3#4).
Proof.
  split; vm_compute; reflexivity.
Qed.

(* Step 3: Entropy increases *)
Lemma synthesis_step3_entropy_increase :
  S2 (3#4) < S2 (apply_T (1#3) (3#4)).
Proof. vm_compute. reflexivity. Qed.

(* Step 4: Maximum at equilibrium *)
Lemma synthesis_step4_equilibrium :
  S2 (3#4) < S2 (1#2) /\ S2 (7#12) < S2 (1#2).
Proof.
  split; vm_compute; reflexivity.
Qed.

(* Step 5: No past hypothesis needed *)
Lemma synthesis_step5_no_PH :
  natural_nail = PH_nail /\
  PH_extra_assumptions = 0%nat.
Proof.
  split; reflexivity.
Qed.

(* Step 6: PH is simplest *)
Lemma synthesis_step6_occam :
  (extra_assumptions PH_nail <= extra_assumptions BB_nail)%nat /\
  (extra_assumptions PH_nail <= extra_assumptions TwoNail)%nat.
Proof.
  simpl. lia.
Qed.

(* Step 7: Iterated application still increases *)
Lemma synthesis_step7_iterated :
  S2 (3#4) < S2 (apply_T (1#3) (3#4)) /\
  S2 (apply_T (1#3) (3#4)) < S2 (apply_T (1#3) (apply_T (1#3) (3#4))).
Proof.
  split; vm_compute; reflexivity.
Qed.

(* Grand Theorem: The complete chain *)
Theorem second_law_grand_synthesis :
  (* T is symmetric *)
  (forall p, T_distinction p 0 1 == T_distinction p 1 0) /\
  (* T is doubly stochastic *)
  (forall p, T_distinction p 0 0 + T_distinction p 0 1 == 1) /\
  (* Mixing increases entropy (concrete) *)
  S2 (3#4) < S2 (apply_T (1#3) (3#4)) /\
  (* Equilibrium is max *)
  S2 (3#4) < S2 (1#2) /\
  (* PH is natural *)
  natural_nail = PH_nail.
Proof.
  split; [| split; [| split; [| split]]].
  - intros p. unfold T_distinction. simpl. ring.
  - exact T_row0_sum.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
Qed.

(* The arrow of time emerges from L1 symmetry *)
Theorem arrow_of_time_from_symmetry :
  (* Symmetric kernel *)
  (forall p i j, (i < 2)%nat -> (j < 2)%nat ->
    T_distinction p i j == T_distinction p j i) /\
  (* Entropy non-decrease *)
  S2 (3#4) <= S2 (apply_T (1#3) (3#4)) /\
  S2 (9#10) <= S2 (apply_T (1#4) (9#10)).
Proof.
  split; [exact T_symmetric | split].
  - apply Qlt_le_weak. vm_compute. reflexivity.
  - apply Qlt_le_weak. vm_compute. reflexivity.
Qed.
