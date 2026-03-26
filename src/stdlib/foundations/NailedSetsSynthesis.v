(* NailedSetsSynthesis.v *)
(* Elements: Boltzmann process + nailed set combination *)
(* Roles: linking kernel symmetry to interpretation selection *)
(* Rules: synthesis theorems connecting BoltzmannProcess and NailedSets *)

From Coq Require Import QArith Lia Lqa.
From ToS Require Import stdlib.foundations.BoltzmannProcess.
From ToS Require Import stdlib.foundations.NailedSets.

Open Scope Q_scope.

(* ===== Synthesis: Boltzmann Process + Nailed Sets ===== *)

(* The symmetric kernel works for any nailed set *)
Lemma kernel_works_for_all : forall n : NailedSet,
  uses_same_kernel n.
Proof.
  destruct n; exact I.
Qed.

(* PH is simplest interpretation of symmetric process *)
Lemma ph_simplest_interpretation :
  (extra_assumptions PH_nail < extra_assumptions BB_nail)%nat /\
  (extra_assumptions PH_nail < extra_assumptions TwoNail)%nat.
Proof.
  simpl. lia.
Qed.

(* Kernel symmetry is a universal property *)
Lemma synthesis_symmetry : forall p,
  T_bp p 0 1 == T_bp p 1 0.
Proof.
  exact T_bp_symmetric_01.
Qed.

(* Kernel stochasticity is universal *)
Lemma synthesis_stochastic : forall p,
  T_bp p 0 0 + T_bp p 0 1 == 1.
Proof.
  exact T_bp_row0_sum.
Qed.

(* Concrete: p=1/3 kernel with PH interpretation *)
Lemma concrete_ph_kernel :
  extra_assumptions PH_nail = 0%nat /\
  T_bp (1#3) 0 0 == 2#3.
Proof.
  split.
  - reflexivity.
  - vm_compute. reflexivity.
Qed.

(* BB requires extra assumption AND same kernel *)
Lemma bb_extra_but_same :
  extra_assumptions BB_nail = 1%nat /\
  T_bp (1#3) 0 0 == 2#3.
Proof.
  split.
  - reflexivity.
  - vm_compute. reflexivity.
Qed.

(* Grand synthesis: PH + symmetric kernel is minimal theory *)
Theorem nailed_sets_grand_synthesis :
  (extra_assumptions PH_nail = 0%nat) /\
  (forall p, T_bp p 0 1 == T_bp p 1 0) /\
  (forall p, T_bp p 0 0 + T_bp p 0 1 == 1).
Proof.
  split; [reflexivity | split; [exact T_bp_symmetric_01 | exact T_bp_row0_sum]].
Qed.
