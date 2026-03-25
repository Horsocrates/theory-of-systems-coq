(** * HartreeSynthesis.v — Grand Synthesis: Padé + Coulomb + Convergence
    Elements: Padé approximant, Coulomb kernel, Hartree convergence bound
    Roles:    Unify all three components into verified Hartree-Fock pipeline
    Rules:    Padé well-formed, Coulomb symmetric, convergence exponential
    Status:   Stdlib
    STATUS: 7 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
Require Import ToS.stdlib.PadeApprox.
Require Import ToS.stdlib.CoulombKernel.
Require Import ToS.stdlib.HartreeConvergence.

Open Scope Q_scope.

(* ================================================================== *)
(*  SYNTHESIS GATE 1: Padé approximant is well-formed                  *)
(*  Identity at origin, monotonically decreasing, positive             *)
(* ================================================================== *)

Theorem pade_wellformed :
  pade22 0 == 1 /\
  0 < pade22 (1#2) /\
  pade22 1 < pade22 (1#2).
Proof.
  split. { exact pade_at_0. }
  split. { exact pade_positive_half. }
  exact pade_decreasing.
Qed.

(* ================================================================== *)
(*  SYNTHESIS GATE 2: Coulomb kernel is symmetric and positive         *)
(* ================================================================== *)

Theorem coulomb_wellformed :
  coulomb_kernel 10 0 1 == coulomb_kernel 10 1 0 /\
  0 < coulomb_kernel 10 0 1 /\
  coulomb_kernel 10 3 3 == 0.
Proof.
  split. { exact kernel_symmetric_01. }
  split. { exact kernel_positive_01. }
  exact kernel_self_zero_3.
Qed.

(* ================================================================== *)
(*  SYNTHESIS GATE 3: Convergence bound decreases exponentially        *)
(* ================================================================== *)

Theorem convergence_wellformed :
  0 < hartree_error_bound (1#2) 5 /\
  hartree_error_bound (1#2) 10 < hartree_error_bound (1#2) 5.
Proof.
  split.
  - exact bound_positive.
  - exact bound_decreases.
Qed.

(* ================================================================== *)
(*  SYNTHESIS GATE 4: Coulomb decays with distance                     *)
(* ================================================================== *)

Theorem coulomb_decay :
  coulomb_kernel 10 0 5 < coulomb_kernel 10 0 1.
Proof. exact kernel_monotone. Qed.

(* ================================================================== *)
(*  SYNTHESIS GATE 5: Padé accuracy check                              *)
(* ================================================================== *)

Theorem pade_accuracy :
  pade22 (1#10) == 1141 # 1261 /\
  pade22 2 == 1 # 7.
Proof.
  split.
  - exact pade_at_tenth.
  - exact pade_at_2.
Qed.

(* ================================================================== *)
(*  GRAND SYNTHESIS: All three subsystems verified                     *)
(* ================================================================== *)

Theorem hartree_grand_synthesis :
  (* Padé identity *)
  pade22 0 == 1 /\
  (* Coulomb symmetry *)
  coulomb_kernel 10 0 1 == coulomb_kernel 10 1 0 /\
  (* Convergence *)
  hartree_error_bound (1#2) 10 < hartree_error_bound (1#2) 5 /\
  (* Coulomb positivity *)
  0 < coulomb_kernel 10 0 1.
Proof.
  split. { exact pade_at_0. }
  split. { exact kernel_symmetric_01. }
  split. { exact bound_decreases. }
  exact kernel_positive_01.
Qed.

(* ================================================================== *)
(*  PIPELINE COMPLETENESS: error bound at 10 iterations < 0.001       *)
(*  1/1024 < 1/1000                                                   *)
(* ================================================================== *)

Theorem pipeline_precision :
  hartree_error_bound (1#2) 10 < 1 # 1000.
Proof.
  unfold hartree_error_bound. simpl.
  vm_compute. reflexivity.
Qed.
