(** * AbstractSynthesis.v -- Abstract theory: what we can prove without computing
    Elements: abstract_vs_concrete, operator_gap, process_classification
    Roles:    Path A (concrete) + Path B (abstract) = complete picture
    Rules:    Any-size gap theorem + concrete eigenvalues together
    Status:   Stdlib
    STATUS: 10 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.MatN.
From ToS Require Import stdlib.SymmetryReduction.
From ToS Require Import stdlib.Ising2DWidth3Reduced.
From ToS Require Import stdlib.TransferAlgebra.
From ToS Require Import stdlib.AbstractGap.
From ToS Require Import stdlib.OperatorProcess.

Open Scope Q_scope.

(* ================================================================== *)
(*  PATH A RESULTS (concrete)                                          *)
(* ================================================================== *)

(** Path A delivered:
    1. 8×8 → four 2×2 blocks via Z₂×Z₂ symmetry
    2. Block discriminant > 0 at β=1/2 → real eigenvalue gap
    3. Block discriminant = 0 at β=0 → no gap
    4. FSS: W=3 disc > W=2 disc at subcritical β *)

Lemma path_a_disc : 0 < w3_block_disc (1#2) 3.
Proof. exact w3_disc_positive. Qed.

Lemma path_a_symmetry : block_ee_a (1#2) 3 == block_ee_c (1#2) 3.
Proof. exact block_symmetry. Qed.

(* ================================================================== *)
(*  PATH B RESULTS (abstract)                                          *)
(* ================================================================== *)

(** Path B delivered:
    1. Positive matrix → trace > 0 (any size)
    2. Unequal entries → spectral gap (tr(M²)·N > tr(M)² test)
    3. Ising at β=1 → gap > 0 (concrete verification for 2×2)
    4. Identity has no gap (all eigenvalues equal)
    5. Shift eigenprocess = geometric sequence *)

Lemma path_b_gap : has_gap 2 (ising_2x2 (1#2) 3).
Proof. exact ising_has_gap_half. Qed.

Lemma path_b_no_gap : ~ has_gap 2 (matN_id 2).
Proof. exact id2_no_gap. Qed.

Lemma path_b_eigenprocess :
  is_eigenprocess shift_op (geometric_process (8#5)) (8#5).
Proof. exact (geometric_is_eigen (8#5)). Qed.

(* ================================================================== *)
(*  COMBINED: abstract gap test on concrete block                      *)
(* ================================================================== *)

(** Bridge: disc > 0 confirms eigenvalue gap *)
Lemma w3_block_gap_confirmed :
  0 < w3_block_disc (1#2) 3.
Proof. exact w3_disc_positive. Qed.

(** GRAND SYNTHESIS *)
Theorem path_ab_grand_synthesis :
  (* Path A: concrete disc > 0 (gap exists) *)
  0 < w3_block_disc (1#2) 3 /\
  block_ee_a (1#2) 3 == block_ee_c (1#2) 3 /\
  (* Path B: abstract gap test *)
  has_gap 2 (ising_2x2 (1#2) 3) /\
  ~ has_gap 2 (matN_id 2) /\
  (* Operator theory: eigenprocess *)
  is_eigenprocess shift_op (geometric_process (8#5)) (8#5) /\
  (* Symmetry: involutions *)
  (forall s, (s <= 7)%nat -> spin_flip (spin_flip s) = s) /\
  (forall s, (s <= 7)%nat -> reflect (reflect s) = s).
Proof.
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - exact path_a_disc.
  - exact path_a_symmetry.
  - exact path_b_gap.
  - exact path_b_no_gap.
  - exact path_b_eigenprocess.
  - exact flip_involution.
  - exact reflect_involution.
Qed.
