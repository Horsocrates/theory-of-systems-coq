(** * Ising2DSynthesis.v -- 2D Ising: Onsager from transfer matrix over Q
    Elements: onsager_synthesis
    Roles:    Unite transfer matrix, eigenvalues, Onsager condition
    Rules:    Phase transition at β_c ∈ (3/7, 4/9) over Q
    Status:   Stdlib
    STATUS: 5 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.Ising2DTransfer.
From ToS Require Import stdlib.OnsagerCondition.
From ToS Require Import stdlib.Ising2DThermodynamics.

Open Scope Q_scope.

(** Transfer matrix structure *)
Lemma transfer_structure :
  lambda_antisym (1#2) 3 == 19#12 /\
  lambda_odd (1#2) 3 == 43#12 /\
  sum_even (1#2) 3 == 13#2.
Proof.
  split; [|split].
  - exact lambda_antisym_value.
  - exact lambda_odd_value.
  - exact sum_even_value.
Qed.

(** Onsager bracket *)
Lemma onsager_bracket :
  onsager_residual (3#7) 3 < 0 /\
  0 < onsager_residual (4#9) 3.
Proof.
  split.
  - exact onsager_low_3_7.
  - exact onsager_high_4_9.
Qed.

(** Gap structure *)
Lemma gap_structure :
  0 < gap_squared (1#2) 3 /\
  gap_squared (1#2) 3 == 3805#72.
Proof.
  split.
  - exact gap_sq_positive_half.
  - exact gap_sq_half.
Qed.

(** Eigenvalue hierarchy *)
Lemma eigenvalue_hierarchy :
  0 < lambda_antisym (1#2) 3 /\
  lambda_antisym (1#2) 3 < lambda_odd (1#2) 3.
Proof.
  split.
  - exact lambda_antisym_pos_half.
  - exact eigenvalue_ordering_half.
Qed.

(** THE GRAND THEOREM *)
Theorem onsager_synthesis :
  (* Onsager bracket: β_c ∈ (3/7, 4/9) *)
  onsager_residual (3#7) 3 < 0 /\
  0 < onsager_residual (4#9) 3 /\
  (* Eigenvalue ordering *)
  0 < lambda_antisym (1#2) 3 /\
  lambda_antisym (1#2) 3 < lambda_odd (1#2) 3 /\
  (* Gap positive *)
  0 < gap_squared (1#2) 3.
Proof.
  split; [|split; [|split; [|split]]].
  - exact onsager_low_3_7.
  - exact onsager_high_4_9.
  - exact lambda_antisym_pos_half.
  - exact eigenvalue_ordering_half.
  - exact gap_sq_positive_half.
Qed.
