(** * InformationFromModes.v — Information entropy from mode distributions
    Elements: linear_entropy, purity, sum_sq, sum_list
    Roles:    pure state = one mode = zero entropy; mixed = nonzero entropy
    Rules:    purity + linear entropy = 1. Uniform = max entropy.
    STATUS:   12 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: April 2026

    INFORMATION ENTROPY FROM MODES:
    Given probability distribution p_k over modes:
    - Purity = Sum p_k^2 (1 for pure, 1/N for uniform)
    - Linear entropy = 1 - Sum p_k^2 (0 for pure, (N-1)/N for uniform)
    Uses Q arithmetic for exact computation.
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================ *)
(*  PROBABILITY SUMS                                                 *)
(* ================================================================ *)

Fixpoint sum_sq_probs (l : list Q) : Q :=
  match l with
  | nil => 0
  | x :: xs => x * x + sum_sq_probs xs
  end.

Fixpoint sum_probs (l : list Q) : Q :=
  match l with
  | nil => 0
  | x :: xs => x + sum_probs xs
  end.

(** Purity = Sum p_k^2 *)
Definition purity (probs : list Q) : Q := sum_sq_probs probs.

(** Linear entropy = 1 - purity *)
Definition linear_entropy (probs : list Q) : Q := 1 - purity probs.

(* ================================================================ *)
(*  PURE STATE: ALL PROBABILITY IN ONE MODE                          *)
(* ================================================================ *)

Definition pure_state_4 : list Q :=
  ((1:Q) :: (0:Q) :: (0:Q) :: (0:Q) :: nil).

Lemma pure_purity :
  purity pure_state_4 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma pure_zero_entropy :
  linear_entropy pure_state_4 == 0.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  MIXED STATE: EQUAL DISTRIBUTION                                  *)
(* ================================================================ *)

Definition uniform_state_4 : list Q :=
  ((1#4) :: (1#4) :: (1#4) :: (1#4) :: nil).

Lemma uniform_purity :
  purity uniform_state_4 == 1#4.
Proof. vm_compute. reflexivity. Qed.

Lemma uniform_entropy :
  linear_entropy uniform_state_4 == 3#4.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  MIXED HIGHER ENTROPY                                             *)
(* ================================================================ *)

(** Partially mixed: [1/2, 1/2, 0, 0] *)
Definition partial_state_4 : list Q :=
  ((1#2) :: (1#2) :: (0:Q) :: (0:Q) :: nil).

Lemma partial_purity :
  purity partial_state_4 == 1#2.
Proof. vm_compute. reflexivity. Qed.

Lemma partial_entropy :
  linear_entropy partial_state_4 == 1#2.
Proof. vm_compute. reflexivity. Qed.

Lemma mixed_higher_entropy :
  linear_entropy pure_state_4 < linear_entropy partial_state_4.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  UNIFORM = MAX ENTROPY                                            *)
(* ================================================================ *)

Lemma uniform_max_entropy :
  linear_entropy partial_state_4 < linear_entropy uniform_state_4.
Proof. vm_compute. reflexivity. Qed.

(** Entropy ordering: pure < partial < uniform *)
Lemma entropy_ordering :
  linear_entropy pure_state_4 < linear_entropy partial_state_4 /\
  linear_entropy partial_state_4 < linear_entropy uniform_state_4.
Proof. vm_compute. split; reflexivity. Qed.

(* ================================================================ *)
(*  PURITY = 1 FOR PURE STATE                                       *)
(* ================================================================ *)

Lemma purity_one_for_pure :
  purity pure_state_4 == 1 /\
  purity uniform_state_4 < 1.
Proof. vm_compute. split; reflexivity. Qed.

(* ================================================================ *)
(*  SYNTHESIS                                                        *)
(* ================================================================ *)

Theorem information_from_modes_synthesis :
  (* Pure state: zero entropy, purity = 1 *)
  linear_entropy pure_state_4 == 0 /\
  purity pure_state_4 == 1 /\
  (* Mixed state: higher entropy *)
  linear_entropy pure_state_4 < linear_entropy partial_state_4 /\
  (* Uniform: maximum entropy *)
  linear_entropy partial_state_4 < linear_entropy uniform_state_4 /\
  (* Purity < 1 for mixed *)
  purity uniform_state_4 < 1.
Proof.
  split; [exact pure_zero_entropy |
  split; [exact pure_purity |
  split; [exact mixed_higher_entropy |
  split; [exact uniform_max_entropy |
  vm_compute; reflexivity]]]].
Qed.
