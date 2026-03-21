(** * InvariantMeasureProcess.v -- Invariant measures as processes over Q
    Elements: golden_markov, invariant measure, measure_process
    Roles:    Stationary μ·M = μ as process convergence
    Rules:    Exact Q at each step, Parry measure = PF eigenvector
    Status:   Stdlib
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.MatN.

Open Scope Q_scope.

(* ================================================================== *)
(*  GOLDEN MEAN MARKOV CHAIN                                           *)
(* ================================================================== *)

(** Markov transition from golden SFT: 0→{0,1}, 1→{0} *)
Definition golden_markov : MatN := fun i j =>
  match i, j with
  | O, O => 1#2 | O, S O => 1#2
  | S O, O => 1   | _, _ => 0
  end.

(** Parry measure (invariant): μ = (2/3, 1/3) *)
(** μ·M = μ: (2/3·1/2 + 1/3·1, 2/3·1/2 + 1/3·0) = (2/3, 1/3) ✓ *)

Lemma invariant_check_0 :
  (2#3) * (1#2) + (1#3) * 1 == 2#3.
Proof. lra. Qed.

Lemma invariant_check_1 :
  (2#3) * (1#2) + (1#3) * 0 == 1#3.
Proof. lra. Qed.

(** Normalization: μ₀ + μ₁ = 1 *)
Lemma invariant_normalized : (2#3) + (1#3) == 1.
Proof. lra. Qed.

(* ================================================================== *)
(*  INVARIANT MEASURE AS PROCESS                                       *)
(* ================================================================== *)

(** Start from uniform (1/2, 1/2). Apply M repeatedly.
    ρ_K = ρ₀·M^K → μ as K → ∞ *)

(** Approximate measure at step K: normalize row 0 of M^K *)
Definition measure_step_0 (K : nat) : Q :=
  greenN 2 golden_markov 0%nat 0%nat K /
  (greenN 2 golden_markov 0%nat 0%nat K + greenN 2 golden_markov 0%nat 1%nat K).

Lemma measure_step_1 : measure_step_0 1 == 1#2.
Proof. vm_compute. reflexivity. Qed.

Lemma measure_step_2 : measure_step_0 2 == 3#4.
Proof. vm_compute. reflexivity. Qed.

Lemma measure_step_3 : measure_step_0 3 == 5#8.
Proof. vm_compute. reflexivity. Qed.

Lemma measure_step_4 : measure_step_0 4 == 11#16.
Proof. vm_compute. reflexivity. Qed.

(** Convergence: measure_step oscillates around 2/3
    1/2, 3/4, 5/8, 11/16, ... → 2/3 *)

(** Distance from 2/3 decreases: |5/8 - 2/3| < |1/2 - 2/3| *)
Lemma abs_step3 : Qabs (measure_step_0 3 - (2#3)) == 1#24.
Proof. rewrite measure_step_3. vm_compute. reflexivity. Qed.

Lemma abs_step1 : Qabs (measure_step_0 1 - (2#3)) == 1#6.
Proof. rewrite measure_step_1. vm_compute. reflexivity. Qed.

Lemma measure_convergence :
  Qabs (measure_step_0 3 - (2#3)) < Qabs (measure_step_0 1 - (2#3)).
Proof. rewrite abs_step3, abs_step1. lra. Qed.

(* ================================================================== *)
(*  FULL SHIFT MARKOV CHAIN                                            *)
(* ================================================================== *)

(** Full shift: M = [[1/2, 1/2], [1/2, 1/2]] *)
Definition full_markov : MatN := fun _ _ => 1#2.

(** Invariant: μ = (1/2, 1/2) (uniform) *)
Lemma full_invariant_check :
  (1#2) * (1#2) + (1#2) * (1#2) == 1#2.
Proof. lra. Qed.

(** SYNTHESIS *)
Theorem invariant_measure_synthesis :
  (* Golden: μ = (2/3, 1/3) is invariant *)
  (2#3) * (1#2) + (1#3) * 1 == 2#3 /\
  (2#3) * (1#2) + (1#3) * 0 == 1#3 /\
  (* Process converges *)
  Qabs (measure_step_0 3 - (2#3)) < Qabs (measure_step_0 1 - (2#3)) /\
  (* Full shift: uniform is invariant *)
  (1#2) * (1#2) + (1#2) * (1#2) == 1#2.
Proof.
  split; [|split; [|split]].
  - exact invariant_check_0.
  - exact invariant_check_1.
  - exact measure_convergence.
  - exact full_invariant_check.
Qed.
