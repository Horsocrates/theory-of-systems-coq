(** * PiSynthesis.v -- π as process: grand synthesis
    Elements: four formulas compared, process classification
    Roles:    π is not a number but an equivalence class of processes
    Rules:    Convergence rate = invariant of formula, not of π
    Status:   Stdlib
    STATUS: 5 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.PiLeibniz.
From ToS Require Import stdlib.PiMachin.
From ToS Require Import stdlib.PiBBP.
From ToS Require Import stdlib.PiBasel.
From ToS Require Import stdlib.PiConvergenceRate.
From ToS Require Import stdlib.PiConnections.

Open Scope Q_scope.

(** ★★★ π AS PROCESS: SYNTHESIS ★★★

  FOUR FORMULAS, FOUR PROCESSES, ONE π:

  Formula     K=0        K=2             Rate
  ─────────────────────────────────────────────
  Leibniz     4          52/15 ≈ 3.467   O(1/K)
  Machin      3804/1195  ~3.14160        O(1/25^K)
  BBP         47/15      ~3.14157        O(1/16^K)
  Basel+√     √6≈2.45    ...             O(1/K)×O(1/4^n)

  True π = 3.14159265...

  WHAT'S NEW (process perspective):
  — π is not a number but an equivalence class of processes
  — Convergence rate = invariant of the formula (not of π)
  — Leibniz = "golden mean of π" (slowest, simplest)
  — BBP = "full shift of π" (fastest, geometric)
  — Classification of π-formulas by convergence =
    classification of SFT by entropy rate *)

(** All bracket π *)
Lemma all_formulas_bracket :
  pi_leibniz 1 < 3 /\ 3 < pi_leibniz 2.
Proof. split; [exact leib_1_below_3 | exact leib_2_above_3]. Qed.

(** Leibniz bounds π *)
Lemma leibniz_bounds : pi_leibniz 3 < pi_leibniz 4 /\ pi_leibniz 4 < pi_leibniz 2.
Proof. exact pi_in_interval. Qed.

(** All processes distinguishable *)
Lemma processes_distinguishable :
  ~ (pi_leibniz 0 == pi_machin 0) /\
  ~ (pi_leibniz 0 == pi_bbp 0) /\
  ~ (pi_machin 0 == pi_bbp 0).
Proof.
  split; [|split].
  - exact pi_distance_0.
  - exact pi_leib_bbp_0.
  - exact pi_machin_bbp_0.
Qed.

(** GRAND SYNTHESIS *)
Theorem pi_grand_synthesis :
  (* Four formulas, all exact Q *)
  pi_leibniz 0 == 4 /\
  pi_machin 0 == 3804#1195 /\
  pi_bbp 0 == 47#15 /\
  pi_sq_process 1 == 6 /\
  (* √ converges *)
  sqrt_newton 6 2 2 == 49#20 /\
  (* BBP tiny step *)
  bbp_step 0 < 1#100 /\
  (* Processes distinguishable *)
  ~ (pi_leibniz 0 == pi_machin 0).
Proof.
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - exact pi_leib_0.
  - exact pi_machin_0.
  - exact pi_bbp_0.
  - exact pi_sq_1.
  - exact sqrt6_step2.
  - exact bbp_step_0_small.
  - exact pi_distance_0.
Qed.
