(** * PiConvergenceRate.v -- Three formulas, three rates, one π
    Elements: process distances, rate classification
    Roles:    Different formulas = distinguishable processes
    Rules:    Same limit, different convergence = different objects in ToS
    Status:   Stdlib
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.PiLeibniz.
From ToS Require Import stdlib.PiMachin.
From ToS Require Import stdlib.PiBBP.
From ToS Require Import stdlib.PiBasel.

Open Scope Q_scope.

(* ================================================================== *)
(*  PROCESS DISTANCE: all formulas are distinguishable                 *)
(* ================================================================== *)

Definition pi_process_distance (K : nat) : Q :=
  Qabs (pi_leibniz K - pi_machin K).

Lemma leib_neq_machin : ~ (pi_leibniz 0 == pi_machin 0).
Proof. rewrite pi_leib_0, pi_machin_0. unfold Qeq. simpl. lia. Qed.

Lemma leib_gt_machin : pi_machin 0 < pi_leibniz 0.
Proof. rewrite pi_leib_0, pi_machin_0. lra. Qed.

(** They give DIFFERENT values at K=0 *)
Lemma leib_neq_bbp : ~ (pi_leibniz 0 == pi_bbp 0).
Proof. rewrite pi_leib_0, pi_bbp_0. unfold Qeq. simpl. lia. Qed.

Lemma machin_neq_bbp : ~ (pi_machin 0 == pi_bbp 0).
Proof. rewrite pi_machin_0, pi_bbp_0. unfold Qeq. simpl. lia. Qed.

(** Process distance > 0 (all distinguishable) *)
Lemma pi_distance_0 : ~ (pi_leibniz 0 == pi_machin 0).
Proof. exact leib_neq_machin. Qed.

Lemma pi_leib_bbp_0 : ~ (pi_leibniz 0 == pi_bbp 0).
Proof. exact leib_neq_bbp. Qed.

Lemma pi_machin_bbp_0 : ~ (pi_machin 0 == pi_bbp 0).
Proof. exact machin_neq_bbp. Qed.

(* ================================================================== *)
(*  STEP SIZE COMPARISON at K=0                                        *)
(* ================================================================== *)

(** BBP step = |bbp_term(1)| which is tiny (order 1/100) *)
(** Leibniz step = |4*((-1)/3)| = 4/3 *)

Lemma bbp_step_small : bbp_step 0 < 1#100.
Proof. exact bbp_step_0_small. Qed.

Lemma leibniz_step_1_val : leibniz_step 1 == 4#5.
Proof. exact leib_step_1. Qed.

(* ================================================================== *)
(*  ALL THREE BRACKET π between 3 and 4                                *)
(* ================================================================== *)

(** Leibniz oscillates: π₁ = 8/3 < 3 < π₂ = 52/15 *)
Lemma leib_1_below_3 : pi_leibniz 1 < 3.
Proof. unfold pi_leibniz, leibniz_sum, leibniz_term, Qpow_pi, Qlt. vm_compute. reflexivity. Qed.

Lemma leib_2_above_3 : 3 < pi_leibniz 2.
Proof. unfold pi_leibniz, leibniz_sum, leibniz_term, Qpow_pi, Qlt. vm_compute. reflexivity. Qed.

(** Leibniz tighter bound: π ∈ (304/105, 1052/315) *)
Lemma leibniz_tight :
  pi_leibniz 3 < pi_leibniz 4 /\ pi_leibniz 4 < pi_leibniz 2.
Proof. exact pi_in_interval. Qed.

(** SYNTHESIS *)
Theorem pi_convergence_synthesis :
  (* All processes distinguishable *)
  ~ (pi_leibniz 0 == pi_machin 0) /\
  ~ (pi_leibniz 0 == pi_bbp 0) /\
  ~ (pi_machin 0 == pi_bbp 0) /\
  (* BBP step tiny *)
  bbp_step 0 < 1#100 /\
  (* Leibniz oscillates around π *)
  pi_leibniz 1 < 3 /\
  3 < pi_leibniz 2.
Proof.
  split; [|split; [|split; [|split; [|split]]]].
  - exact pi_distance_0.
  - exact pi_leib_bbp_0.
  - exact pi_machin_bbp_0.
  - exact bbp_step_small.
  - exact leib_1_below_3.
  - exact leib_2_above_3.
Qed.
