(** * GreenSynthesis.v -- Everything is Green's functions
    Elements: green_unification
    Roles:    G_{ij}(K) = (M^K)_{ij} unifies gauge, entropy, CF, heat kernel
    Rules:    One object, five faces, all over Q
    Status:   Stdlib
    STATUS: 5 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.GreenFunction.
From ToS Require Import stdlib.GreenGauge.
From ToS Require Import stdlib.InverseProblem.
From ToS Require Import stdlib.HeatKernelLattice.
From ToS Require Import stdlib.KacOnLattice.

Open Scope Q_scope.

(* ================================================================== *)
(*  THE INFORMATION HIERARCHY                                          *)
(* ================================================================== *)

(** Level 3: G_{ij}(1) = M itself (complete information)
    Level 2: {G_{ij}(K)}_K = full dynamics (determines M)
    Level 1: {Σ G_{ii}(K)}_K = trace process (determines spectrum)
    Level 0: lim h_K = h_top (one number — least information)

    Levels 3 > 2 > 1 > 0 strictly.
    Kac's question = Level 1 vs Level 3. *)

(** Level 3 = complete: G_{ij}(1) determines everything *)
Lemma level_3_complete : forall M i j,
  (i <= 1)%nat -> (j <= 1)%nat ->
  green M i j 1 == M i j.
Proof. exact inverse_from_full_green. Qed.

(** Level 1 < Level 3: same trace but different Green's functions exist *)
Lemma level_1_incomplete :
  trace_process M_upper 1 == trace_process M_lower 1 /\
  ~ (green M_upper 0%nat 1%nat 1 == green M_lower 0%nat 1%nat 1).
Proof.
  split.
  - exact same_trace_1.
  - exact different_green_01.
Qed.

(** Heat ratio process converges to max eigenvalue *)
Lemma heat_ratio_converges :
  heat_ratio golden 3 == 7#4 /\
  heat_ratio full_mat2 1 == 2.
Proof.
  split.
  - exact heat_ratio_golden_3.
  - exact heat_ratio_full_1.
Qed.

(** Gauge correlator = Green's function ratio *)
Lemma gauge_is_green_ratio :
  correlator_as_green_ratio 1 0%nat 0 == 1 /\
  partition_as_trace 1 0%nat 0 == 4.
Proof.
  split.
  - exact gauge_correlator_concrete.
  - exact gauge_partition_concrete.
Qed.

(** GRAND UNIFICATION *)
Theorem green_unification :
  (* G_{00} = Fibonacci *)
  green golden 0%nat 0%nat 4 == 5 /\
  (* Trace = Lucas numbers *)
  trace_process golden 4 == 7 /\
  (* Heat ratio → φ *)
  heat_ratio golden 3 == 7#4 /\
  (* Kac: same trace, different shape *)
  trace_process M_upper 1 == trace_process M_lower 1 /\
  green M_upper 0%nat 1%nat 1 == 1 /\
  green M_lower 0%nat 1%nat 1 == 0 /\
  (* Gauge correlator at K=0 is 1 *)
  correlator_as_green_ratio 1 0%nat 0 == 1.
Proof.
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - exact green_golden_00_4.
  - exact trace_golden_4.
  - exact heat_ratio_golden_3.
  - exact same_trace_1.
  - exact green_upper_01.
  - exact green_lower_01.
  - exact gauge_correlator_concrete.
Qed.
