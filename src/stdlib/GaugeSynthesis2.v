(** * GaugeSynthesis2.v -- Gauge Group Grand Synthesis as ToS System
    Elements: Gell-Mann matrices, rotation plane counting, Standard Model
    Roles:    SU(3) traceless generators + plane decomposition + SM count
    Rules:    Gauge structure from rotation planes; 12 SM generators in SU(5) GUT
    Status:   Stdlib -- Six Directions Phase 2, Section D6
    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Lia ZArith Arith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.GellMannExplicit.
From ToS Require Import stdlib.GaugeFromPlanes.
From ToS Require Import stdlib.StandardModelCount.

Open Scope Q_scope.

(* ================================================================== *)
(*  GELL-MANN TRACELESSNESS RECAP                                       *)
(* ================================================================== *)

Theorem gellmann_all_traceless :
  (mat3_trace lambda1 == 0) /\
  (mat3_trace lambda3 == 0) /\
  (mat3_trace lambda8_scaled == 0).
Proof.
  split. { exact trace_lambda1. }
  split. { exact trace_lambda3. }
  exact trace_lambda8.
Qed.

(* ================================================================== *)
(*  PLANE DECOMPOSITION RECAP                                           *)
(* ================================================================== *)

Theorem su3_plane_decomposition :
  (su_off_diag 3 + su_diagonal 3 = su_generators 3)%nat.
Proof. exact su3_decomposition. Qed.

Theorem su3_has_8_generators : (su_generators 3 = 8)%nat.
Proof. exact su3_generators. Qed.

(* ================================================================== *)
(*  SM IN GUT                                                           *)
(* ================================================================== *)

Theorem sm_fits_in_su5 : (sm_total <= su_generators 5)%nat.
Proof. exact su5_contains_sm. Qed.

Theorem sm_has_12 : (sm_total = 12)%nat.
Proof. exact standard_model_count. Qed.

(* ================================================================== *)
(*  GRAND SYNTHESIS                                                     *)
(* ================================================================== *)

Theorem gauge_grand_synthesis :
  (mat3_trace lambda1 == 0) /\
  (su_generators 3 = 8)%nat /\
  (sm_total = 12)%nat /\
  (su_generators 5 = 24)%nat.
Proof.
  split. { exact trace_lambda1. }
  split. { exact su3_generators. }
  split. { exact standard_model_count. }
  exact su5_generators.
Qed.

Theorem gauge_su2_recap : (su_generators 2 = 3)%nat.
Proof. exact su2_generators. Qed.

Theorem gauge_direction_complete :
  (mat3_trace lambda8_scaled == 0) /\
  (su_off_diag 3 + su_diagonal 3 = su_generators 3)%nat /\
  (sm_total <= su_generators 5)%nat.
Proof.
  split. { exact trace_lambda8. }
  split. { exact su3_decomposition. }
  exact su5_contains_sm.
Qed.
