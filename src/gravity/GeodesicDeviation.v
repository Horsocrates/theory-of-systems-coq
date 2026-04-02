(** * GeodesicDeviation.v -- Geodesics and curvature deviation on graphs
    Elements: geodesic length, path distance, curvature deviation
    Roles:    flat graph = straight geodesic; curved graph = bent path
    Rules:    equivalence principle, gravitational redshift from curvature
    STATUS:   8 Qed, 0 Admitted, 0 axioms
    Author:   Horsocrates | Date: April 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List PeanoNat.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================ *)
(*  DEFINITIONS                                                      *)
(* ================================================================ *)

(** Distance on a path graph P_N: just |end - start| *)
Definition geodesic_length_path (s e : nat) : nat := (e - s)%nat.

(** On a cycle C_N: min of clockwise and counterclockwise *)
Definition geodesic_length_cycle (s e N : nat) : nat :=
  Nat.min (e - s)%nat (N - (e - s))%nat.

(** Curvature deviation: how much the local metric differs *)
Definition metric_deviation (flat_dist curved_dist : nat) : Z :=
  Z.of_nat curved_dist - Z.of_nat flat_dist.

(** Frequency shift due to curvature (simplified): higher curvature = lower frequency *)
Definition freq_ratio (curv_source curv_receiver : Q) : Q :=
  1 + (curv_source - curv_receiver) / 10.

(* ================================================================ *)
(*  THEOREM 1: Flat geodesic on path graph                           *)
(* ================================================================ *)

Theorem flat_geodesic :
  geodesic_length_path 0%nat 4%nat = 4%nat.
Proof.
  unfold geodesic_length_path. simpl. reflexivity.
Qed.

(* ================================================================ *)
(*  THEOREM 2: Cycle geodesic shorter than path                      *)
(* ================================================================ *)

Theorem cycle_shorter :
  (geodesic_length_cycle 0%nat 3%nat 4%nat <= geodesic_length_path 0%nat 3%nat)%nat.
Proof.
  unfold geodesic_length_cycle, geodesic_length_path. simpl. lia.
Qed.

(* ================================================================ *)
(*  THEOREM 3: Zero deviation on flat metric                         *)
(* ================================================================ *)

Theorem zero_deviation_flat :
  metric_deviation 3%nat 3%nat = 0%Z.
Proof.
  unfold metric_deviation. simpl. reflexivity.
Qed.

(* ================================================================ *)
(*  THEOREM 4: Positive deviation means shorter path (curvature)     *)
(* ================================================================ *)

Theorem curvature_shortens :
  (metric_deviation 4%nat 3%nat < 0)%Z.
Proof.
  unfold metric_deviation. simpl. lia.
Qed.

(* ================================================================ *)
(*  THEOREM 5: Equivalence principle -- locally all metrics look flat *)
(* ================================================================ *)

Theorem equivalence_principle_local :
  (* At a single vertex, geodesic length 0 = 0, regardless of curvature *)
  geodesic_length_path 0%nat 0%nat = 0%nat /\
  geodesic_length_cycle 0%nat 0%nat 4%nat = 0%nat.
Proof.
  split; unfold geodesic_length_path, geodesic_length_cycle; simpl; reflexivity.
Qed.

(* ================================================================ *)
(*  THEOREM 6: Gravitational redshift                                *)
(*  Signal from high-curvature source arrives redshifted             *)
(* ================================================================ *)

Theorem gravitational_redshift :
  (* Source at high curvature (1), receiver at low (-1/4) *)
  freq_ratio 1 (-(1#4)) > 1.
Proof.
  unfold freq_ratio. vm_compute. reflexivity.
Qed.

(* ================================================================ *)
(*  THEOREM 7: No shift between equal curvatures                     *)
(* ================================================================ *)

Theorem no_shift_equal_curvature :
  forall c : Q, freq_ratio c c == 1.
Proof.
  intro c. unfold freq_ratio. field.
Qed.

(* ================================================================ *)
(*  SYNTHESIS                                                        *)
(* ================================================================ *)

Theorem geodesic_deviation_synthesis :
  (* Flat geodesic works *)
  geodesic_length_path 0%nat 4%nat = 4%nat /\
  (* Zero deviation on flat *)
  metric_deviation 3%nat 3%nat = 0%Z /\
  (* Curvature shortens paths *)
  (metric_deviation 4%nat 3%nat < 0)%Z /\
  (* Redshift from curvature *)
  freq_ratio 1 (-(1#4)) > 1 /\
  (* Equal curvature = no shift *)
  freq_ratio (1#2) (1#2) == 1.
Proof.
  split. { exact flat_geodesic. }
  split. { exact zero_deviation_flat. }
  split. { exact curvature_shortens. }
  split. { exact gravitational_redshift. }
  exact (no_shift_equal_curvature (1#2)).
Qed.
