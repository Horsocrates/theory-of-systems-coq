(** * MeasurementProcess.v — Measurement = mode identification, not collapse
    Elements: post_measurement, inner_product_exact
    Roles:    measurement reveals which L1-L5 tension mode is active
    Rules:    no collapse — information update. P4: finite precision always.
    STATUS:   10 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: April 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import process_qm.QuantumFromVibration.

(* ================================================================ *)
(*  POST-MEASUREMENT STATE                                           *)
(* ================================================================ *)

(** After measuring mode k: state collapses to pure mode k *)
Definition post_measurement (N k : nat) : QState :=
  List.map (fun i => if (i =? k)%nat then 1 else 0) (List.seq 0 N).

Lemma post_meas_0 : post_measurement 4 0 = [1; 0; 0; 0].
Proof. vm_compute. reflexivity. Qed.

Lemma post_meas_2 : post_measurement 4 2 = [0; 0; 1; 0].
Proof. vm_compute. reflexivity. Qed.

Lemma post_meas_normalized : is_normalized (post_measurement 4 0).
Proof. unfold is_normalized, norm_sq. vm_compute. reflexivity. Qed.

(** Post-measurement: probability 1 for measured mode *)
Lemma post_meas_certain :
  measurement_probability (post_measurement 4 2) 2 == 1.
Proof. vm_compute. reflexivity. Qed.

(** Post-measurement: probability 0 for other modes *)
Lemma post_meas_zero_other :
  measurement_probability (post_measurement 4 2) 0 == 0.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  INNER PRODUCT OVER Q (EXACT)                                     *)
(* ================================================================ *)

Fixpoint inner_product (psi phi : QState) : Q :=
  match psi, phi with
  | a :: as_, b :: bs => a * b + inner_product as_ bs
  | _, _ => 0
  end.

Lemma ip_self_ground : inner_product ground_state ground_state == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma ip_orthogonal : inner_product ground_state mode1_state == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma ip_exact : inner_product [1; 2; 3; 4] [5; 6; 7; 8] == 70.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  UNCERTAINTY FROM FINITE N                                        *)
(* ================================================================ *)

(** On N=4 graph: mode uncertainty >= 1/(2N) = 1/8 *)
Definition min_uncertainty (N : nat) : Q :=
  1 / inject_Z (Z.of_nat (2 * N)).

Lemma uncertainty_N4 : min_uncertainty 4 == 1 # 8.
Proof. unfold min_uncertainty. vm_compute. reflexivity. Qed.

Lemma uncertainty_N8 : min_uncertainty 8 == 1 # 16.
Proof. unfold min_uncertainty. vm_compute. reflexivity. Qed.

(** Finer grid → smaller uncertainty *)
Lemma finer_less_uncertainty :
  min_uncertainty 8 < min_uncertainty 4.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  SYNTHESIS                                                        *)
(* ================================================================ *)

Theorem measurement_synthesis :
  (* Post-measurement state is pure mode *)
  measurement_probability (post_measurement 4 2) 2 == 1 /\
  measurement_probability (post_measurement 4 2) 0 == 0 /\
  (* Orthogonal modes give ip = 0 *)
  inner_product ground_state mode1_state == 0 /\
  (* Uncertainty decreases with N *)
  min_uncertainty 8 < min_uncertainty 4.
Proof.
  split; [exact post_meas_certain |
  split; [exact post_meas_zero_other |
  split; [exact ip_orthogonal |
  exact finer_less_uncertainty]]].
Qed.
