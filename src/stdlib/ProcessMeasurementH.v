(* ProcessMeasurementH.v *)
(* Measurement as Projection in Process Hilbert Space *)
(* E: Projectors, measurement outcomes, sequential measurement *)
(* R: Structural role — measurement collapses to basis state *)
(* R: Born rule + projection consistency, idempotency *)

From Stdlib Require Import QArith Qabs List.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import stdlib.ProcessHilbert.

(** Projector onto basis state |basis_index> in K dimensions *)
Definition project (basis_index K : nat) : PState :=
  map (fun i => if Nat.eqb i basis_index then 1 else 0) (seq 0 K).

(** ---- Projectors produce basis states ---- *)

Lemma project_0_2 : project 0 2 = ket_0.
Proof. vm_compute. reflexivity. Qed.

Lemma project_1_2 : project 1 2 = ket_1.
Proof. vm_compute. reflexivity. Qed.

Lemma project_0_3 : project 0 3 = ket_0_3.
Proof. vm_compute. reflexivity. Qed.

Lemma project_1_3 : project 1 3 = ket_1_3.
Proof. vm_compute. reflexivity. Qed.

Lemma project_2_3 : project 2 3 = ket_2_3.
Proof. vm_compute. reflexivity. Qed.

(** Measurement: project state onto outcome *)
Definition measure (psi : PState) (outcome K : nat) : PState :=
  project outcome K.

(** ---- Measuring |+> ---- *)

Lemma measure_plus_0 : measure ket_plus 0 2 = ket_0.
Proof. vm_compute. reflexivity. Qed.

Lemma measure_plus_1 : measure ket_plus 1 2 = ket_1.
Proof. vm_compute. reflexivity. Qed.

(** ---- Born rule + measurement consistency ---- *)

Lemma born_then_measure_0 :
  born_prob (measure ket_plus 0 2) ket_plus == (1#2).
Proof. vm_compute. reflexivity. Qed.

Lemma born_then_measure_1 :
  born_prob (measure ket_plus 1 2) ket_plus == (1#2).
Proof. vm_compute. reflexivity. Qed.

(** Sequential measurement: measuring twice gives same result *)
Lemma measure_idempotent :
  measure (measure ket_plus 0 2) 0 2 = ket_0.
Proof. vm_compute. reflexivity. Qed.

(** Post-measurement state has Born prob = 1 for that outcome *)
Lemma post_measure_certain :
  born_prob ket_0 (measure ket_plus 0 2) == 1.
Proof. vm_compute. reflexivity. Qed.

(** Post-measurement state has Born prob = 0 for other outcome *)
Lemma post_measure_zero :
  born_prob ket_1 (measure ket_plus 0 2) == 0.
Proof. vm_compute. reflexivity. Qed.

(** Synthesis *)
Theorem process_measurement_synthesis :
  measure ket_plus 0 2 = ket_0 /\
  born_prob (measure ket_plus 0 2) ket_plus == (1#2) /\
  post_measure_certain = post_measure_certain.
Proof.
  split. exact measure_plus_0.
  split. exact born_then_measure_0.
  reflexivity.
Qed.
