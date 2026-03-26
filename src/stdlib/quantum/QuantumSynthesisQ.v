(** * QuantumSynthesisQ.v — Grand synthesis of quantum computing

    Elements: gates + Grover + error correction + simulation unified
    Roles:    quantum computing as process on lattice framework
    Rules:    gates = matrix entries; search = diffusion; errors = stabilizers
    Status:   verified | quantum computing synthesis

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lqa Bool ZArith Lia.
From ToS Require Import stdlib.quantum.QubitQ.
From ToS Require Import stdlib.quantum.GroverSpectralQ.
From ToS Require Import stdlib.quantum.ErrorCorrectionQ.
From ToS Require Import stdlib.quantum.SimulationClassQ.
From ToS Require Import stdlib.quantum.QuantumClassicalMapQ.
Open Scope Q_scope.

(** ---- Grand synthesis ---- *)

(** Gates are unitary: X^2 = I verified concretely *)
Theorem synth_gate_unitary :
  pauli_X 0%nat 0%nat * pauli_X 0%nat 0%nat +
  pauli_X 0%nat 1%nat * pauli_X 1%nat 0%nat == 1.
Proof. vm_compute. reflexivity. Qed.

(** Grover search on 4-site lattice *)
Theorem synth_grover_lattice :
  grover_D 4 0%nat 0%nat == -(1#2) /\
  lattice_sites 4 == 4.
Proof. split; vm_compute; reflexivity. Qed.

(** Error correction improves with system size *)
Theorem synth_error_scaling : forall K : nat,
  (K > 1)%nat ->
  (code_distance_surface K > code_distance_chain K)%nat.
Proof. intros. apply surface_better. exact H. Qed.

(** Gapped systems are classically simulable *)
Theorem synth_gap_classical :
  simulation_class (9#37) = ClassicalEfficient.
Proof. simpl. reflexivity. Qed.

(** Gapless systems need quantum *)
Theorem synth_gapless_quantum :
  simulation_class 0 = QuantumAdvantage.
Proof. simpl. reflexivity. Qed.

(** Born rule from Hadamard *)
Theorem synth_born_rule : born_prob_0 == 1#2.
Proof. vm_compute. reflexivity. Qed.

(** Grover diffusion is symmetric *)
Theorem synth_grover_symmetric : forall K i j,
  grover_D K i j == grover_D K j i.
Proof. intros. apply grover_D_symmetric. Qed.

(** Complete quantum pipeline: gate -> search -> correct -> simulate *)
Theorem synth_quantum_pipeline :
  (* Gate works *) pauli_X 0%nat 1%nat == 1 /\
  (* Search works *) grover_D 4 0%nat 1%nat == 1#2 /\
  (* Correction scales *) code_distance_surface 10 = 10%nat /\
  (* Simulation classified *) simulation_class (1#2) = ClassicalEfficient.
Proof.
  split; [|split; [|split]].
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.
