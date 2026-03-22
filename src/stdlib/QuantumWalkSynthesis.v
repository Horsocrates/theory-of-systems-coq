(** * QuantumWalkSynthesis.v -- Grand Synthesis of Quantum Walk Results
    Elements: asymmetry, spreading, norm verification, return probability
    Roles:    Combines all quantum walk files into unified summary theorems
    Rules:    Every claim backed by exact Q arithmetic; zero axioms
    Status:   complete
    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Lia Lqa.
From ToS Require Import stdlib.QuantumWalkDef.
From ToS Require Import stdlib.QuantumWalkSpreading.
From ToS Require Import stdlib.QuantumInterference.
From ToS Require Import stdlib.QuantumWalkExact.
From ToS Require Import stdlib.QuantumClassicalComparison.
Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(* Grand synthesis: K=3 asymmetry + quantum faster + norm checks       *)
(* ------------------------------------------------------------------ *)

Theorem quantum_walk_K3_summary :
  (* Asymmetry ratio = 5 *)
  P_K3_plus1 == 5 * P_K3_minus1 /\
  (* Norm conservation *)
  P_K3_plus3 + P_K3_plus1 + P_K3_minus1 + P_K3_minus3 == 1 /\
  (* Interference is antisymmetric *)
  interference_plus1 + interference_minus1 == 0.
Proof.
  split; [| split].
  - exact asymmetry_K3_ratio.
  - exact P_K3_sum_one.
  - exact interference_cancels.
Qed.

Theorem quantum_walk_spreading_summary :
  (* Quantum = classical for K<=3 *)
  sigma2_quantum_1 == sigma2_classical 1%nat /\
  sigma2_quantum_3 == sigma2_classical 3%nat /\
  (* Quantum exceeds classical at K=4 *)
  sigma2_quantum_4 > sigma2_classical 4%nat.
Proof.
  split; [| split].
  - exact sigma2_equal_K1.
  - exact sigma2_equal_K3.
  - exact spreading_quantum_faster_K4.
Qed.

Theorem quantum_walk_norm_checks :
  (* K=4 norm = 16 = 2^4 *)
  (K4_m4_L * K4_m4_L + K4_m4_R * K4_m4_R) +
  (K4_m2_L * K4_m2_L + K4_m2_R * K4_m2_R) +
  (K4_z0_L * K4_z0_L + K4_z0_R * K4_z0_R) +
  (K4_p2_L * K4_p2_L + K4_p2_R * K4_p2_R) +
  (K4_p4_L * K4_p4_L + K4_p4_R * K4_p4_R) == 16 /\
  (* K=5 norm = 32 = 2^5 *)
  (K5_m5_L * K5_m5_L + K5_m5_R * K5_m5_R) +
  (K5_m3_L * K5_m3_L + K5_m3_R * K5_m3_R) +
  (K5_m1_L * K5_m1_L + K5_m1_R * K5_m1_R) +
  (K5_p1_L * K5_p1_L + K5_p1_R * K5_p1_R) +
  (K5_p3_L * K5_p3_L + K5_p3_R * K5_p3_R) +
  (K5_p5_L * K5_p5_L + K5_p5_R * K5_p5_R) == 32.
Proof.
  split.
  - exact K4_norm_check.
  - exact K5_norm_check.
Qed.

Theorem quantum_walk_return_probability :
  (* Quantum return < classical at K=4 *)
  P_return_quantum_K4 < P_return_classical_K4 /\
  (* Classical is 3x quantum *)
  P_return_classical_K4 / P_return_quantum_K4 == 3.
Proof.
  split.
  - exact return_quantum_lower_K4.
  - exact return_ratio_K4.
Qed.

Theorem quantum_walk_peaks :
  (* K=4 peak at +2 *)
  K4_p2_L * K4_p2_L + K4_p2_R * K4_p2_R >
  K4_m2_L * K4_m2_L + K4_m2_R * K4_m2_R /\
  (* K=5 peak at +3 *)
  K5_p3_L * K5_p3_L + K5_p3_R * K5_p3_R >
  K5_m3_L * K5_m3_L + K5_m3_R * K5_m3_R.
Proof.
  split.
  - exact K4_peak_at_plus2.
  - exact K5_peak_at_plus3.
Qed.

(* The three quantum-classical differences, unified *)
Theorem quantum_walk_three_differences :
  (* 1. Faster spreading *)
  sigma2_quantum_4 > sigma2_classical 4%nat /\
  (* 2. Broken symmetry *)
  ~ (P_K3_plus1 == P_K3_minus1) /\
  (* 3. Lower return probability *)
  P_return_quantum_K4 < P_return_classical_K4.
Proof. exact three_differences. Qed.

(* Interference is the mechanism *)
Theorem interference_explains_asymmetry :
  (* Constructive at +1 *)
  interference_plus1 == 1 # 4 /\
  (* Destructive at -1 *)
  interference_minus1 == -(1 # 4) /\
  (* Total conserved *)
  interference_plus1 + interference_minus1 == 0.
Proof.
  split; [| split].
  - exact interference_plus1_value.
  - exact interference_minus1_value.
  - exact interference_cancels.
Qed.

Theorem quantum_walk_complete :
  (* K=3 asymmetry *)
  P_K3_plus1 == 5 * P_K3_minus1 /\
  (* Quantum faster at K=4 *)
  sigma2_quantum_4 > sigma2_classical 4%nat /\
  (* K=4 norm = 16 *)
  (K4_m4_L * K4_m4_L + K4_m4_R * K4_m4_R) +
  (K4_m2_L * K4_m2_L + K4_m2_R * K4_m2_R) +
  (K4_z0_L * K4_z0_L + K4_z0_R * K4_z0_R) +
  (K4_p2_L * K4_p2_L + K4_p2_R * K4_p2_R) +
  (K4_p4_L * K4_p4_L + K4_p4_R * K4_p4_R) == 16 /\
  (* Return probability lower *)
  P_return_quantum_K4 < P_return_classical_K4.
Proof.
  split; [| split; [| split]].
  - exact asymmetry_K3_ratio.
  - exact spreading_quantum_faster_K4.
  - exact K4_norm_check.
  - exact return_quantum_lower_K4.
Qed.
