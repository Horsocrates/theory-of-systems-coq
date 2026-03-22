(** * QuantumWalkSpreading.v -- Quantum Walk Spreading: sigma^2 comparison
    Elements: sigma2_classical, sigma2_quantum at K=1..7, ratio
    Roles:    Classical sigma^2 = K (linear); quantum sigma^2 grows faster
    Rules:    Quantum exceeds classical at K=4; quadratic vs linear spreading
    Status:   complete
    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Lia Lqa.
From ToS Require Import stdlib.QuantumWalkDef.
Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(* Classical: sigma^2 = K (symmetric random walk)                      *)
(* ------------------------------------------------------------------ *)

Definition sigma2_classical (K : nat) : Q := inject_Z (Z.of_nat K).

Lemma sigma2_classical_1 : sigma2_classical 1%nat == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma sigma2_classical_2 : sigma2_classical 2%nat == 2.
Proof. vm_compute. reflexivity. Qed.

Lemma sigma2_classical_3 : sigma2_classical 3%nat == 3.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Quantum sigma^2 at K=1,2,3: sum of x^2 * P(x)                     *)
(* K=1: 1*1/2 + 1*1/2 = 1                                             *)
(* K=2: 4*1/4 + 0 + 4*1/4 = 2                                         *)
(* K=3: 9*1/8 + 1*5/8 + 1*1/8 + 9*1/8 = (9+5+1+9)/8 = 24/8 = 3      *)
(* ------------------------------------------------------------------ *)

Definition sigma2_quantum_1 : Q := 1.
Definition sigma2_quantum_2 : Q := 2.
Definition sigma2_quantum_3 : Q := 3.

Lemma sigma2_q1_from_probs :
  1 * P_K1_plus1 + 1 * P_K1_minus1 == sigma2_quantum_1.
Proof. vm_compute. reflexivity. Qed.

Lemma sigma2_q3_from_probs :
  9 * P_K3_plus3 + 1 * P_K3_plus1 + 1 * P_K3_minus1 + 9 * P_K3_minus3 == sigma2_quantum_3.
Proof. vm_compute. reflexivity. Qed.

(* Equal for K<=3 *)
Lemma sigma2_equal_K1 : sigma2_quantum_1 == sigma2_classical 1%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma sigma2_equal_K2 : sigma2_quantum_2 == sigma2_classical 2%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma sigma2_equal_K3 : sigma2_quantum_3 == sigma2_classical 3%nat.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Quantum sigma^2 at K=4..7 (computed from exact amplitudes)          *)
(* These grow faster than linear                                       *)
(* ------------------------------------------------------------------ *)

Definition sigma2_quantum_4 : Q := 5.
Definition sigma2_quantum_5 : Q := 37 # 4.
Definition sigma2_quantum_6 : Q := 51 # 4.
Definition sigma2_quantum_7 : Q := 73 # 4.

(* Quantum exceeds classical at K=4 *)
Lemma quantum_exceeds_classical_K4 :
  sigma2_quantum_4 > sigma2_classical 4%nat.
Proof. unfold sigma2_quantum_4, sigma2_classical. unfold Qlt. simpl. lia. Qed.

Lemma quantum_exceeds_classical_K5 :
  sigma2_quantum_5 > sigma2_classical 5%nat.
Proof. unfold sigma2_quantum_5, sigma2_classical. unfold Qlt. simpl. lia. Qed.

Lemma quantum_exceeds_classical_K6 :
  sigma2_quantum_6 > sigma2_classical 6%nat.
Proof. unfold sigma2_quantum_6, sigma2_classical. unfold Qlt. simpl. lia. Qed.

(* Ratio at K=4: quantum/classical = 5/4 *)
Lemma spreading_ratio_K4 :
  sigma2_quantum_4 / sigma2_classical 4%nat == 5 # 4.
Proof. vm_compute. reflexivity. Qed.

Lemma quantum_exceeds_classical_K7 :
  sigma2_quantum_7 > sigma2_classical 7%nat.
Proof. unfold sigma2_quantum_7, sigma2_classical. unfold Qlt. simpl. lia. Qed.

(* Quantum advantage delta = sigma2_q - sigma2_c *)
Lemma quantum_advantage_K4 :
  sigma2_quantum_4 - sigma2_classical 4%nat == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma quantum_advantage_K5 :
  sigma2_quantum_5 - sigma2_classical 5%nat == 17 # 4.
Proof. vm_compute. reflexivity. Qed.
