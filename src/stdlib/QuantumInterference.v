(** * QuantumInterference.v -- Quantum Walk Interference Analysis
    Elements: L-component amplitudes, classical probabilities, interference terms
    Roles:    Interference causes asymmetry; L-component cancellation at pos -1
    Rules:    Classical P(+1)=P(-1)=3/8; quantum breaks this symmetry via interference
    Status:   complete
    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Lia Lqa.
From ToS Require Import stdlib.QuantumWalkDef.
Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(* L-component analysis at K=3                                         *)
(* Position -1: L-component = 1, R-component = 0                      *)
(* Position +1: L-component = -2, R-component = -1                    *)
(* The L-component at -1 is nonzero but small (1 vs 2 at +1)          *)
(* ------------------------------------------------------------------ *)

Lemma L_component_minus1_K3 :
  amp_K3_minus1_L == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma R_component_minus1_K3 :
  amp_K3_minus1_R == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma L_component_plus1_K3 :
  amp_K3_plus1_L == -(2).
Proof. vm_compute. reflexivity. Qed.

Lemma R_component_plus1_K3 :
  amp_K3_plus1_R == -(1).
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Classical probabilities at K=3 (symmetric random walk)              *)
(* Classical: P(+3)=1/8, P(+1)=3/8, P(-1)=3/8, P(-3)=1/8            *)
(* ------------------------------------------------------------------ *)

Definition P_classical_K3_plus3 : Q := 1 # 8.
Definition P_classical_K3_plus1 : Q := 3 # 8.
Definition P_classical_K3_minus1 : Q := 3 # 8.
Definition P_classical_K3_minus3 : Q := 1 # 8.

Lemma P_classical_K3_sum :
  P_classical_K3_plus3 + P_classical_K3_plus1 +
  P_classical_K3_minus1 + P_classical_K3_minus3 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma P_classical_K3_symmetric :
  P_classical_K3_plus1 == P_classical_K3_minus1.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Quantum vs classical: asymmetry comparison                          *)
(* Quantum: P(+1) = 5/8, P(-1) = 1/8                                  *)
(* Classical: P(+1) = 3/8, P(-1) = 3/8                                *)
(* ------------------------------------------------------------------ *)

Lemma quantum_plus1_exceeds_classical :
  P_K3_plus1 > P_classical_K3_plus1.
Proof. unfold P_K3_plus1, P_classical_K3_plus1, Qlt. simpl. lia. Qed.

Lemma quantum_minus1_below_classical :
  P_K3_minus1 < P_classical_K3_minus1.
Proof. unfold P_K3_minus1, P_classical_K3_minus1, Qlt. simpl. lia. Qed.

(* ------------------------------------------------------------------ *)
(* Interference quantification                                         *)
(* Delta_plus1 = P_q(+1) - P_c(+1) = 5/8 - 3/8 = 2/8 = 1/4         *)
(* Delta_minus1 = P_q(-1) - P_c(-1) = 1/8 - 3/8 = -2/8 = -1/4      *)
(* ------------------------------------------------------------------ *)

Definition interference_plus1 : Q := P_K3_plus1 - P_classical_K3_plus1.
Definition interference_minus1 : Q := P_K3_minus1 - P_classical_K3_minus1.

Lemma interference_plus1_value :
  interference_plus1 == 1 # 4.
Proof. vm_compute. reflexivity. Qed.

Lemma interference_minus1_value :
  interference_minus1 == -(1 # 4).
Proof. vm_compute. reflexivity. Qed.

(* Interference conserves total probability *)
Lemma interference_cancels :
  interference_plus1 + interference_minus1 == 0.
Proof. vm_compute. reflexivity. Qed.

(* Interference magnitude *)
Lemma interference_magnitude :
  interference_plus1 == -(interference_minus1).
Proof. vm_compute. reflexivity. Qed.

(* L2 connection: amplitude squared gives probability *)
Lemma amp_squared_K3_plus1 :
  amp_K3_plus1_L * amp_K3_plus1_L + amp_K3_plus1_R * amp_K3_plus1_R == 5.
Proof. vm_compute. reflexivity. Qed.

Lemma amp_squared_K3_minus1 :
  amp_K3_minus1_L * amp_K3_minus1_L + amp_K3_minus1_R * amp_K3_minus1_R == 1.
Proof. vm_compute. reflexivity. Qed.
