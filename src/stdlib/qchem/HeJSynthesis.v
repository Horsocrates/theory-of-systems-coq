(** * HeJSynthesis.v — Synthesis of J-integral results for Helium

    Elements: J_same, J_cross, h_one_electron computations
    Roles:    same-exponent -> diagonal, cross-exponent -> off-diagonal
    Rules:    variational energy = 2h + J (constitution)
    Status:   synthesis | verified

    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lqa.
From ToS Require Import stdlib.qchem.JIntegralExact.
From ToS Require Import stdlib.qchem.JCrossTerms.
Open Scope Q_scope.

(** Grand synthesis: J-integral results *)
Theorem he_j_synthesis :
  J_same (27 # 16) == 135 # 128 /\
  J_cross 1 2 == 5 # 6 /\
  J_cross 1 (5 # 2) == 25 # 28 /\
  2 * h_one_electron (27 # 16) 2 + J_same (27 # 16) == -(729 # 256).
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

(** Cross terms are smaller than same-exponent terms *)
Theorem cross_smaller_than_same :
  J_cross 1 2 < J_same 2 /\
  J_cross 1 (5 # 2) < J_same (5 # 2).
Proof.
  split; vm_compute; reflexivity.
Qed.

(** Same-exponent J at optimized He exponent *)
Theorem he_optimal_J : J_same (27 # 16) == 135 # 128.
Proof. vm_compute. reflexivity. Qed.

(** The variational energy with optimal exponent *)
Theorem he_variational_energy :
  2 * h_one_electron (27 # 16) 2 + J_same (27 # 16) == -(729 # 256).
Proof. vm_compute. reflexivity. Qed.

(** Energy decomposition: kinetic + nuclear + repulsion *)
Theorem he_energy_decomposition :
  let h := h_one_electron (27 # 16) 2 in
  let j := J_same (27 # 16) in
  h == -(999 # 512) /\ j == 135 # 128 /\ 2 * h + j == -(729 # 256).
Proof.
  simpl. repeat split; vm_compute; reflexivity.
Qed.

(** J_cross symmetry verification *)
Theorem j_cross_symmetry_check :
  J_cross 1 2 == J_cross 2 1 /\
  J_cross 1 (5 # 2) == J_cross (5 # 2) 1.
Proof.
  split; vm_compute; reflexivity.
Qed.

(** All J integrals positive *)
Theorem all_j_positive :
  J_same (27 # 16) > 0 /\
  J_cross 1 2 > 0 /\
  J_cross 1 (5 # 2) > 0.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

(** J_same at He optimal vs hydrogen *)
Theorem j_he_vs_hydrogen :
  J_same (27 # 16) > J_same 1.
Proof. vm_compute. reflexivity. Qed.

(** Cross-term ratio *)
Theorem j_cross_ratio :
  J_cross 1 2 / J_cross 1 (5 # 2) == 70 # 75.
Proof. vm_compute. reflexivity. Qed.

(** E/R/R verification *)
Theorem he_j_synthesis_err :
  J_same (27 # 16) == 135 # 128 /\
  J_cross 1 2 == 5 # 6 /\
  2 * h_one_electron (27 # 16) 2 + J_same (27 # 16) == -(729 # 256) /\
  J_cross 1 2 == J_cross 2 1.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.
