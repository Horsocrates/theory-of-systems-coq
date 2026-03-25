(** * HeCISynthesisQ.v — Configuration Interaction synthesis for Helium

    Elements: energy levels, correlation energy, basis error
    Roles:    CI -> beyond-HF correction, variational -> energy bounds
    Rules:    E_exact < E_HF < E_1slater (variational principle)
    Status:   synthesis | verified

    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lqa.
From ToS Require Import stdlib.qchem.JIntegralExact.
From ToS Require Import stdlib.qchem.HeEnergyLadder.
Open Scope Q_scope.

(** The 1-Slater energy matches the J-integral computation *)
Theorem ci_1slater_consistent :
  2 * h_one_electron (27 # 16) 2 + J_same (27 # 16) == he_E_1slater.
Proof. vm_compute. reflexivity. Qed.

(** Correlation energy is about 1.4% of total energy *)
(** |E_corr/E_exact| = (21/500)/(29037/10000) = 210000/(500*29037) = 420/29037 *)
Theorem corr_fraction_numerator :
  -(he_E_corr) * 10000 == 420.
Proof. vm_compute. reflexivity. Qed.

(** The basis set error is smaller than correlation energy *)
(** basis_error = 2247/160000 ≈ 0.014, |corr| = 21/500 = 0.042 *)
Theorem basis_lt_corr :
  basis_error < -(he_E_corr).
Proof.
  assert (Hb : basis_error == 2247 # 160000) by (vm_compute; reflexivity).
  assert (Hc : he_E_corr == -(21 # 500)) by (vm_compute; reflexivity).
  rewrite Hb, Hc. lra.
Qed.

(** Full energy ladder *)
Theorem ci_energy_ladder :
  he_E_exact < he_E_HF_limit /\
  he_E_HF_limit < he_E_1slater /\
  he_E_1slater < 0.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

(** The J-integral contributes positively (raises energy) *)
Theorem j_raises_energy :
  2 * h_one_electron (27 # 16) 2 < he_E_1slater.
Proof. vm_compute. reflexivity. Qed.

(** Without J, energy would be much lower *)
Theorem without_j_energy :
  2 * h_one_electron (27 # 16) 2 == -(999 # 256).
Proof. vm_compute. reflexivity. Qed.

(** Repulsion energy contribution *)
Theorem repulsion_contribution :
  he_E_1slater - 2 * h_one_electron (27 # 16) 2 == 135 # 128.
Proof. vm_compute. reflexivity. Qed.

(** Binding relative to He+ + e- threshold (-2 Hartree) *)
Theorem he_is_bound :
  he_E_exact < -(2 # 1).
Proof. vm_compute. reflexivity. Qed.

(** Ionization energy (E_exact - E_He+ where E_He+ = -2) *)
Theorem ionization_energy :
  he_E_exact - (-(2 # 1)) == -(9037 # 10000).
Proof. vm_compute. reflexivity. Qed.

(** E/R/R verification *)
Theorem he_ci_synthesis_err :
  2 * h_one_electron (27 # 16) 2 + J_same (27 # 16) == he_E_1slater /\
  he_E_exact < he_E_HF_limit /\
  he_E_HF_limit < he_E_1slater /\
  he_E_exact < -(2 # 1).
Proof.
  split; [| split; [| split]].
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.
