(** * HFSynthesis.v — Grand synthesis: He CI + HF molecule results

    Elements: He energy ladder, HF potential curve, J-integrals
    Roles:    variational -> energy bounds, equilibrium -> bound state
    Rules:    He CI converges; HF has minimum; both are bound states
    Status:   synthesis | verified

    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lqa.
From ToS Require Import stdlib.qchem.JIntegralExact.
From ToS Require Import stdlib.qchem.HeEnergyLadder.
From ToS Require Import stdlib.qchem.HFMolecule.
Open Scope Q_scope.

(** He CI and HF molecule are both bound states *)
Theorem both_bound :
  he_E_exact < -(2 # 1) /\ E_HF_mol 17 < -(1 # 2).
Proof.
  split; vm_compute; reflexivity.
Qed.

(** He 1-Slater from J-integral matches energy ladder *)
Theorem he_consistency :
  2 * h_one_electron (27 # 16) 2 + J_same (27 # 16) == he_E_1slater.
Proof. vm_compute. reflexivity. Qed.

(** He energy ordering *)
Theorem he_ladder :
  he_E_exact < he_E_HF_limit /\ he_E_HF_limit < he_E_1slater.
Proof.
  split; vm_compute; reflexivity.
Qed.

(** HF has a potential minimum *)
Theorem hf_has_minimum :
  E_HF_mol 17 < E_HF_mol 14 /\ E_HF_mol 17 < E_HF_mol 20.
Proof.
  split; vm_compute; reflexivity.
Qed.

(** He is more deeply bound than HF *)
Theorem he_deeper_than_hf :
  he_E_exact < E_HF_mol 17.
Proof. vm_compute. reflexivity. Qed.

(** Correlation energy for He is small *)
Theorem he_corr_small : -(he_E_corr) < 5 # 100.
Proof.
  assert (Hv : he_E_corr == -(21 # 500)) by (vm_compute; reflexivity).
  rewrite Hv. lra.
Qed.

(** HF dissociation energy magnitude *)
Theorem hf_diss_magnitude : -(HF_dissociation) < 1 # 10.
Proof.
  assert (Hv : HF_dissociation == -(45 # 1000)) by (vm_compute; reflexivity).
  rewrite Hv. lra.
Qed.

(** J-integral value at He optimal exponent *)
Theorem he_repulsion : J_same (27 # 16) == 135 # 128.
Proof. vm_compute. reflexivity. Qed.

(** Both systems have negative total energy (bound) *)
Theorem both_negative :
  he_E_1slater < 0 /\ E_HF_mol 17 < 0.
Proof.
  split; vm_compute; reflexivity.
Qed.

(** Grand E/R/R synthesis *)
Theorem hf_grand_synthesis :
  he_E_exact < -(2 # 1) /\
  E_HF_mol 17 < -(1 # 2) /\
  2 * h_one_electron (27 # 16) 2 + J_same (27 # 16) == he_E_1slater /\
  E_HF_mol 17 < E_HF_mol 14 /\
  E_HF_mol 17 < E_HF_mol 20.
Proof.
  split; [| split; [| split; [| split]]].
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.
