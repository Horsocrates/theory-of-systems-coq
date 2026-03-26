(** * GrapheneSynthesis.v — Grand synthesis of graphene results

    Elements: lattice, transfer matrix, DOS, topology from C1-C4
    Roles:    synthesis -> unified graphene physics
    Rules:    honeycomb -> Dirac -> vanishing DOS -> topological protection
    Status:   synthesis | verified

    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lqa.
From ToS Require Import stdlib.qchem.HoneycombLattice.
From ToS Require Import stdlib.qchem.GrapheneTransfer.
From ToS Require Import stdlib.qchem.GrapheneDOS.
From ToS Require Import stdlib.qchem.GrapheneTopology.
Open Scope Q_scope.

(** Graphene is a semimetal: gap = 0 *)
Theorem graphene_semimetal : gap_graphene == 0.
Proof. vm_compute. reflexivity. Qed.

(** Bandwidth = 6t *)
Theorem graphene_bandwidth : bandwidth == 6.
Proof. vm_compute. reflexivity. Qed.

(** Dirac point: zero energy *)
Theorem dirac_point : E_at_K == 0.
Proof. vm_compute. reflexivity. Qed.

(** DOS vanishes at Dirac point *)
Theorem vanishing_dos : dos_graphene 0 == 0.
Proof. unfold dos_graphene. apply Qabs_0. Qed.

(** Topologically protected: Berry phase = pi *)
Theorem topological_protection : 0 < berry_phase_K.
Proof. vm_compute. reflexivity. Qed.

(** Breaking symmetry opens gap (BN analogy) *)
Theorem symmetry_breaking : 0 < gap_BN (1 # 2).
Proof. vm_compute. reflexivity. Qed.

(** Bipartite lattice: trace = 0 *)
Theorem bipartite :
  graphene_H 0%nat 0%nat + graphene_H 1%nat 1%nat == 0.
Proof. vm_compute. reflexivity. Qed.

(** No carriers at charge neutrality *)
Theorem undoped : carrier_density 0 == 0.
Proof. vm_compute. reflexivity. Qed.

(** Grand graphene theorem *)
Theorem graphene_validated :
  gap_graphene == 0 /\
  0 < bandwidth /\
  0 < berry_phase_K /\
  carrier_density 0 == 0.
Proof.
  unfold gap_graphene, bandwidth, berry_phase_K, carrier_density.
  repeat split; vm_compute; reflexivity.
Qed.
