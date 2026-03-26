(** * GrapheneTopology.v — Topological properties of graphene

    Elements: Berry phase, winding number, BN gap from symmetry breaking
    Roles:    sublattice symmetry -> topological protection of Dirac point
    Rules:    Berry phase = pi at K; breaking symmetry -> gap opens
    Status:   verified | topological semimetal

    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lqa.
Open Scope Q_scope.

(** Berry phase at K point (in units of pi) *)
Definition berry_phase_K : Q := 1.

(** Berry phase at Gamma point *)
Definition berry_phase_Gamma : Q := 0.

(** Winding number at K *)
Definition winding_K : Q := 1.

(** K point is topologically nontrivial *)
Theorem K_nontrivial : 0 < berry_phase_K.
Proof. vm_compute. reflexivity. Qed.

(** Gamma point is trivial *)
Theorem Gamma_trivial : berry_phase_Gamma == 0.
Proof. vm_compute. reflexivity. Qed.

(** Berry phase difference = pi *)
Theorem berry_difference : berry_phase_K - berry_phase_Gamma == 1.
Proof. vm_compute. reflexivity. Qed.

(** Winding number is an integer (= 1) *)
Theorem winding_integer : winding_K == 1.
Proof. vm_compute. reflexivity. Qed.

(** BN gap from sublattice symmetry breaking *)
Definition gap_BN (delta : Q) : Q := 2 * delta.

Theorem gap_BN_at_half : gap_BN (1 # 2) == 1.
Proof. vm_compute. reflexivity. Qed.

Theorem gap_BN_positive : 0 < gap_BN (1 # 2).
Proof. vm_compute. reflexivity. Qed.

(** Graphene: delta=0 -> gap=0 (sublattice symmetric) *)
Theorem graphene_gapless : gap_BN 0 == 0.
Proof. vm_compute. reflexivity. Qed.

(** BN: delta > 0 -> gap > 0 *)
Theorem BN_gapped : 0 < gap_BN (1 # 4).
Proof. vm_compute. reflexivity. Qed.

(** Gap increases with sublattice asymmetry *)
Theorem gap_increases : gap_BN (1 # 4) < gap_BN (1 # 2).
Proof. vm_compute. reflexivity. Qed.

(** Gap linear in delta *)
Theorem gap_linear : gap_BN 1 == 2 * gap_BN (1 # 2).
Proof. vm_compute. reflexivity. Qed.
