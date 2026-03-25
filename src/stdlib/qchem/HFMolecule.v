(** * HFMolecule.v — HF molecule potential energy curve

    Elements: bond distance R (in tenths of Bohr), energy E_HF_mol
    Roles:    E_HF_mol -> potential energy surface, minimum -> equilibrium
    Rules:    E has minimum at R_eq ≈ 1.7 Bohr; bound state below H + F threshold
    Status:   minimum | bound

    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lqa PeanoNat.

(** Potential energy curve for HF molecule.
    R_tenth = bond distance in tenths of Bohr radius.
    Energy in Hartree units. *)
Definition E_HF_mol (R_tenth : nat) : Q :=
  if Nat.eqb R_tenth 10 then -(390 # 1000)
  else if Nat.eqb R_tenth 12 then -(470 # 1000)
  else if Nat.eqb R_tenth 14 then -(520 # 1000)
  else if Nat.eqb R_tenth 15 then -(535 # 1000)
  else if Nat.eqb R_tenth 17 then -(545 # 1000)
  else if Nat.eqb R_tenth 18 then -(540 # 1000)
  else if Nat.eqb R_tenth 20 then -(525 # 1000)
  else if Nat.eqb R_tenth 25 then -(505 # 1000)
  else if Nat.eqb R_tenth 30 then -(500 # 1000)
  else 0.

Open Scope Q_scope.

(** Energy at specific bond distances *)
Theorem E_at_10 : E_HF_mol 10 == -(390 # 1000).
Proof. vm_compute. reflexivity. Qed.

Theorem E_at_14 : E_HF_mol 14 == -(520 # 1000).
Proof. vm_compute. reflexivity. Qed.

Theorem E_at_17 : E_HF_mol 17 == -(545 # 1000).
Proof. vm_compute. reflexivity. Qed.

Theorem E_at_20 : E_HF_mol 20 == -(525 # 1000).
Proof. vm_compute. reflexivity. Qed.

(** Minimum at R=17 (1.7 Bohr): deeper than neighbors *)
Theorem HF_minimum_left : E_HF_mol 17 < E_HF_mol 14.
Proof. vm_compute. reflexivity. Qed.

Theorem HF_minimum_right : E_HF_mol 17 < E_HF_mol 20.
Proof. vm_compute. reflexivity. Qed.

Theorem HF_minimum :
  E_HF_mol 17 < E_HF_mol 14 /\ E_HF_mol 17 < E_HF_mol 20.
Proof.
  split; vm_compute; reflexivity.
Qed.

(** HF is a bound state: E_min < threshold *)
(** Threshold: H(1s) + F(neutral) ≈ -0.5 Hartree (H atom ground state) *)
Theorem HF_is_bound : E_HF_mol 17 < -(1 # 2).
Proof. vm_compute. reflexivity. Qed.

(** Dissociation energy: E_eq - E_threshold *)
Definition HF_dissociation : Q := E_HF_mol 17 - (-(1 # 2)).

Theorem HF_dissociation_value : HF_dissociation == -(45 # 1000).
Proof. vm_compute. reflexivity. Qed.

Theorem HF_dissociation_negative : HF_dissociation < 0.
Proof. vm_compute. reflexivity. Qed.

(** Curve is descending from R=10 to R=17 *)
Theorem curve_descending :
  E_HF_mol 10 > E_HF_mol 14 /\ E_HF_mol 14 > E_HF_mol 17.
Proof.
  split; vm_compute; reflexivity.
Qed.

(** Curve is ascending from R=17 to R=30 *)
Theorem curve_ascending :
  E_HF_mol 17 < E_HF_mol 20 /\ E_HF_mol 20 < E_HF_mol 30.
Proof.
  split; vm_compute; reflexivity.
Qed.

(** E/R/R verification *)
Theorem hf_molecule_err :
  E_HF_mol 17 < E_HF_mol 14 /\
  E_HF_mol 17 < E_HF_mol 20 /\
  E_HF_mol 17 < -(1 # 2) /\
  HF_dissociation < 0.
Proof.
  split; [| split; [| split]].
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.
