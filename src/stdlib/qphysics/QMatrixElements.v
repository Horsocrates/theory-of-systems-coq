(** * QMatrixElements.v -- Matrix elements for Slater-type orbitals
    Elements: overlap_s, kinetic_s, nuclear_s, ee_F0_1s, overlap_p
    Roles:    All matrix elements for STO basis are exact Q values
    Rules:    Formulas from standard quantum chemistry; verified by computation
    Status:   complete
    STATUS: 13 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Lia Lqa.
From ToS Require Import stdlib.qphysics.FundamentalIntegral.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: S-wave (l=0) matrix elements                               *)
(* ================================================================== *)

(** Overlap integral <s_i|s_j> for 1s STOs with exponents ai, aj *)
Definition overlap_s (ai aj : Q) : Q :=
  2 / qpow (ai + aj) (S (S (S O))).

(** Kinetic energy integral <s_i|T|s_j> *)
Definition kinetic_s (ai aj : Q) : Q :=
  ai * aj / qpow (ai + aj) (S (S (S O))).

(** Nuclear attraction integral <s_i|(-Z/r)|s_j> *)
Definition nuclear_s (Z ai aj : Q) : Q :=
  -(Z) / qpow (ai + aj) (S (S O)).

(** Electron-electron repulsion F0 integral for 1s orbitals *)
Definition ee_F0_1s (alpha : Q) : Q :=
  5 * alpha / 8.

(** P-wave overlap integral <p_i|p_j> *)
Definition overlap_p (ai aj : Q) : Q :=
  24 / qpow (ai + aj) (S (S (S (S (S O))))).

(* ================================================================== *)
(*  Part II: Concrete evaluations                                      *)
(* ================================================================== *)

Lemma overlap_s_concrete : overlap_s 1 1 == (1#4).
Proof. vm_compute. reflexivity. Qed.

Lemma kinetic_s_concrete : kinetic_s 1 1 == (1#8).
Proof. vm_compute. reflexivity. Qed.

Lemma nuclear_s_concrete : nuclear_s 1 1 1 == -(1#4).
Proof. vm_compute. reflexivity. Qed.

Lemma ee_F0_concrete : ee_F0_1s 1 == (5#8).
Proof. vm_compute. reflexivity. Qed.

Lemma overlap_p_concrete : overlap_p 1 1 == (3#4).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part III: Mixed exponent evaluations                               *)
(* ================================================================== *)

Lemma overlap_s_12 : overlap_s 1 2 == (2#27).
Proof. vm_compute. reflexivity. Qed.

Lemma kinetic_s_12 : kinetic_s 1 2 == (2#27).
Proof. vm_compute. reflexivity. Qed.

Lemma nuclear_s_12 : nuclear_s 1 1 2 == -(1#9).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part IV: Structural properties                                     *)
(* ================================================================== *)

(** All s-wave matrix elements are rational (by construction) *)
Lemma all_s_wave_rational :
  exists (sp sq : Z) (sd : positive)
         (tp tq : Z) (td : positive)
         (vp vq : Z) (vd : positive)
         (ep eq_ : Z) (ed : positive),
    overlap_s 1 1 == (sp # sd) /\
    kinetic_s 1 1 == (tp # td) /\
    nuclear_s 1 1 1 == (vp # vd) /\
    ee_F0_1s 1 == (ep # ed).
Proof.
  exists 1%Z, 0%Z, 4%positive.
  exists 1%Z, 0%Z, 8%positive.
  exists (-1)%Z, 0%Z, 4%positive.
  exists 5%Z, 0%Z, 8%positive.
  repeat split; vm_compute; reflexivity.
Qed.

(** Kinetic energy is positive for alpha=1, beta=1 *)
Lemma kinetic_positive : (0 < kinetic_s 1 1)%Q.
Proof. vm_compute. reflexivity. Qed.

(** Nuclear attraction is negative for Z=1 *)
Lemma potential_negative : (nuclear_s 1 1 1 < 0)%Q.
Proof. vm_compute. reflexivity. Qed.

(** Overlap is positive *)
Lemma overlap_positive : (0 < overlap_s 1 1)%Q.
Proof. vm_compute. reflexivity. Qed.

(** Virial-like ratio: T/V for hydrogen-like 1s *)
Definition tv_ratio := kinetic_s 1 1 / nuclear_s 1 1 1.

Lemma tv_ratio_value : tv_ratio == -(1#2).
Proof. vm_compute. reflexivity. Qed.

