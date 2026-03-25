(** * HeSlaterBasis.v -- Helium 1s STO basis with multiple exponents
    Elements: he_alpha_1, he_alpha_2, overlap/kinetic/nuclear for He basis
    Roles:    Concrete Q matrix elements for 2-STO helium basis
    Rules:    All integrals computed exactly via qpow; verified by vm_compute
    Status:   complete
    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Lia Lqa.
From ToS Require Import stdlib.qphysics.FundamentalIntegral.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Helium basis exponents                                     *)
(* ================================================================== *)

(** Optimized exponent for He 1s (Slater's rules: Z_eff = 27/16) *)
Definition he_alpha_1 : Q := 27#16.

(** Second exponent for 2-STO basis *)
Definition he_alpha_2 : Q := 3#2.

(** Nuclear charge of helium *)
Definition he_Z : Q := 2.

(* ================================================================== *)
(*  Part II: Local matrix element functions (for independence)         *)
(* ================================================================== *)

(** Overlap integral <s_i|s_j> for unnormalized 1s STOs *)
Definition overlap_s_local (ai aj : Q) : Q :=
  2 / qpow (ai + aj) (S (S (S O))).

(** Kinetic energy integral <s_i|T|s_j> for unnormalized 1s STOs *)
Definition kinetic_s_local (ai aj : Q) : Q :=
  ai * aj / qpow (ai + aj) (S (S (S O))).

(** Nuclear attraction integral <s_i|(-Z/r)|s_j> for unnormalized 1s STOs *)
Definition nuclear_s_local (Z ai aj : Q) : Q :=
  -(Z) / qpow (ai + aj) (S (S O)).

(* ================================================================== *)
(*  Part III: Overlap matrix elements                                  *)
(* ================================================================== *)

Lemma he_S11 : overlap_s_local he_alpha_1 he_alpha_1 == 1024#19683.
Proof. vm_compute. reflexivity. Qed.

Lemma he_S12 : overlap_s_local he_alpha_1 he_alpha_2 == 8192#132651.
Proof. vm_compute. reflexivity. Qed.

Lemma he_S22 : overlap_s_local he_alpha_2 he_alpha_2 == 2#27.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part IV: Kinetic energy matrix elements                            *)
(* ================================================================== *)

Lemma he_T11 : kinetic_s_local he_alpha_1 he_alpha_1 == 2#27.
Proof. vm_compute. reflexivity. Qed.

Lemma he_T12 : kinetic_s_local he_alpha_1 he_alpha_2 == 384#4913.
Proof. vm_compute. reflexivity. Qed.

Lemma he_T22 : kinetic_s_local he_alpha_2 he_alpha_2 == 1#12.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part V: Nuclear attraction matrix elements (Z=2)                   *)
(* ================================================================== *)

Lemma he_V11 : nuclear_s_local he_Z he_alpha_1 he_alpha_1 == -(128#729).
Proof. vm_compute. reflexivity. Qed.

Lemma he_V12 : nuclear_s_local he_Z he_alpha_1 he_alpha_2 == -(512#2601).
Proof. vm_compute. reflexivity. Qed.

Lemma he_V22 : nuclear_s_local he_Z he_alpha_2 he_alpha_2 == -(2#9).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part VI: Structural properties                                     *)
(* ================================================================== *)

(** All overlap elements are positive *)
Lemma he_overlaps_positive :
  (0 < overlap_s_local he_alpha_1 he_alpha_1) /\
  (0 < overlap_s_local he_alpha_1 he_alpha_2) /\
  (0 < overlap_s_local he_alpha_2 he_alpha_2).
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

(** All kinetic elements are positive *)
Lemma he_kinetics_positive :
  (0 < kinetic_s_local he_alpha_1 he_alpha_1) /\
  (0 < kinetic_s_local he_alpha_1 he_alpha_2) /\
  (0 < kinetic_s_local he_alpha_2 he_alpha_2).
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

(** All nuclear attractions are negative *)
Lemma he_nuclear_negative :
  (nuclear_s_local he_Z he_alpha_1 he_alpha_1 < 0) /\
  (nuclear_s_local he_Z he_alpha_1 he_alpha_2 < 0) /\
  (nuclear_s_local he_Z he_alpha_2 he_alpha_2 < 0).
Proof.
  repeat split; vm_compute; reflexivity.
Qed.
