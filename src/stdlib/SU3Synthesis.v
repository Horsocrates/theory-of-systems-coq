(** * SU3Synthesis.v — SU(3) from Distinction Planes: Synthesis
    Elements: Plane count, generator count, Cartan dimension
    Roles:    Unify distinction-plane derivation of SU(n)
    Rules:    n objects → n²-1 generators, confirmed for n=2,3,4
    Status:   Stdlib
    STATUS: 5 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.SU3Attempt.
Open Scope Q_scope.

(* ================================================================== *)
(*  SU(3) FROM 3 DISTINCTION PLANES                                   *)
(*  3 objects → 3 planes → 6 off-diag + 2 diag = 8 generators        *)
(* ================================================================== *)

Theorem su3_from_planes :
  distinction_planes 3%nat = 3%nat /\
  (2 * distinction_planes 3 + cartan_dim 3)%nat = su_dim 3%nat.
Proof.
  split; [exact planes_3|exact planes_to_generators_3].
Qed.

(* ================================================================== *)
(*  PATTERN: SU(n) for n = 2, 3, 4                                    *)
(* ================================================================== *)

Theorem su_dimension_table :
  su_dim 2%nat = 3%nat /\
  su_dim 3%nat = 8%nat /\
  su_dim 4%nat = 15%nat /\
  su_dim 5%nat = 24%nat.
Proof.
  split; [exact su2_dim|].
  split; [exact su3_dim|].
  split; [exact su4_dim|].
  exact su5_dim.
Qed.

(* Decomposition holds for all checked n *)
Theorem decomposition_universal :
  (off_diag 2 + cartan_dim 2)%nat = su_dim 2%nat /\
  (off_diag 3 + cartan_dim 3)%nat = su_dim 3%nat /\
  (off_diag 4 + cartan_dim 4)%nat = su_dim 4%nat.
Proof.
  split; [exact decomposition_su2|].
  split; [exact decomposition_su3|].
  exact decomposition_su4.
Qed.

(* Tracelessness: defining property of su(n) *)
Theorem tracelessness_verified :
  gellmann_3_trace == 0 /\ gellmann_8_trace == 0.
Proof.
  split; [exact gellmann_3_traceless|exact gellmann_8_traceless].
Qed.

Theorem su3_grand_synthesis :
  su_dim 3%nat = 8%nat /\
  distinction_planes 3%nat = 3%nat /\
  gellmann_3_trace == 0.
Proof.
  split; [exact su3_dim|].
  split; [exact planes_3|].
  exact gellmann_3_traceless.
Qed.
