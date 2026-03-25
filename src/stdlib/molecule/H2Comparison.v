(** * H2Comparison.v -- Compare our H₂ energy with exact and Hartree-Fock
    Elements: H2_our, H2_exact, H2_HF
    Roles:    Variational ordering: exact ≤ HF ≤ our (simple LCAO)
    Rules:    Qabs-based error bounds, energy ordering
    Status:   Stdlib/molecule
    STATUS: 7 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

(* ================================================================== *)
(*  REFERENCE ENERGY VALUES                                            *)
(* ================================================================== *)

(** Our simple LCAO-MO result *)
Definition H2_our : Q := -(1094#1000).

(** Exact non-relativistic energy (Kolos & Wolniewicz) *)
Definition H2_exact : Q := -(11745#10000).

(** Hartree-Fock limit *)
Definition H2_HF : Q := -(11336#10000).

(* ================================================================== *)
(*  ERROR ANALYSIS                                                     *)
(* ================================================================== *)

(** Difference: our - exact *)
Lemma our_minus_exact : H2_our - H2_exact == 805#10000.
Proof. unfold H2_our, H2_exact. vm_compute. reflexivity. Qed.

(** The difference is positive, so Qabs is identity *)
Lemma qabs_our_exact : Qabs (H2_our - H2_exact) == 805#10000.
Proof.
  rewrite our_minus_exact. vm_compute. reflexivity.
Qed.

(** Error is less than 0.1 Hartree *)
Lemma our_vs_exact : Qabs (H2_our - H2_exact) < 1#10.
Proof. rewrite qabs_our_exact. lra. Qed.

(** Difference: our - HF *)
Lemma our_minus_HF : H2_our - H2_HF == 396#10000.
Proof. unfold H2_our, H2_HF. vm_compute. reflexivity. Qed.

Lemma qabs_our_HF : Qabs (H2_our - H2_HF) == 396#10000.
Proof. rewrite our_minus_HF. vm_compute. reflexivity. Qed.

(** Error vs HF is less than 0.05 Hartree *)
Lemma our_vs_HF : Qabs (H2_our - H2_HF) < 1#20.
Proof. rewrite qabs_our_HF. lra. Qed.

(* ================================================================== *)
(*  VARIATIONAL ENERGY ORDERING                                        *)
(* ================================================================== *)

(** Variational principle: more approximate = higher energy
    exact ≤ HF ≤ our (simple LCAO) *)
Lemma energy_ordering : H2_exact < H2_HF /\ H2_HF < H2_our.
Proof. unfold H2_exact, H2_HF, H2_our. split; lra. Qed.
