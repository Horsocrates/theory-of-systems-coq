(** * SlaterBasis.v — Slater-Type Orbital Basis on Discrete Lattice
    Elements: Padé [2,2] approximant, STO-1s, STO-2s basis functions, lattice sites
    Roles:    Provide rational wavefunction basis for quantum chemistry on finite lattice
    Rules:    φ_1s(i) = pade22(ζ·(i+1)/M); φ_2s(i) = (i+1)/M · φ_1s(i);
              pade22(x) = (12-6x+x²)/(12+6x+x²) ≈ exp(-x)
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.

(* ================================================================== *)
(*  PADÉ [2,2] APPROXIMANT FOR exp(-x)  (standalone)                  *)
(* ================================================================== *)

Definition pade22_local (x : Q) : Q := (12 - 6*x + x*x) / (12 + 6*x + x*x).

(* ================================================================== *)
(*  CONCRETE PADÉ VALUES                                               *)
(* ================================================================== *)

Lemma pade22_at_0 : pade22_local 0 == 1.
Proof. unfold pade22_local. vm_compute. reflexivity. Qed.

Lemma pade22_at_1 : pade22_local 1 == 7 # 19.
Proof. unfold pade22_local. vm_compute. reflexivity. Qed.

Lemma pade22_at_half : pade22_local (1#2) == 37 # 61.
Proof. unfold pade22_local. vm_compute. reflexivity. Qed.

Lemma pade22_at_third : pade22_local (1#3) == 91 # 127.
Proof. unfold pade22_local. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  STO-1s: φ_1s(i, ζ, M) = pade22(ζ·(i+1)/M)                       *)
(* ================================================================== *)

Definition sto_1s (zeta : Q) (M : nat) (i : nat) : Q :=
  pade22_local (zeta * inject_Z (Z.of_nat (S i)) / inject_Z (Z.of_nat M)).

(* ================================================================== *)
(*  STO-2s: φ_2s(i, ζ, M) = (i+1)/M · φ_1s(i, ζ, M)                *)
(* ================================================================== *)

Definition sto_2s (zeta : Q) (M : nat) (i : nat) : Q :=
  inject_Z (Z.of_nat (S i)) / inject_Z (Z.of_nat M) * sto_1s zeta M i.

(* ================================================================== *)
(*  CONCRETE STO-1s VALUES (ζ=1, M=3)                                 *)
(*  i=0: pade22(1/3) = 91/127                                         *)
(*  i=1: pade22(2/3) = 19/37                                          *)
(*  i=2: pade22(1)   = 7/19                                           *)
(* ================================================================== *)

Lemma sto_1s_val_0 : sto_1s 1 3 O == 91 # 127.
Proof. unfold sto_1s, pade22_local. vm_compute. reflexivity. Qed.

Lemma sto_1s_val_1 : sto_1s 1 3 (S O) == 19 # 37.
Proof. unfold sto_1s, pade22_local. vm_compute. reflexivity. Qed.

Lemma sto_1s_val_2 : sto_1s 1 3 (S (S O)) == 7 # 19.
Proof. unfold sto_1s, pade22_local. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  POSITIVITY: pade22(x) > 0 for 0 <= x <= 1                        *)
(*  Numerator 12 - 6x + x² = (x-3)² + 3 > 0 always                  *)
(*  Denominator 12 + 6x + x² = (x+3)² + 3 > 0 always                *)
(* ================================================================== *)

Lemma pade22_num_pos : forall x : Q, 0 <= x -> x <= 1 -> 0 < 12 - 6*x + x*x.
Proof.
  intros x Hx0 Hx1. nra.
Qed.

Lemma pade22_den_pos : forall x : Q, 0 <= x -> 0 < 12 + 6*x + x*x.
Proof.
  intros x Hx0. nra.
Qed.

(* ================================================================== *)
(*  CONCRETE STO-2s VALUES (ζ=1, M=3)                                 *)
(*  i=0: (1/3)·(91/127) = 91/381                                     *)
(*  i=1: (2/3)·(19/37)  = 38/111                                     *)
(*  i=2: (3/3)·(7/19)   = 7/19                                       *)
(* ================================================================== *)

Lemma sto_2s_val_0 : sto_2s 1 3 O == 91 # 381.
Proof. unfold sto_2s, sto_1s, pade22_local. vm_compute. reflexivity. Qed.

Lemma sto_2s_val_1 : sto_2s 1 3 (S O) == 38 # 111.
Proof. unfold sto_2s, sto_1s, pade22_local. vm_compute. reflexivity. Qed.

Lemma sto_2s_val_2 : sto_2s 1 3 (S (S O)) == 7 # 19.
Proof. unfold sto_2s, sto_1s, pade22_local. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  DECAY: sto_1s decreases along lattice (monotone decay)            *)
(* ================================================================== *)

Lemma sto_1s_decay_01 : sto_1s 1 3 (S O) < sto_1s 1 3 O.
Proof. unfold sto_1s, pade22_local. vm_compute. reflexivity. Qed.

Lemma sto_1s_decay_12 : sto_1s 1 3 (S (S O)) < sto_1s 1 3 (S O).
Proof. unfold sto_1s, pade22_local. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  NORMALIZATION: sum of sto_1s values is strictly positive           *)
(* ================================================================== *)

Definition sto_1s_sum3 : Q :=
  sto_1s 1 3 O + sto_1s 1 3 (S O) + sto_1s 1 3 (S (S O)).

Lemma sto_1s_sum3_pos : 0 < sto_1s_sum3.
Proof. unfold sto_1s_sum3, sto_1s, pade22_local. vm_compute. reflexivity. Qed.
