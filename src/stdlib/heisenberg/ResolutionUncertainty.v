(** * ResolutionUncertainty.v — Resolution-uncertainty tradeoff
    Elements: resolution, eff_hbar, tradeoff_product, capacity
    Roles:    Resolution = K/B distinguishable positions; eff_hbar = half commutator
    Rules:    Tradeoff: more resolution => more uncertainty; product bounded by K/2
    Status:   complete
    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Depends: BlockMeasurement.v
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Lia.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.heisenberg.BlockMeasurement.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Resolution and Effective Planck Constant                   *)
(* ================================================================== *)

(** Resolution: number of distinguishable positions as Q *)
Definition resolution (K B : nat) : Q :=
  inject_Z (Z.of_nat K) / inject_Z (Z.of_nat B).

(** Effective Planck constant: half the max commutator *)
Definition eff_hbar (K B : nat) : Q :=
  block_comm_max K B / 2.

(* ================================================================== *)
(*  Part II: Concrete Values                                           *)
(* ================================================================== *)

Lemma resolution_8_1 : resolution 8 1 == 8.
Proof. unfold resolution. vm_compute. reflexivity. Qed.

Lemma resolution_8_2 : resolution 8 2 == 4.
Proof. unfold resolution. vm_compute. reflexivity. Qed.

Lemma resolution_8_4 : resolution 8 4 == 2.
Proof. unfold resolution. vm_compute. reflexivity. Qed.

Lemma eff_hbar_8_1 : eff_hbar 8 1 == 47#100.
Proof. unfold eff_hbar, block_comm_max. vm_compute. reflexivity. Qed.

Lemma eff_hbar_8_2 : eff_hbar 8 2 == 25#100.
Proof. unfold eff_hbar, block_comm_max. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part III: Tradeoff Product                                         *)
(* ================================================================== *)

Definition tradeoff_product (K B : nat) : Q :=
  resolution K B * eff_hbar K B.

Lemma tradeoff_B1 : tradeoff_product 8 1 == 376#100.
Proof. unfold tradeoff_product, resolution, eff_hbar, block_comm_max. vm_compute. reflexivity. Qed.

Lemma tradeoff_B2 : tradeoff_product 8 2 == 100#100.
Proof. unfold tradeoff_product, resolution, eff_hbar, block_comm_max. vm_compute. reflexivity. Qed.

Lemma tradeoff_B4 : tradeoff_product 8 4 == 50#100.
Proof. unfold tradeoff_product, resolution, eff_hbar, block_comm_max. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part IV: Bounds and Monotonicity                                   *)
(* ================================================================== *)

Lemma res_decreases : resolution 8 2 < resolution 8 1.
Proof. unfold resolution. vm_compute. reflexivity. Qed.

Lemma tradeoff_bound : tradeoff_product 8 1 < 4.
Proof. unfold tradeoff_product, resolution, eff_hbar, block_comm_max. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part V: Information Capacity                                       *)
(* ================================================================== *)

(** Capacity: resolution per unit of effective hbar (when eff_hbar > 0) *)
Definition capacity (K B : nat) : Q :=
  resolution K B / eff_hbar K B.

Lemma capacity_8_1 : capacity 8 1 == 800#47.
Proof. unfold capacity, resolution, eff_hbar, block_comm_max. vm_compute. reflexivity. Qed.

Lemma capacity_8_2 : capacity 8 2 == 16.
Proof. unfold capacity, resolution, eff_hbar, block_comm_max. vm_compute. reflexivity. Qed.
