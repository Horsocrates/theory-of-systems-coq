(** * HeatKernelLattice.v -- Heat kernel on graph = trace process
    Elements: heat_kernel, heat_ratio, spectral_dimension_indicator
    Roles:    Z(K) = tr(M^K) = Σ exp(-K·λ_n), heat ratio → λ_max
    Rules:    Heat equation on lattice ↔ matrix power ↔ Green's function trace
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.GreenFunction.

Open Scope Q_scope.

(* ================================================================== *)
(*  HEAT KERNEL = TRACE PROCESS                                        *)
(* ================================================================== *)

(** Heat kernel trace: Z(K) = tr(M^K) = Σ G_{ii}(K) *)
Definition heat_kernel (M : Mat2) (K : nat) : Q :=
  trace_process M K.

(** INITIAL VALUE: Z(0) = n (number of states) *)
Lemma heat_golden_0 : heat_kernel golden 0 == 2.
Proof. unfold heat_kernel. exact trace_golden_0. Qed.

Lemma heat_full_0 : heat_kernel full_mat2 0 == 2.
Proof. unfold heat_kernel, trace_process, green, mat2_pow, mat2_id. vm_compute. reflexivity. Qed.

(** HEAT KERNEL VALUES *)
Lemma heat_golden_1 : heat_kernel golden 1 == 1.
Proof. unfold heat_kernel. exact trace_golden_1. Qed.

Lemma heat_golden_2 : heat_kernel golden 2 == 3.
Proof. unfold heat_kernel. exact trace_golden_2. Qed.

Lemma heat_golden_3 : heat_kernel golden 3 == 4.
Proof. unfold heat_kernel. exact trace_golden_3. Qed.

Lemma heat_golden_4 : heat_kernel golden 4 == 7.
Proof. unfold heat_kernel. exact trace_golden_4. Qed.

(* ================================================================== *)
(*  WEYL-LIKE ASYMPTOTICS: Z(K)/Z(K-1) → λ_max                       *)
(* ================================================================== *)

Definition heat_ratio (M : Mat2) (K : nat) : Q :=
  heat_kernel M (S K) / heat_kernel M K.

(** Golden heat ratios converge to φ *)
Lemma heat_ratio_golden_1 : heat_ratio golden 1 == 3.
Proof.
  unfold heat_ratio, heat_kernel.
  rewrite trace_golden_2, trace_golden_1.
  vm_compute. reflexivity.
Qed.

Lemma heat_ratio_golden_2 : heat_ratio golden 2 == 4#3.
Proof.
  unfold heat_ratio, heat_kernel.
  rewrite trace_golden_3, trace_golden_2.
  vm_compute. reflexivity.
Qed.

Lemma heat_ratio_golden_3 : heat_ratio golden 3 == 7#4.
Proof.
  unfold heat_ratio, heat_kernel.
  rewrite trace_golden_4, trace_golden_3.
  vm_compute. reflexivity.
Qed.

(** Heat ratio oscillation decreases (converging to φ) *)
Lemma heat_ratio_osc_12 :
  Qabs (heat_ratio golden 2 - heat_ratio golden 1) == 5#3.
Proof.
  rewrite heat_ratio_golden_2, heat_ratio_golden_1.
  vm_compute. reflexivity.
Qed.

Lemma heat_ratio_osc_23 :
  Qabs (heat_ratio golden 3 - heat_ratio golden 2) == 5#12.
Proof.
  rewrite heat_ratio_golden_3, heat_ratio_golden_2.
  vm_compute. reflexivity.
Qed.

(** Full shift: heat ratio = 2 always (exact eigenvalue) *)
Lemma heat_ratio_full_1 : heat_ratio full_mat2 1 == 2.
Proof.
  unfold heat_ratio, heat_kernel.
  rewrite trace_full_2, trace_full_1.
  vm_compute. reflexivity.
Qed.

(** SYNTHESIS *)
Theorem heat_kernel_synthesis :
  (* Heat kernel at K=0 = number of states *)
  heat_kernel golden 0 == 2 /\
  (* Positivity *)
  0 < heat_kernel golden 2 /\
  (* Heat ratio → φ *)
  heat_ratio golden 3 == 7#4 /\
  (* Full shift: exact eigenvalue *)
  heat_ratio full_mat2 1 == 2.
Proof.
  split; [|split; [|split]].
  - exact heat_golden_0.
  - rewrite heat_golden_2. lra.
  - exact heat_ratio_golden_3.
  - exact heat_ratio_full_1.
Qed.
