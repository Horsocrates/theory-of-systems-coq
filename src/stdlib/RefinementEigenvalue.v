(** * RefinementEigenvalue.v -- Process refinement for eigenvalues
    CLASSICAL: λ_max(M) = one number.
    PROCESS:   Rayleigh_K = tr(M^{K+1})/tr(M^K) → λ_max.
    WITNESS:   diag(3,1) vs diag(3,2): same λ_max=3, different Rayleigh process.
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.ProcessRefinement.

Open Scope Q_scope.

(* ================================================================== *)
(*  RAYLEIGH QUOTIENT FROM TRACE                                       *)
(* ================================================================== *)

Definition rayleigh (trace_fn : nat -> Q) (K : nat) : Q :=
  trace_fn (S K) / trace_fn K.

(** WITNESS: diag(3,1) vs diag(3,2) *)
Definition trace_31 : Process := fun K => Qpow 3 K + Qpow 1 K.
Definition trace_32 : Process := fun K => Qpow 3 K + Qpow 2 K.

(* ================================================================== *)
(*  CONCRETE VALUES                                                    *)
(* ================================================================== *)

Lemma trace_31_0 : trace_31 0%nat == 2.
Proof. unfold trace_31. vm_compute. reflexivity. Qed.

Lemma trace_31_1 : trace_31 1%nat == 4.
Proof. unfold trace_31. vm_compute. reflexivity. Qed.

Lemma trace_31_2 : trace_31 2%nat == 10.
Proof. unfold trace_31. vm_compute. reflexivity. Qed.

Lemma trace_31_3 : trace_31 3%nat == 28.
Proof. unfold trace_31. vm_compute. reflexivity. Qed.

Lemma trace_32_0 : trace_32 0%nat == 2.
Proof. unfold trace_32. vm_compute. reflexivity. Qed.

Lemma trace_32_1 : trace_32 1%nat == 5.
Proof. unfold trace_32. vm_compute. reflexivity. Qed.

Lemma trace_32_2 : trace_32 2%nat == 13.
Proof. unfold trace_32. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  RAYLEIGH PROCESS DIFFERS                                           *)
(* ================================================================== *)

Lemma ray_31_0 : rayleigh trace_31 0%nat == 2.
Proof. unfold rayleigh. rewrite trace_31_1, trace_31_0. vm_compute. reflexivity. Qed.

Lemma ray_32_0 : rayleigh trace_32 0%nat == 5#2.
Proof. unfold rayleigh. rewrite trace_32_1, trace_32_0. vm_compute. reflexivity. Qed.

Lemma ray_diff_0 : ~ (rayleigh trace_31 0%nat == rayleigh trace_32 0%nat).
Proof. rewrite ray_31_0, ray_32_0. unfold Qeq. simpl. lia. Qed.

(** ★ EIGENVALUE STRICT REFINEMENT *)
Theorem eigenvalue_strict_refinement :
  rayleigh trace_31 0%nat == 2 /\
  rayleigh trace_32 0%nat == 5#2 /\
  ~ (rayleigh trace_31 0%nat == rayleigh trace_32 0%nat).
Proof.
  split; [|split].
  - exact ray_31_0.
  - exact ray_32_0.
  - exact ray_diff_0.
Qed.

(** Both → 3 as K→∞. Different Rayleigh process.
    Rate: diag(3,1) has |λ₂/λ₁| = 1/3 (fast).
          diag(3,2) has |λ₂/λ₁| = 2/3 (slow). *)
