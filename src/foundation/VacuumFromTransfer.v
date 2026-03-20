(** * VacuumFromTransfer.v -- Vacuum energy from transfer matrix eigenvalue
    Elements: E_vac_transfer, lambda_from_transfer
    Roles:    Replace ad hoc E_vac = 1/(1+K) with derived E_vac = 1 - λ₀
    Rules:    E_vac(β,M) = 1 - λ₀(β,M), Λ = E_vac · κ²
    Status:   Foundation
    STATUS: 8 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

(* ================================================================== *)
(*  REPLICATE TRANSFER EIGENVALUE                                      *)
(* ================================================================== *)

(** Replicated from CharacterTransfer to avoid stale .vo *)
Fixpoint Qpow (q : Q) (n : nat) : Q :=
  match n with O => 1 | S n' => q * Qpow q n' end.

Definition fact_Q (n : nat) : Q := inject_Z (Z.of_nat (fact n)).
Definition fact_prod (m n : nat) : Q := fact_Q m * fact_Q n.

Definition bessel_term (n m : nat) (beta : Q) : Q :=
  Qpow (beta / 2) (n + 2 * m) / fact_prod m (n + m).

Fixpoint bessel_partial (n : nat) (beta : Q) (M : nat) : Q :=
  match M with
  | O => bessel_term n 0 beta
  | S M' => bessel_partial n beta M' + bessel_term n (S M') beta
  end.

Definition transfer_eig (j : nat) (beta : Q) (M : nat) : Q :=
  bessel_partial (2 * j) beta M - bessel_partial (2 * j + 2) beta M.

(* ================================================================== *)
(*  VACUUM ENERGY FROM TRANSFER MATRIX                                 *)
(* ================================================================== *)

(** PREVIOUS: vacuum_energy(K) = 1/(1+K) — ad hoc placeholder.

    NEW: vacuum energy = ground state of transfer matrix.
    E_vac(β, M) = -ln(λ₀(β, M)) ≈ 1 - λ₀ (Padé for small E)

    λ₀ = transfer_eigenvalue 0 β M.
    THIS IS DERIVED, not ad hoc! *)

Definition E_vac_transfer (beta : Q) (M : nat) : Q :=
  1 - transfer_eig 0 beta M.

(** E_vac at β=1, M=0 *)
(** λ₀ = t₀ = 7/8 *)
(** E_vac = 1 - 7/8 = 1/8 *)
Lemma E_vac_b1_M0 : E_vac_transfer 1 0 == 1 # 8.
Proof.
  unfold E_vac_transfer, transfer_eig, bessel_partial, bessel_term,
         fact_prod, fact_Q. vm_compute. reflexivity.
Qed.

(** E_vac > 0 because λ₀ < 1 *)
Theorem E_vac_positive_b1 : 0 < E_vac_transfer 1 0.
Proof. rewrite E_vac_b1_M0. lra. Qed.

(** E_vac at β=2, M=0 *)
Lemma E_vac_b2_M0 : E_vac_transfer 2 0 == 1 # 2.
Proof.
  unfold E_vac_transfer, transfer_eig, bessel_partial, bessel_term,
         fact_prod, fact_Q. vm_compute. reflexivity.
Qed.

(** E_vac increases from β=1 to β=2 *)
(** Physical: strong coupling → eigenvalue further from 1 → larger E_vac *)
Theorem E_vac_monotone :
  E_vac_transfer 1 0 < E_vac_transfer 2 0.
Proof. rewrite E_vac_b1_M0, E_vac_b2_M0. lra. Qed.

(* ================================================================== *)
(*  COSMOLOGICAL CONSTANT FROM TRANSFER MATRIX                         *)
(* ================================================================== *)

(** Λ = E_vac · κ² where κ = 1/10 (from D=4 → 10 metric components) *)
Definition lambda_from_transfer (beta : Q) (M : nat) : Q :=
  E_vac_transfer beta M * (1 # 100).

Lemma lambda_b1_M0 : lambda_from_transfer 1 0 == 1 # 800.
Proof.
  unfold lambda_from_transfer. rewrite E_vac_b1_M0. ring.
Qed.

Theorem lambda_positive : 0 < lambda_from_transfer 1 0.
Proof. rewrite lambda_b1_M0. lra. Qed.

Theorem lambda_b2_M0 : lambda_from_transfer 2 0 == 1 # 200.
Proof.
  unfold lambda_from_transfer. rewrite E_vac_b2_M0. ring.
Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

(** THIS REPLACES VacuumNecessity.v's ad hoc E_vac = 1/(1+K).
    NOW: E_vac = 1 - λ₀(β,M) — DERIVED from transfer matrix.

    E_vac(β=1, M=0) = 1/8 (concrete Q, not placeholder)
    E_vac(β=2, M=0) = 1/2
    Λ(β=1) = (1/8)·(1/100) = 1/800 *)

Theorem vacuum_from_transfer_synthesis :
  E_vac_transfer 1 0 == 1 # 8 /\
  0 < E_vac_transfer 1 0 /\
  E_vac_transfer 1 0 < E_vac_transfer 2 0 /\
  lambda_from_transfer 1 0 == 1 # 800 /\
  0 < lambda_from_transfer 1 0.
Proof.
  split; [|split; [|split; [|split]]].
  - exact E_vac_b1_M0.
  - exact E_vac_positive_b1.
  - exact E_vac_monotone.
  - exact lambda_b1_M0.
  - exact lambda_positive.
Qed.
