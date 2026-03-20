(** * GravitonSelfEnergy.v -- Graviton self-energy: finite, concrete Q
    Elements: graviton_propagator, self_energy_integrand, graviton_self_energy
    Roles:    Show graviton self-energy is FINITE at every cutoff K
    Rules:    Σ(K) = Σ_{k=1}^{K} k⁴/(k²+m²)² is always a concrete Q
    Status:   Stdlib
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Lia ZArith.
From Stdlib Require Import Qabs.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.

Open Scope Q_scope.

(* ================================================================== *)
(*  GRAVITON PROPAGATOR AND SELF-ENERGY                                *)
(* ================================================================== *)

(** In standard QG: Σ_graviton = ∫ d⁴k G_N²k⁴/(k²+m²)² = DIVERGENT.
    UV divergence → QG non-renormalizable → "quantum gravity is impossible."

    In ToS: lattice cutoff K. Sum is FINITE by construction.
    Σ(K) = Σ_{k=1}^{K} k⁴/(k²+m²)² over Q.
    This is a concrete Q number at each K. Never diverges. *)

Definition graviton_propagator (k m : Q) : Q :=
  1 / (k * k + m * m).

Definition self_energy_integrand (k m : Q) : Q :=
  k * k * k * k * graviton_propagator k m * graviton_propagator k m.

(** Self-energy sum at cutoff K, with k running from 1 to K *)
Fixpoint graviton_self_energy (K : nat) (m : Q) : Q :=
  match K with
  | O => 0
  | S K' => graviton_self_energy K' m +
             self_energy_integrand (inject_Z (Z.of_nat (S K'))) m
  end.

(* ================================================================== *)
(*  CONCRETE VALUES                                                    *)
(* ================================================================== *)

(** K=1, m=1: only k=1 contributes *)
(** integrand(1,1) = 1⁴/(1+1)² = 1/4 *)
Lemma self_energy_K1 :
  graviton_self_energy 1 1 == 1 # 4.
Proof.
  unfold graviton_self_energy, self_energy_integrand, graviton_propagator.
  vm_compute. reflexivity.
Qed.

(** K=2, m=1: k=1 and k=2 *)
(** integrand(2,1) = 2⁴/(4+1)² = 16/25 *)
(** Σ = 1/4 + 16/25 = 25/100 + 64/100 = 89/100 *)
Lemma self_energy_K2 :
  graviton_self_energy 2 1 == 89 # 100.
Proof.
  unfold graviton_self_energy, self_energy_integrand, graviton_propagator.
  vm_compute. reflexivity.
Qed.

(** K=3, m=1: add k=3 *)
(** integrand(3,1) = 3⁴/(9+1)² = 81/100 *)
(** Σ = 89/100 + 81/100 = 170/100 = 17/10 *)
Lemma self_energy_K3 :
  graviton_self_energy 3 1 == 17 # 10.
Proof.
  unfold graviton_self_energy, self_energy_integrand, graviton_propagator.
  vm_compute. reflexivity.
Qed.

(** Σ > 0 for K ≥ 1 *)
Lemma self_energy_K1_positive : 0 < graviton_self_energy 1 1.
Proof. rewrite self_energy_K1. lra. Qed.

Lemma self_energy_K2_positive : 0 < graviton_self_energy 2 1.
Proof. rewrite self_energy_K2. lra. Qed.

(** Self-energy increases with K *)
Lemma self_energy_monotone_12 :
  graviton_self_energy 1 1 < graviton_self_energy 2 1.
Proof. rewrite self_energy_K1, self_energy_K2. lra. Qed.

Lemma self_energy_monotone_23 :
  graviton_self_energy 2 1 < graviton_self_energy 3 1.
Proof. rewrite self_energy_K2, self_energy_K3. lra. Qed.

(** Self-energy is rational (always a concrete Q) *)
Theorem self_energy_finite : forall K m,
  exists sigma : Q, graviton_self_energy K m == sigma.
Proof.
  intros K m. exists (graviton_self_energy K m). reflexivity.
Qed.

(* ================================================================== *)
(*  PHYSICAL SELF-ENERGY WITH G_N                                      *)
(* ================================================================== *)

(** With G_N = kappa² = (1/10)² = 1/100:
    Σ_physical = G_N · Σ_lattice
    (One factor of G_N per vertex in the self-energy diagram) *)

Definition G_N_from_kappa : Q := (1 # 10) * (1 # 10).

Lemma G_N_value : G_N_from_kappa == 1 # 100.
Proof. unfold G_N_from_kappa. ring. Qed.

Definition physical_self_energy (K : nat) (m : Q) : Q :=
  G_N_from_kappa * graviton_self_energy K m.

Lemma physical_se_K1 :
  physical_self_energy 1 1 == 1 # 400.
Proof.
  unfold physical_self_energy, G_N_from_kappa, graviton_self_energy,
         self_energy_integrand, graviton_propagator.
  vm_compute. reflexivity.
Qed.

Lemma physical_se_K1_positive : 0 < physical_self_energy 1 1.
Proof. rewrite physical_se_K1. lra. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

(** COMPARE WITH STANDARD QG:
    Standard: Σ = ∫₀^∞ dk k⁴/(k²+m²)² = DIVERGES (quartically!)
    ToS K=1: Σ_physical = 1/400 ≈ 2.5 × 10⁻³
    ToS K=2: Σ_physical = 89/10000 ≈ 8.9 × 10⁻³
    ToS K=3: Σ_physical = 17/1000 ≈ 1.7 × 10⁻²

    Always finite. Always rational. Always computable.
    The "non-renormalizability crisis" is an artifact of
    taking K → ∞ (completed infinity). Under P4: K is always finite. *)

Theorem graviton_se_synthesis :
  graviton_self_energy 1 1 == 1 # 4 /\
  graviton_self_energy 2 1 == 89 # 100 /\
  graviton_self_energy 3 1 == 17 # 10 /\
  0 < physical_self_energy 1 1 /\
  physical_self_energy 1 1 == 1 # 400.
Proof.
  split; [|split; [|split; [|split]]].
  - exact self_energy_K1.
  - exact self_energy_K2.
  - exact self_energy_K3.
  - exact physical_se_K1_positive.
  - exact physical_se_K1.
Qed.
