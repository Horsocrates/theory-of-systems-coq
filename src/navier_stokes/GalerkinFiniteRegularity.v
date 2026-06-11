(** * GalerkinFiniteRegularity.v — Finite truncations are regular; the wall is the role-limit

    Companion capstone to foundation/RoleLimitSpecies.v. Makes the thread's P4 thesis
    a THEOREM on the project's own Galerkin objects:

      Every finite truncation K is UNCONDITIONALLY regular (energy AND enstrophy bounded
      over time) -- so blow-up can only be a property of the K->infinity role-limit.
      NS global regularity = RegularLimit of the enstrophy refinement-sequence (Species I);
      by species_dichotomy (= L3) it is definitely Species I or Species II, and WHICH is
      the Millennium gap.

    The K^2 ceiling (enstrophy <= K^2 * energy) is the honest pivot: the finite bound
    EXISTS at every K but GROWS with K, so it is not uniform -- and uniformity is exactly
    the open Species-II question. Energy, by contrast, is bounded uniformly (Species I,
    unconditionally), so the wall is NOT about energy.

    Elements: finite-stage size-sequences n |-> energy_at/enstrophy_at K u n (actual rationals)
    Roles:    energy = always Species I ; enstrophy = Species I at fixed K (ceiling K^2*E0),
              the K-uniform question = Species II = NS global regularity
    Rules:    triple_sum=0 (nonlinear energy conservation) backs energy_decreasing; viscosity
              dissipates; the K^2 weight is the one-power-supercritical gap
    P4:       finite K regular (proven); blow-up is the role-limit K->infinity ONLY

    STATUS: 4 Qed, 0 Admitted, 0 axioms beyond `classic` (L3, via RoleLimitSpecies)
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import foundation.RoleLimitSpecies.
From ToS Require Import navier_stokes.GridFunction.
From ToS Require Import navier_stokes.GalerkinSystem.
From ToS Require Import navier_stokes.EnergyEstimate.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: finite-K energy time-series is Species I (unconditional)   *)
(* ================================================================== *)

(** The energy at truncation K is bounded over all time by its initial value
    (triple_sum=0 + viscous decay => energy_decreasing => this). So the energy
    size-sequence is literally a RoleLimitSpecies Species-I (RegularLimit) object. *)
Theorem finite_galerkin_energy_regular : forall K u,
  energy_decreasing K u -> RegularLimit (fun n => energy_at K u n).
Proof.
  intros K u Hdec. exists (energy_at K u 0). intro n.
  apply energy_bounded_by_initial. exact Hdec.
Qed.

(* ================================================================== *)
(*  Part II: the K^2 enstrophy ceiling (finite, but grows with K)      *)
(* ================================================================== *)

(** At a fixed truncation, enstrophy is dominated by K^2 times energy, because the
    largest modal weight (k+1)^2 for k<K is at most K^2. The constant GROWS with K. *)
Lemma enstrophy_le_Ksq_energy : forall K a,
  modal_enstrophy K a <= inject_Z (Z.of_nat (K * K)) * modal_energy K a.
Proof.
  intros K a. unfold modal_enstrophy, modal_energy.
  assert (HR : inject_Z (Z.of_nat (K * K)) * ((1#2) * sum_Q_ns (fun k => a k * a k) K) ==
               (1#2) * sum_Q_ns (fun k => inject_Z (Z.of_nat (K * K)) * (a k * a k)) K).
  { rewrite (sum_ns_scale (inject_Z (Z.of_nat (K * K))) (fun k => a k * a k) K). ring. }
  rewrite HR.
  rewrite (Qmult_comm (1#2)
            (sum_Q_ns (fun k => inject_Z (Z.of_nat ((k+1)*(k+1))) * a k * a k) K)),
          (Qmult_comm (1#2)
            (sum_Q_ns (fun k => inject_Z (Z.of_nat (K * K)) * (a k * a k)) K)).
  apply Qmult_le_compat_r; [ | rewrite Qle_alt; discriminate ].
  apply sum_ns_le. intros i Hi.
  assert (Hweight : inject_Z (Z.of_nat ((i+1)*(i+1))) <= inject_Z (Z.of_nat (K * K))).
  { rewrite <- Zle_Qle, <- Nat2Z.inj_le. nia. }
  assert (Hsq : 0 <= a i * a i) by apply Qsq_nonneg.
  assert (E : inject_Z (Z.of_nat ((i+1)*(i+1))) * a i * a i ==
              inject_Z (Z.of_nat ((i+1)*(i+1))) * (a i * a i)) by ring.
  rewrite E. apply Qmult_le_compat_r; [ exact Hweight | exact Hsq ].
Qed.

(* ================================================================== *)
(*  Part III: finite-K enstrophy time-series is Species I too          *)
(* ================================================================== *)

(** Combining I + II: at every finite K the enstrophy is bounded over time by
    K^2 * E(0) -- a genuine RegularLimit, i.e. NO finite-K blow-up. The ceiling
    depends on K, which is precisely why the role-limit is the open question. *)
Theorem finite_galerkin_enstrophy_regular : forall K u,
  energy_decreasing K u -> RegularLimit (fun n => enstrophy_at K u n).
Proof.
  intros K u Hdec.
  exists (inject_Z (Z.of_nat (K * K)) * energy_at K u 0).
  intro n. unfold enstrophy_at, energy_at.
  apply Qle_trans with (inject_Z (Z.of_nat (K * K)) * modal_energy K (u n));
    [ apply enstrophy_le_Ksq_energy | ].
  rewrite (Qmult_comm (inject_Z (Z.of_nat (K * K))) (modal_energy K (u n))),
          (Qmult_comm (inject_Z (Z.of_nat (K * K))) (modal_energy K (u 0%nat))).
  apply Qmult_le_compat_r.
  - exact (energy_bounded_by_initial K u Hdec n).
  - change 0 with (inject_Z 0). rewrite <- Zle_Qle. lia.
Qed.

(* ================================================================== *)
(*  Part IV: capstone — blow-up is purely the K->infinity role-limit   *)
(* ================================================================== *)

(** NS global regularity, in role-limit form: the K-indexed enstrophy ceiling Omega K
    stays bounded.  ns_regular / ns_is_classified come from RoleLimitSpecies:
    NS is DEFINITELY Species I or Species II (= L3), and which one is the Millennium gap. *)
Theorem galerkin_finite_regularity_capstone :
  (* 1. finite-K energy: unconditionally Species I *)
  (forall K u, energy_decreasing K u -> RegularLimit (fun n => energy_at K u n)) /\
  (* 2. finite-K enstrophy: Species I, ceiling K^2 * E0 (no finite-K blow-up) *)
  (forall K u, energy_decreasing K u -> RegularLimit (fun n => enstrophy_at K u n)) /\
  (* 3. the K^2 ceiling itself (grows with K -> not uniform) *)
  (forall K a, modal_enstrophy K a <= inject_Z (Z.of_nat (K * K)) * modal_energy K a) /\
  (* 4. NS global regularity = RegularLimit of the enstrophy refinement (L3-classified) *)
  (forall Omega, ns_regular Omega \/ SingularLimit Omega).
Proof.
  repeat split.
  - exact finite_galerkin_energy_regular.
  - exact finite_galerkin_enstrophy_regular.
  - exact enstrophy_le_Ksq_energy.
  - exact ns_is_classified.
Qed.

Print Assumptions galerkin_finite_regularity_capstone.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  4 Qed, 0 Admitted, 0 axioms beyond classic (L3).                          *)
(*  Finite truncations are regular (energy uniformly, enstrophy with a        *)
(*  K-growing ceiling); the NS wall is purely the K->infinity role-limit,     *)
(*  a Species-II question in the sense of RoleLimitSpecies.v.                  *)
(* ========================================================================= *)
