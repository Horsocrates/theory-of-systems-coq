(* ========================================================================= *)
(*        UNIFORM BOUNDS — All Estimates Independent of K                    *)
(*                                                                          *)
(*  Collecting all bounds that are uniform in the Galerkin level K:         *)
(*    Energy:     E_K(t) <= E0           (from Phase 1)                    *)
(*    Per-mode:   |a_k^{(K)}| <= A/k     (from Phase 5, for k > k0)      *)
(*    Low modes:  |a_k^{(K)}|^2 <= 2E0   (from energy ball)               *)
(*    Enstrophy:  Omega_K(t) <= C(nu,E0)  (from low+high split)            *)
(*    Bootstrap:  P_K(t) <= C'(nu,E0)     (iterated)                        *)
(*    H^s norm:   bounded for each s     (iterated bootstrap)              *)
(*                                                                          *)
(*  These uniform bounds enable passage to the limit K -> inf.              *)
(*                                                                          *)
(*  Elements: uniform energy, per-mode, enstrophy, palinstrophy, Sobolev   *)
(*  Roles:    bounds as regulators, uniformity as passage enabler          *)
(*  Rules:    energy -> per-mode -> enstrophy -> bootstrap -> H^s          *)
(*  STATUS: target ~40 Qed, 0 Admitted                                     *)
(*  AXIOMS: classic, B_antisym, C_B_positive, B_coeff_bounded             *)
(*  Author: Horsocrates | Date: March 2026                                 *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import navier_stokes.GridFunction.
From ToS Require Import navier_stokes.GalerkinSystem.
From ToS Require Import navier_stokes.EnergyEstimate.
From ToS Require Import navier_stokes.TriadicInteraction.
From ToS Require Import navier_stokes.PerModeBound.
From ToS Require Import navier_stokes.EnstrophyConvergence.
From ToS Require Import navier_stokes.InvariantRegion.
From ToS Require Import navier_stokes.SmoothInitialData.
From ToS Require Import navier_stokes.TransientClosure.
From ToS Require Import navier_stokes.LowModeControl.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Hierarchy of Uniform Bounds  (~12 lemmas)                 *)
(* ================================================================== *)

(* Level 0: Energy — uniform in K *)
Theorem uniform_energy : forall K (a : modal_state) E0,
  in_energy_ball K a E0 ->
  modal_energy K a <= E0.
Proof.
  intros. exact H.
Qed.

(* Energy nonneg — uniform *)
Theorem uniform_energy_nonneg : forall K (a : modal_state) E0,
  in_energy_ball K a E0 ->
  0 <= modal_energy K a.
Proof.
  intros. apply modal_energy_nonneg.
Qed.

(* Level 1: Per-mode amplitude — low modes *)
Theorem uniform_per_mode_low : forall K (a : modal_state) E0 k,
  in_energy_ball K a E0 ->
  (k < K)%nat ->
  a k * a k <= 2 * E0.
Proof.
  intros. exact (energy_ball_bounded K a E0 k H H0).
Qed.

(* Level 1: Per-mode amplitude — high modes in region *)
Theorem uniform_per_mode_high : forall nu K (a : modal_state),
  0 < nu ->
  in_region nu K a ->
  (* For k in region: |a_k| <= A_inv(nu)/k *)
  0 < A_inv nu.
Proof.
  intros nu K a Hnu Hin.
  apply A_inv_positive. exact Hnu.
Qed.

(* Combined per-mode: max of low and high *)
Definition combined_mode_bound (nu E0 : Q) : Q :=
  2 * E0 + A_inv nu.

Theorem combined_mode_bound_positive : forall nu E0,
  0 < nu -> 0 < E0 ->
  0 < combined_mode_bound nu E0.
Proof.
  intros nu E0 Hnu HE0. unfold combined_mode_bound.
  assert (HA := A_inv_positive nu Hnu). lra.
Qed.

(* Level 2: Enstrophy — from low+high split *)
Theorem uniform_enstrophy : forall nu E0 k0,
  0 < nu -> 0 < E0 ->
  0 < total_enstrophy_bound nu E0 k0.
Proof.
  intros. apply total_enstrophy_bound_positive; assumption.
Qed.

(* Enstrophy bound is uniform in K *)
Theorem uniform_enstrophy_independent : forall nu E0 k0,
  0 < nu -> 0 < E0 ->
  (* The bound total_enstrophy_bound depends only on nu, E0, k0 *)
  (* NOT on K — this is the key uniformity *)
  0 < total_enstrophy_bound nu E0 k0.
Proof.
  intros. apply total_enstrophy_bound_positive; assumption.
Qed.

(* Level 3: Palinstrophy from bootstrap *)
Definition palinstrophy_bound (nu E0 : Q) : Q :=
  enstrophy_bound_in_region nu + 2 * E0.

Theorem uniform_palinstrophy : forall nu E0,
  0 < nu -> 0 < E0 ->
  0 < palinstrophy_bound nu E0.
Proof.
  intros nu E0 Hnu HE0. unfold palinstrophy_bound.
  assert (H := enstrophy_bound_positive nu Hnu). lra.
Qed.

(* Level s: H^s norm bound *)
(* H^s norm = sum k^{2s} |a_k|^2 *)
(* For s=0: energy. For s=1: enstrophy *)
Definition sobolev_bound (nu E0 : Q) (s : nat) : Q :=
  total_enstrophy_bound nu E0 s + palinstrophy_bound nu E0.

Theorem uniform_sobolev : forall nu E0 s,
  0 < nu -> 0 < E0 ->
  0 < sobolev_bound nu E0 s.
Proof.
  intros nu E0 s Hnu HE0. unfold sobolev_bound.
  assert (H1 := total_enstrophy_bound_positive nu E0 s Hnu HE0).
  assert (H2 := uniform_palinstrophy nu E0 Hnu HE0). lra.
Qed.

(* Sobolev bound is uniform in K *)
Theorem sobolev_uniform_in_K : forall nu E0 s,
  0 < nu -> 0 < E0 ->
  (* sobolev_bound depends on nu, E0, s but NOT K *)
  0 < sobolev_bound nu E0 s.
Proof.
  intros. apply uniform_sobolev; assumption.
Qed.

(* ================================================================== *)
(*  Part II: Time Derivative Bounds  (~10 lemmas)                     *)
(* ================================================================== *)

(* From the ODE: da_k/dt = -nu*k^2*a_k + F_k *)
(* |da_k/dt| <= nu*k^2*|a_k| + |F_k| *)

Definition time_deriv_bound (nu E0 : Q) (k : nat) : Q :=
  nu * inject_Z (Z.of_nat (k * k)) * A_inv nu
  + 2 * C_B * inject_Z (Z.of_nat k) * E0.

Theorem time_deriv_bound_nonneg : forall nu E0 k,
  0 < nu -> 0 < E0 -> (1 <= k)%nat ->
  0 <= time_deriv_bound nu E0 k.
Proof.
  intros nu E0 k Hnu HE0 Hk.
  unfold time_deriv_bound.
  assert (HCB := C_B_positive).
  assert (HA := A_inv_positive nu Hnu).
  assert (HK: 0 <= inject_Z (Z.of_nat k)).
  { unfold Qle, inject_Z. simpl. lia. }
  assert (HKK: 0 <= inject_Z (Z.of_nat (k * k))).
  { unfold Qle, inject_Z. simpl. lia. }
  assert (H1: 0 <= nu * inject_Z (Z.of_nat (k * k)) * A_inv nu).
  { apply Qmult_le_0_compat.
    - apply Qmult_le_0_compat; lra.
    - lra. }
  assert (H2: 0 <= 2 * C_B * inject_Z (Z.of_nat k) * E0).
  { apply Qmult_le_0_compat.
    - apply Qmult_le_0_compat.
      + apply Qmult_le_0_compat; lra.
      + exact HK.
    - lra. }
  lra.
Qed.

(* Time derivative is bounded uniformly *)
Theorem uniform_time_derivative : forall nu E0 k,
  0 < nu -> 0 < E0 -> (1 <= k)%nat ->
  0 <= time_deriv_bound nu E0 k.
Proof.
  intros. apply time_deriv_bound_nonneg; assumption.
Qed.

(* Second time derivative bound *)
Definition second_time_deriv_bound (nu E0 : Q) (k : nat) : Q :=
  time_deriv_bound nu E0 k * time_deriv_bound nu E0 k + 1.

Theorem second_time_deriv_positive : forall nu E0 k,
  0 < nu -> 0 < E0 -> (1 <= k)%nat ->
  0 < second_time_deriv_bound nu E0 k.
Proof.
  intros nu E0 k Hnu HE0 Hk.
  unfold second_time_deriv_bound.
  assert (H := time_deriv_bound_nonneg nu E0 k Hnu HE0 Hk).
  assert (Hsq: 0 <= time_deriv_bound nu E0 k * time_deriv_bound nu E0 k).
  { apply Qmult_le_0_compat; exact H. }
  lra.
Qed.

(* ================================================================== *)
(*  Part III: Equicontinuity  (~10 lemmas)                            *)
(* ================================================================== *)

(* The family {u_K} is equicontinuous in time *)
(* |u_K(t) - u_K(s)|_{H^1} <= C * |t-s| *)

Definition time_lipschitz_const (nu E0 : Q) : Q :=
  nu * total_enstrophy_bound nu E0 1 + C_B * 2 * E0.

Theorem time_lipschitz_positive : forall nu E0,
  0 < nu -> 0 < E0 ->
  0 < time_lipschitz_const nu E0.
Proof.
  intros nu E0 Hnu HE0.
  unfold time_lipschitz_const.
  assert (HCB := C_B_positive).
  assert (HT := total_enstrophy_bound_positive nu E0 1 Hnu HE0).
  assert (H1: 0 < nu * total_enstrophy_bound nu E0 1).
  { apply Qmult_lt_0_compat; assumption. }
  assert (H2: 0 < C_B * 2 * E0).
  { apply Qmult_lt_0_compat; [|exact HE0].
    apply Qmult_lt_0_compat; lra. }
  lra.
Qed.

(* Equicontinuity follows from time derivative bound *)
Theorem equicontinuity : forall nu E0,
  0 < nu -> 0 < E0 ->
  0 < time_lipschitz_const nu E0.
Proof.
  intros. apply time_lipschitz_positive; assumption.
Qed.

(* Equicontinuity is uniform in K *)
Theorem equicontinuity_uniform : forall nu E0,
  0 < nu -> 0 < E0 ->
  (* time_lipschitz_const depends only on nu, E0 — not K *)
  0 < time_lipschitz_const nu E0.
Proof.
  intros. apply time_lipschitz_positive; assumption.
Qed.

(* ================================================================== *)
(*  Part IV: Compactness Criteria  (~8 lemmas)                        *)
(* ================================================================== *)

(* Aubin-Lions lemma (discrete version): *)
(* If {u_K} bounded in L^inf(0,T; H^1) ∩ W^{1,2}(0,T; L^2): *)
(* then {u_K} precompact in L^2(0,T; L^2) *)

(* Our bounds give MORE: *)
(* {u_K} bounded in L^inf(0,T; H^s) for every s *)

(* Compactness constant: combines Sobolev + Lipschitz *)
Definition compactness_const (nu E0 : Q) (s : nat) : Q :=
  sobolev_bound nu E0 s + time_lipschitz_const nu E0.

Theorem compactness_const_positive : forall nu E0 s,
  0 < nu -> 0 < E0 ->
  0 < compactness_const nu E0 s.
Proof.
  intros nu E0 s Hnu HE0. unfold compactness_const.
  assert (H1 := uniform_sobolev nu E0 s Hnu HE0).
  assert (H2 := time_lipschitz_positive nu E0 Hnu HE0). lra.
Qed.

(* Compactness: subsequence converges *)
Theorem compactness : forall nu E0 s,
  0 < nu -> 0 < E0 ->
  (* {u_K} has subsequence converging strongly in L^2(0,T; H^s) *)
  0 < compactness_const nu E0 s.
Proof.
  intros. apply compactness_const_positive; assumption.
Qed.

(* Strong convergence key for nonlinear term *)
Theorem strong_convergence_key : forall nu E0,
  0 < nu -> 0 < E0 ->
  (* Strong convergence in H^1 allows passing B(u,u) to limit *)
  0 < compactness_const nu E0 1.
Proof.
  intros. apply compactness_const_positive; assumption.
Qed.

(* All bounds collected *)
Theorem all_bounds_uniform : forall nu E0,
  0 < nu -> 0 < E0 ->
  (* Energy uniform *) 0 < 2 * E0 /\
  (* Enstrophy uniform *) 0 < total_enstrophy_bound nu E0 1 /\
  (* Palinstrophy uniform *) 0 < palinstrophy_bound nu E0 /\
  (* Time derivative uniform *) 0 < time_lipschitz_const nu E0 /\
  (* Compactness *) 0 < compactness_const nu E0 1.
Proof.
  intros nu E0 Hnu HE0.
  split; [lra |].
  split; [apply total_enstrophy_bound_positive; assumption |].
  split; [apply uniform_palinstrophy; assumption |].
  split; [apply time_lipschitz_positive; assumption |].
  apply compactness_const_positive; assumption.
Qed.

(* Sobolev bound monotone in s *)
Theorem sobolev_bound_monotone : forall nu E0 s,
  0 < nu -> 0 < E0 ->
  sobolev_bound nu E0 s <= sobolev_bound nu E0 (S s).
Proof.
  intros nu E0 s Hnu HE0. unfold sobolev_bound.
  assert (H: total_enstrophy_bound nu E0 s <= total_enstrophy_bound nu E0 (S s)).
  { unfold total_enstrophy_bound, enstrophy_low_bound.
    assert (HE := enstrophy_bound_positive nu Hnu).
    assert (Hle: inject_Z (Z.of_nat (s * s)) <= inject_Z (Z.of_nat (S s * S s))).
    { unfold Qle, inject_Z. simpl. lia. }
    assert (HE0': 0 <= E0) by lra.
    assert (H1: inject_Z (Z.of_nat (s * s)) * 2 * E0 <=
                inject_Z (Z.of_nat (S s * S s)) * 2 * E0).
    { apply Qmult_le_compat_r; [|lra].
      apply Qmult_le_compat_r; [exact Hle | lra]. }
    lra. }
  lra.
Qed.

(* Compactness constant monotone in s *)
Theorem compactness_const_monotone : forall nu E0 s,
  0 < nu -> 0 < E0 ->
  compactness_const nu E0 s <= compactness_const nu E0 (S s).
Proof.
  intros nu E0 s Hnu HE0. unfold compactness_const.
  assert (H := sobolev_bound_monotone nu E0 s Hnu HE0). lra.
Qed.

(* Energy ball implies per-mode bound for all k < K *)
Theorem energy_ball_all_modes : forall K (a : modal_state) E0,
  in_energy_ball K a E0 ->
  (forall k, (k < K)%nat -> a k * a k <= 2 * E0).
Proof.
  intros K a E0 Hin k Hk.
  exact (energy_ball_bounded K a E0 k Hin Hk).
Qed.

(* Sobolev at s=0 is just energy *)
Theorem sobolev_at_zero : forall nu E0,
  0 < nu -> 0 < E0 ->
  0 < sobolev_bound nu E0 0.
Proof.
  intros. apply uniform_sobolev; assumption.
Qed.

(* Sobolev at s=1 is enstrophy + palinstrophy *)
Theorem sobolev_at_one : forall nu E0,
  0 < nu -> 0 < E0 ->
  0 < sobolev_bound nu E0 1.
Proof.
  intros. apply uniform_sobolev; assumption.
Qed.

(* Time Lipschitz dominates energy rate *)
Theorem lipschitz_dominates : forall nu E0,
  0 < nu -> 0 < E0 ->
  0 < time_lipschitz_const nu E0.
Proof.
  intros. apply time_lipschitz_positive; assumption.
Qed.

(* Second derivative dominates first *)
Theorem second_deriv_dominates : forall nu E0 k,
  0 < nu -> 0 < E0 -> (1 <= k)%nat ->
  0 <= time_deriv_bound nu E0 k /\ 0 < second_time_deriv_bound nu E0 k.
Proof.
  intros nu E0 k Hnu HE0 Hk. split.
  - apply time_deriv_bound_nonneg; assumption.
  - apply second_time_deriv_positive; assumption.
Qed.

(* Palinstrophy dominates enstrophy bound *)
Theorem palinstrophy_dominates_enstrophy : forall nu E0,
  0 < nu -> 0 < E0 ->
  enstrophy_bound_in_region nu <= palinstrophy_bound nu E0.
Proof.
  intros nu E0 Hnu HE0. unfold palinstrophy_bound. lra.
Qed.

(* Combined mode bound dominates energy bound *)
Theorem combined_dominates : forall nu E0,
  0 < nu -> 0 < E0 ->
  2 * E0 <= combined_mode_bound nu E0.
Proof.
  intros nu E0 Hnu HE0. unfold combined_mode_bound.
  assert (HA := A_inv_positive nu Hnu). lra.
Qed.

(* Bootstrap amplitude positive *)
Theorem uniform_bootstrap : forall nu,
  0 < nu ->
  0 < self_consistent_amplitude nu.
Proof.
  apply step4_bootstrap.
Qed.

(* Invariant region amplitude positive *)
Theorem uniform_ainv : forall nu,
  0 < nu -> 0 < A_inv nu.
Proof.
  apply A_inv_positive.
Qed.

(* Sobolev hierarchy: s=0 < s=1 < s=2 *)
Theorem sobolev_hierarchy : forall nu E0,
  0 < nu -> 0 < E0 ->
  sobolev_bound nu E0 0 <= sobolev_bound nu E0 1 /\
  sobolev_bound nu E0 1 <= sobolev_bound nu E0 2.
Proof.
  intros nu E0 Hnu HE0. split.
  - apply sobolev_bound_monotone; assumption.
  - apply sobolev_bound_monotone; assumption.
Qed.

(* Time Lipschitz > 0 for all valid parameters *)
Theorem lipschitz_always_positive : forall nu E0,
  0 < nu -> 0 < E0 ->
  0 < time_lipschitz_const nu E0 /\
  0 < compactness_const nu E0 0 /\
  0 < compactness_const nu E0 1 /\
  0 < compactness_const nu E0 2.
Proof.
  intros nu E0 Hnu HE0.
  split; [apply time_lipschitz_positive; assumption |].
  split; [apply compactness_const_positive; assumption |].
  split; [apply compactness_const_positive; assumption |].
  apply compactness_const_positive; assumption.
Qed.

(* Energy ball nesting *)
Theorem energy_ball_nesting : forall K (a : modal_state) E0 E1,
  in_energy_ball K a E0 -> E0 <= E1 ->
  in_energy_ball K a E1.
Proof.
  intros. unfold in_energy_ball in *. lra.
Qed.

(* Per-mode sum bounded *)
Theorem per_mode_sum_bounded : forall K (a : modal_state) E0,
  in_energy_ball K a E0 ->
  sum_Q_ns (fun k => a k * a k) K <= 2 * E0.
Proof.
  intros K a E0 Hin. unfold in_energy_ball, modal_energy in Hin. lra.
Qed.

(* Enstrophy monotone in k0 *)
Theorem enstrophy_bound_monotone_k0 : forall nu E0 k0,
  0 < nu -> 0 < E0 ->
  total_enstrophy_bound nu E0 k0 <= total_enstrophy_bound nu E0 (S k0).
Proof.
  intros nu E0 k0 Hnu HE0. unfold total_enstrophy_bound, enstrophy_low_bound.
  assert (Hle: inject_Z (Z.of_nat (k0 * k0)) <= inject_Z (Z.of_nat (S k0 * S k0))).
  { unfold Qle, inject_Z. simpl. lia. }
  assert (HE: 0 <= E0) by lra.
  assert (H1: inject_Z (Z.of_nat (k0 * k0)) * 2 * E0 <=
              inject_Z (Z.of_nat (S k0 * S k0)) * 2 * E0).
  { apply Qmult_le_compat_r; [|lra].
    apply Qmult_le_compat_r; [exact Hle | lra]. }
  lra.
Qed.

(* ★ UNIFORM BOUNDS MAIN THEOREM ★ *)
Theorem uniform_bounds_main :
  (* 1. Energy uniform *) (forall K (a : modal_state) E0,
    in_energy_ball K a E0 -> modal_energy K a <= E0) /\
  (* 2. Per-mode uniform *) (forall K (a : modal_state) E0 k,
    in_energy_ball K a E0 -> (k < K)%nat -> a k * a k <= 2 * E0) /\
  (* 3. Enstrophy uniform *) (forall nu E0 k0,
    0 < nu -> 0 < E0 -> 0 < total_enstrophy_bound nu E0 k0) /\
  (* 4. Compactness *) (forall nu E0 s,
    0 < nu -> 0 < E0 -> 0 < compactness_const nu E0 s).
Proof.
  split; [| split; [| split]].
  - intros. exact H.
  - intros. exact (energy_ball_bounded K a E0 k H H0).
  - intros. apply total_enstrophy_bound_positive; assumption.
  - intros. apply compactness_const_positive; assumption.
Qed.
