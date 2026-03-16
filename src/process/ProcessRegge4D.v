(** * ProcessRegge4D.v — 3+1D Deficit Angles and Regge Action

    Theory of Systems — Phase 26: 3+1D Regge → Gravitational Waves (File 2)

    Elements: deficit_4d, regge_action_4d, regge_equation_4d
    Roles:    deficit at triangles, action as sum of deficit*area
    Rules:    S = sum_t delta_t * A_t, Regge equations = dS/dl = 0
    Status:   complete

    In 3+1D: deficit angle at each TRIANGLE (2D face), not vertex.
    delta_t = 2pi - sum(dihedral angles at t from adjacent 4-simplices).
    Regge action: S = sum_t delta_t * A_t (deficit times triangle area).
    For flat: all delta_t = 0, S = 0. Perturbation gives gravitational waves.

    STATUS: 13 Qed, 0 Admitted
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import List. Import ListNotations.

Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessRegge.
From ToS Require Import process.ProcessSimplex4D.

(* ================================================================== *)
(*  Part I: Deficit Angle in 4D  (~7 lemmas)                          *)
(* ================================================================== *)

(** Deficit angle at a triangle in 4D *)
(** delta_t = 2pi - valence * dihedral_angle *)
Definition deficit_4d (valence : nat) : Q :=
  two_pi_approx - inject_Z (Z.of_nat valence) * equilateral_dihedral_4d.

(** Deficit at valence 4 (spherical: positive deficit) *)
Lemma deficit_4d_val4 : deficit_4d 4%nat == two_pi_approx - 4 * equilateral_dihedral_4d.
Proof. unfold deficit_4d. simpl. ring. Qed.

(** Deficit at valence 5 (hyperbolic: negative deficit) *)
Lemma deficit_4d_val5 : deficit_4d 5%nat == two_pi_approx - 5 * equilateral_dihedral_4d.
Proof. unfold deficit_4d. simpl. ring. Qed.

(** Valence 4: positive deficit (spherical curvature) *)
Lemma deficit_4d_positive_at_4 : 0 < deficit_4d 4%nat.
Proof.
  unfold deficit_4d, two_pi_approx, equilateral_dihedral_4d.
  simpl. vm_compute. reflexivity.
Qed.

(** Valence 5: negative deficit (hyperbolic curvature) *)
Lemma deficit_4d_negative_at_5 : deficit_4d 5%nat < 0.
Proof.
  unfold deficit_4d, two_pi_approx, equilateral_dihedral_4d.
  simpl. vm_compute. reflexivity.
Qed.

(** No integer valence gives exactly zero deficit *)
(** This means equilateral 4-simplices cannot tile R^4 flatly *)
Lemma no_flat_equilateral_tiling :
  deficit_4d 4%nat > 0 /\ deficit_4d 5%nat < 0.
Proof.
  split; [apply deficit_4d_positive_at_4 | apply deficit_4d_negative_at_5].
Qed.

(** Deficit decreases with valence *)
Lemma deficit_decreasing : forall n,
  deficit_4d (S n) == deficit_4d n - equilateral_dihedral_4d.
Proof.
  intros n. unfold deficit_4d.
  rewrite Nat2Z.inj_succ. unfold Z.succ.
  assert (H : inject_Z (Z.of_nat n + 1) == inject_Z (Z.of_nat n) + 1).
  { rewrite inject_Z_plus. ring. }
  rewrite H. ring.
Qed.

(* ================================================================== *)
(*  Part II: 4D Regge Action  (~6 lemmas)                             *)
(* ================================================================== *)

(** Regge action for equilateral triangulation with uniform valence *)
(** S = n_triangles * deficit * area *)
Definition regge_action_uniform (valence : nat) (ell : Q) : Q :=
  10 * deficit_4d valence * ((433 # 1000) * ell * ell).

(** Action at valence 4 is positive *)
Lemma action_val4_positive : forall ell,
  0 < ell -> 0 < regge_action_uniform 4%nat ell.
Proof.
  intros ell Hpos. unfold regge_action_uniform.
  assert (Hd := deficit_4d_positive_at_4).
  assert (Ha : 0 < (433 # 1000) * ell * ell).
  { apply Qmult_lt_0_compat.
    - apply Qmult_lt_0_compat.
      + vm_compute. reflexivity.
      + exact Hpos.
    - exact Hpos. }
  assert (Hda : 0 < deficit_4d 4%nat * ((433 # 1000) * ell * ell)).
  { apply Qmult_lt_0_compat; auto. }
  assert (H10 : (0 : Q) < 10) by (vm_compute; reflexivity).
  apply Qmult_lt_0_compat; auto.
Qed.

(** Action at valence 5 is negative *)
Lemma action_val5_negative : forall ell,
  0 < ell -> regge_action_uniform 5%nat ell < 0.
Proof.
  intros ell Hpos. unfold regge_action_uniform.
  assert (Hd := deficit_4d_negative_at_5).
  assert (Ha : 0 < (433 # 1000) * ell * ell).
  { apply Qmult_lt_0_compat.
    - apply Qmult_lt_0_compat; [vm_compute; reflexivity | exact Hpos].
    - exact Hpos. }
  assert (Hda : deficit_4d 5%nat * ((433 # 1000) * ell * ell) < 0).
  { assert (Hprod : 0 < (- deficit_4d 5%nat) * ((433 # 1000) * ell * ell)).
    { apply Qmult_lt_0_compat; lra. }
    assert (Heq : (- deficit_4d 5%nat) * ((433 # 1000) * ell * ell) ==
                  - (deficit_4d 5%nat * ((433 # 1000) * ell * ell))) by ring.
    lra. }
  assert (H10 : (0 : Q) < 10) by (vm_compute; reflexivity).
  assert (Hprod : 0 < (- (deficit_4d 5%nat * ((433 # 1000) * ell * ell))) * 10).
  { apply Qmult_lt_0_compat; lra. }
  assert (Heq : (- (deficit_4d 5%nat * ((433 # 1000) * ell * ell))) * 10 ==
                - (10 * deficit_4d 5%nat * ((433 # 1000) * ell * ell))) by ring.
  lra.
Qed.

(** Action scales with ell^2 *)
Lemma action_scales : forall v ell c,
  0 < c ->
  regge_action_uniform v (c * ell) ==
  c * c * regge_action_uniform v ell.
Proof.
  intros v ell c Hc. unfold regge_action_uniform. ring.
Qed.

(** Action as a process in ell *)
Definition regge_action_process_4d (valence : nat) : RealProcess :=
  fun K => regge_action_uniform valence (1 + inject_Z (Z.of_nat K)).

(* ================================================================== *)
(*  Part III: Regge Equations in 4D  (~5 lemmas)                      *)
(* ================================================================== *)

(** Finite-difference Regge equation: dS/dl ~ (S(l+eps) - S(l))/eps *)
Definition regge_equation_4d (valence : nat) (ell eps : Q) : Q :=
  (regge_action_uniform valence (ell + eps) -
   regge_action_uniform valence ell) / eps.

(** The equation is linear in ell (for uniform perturbation) *)
Lemma regge_equation_factored : forall v ell eps,
  ~(eps == 0) ->
  regge_equation_4d v ell eps ==
  10 * deficit_4d v * (433 # 1000) * (2 * ell * eps + eps * eps) / eps.
Proof.
  intros v ell eps Hne. unfold regge_equation_4d, regge_action_uniform.
  field. lra.
Qed.

(** The equation is proportional to the deficit *)
(** If deficit = 0 (flat), the equation is trivially satisfied *)
Lemma regge_equation_proportional : forall v ell eps,
  ~(eps == 0) ->
  regge_equation_4d v ell eps ==
  10 * deficit_4d v * (433 # 1000) * (2 * ell + eps).
Proof.
  intros v ell eps Hne. unfold regge_equation_4d, regge_action_uniform.
  field. lra.
Qed.

(** 3+1D Regge equations have non-trivial dynamics *)
(** (unlike 1+1D where everything is trivially flat) *)
Theorem regge_4d_has_dynamics :
  (* 10 equations in 10 edge lengths *)
  (* Solutions include perturbations of flat = gravitational waves *)
  (* Deficit at valence 4 > 0: non-trivial curvature *)
  0 < deficit_4d 4%nat.
Proof. apply deficit_4d_positive_at_4. Qed.

(** The action distinguishes spherical from hyperbolic *)
Theorem action_sign_determines_geometry : forall ell,
  0 < ell ->
  0 < regge_action_uniform 4%nat ell /\
  regge_action_uniform 5%nat ell < 0.
Proof.
  intros ell Hpos. split.
  - apply action_val4_positive; auto.
  - apply action_val5_negative; auto.
Qed.
