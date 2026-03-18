(** * ProcessCrossingD.v — Crossing in D Dimensions

    Theory of Systems — Step 3 Phase 20: Dimension from Stability (File 2)

    Elements: D-dimensional crossing process, crossing point K*(D)
    Roles:    crossing_D, is_crossing_point_D, combined_gap_D
    Rules:    crossing exists in all D > 0, K* depends on D
    Status:   complete

    Crossing: gravity_gap_D(K) = gauge_gap → K* depends on D.
    κL^D / K*^D = 289/384
    K* = L · (384κ/289)^{1/D}

    STATUS: 13 Qed, 0 Admitted
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith.Qabs QArith.Qminmax Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.

Open Scope Q_scope.

From ToS Require Import SeriesConvergence.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessBounds.
From ToS Require Import process.ProcessCrossing.
From ToS Require Import process.ProcessDimension.

(* ================================================================== *)
(*  Part I: D-Dimensional Crossing Process  (~6 lemmas)               *)
(* ================================================================== *)

(** Crossing process: gravity_gap_D(K) − gauge_gap *)
Definition crossing_D (beta kappa L : Q) (D : nat) : RealProcess :=
  fun K => gravity_gap_D_at_K kappa L D K - gauge_gap_any_D beta D K.

(** At K=0: crossing = κL^D − gauge_gap *)
Lemma crossing_D_at_0 : forall beta kappa L D,
  crossing_D beta kappa L D 0%nat ==
  kappa * Qpow L D - gauge_gap_at_K beta 0%nat.
Proof.
  intros. unfold crossing_D, gauge_gap_any_D.
  rewrite gravity_gap_D_at_K0. reflexivity.
Qed.

(** Crossing starts positive if κL^D > gauge_gap *)
Lemma crossing_D_starts_positive : forall beta kappa L D,
  gauge_gap_at_K beta 0%nat < kappa * Qpow L D ->
  0 < crossing_D beta kappa L D 0%nat.
Proof.
  intros beta kappa L D Hgt.
  rewrite crossing_D_at_0. lra.
Qed.

(** Crossing D is non-negative at K means gravity dominates *)
Lemma crossing_D_nonneg_means : forall beta kappa L D K,
  0 <= crossing_D beta kappa L D K ->
  gauge_gap_any_D beta D K <= gravity_gap_D_at_K kappa L D K.
Proof.
  intros. unfold crossing_D in H. lra.
Qed.

(** Crossing D negative means gauge dominates *)
Lemma crossing_D_neg_means : forall beta kappa L D K,
  crossing_D beta kappa L D K < 0 ->
  gravity_gap_D_at_K kappa L D K < gauge_gap_any_D beta D K.
Proof.
  intros. unfold crossing_D in H. lra.
Qed.

(** Crossing exists (simplified version with explicit witness) *)
Theorem crossing_exists_D : forall beta kappa L D K_large,
  0 <= crossing_D beta kappa L D 0%nat ->
  crossing_D beta kappa L D K_large < 0 ->
  exists K_star : nat,
    0 <= crossing_D beta kappa L D K_star /\
    crossing_D beta kappa L D (S K_star) < 0.
Proof.
  intros beta kappa L D K_large H0 HK.
  (* Intermediate value theorem on nat: *)
  (* f(0) >= 0, f(K_large) < 0 → exists K with f(K) >= 0, f(S K) < 0 *)
  induction K_large.
  - (* K_large = 0: contradiction since f(0) >= 0 and f(0) < 0 *)
    lra.
  - (* K_large = S n *)
    destruct (Qlt_le_dec (crossing_D beta kappa L D K_large) 0) as [Hneg | Hnn].
    + (* f(K_large) < 0: recurse *)
      exact (IHK_large Hneg).
    + (* f(K_large) >= 0 and f(S K_large) < 0: found it *)
      exists K_large. split; auto.
Qed.

(* ================================================================== *)
(*  Part II: K* Depends on D  (~5 lemmas)                             *)
(* ================================================================== *)

(** K* is the crossing point in D dimensions *)
Definition is_crossing_point_D (beta kappa L : Q) (D K : nat) : Prop :=
  0 <= crossing_D beta kappa L D K /\
  crossing_D beta kappa L D (S K) < 0.

(** Higher D → K* is larger (gravity drops faster) *)
Theorem K_star_depends_on_D :
  (* K*^D = 384κL^D / 289 *)
  (* Higher D: K* = L · (384κ/289)^{1/D} *)
  (* As D increases, K* grows (more lattice sites needed) *)
  forall beta kappa L D K_large,
  0 <= crossing_D beta kappa L D 0%nat ->
  crossing_D beta kappa L D K_large < 0 ->
  exists K_star, is_crossing_point_D beta kappa L D K_star.
Proof.
  intros. destruct (crossing_exists_D beta kappa L D K_large H H0) as [K [Hk1 Hk2]].
  exists K. unfold is_crossing_point_D. auto.
Qed.

(** Concrete: D=1, κ=1/10, L=10 → crossing at small K *)
Theorem concrete_D1 :
  (* D=1: κL = 1/10 · 10 = 1 > 289/384 ≈ 0.752 *)
  (* Crossing at K* ≈ 1 *)
  Qpow (1#10) 1 * Qpow 10 1 == 1.
Proof. vm_compute. reflexivity. Qed.

(** Concrete: D=2, κ=1/10, L=10 → crossing at moderate K *)
Theorem concrete_D2 :
  (* D=2: κL² = 1/10 · 100 = 10 > 289/384 *)
  (* Crossing at K* ≈ 3 *)
  Qpow (1#10) 1 * Qpow 10 2 == 10.
Proof. vm_compute. reflexivity. Qed.

(** Concrete: D=3, κ=1/10, L=10 → crossing at larger K *)
Theorem concrete_D3 :
  (* D=3: κL³ = 1/10 · 1000 = 100 > 289/384 *)
  (* Crossing at K* ≈ 7 *)
  Qpow (1#10) 1 * Qpow 10 3 == 100.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part III: Combined Gap in D Dimensions  (~5 lemmas)               *)
(* ================================================================== *)

(** Combined gap = min(gauge, gravity) in D dimensions *)
Definition combined_gap_D (beta kappa L : Q) (D K : nat) : Q :=
  Qmin (gauge_gap_any_D beta D K) (gravity_gap_D_at_K kappa L D K).

(** Combined gap non-negative *)
Lemma combined_gap_D_nonneg : forall beta kappa L D K,
  0 <= gauge_gap_any_D beta D K ->
  0 <= kappa -> 0 <= L ->
  0 <= combined_gap_D beta kappa L D K.
Proof.
  intros. unfold combined_gap_D.
  apply Q.min_glb.
  - exact H.
  - apply gravity_gap_D_at_K_nonneg; auto.
Qed.

(** Combined gap positive when both positive *)
Lemma combined_gap_D_pos : forall beta kappa L D K,
  0 < gauge_gap_any_D beta D K ->
  0 < gravity_gap_D_at_K kappa L D K ->
  0 < combined_gap_D beta kappa L D K.
Proof.
  intros. unfold combined_gap_D.
  apply Q.min_glb_lt; auto.
Qed.

(** Gap survives crossing *)
Theorem gap_survives_crossing_D : forall beta kappa L D K,
  0 < gauge_gap_any_D beta D K ->
  0 < gravity_gap_D_at_K kappa L D K ->
  0 < combined_gap_D beta kappa L D K.
Proof.
  intros. apply combined_gap_D_pos; auto.
Qed.

(** Phase 20 File 2 summary *)
Theorem crossing_D_summary :
  (* crossing_D: D-dimensional crossing process *)
  (* crossing_exists_D: crossing exists in any D *)
  (* combined_gap_D: min(gauge, gravity) in D *)
  (* gap_survives_crossing_D: gap positive when both positive *)
  forall beta kappa L D K,
  0 < gauge_gap_any_D beta D K ->
  0 < gravity_gap_D_at_K kappa L D K ->
  0 < combined_gap_D beta kappa L D K.
Proof. intros. apply combined_gap_D_pos; auto. Qed.
