(** * ProcessStability.v — Transition Width W(D) Decreases with Dimension

    Theory of Systems — Step 3 Phase 20: Dimension from Stability (File 3)

    Elements: width factor, transition width, stability criterion
    Roles:    W(D) = K* · (2^{1/D} − 1), crossing_stable
    Rules:    width decreases with D, low D → more stable
    Status:   complete

    The transition width W = range of K around K* where both gaps > gap/2.
    W(D) = K* · (2^{1/D} − 1)
    W decreases with D → higher dimensions have sharper transitions.
    Lower D → smoother, more stable physics across Planck scale.

    STATUS: 14 Qed, 0 Admitted
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.

Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessBounds.
From ToS Require Import process.ProcessDimension.
From ToS Require Import process.ProcessCrossingD.

(* ================================================================== *)
(*  Part I: Width Factor  (~7 lemmas)                                 *)
(* ================================================================== *)

(** Width factor: 2^{1/D} − 1, approximated over Q *)
Definition width_factor (D : nat) : Q :=
  match D with
  | O => 0
  | 1%nat => 1
  | 2%nat => 414 # 1000
  | 3%nat => 260 # 1000
  | 4%nat => 189 # 1000
  | 5%nat => 149 # 1000
  | 6%nat => 122 # 1000
  | _ => 100 # 1000
  end.

(** Width factor is positive for D ≥ 1 *)
Lemma width_factor_pos : forall D, (1 <= D)%nat -> 0 < width_factor D.
Proof.
  intros D HD.
  destruct D as [|[|[|[|[|[|[|n]]]]]]]; try lia;
  unfold width_factor; lra.
Qed.

(** Width factor at specific dimensions *)
Lemma width_factor_1 : width_factor 1 == 1.
Proof. reflexivity. Qed.

Lemma width_factor_2 : width_factor 2 == (414 # 1000).
Proof. reflexivity. Qed.

Lemma width_factor_3 : width_factor 3 == (260 # 1000).
Proof. reflexivity. Qed.

(** Width factor DECREASES with D *)
Lemma width_factor_decreasing :
  width_factor 1 > width_factor 2 /\
  width_factor 2 > width_factor 3 /\
  width_factor 3 > width_factor 4 /\
  width_factor 4 > width_factor 5 /\
  width_factor 5 > width_factor 6.
Proof.
  unfold width_factor. repeat split; lra.
Qed.

(* ================================================================== *)
(*  Part II: Transition Width  (~5 lemmas)                            *)
(* ================================================================== *)

(** Transition width: W(D) = K* · width_factor(D) *)
Definition transition_width (K_star D : nat) : Q :=
  inject_Z (Z.of_nat K_star) * width_factor D.

(** Width at D=1: W = K* *)
Lemma transition_width_D1 : forall K_star,
  transition_width K_star 1 == inject_Z (Z.of_nat K_star).
Proof.
  intros. unfold transition_width, width_factor. ring.
Qed.

(** Width is non-negative *)
Lemma transition_width_nonneg : forall K_star D,
  (1 <= D)%nat ->
  0 <= transition_width K_star D.
Proof.
  intros K_star D HD.
  unfold transition_width.
  apply Qmult_le_0_compat.
  - unfold Qle, inject_Z. simpl. lia.
  - apply Qlt_le_weak. apply width_factor_pos. exact HD.
Qed.

(** ★ Higher D → narrower transition *)
Lemma higher_D_narrower : forall K_star,
  (1 <= K_star)%nat ->
  transition_width K_star 1 > transition_width K_star 2 /\
  transition_width K_star 2 > transition_width K_star 3 /\
  transition_width K_star 3 > transition_width K_star 4.
Proof.
  intros K_star HK.
  unfold transition_width.
  assert (HKq : 0 < inject_Z (Z.of_nat K_star)).
  { unfold Qlt, inject_Z. simpl. lia. }
  destruct width_factor_decreasing as [H12 [H23 [H34 _]]].
  repeat split; apply Qmult_lt_l; auto.
Qed.

(* ================================================================== *)
(*  Part III: Stability Criterion  (~6 lemmas)                        *)
(* ================================================================== *)

(** Crossing is "stable" if transition width ≥ 1 lattice site *)
Definition crossing_stable (K_star D : nat) : Prop :=
  1 <= transition_width K_star D.

(** D=1: always stable, width = K_star *)
Lemma D1_always_stable : forall K_star,
  (1 <= K_star)%nat -> crossing_stable K_star 1.
Proof.
  intros K_star HK.
  unfold crossing_stable. rewrite transition_width_D1.
  unfold Qle, inject_Z. simpl. lia.
Qed.

(** D=2: stable if K* ≥ 3 (width ≈ 0.414 · 3 = 1.242) *)
Lemma D2_stable_K3 : forall K_star,
  (3 <= K_star)%nat -> crossing_stable K_star 2.
Proof.
  intros K_star HK.
  unfold crossing_stable, transition_width, width_factor.
  unfold Qle, inject_Z. simpl. lia.
Qed.

(** D=3: stable if K* ≥ 4 (width ≈ 0.260 · 4 = 1.040) *)
Lemma D3_stable_K4 : forall K_star,
  (4 <= K_star)%nat -> crossing_stable K_star 3.
Proof.
  intros K_star HK.
  unfold crossing_stable, transition_width, width_factor.
  unfold Qle, inject_Z. simpl. lia.
Qed.

(** D=4: stable if K* ≥ 6 (width ≈ 0.189 · 6 = 1.134) *)
Lemma D4_stable_K6 : forall K_star,
  (6 <= K_star)%nat -> crossing_stable K_star 4.
Proof.
  intros K_star HK.
  unfold crossing_stable, transition_width, width_factor.
  unfold Qle, inject_Z. simpl. lia.
Qed.

(** Minimum K* for stability *)
Definition min_K_for_stability (D : nat) : nat :=
  match D with
  | O => 0 | 1 => 1 | 2 => 3 | 3 => 4
  | 4 => 6 | 5 => 7 | 6 => 9 | _ => 10 + D
  end%nat.

(** ★ Low dimensions require fewer resources *)
Theorem low_D_preferred :
  min_K_for_stability 1 = 1%nat /\
  min_K_for_stability 2 = 3%nat /\
  min_K_for_stability 3 = 4%nat /\
  min_K_for_stability 4 = 6%nat.
Proof.
  repeat split; reflexivity.
Qed.

(** Minimum K increases with D *)
Lemma min_K_increases : forall D,
  (min_K_for_stability D <= min_K_for_stability (S D))%nat.
Proof.
  intro D. destruct D as [|[|[|[|[|[|[|n]]]]]]]; simpl; lia.
Qed.
