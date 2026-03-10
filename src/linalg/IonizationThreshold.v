(* ========================================================================= *)
(*        IONIZATION THRESHOLD — Energy spectrum accumulation at E=0         *)
(*                                                                          *)
(*  Proves that the hydrogen-like spectrum {E_n} has:                       *)
(*  - All E_n < 0 (bound states)                                           *)
(*  - E_n strictly increasing toward 0                                      *)
(*  - 0 is the accumulation point (ionization threshold)                    *)
(*  - Energy spacing decreases                                              *)
(*                                                                          *)
(*  Builds on CoulombTower (1D) and CoulombFull3D (3D) results.            *)
(*                                                                          *)
(*  STATUS: ~20 Qed, 0 Admitted                                            *)
(*  AXIOMS: classic (via MonotoneConvergence)                               *)
(*  Author: Horsocrates | Date: March 2026                                  *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs List Lia ZArith.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import CauchyReal.
From ToS Require Import SeriesConvergence.
From ToS Require Import MonotoneConvergence.
From ToS Require Import experimental.CoulombTower.
From ToS Require Import experimental.CoulombFull3D.

(* ========================================================================= *)
(*  PART I: Basic energy spectrum properties                                *)
(* ========================================================================= *)

(** Ionization energy is 0 (by definition in our model) *)
Definition ionization_energy : Q := 0.

(** Bound state: energy below ionization *)
Definition is_bound_state (energy : Q) : Prop := energy < 0.

(** Free state: energy at or above ionization *)
Definition is_free_state (energy : Q) : Prop := 0 <= energy.

(** Energy levels are the hydrogen limits *)
Definition energy_level (n : nat) : Q := hydrogen_limit n.

(** Ionization energy value *)
Lemma ionization_energy_value : ionization_energy == 0.
Proof. reflexivity. Qed.

(** Ground state energy = -1/4 *)
Lemma ground_state_energy : energy_level 0 == -(1#4).
Proof. unfold energy_level. exact hydrogen_limit_ground. Qed.

(** First excited state energy = -1/8 *)
Lemma first_excited_energy : energy_level 1 == -(1#8).
Proof. unfold energy_level. exact hydrogen_limit_excited. Qed.

(** Second excited state energy = -1/12 *)
Lemma second_excited_energy : energy_level 2 == -(1#12).
Proof. unfold energy_level. exact hydrogen_limit_n2. Qed.

(** All energy levels are negative (bound) *)
Theorem all_states_bound : forall n, is_bound_state (energy_level n).
Proof.
  intros n. unfold is_bound_state, energy_level.
  exact (limit_negative n).
Qed.

(** Ground state is bound *)
Corollary ground_state_bound : is_bound_state (energy_level 0).
Proof. exact (all_states_bound 0). Qed.

(* ========================================================================= *)
(*  PART II: Energy ordering                                                *)
(* ========================================================================= *)

(** Energy levels are increasing: E_n < E_{n+1} *)
Theorem energy_increasing : forall n, energy_level n < energy_level (S n).
Proof.
  intros n. unfold energy_level, hydrogen_limit.
  unfold Qlt, Qnum, Qden.
  simpl.
  (* -(1 / (4 * (S n + 1))) < -(1 / (4 * (S (S n) + 1))) *)
  (* i.e., -1/(4*(n+1)) < -1/(4*(n+2)) *)
  (* i.e., 1/(4*(n+2)) < 1/(4*(n+1)) *)
  lia.
Qed.

(** Ground state is the minimum *)
Theorem ground_state_minimum : forall n, energy_level 0 <= energy_level n.
Proof.
  induction n as [| n' IH].
  - lra.
  - apply Qle_trans with (energy_level n'); [exact IH |].
    apply Qlt_le_weak. exact (energy_increasing n').
Qed.

(** Energy spacing: E_{n+1} - E_n > 0 *)
Theorem energy_spacing_positive : forall n,
  energy_level (S n) - energy_level n > 0.
Proof.
  intros n. assert (H := energy_increasing n). lra.
Qed.

(** Ground state gap: E_1 - E_0 *)
Lemma ground_state_gap : energy_level 1 - energy_level 0 == 1#8.
Proof.
  unfold energy_level, hydrogen_limit. unfold Qeq, Qnum, Qden. simpl. lia.
Qed.

(** First excited gap: E_2 - E_1 *)
Lemma first_excited_gap : energy_level 2 - energy_level 1 == 1#24.
Proof.
  unfold energy_level, hydrogen_limit. unfold Qeq, Qnum, Qden. simpl. lia.
Qed.

(** Energy spacing decreases: gap_{n+1} < gap_n *)
Theorem energy_spacing_decreases : forall n,
  energy_level (S (S n)) - energy_level (S n) <
  energy_level (S n) - energy_level n.
Proof.
  intros n. unfold energy_level, hydrogen_limit.
  unfold Qlt, Qminus, Qplus, Qopp, Qnum, Qden. simpl.
  apply Z.compare_lt_iff.
  (* Simplify Z.pos_sub (Pos.succ q) q → 1 *)
  assert (Hps : forall q : positive, Z.pos_sub (Pos.succ q) q = 1%Z).
  { intros q. rewrite Z.pos_sub_gt; [| lia]. f_equal. lia. }
  rewrite !Hps. clear Hps.
  simpl Z.double.
  (* Goal: 4 * Z.pos(d2*d1) < 4 * Z.pos(d3*d2) *)
  apply Z.mul_lt_mono_pos_l; [lia |].
  (* Goal: (Z.pos(d2*d1) < Z.pos(d3*d2))%Z, which is (d2*d1 < d3*d2)%positive *)
  set (p1 := Pos.of_succ_nat n).
  set (p2 := Pos.succ (Pos.of_succ_nat n)).
  set (p3 := Pos.succ (Pos.succ (Pos.of_succ_nat n))).
  (* Goal: Z.pos(p2 * p1~0~0)~0~0 < Z.pos(p3 * p2~0~0)~0~0 *)
  (* = (p2 * p1~0~0 < p3 * p2~0~0)%positive via xO wrapper *)
  assert (Hp12 : (p1~0~0 < p2~0~0)%positive) by (unfold p1, p2; lia).
  assert (Hp23 : (p2 < p3)%positive) by (unfold p2, p3; lia).
  assert (Hstep1 : (p2 * p1~0~0 < p2 * p2~0~0)%positive).
  { apply Pos.mul_lt_mono_l. exact Hp12. }
  assert (Hstep2 : (p2 * p2~0~0 < p3 * p2~0~0)%positive).
  { apply Pos.mul_lt_mono_r. exact Hp23. }
  assert (Hlt : (p2 * p1~0~0 < p3 * p2~0~0)%positive).
  { exact (Pos.lt_trans _ _ _ Hstep1 Hstep2). }
  (* The outer ~0~0 preserves ordering *)
  assert (Hfinal : ((p2 * p1~0~0)~0~0 < (p3 * p2~0~0)~0~0)%positive) by lia.
  exact Hfinal.
Qed.

(* ========================================================================= *)
(*  PART III: Ionization threshold                                          *)
(* ========================================================================= *)

(** Ionization at zero: for any eps > 0, some E_n is within eps of 0 *)
Theorem ionization_at_zero : forall (eps : Q),
  0 < eps ->
  exists N, Qabs (energy_level N) < eps.
Proof.
  intros eps Heps.
  assert (Hion := ionization eps Heps).
  destruct Hion as [N HN].
  exists N. unfold energy_level. exact (HN N (Nat.le_refl N)).
Qed.

(** Ionization is supremum: all E_n < 0, and 0 is the limit *)
Theorem ionization_is_supremum :
  (forall n, energy_level n < 0) /\
  (forall eps, 0 < eps -> exists N, Qabs (energy_level N) < eps).
Proof.
  split.
  - exact all_states_bound.
  - exact ionization_at_zero.
Qed.

(** Finitely many bound states below any threshold *)
Theorem finite_bound_states_below : forall (E : Q),
  E < 0 ->
  exists N_max, forall n, (N_max < n)%nat -> E < energy_level n.
Proof.
  intros E HE.
  assert (Heps : 0 < -E) by lra.
  destruct (ionization_at_zero (-E) Heps) as [N HN].
  exists N.
  intros n Hn.
  (* E_n > E_N > E because |E_N| < -E means E_N > E *)
  assert (HNn : energy_level N < energy_level n).
  { clear HN. induction Hn as [| n' Hn' IH].
    - exact (energy_increasing N).
    - apply Qlt_trans with (energy_level n'); [exact IH | exact (energy_increasing n')]. }
  assert (Hbound : energy_level N > E).
  { assert (Hneg := all_states_bound N).
    unfold is_bound_state in Hneg.
    destruct (Qlt_le_dec (energy_level N) 0) as [Hn2 | Hp].
    - rewrite Qabs_neg in HN; [| lra]. lra.
    - lra. }
  lra.
Qed.

(** Infinite accumulation near zero *)
Theorem infinite_accumulation : forall (eps : Q),
  0 < eps ->
  exists n, - eps < energy_level n /\ energy_level n < 0.
Proof.
  intros eps Heps.
  destruct (ionization_at_zero eps Heps) as [N HN].
  exists N. split.
  - assert (Hneg := all_states_bound N). unfold is_bound_state in Hneg.
    rewrite Qabs_neg in HN; [| lra]. lra.
  - exact (all_states_bound N).
Qed.

(** 3D convergence: energy levels converge in 3D too *)
Theorem energy_3d_converges : forall n_r l (eps : Q),
  0 < eps ->
  exists N, forall K, (N <= K)%nat ->
    Qabs (scaled_energy_3d K n_r l - hydrogen_limit_3d n_r l) < eps.
Proof.
  intros n_r l eps Heps.
  exact (convergence_3d n_r l eps Heps).
Qed.

(** Centrifugal splitting vanishes *)
Theorem centrifugal_vanishes : forall n_r l (eps : Q),
  0 < eps ->
  exists N, forall K, (N <= K)%nat ->
    Qabs (scaled_energy_3d K n_r l - scaled_energy_3d K n_r 0) < eps.
Proof.
  intros n_r l eps Heps.
  exact (splitting_vanishes n_r l eps Heps).
Qed.

(** Energy ratio: E_n / E_0 = 1/(n+1) *)
Theorem energy_ratio : forall n,
  energy_level n / energy_level 0 == 1 / inject_Z (Z.of_nat (S n)).
Proof.
  intros n. unfold energy_level. exact (limit_ratio n).
Qed.

(* ========================================================================= *)
(*  PART IV: Spectral threshold                                             *)
(* ========================================================================= *)

(** Spectral transition: below 0 finitely many, accumulation at 0 *)
Theorem spectral_transition :
  (forall E, E < 0 -> exists N_max, forall n, (N_max < n)%nat -> E < energy_level n) /\
  (forall eps, 0 < eps -> exists n, - eps < energy_level n /\ energy_level n < 0).
Proof.
  split.
  - exact finite_bound_states_below.
  - exact infinite_accumulation.
Qed.

(** Honest limitation: our spectrum is -1/(4(n+1)), true hydrogen is -1/(2n²) *)
Theorem honest_limitation :
  energy_level 0 == -(1#4) /\
  energy_level 1 == -(1#8) /\
  energy_level 2 == -(1#12).
Proof.
  split; [exact ground_state_energy |].
  split; [exact first_excited_energy | exact second_excited_energy].
Qed.

(** Main ionization theorem *)
Theorem ionization_main_theorem :
  (* 1. All bound *)
  (forall n, energy_level n < 0) /\
  (* 2. Increasing *)
  (forall n, energy_level n < energy_level (S n)) /\
  (* 3. Ionization at 0 *)
  (forall eps, 0 < eps -> exists N, Qabs (energy_level N) < eps) /\
  (* 4. Spacing decreases *)
  (forall n, energy_level (S (S n)) - energy_level (S n) <
             energy_level (S n) - energy_level n).
Proof.
  split; [exact all_states_bound |].
  split; [exact energy_increasing |].
  split; [exact ionization_at_zero | exact energy_spacing_decreases].
Qed.

(* ========================================================================= *)
(*  SUMMARY                                                                 *)
(*  ~20 Qed, 0 Admitted                                                    *)
(*                                                                          *)
(*  Part I: ionization_energy_value, ground_state_energy,                   *)
(*          first_excited_energy, second_excited_energy,                     *)
(*          all_states_bound, ground_state_bound                            *)
(*  Part II: energy_increasing, ground_state_minimum,                       *)
(*           energy_spacing_positive, ground_state_gap,                     *)
(*           first_excited_gap, energy_spacing_decreases                    *)
(*  Part III: ionization_at_zero, ionization_is_supremum,                   *)
(*            finite_bound_states_below, infinite_accumulation,             *)
(*            energy_3d_converges, centrifugal_vanishes, energy_ratio       *)
(*  Part IV: spectral_transition, honest_limitation,                        *)
(*           ionization_main_theorem                                        *)
(* ========================================================================= *)
