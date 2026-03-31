(* ========================================================================= *)
(*                     COUPLING RUNNING                                      *)
(*           Running coupling as process, alpha notation                     *)
(*                                                                          *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)        *)
(*                                                                          *)
(*  Author:  Horsocrates | Version: 1.0 (E/R/R) | Date: March 2026         *)
(*                                                                          *)
(*  STATUS: 8 Qed, 0 Admitted, 0 axioms                                    *)
(*                                                                          *)
(* ========================================================================= *)
(*                                                                          *)
(*  E/R/R INTERPRETATION:                                                   *)
(*  =====================                                                   *)
(*                                                                          *)
(*  The running coupling alpha(n) is a P4 process (nat -> Q):              *)
(*                                                                          *)
(*    Elements = coupling values alpha(0)=1, alpha(1)=1/5                   *)
(*    Roles    = alpha (coupling) vs alpha_inv (inverse coupling)            *)
(*    Rules    = alpha decreases, alpha_inv grows linearly with beta=4,     *)
(*               extrapolation gives alpha_inv(14) = 57                     *)
(*                                                                          *)
(* ========================================================================= *)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ===== Running coupling data ===== *)

Definition alpha_running_0 : Q := 1.
Definition alpha_running_1 : Q := 1#5.
Definition alpha_inv_0 : Q := 1.
Definition alpha_inv_1 : Q := 5.
Definition beta_per_step : Q := 4.

(* ===== Lemmas ===== *)

Lemma alpha_0 : alpha_running_0 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma alpha_1 : alpha_running_1 == 1#5.
Proof. vm_compute. reflexivity. Qed.

Lemma alpha_inv_diff : alpha_inv_1 - alpha_inv_0 == 4.
Proof. vm_compute. reflexivity. Qed.

Lemma coupling_ratio : alpha_running_1 / alpha_running_0 == 1#5.
Proof. vm_compute. reflexivity. Qed.

Lemma extrapolate_14 : alpha_inv_0 + beta_per_step * 14 == 57.
Proof. vm_compute. reflexivity. Qed.

Lemma running_positive : 0 < alpha_running_1.
Proof.
  assert (H : alpha_running_1 == 1#5) by (vm_compute; reflexivity).
  rewrite H. lra.
Qed.

Lemma running_decreasing : alpha_running_1 < alpha_running_0.
Proof.
  assert (H0 : alpha_running_0 == 1) by (vm_compute; reflexivity).
  assert (H1 : alpha_running_1 == 1#5) by (vm_compute; reflexivity).
  rewrite H0, H1. lra.
Qed.

(* ===== Synthesis ===== *)

Lemma coupling_running_synthesis :
  (* Running coupling is a well-defined P4 process *)
  alpha_running_1 < alpha_running_0 /\
  0 < alpha_running_1 /\
  alpha_inv_1 - alpha_inv_0 == 4 /\
  alpha_inv_0 + beta_per_step * 14 == 57.
Proof.
  split; [exact running_decreasing |].
  split; [exact running_positive |].
  split; [exact alpha_inv_diff |].
  exact extrapolate_14.
Qed.
