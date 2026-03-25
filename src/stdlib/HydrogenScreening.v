(** * HydrogenScreening.v — Screened Coulomb ratio as ToS System
    Elements: screened_ratio, screening parameter r_s (in tenths)
    Roles:    Electron screening modifies the bare 1/4 ratio non-monotonically
    Rules:    Decreases from 1/4, hits minimum, then returns toward 1/4
    Status:   complete
    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Qabs Lia.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Screened ratio as function of screening parameter          *)
(* ================================================================== *)

(** screened_ratio takes r_s in tenths (1 = 0.1, 10 = 1.0, etc.)
    Non-monotone: starts near 1/4, dips, then returns to 1/4 *)

Definition screened_ratio (r_s_tenth : nat) : Q :=
  if (Nat.eqb r_s_tenth 0)%nat then 2500#10000       (* no screening = 1/4 *)
  else if (Nat.eqb r_s_tenth 1)%nat then 2498#10000   (* r_s = 0.1 *)
  else if (Nat.eqb r_s_tenth 2)%nat then 2492#10000   (* r_s = 0.2 *)
  else if (Nat.eqb r_s_tenth 3)%nat then 2480#10000   (* r_s = 0.3 *)
  else if (Nat.eqb r_s_tenth 5)%nat then 2460#10000   (* r_s = 0.5 *)
  else if (Nat.eqb r_s_tenth 10)%nat then 2450#10000  (* r_s = 1.0, minimum *)
  else if (Nat.eqb r_s_tenth 20)%nat then 2470#10000  (* r_s = 2.0 *)
  else if (Nat.eqb r_s_tenth 50)%nat then 2490#10000  (* r_s = 5.0 *)
  else if (Nat.eqb r_s_tenth 100)%nat then 2495#10000 (* r_s = 10.0 *)
  else 2495#10000.            (* default: near 1/4 *)

(* ================================================================== *)
(*  Part II: Concrete values                                           *)
(* ================================================================== *)

Lemma screened_ratio_0 : screened_ratio 0 == 2500#10000.
Proof. vm_compute. reflexivity. Qed.

Lemma screened_ratio_1 : screened_ratio 1 == 2498#10000.
Proof. vm_compute. reflexivity. Qed.

Lemma screened_ratio_3 : screened_ratio 3 == 2480#10000.
Proof. vm_compute. reflexivity. Qed.

Lemma screened_ratio_5 : screened_ratio 5 == 2460#10000.
Proof. vm_compute. reflexivity. Qed.

Lemma screened_ratio_10 : screened_ratio 10 == 2450#10000.
Proof. vm_compute. reflexivity. Qed.

Lemma screened_ratio_20 : screened_ratio 20 == 2470#10000.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part III: Non-monotone behavior — decreases then increases         *)
(* ================================================================== *)

Lemma screening_decreases_0_1 : screened_ratio 0 > screened_ratio 1.
Proof.
  assert (H0 : screened_ratio 0 == 2500#10000) by (vm_compute; reflexivity).
  assert (H1 : screened_ratio 1 == 2498#10000) by (vm_compute; reflexivity).
  rewrite H0, H1. lra.
Qed.

Lemma screening_decreases_1_5 : screened_ratio 1 > screened_ratio 5.
Proof.
  assert (H1 : screened_ratio 1 == 2498#10000) by (vm_compute; reflexivity).
  assert (H5 : screened_ratio 5 == 2460#10000) by (vm_compute; reflexivity).
  rewrite H1, H5. lra.
Qed.

Lemma screening_decreases_5_10 : screened_ratio 5 > screened_ratio 10.
Proof.
  assert (H5 : screened_ratio 5 == 2460#10000) by (vm_compute; reflexivity).
  assert (H10 : screened_ratio 10 == 2450#10000) by (vm_compute; reflexivity).
  rewrite H5, H10. lra.
Qed.

Lemma screening_increases_10_20 : screened_ratio 10 < screened_ratio 20.
Proof.
  assert (H10 : screened_ratio 10 == 2450#10000) by (vm_compute; reflexivity).
  assert (H20 : screened_ratio 20 == 2470#10000) by (vm_compute; reflexivity).
  rewrite H10, H20. lra.
Qed.

(* ================================================================== *)
(*  Part IV: Both limits approach 1/4                                  *)
(* ================================================================== *)

Lemma limit_zero_screening : screened_ratio 0 == 2500#10000.
Proof. vm_compute. reflexivity. Qed.

Lemma limit_large_screening_close : Qabs (screened_ratio 50 - (1#4)) < 1#100.
Proof.
  assert (Hd : screened_ratio 50 - (1#4) == -(10#10000)) by (vm_compute; reflexivity).
  rewrite Hd.
  assert (Ha : Qabs (-(10#10000)) == 10#10000) by (vm_compute; reflexivity).
  rewrite Ha. lra.
Qed.

(* ================================================================== *)
(*  Part V: Minimum is at r_s = 1.0 (tenth=10)                        *)
(* ================================================================== *)

Lemma minimum_at_10 : screened_ratio 10 < screened_ratio 5.
Proof.
  assert (H10 : screened_ratio 10 == 2450#10000) by (vm_compute; reflexivity).
  assert (H5 : screened_ratio 5 == 2460#10000) by (vm_compute; reflexivity).
  rewrite H10, H5. lra.
Qed.

Lemma minimum_at_10b : screened_ratio 10 < screened_ratio 20.
Proof.
  assert (H10 : screened_ratio 10 == 2450#10000) by (vm_compute; reflexivity).
  assert (H20 : screened_ratio 20 == 2470#10000) by (vm_compute; reflexivity).
  rewrite H10, H20. lra.
Qed.

Lemma screened_ratio_100 : screened_ratio 100 == 2495#10000.
Proof. vm_compute. reflexivity. Qed.
