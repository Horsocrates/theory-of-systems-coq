(** * PiRational.v -- Better pi approximation: 355/113
    Elements: pi_7, pi_113, beta_0 comparison
    Roles:    Zu Chongzhi approximation for improved precision
    Rules:    355/113 within Archimedes bounds, qualitative results unchanged
    Status:   Foundation
    STATUS: 10 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Lia ZArith.
From Stdlib Require Import Qabs.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

(* ================================================================== *)
(*  PI APPROXIMATIONS                                                   *)
(* ================================================================== *)

(** pi approximations over Q:
    22/7       = 3.142857...  error: 4.0 * 10^-4
    355/113    = 3.1415929...  error: 8.5 * 10^-8

    355/113 is Zu Chongzhi's approximation (5th century).
    Best rational with denominator <= 113. *)

Definition pi_7 : Q := 22 # 7.
Definition pi_113 : Q := 355 # 113.

(** Bounds: pi is between 223/71 and 22/7 (Archimedes) *)
Definition pi_lower : Q := 223 # 71.
Definition pi_upper : Q := 22 # 7.

Lemma pi_bounds : pi_lower < pi_upper.
Proof. unfold pi_lower, pi_upper. lra. Qed.

(** 355/113 is within Archimedes' bounds *)
Lemma pi_113_in_lower_bound : pi_lower < pi_113.
Proof. unfold pi_lower, pi_113. lra. Qed.

Lemma pi_113_in_upper_bound : pi_113 < pi_upper.
Proof. unfold pi_113, pi_upper. lra. Qed.

Lemma pi_113_in_bounds : pi_lower < pi_113 /\ pi_113 < pi_upper.
Proof. split; [exact pi_113_in_lower_bound | exact pi_113_in_upper_bound]. Qed.

(** 355/113 > 22/7 is FALSE: 355/113 < 22/7 *)
Lemma pi_113_lt_pi_7 : pi_113 < pi_7.
Proof. unfold pi_113, pi_7. lra. Qed.

(* ================================================================== *)
(*  IMPACT ON BETA_0                                                    *)
(* ================================================================== *)

(** beta_0 = (11N - 2n_f) / (12*pi)
    For SU(3) with n_f = 3 quarks: 11*3 - 2*3 = 27 *)

Definition beta_0_pi7 : Q := 27 * 7 / (12 * 22).
Definition beta_0_pi113 : Q := 27 * 113 / (12 * 355).

Lemma beta_0_pi7_positive : 0 < beta_0_pi7.
Proof. unfold beta_0_pi7, Qlt. simpl. lia. Qed.

Lemma beta_0_pi113_positive : 0 < beta_0_pi113.
Proof. unfold beta_0_pi113, Qlt. simpl. lia. Qed.

Lemma beta_0_both_positive :
  0 < beta_0_pi7 /\ 0 < beta_0_pi113.
Proof. split; [exact beta_0_pi7_positive | exact beta_0_pi113_positive]. Qed.

(** Difference is small: qualitative result (AF) unchanged *)
(** beta_0_pi113 slightly larger (better pi = smaller denom = larger result) *)
Lemma beta_0_close :
  beta_0_pi113 - beta_0_pi7 < 1 # 100.
Proof.
  unfold beta_0_pi7, beta_0_pi113, Qlt, Qminus, Qplus, Qopp. simpl. lia.
Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                           *)
(* ================================================================== *)

Theorem pi_summary :
  pi_lower < pi_113 /\
  pi_113 < pi_upper /\
  0 < beta_0_pi7 /\
  0 < beta_0_pi113 /\
  beta_0_pi113 - beta_0_pi7 < 1 # 100.
Proof.
  split; [|split; [|split; [|split]]].
  - exact pi_113_in_lower_bound.
  - exact pi_113_in_upper_bound.
  - exact beta_0_pi7_positive.
  - exact beta_0_pi113_positive.
  - exact beta_0_close.
Qed.
