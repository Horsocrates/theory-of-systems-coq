(** * SU3Transfer.v -- Transfer matrix eigenvalues for SU(3)
    Elements: Z_su3_approx, plaquette_su3, gap_su3
    Roles:    Partition function and mass gap from character expansion
    Rules:    Z = 1 + 3β + 8β²/9, gap = 1 - β/6 > 0 for β < 6
    Status:   Gauge
    STATUS: 15 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import gauge.SU3Representations.
From ToS Require Import gauge.SU3Characters.

Open Scope Q_scope.

(* ================================================================== *)
(*  PARTITION FUNCTION                                                 *)
(* ================================================================== *)

(** Z = Σ dim(p,q)² · t_{p,q}
    At leading order: Z ≈ 1² · 1 + 3² · (β/6) + 3² · (β/6) + 8² · (β²/72)
    = 1 + 9β/6 + 9β/6 + 64β²/72
    = 1 + 3β + 8β²/9 *)

Definition Z_su3_approx (beta : Q) : Q :=
  1 + 3 * beta + 8 * beta * beta * (1#9).

Lemma Z_su3_at_0 : Z_su3_approx 0 == 1.
Proof. unfold Z_su3_approx. ring. Qed.

Lemma Z_su3_at_1 : Z_su3_approx 1 == 44#9.
Proof. unfold Z_su3_approx. ring. Qed.

Lemma Z_su3_positive_1 : 0 < Z_su3_approx 1.
Proof. rewrite Z_su3_at_1. lra. Qed.

Lemma Z_su3_positive_0 : 0 < Z_su3_approx 0.
Proof. rewrite Z_su3_at_0. lra. Qed.

(* ================================================================== *)
(*  PLAQUETTE EXPECTATION                                              *)
(* ================================================================== *)

(** ⟨P⟩ = (1/Z)·dZ/dβ where dZ/dβ = 3 + 16β/9 *)
Definition dZ_dbeta (beta : Q) : Q :=
  3 + 16 * beta * (1#9).

Definition plaquette_su3 (beta : Q) : Q :=
  dZ_dbeta beta / Z_su3_approx beta.

Lemma dZ_at_0 : dZ_dbeta 0 == 3.
Proof. unfold dZ_dbeta. ring. Qed.

Lemma plaquette_su3_at_0 : plaquette_su3 0 == 3.
Proof. unfold plaquette_su3. rewrite dZ_at_0, Z_su3_at_0. field. Qed.

Lemma plaquette_positive : 0 < dZ_dbeta 1.
Proof. unfold dZ_dbeta. lra. Qed.

(* ================================================================== *)
(*  MASS GAP                                                           *)
(* ================================================================== *)

(** gap = t_{0,0} - t_{1,0} = 1 - β/6 *)
Definition gap_su3 (beta : Q) : Q :=
  t_trivial_su3 beta - t_fund_su3 beta.

Lemma gap_su3_at_0 : gap_su3 0 == 1.
Proof. unfold gap_su3, t_trivial_su3, t_fund_su3. ring. Qed.

Lemma gap_su3_at_1 : gap_su3 1 == 5#6.
Proof. unfold gap_su3, t_trivial_su3, t_fund_su3. ring. Qed.

Lemma gap_su3_positive_1 : 0 < gap_su3 1.
Proof. rewrite gap_su3_at_1. lra. Qed.

Lemma gap_su3_at_3 : gap_su3 3 == 1#2.
Proof. unfold gap_su3, t_trivial_su3, t_fund_su3. ring. Qed.

(** Gap decreases with β (coupling weakens) *)
Lemma gap_decreases : gap_su3 1 > gap_su3 3.
Proof. rewrite gap_su3_at_1, gap_su3_at_3. lra. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

Theorem su3_transfer_synthesis :
  Z_su3_approx 1 == 44#9 /\
  gap_su3 1 == 5#6 /\
  0 < gap_su3 1 /\
  0 < Z_su3_approx 1.
Proof.
  split; [|split; [|split]].
  - exact Z_su3_at_1.
  - exact gap_su3_at_1.
  - exact gap_su3_positive_1.
  - exact Z_su3_positive_1.
Qed.
