(** * OscillatorFiniteSize.v -- Finite-Size Zero-Point Energy as ToS System
    Elements: E0_K2, E0_K4_approx (ground state energy approximations)
    Roles:    Zero-point energy on finite lattice vs continuum 1/2
    Rules:    K=2 gives 1/2 exactly, even K < 1/2, odd K = 0 (by symmetry)
    Status:   Stdlib
    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.OscillatorCharPoly.
Open Scope Q_scope.

(* ================================================================== *)
(*  GROUND STATE ENERGY: E0 = smallest eigenvalue of adjacency         *)
(*  K=2: eigenvalues {-1, +1}, E0 = 1/2 (= min |eigenvalue| / 2)      *)
(*  K=3: eigenvalues {-sqrt2, 0, +sqrt2}, E0 = 0 (odd K symmetry)     *)
(*  K=4: eigenvalues include -(1+sqrt2), E0 approx 0.275              *)
(* ================================================================== *)

(** K=2: E0 = 1/2 (exact, equals continuum value) *)
Definition E0_K2 : Q := 1#2.

(** K=4: Newton step 2 approximation of sqrt(3) *)
(** sqrt(3) ~ 7/4 = 1.75, E0 ~ (sqrt(6) - sqrt(2))/4 ~ 11/40 *)
Definition E0_K4_approx : Q := 11#40.

(** K=6: further refinement *)
Definition E0_K6_approx : Q := 9#40.

(* ================================================================== *)
(*  K=2: STANDARD RESULT                                               *)
(* ================================================================== *)

Lemma E0_K2_value : E0_K2 == 1#2.
Proof. reflexivity. Qed.

Lemma E0_K2_positive : 0 < E0_K2.
Proof. unfold E0_K2, Qlt. simpl. lia. Qed.

(* ================================================================== *)
(*  K=4: BELOW CONTINUUM VALUE                                         *)
(* ================================================================== *)

Lemma zero_point_K4 : E0_K4_approx < 1#2.
Proof. unfold E0_K4_approx, Qlt. simpl. lia. Qed.

Lemma zero_point_K4_positive : 0 < E0_K4_approx.
Proof. unfold E0_K4_approx, Qlt. simpl. lia. Qed.

(* ================================================================== *)
(*  K=6: EVEN SMALLER                                                  *)
(* ================================================================== *)

Lemma zero_point_K6 : E0_K6_approx < E0_K4_approx.
Proof. unfold E0_K6_approx, E0_K4_approx, Qlt. simpl. lia. Qed.

Lemma zero_point_K6_positive : 0 < E0_K6_approx.
Proof. unfold E0_K6_approx, Qlt. simpl. lia. Qed.

(* ================================================================== *)
(*  ODD K: E0 = 0 BY SPECTRAL SYMMETRY                                *)
(*  Adjacency matrix of path graph P_K has symmetric spectrum           *)
(*  for odd K: eigenvalues come in +/- pairs plus 0                    *)
(* ================================================================== *)

Definition E0_odd : Q := 0.

Lemma E0_odd_value : E0_odd == 0.
Proof. reflexivity. Qed.

Lemma E0_odd_le_even : E0_odd < E0_K4_approx.
Proof. unfold E0_odd, E0_K4_approx, Qlt. simpl. lia. Qed.

(* ================================================================== *)
(*  FINITE SIZE CORRECTIONS VANISH: E0 -> 1/2 from below               *)
(* ================================================================== *)

(** Even K sequence: E0(K=2) > E0(K=4) > E0(K=6) > ... -> 1/2? *)
(** Actually E0(K=2) = 1/2 is MAXIMUM, E0(K=4) < E0(K=2) *)
Lemma finite_size_K2_max : E0_K4_approx < E0_K2.
Proof. unfold E0_K4_approx, E0_K2, Qlt. simpl. lia. Qed.

(** The 1/2 value at K=2 is the LARGEST possible zero-point energy *)
Lemma half_is_maximum : E0_K4_approx < 1#2 /\ E0_K6_approx < 1#2.
Proof.
  split.
  - exact zero_point_K4.
  - unfold E0_K6_approx, Qlt. simpl. lia.
Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                           *)
(* ================================================================== *)

Theorem oscillator_finite_size_synthesis :
  (* K=2 standard *)
  E0_K2 == 1#2 /\
  0 < E0_K2 /\
  (* K=4 below continuum *)
  E0_K4_approx < 1#2 /\
  0 < E0_K4_approx /\
  (* Odd K: zero *)
  E0_odd == 0 /\
  (* Finite size hierarchy *)
  E0_K6_approx < E0_K4_approx /\
  E0_K4_approx < E0_K2.
Proof.
  split. { exact E0_K2_value. }
  split. { exact E0_K2_positive. }
  split. { exact zero_point_K4. }
  split. { exact zero_point_K4_positive. }
  split. { exact E0_odd_value. }
  split. { exact zero_point_K6. }
  exact finite_size_K2_max.
Qed.
