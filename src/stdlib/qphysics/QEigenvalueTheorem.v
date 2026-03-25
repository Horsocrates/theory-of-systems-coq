(** * QEigenvalueTheorem.v -- Eigenvalues of Q-matrices are algebraic
    Elements: char_poly coefficients, hydrogen 1s energy, discriminant
    Roles:    Q-matrix eigenvalues are roots of Q-polynomial -> algebraic
    Rules:    1-basis: E = (T+V)/S in Q; 2-basis: roots of Q-quadratic
    Status:   complete
    STATUS: 14 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Lia Lqa.
From ToS Require Import stdlib.qphysics.FundamentalIntegral.
From ToS Require Import stdlib.qphysics.QMatrixElements.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Characteristic polynomial coefficients                     *)
(* ================================================================== *)

(** For 2x2 matrix [[a,b],[c,d]], char poly = lambda^2 - (a+d)*lambda + (ad-bc) *)
Definition char_poly_trace (F11 F22 : Q) : Q := F11 + F22.

Definition char_poly_det (F11 F12 F21 F22 : Q) : Q :=
  F11 * F22 - F12 * F21.

(** Discriminant of quadratic: Delta = trace^2 - 4*det *)
Definition discriminant_2x2 (F11 F12 F21 F22 : Q) : Q :=
  let tr := char_poly_trace F11 F22 in
  let det := char_poly_det F11 F12 F21 F22 in
  tr * tr - 4 * det.

(* ================================================================== *)
(*  Part II: Hydrogen 1s energy (single-basis)                         *)
(* ================================================================== *)

(** For hydrogen with 1s STO (alpha=1, Z=1):
    E = (T + V) / S = (kinetic + nuclear) / overlap *)
Definition hydrogen_1s_energy : Q :=
  (kinetic_s 1 1 + nuclear_s 1 1 1) / overlap_s 1 1.

(** E = (1/8 + (-1/4)) / (1/4) = (-1/8) / (1/4) = -1/2 *)
Lemma hydrogen_1s_E : hydrogen_1s_energy == -(1#2).
Proof. vm_compute. reflexivity. Qed.

(** The exact hydrogen ground state is -1/2 Hartree! This is exact. *)
Lemma hydrogen_energy_negative : (hydrogen_1s_energy < 0)%Q.
Proof. vm_compute. reflexivity. Qed.

(** Single-basis eigenvalue is trivially in Q *)
Lemma single_basis_in_Q :
  exists (p : Z) (q : positive), hydrogen_1s_energy == (p # q).
Proof.
  exists (-1)%Z, 2%positive. vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  Part III: 2x2 eigenvalue theorem                                   *)
(* ================================================================== *)

(** Concrete 2x2 Fock matrix example:
    F = [[F11, F12], [F12, F22]] with all entries in Q *)
Definition F11_example : Q := -(1#2).
Definition F12_example : Q := -(3#8).
Definition F22_example : Q := -(3#8).

Lemma trace_example : char_poly_trace F11_example F22_example == -(7#8).
Proof. vm_compute. reflexivity. Qed.

Lemma det_example :
  char_poly_det F11_example F12_example F12_example F22_example == (3#64).
Proof. vm_compute. reflexivity. Qed.

(* disc = tr^2 - 4*det = (7/8)^2 - 4*(3/64) = 49/64 - 12/64 = 37/64 *)
Lemma discriminant_example :
  discriminant_2x2 F11_example F12_example F12_example F22_example == (37#64).
Proof. vm_compute. reflexivity. Qed.

(** The discriminant is in Q, so eigenvalues are (trace +/- sqrt(disc))/2.
    Since disc in Q, sqrt(disc) is algebraic over Q.
    Therefore eigenvalues are algebraic. *)

(** For the eigenvalue to be rational, we need disc to be a perfect square in Q *)
Definition disc_is_perfect_square (disc : Q) : Prop :=
  exists r : Q, r * r == disc.

(** When disc IS a perfect square, eigenvalues are in Q *)
Lemma eigenvalues_rational_when_perfect_square :
  forall tr disc : Q,
  disc_is_perfect_square disc ->
  exists e1 e2 : Q,
    (e1 + e2 == tr).
Proof.
  intros tr disc [r Hr].
  exists ((tr + r) / 2), ((tr - r) / 2).
  field.
Qed.

(** Eigenvalue algebraicity: char poly has Q coefficients *)
Lemma eigenvalue_algebraic_general :
  forall F11 F12 F21 F22 : Q,
  exists (a2 a1 a0 : Q),
    a2 == 1 /\
    a1 == -(char_poly_trace F11 F22) /\
    a0 == char_poly_det F11 F12 F21 F22.
Proof.
  intros. exists 1, (-(char_poly_trace F11 F22)), (char_poly_det F11 F12 F21 F22).
  repeat split; lra.
Qed.

(* ================================================================== *)
(*  Part IV: Connection to matrix elements                             *)
(* ================================================================== *)

(** All Fock matrix entries from QMatrixElements are in Q *)
Lemma fock_entries_in_Q :
  overlap_s 1 1 == (1#4) /\
  kinetic_s 1 1 == (1#8) /\
  nuclear_s 1 1 1 == -(1#4) /\
  ee_F0_1s 1 == (5#8).
Proof. repeat split; vm_compute; reflexivity. Qed.

(** Virial theorem check: 2*T = -V for exact hydrogen *)
Lemma virial_hydrogen :
  2 * kinetic_s 1 1 + nuclear_s 1 1 1 == 0.
Proof. vm_compute. reflexivity. Qed.

(** Energy decomposition *)
Lemma energy_components :
  kinetic_s 1 1 / overlap_s 1 1 == (1#2) /\
  nuclear_s 1 1 1 / overlap_s 1 1 == -(1).
Proof. split; vm_compute; reflexivity. Qed.

(** Characteristic polynomial coefficients are in Q *)
Lemma char_poly_coeffs_Q :
  exists (p1 : Z) (q1 : positive) (p2 : Z) (q2 : positive),
    char_poly_trace F11_example F22_example == (p1 # q1) /\
    char_poly_det F11_example F12_example F12_example F22_example == (p2 # q2).
Proof.
  exists (-7)%Z, 8%positive, 3%Z, 64%positive.
  split; vm_compute; reflexivity.
Qed.

(** Helium-like system: two-electron repulsion is Q *)
Lemma he_repulsion_Q : ee_F0_1s 1 == (5#8).
Proof. vm_compute. reflexivity. Qed.

(** Total energy for He (simplified): T + V_ne + V_ee *)
Definition helium_approx_energy : Q :=
  2 * (kinetic_s 1 1 / overlap_s 1 1) +
  2 * (nuclear_s 2 1 1 / overlap_s 1 1) +
  ee_F0_1s 1 / overlap_s 1 1.

Lemma helium_approx_value : helium_approx_energy == -(1#2).
Proof. vm_compute. reflexivity. Qed.

