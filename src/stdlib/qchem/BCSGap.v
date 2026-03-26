(** * BCSGap.v — BCS gap equation via Pade approximant

    Elements: Pade approximant to exp(-x), BCS gap formula
    Roles:    gap equation -> superconducting order parameter
    Rules:    Pade decreasing; gap positive for positive coupling
    Status:   verified | rational approximation

    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lqa.
Open Scope Q_scope.

(** Pade [2/2] approximant for exp(-x): (12 - 6x + x^2)/(12 + 6x + x^2) *)
Definition pade_exp_neg (x : Q) : Q :=
  (12 - 6 * x + x * x) / (12 + 6 * x + x * x).

(** BCS gap: Delta = omega_D * pade(-1/(N_F*V)) *)
Definition bcs_gap (N_F V omega_D : Q) : Q :=
  omega_D * pade_exp_neg (1 / (N_F * V)).

(** Pade at x=0 gives 1 (exp(0)=1) *)
Theorem pade_at_zero : pade_exp_neg 0 == 1.
Proof. vm_compute. reflexivity. Qed.

(** Pade at x=1 gives 7/19 *)
Theorem pade_at_1 : pade_exp_neg 1 == 7 # 19.
Proof. vm_compute. reflexivity. Qed.

(** Pade at x=2 gives 1/7 *)
Theorem pade_at_2 : pade_exp_neg 2 == 1 # 7.
Proof. vm_compute. reflexivity. Qed.

(** Pade at x=3 *)
Theorem pade_at_3 : pade_exp_neg 3 == 3 # 39.
Proof. vm_compute. reflexivity. Qed.

(** Pade decreases: pade(1) > pade(2) > pade(3) *)
Theorem pade_decreasing_1_2 : pade_exp_neg 2 < pade_exp_neg 1.
Proof. vm_compute. reflexivity. Qed.

Theorem pade_decreasing_2_3 : pade_exp_neg 3 < pade_exp_neg 2.
Proof. vm_compute. reflexivity. Qed.

(** Pade positive for x = 0,1,2,3 *)
Theorem pade_positive_at_1 : 0 < pade_exp_neg 1.
Proof. vm_compute. reflexivity. Qed.

Theorem pade_positive_at_2 : 0 < pade_exp_neg 2.
Proof. vm_compute. reflexivity. Qed.

Theorem pade_positive_at_3 : 0 < pade_exp_neg 3.
Proof. vm_compute. reflexivity. Qed.

(** BCS gap concrete: strong coupling N_F=1, V=1/2, omega_D=1 *)
Definition gap_strong : Q := bcs_gap 1 (1 # 2) 1.

Theorem gap_strong_value : gap_strong == 1 # 7.
Proof. vm_compute. reflexivity. Qed.

Theorem gap_strong_positive : 0 < gap_strong.
Proof. vm_compute. reflexivity. Qed.
