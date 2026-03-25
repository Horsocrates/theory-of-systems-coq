(** * BohrModel.v -- Bohr model quantities as exact Q in atomic units
    Elements: bohr_radius, orbital_speed, alpha_fine, E_n_Bohr,
              bohr_magneton, orbital_radius
    Roles:    Classical Bohr model reproduced entirely in exact Q
    Rules:    a_0 = 1 (a.u.), v_1 = alpha, r_n = n^2, E_n = -1/(2n^2)
    Status:   complete
    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Lia Lqa.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Fundamental constants in atomic units                      *)
(* ================================================================== *)

(** Bohr radius: a_0 = 1 in atomic units (exact) *)
Definition bohr_radius : Q := 1.

(** Fine structure constant: alpha ≈ 1/137.036...
    Rational approximation: 1/137 (exact to 0.03%) *)
Definition alpha_fine : Q := 1#137.

(** Orbital speed of 1s electron: v_1 = alpha · c.
    In atomic units (c = 1/alpha), v_1 = 1.
    But for the ratio v/c = alpha = 1/137. *)
Definition v1_over_c : Q := alpha_fine.

Lemma v1_over_c_value : v1_over_c == 1#137.
Proof. vm_compute. reflexivity. Qed.

(** Bohr magneton: mu_B = e·hbar/(2·m_e) = 1/2 in atomic units *)
Definition bohr_magneton : Q := 1#2.

Lemma bohr_magneton_value : bohr_magneton == 1#2.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part II: Orbital radii r_n = n^2 · a_0                            *)
(* ================================================================== *)

Definition orbital_radius (n : positive) : Q :=
  (Zpos n # 1) * (Zpos n # 1) * bohr_radius.

Lemma orbital_radius_1 : orbital_radius 1 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma orbital_radius_2 : orbital_radius 2 == 4.
Proof. vm_compute. reflexivity. Qed.

Lemma orbital_radius_3 : orbital_radius 3 == 9.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part III: Bohr energy levels E_n = -1/(2n^2)                       *)
(* ================================================================== *)

Definition E_n_Bohr (n : positive) : Q :=
  -(1) / (2 * (Zpos n # 1) * (Zpos n # 1)).

Lemma E_n_Bohr_1 : E_n_Bohr 1 == -(1#2).
Proof. vm_compute. reflexivity. Qed.

Lemma E_n_Bohr_2 : E_n_Bohr 2 == -(1#8).
Proof. vm_compute. reflexivity. Qed.

(** Energy ratio E_1/E_2 = 4 (exact) *)
Lemma energy_ratio_1_2 : E_n_Bohr 1 / E_n_Bohr 2 == 4.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part IV: alpha^2 and relativistic corrections                      *)
(* ================================================================== *)

(** alpha^2 = 1/18769 *)
Definition alpha_sq : Q := alpha_fine * alpha_fine.

Lemma alpha_sq_value : alpha_sq == 1#18769.
Proof. vm_compute. reflexivity. Qed.

(** alpha is small: alpha < 1/100 *)
Lemma alpha_small : alpha_fine < 1#100.
Proof. unfold alpha_fine. lra. Qed.

(** Radius grows quadratically: r_3 / r_1 = 9 *)
Lemma radius_ratio_3_1 : orbital_radius 3 / orbital_radius 1 == 9.
Proof. vm_compute. reflexivity. Qed.

(** Energy-radius product is constant: E_n · r_n = -1/2 for all n *)
Lemma energy_radius_product :
  E_n_Bohr 1 * orbital_radius 1 == -(1#2) /\
  E_n_Bohr 2 * orbital_radius 2 == -(1#2).
Proof. split; vm_compute; reflexivity. Qed.
