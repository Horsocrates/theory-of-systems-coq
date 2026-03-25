(** * HydrogenNumbers.v -- Verified hydrogen atom numbers in exact Q
    Elements: E_1, E_2, E_3, lyman_alpha, balmer_alpha, rydberg terms,
              ionization_energy_H
    Roles:    Hydrogen spectrum as exact rational arithmetic
    Rules:    E_n = -1/(2n^2); transition = E_upper - E_lower; all Q
    Status:   complete
    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Lia Lqa.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Helper — Q power                                           *)
(* ================================================================== *)

Fixpoint qpow_h (base : Q) (n : nat) : Q :=
  match n with
  | O => 1
  | S k => base * qpow_h base k
  end.

(* ================================================================== *)
(*  Part II: Hydrogen energy levels E_n = -1/(2n^2)                    *)
(* ================================================================== *)

Definition hydrogen_E (n : positive) : Q :=
  -(1) / (2 * (Zpos n # 1) * (Zpos n # 1)).

Definition H_E1 : Q := hydrogen_E 1.
Definition H_E2 : Q := hydrogen_E 2.
Definition H_E3 : Q := hydrogen_E 3.

Lemma H_E1_value : H_E1 == -(1#2).
Proof. vm_compute. reflexivity. Qed.

Lemma H_E2_value : H_E2 == -(1#8).
Proof. vm_compute. reflexivity. Qed.

Lemma H_E3_value : H_E3 == -(1#18).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part III: Spectral transitions                                     *)
(* ================================================================== *)

(** Transition energy: ΔE = E_upper - E_lower (positive for emission) *)
Definition transition_energy (n_upper n_lower : positive) : Q :=
  hydrogen_E n_upper - hydrogen_E n_lower.

(** Lyman-alpha: n=2 → n=1, photon energy = E_2 - E_1 = -1/8 - (-1/2) = 3/8 *)
Definition lyman_alpha : Q := hydrogen_E 2 - hydrogen_E 1.

Lemma lyman_alpha_value : lyman_alpha == 3#8.
Proof. vm_compute. reflexivity. Qed.

(** Balmer-alpha: n=3 → n=2, photon energy = E_3 - E_2 = -1/18 - (-1/8) = 5/72 *)
Definition balmer_alpha : Q := hydrogen_E 3 - hydrogen_E 2.

Lemma balmer_alpha_value : balmer_alpha == 5#72.
Proof. vm_compute. reflexivity. Qed.

(** Lyman series limit: n=∞ → n=1, energy = |E_1| = 1/2 *)
(** (At n → ∞, E_n → 0, so photon energy = |E_1|) *)

(* ================================================================== *)
(*  Part IV: Rydberg process — partial sums                            *)
(* ================================================================== *)

(** Rydberg formula: 1/λ ∝ (1/n_lower² - 1/n_upper²)
    In Hartree: ΔE = 1/2 · (1/n_l² - 1/n_u²) *)
Definition rydberg_term (n : positive) : Q :=
  1 / (2 * (Zpos n # 1) * (Zpos n # 1)).

Lemma rydberg_term_1 : rydberg_term 1 == 1#2.
Proof. vm_compute. reflexivity. Qed.

Lemma rydberg_term_2 : rydberg_term 2 == 1#8.
Proof. vm_compute. reflexivity. Qed.

Lemma rydberg_term_3 : rydberg_term 3 == 1#18.
Proof. vm_compute. reflexivity. Qed.

(** Lyman-α from Rydberg: R·(1/1² - 1/2²) = 1/2 - 1/8 = 3/8 *)
Lemma lyman_alpha_rydberg :
  rydberg_term 1 - rydberg_term 2 == 3#8.
Proof. vm_compute. reflexivity. Qed.

(** Balmer-α from Rydberg: R·(1/2² - 1/3²) = 1/8 - 1/18 = 5/72 *)
Lemma balmer_alpha_rydberg :
  rydberg_term 2 - rydberg_term 3 == 5#72.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part V: Ionization energy                                          *)
(* ================================================================== *)

(** Ionization energy = energy to remove electron from ground state
    IE = 0 - E_1 = 1/2 Hartree = 13.6 eV *)
Definition ionization_energy_H : Q := -(H_E1).

Lemma ionization_energy_H_value : ionization_energy_H == 1#2.
Proof. vm_compute. reflexivity. Qed.

Lemma ionization_energy_H_positive : 0 < ionization_energy_H.
Proof.
  assert (H: ionization_energy_H == 1#2) by (vm_compute; reflexivity).
  rewrite H. lra.
Qed.

(** Consistency: lyman-alpha < ionization energy *)
Lemma lyman_lt_ionization : lyman_alpha < ionization_energy_H.
Proof.
  assert (H1: lyman_alpha == 3#8) by (vm_compute; reflexivity).
  assert (H2: ionization_energy_H == 1#2) by (vm_compute; reflexivity).
  rewrite H1, H2. lra.
Qed.

(** Paschen-alpha: n=4 → n=3 *)
Definition H_E4 : Q := hydrogen_E 4.

Lemma H_E4_value : H_E4 == -(1#32).
Proof. vm_compute. reflexivity. Qed.

Definition paschen_alpha : Q := hydrogen_E 4 - hydrogen_E 3.

Lemma paschen_alpha_value : paschen_alpha == 7#288.
Proof. vm_compute. reflexivity. Qed.
