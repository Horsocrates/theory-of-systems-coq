(** * LithiumNumbers.v -- Verified lithium atom numbers in exact Q
    Elements: E_Li_1s, E_Li_2s, IE_Li_Koopmans, Li_plus_energy
    Roles:    Lithium ground state energetics as exact Q
    Rules:    1s²2s configuration; Koopmans IE = -ε_2s; Li+ He-like
    Status:   complete
    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Lia Lqa.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Lithium 1s orbital energy                                  *)
(* ================================================================== *)

(** Z_eff for Li 1s: Z - 0.3 = 3 - 0.3 = 2.7 = 27/10 (Slater's rules) *)
Definition li_zeff_1s : Q := 27#10.

(** Energy of each 1s electron: E_1s = -Z_eff^2/2 *)
Definition li_E_1s : Q := -(li_zeff_1s * li_zeff_1s / 2).

Lemma li_E_1s_value : li_E_1s == -(729#200).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part II: Lithium 2s orbital energy                                 *)
(* ================================================================== *)

(** Z_eff for Li 2s: Z - 0.85·2 = 3 - 1.7 = 1.3 = 13/10 (Slater's rules) *)
Definition li_zeff_2s : Q := 13#10.

(** Energy of 2s electron: E_2s = -Z_eff^2/(2·n^2) = -(13/10)^2/8 *)
Definition li_E_2s : Q := -(li_zeff_2s * li_zeff_2s / (2 * 4)).

Lemma li_E_2s_value : li_E_2s == -(169#800).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part III: Total energy and ionization                              *)
(* ================================================================== *)

(** Total Slater-rules energy: E_Li = 2·E_1s + E_2s *)
Definition li_E_total : Q := 2 * li_E_1s + li_E_2s.

Lemma li_E_total_value : li_E_total == -(6001#800).
Proof. vm_compute. reflexivity. Qed.

(** Koopmans' theorem: IE ≈ -ε_2s (first ionization = remove 2s electron) *)
Definition li_IE_Koopmans : Q := -(li_E_2s).

Lemma li_IE_Koopmans_value : li_IE_Koopmans == 169#800.
Proof. vm_compute. reflexivity. Qed.

(** NIST Li IE: 0.1981 Hartree = 1981/10000 *)
Definition nist_li_IE : Q := 1981#10000.

Lemma li_IE_Koopmans_positive : 0 < li_IE_Koopmans.
Proof.
  assert (H: li_IE_Koopmans == 169#800) by (vm_compute; reflexivity).
  rewrite H. lra.
Qed.

(** Our IE = 169/800 = 0.21125. NIST = 0.1981. Off by ~6.6%.
    Slater rules overestimate IE slightly. *)
Lemma li_IE_overestimates : nist_li_IE < li_IE_Koopmans.
Proof.
  assert (H: li_IE_Koopmans == 169#800) by (vm_compute; reflexivity).
  rewrite H. unfold nist_li_IE. lra.
Qed.

(* ================================================================== *)
(*  Part IV: Li+ (He-like, Z=3)                                       *)
(* ================================================================== *)

(** Li+ has 2 electrons with Z=3.
    Using Slater rules: Z_eff = 3 - 0.3 = 2.7 = 27/10
    E(Li+) = 2 · (-(27/10)^2/2) = -(729/100) *)
Definition li_plus_energy : Q := 2 * (-(li_zeff_1s * li_zeff_1s / 2)).

Lemma li_plus_energy_value : li_plus_energy == -(729#100).
Proof. vm_compute. reflexivity. Qed.

(** Delta-SCF ionization: IE = E(Li+) - E(Li) *)
Definition li_IE_delta : Q := li_plus_energy - li_E_total.

Lemma li_IE_delta_value : li_IE_delta == 169#800.
Proof. vm_compute. reflexivity. Qed.

(** Delta-SCF agrees with Koopmans for this Slater-rules model
    because screening for Li+ 1s is the same as for Li 1s. *)
Lemma li_koopmans_vs_nist_bound :
  li_IE_Koopmans - nist_li_IE < 15#1000.
Proof.
  assert (H: li_IE_Koopmans == 169#800) by (vm_compute; reflexivity).
  rewrite H. unfold nist_li_IE. lra.
Qed.

(** Delta-SCF and Koopmans agree exactly *)
Lemma li_delta_eq_koopmans : li_IE_delta == li_IE_Koopmans.
Proof. vm_compute. reflexivity. Qed.

(** Li total energy is negative (bound state) *)
Lemma li_E_total_negative : li_E_total < 0.
Proof.
  assert (H: li_E_total == -(6001#800)) by (vm_compute; reflexivity).
  rewrite H. lra.
Qed.

(** Li binding energy per electron: E_total/3 *)
Definition li_E_per_electron : Q := li_E_total / 3.

Lemma li_E_per_electron_value : li_E_per_electron == -(6001#2400).
Proof. vm_compute. reflexivity. Qed.
