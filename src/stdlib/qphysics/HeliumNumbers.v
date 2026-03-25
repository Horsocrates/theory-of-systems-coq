(** * HeliumNumbers.v -- Verified helium atom numbers in exact Q
    Elements: E_HF_He, J_He, T_He, ionization_energy_He, nist_comparison
    Roles:    Helium HF energy components and ionization as exact Q
    Rules:    IE = E(He+) - E(He); NIST comparison via Q bounds
    Status:   complete
    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Lia Lqa.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Helium HF energy components (replicated for independence)  *)
(* ================================================================== *)

(** Optimal exponent alpha = 27/16 (Slater's rules, Z_eff) *)
Definition he_alpha : Q := 27#16.

(** Nuclear charge *)
Definition he_Z_local : Q := 2.

(** Kinetic energy per electron: T = alpha^2/2 *)
Definition he_T : Q := he_alpha * he_alpha / 2.

(** Coulomb repulsion: J = 5*alpha/8 *)
Definition he_J : Q := 5 * he_alpha / 8.

(** Nuclear attraction per electron: V = -Z*alpha *)
Definition he_V : Q := -(he_Z_local) * he_alpha.

(** Total HF energy: E_HF = 2T + 2V + J *)
Definition he_E_HF_local : Q := 2 * he_T + 2 * he_V + he_J.

(* ================================================================== *)
(*  Part II: Verified component values                                 *)
(* ================================================================== *)

Lemma he_T_exact : he_T == 729#512.
Proof. vm_compute. reflexivity. Qed.

Lemma he_J_exact : he_J == 135#128.
Proof. vm_compute. reflexivity. Qed.

Lemma he_V_exact : he_V == -(27#8).
Proof. vm_compute. reflexivity. Qed.

Lemma he_E_HF_exact : he_E_HF_local == -(729#256).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part III: NIST comparison                                          *)
(* ================================================================== *)

(** NIST total energy for He: -2.9037 Hartree (experimental).
    Rational approximation: 29037/10000 *)
Definition nist_he_total : Q := 29037#10000.

(** Our HF value: 729/256 ≈ 2.8477.
    HF underestimates binding (less negative than experiment). *)
Lemma hf_underestimates_binding : 729#256 < nist_he_total.
Proof. unfold nist_he_total. lra. Qed.

(** Error: nist - HF = 29037/10000 - 729/256.
    = 29037·256/(10000·256) - 729·10000/(256·10000)
    = 7433472/2560000 - 7290000/2560000 = 143472/2560000
    = 8967/160000 *)
Definition he_hf_error : Q := nist_he_total - (729#256).

Lemma he_hf_error_value : he_hf_error == 8967#160000.
Proof. vm_compute. reflexivity. Qed.

(** Error is about 1.9% of NIST total.
    8967/160000 ≈ 0.056, which is < 1/10. *)
Lemma he_hf_error_small : he_hf_error < 1#10.
Proof.
  assert (H1: he_hf_error == 8967#160000) by (vm_compute; reflexivity).
  rewrite H1. lra.
Qed.

(* ================================================================== *)
(*  Part IV: Ionization energy                                         *)
(* ================================================================== *)

(** He+ is hydrogenic with Z=2: E(He+) = -Z²/2 = -2 Hartree *)
Definition he_plus_energy : Q := -(2).

(** Ionization energy: IE = E(He+) - E(He_neutral)
    = -2 - (-729/256) = -2 + 729/256 = (-512+729)/256 = 217/256 *)
Definition he_IE_HF : Q := he_plus_energy - (-(729#256)).

Lemma he_IE_HF_value : he_IE_HF == 217#256.
Proof. vm_compute. reflexivity. Qed.

Lemma he_IE_HF_positive : 0 < he_IE_HF.
Proof.
  assert (H: he_IE_HF == 217#256) by (vm_compute; reflexivity).
  rewrite H. lra.
Qed.

(** NIST IE for He: 0.9036 Hartree = 9036/10000 *)
Definition nist_he_IE : Q := 9036#10000.

(** HF underestimates ionization energy *)
Lemma hf_underestimates_IE : he_IE_HF < nist_he_IE.
Proof.
  assert (H: he_IE_HF == 217#256) by (vm_compute; reflexivity).
  rewrite H. unfold nist_he_IE. lra.
Qed.

(** IE error: ~6.2%.  217/256 ≈ 0.8477.
    Error = 9036/10000 - 217/256 = (9036·256 - 217·10000)/(10000·256)
    = (2313216 - 2170000)/2560000 = 143216/2560000 = 8951/160000
    Relative: 8951/160000 / (9036/10000) ≈ 6.2% *)
Definition he_IE_error : Q := nist_he_IE - he_IE_HF.

Lemma he_IE_error_positive : 0 < he_IE_error.
Proof.
  unfold he_IE_error.
  assert (H1: he_IE_HF == 217#256) by (vm_compute; reflexivity).
  assert (H2: nist_he_IE == 9036#10000) by reflexivity.
  rewrite H1. unfold nist_he_IE. lra.
Qed.

(** IE error < 1/10 Hartree (actual ~0.056) *)
Lemma he_IE_error_small : he_IE_error < 1#10.
Proof.
  unfold he_IE_error.
  assert (H1: he_IE_HF == 217#256) by (vm_compute; reflexivity).
  rewrite H1. unfold nist_he_IE. lra.
Qed.

(** He+ energy is exact (single electron, Z=2) *)
Lemma he_plus_exact : he_plus_energy == -(2).
Proof. vm_compute. reflexivity. Qed.

(** He binding energy: E_HF < E(He+) (neutral more tightly bound) *)
Lemma he_neutral_more_bound : he_E_HF_local < he_plus_energy.
Proof.
  assert (H1: he_E_HF_local == -(729#256)) by (vm_compute; reflexivity).
  assert (H2: he_plus_energy == -(2)) by (vm_compute; reflexivity).
  rewrite H1, H2. lra.
Qed.

(** HF error is small: 8967/160000 < 6/100 *)
Lemma he_hf_error_pct : he_hf_error < 6#100.
Proof.
  assert (H: he_hf_error == 8967#160000) by (vm_compute; reflexivity).
  rewrite H. lra.
Qed.
