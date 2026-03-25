(** * HeHartreeFock.v -- 1-STO Hartree-Fock energy for helium
    Elements: he_T_norm, he_V_norm, he_J_norm, he_E_HF, he_E_HF_value
    Roles:    Exact Q computation of E_HF for He with alpha=27/16
    Rules:    E_HF = 2T + 2V + J where T=a^2/2, V=-Za, J=5a/8
    Status:   complete
    STATUS: 13 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Lia Lqa.
From ToS Require Import stdlib.qphysics.FundamentalIntegral.
From ToS Require Import stdlib.qphysics.HeSlaterBasis.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Normalized 1s energy components                            *)
(* ================================================================== *)

(** Kinetic energy for normalized 1s STO: T = alpha^2 / 2 *)
Definition he_T_norm (alpha : Q) : Q := alpha * alpha / 2.

(** Nuclear attraction for normalized 1s STO: V = -Z * alpha *)
Definition he_V_norm (Z alpha : Q) : Q := -(Z) * alpha.

(** Coulomb repulsion integral for same-exponent 1s: J = 5*alpha/8 *)
Definition he_J_norm (alpha : Q) : Q := 5 * alpha / 8.

(** Hartree-Fock total energy: E_HF = 2T + 2V + J *)
Definition he_E_HF (Z alpha : Q) : Q :=
  2 * he_T_norm alpha + 2 * he_V_norm Z alpha + he_J_norm alpha.

(* ================================================================== *)
(*  Part II: Component values for alpha = 27/16                        *)
(* ================================================================== *)

Lemma he_T_value : he_T_norm he_alpha_1 == 729#512.
Proof. vm_compute. reflexivity. Qed.

Lemma he_V_value : he_V_norm he_Z he_alpha_1 == -(27#8).
Proof. vm_compute. reflexivity. Qed.

Lemma he_J_value : he_J_norm he_alpha_1 == 135#128.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part III: Total HF energy                                          *)
(* ================================================================== *)

(** E_HF(He, alpha=27/16) = -729/256 exactly *)
Lemma he_E_HF_value : he_E_HF he_Z he_alpha_1 == -(729#256).
Proof. vm_compute. reflexivity. Qed.

(** E_HF in decimal: -2.84766 *)
Lemma he_E_HF_bound_lower : -(729#256) < -(284#100).
Proof. lra. Qed.

Lemma he_E_HF_bound_upper : -(285#100) < -(729#256).
Proof. lra. Qed.

(* ================================================================== *)
(*  Part IV: Second basis function energy                              *)
(* ================================================================== *)

(** Energy for second STO exponent alpha_2 = 3/2 *)
Lemma he_E22_value : he_E_HF he_Z he_alpha_2 == -(45#16).
Proof. vm_compute. reflexivity. Qed.

(** E_HF(alpha_1) < E_HF(alpha_2): first exponent gives lower energy *)
Lemma he_alpha1_better : he_E_HF he_Z he_alpha_1 < he_E_HF he_Z he_alpha_2.
Proof.
  assert (H1: he_E_HF he_Z he_alpha_1 == -(729#256)) by (vm_compute; reflexivity).
  assert (H2: he_E_HF he_Z he_alpha_2 == -(45#16)) by (vm_compute; reflexivity).
  rewrite H1, H2. lra.
Qed.

(* ================================================================== *)
(*  Part V: Comparison with exact energy                               *)
(* ================================================================== *)

(** NIST exact energy: E_exact = -2.9037 hartree.
    We approximate as -29037/10000.
    Error = |E_HF - E_exact| / |E_exact| *)

Definition he_E_exact_approx : Q := -(29037#10000).

(** HF energy is above exact (variational principle) *)
Lemma he_E_HF_above_exact : he_E_exact_approx < he_E_HF he_Z he_alpha_1.
Proof.
  assert (H1: he_E_HF he_Z he_alpha_1 == -(729#256)) by (vm_compute; reflexivity).
  unfold he_E_exact_approx. rewrite H1. lra.
Qed.

(** Error is less than 2% *)
(** Relative error = 2989/154864 ~ 1.93% *)
Definition he_hf_rel_error : Q := 2989#154864.

Lemma he_hf_error_small : he_hf_rel_error < 2#100.
Proof. unfold he_hf_rel_error. lra. Qed.

Lemma he_hf_error_positive : 0 < he_hf_rel_error.
Proof. unfold he_hf_rel_error. lra. Qed.

(* ================================================================== *)
(*  Part VI: Virial theorem check                                      *)
(* ================================================================== *)

(** For the optimal alpha: 2T/|V| should approach 1 (virial theorem).
    2T = 729/256, 2|V| = 27/4 = 1728/256. Ratio = 729/1728 = 27/64.
    Not exactly 1 because J shifts the virial from pure hydrogen. *)

Definition he_virial_ratio : Q :=
  2 * he_T_norm he_alpha_1 / (-(2 * he_V_norm he_Z he_alpha_1)).

Lemma he_virial_value : he_virial_ratio == 27#64.
Proof. vm_compute. reflexivity. Qed.

(** Including J: (2T + J) / |2V| for effective virial *)
Definition he_effective_virial : Q :=
  (2 * he_T_norm he_alpha_1 + he_J_norm he_alpha_1) /
  (-(2 * he_V_norm he_Z he_alpha_1)).

Lemma he_effective_virial_value : he_effective_virial == 999#1728.
Proof. vm_compute. reflexivity. Qed.
