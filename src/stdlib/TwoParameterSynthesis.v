(** * TwoParameterSynthesis.v — Synthesis of Two-Parameter Screening + Variational
    Elements: Two-parameter Z_eff, variational convergence, unified verification
    Roles:    Combine screening model with energy convergence for full pipeline check
    Rules:    Constraints satisfied, energies converge, Z_eff recovers bare charge
    Status:   Stdlib
    STATUS: 8 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
Require Import ToS.stdlib.PadeApprox.
Require Import ToS.stdlib.TwoParameterScreening.
Require Import ToS.stdlib.VariationalFit.

Open Scope Q_scope.

(* ================================================================== *)
(*  SYNTHESIS GATE 1: He constraint + bare charge recovery             *)
(* ================================================================== *)

Theorem he_model_consistent :
  he_c1 + he_c2 == 1 /\
  Z_eff_two he_c1 he_c2 he_r1 he_r2 10 0 == 2.
Proof.
  split.
  - exact he_constraint.
  - exact he_Z_eff_site0.
Qed.

(* ================================================================== *)
(*  SYNTHESIS GATE 2: Li constraint + bare charge recovery             *)
(* ================================================================== *)

Theorem li_model_consistent :
  li_c1 + li_c2 == 2 /\
  Z_eff_two li_c1 li_c2 li_r1 li_r2 10 0 == 3.
Proof.
  split.
  - exact li_constraint.
  - exact li_Z_eff_site0.
Qed.

(* ================================================================== *)
(*  SYNTHESIS GATE 3: NIST deltas ordered                              *)
(* ================================================================== *)

Theorem nist_ordering : nist_he_delta < nist_li_delta.
Proof. exact li_delta_larger. Qed.

(* ================================================================== *)
(*  SYNTHESIS GATE 4: Variational convergence for both atoms           *)
(* ================================================================== *)

Theorem variational_convergence :
  variational_energy nist_he_delta 20 < variational_energy nist_he_delta 10 /\
  variational_energy nist_li_delta 20 < variational_energy nist_li_delta 10.
Proof.
  split.
  - exact var_energy_converges_he.
  - unfold variational_energy, nist_li_delta. vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  SYNTHESIS GATE 5: All parameters positive                          *)
(* ================================================================== *)

Theorem he_parameters_valid :
  0 < he_c1 /\ 0 < he_c2 /\ 0 < he_r1 /\ 0 < he_r2.
Proof.
  split. { exact he_c1_positive. }
  split. { exact he_c2_positive. }
  split. { exact he_r1_positive. }
  exact he_r2_positive.
Qed.

Theorem li_parameters_valid :
  0 < li_c1 /\ 0 < li_c2 /\ 0 < li_r1 /\ 0 < li_r2.
Proof.
  split. { exact li_c1_positive. }
  split. { exact li_c2_positive. }
  split. { exact li_r1_positive. }
  exact li_r2_positive.
Qed.

(* ================================================================== *)
(*  GRAND SYNTHESIS: Full two-parameter model verified                 *)
(* ================================================================== *)

Theorem two_parameter_grand_synthesis :
  he_c1 + he_c2 == 1 /\
  li_c1 + li_c2 == 2 /\
  nist_he_delta < nist_li_delta /\
  variational_energy nist_he_delta 20 < variational_energy nist_he_delta 10.
Proof.
  split. { exact he_constraint. }
  split. { exact li_constraint. }
  split. { exact li_delta_larger. }
  exact var_energy_converges_he.
Qed.

(* ================================================================== *)
(*  PADE FOUNDATION: approximant is well-behaved                       *)
(* ================================================================== *)

Theorem pade_foundation :
  pade22 0 == 1 /\ 0 < pade22 (1#2).
Proof.
  split.
  - exact pade_at_0.
  - exact pade_positive_half.
Qed.
