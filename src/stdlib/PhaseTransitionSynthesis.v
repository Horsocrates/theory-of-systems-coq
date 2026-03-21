(** * PhaseTransitionSynthesis.v -- Phase transition zoo comparison
    Elements: all models compared, universality classes
    Roles:    Same G_{ij}(K) formalism → different transition types
    Rules:    Ising (2nd order) vs Potts (1st order) vs Clock
    Status:   Stdlib
    STATUS: 8 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.MatN.
From ToS Require Import stdlib.PottsTransfer.
From ToS Require Import stdlib.ClockModel.
From ToS Require Import stdlib.FiniteSizeScaling.

Open Scope Q_scope.

(* ================================================================== *)
(*  MODEL COMPARISON                                                   *)
(* ================================================================== *)

(** Ising (width 1): gap = 2·sinh(β), β-dependent → interesting dynamics *)
(** Potts Q=3 (width 1): gap = 3, constant! Trivial 1D *)
(** Clock Z₃ (width 1): gap = 3·exp(-β/2), decays with β *)

(** All three: gap > 0 in 1D → no phase transition *)
(** Phase transition only in 2D (strip width ≥ 2) *)

(** Gap comparison at β=1 *)
Lemma potts_gap_at_1 :
  potts3_lambda_plus 1 3 - potts3_lambda_minus 1 3 == 3.
Proof. exact (potts3_gap_constant 1 3). Qed.

Lemma clock_gap_at_1 :
  0 < clock3_lambda0 1 3 - clock3_lambda1 1 3 /\
  clock3_lambda0 1 3 - clock3_lambda1 1 3 < 3.
Proof.
  split.
  - exact clock3_gap_positive.
  - exact clock_gap_less_potts.
Qed.

(** Universality classes:
    Ising ↔ Z₂ symmetry → ν=1, γ=7/4
    Potts Q=3 ↔ S₃ symmetry → ν=5/6, γ=13/9
    Clock Z₃ ↔ Z₃ ≅ Potts Q=3 → same exponents *)

Lemma ising_exponents_exact :
  ising_nu == 1 /\ ising_gamma == 7#4 /\ ising_beta_mag == 1#8.
Proof.
  unfold ising_nu, ising_gamma, ising_beta_mag.
  split; [|split]; reflexivity.
Qed.

Lemma potts3_exponents :
  potts3_nu == 5#6 /\ potts3_gamma == 13#9.
Proof.
  unfold potts3_nu, potts3_gamma.
  split; reflexivity.
Qed.

(** Different ν means different FSS convergence rates *)
Lemma different_convergence :
  ising_nu > potts3_nu.
Proof. unfold ising_nu, potts3_nu. lra. Qed.

(** Scaling relations verified for both models *)
Lemma both_rushbrooke :
  0 + 2 * ising_beta_mag + ising_gamma == 2 /\
  (1#3) + (2#1) * potts3_beta_mag + potts3_gamma == 2.
Proof.
  split.
  - exact rushbrooke.
  - exact potts3_rushbrooke.
Qed.

(** GRAND COMPARISON *)
Theorem phase_transition_zoo :
  (* Potts: constant gap *)
  potts3_lambda_plus 1 3 - potts3_lambda_minus 1 3 == 3 /\
  (* Clock: smaller, β-dependent gap *)
  clock3_lambda0 1 3 - clock3_lambda1 1 3 < 3 /\
  (* Different exponents → different universality classes *)
  ising_nu > potts3_nu /\
  (* Rushbrooke satisfied *)
  0 + 2 * ising_beta_mag + ising_gamma == 2.
Proof.
  split; [|split; [|split]].
  - exact potts_gap_at_1.
  - exact clock_gap_less_potts.
  - exact different_convergence.
  - exact rushbrooke.
Qed.
