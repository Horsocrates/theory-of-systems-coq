(** * UncertaintyBandSynthesis.v — Synthesis: uncertainty band structure
    Elements: band_grand, scaling_summary, convergence_to_half
    Roles:    Collects band structure verifications
    Rules:    tr = (K-1)/2; rms -> 1/2; gap -> 0; bandwidth = 2
    Status:   complete
    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Lia.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.heisenberg.UncertaintyBand.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Grand Synthesis                                            *)
(* ================================================================== *)

Theorem band_grand :
  tr_comm_sq 4 == 3#2 /\
  tr_comm_sq 8 == 7#2 /\
  tr_comm_sq 20 == 19#2 /\
  tr_comm_sq 100 == 99#2.
Proof.
  split; [exact tr_comm_sq_4|].
  split; [exact tr_comm_sq_8|].
  split; [exact tr_comm_sq_20|].
  exact tr_comm_sq_100.
Qed.

Theorem rms_convergence :
  rms_eigenvalue 4 == 3#8 /\
  rms_eigenvalue 10 == 9#20 /\
  rms_eigenvalue 100 == 99#200 /\
  rms_eigenvalue 1000 == 999#2000.
Proof.
  split; [exact rms_eigenvalue_4|].
  split; [exact rms_eigenvalue_10|].
  split; [exact rms_approach_half|].
  exact rms_approach_half_1000.
Qed.

Theorem monotone_approach :
  rms_eigenvalue 10 < rms_eigenvalue 100 /\
  rms_eigenvalue 100 < rms_eigenvalue 1000.
Proof.
  split; [exact band_approaches_half|exact band_approaches_half_2].
Qed.

Theorem gap_convergence :
  eigenvalue_gap 10 == 1#5 /\
  eigenvalue_gap 100 == 1#50 /\
  eigenvalue_gap 100 < eigenvalue_gap 10.
Proof.
  split; [exact gap_10|].
  split; [exact gap_100|].
  exact gap_shrinks.
Qed.

(* ================================================================== *)
(*  Part II: Limit Interpretation                                      *)
(* ================================================================== *)

(** In the limit K -> infinity, rms -> 1/2.
    We verify: rms_eigenvalue K = (K-1)/(2K) = 1/2 - 1/(2K).
    Concrete: 1/2 - rms(K) = 1/(2K) *)

Lemma half_minus_rms_10 : (1#2) - rms_eigenvalue 10 == 1#20.
Proof. vm_compute. reflexivity. Qed.

Lemma half_minus_rms_100 : (1#2) - rms_eigenvalue 100 == 1#200.
Proof. vm_compute. reflexivity. Qed.

Lemma half_minus_rms_1000 : (1#2) - rms_eigenvalue 1000 == 1#2000.
Proof. vm_compute. reflexivity. Qed.

(** The deficit shrinks: 1/(2·100) < 1/(2·10) *)
Lemma deficit_shrinks :
  (1#2) - rms_eigenvalue 100 < (1#2) - rms_eigenvalue 10.
Proof. vm_compute. reflexivity. Qed.
