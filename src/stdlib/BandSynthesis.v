(** * BandSynthesis.v — Grand Band Theory Synthesis
    Elements: Periodic tridiag, band gap, ring vs chain
    Roles:    Unify band structure computations
    Rules:    Ring > chain connectivity; gap = 4|delta|
    Status:   Stdlib
    STATUS: 5 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.PeriodicTridiag.
From ToS Require Import stdlib.BandGap.
Open Scope Q_scope.

(* ================================================================== *)
(*  BAND STRUCTURE GRAND SYNTHESIS                                     *)
(* ================================================================== *)

Lemma ring_vs_chain_trace :
  chain_trace_sq_3 < ring_trace_sq_3.
Proof. exact ring_more_connected. Qed.

Lemma gap_closes_at_zero : band_gap 0 == 0.
Proof. exact gap_zero. Qed.

Lemma gap_opens_with_perturbation : band_gap (1#4) == 1.
Proof. exact gap_quarter. Qed.

Lemma periodic_adds_wraparound :
  ring_entry 3%nat O (S (S O)) == 1 /\
  chain_entry 3%nat O (S (S O)) == 0.
Proof.
  split; [exact ring_3_wrap|exact chain_3_no_wrap].
Qed.

Theorem band_grand_synthesis :
  (* Ring has more spectral weight *)
  chain_trace_sq_3 < ring_trace_sq_3 /\
  (* Gap vanishes at zero perturbation *)
  band_gap 0 == 0 /\
  (* Gap opens with nonzero perturbation *)
  band_gap (1#4) == 1 /\
  (* Ring adds periodic bond *)
  ring_entry 3%nat O (S (S O)) == 1.
Proof.
  split; [exact ring_vs_chain_trace|].
  split; [exact gap_closes_at_zero|].
  split; [exact gap_opens_with_perturbation|].
  exact ring_3_wrap.
Qed.
