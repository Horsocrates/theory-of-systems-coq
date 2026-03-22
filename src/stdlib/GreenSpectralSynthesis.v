(** * GreenSpectralSynthesis.v -- Spectral analysis: recurrence at multiple K
    Elements: recurrence verification, full shift doubling, mode ratio
    Roles:    Cayley-Hamilton drives all propagation; spectrum determines dynamics
    Rules:    Recurrence G(K+2) = tr*G(K+1) - det*G(K) verified concretely
    Status:   Stdlib
    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.GreenFunction.
From ToS Require Import stdlib.GreenSpectral.

Open Scope Q_scope.

(* ================================================================== *)
(*  RECURRENCE AT HIGHER K VALUES                                      *)
(* ================================================================== *)

Lemma golden_recurrence_4 :
  green golden 0%nat 0%nat 6 == green golden 0%nat 0%nat 5 + green golden 0%nat 0%nat 4.
Proof. vm_compute. reflexivity. Qed.

Lemma golden_recurrence_01 :
  green golden 0%nat 1%nat 3 == green golden 0%nat 1%nat 2 + green golden 0%nat 1%nat 1.
Proof. vm_compute. reflexivity. Qed.

Lemma golden_recurrence_01_K3 :
  green golden 0%nat 1%nat 4 == green golden 0%nat 1%nat 3 + green golden 0%nat 1%nat 2.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  FULL SHIFT: G(K+2) = 2*G(K+1) (det=0 kills the G(K) term)         *)
(* ================================================================== *)

Lemma full_doubling_00_2 :
  green full_mat2 0%nat 0%nat 4 == 2 * green full_mat2 0%nat 0%nat 3.
Proof. vm_compute. reflexivity. Qed.

Lemma full_doubling_00_3 :
  green full_mat2 0%nat 0%nat 5 == 2 * green full_mat2 0%nat 0%nat 4.
Proof. vm_compute. reflexivity. Qed.

Lemma full_green_00_5 : green full_mat2 0%nat 0%nat 5 == 16.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  MODE RATIO: golden trace decays vs full trace doubles               *)
(* ================================================================== *)

(** Golden trace grows sub-exponentially (Fibonacci-like) *)
Lemma golden_trace_5 : trace_process golden 5 == 11.
Proof. vm_compute. reflexivity. Qed.

(** Full trace doubles every step *)
Lemma full_trace_3 : trace_process full_mat2 3 == 8.
Proof. vm_compute. reflexivity. Qed.

Lemma full_trace_4 : trace_process full_mat2 4 == 16.
Proof. vm_compute. reflexivity. Qed.

(** Trace recurrence: trace(K+2) = tr*trace(K+1) - det*trace(K) *)
Lemma golden_trace_recurrence :
  trace_process golden 5 == trace_process golden 4 + trace_process golden 3.
Proof. vm_compute. reflexivity. Qed.

Lemma full_trace_doubling :
  trace_process full_mat2 4 == 2 * trace_process full_mat2 3.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

Theorem spectral_synthesis :
  (* Golden recurrence persists at K=4 *)
  green golden 0%nat 0%nat 6 == green golden 0%nat 0%nat 5 + green golden 0%nat 0%nat 4 /\
  (* Full shift doubles: G(5) = 16 *)
  green full_mat2 0%nat 0%nat 5 == 16 /\
  (* Full trace = 2^K: trace(4) = 16 *)
  trace_process full_mat2 4 == 16 /\
  (* Golden trace = Lucas: trace(5) = 11 *)
  trace_process golden 5 == 11.
Proof.
  split; [exact golden_recurrence_4|].
  split; [exact full_green_00_5|].
  split; [exact full_trace_4|exact golden_trace_5].
Qed.
