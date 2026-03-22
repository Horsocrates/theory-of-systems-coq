(** * SpectralFlowTraces.v — Trace Computations for Box Path Graphs
    Elements: tridiag_box, box matrices H2/H3/H4/H5, trace powers
    Roles:    Spectral invariants from adjacency matrix traces
    Rules:    tr(H^1)=0, tr(H^2)=2(K-1), tr(H^4)=6K-10, bipartite odd vanishing
    Status:   Stdlib
    STATUS: 18 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs List.
From ToS Require Import stdlib.MatN.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================== *)
(*  TRIDIAG BOX: simple adjacency for path graph P_K                  *)
(* ================================================================== *)

Definition tridiag_box (K : nat) : MatN := fun i j =>
  if andb (Nat.ltb i K) (Nat.ltb j K) then
    if Nat.eqb (S i) j then 1
    else if Nat.eqb i (S j) then 1
    else 0
  else 0.

(* ================================================================== *)
(*  H2 = [[0,1],[1,0]]: 2×2 path graph                                *)
(* ================================================================== *)

Lemma H2_trace : traceN 2 (tridiag_box 2) == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma H2_trace_sq : traceN 2 (matN_pow 2 (tridiag_box 2) 2) == 2.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  H3 = [[0,1,0],[1,0,1],[0,1,0]]: 3-vertex path                     *)
(* ================================================================== *)

Lemma H3_trace : traceN 3 (tridiag_box 3) == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma H3_trace_sq : traceN 3 (matN_pow 3 (tridiag_box 3) 2) == 4.
Proof. vm_compute. reflexivity. Qed.

Lemma H3_trace_cube : traceN 3 (matN_pow 3 (tridiag_box 3) 3) == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma H3_trace_fourth : traceN 3 (matN_pow 3 (tridiag_box 3) 4) == 8.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  H4: 4-vertex path                                                  *)
(* ================================================================== *)

Lemma H4_trace : traceN 4 (tridiag_box 4) == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma H4_trace_sq : traceN 4 (matN_pow 4 (tridiag_box 4) 2) == 6.
Proof. vm_compute. reflexivity. Qed.

Lemma H4_trace_fourth : traceN 4 (matN_pow 4 (tridiag_box 4) 4) == 14.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  H5: 5-vertex path                                                  *)
(* ================================================================== *)

Lemma H5_trace_sq : traceN 5 (matN_pow 5 (tridiag_box 5) 2) == 8.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  FORMULA: tr(H^2_K) = 2(K-1) for path graph P_K                    *)
(* ================================================================== *)

Lemma trace_sq_formula_K2 : traceN 2 (matN_pow 2 (tridiag_box 2) 2) == 2 * (2 - 1).
Proof. vm_compute. reflexivity. Qed.

Lemma trace_sq_formula_K3 : traceN 3 (matN_pow 3 (tridiag_box 3) 2) == 2 * (3 - 1).
Proof. vm_compute. reflexivity. Qed.

Lemma trace_sq_formula_K5 : traceN 5 (matN_pow 5 (tridiag_box 5) 2) == 2 * (5 - 1).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  FORMULA: tr(H^4_K) = 6K-10 for K >= 3                             *)
(* ================================================================== *)

Lemma trace_fourth_formula_K3 :
  traceN 3 (matN_pow 3 (tridiag_box 3) 4) == 6 * 3 - 10.
Proof. vm_compute. reflexivity. Qed.

Lemma trace_fourth_formula_K5 :
  traceN 5 (matN_pow 5 (tridiag_box 5) 4) == 6 * 5 - 10.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  BIPARTITE: odd power traces vanish                                 *)
(* ================================================================== *)

Lemma bipartite_H2 : traceN 2 (matN_pow 2 (tridiag_box 2) 3) == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma bipartite_H3 : traceN 3 (matN_pow 3 (tridiag_box 3) 3) == 0.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

Theorem spectral_flow_traces_synthesis :
  traceN 2 (tridiag_box 2) == 0 /\
  traceN 2 (matN_pow 2 (tridiag_box 2) 2) == 2 /\
  traceN 3 (matN_pow 3 (tridiag_box 3) 4) == 8 /\
  traceN 3 (matN_pow 3 (tridiag_box 3) 3) == 0.
Proof.
  split; [exact H2_trace|].
  split; [exact H2_trace_sq|].
  split; [exact H3_trace_fourth|].
  exact H3_trace_cube.
Qed.
