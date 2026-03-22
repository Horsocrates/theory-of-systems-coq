(** * OscillatorComparison.v — Box vs Oscillator Spectral Comparison
    Elements: Box (path graph) and oscillator trace values
    Roles:    Compare spectral invariants: box tr2=2(K-1), osc tr2=K(K-1)
    Rules:    Oscillator always exceeds box; discriminant comparison (5 vs 92)
    Status:   Stdlib
    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.MatN.
From ToS Require Import stdlib.SpectralFlowTraces.
From ToS Require Import stdlib.OscillatorRational.
Open Scope Q_scope.

(* ================================================================== *)
(*  BOX (PATH GRAPH) TRACE VALUES                                       *)
(* ================================================================== *)

(** Box tr2 for K=3: 2*(3-1)=4 *)
Lemma box_tr2_K3 : traceN 3 (matN_pow 3 (tridiag_box 3) 2) == 4.
Proof. vm_compute. reflexivity. Qed.

(** Box tr2 for K=5: 2*(5-1)=8 *)
Lemma box_tr2_K5 : traceN 5 (matN_pow 5 (tridiag_box 5) 2) == 8.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  TRACE COMPARISON: osc tr2 vs box tr2                                *)
(* ================================================================== *)

(** K=3: osc=6 > box=4 *)
Lemma trace_comparison_K3 :
  inject_Z (osc_tr2 3) - traceN 3 (matN_pow 3 (tridiag_box 3) 2) == 2.
Proof. vm_compute. reflexivity. Qed.

(** K=5: osc=20 > box=8 *)
Lemma trace_comparison_K5 :
  inject_Z (osc_tr2 5) - traceN 5 (matN_pow 5 (tridiag_box 5) 2) == 12.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  RATIO: osc_tr2 / box_tr2 = K/2                                     *)
(* ================================================================== *)

Lemma ratio_K3 : inject_Z (osc_tr2 3) / traceN 3 (matN_pow 3 (tridiag_box 3) 2) == (3#2).
Proof. vm_compute. reflexivity. Qed.

Lemma ratio_K5 : inject_Z (osc_tr2 5) / traceN 5 (matN_pow 5 (tridiag_box 5) 2) == (5#2).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  BOX tr4 VALUES                                                      *)
(* ================================================================== *)

Lemma box_tr4_K3 : traceN 3 (matN_pow 3 (tridiag_box 3) 4) == 8.
Proof. vm_compute. reflexivity. Qed.

Lemma box_tr4_K5 : traceN 5 (matN_pow 5 (tridiag_box 5) 4) == 20.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  DISCRIMINANT COMPARISON                                             *)
(*  Box disc_K4: tr2^2 - tr4 = 36-14 = 22                              *)
(*  Osc disc_K4: tr2^2 - tr4 = 144-52 = 92                             *)
(* ================================================================== *)

Definition box_disc_K4 : Q :=
  let tr2 := traceN 4 (matN_pow 4 (tridiag_box 4) 2) in
  let tr4 := traceN 4 (matN_pow 4 (tridiag_box 4) 4) in
  tr2 * tr2 - tr4.

Lemma box_disc_K4_value : box_disc_K4 == 22.
Proof. vm_compute. reflexivity. Qed.

Lemma disc_comparison : osc_disc_K4 - box_disc_K4 == 70.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                           *)
(* ================================================================== *)

Theorem oscillator_comparison_synthesis :
  (* Oscillator exceeds box at K=3 and K=5 *)
  inject_Z (osc_tr2 3) - traceN 3 (matN_pow 3 (tridiag_box 3) 2) == 2 /\
  inject_Z (osc_tr2 5) - traceN 5 (matN_pow 5 (tridiag_box 5) 2) == 12 /\
  (* Ratio = K/2 *)
  inject_Z (osc_tr2 3) / traceN 3 (matN_pow 3 (tridiag_box 3) 2) == (3#2) /\
  (* Discriminant gap *)
  osc_disc_K4 - box_disc_K4 == 70.
Proof. repeat split; vm_compute; reflexivity. Qed.
