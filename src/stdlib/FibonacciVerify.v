(** * FibonacciVerify.v -- Verify Fibonacci/Lucas against OEIS
    Elements: OEIS A000045 (Fibonacci), A000032 (Lucas), Cassini
    Roles:    G_{00}(K) = F(K+1), trace(K) = L(K), all verified
    Rules:    Every identity = matrix identity for golden mean matrix
    Status:   Stdlib
    STATUS: 8 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.GreenFunction.
From ToS Require Import stdlib.FibonacciGreen.

Open Scope Q_scope.

(* ================================================================== *)
(*  OEIS VERIFICATION                                                  *)
(* ================================================================== *)

(** OEIS A000045 (Fibonacci): 0, 1, 1, 2, 3, 5, 8, 13, 21, 34, ...
    Our G_{00}(K) = F(K+1):
    G_{00}(0)=1=F(1), G_{00}(1)=1=F(2), G_{00}(2)=2=F(3),
    G_{00}(3)=3=F(4), G_{00}(4)=5=F(5), G_{00}(5)=8=F(6), G_{00}(6)=13=F(7) *)

(** OEIS A000032 (Lucas): 2, 1, 3, 4, 7, 11, 18, 29, ...
    Our trace(K) = L(K):
    trace(0)=2=L(0), trace(1)=1=L(1), trace(2)=3=L(2),
    trace(3)=4=L(3), trace(4)=7=L(4) *)

(** Extended trace = Lucas *)
Lemma trace_golden_5 : trace_process golden 5 == 11.
Proof. vm_compute. reflexivity. Qed.

Lemma trace_golden_6 : trace_process golden 6 == 18.
Proof. vm_compute. reflexivity. Qed.

(** Lucas recurrence: L(K+2) = L(K+1) + L(K) *)
Lemma lucas_recurrence_4 :
  trace_process golden 4 == trace_process golden 3 + trace_process golden 2.
Proof. vm_compute. reflexivity. Qed.

Lemma lucas_recurrence_5 :
  trace_process golden 5 == trace_process golden 4 + trace_process golden 3.
Proof. vm_compute. reflexivity. Qed.

(** Fibonacci-Lucas relation: L(K) = F(K+1) + F(K-1) *)
(** trace(K) = G_{00}(K) + G_{11}(K) *)
Lemma fib_lucas_relation_3 :
  trace_process golden 3 ==
  green golden 0%nat 0%nat 3 + green golden 1%nat 1%nat 3.
Proof. vm_compute. reflexivity. Qed.

(** Cassini sign alternation *)
Lemma cassini_sign_alternates :
  green_det 1 == -(1) /\ green_det 2 == 1 /\
  green_det 3 == -(1) /\ green_det 4 == 1.
Proof.
  split; [|split; [|split]].
  - exact cassini_1.
  - exact cassini_2.
  - exact cassini_3.
  - exact cassini_4.
Qed.

(** Symmetry of golden matrix: G_{01} = G_{10} *)
Lemma golden_symmetric_2 :
  green golden 0%nat 1%nat 2 == green golden 1%nat 0%nat 2.
Proof. vm_compute. reflexivity. Qed.

(** SYNTHESIS *)
Theorem fibonacci_verify_synthesis :
  (* F(7) = 13 *)
  green golden 0%nat 0%nat 6 == 13 /\
  (* L(5) = 11, L(6) = 18 *)
  trace_process golden 5 == 11 /\
  trace_process golden 6 == 18 /\
  (* Cassini alternates *)
  green_det 3 == -(1) /\ green_det 4 == 1.
Proof.
  split; [|split; [|split; [|split]]].
  - exact green_golden_00_6.
  - exact trace_golden_5.
  - exact trace_golden_6.
  - exact cassini_3.
  - exact cassini_4.
Qed.
