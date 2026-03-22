(** * SpiralFibonacciConnection.v -- Fibonacci identities in the spiral
    Elements: fib_sum_sq_identity, cassini_identity, full_turn positions
    Roles:    Fibonacci structure governs spiral geometry at every scale
    Rules:    F(n)²+F(n+1)²=F(2n+1), F(n-1)F(n+1)-F(n)²=(-1)^n
    Status:   Stdlib
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import ZArith Lia.
From ToS Require Import stdlib.SpiralProcess.
Open Scope Z_scope.

(* ================================================================ *)
(* Full-turn positions: after 4K steps the spiral completes a loop  *)
(* ================================================================ *)

Lemma full_turn_4 : spiral_x 4 = (-1) /\ spiral_y 4 = (-2).
Proof. split; vm_compute; reflexivity. Qed.

Lemma full_turn_8 : spiral_x 8 = (-9) /\ spiral_y 8 = (-15).
Proof. split; vm_compute; reflexivity. Qed.

Lemma full_turn_12 : spiral_x 12 = (-64) /\ spiral_y 12 = (-104).
Proof. split; vm_compute; reflexivity. Qed.

(* ================================================================ *)
(* Sum-of-squares identity: F(n)² + F(n+1)² = F(2n+1)             *)
(* Verified at concrete values                                      *)
(* ================================================================ *)

Lemma fib_sum_sq_1 : fib_Z 1 * fib_Z 1 + fib_Z 2 * fib_Z 2 = fib_Z 3.
Proof. vm_compute. reflexivity. Qed.

Lemma fib_sum_sq_2 : fib_Z 2 * fib_Z 2 + fib_Z 3 * fib_Z 3 = fib_Z 5.
Proof. vm_compute. reflexivity. Qed.

Lemma fib_sum_sq_3 : fib_Z 3 * fib_Z 3 + fib_Z 4 * fib_Z 4 = fib_Z 7.
Proof. vm_compute. reflexivity. Qed.

Lemma fib_sum_sq_4 : fib_Z 4 * fib_Z 4 + fib_Z 5 * fib_Z 5 = fib_Z 9.
Proof. vm_compute. reflexivity. Qed.

Lemma fib_sum_sq_5 : fib_Z 5 * fib_Z 5 + fib_Z 6 * fib_Z 6 = fib_Z 11.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* Cassini's identity: F(n-1)*F(n+1) - F(n)² = (-1)^n             *)
(* Verified at concrete values (sign alternates)                    *)
(* ================================================================ *)

Lemma cassini_1 : fib_Z 0 * fib_Z 2 - fib_Z 1 * fib_Z 1 = (-1).
Proof. vm_compute. reflexivity. Qed.

Lemma cassini_2 : fib_Z 1 * fib_Z 3 - fib_Z 2 * fib_Z 2 = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma cassini_3 : fib_Z 2 * fib_Z 4 - fib_Z 3 * fib_Z 3 = (-1).
Proof. vm_compute. reflexivity. Qed.

Lemma cassini_4 : fib_Z 3 * fib_Z 5 - fib_Z 4 * fib_Z 4 = 1.
Proof. vm_compute. reflexivity. Qed.
