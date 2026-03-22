(** * SpiralProcess.v -- Fibonacci spiral as discrete process on Z²
    Elements: fib_Z, spiral_dx, spiral_dy, spiral_x, spiral_y, spiral_r_sq
    Roles:    Spiral traces Fibonacci-sized steps cycling through 4 directions
    Rules:    Step K has length fib_Z(K), direction cycles with period 4
    Status:   Stdlib
    STATUS: 25 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

(* === Standard Fibonacci on Z === *)

Fixpoint fib_Z (n : nat) : Z :=
  match n with
  | O => 0
  | S O => 1
  | S (S m as p) => fib_Z p + fib_Z m
  end.

(* === Direction vectors with period 4 === *)
(* K=1: right (1,0), K=2: up (0,1), K=3: left (-1,0), K=4: down (0,-1), ... *)

(* Direction from phase (0-3):
   Phase 1: right (1,0), Phase 2: up (0,1),
   Phase 3: left (-1,0), Phase 0: down (0,-1) *)

Definition dx_phase (p : nat) : Z :=
  match p with 1%nat => 1 | 3%nat => (-1) | _ => 0 end.

Definition dy_phase (p : nat) : Z :=
  match p with 2%nat => 1 | 0%nat => (-1) | _ => 0 end.

Definition spiral_dx (K : nat) : Z := dx_phase (Nat.modulo K 4).
Definition spiral_dy (K : nat) : Z := dy_phase (Nat.modulo K 4).

(* === Spiral position: cumulative sum of fib_Z(K) * direction(K) === *)

Fixpoint spiral_x (K : nat) : Z :=
  match K with
  | O => 0
  | S k => spiral_x k + fib_Z (S k) * spiral_dx (S k)
  end.

Fixpoint spiral_y (K : nat) : Z :=
  match K with
  | O => 0
  | S k => spiral_y k + fib_Z (S k) * spiral_dy (S k)
  end.

(* === Squared distance from origin === *)

Definition spiral_r_sq (K : nat) : Z :=
  spiral_x K * spiral_x K + spiral_y K * spiral_y K.

(* ================================================================ *)
(* Concrete Fibonacci values                                        *)
(* ================================================================ *)

Lemma fib_Z_0 : fib_Z 0 = 0. Proof. reflexivity. Qed.
Lemma fib_Z_1 : fib_Z 1 = 1. Proof. reflexivity. Qed.
Lemma fib_Z_2 : fib_Z 2 = 1. Proof. reflexivity. Qed.
Lemma fib_Z_3 : fib_Z 3 = 2. Proof. reflexivity. Qed.
Lemma fib_Z_4 : fib_Z 4 = 3. Proof. reflexivity. Qed.
Lemma fib_Z_5 : fib_Z 5 = 5. Proof. reflexivity. Qed.
Lemma fib_Z_6 : fib_Z 6 = 8. Proof. reflexivity. Qed.
Lemma fib_Z_7 : fib_Z 7 = 13. Proof. reflexivity. Qed.
Lemma fib_Z_8 : fib_Z 8 = 21. Proof. reflexivity. Qed.
Lemma fib_Z_9 : fib_Z 9 = 34. Proof. reflexivity. Qed.
Lemma fib_Z_10 : fib_Z 10 = 55. Proof. reflexivity. Qed.

(* ================================================================ *)
(* Concrete spiral positions                                        *)
(* ================================================================ *)

(* K=1: step right by 1 → (1,0) *)
Lemma spiral_pos_1 : spiral_x 1 = 1 /\ spiral_y 1 = 0.
Proof. split; vm_compute; reflexivity. Qed.

(* K=2: step up by 1 → (1,1) *)
Lemma spiral_pos_2 : spiral_x 2 = 1 /\ spiral_y 2 = 1.
Proof. split; vm_compute; reflexivity. Qed.

(* K=3: step left by 2 → (-1,1) *)
Lemma spiral_pos_3 : spiral_x 3 = (-1) /\ spiral_y 3 = 1.
Proof. split; vm_compute; reflexivity. Qed.

(* K=4: step down by 3 → (-1,-2) *)
Lemma spiral_pos_4 : spiral_x 4 = (-1) /\ spiral_y 4 = (-2).
Proof. split; vm_compute; reflexivity. Qed.

(* K=5: step right by 5 → (4,-2) *)
Lemma spiral_pos_5 : spiral_x 5 = 4 /\ spiral_y 5 = (-2).
Proof. split; vm_compute; reflexivity. Qed.

(* K=6: step up by 8 → (4,6) *)
Lemma spiral_pos_6 : spiral_x 6 = 4 /\ spiral_y 6 = 6.
Proof. split; vm_compute; reflexivity. Qed.

(* K=7: step left by 13 → (-9,6) *)
Lemma spiral_pos_7 : spiral_x 7 = (-9) /\ spiral_y 7 = 6.
Proof. split; vm_compute; reflexivity. Qed.

(* K=8: step down by 21 → (-9,-15) *)
Lemma spiral_pos_8 : spiral_x 8 = (-9) /\ spiral_y 8 = (-15).
Proof. split; vm_compute; reflexivity. Qed.

(* ================================================================ *)
(* Squared distance from origin                                     *)
(* ================================================================ *)

Lemma r_sq_1 : spiral_r_sq 1 = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma r_sq_2 : spiral_r_sq 2 = 2.
Proof. vm_compute. reflexivity. Qed.

Lemma r_sq_4 : spiral_r_sq 4 = 5.
Proof. vm_compute. reflexivity. Qed.

Lemma r_sq_5 : spiral_r_sq 5 = 20.
Proof. vm_compute. reflexivity. Qed.

Lemma r_sq_8 : spiral_r_sq 8 = 306.
Proof. vm_compute. reflexivity. Qed.

Lemma r_sq_10 : spiral_r_sq 10 = 2225.
Proof. vm_compute. reflexivity. Qed.
