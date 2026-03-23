(** * GroverPhase.v -- Grover's algorithm: oracle + diffusion find target
    Elements: grover_oracle (marks target 2), grover_diffusion, uniform state
    Roles:    Oracle negates target amplitude; diffusion amplifies it
    Rules:    D(O(psi)) concentrates amplitude on target (concrete Q proof)
    Status:   Stdlib
    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================== *)
(*  LOCAL: 4x4 matrix multiplication                                   *)
(* ================================================================== *)

Definition mat4_mul_gp (A B : nat -> nat -> Q) (r c : nat) : Q :=
  fold_left (fun acc m => acc + A r m * B m c) (seq 0%nat 4%nat) 0.

(* ================================================================== *)
(*  PART I: GROVER OPERATORS                                           *)
(* ================================================================== *)

(* Oracle: flip sign of target state |2>.  Diagonal: -1 at (2,2), else 1 *)
Definition grover_oracle (r c : nat) : Q :=
  if Nat.eqb r c then
    (if Nat.eqb r (S (S O)) then -(1) else 1)
  else 0.

(* Diffusion: D_{rc} = 2/N - delta_{rc} = 1/2 - delta_{rc}            *)
(* For N=4: 2*|psi><psi| - I, where |psi> = (1/2, 1/2, 1/2, 1/2)     *)
(* D_{rc} = 2*(1/4) - delta = 1/2 - delta                             *)
Definition grover_diffusion (r c : nat) : Q :=
  if Nat.eqb r c then -(1#2) else (1#2).

(* Uniform state: psi = (1/2, 1/2, 1/2, 1/2) as column vector *)
Definition uniform (r c : nat) : Q :=
  match c with O => (1#2) | _ => 0 end.

(* ================================================================== *)
(*  PART II: ORACLE ON UNIFORM STATE                                    *)
(* ================================================================== *)

(* O|psi>: flips amplitude of |2> component *)
(* O·psi = (1/2, 1/2, -1/2, 1/2) *)

Lemma oracle_psi_0 : mat4_mul_gp grover_oracle uniform O O == (1#2).
Proof. vm_compute. reflexivity. Qed.

Lemma oracle_psi_1 : mat4_mul_gp grover_oracle uniform (S O) O == (1#2).
Proof. vm_compute. reflexivity. Qed.

Lemma oracle_psi_2 : mat4_mul_gp grover_oracle uniform (S (S O)) O == -(1#2).
Proof. vm_compute. reflexivity. Qed.

Lemma oracle_psi_3 : mat4_mul_gp grover_oracle uniform (S (S (S O))) O == (1#2).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  PART III: DIFFUSION ON (ORACLE RESULT)                              *)
(* ================================================================== *)

(* v = O·psi. Compute D·v: *)
(* (Dv)_r = sum_c D_{rc} * v_c *)
(* (Dv)_0 = -1/2 * 1/2 + 1/2 * 1/2 + 1/2 * (-1/2) + 1/2 * 1/2 *)
(*        = -1/4 + 1/4 - 1/4 + 1/4 = 0 *)
(* (Dv)_2 = 1/2 * 1/2 + 1/2 * 1/2 + (-1/2)*(-1/2) + 1/2 * 1/2 *)
(*        = 1/4 + 1/4 + 1/4 + 1/4 = 1 *)

Definition oracle_result (r c : nat) : Q := mat4_mul_gp grover_oracle uniform r c.
Definition grover_result (r c : nat) : Q := mat4_mul_gp grover_diffusion oracle_result r c.

Lemma grover_target_0 : grover_result O O == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma grover_target_1 : grover_result (S O) O == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma grover_target_2 : grover_result (S (S O)) O == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma grover_target_3 : grover_result (S (S (S O))) O == 0.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  PART IV: GROVER FINDS TARGET (amplitude = 1 at target, 0 elsewhere) *)
(* ================================================================== *)

Theorem grover_finds_target :
  grover_result O O == 0 /\
  grover_result (S O) O == 0 /\
  grover_result (S (S O)) O == 1 /\
  grover_result (S (S (S O))) O == 0.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

(* The target state |2> gets amplitude 1 after one Grover step *)
(* All other states get amplitude 0 *)
(* This is exact for N=4 with one marked item *)

Theorem grover_phase_synthesis :
  (* Oracle flips target *)
  mat4_mul_gp grover_oracle uniform (S (S O)) O == -(1#2) /\
  (* Diffusion concentrates on target *)
  grover_result (S (S O)) O == 1 /\
  (* Non-targets vanish *)
  grover_result O O == 0.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.
