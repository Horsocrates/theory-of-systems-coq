(** * DeutschAlgorithm.v — Deutsch Algorithm: 1 Query Suffices
    Elements: 4x4 matrices (H tensor H, CNOT, oracle), balanced/constant
    Roles:    Demonstrate quantum query advantage over classical
    Rules:    Balanced f → measure |1>, Constant f → measure |0>
    Status:   Stdlib
    STATUS: 8 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ================================================================== *)
(*  4x4 MATRIX ARITHMETIC                                             *)
(* ================================================================== *)

Definition mat4 := nat -> nat -> Q.

Definition mat4_mul (A B : mat4) (r c : nat) : Q :=
  A r O * B O c + A r (S O) * B (S O) c +
  A r (S (S O)) * B (S (S O)) c + A r (S (S (S O))) * B (S (S (S O))) c.

Definition mat4_compose (A B : mat4) : mat4 :=
  fun r c => mat4_mul A B r c.

(* Identity *)
Definition I_4 : mat4 := fun r c =>
  match r, c with
  | O, O => 1 | S O, S O => 1
  | S (S O), S (S O) => 1 | S (S (S O)), S (S (S O)) => 1
  | _, _ => 0
  end.

(* H ⊗ H = Hadamard on each qubit *)
(* H = (1/√2)[[1,1],[1,-1]], so H⊗H = (1/2)[[1,1,1,1],[1,-1,1,-1],[1,1,-1,-1],[1,-1,-1,1]] *)
(* We work with 2*H⊗H to avoid fractions, then normalize at end *)
Definition HH : mat4 := fun r c =>
  match r, c with
  | O, O => 1 | O, S O => 1 | O, S (S O) => 1 | O, S (S (S O)) => 1
  | S O, O => 1 | S O, S O => -(1) | S O, S (S O) => 1 | S O, S (S (S O)) => -(1)
  | S (S O), O => 1 | S (S O), S O => 1 | S (S O), S (S O) => -(1) | S (S O), S (S (S O)) => -(1)
  | S (S (S O)), O => 1 | S (S (S O)), S O => -(1) | S (S (S O)), S (S O) => -(1) | S (S (S O)), S (S (S O)) => 1
  | _, _ => 0
  end.

(* CNOT: |a,b> → |a, a XOR b> *)
Definition CNOT : mat4 := fun r c =>
  match r, c with
  | O, O => 1 | S O, S O => 1
  | S (S O), S (S (S O)) => 1 | S (S (S O)), S (S O) => 1
  | _, _ => 0
  end.

(* ================================================================== *)
(*  DEUTSCH ORACLES                                                    *)
(*  f: {0,1} → {0,1}                                                  *)
(*  Constant: f(0)=f(1)=0 or f(0)=f(1)=1                             *)
(*  Balanced: f(0)≠f(1)                                               *)
(*  Oracle U_f: |x,y> → |x, y XOR f(x)>                               *)
(* ================================================================== *)

(* Constant oracle: f(x) = 0 for all x *)
Definition oracle_const : mat4 := I_4.

(* Balanced oracle: f(x) = x, so |x,y> → |x, y XOR x> = CNOT *)
Definition oracle_balanced : mat4 := CNOT.

(* ================================================================== *)
(*  DEUTSCH CIRCUIT: HH · U_f · HH · |01>                             *)
(*  Initial state |01> = (0, 1, 0, 0)                                  *)
(*  Apply HH, then oracle, then HH, measure first qubit               *)
(* ================================================================== *)

(* Step 1: HH |01> *)
Lemma hh_01_0 : mat4_mul HH I_4 O (S O) == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma hh_01_1 : mat4_mul HH I_4 (S O) (S O) == -(1).
Proof. vm_compute. reflexivity. Qed.

(* For constant oracle: HH · I · HH applied to |01> *)
Definition deutsch_const (r : nat) : Q :=
  mat4_mul (mat4_compose HH (mat4_compose oracle_const HH)) I_4 r (S O).

(* For balanced oracle: HH · CNOT · HH applied to |01> *)
Definition deutsch_balanced (r : nat) : Q :=
  mat4_mul (mat4_compose HH (mat4_compose oracle_balanced HH)) I_4 r (S O).

(* Constant oracle: amplitude 4 at |01>, zero at |11> *)
Lemma deutsch_const_1 : deutsch_const (S O) == 4.
Proof. vm_compute. reflexivity. Qed.

Lemma deutsch_const_3 : deutsch_const (S (S (S O))) == 0.
Proof. vm_compute. reflexivity. Qed.

(* Balanced oracle: amplitude 4 at |11>, zero at |01> *)
Lemma deutsch_balanced_1 : deutsch_balanced (S O) == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma deutsch_balanced_3 : deutsch_balanced (S (S (S O))) == 4.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  DISTINGUISHABILITY                                                 *)
(*  Constant → amplitude on |0,1> nonzero, |1,1> zero                *)
(*  Balanced → amplitude on |0,1> zero, |1,1> nonzero                *)
(*  First qubit measurement distinguishes: one query suffices!         *)
(* ================================================================== *)

Theorem deutsch_one_query :
  deutsch_const (S O) == 4 /\ deutsch_const (S (S (S O))) == 0 /\
  deutsch_balanced (S O) == 0 /\ deutsch_balanced (S (S (S O))) == 4.
Proof.
  split; [exact deutsch_const_1|].
  split; [exact deutsch_const_3|].
  split; [exact deutsch_balanced_1|].
  exact deutsch_balanced_3.
Qed.

Theorem deutsch_algorithm_synthesis :
  (* Constant: |01> amplitude nonzero *)
  deutsch_const (S O) == 4 /\
  (* Balanced: |01> amplitude zero *)
  deutsch_balanced (S O) == 0.
Proof.
  split; [exact deutsch_const_1|exact deutsch_balanced_1].
Qed.
