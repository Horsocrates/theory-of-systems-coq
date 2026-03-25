(** * BitOperators.v — Bit extraction and reconstruction for binary Heisenberg
    Elements: bit_of, bit_op, bit decomposition lemmas, reconstruction lemmas
    Roles:    Extract k-th bit of integer j; diagonal bit operator
    Rules:    Bit extraction via odd(j/2^k); reconstruction via Σ 2^k · b_k = j
    Status:   complete
    STATUS: 13 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Lia.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Bit Extraction                                             *)
(* ================================================================== *)

Definition bit_of (j k : nat) : Q :=
  if Nat.odd (Nat.div j (Nat.pow 2 k)) then 1 else 0.

Definition bit_op (k i j : nat) : Q :=
  if Nat.eqb i j then bit_of i k else 0.

(* ================================================================== *)
(*  Part II: 2-bit Decomposition (K=4)                                 *)
(* ================================================================== *)

Lemma bit_decomp_0 : bit_of 0 0 == 0 /\ bit_of 0 1 == 0.
Proof. split; vm_compute; reflexivity. Qed.

Lemma bit_decomp_1 : bit_of 1 0 == 1 /\ bit_of 1 1 == 0.
Proof. split; vm_compute; reflexivity. Qed.

Lemma bit_decomp_2 : bit_of 2 0 == 0 /\ bit_of 2 1 == 1.
Proof. split; vm_compute; reflexivity. Qed.

Lemma bit_decomp_3 : bit_of 3 0 == 1 /\ bit_of 3 1 == 1.
Proof. split; vm_compute; reflexivity. Qed.

(* ================================================================== *)
(*  Part III: Reconstruction (K=4)                                     *)
(* ================================================================== *)

Lemma reconstruct_0 : 1 * bit_of 0 0 + 2 * bit_of 0 1 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma reconstruct_1 : 1 * bit_of 1 0 + 2 * bit_of 1 1 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma reconstruct_2 : 1 * bit_of 2 0 + 2 * bit_of 2 1 == 2.
Proof. vm_compute. reflexivity. Qed.

Lemma reconstruct_3 : 1 * bit_of 3 0 + 2 * bit_of 3 1 == 3.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part IV: 3-bit Example (K=8, j=5 = 101_2)                         *)
(* ================================================================== *)

Lemma bit_of_5_0 : bit_of 5 0 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma bit_of_5_1 : bit_of 5 1 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma bit_of_5_2 : bit_of 5 2 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma reconstruct_5 : 1 * bit_of 5 0 + 2 * bit_of 5 1 + 4 * bit_of 5 2 == 5.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part V: Zero is Always Zero                                        *)
(* ================================================================== *)

Lemma bit_of_0_always : bit_of 0 0 == 0 /\ bit_of 0 1 == 0 /\ bit_of 0 2 == 0.
Proof. repeat split; vm_compute; reflexivity. Qed.
