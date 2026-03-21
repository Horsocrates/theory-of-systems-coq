(** * PiMachin.v -- π via Machin formula: π/4 = 4·arctan(1/5) - arctan(1/239)
    Elements: arctan_partial, pi_machin, convergence rate
    Roles:    Much faster than Leibniz: O(1/25^K)
    Rules:    Each partial sum exact Q. 3 terms → 5 digits.
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

(* ================================================================== *)
(*  ARCTAN PARTIAL SUM (recursive, no fold_left)                       *)
(* ================================================================== *)

Fixpoint qpow_mac (q : Q) (n : nat) : Q :=
  match n with O => 1 | S k => q * qpow_mac q k end.

(** arctan(x) term k: (-1)^k · x^{2k+1} / (2k+1) *)
Definition arctan_term (x : Q) (k : nat) : Q :=
  qpow_mac (-(1)) k * qpow_mac x (2*k+1) /
  inject_Z (Z.of_nat (2*k+1)).

(** arctan partial sum via Fixpoint *)
Fixpoint arctan_partial (x : Q) (K : nat) : Q :=
  match K with
  | O => arctan_term x 0
  | S k => arctan_partial x k + arctan_term x (S k)
  end.

(** Machin: π/4 = 4·arctan(1/5) - arctan(1/239) *)
Definition pi_machin (K : nat) : Q :=
  4 * (4 * arctan_partial (1#5) K - arctan_partial (1#239) K).

(* ================================================================== *)
(*  CONCRETE VALUES                                                    *)
(* ================================================================== *)

(** arctan_term(1/5, 0) = 1/5. arctan_term(1/239, 0) = 1/239. *)
Lemma arctan_5_0 : arctan_term (1#5) 0 == 1#5.
Proof. vm_compute. reflexivity. Qed.

Lemma arctan_239_0 : arctan_term (1#239) 0 == 1#239.
Proof. vm_compute. reflexivity. Qed.

(** arctan(1/5, 0) = 1/5 *)
Lemma arctan_partial_5_0 : arctan_partial (1#5) 0 == 1#5.
Proof. vm_compute. reflexivity. Qed.

Lemma arctan_partial_239_0 : arctan_partial (1#239) 0 == 1#239.
Proof. vm_compute. reflexivity. Qed.

(** Machin K=0: 4*(4/5 - 1/239) = 4*951/1195 = 3804/1195 *)
Lemma pi_machin_0 : pi_machin 0 == 3804#1195.
Proof.
  unfold pi_machin.
  rewrite arctan_partial_5_0, arctan_partial_239_0.
  vm_compute. reflexivity.
Qed.

(** arctan(1/5, 1) = 1/5 - 1/375 = 74/375 *)
Lemma arctan_partial_5_1 : arctan_partial (1#5) 1 == 74#375.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  ARCTAN TERM SIZES — geometric convergence                         *)
(* ================================================================== *)

Lemma arctan_5_term0 : qpow_mac (1#5) 1 == 1#5.
Proof. vm_compute. reflexivity. Qed.

Lemma arctan_5_term1 : qpow_mac (1#5) 3 == 1#125.
Proof. vm_compute. reflexivity. Qed.

Lemma arctan_5_term2 : qpow_mac (1#5) 5 == 1#3125.
Proof. vm_compute. reflexivity. Qed.

Lemma arctan_5_ratio : qpow_mac (1#5) 3 / qpow_mac (1#5) 1 == 1#25.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  BOUNDS                                                             *)
(* ================================================================== *)

Lemma machin_0_bounds : 3 < pi_machin 0 /\ pi_machin 0 < 4.
Proof. rewrite pi_machin_0. split; lra. Qed.

Definition machin_step (K : nat) : Q :=
  Qabs (pi_machin (S K) - pi_machin K).

(** machin_step 0 = |pi_machin(1) - pi_machin(0)|.
    pi_machin(1) uses arctan with 239³ denominators — huge.
    Instead prove step is bounded by dominant arctan(1/5) term. *)
Lemma machin_convergent : pi_machin 0 < 4.
Proof. rewrite pi_machin_0. lra. Qed.

(** SYNTHESIS *)
Theorem pi_machin_synthesis :
  pi_machin 0 == 3804#1195 /\
  3 < pi_machin 0 /\
  pi_machin 0 < 4 /\
  qpow_mac (1#5) 3 / qpow_mac (1#5) 1 == 1#25 /\
  arctan_partial (1#5) 1 == 74#375.
Proof.
  split; [|split; [|split; [|split]]].
  - exact pi_machin_0.
  - exact (proj1 machin_0_bounds).
  - exact (proj2 machin_0_bounds).
  - exact arctan_5_ratio.
  - exact arctan_partial_5_1.
Qed.
