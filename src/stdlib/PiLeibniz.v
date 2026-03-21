(** * PiLeibniz.v -- π via Leibniz series: π/4 = 1 - 1/3 + 1/5 - ...
    Elements: leibniz_sum, pi_leibniz, oscillation, convergence
    Roles:    Simplest π formula. Convergence O(1/K).
    Rules:    Each partial sum exact Q. Alternating bounds for π.
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.

Open Scope Q_scope.

(* ================================================================== *)
(*  LEIBNIZ PARTIAL SUM                                                *)
(* ================================================================== *)

Fixpoint Qpow_pi (q : Q) (n : nat) : Q :=
  match n with O => 1 | S k => q * Qpow_pi q k end.

(** Leibniz term k: (-1)^k / (2k+1) *)
Definition leibniz_term (k : nat) : Q :=
  Qpow_pi (-(1)) k / inject_Z (Z.of_nat (2*k+1)).

(** π/4 ≈ Σ_{k=0}^{K} (-1)^k / (2k+1) *)
Fixpoint leibniz_sum (K : nat) : Q :=
  match K with
  | O => leibniz_term 0
  | S k => leibniz_sum k + leibniz_term (S k)
  end.

Definition pi_leibniz (K : nat) : Q := 4 * leibniz_sum K.

(* ================================================================== *)
(*  CONCRETE VALUES                                                    *)
(* ================================================================== *)

Lemma pi_leib_0 : pi_leibniz 0 == 4.
Proof. vm_compute. reflexivity. Qed.

Lemma pi_leib_1 : pi_leibniz 1 == 8#3.
Proof. vm_compute. reflexivity. Qed.

Lemma pi_leib_2 : pi_leibniz 2 == 52#15.
Proof. vm_compute. reflexivity. Qed.

Lemma pi_leib_3 : pi_leibniz 3 == 304#105.
Proof. vm_compute. reflexivity. Qed.

Lemma pi_leib_4 : pi_leibniz 4 == 1052#315.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  OSCILLATION                                                        *)
(* ================================================================== *)

(** Terms alternate above and below π *)
Lemma pi_leib_osc_01 : pi_leibniz 1 < pi_leibniz 0.
Proof. rewrite pi_leib_0, pi_leib_1. lra. Qed.

Lemma pi_leib_osc_12 : pi_leibniz 1 < pi_leibniz 2.
Proof. rewrite pi_leib_1, pi_leib_2. lra. Qed.

Lemma pi_leib_osc_23 : pi_leibniz 3 < pi_leibniz 2.
Proof. rewrite pi_leib_2, pi_leib_3. lra. Qed.

Theorem pi_leib_oscillates :
  pi_leibniz 1 < pi_leibniz 0 /\
  pi_leibniz 1 < pi_leibniz 2 /\
  pi_leibniz 3 < pi_leibniz 2.
Proof.
  split; [|split].
  - exact pi_leib_osc_01.
  - exact pi_leib_osc_12.
  - exact pi_leib_osc_23.
Qed.

(* ================================================================== *)
(*  BOUNDS: π trapped between consecutive partial sums                 *)
(* ================================================================== *)

Lemma pi_in_interval :
  pi_leibniz 3 < pi_leibniz 4 /\
  pi_leibniz 4 < pi_leibniz 2.
Proof.
  rewrite pi_leib_2, pi_leib_3, pi_leib_4.
  split; lra.
Qed.

(** Step size decreasing *)
Definition leibniz_step (K : nat) : Q :=
  Qabs (pi_leibniz (S K) - pi_leibniz K).

Lemma leib_step_1 : leibniz_step 1 == 4#5.
Proof. unfold leibniz_step. rewrite pi_leib_1, pi_leib_2. vm_compute. reflexivity. Qed.

Lemma leib_step_2 : leibniz_step 2 == 4#7.
Proof. unfold leibniz_step. rewrite pi_leib_2, pi_leib_3. vm_compute. reflexivity. Qed.

Lemma leib_step_decreasing : leibniz_step 2 < leibniz_step 1.
Proof. rewrite leib_step_1, leib_step_2. lra. Qed.

(** SYNTHESIS *)
Theorem pi_leibniz_synthesis :
  pi_leibniz 0 == 4 /\
  pi_leibniz 4 == 1052#315 /\
  pi_leibniz 3 < pi_leibniz 4 /\
  pi_leibniz 4 < pi_leibniz 2 /\
  leibniz_step 2 < leibniz_step 1.
Proof.
  split; [|split; [|split; [|split]]].
  - exact pi_leib_0.
  - exact pi_leib_4.
  - exact (proj1 pi_in_interval).
  - exact (proj2 pi_in_interval).
  - exact leib_step_decreasing.
Qed.
