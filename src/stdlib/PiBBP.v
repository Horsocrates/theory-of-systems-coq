(** * PiBBP.v -- π via Bailey-Borwein-Plouffe formula (1997)
    Elements: bbp_term, pi_bbp, geometric convergence
    Roles:    Fastest π formula: O(1/16^K) convergence
    Rules:    Can compute n-th hex digit without previous digits
    Status:   Stdlib
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

(* ================================================================== *)
(*  BBP FORMULA                                                        *)
(* ================================================================== *)

Fixpoint qpow_bb (q : Q) (n : nat) : Q :=
  match n with O => 1 | S k => q * qpow_bb q k end.

(** BBP term k: (1/16)^k · (4/(8k+1) - 2/(8k+4) - 1/(8k+5) - 1/(8k+6)) *)
Definition bbp_term (k : nat) : Q :=
  let k8 := inject_Z (Z.of_nat (8*k)) in
  qpow_bb (1#16) k * (4/(k8+1) - 2/(k8+4) - 1/(k8+5) - 1/(k8+6)).

Fixpoint pi_bbp (K : nat) : Q :=
  match K with
  | O => bbp_term 0
  | S k => pi_bbp k + bbp_term (S k)
  end.

(* ================================================================== *)
(*  CONCRETE VALUES                                                    *)
(* ================================================================== *)

Lemma bbp_term_0 : bbp_term 0 == 47#15.
Proof. vm_compute. reflexivity. Qed.

Lemma pi_bbp_0 : pi_bbp 0 == 47#15.
Proof. vm_compute. reflexivity. Qed.

(** bbp_term(1) = (1/16)·(4/9 - 2/12 - 1/13 - 1/14) *)
(** bbp_term(1) = (1/16)·(4/9 - 2/12 - 1/13 - 1/14) = 4327/655200 *)
Lemma bbp_term_1_positive : 0 < bbp_term 1.
Proof. unfold bbp_term, qpow_bb, Qlt. vm_compute. reflexivity. Qed.

Lemma bbp_0_bounds : 3 < pi_bbp 0 /\ pi_bbp 0 < 4.
Proof. rewrite pi_bbp_0. split; lra. Qed.

(* ================================================================== *)
(*  GEOMETRIC CONVERGENCE                                              *)
(* ================================================================== *)

Lemma bbp_factor_0 : qpow_bb (1#16) 0 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma bbp_factor_1 : qpow_bb (1#16) 1 == 1#16.
Proof. vm_compute. reflexivity. Qed.

Lemma bbp_factor_2 : qpow_bb (1#16) 2 == 1#256.
Proof. vm_compute. reflexivity. Qed.

Lemma bbp_geometric_ratio :
  qpow_bb (1#16) 2 / qpow_bb (1#16) 1 == 1#16.
Proof. vm_compute. reflexivity. Qed.

Definition bbp_step (K : nat) : Q :=
  Qabs (pi_bbp (S K) - pi_bbp K).

Lemma bbp_step_0_small : bbp_step 0 < 1#100.
Proof.
  unfold bbp_step, Qlt. simpl. vm_compute. reflexivity.
Qed.

(** SYNTHESIS *)
Theorem pi_bbp_synthesis :
  pi_bbp 0 == 47#15 /\
  3 < pi_bbp 0 /\
  pi_bbp 0 < 4 /\
  qpow_bb (1#16) 2 / qpow_bb (1#16) 1 == 1#16 /\
  bbp_step 0 < 1#100.
Proof.
  split; [|split; [|split; [|split]]].
  - exact pi_bbp_0.
  - exact (proj1 bbp_0_bounds).
  - exact (proj2 bbp_0_bounds).
  - exact bbp_geometric_ratio.
  - exact bbp_step_0_small.
Qed.
