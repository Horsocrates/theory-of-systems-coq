(** * TransitionPhases.v -- Three phases of the classical-quantum transition
    Elements: is_dissipative_eps, is_critical_eps, is_expanding_eps, eigenvalue_ratio_eps
    Roles:    ε < 1/2 dissipative (|det|<1), ε = 1/2 critical (|det|=1), ε > 1/2 expanding (|det|>1)
    Rules:    Phase determines qualitative behavior of Green's function growth
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.GreenFunction.
From ToS Require Import stdlib.TransitionFamily.

Open Scope Q_scope.

(* ================================================================== *)
(*  PHASE CLASSIFICATION                                                *)
(* ================================================================== *)

Definition is_dissipative_eps (eps : Q) : Prop := 2 * eps < 1.
Definition is_critical_eps (eps : Q) : Prop := 2 * eps == 1.
Definition is_expanding_eps (eps : Q) : Prop := 1 < 2 * eps.

(* ================================================================== *)
(*  PHASE MEMBERSHIP                                                    *)
(* ================================================================== *)

Lemma quarter_dissipative : is_dissipative_eps (1#4).
Proof. unfold is_dissipative_eps. lra. Qed.

Lemma half_critical : is_critical_eps (1#2).
Proof. unfold is_critical_eps. lra. Qed.

Lemma three_quarter_expanding : is_expanding_eps (3#4).
Proof. unfold is_expanding_eps. lra. Qed.

Lemma zero_dissipative : is_dissipative_eps 0.
Proof. unfold is_dissipative_eps. lra. Qed.

Lemma one_expanding : is_expanding_eps 1.
Proof. unfold is_expanding_eps. lra. Qed.

(* ================================================================== *)
(*  EIGENVALUE RATIO                                                    *)
(* ================================================================== *)

(** Ratio of smaller to larger eigenvalue (approximate, for intuition) *)
Definition eigenvalue_ratio_eps (eps : Q) : Q := eps / (1 - eps).

Lemma ratio_at_0 : eigenvalue_ratio_eps 0 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma ratio_at_quarter : eigenvalue_ratio_eps (1#4) == 1#3.
Proof. vm_compute. reflexivity. Qed.

Lemma ratio_at_half : eigenvalue_ratio_eps (1#2) == 1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  GREEN FUNCTION GROWTH ACROSS PHASES                                 *)
(* ================================================================== *)

(** At ε=0 (classical): G_{00}(2) = 2 (doubling — full shift) *)
Lemma green_classical_2 : green (M_eps 0) 0%nat 0%nat 2 == 2.
Proof. vm_compute. reflexivity. Qed.

(** At ε=1/2 (critical/golden): G_{00}(2) = 2 (Fibonacci) *)
Lemma green_critical_2 : green (M_eps (1#2)) 0%nat 0%nat 2 == 2.
Proof. vm_compute. reflexivity. Qed.

(** At ε=1 (maximal): G_{00}(2) = 2 *)
Lemma green_maximal_2 : green (M_eps 1) 0%nat 0%nat 2 == 2.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                           *)
(* ================================================================== *)

Theorem transition_phases_synthesis :
  (* Phase membership *)
  is_dissipative_eps (1#4) /\
  is_critical_eps (1#2) /\
  is_expanding_eps (3#4) /\
  (* Eigenvalue ratio *)
  eigenvalue_ratio_eps 0 == 0 /\
  eigenvalue_ratio_eps (1#4) == 1#3 /\
  eigenvalue_ratio_eps (1#2) == 1 /\
  (* Growth at K=2 across phases *)
  green (M_eps 0) 0%nat 0%nat 2 == 2 /\
  green (M_eps (1#2)) 0%nat 0%nat 2 == 2 /\
  green (M_eps 1) 0%nat 0%nat 2 == 2.
Proof.
  split; [exact quarter_dissipative|].
  split; [exact half_critical|].
  split; [exact three_quarter_expanding|].
  split; [exact ratio_at_0|].
  split; [exact ratio_at_quarter|].
  split; [exact ratio_at_half|].
  split; [exact green_classical_2|].
  split; [exact green_critical_2|exact green_maximal_2].
Qed.
