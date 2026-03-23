(** * TopologicalProcessRefinement.v — Process is Strictly Finer than Chern Number
    Elements: Concentrated vs uniform Berry curvature distributions
    Roles:    Same Chern number, different process distributions
    Rules:    Process distinguishes what Chern number cannot → strictly finer
    Status:   Stdlib — Six Directions Phase 2, Section E7
    STATUS: 10 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================== *)
(*  PART I: TWO DISTRIBUTIONS WITH SAME CHERN                         *)
(*  concentrated_F: all curvature at one point                        *)
(*  uniform_F: curvature spread equally                               *)
(* ================================================================== *)

(* Berry curvature on 4-point BZ grid *)
Definition concentrated_F (i : nat) : Q :=
  match i with
  | O => 4
  | _ => 0
  end.

Definition uniform_F (i : nat) : Q := 1.

(* Sum over 4 points *)
Definition sum4 (f : nat -> Q) : Q :=
  f O + f (S O) + f (S (S O)) + f (S (S (S O))).

Lemma concentrated_total : sum4 concentrated_F == 4.
Proof. vm_compute. reflexivity. Qed.

Lemma uniform_total : sum4 uniform_F == 4.
Proof. vm_compute. reflexivity. Qed.

(* Same Chern number (same total) *)
Lemma same_chern :
  sum4 concentrated_F == sum4 uniform_F.
Proof.
  assert (H1 : sum4 concentrated_F == 4) by (vm_compute; reflexivity).
  assert (H2 : sum4 uniform_F == 4) by (vm_compute; reflexivity).
  rewrite H1, H2. reflexivity.
Qed.

(* ================================================================== *)
(*  PART II: DIFFERENT DISTRIBUTIONS                                    *)
(*  The processes differ at individual points                          *)
(* ================================================================== *)

Lemma concentrated_at_0 : concentrated_F O == 4.
Proof. vm_compute. reflexivity. Qed.

Lemma uniform_at_0 : uniform_F O == 1.
Proof. vm_compute. reflexivity. Qed.

(* Concentrated ≠ uniform at point 0 *)
Lemma different_at_0 : ~ (concentrated_F O == uniform_F O).
Proof.
  unfold concentrated_F, uniform_F.
  intros H. inversion H.
Qed.

(* ================================================================== *)
(*  PART III: VARIANCE AS DISTINGUISHER                                 *)
(*  sum of squares differs → different process                        *)
(* ================================================================== *)

Definition sum_sq4 (f : nat -> Q) : Q :=
  f O * f O + f (S O) * f (S O) +
  f (S (S O)) * f (S (S O)) + f (S (S (S O))) * f (S (S (S O))).

Lemma concentrated_variance : sum_sq4 concentrated_F == 16.
Proof. vm_compute. reflexivity. Qed.

Lemma uniform_variance : sum_sq4 uniform_F == 4.
Proof. vm_compute. reflexivity. Qed.

Lemma variance_differs : ~ (sum_sq4 concentrated_F == sum_sq4 uniform_F).
Proof.
  assert (H1 : sum_sq4 concentrated_F == 16) by (vm_compute; reflexivity).
  assert (H2 : sum_sq4 uniform_F == 4) by (vm_compute; reflexivity).
  rewrite H1, H2. intros H. inversion H.
Qed.

(* ================================================================== *)
(*  PART IV: PROCESS STRICTLY FINER                                     *)
(* ================================================================== *)

Theorem process_strictly_finer :
  (* Same Chern number *)
  sum4 concentrated_F == sum4 uniform_F /\
  (* Different local distributions *)
  ~ (concentrated_F O == uniform_F O) /\
  (* Different variances *)
  ~ (sum_sq4 concentrated_F == sum_sq4 uniform_F).
Proof.
  split; [exact same_chern|].
  split; [exact different_at_0|].
  exact variance_differs.
Qed.
