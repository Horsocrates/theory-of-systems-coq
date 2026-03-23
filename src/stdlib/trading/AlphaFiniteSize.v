(** * AlphaFiniteSize.v — Alpha decay as finite-size effect
    Elements: alpha process, decay parameter, qpow;
    Roles:    model trading alpha as exponentially decaying process;
    Rules:    alpha decays to zero, halflife and death thresholds quantified.
    STATUS: 14 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs List Bool Lia Lra Lqa.
Open Scope Q_scope.

(* ===== Rational power ===== *)

Fixpoint qpow (b : Q) (n : nat) : Q :=
  match n with
  | O => 1
  | S k => b * qpow b k
  end.

(* ===== Alpha process: A(t) = A0 * (1-p)^t ===== *)

Definition alpha_process (A0 p : Q) (t : nat) : Q := A0 * qpow (1 - p) t.

(* ===== Decay factor ===== *)

Definition alpha_decay_factor (p : Q) (t : nat) : Q := qpow (1 - p) t.

(* ===== Concrete alpha: A0=10, p=1/5 (so decay=4/5) ===== *)

Lemma alpha_day0 : alpha_process 10 (1#5) O == 10.
Proof. vm_compute. reflexivity. Qed.

Lemma alpha_day1 : alpha_process 10 (1#5) 1 == 8.
Proof. vm_compute. reflexivity. Qed.

Lemma alpha_day2 : alpha_process 10 (1#5) 2 == 32#5.
Proof. vm_compute. reflexivity. Qed.

Lemma alpha_day3 : alpha_process 10 (1#5) 3 == 128#25.
Proof. vm_compute. reflexivity. Qed.

Lemma alpha_day4 : alpha_process 10 (1#5) 4 == 512#125.
Proof. vm_compute. reflexivity. Qed.

(* ===== Decay factor values ===== *)

Lemma decay_factor_0 : alpha_decay_factor (1#5) O == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma decay_factor_1 : alpha_decay_factor (1#5) 1 == 4#5.
Proof. vm_compute. reflexivity. Qed.

Lemma decay_factor_3 : alpha_decay_factor (1#5) 3 == 64#125.
Proof. vm_compute. reflexivity. Qed.

(* ===== Halflife: (4/5)^4 < 1/2 ===== *)

Lemma alpha_halflife : qpow (4#5) 4 < 1#2.
Proof. unfold Qlt; simpl; lia. Qed.

(* ===== Alpha dead: (4/5)^8 < 1/5 ===== *)

Lemma alpha_dead : qpow (4#5) 8 < 1#5.
Proof. unfold Qlt; simpl; lia. Qed.

(* ===== Monotonic decay ===== *)

Lemma alpha_monotone_01 : alpha_process 10 (1#5) 1 < alpha_process 10 (1#5) O.
Proof. unfold Qlt; simpl; lia. Qed.

Lemma alpha_monotone_12 : alpha_process 10 (1#5) 2 < alpha_process 10 (1#5) 1.
Proof. unfold Qlt; simpl; lia. Qed.

(* ===== Initial value recovery ===== *)

Lemma alpha_initial_value : forall A0 p, alpha_process A0 p O == A0.
Proof. intros. unfold alpha_process. simpl. ring. Qed.

(* ===== Synthesis ===== *)

Theorem alpha_finite_size_synthesis :
  alpha_process 10 (1#5) O == 10 /\
  alpha_process 10 (1#5) 1 == 8 /\
  qpow (4#5) 4 < 1#2 /\
  qpow (4#5) 8 < 1#5 /\
  (forall A0 p, alpha_process A0 p O == A0).
Proof.
  split; [exact alpha_day0|].
  split; [exact alpha_day1|].
  split; [exact alpha_halflife|].
  split; [exact alpha_dead|].
  exact alpha_initial_value.
Qed.
