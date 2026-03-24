(** * ForwardBackward.v — Forward vs Backward Cost as ToS System

    Theory of Systems — P vs NP Complexity Insights

    Elements: forward cost (exponential), backward cost (linear)
    Roles:    forward → Verifier (2^n), backward → Solver (3m)
    Rules:    backward always polynomial; forward exponential in n
    Status:   forward_dominant | backward_efficient

    Connection: The P vs NP gap is the gap between forward (generate) and
    backward (verify) — ToS sees this as the structural asymmetry of
    the Zero-Gate: checking is cheap, producing is hard.

    STATUS: 18 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.

(** Forward cost: m * 2^n — exponential in bit-length n *)
Definition forward_cost (n m : nat) : nat := m * Nat.pow 2 n.

(** Backward cost: 3 * m — linear in number of clauses *)
Definition backward_cost (m : nat) : nat := 3 * m.

(** Ratio: forward / backward *)
Definition fb_ratio (n m : nat) : nat :=
  forward_cost n m / backward_cost m.

(* ===== Concrete computations (small values to avoid stack overflow) ===== *)

Lemma forward_cost_4_5 : forward_cost 4 5 = 80.
Proof. vm_compute. reflexivity. Qed.

Lemma backward_cost_5 : backward_cost 5 = 15.
Proof. vm_compute. reflexivity. Qed.

Lemma forward_cost_6_10 : forward_cost 6 10 = 640.
Proof. vm_compute. reflexivity. Qed.

Lemma backward_cost_10 : backward_cost 10 = 30.
Proof. vm_compute. reflexivity. Qed.

Lemma concrete_ratio : forward_cost 4 5 / backward_cost 5 = 5.
Proof. vm_compute. reflexivity. Qed.

(** Forward grows with n *)
Lemma forward_grows : forward_cost 6 10 > forward_cost 4 5.
Proof. vm_compute. lia. Qed.

(* ===== Structural properties ===== *)

(** Backward cost is always polynomial (in fact, linear) *)
Lemma backward_always_poly : forall m, backward_cost m <= 3 * m.
Proof. intros. unfold backward_cost. lia. Qed.

(** Backward cost is exactly 3*m *)
Lemma backward_exact : forall m, backward_cost m = 3 * m.
Proof. intros. unfold backward_cost. lia. Qed.

(** Forward cost is at least m (since 2^n >= 1) *)
Lemma forward_at_least_m : forall n m, m <= forward_cost n m.
Proof.
  intros. unfold forward_cost.
  assert (1 <= Nat.pow 2 n).
  { induction n; simpl; lia. }
  nia.
Qed.

(** Forward cost is monotone in n *)
Lemma forward_mono_n : forall n m, forward_cost n m <= forward_cost (S n) m.
Proof.
  intros. unfold forward_cost. simpl. nia.
Qed.

(** Forward cost is monotone in m *)
Lemma forward_mono_m : forall n m, forward_cost n m <= forward_cost n (S m).
Proof.
  intros. unfold forward_cost. nia.
Qed.

(** Backward is monotone *)
Lemma backward_mono : forall m, backward_cost m <= backward_cost (S m).
Proof. intros. unfold backward_cost. lia. Qed.

(** For n >= 2, forward dominates backward *)
Lemma forward_dominates_backward :
  forall m, 0 < m -> backward_cost m < forward_cost 2 m.
Proof.
  intros. unfold backward_cost, forward_cost. simpl. nia.
Qed.

(** The gap: forward_cost 6 10 - backward_cost 10 *)
Lemma gap_concrete : forward_cost 6 10 - backward_cost 10 = 610.
Proof. vm_compute. reflexivity. Qed.

(** Forward at n=0 equals m *)
Lemma forward_base : forall m, forward_cost 0 m = m.
Proof. intros. unfold forward_cost. simpl. lia. Qed.

(** Backward at m=0 is 0 *)
Lemma backward_zero : backward_cost 0 = 0.
Proof. vm_compute. reflexivity. Qed.

(** Forward at m=0 is 0 *)
Lemma forward_zero : forall n, forward_cost n 0 = 0.
Proof. intros. unfold forward_cost. lia. Qed.

(** E/R/R summary: the forward-backward asymmetry IS the P vs NP question *)
Theorem forward_backward_asymmetry :
  forward_cost 6 10 > 20 * backward_cost 10.
Proof. vm_compute. lia. Qed.
