(** * CauchyCriterion.v — Cauchy convergence criterion for PnL as ToS System
    Elements: PnL sequences, epsilon tolerance, convergence windows
    Roles:    Cauchy checking (is_cauchy_seq), convergence rate estimation
    Rules:    sequence is Cauchy if all adjacent diffs < epsilon,
              convergence rate = max adjacent diff in window
    STATUS: 18 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia Lra List.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================ *)
(* Cauchy check on concrete PnL list                                *)
(* ================================================================ *)

(* Adjacent differences in a list *)
Fixpoint adjacent_diffs (xs : list Q) : list Q :=
  match xs with
  | nil => nil
  | _ :: nil => nil
  | x :: ((y :: _) as rest) => Qabs (y - x) :: adjacent_diffs rest
  end.

(* Check if all elements of list are <= epsilon *)
Fixpoint all_le_eps (eps : Q) (xs : list Q) : bool :=
  match xs with
  | nil => true
  | x :: rest => Qle_bool x eps && all_le_eps eps rest
  end.

(* Is a PnL sequence Cauchy within tolerance epsilon? *)
Definition is_cauchy_seq (pnl : list Q) (epsilon : Q) : bool :=
  all_le_eps epsilon (adjacent_diffs pnl).

(* Maximum of a Q list *)
Fixpoint q_max_list (xs : list Q) : Q :=
  match xs with
  | nil => 0
  | x :: nil => x
  | x :: rest => let m := q_max_list rest in
                 if Qle_bool m x then x else m
  end.

(* Convergence rate: max adjacent diff *)
Definition convergence_rate (pnl : list Q) : Q :=
  q_max_list (adjacent_diffs pnl).

(* ================================================================ *)
(* Test sequences                                                   *)
(* ================================================================ *)

(* Converging sequence: 1, 1/2, 1/4, 1/8 *)
Definition pnl_converging : list Q := [1; 1#2; 1#4; 1#8].

(* Diverging sequence: 1, 2, 4, 8 *)
Definition pnl_diverging : list Q := [1; 2; 4; 8].

(* Stable sequence: 1, 1, 1, 1 *)
Definition pnl_stable : list Q := [1; 1; 1; 1].

(* Oscillating: 0, 1, 0, 1 *)
Definition pnl_oscillating : list Q := [0; 1; 0; 1].

(* Slowly converging: 1, 3/4, 5/8, 9/16 *)
Definition pnl_slow : list Q := [1; 3#4; 5#8; 9#16].

(* ================================================================ *)
(* Adjacent differences                                             *)
(* ================================================================ *)

(* Diffs compute to Q values that may not be in reduced form.
   We verify via Qeq on individual elements instead. *)

(* First diff of converging = |1/2 - 1| = 1/2 *)
Lemma diffs_converging_first :
  match adjacent_diffs pnl_converging with
  | d :: _ => d == 1#2
  | _ => False
  end.
Proof. unfold pnl_converging, adjacent_diffs. vm_compute. reflexivity. Qed.

(* Stable diffs are all zero *)
Lemma diffs_stable_first :
  match adjacent_diffs pnl_stable with
  | d :: _ => d == 0
  | _ => False
  end.
Proof. unfold pnl_stable, adjacent_diffs. vm_compute. reflexivity. Qed.

(* Diverging first diff = 1 *)
Lemma diffs_diverging_first :
  match adjacent_diffs pnl_diverging with
  | d :: _ => d == 1
  | _ => False
  end.
Proof. unfold pnl_diverging, adjacent_diffs. vm_compute. reflexivity. Qed.

(* Oscillating first diff = 1 *)
Lemma diffs_oscillating_first :
  match adjacent_diffs pnl_oscillating with
  | d :: _ => d == 1
  | _ => False
  end.
Proof. unfold pnl_oscillating, adjacent_diffs. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* Cauchy checks                                                    *)
(* ================================================================ *)

(* Converging with eps=1: all diffs <= 1 *)
Lemma cauchy_converging_eps1 :
  is_cauchy_seq pnl_converging 1 = true.
Proof. unfold is_cauchy_seq, pnl_converging. vm_compute. reflexivity. Qed.

(* Converging with eps=1/4: fails because first diff = 1/2 > 1/4 *)
Lemma not_cauchy_converging_eps_quarter :
  is_cauchy_seq pnl_converging (1#4) = false.
Proof. unfold is_cauchy_seq, pnl_converging. vm_compute. reflexivity. Qed.

(* Stable is always Cauchy *)
Lemma cauchy_stable :
  is_cauchy_seq pnl_stable (1#100) = true.
Proof. unfold is_cauchy_seq, pnl_stable. vm_compute. reflexivity. Qed.

(* Diverging is not Cauchy at eps=1 *)
Lemma not_cauchy_diverging :
  is_cauchy_seq pnl_diverging 1 = false.
Proof. unfold is_cauchy_seq, pnl_diverging. vm_compute. reflexivity. Qed.

(* Oscillating is not Cauchy at eps=1/2 *)
Lemma not_cauchy_oscillating :
  is_cauchy_seq pnl_oscillating (1#2) = false.
Proof. unfold is_cauchy_seq, pnl_oscillating. vm_compute. reflexivity. Qed.

(* Oscillating IS Cauchy at eps=1 (all diffs exactly 1) *)
Lemma cauchy_oscillating_eps1 :
  is_cauchy_seq pnl_oscillating 1 = true.
Proof. unfold is_cauchy_seq, pnl_oscillating. vm_compute. reflexivity. Qed.

(* Slowly converging at eps=1/4 *)
Lemma cauchy_slow_eps_quarter :
  is_cauchy_seq pnl_slow (1#4) = true.
Proof. unfold is_cauchy_seq, pnl_slow. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* Convergence rates                                                *)
(* ================================================================ *)

Lemma rate_converging :
  convergence_rate pnl_converging == 1#2.
Proof. unfold convergence_rate, pnl_converging. vm_compute. reflexivity. Qed.

Lemma rate_stable :
  convergence_rate pnl_stable == 0.
Proof. unfold convergence_rate, pnl_stable. vm_compute. reflexivity. Qed.

Lemma rate_diverging :
  convergence_rate pnl_diverging == 4.
Proof. unfold convergence_rate, pnl_diverging. vm_compute. reflexivity. Qed.

Lemma rate_oscillating :
  convergence_rate pnl_oscillating == 1.
Proof. unfold convergence_rate, pnl_oscillating. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* Empty and singleton                                              *)
(* ================================================================ *)

Lemma cauchy_empty : is_cauchy_seq nil (1#10) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cauchy_singleton : is_cauchy_seq [42] (1#10) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* Synthesis                                                        *)
(* ================================================================ *)

Definition cauchy_synthesis : Prop :=
  is_cauchy_seq pnl_converging 1 = true /\
  is_cauchy_seq pnl_diverging 1 = false /\
  convergence_rate pnl_stable == 0 /\
  is_cauchy_seq pnl_stable (1#100) = true.

Lemma cauchy_synthesis_holds : cauchy_synthesis.
Proof.
  split. exact cauchy_converging_eps1.
  split. exact not_cauchy_diverging.
  split. exact rate_stable.
  exact cauchy_stable.
Qed.
