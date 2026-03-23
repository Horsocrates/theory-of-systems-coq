(** * ZeroGateTrading.v — ERR structural validation for trading signals
    Elements: signals, entropy directions, stress levels, convergence rates;
    Roles:    gate checks (consistency, stress, confidence), zero gate;
    Rules:    annihilation — any check=0 forces result=0.
    STATUS: 20 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ================================================================ *)
(* Core definitions                                                  *)
(* ================================================================ *)

Definition gate (condition : bool) : Q := if condition then 1 else 0.

(* Consistency: signal and entropy must agree on direction *)
Definition check_consistency (signal_direction entropy_direction : Z) : Q :=
  gate (Z.eqb signal_direction entropy_direction || Z.eqb entropy_direction 0)%bool.

(* Stress: kill individual signals in crisis *)
Definition check_stress (stress : Q) (is_systematic : bool) : Q :=
  match is_systematic with
  | true => 1
  | false => if Qlt_le_dec stress (7#10) then 1 else 0
  end.

(* Confidence: kill signals when regime is unstable *)
Definition check_confidence (convergence_rate : Q) : Q :=
  if Qlt_le_dec convergence_rate (1#10) then 1 else 0.

(* Zero Gate: product of all checks *)
Definition zero_gate (signal : Q) (sig_dir entropy_dir : Z)
  (stress convergence : Q) (is_systematic : bool) : Q :=
  signal * check_consistency sig_dir entropy_dir *
  check_stress stress is_systematic *
  check_confidence convergence.

(* ================================================================ *)
(* Gate basics                                                       *)
(* ================================================================ *)

Lemma gate_true : gate true == 1.
Proof. unfold gate. reflexivity. Qed.

Lemma gate_false : gate false == 0.
Proof. unfold gate. reflexivity. Qed.

(* ================================================================ *)
(* Consistency checks                                                *)
(* ================================================================ *)

Lemma consistency_agree : check_consistency 1 1 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma consistency_disagree : check_consistency 1 (-1) == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma consistency_neutral : check_consistency 1 0 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma consistency_neg_agree : check_consistency (-1) (-1) == 1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* Stress checks                                                     *)
(* ================================================================ *)

Lemma stress_low : check_stress (3#10) false == 1.
Proof.
  unfold check_stress. destruct (Qlt_le_dec (3#10) (7#10)).
  - reflexivity.
  - exfalso. lra.
Qed.

Lemma stress_high : check_stress (8#10) false == 0.
Proof.
  unfold check_stress. destruct (Qlt_le_dec (8#10) (7#10)).
  - exfalso. lra.
  - reflexivity.
Qed.

Lemma stress_systematic : check_stress (8#10) true == 1.
Proof. unfold check_stress. reflexivity. Qed.

(* ================================================================ *)
(* Confidence checks                                                 *)
(* ================================================================ *)

Lemma confidence_stable : check_confidence (1#20) == 1.
Proof.
  unfold check_confidence. destruct (Qlt_le_dec (1#20) (1#10)).
  - reflexivity.
  - exfalso. lra.
Qed.

Lemma confidence_unstable : check_confidence (2#10) == 0.
Proof.
  unfold check_confidence. destruct (Qlt_le_dec (2#10) (1#10)).
  - exfalso. lra.
  - reflexivity.
Qed.

(* ================================================================ *)
(* Zero gate compound checks                                         *)
(* ================================================================ *)

Lemma good_signal : zero_gate 1 1 1 (3#10) (1#20) false == 1.
Proof.
  unfold zero_gate.
  rewrite consistency_agree, stress_low, confidence_stable.
  ring.
Qed.

Lemma killed_inconsistent : zero_gate 1 1 (-1) (3#10) (1#20) false == 0.
Proof.
  unfold zero_gate.
  rewrite consistency_disagree, stress_low, confidence_stable.
  ring.
Qed.

Lemma killed_stress : zero_gate 1 1 1 (8#10) (1#20) false == 0.
Proof.
  unfold zero_gate.
  rewrite consistency_agree, stress_high, confidence_stable.
  ring.
Qed.

Lemma killed_unstable : zero_gate 1 1 1 (3#10) (2#10) false == 0.
Proof.
  unfold zero_gate.
  rewrite consistency_agree, stress_low, confidence_unstable.
  ring.
Qed.

Lemma double_kill : zero_gate 1 1 (-1) (8#10) (2#10) false == 0.
Proof.
  unfold zero_gate.
  rewrite consistency_disagree, stress_high, confidence_unstable.
  ring.
Qed.

Lemma systematic_survives : zero_gate 1 1 1 (8#10) (1#20) true == 1.
Proof.
  unfold zero_gate.
  rewrite consistency_agree, stress_systematic, confidence_stable.
  ring.
Qed.

Lemma zero_gate_zero_signal : zero_gate 0 1 1 (3#10) (1#20) false == 0.
Proof.
  unfold zero_gate.
  rewrite consistency_agree, stress_low, confidence_stable.
  ring.
Qed.

(* ================================================================ *)
(* Property: any check = 0 annihilates the result                   *)
(* ================================================================ *)

Lemma gate_annihilates_consistency :
  forall signal stress conv sys sig_dir ent_dir,
    check_consistency sig_dir ent_dir == 0 ->
    zero_gate signal sig_dir ent_dir stress conv sys == 0.
Proof.
  intros. unfold zero_gate. rewrite H. ring.
Qed.

Lemma gate_annihilates_stress :
  forall signal sig_dir ent_dir stress conv sys,
    check_stress stress sys == 0 ->
    zero_gate signal sig_dir ent_dir stress conv sys == 0.
Proof.
  intros. unfold zero_gate. rewrite H. ring.
Qed.

Lemma gate_annihilates_confidence :
  forall signal sig_dir ent_dir stress conv sys,
    check_confidence conv == 0 ->
    zero_gate signal sig_dir ent_dir stress conv sys == 0.
Proof.
  intros. unfold zero_gate. rewrite H. ring.
Qed.

(* ================================================================ *)
(* Synthesis: Zero Gate enforces structural integrity                *)
(* ================================================================ *)

Theorem zero_gate_trading_synthesis :
  (* Good signal passes *)
  zero_gate 1 1 1 (3#10) (1#20) false == 1 /\
  (* Inconsistency kills *)
  zero_gate 1 1 (-1) (3#10) (1#20) false == 0 /\
  (* Stress kills *)
  zero_gate 1 1 1 (8#10) (1#20) false == 0 /\
  (* Instability kills *)
  zero_gate 1 1 1 (3#10) (2#10) false == 0 /\
  (* Systematic survives stress *)
  zero_gate 1 1 1 (8#10) (1#20) true == 1.
Proof.
  split. { exact good_signal. }
  split. { exact killed_inconsistent. }
  split. { exact killed_stress. }
  split. { exact killed_unstable. }
  exact systematic_survives.
Qed.
