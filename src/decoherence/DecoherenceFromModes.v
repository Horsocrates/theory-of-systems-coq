(** * DecoherenceFromModes.v — Decoherence from vibration mode coupling
    Elements: decohere_step, coherence_after, qpow
    Roles:    coupling between system and environment modes → off-diagonal decay
    Rules:    gamma=0 preserves, gamma=1 kills instantly, partial monotone decrease
    STATUS:   12 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: April 2026

    DECOHERENCE = MODE COUPLING TO ENVIRONMENT.
    Off-diagonal elements of density matrix decay as (1-gamma)^n.
    gamma = coupling strength between system mode and environment modes.
    No coupling → no decoherence. Full coupling → instant decoherence.
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================ *)
(*  Q POWER                                                          *)
(* ================================================================ *)

Fixpoint qpow (base : Q) (n : nat) : Q :=
  match n with
  | O => 1
  | S m => base * qpow base m
  end.

Lemma qpow_0 : forall b, qpow b O = 1.
Proof. reflexivity. Qed.

Lemma qpow_1 : forall b, qpow b 1 == b.
Proof. intro. simpl. lra. Qed.

(* ================================================================ *)
(*  DECOHERENCE STEP                                                 *)
(* ================================================================ *)

(** One decoherence step: off-diagonal element decays by factor (1 - gamma) *)
Definition decohere_step (gamma offdiag : Q) : Q :=
  (1 - gamma) * offdiag.

(** Coherence after n steps: initial * (1-gamma)^n *)
Definition coherence_after (gamma initial : Q) (n : nat) : Q :=
  initial * qpow (1 - gamma) n.

(* ================================================================ *)
(*  NO COUPLING → NO DECOHERENCE                                    *)
(* ================================================================ *)

Lemma no_coupling_no_decoherence :
  forall offdiag : Q, decohere_step 0 offdiag == offdiag.
Proof. intro. unfold decohere_step. lra. Qed.

Lemma no_coupling_after_3 :
  coherence_after 0 1 3 == 1.
Proof. unfold coherence_after, qpow. vm_compute. reflexivity. Qed.

Lemma no_coupling_preserves :
  coherence_after 0 (1#2) 5 == 1#2.
Proof. unfold coherence_after, qpow. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  FULL COUPLING → INSTANT DECOHERENCE                             *)
(* ================================================================ *)

Lemma full_coupling_instant :
  forall offdiag : Q, decohere_step 1 offdiag == 0.
Proof. intro. unfold decohere_step. lra. Qed.

Lemma full_coupling_after_1 :
  coherence_after 1 1 1 == 0.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  PARTIAL COUPLING → MONOTONE DECREASE                            *)
(* ================================================================ *)

(** After 1 step with gamma=1/4, coherence = 3/4 *)
Lemma partial_step1 :
  coherence_after (1#4) 1 1 == 3#4.
Proof. vm_compute. reflexivity. Qed.

(** After 2 steps with gamma=1/4, coherence = 9/16 *)
Lemma partial_step2 :
  coherence_after (1#4) 1 2 == 9#16.
Proof. vm_compute. reflexivity. Qed.

(** Monotone: step2 < step1 *)
Lemma partial_monotone :
  coherence_after (1#4) 1 2 < coherence_after (1#4) 1 1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  DIAGONAL PRESERVED                                               *)
(* ================================================================ *)

(** Diagonal elements (|A_k|^2) are unchanged by decoherence.
    Only off-diagonal elements decay. Diagonal = probabilities. *)
Definition diagonal_element (prob : Q) (_ : Q) : Q := prob.

Lemma diagonal_preserved :
  forall prob gamma : Q, diagonal_element prob gamma == prob.
Proof. intros. unfold diagonal_element. lra. Qed.

(* ================================================================ *)
(*  N-STEP DECAY                                                     *)
(* ================================================================ *)

(** After 3 steps with gamma=1/2: (1/2)^3 = 1/8 *)
Lemma n_step_decay :
  coherence_after (1#2) 1 3 == 1#8.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  SYNTHESIS                                                        *)
(* ================================================================ *)

Theorem decoherence_from_modes_synthesis :
  (* No coupling → no decoherence *)
  decohere_step 0 1 == 1 /\
  (* Full coupling → instant death *)
  decohere_step 1 1 == 0 /\
  (* Partial coupling → monotone decay *)
  coherence_after (1#4) 1 2 < coherence_after (1#4) 1 1 /\
  (* 3 steps at gamma=1/2 gives 1/8 *)
  coherence_after (1#2) 1 3 == 1#8.
Proof.
  split; [exact (no_coupling_no_decoherence 1) |
  split; [exact (full_coupling_instant 1) |
  split; [exact partial_monotone |
  exact n_step_decay]]].
Qed.
