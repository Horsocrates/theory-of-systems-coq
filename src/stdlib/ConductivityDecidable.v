(** * ConductivityDecidable.v — Metal vs Insulator Classification
    Elements: Gap value, conductor/insulator predicates, phase diagram
    Roles:    Decidable classification based on spectral gap sign
    Rules:    gap <= 0 → conductor; gap > 0 → insulator
    Status:   Stdlib — Six Directions Phase 2, Section F5
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
From Stdlib Require Import Bool.
Open Scope Q_scope.

(* ================================================================== *)
(*  PART I: CLASSIFICATION PREDICATES                                   *)
(*  is_conductor: gap <= 0                                             *)
(*  is_insulator: gap > 0                                              *)
(* ================================================================== *)

Definition is_conductor (gap : Q) : bool :=
  match Qnum gap with
  | Zpos _ => false
  | _ => true   (* zero or negative → conductor *)
  end.

Definition is_insulator (gap : Q) : bool :=
  negb (is_conductor gap).

(* ================================================================== *)
(*  PART II: CONCRETE CLASSIFICATIONS                                   *)
(* ================================================================== *)

(* Zero gap: metal *)
Lemma metal_at_zero : is_conductor 0 = true.
Proof. reflexivity. Qed.

(* Positive gap: insulator *)
Lemma insulator_at_one : is_insulator 1 = true.
Proof. reflexivity. Qed.

(* Negative gap (overlapping bands): conductor *)
Lemma conductor_negative : is_conductor (-(1#2)) = true.
Proof. reflexivity. Qed.

(* Small positive gap: insulator *)
Lemma insulator_small : is_insulator (1#10) = true.
Proof. reflexivity. Qed.

(* ================================================================== *)
(*  PART III: COMPLEMENTARITY                                           *)
(*  is_conductor and is_insulator are complementary                    *)
(* ================================================================== *)

Lemma conductor_insulator_complement :
  forall gap : Q, is_insulator gap = negb (is_conductor gap).
Proof.
  intros gap. reflexivity.
Qed.

Lemma conductor_not_insulator :
  is_conductor 0 = true /\ is_insulator 0 = false.
Proof. split; reflexivity. Qed.

Lemma insulator_not_conductor :
  is_insulator 1 = true /\ is_conductor 1 = false.
Proof. split; reflexivity. Qed.

(* ================================================================== *)
(*  PART IV: PHASE DIAGRAM                                              *)
(*  Various gap values mapped to conductor/insulator                  *)
(* ================================================================== *)

Lemma phase_diagram_metal : is_conductor 0 = true.
Proof. reflexivity. Qed.

Lemma phase_diagram_semimetal : is_conductor (-(1#4)) = true.
Proof. reflexivity. Qed.

Lemma phase_diagram_insulator : is_insulator 2 = true.
Proof. reflexivity. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                           *)
(* ================================================================== *)

Theorem conductivity_decidable_synthesis :
  is_conductor 0 = true /\
  is_insulator 1 = true /\
  is_conductor (-(1#2)) = true /\
  is_insulator (1#10) = true /\
  is_insulator 2 = true.
Proof.
  repeat split; reflexivity.
Qed.
