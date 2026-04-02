(** * Harmony.v — Musical intervals from eigenvalue ratios
    Elements: consonance, intervals, shared harmonics
    Roles:    L1 (identity → periodic return) → consonance measure
    Rules:    C(p,q) = 1/(p*q). Simple ratio → consonant.
    STATUS:   12 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: April 2026

    CONSONANCE FROM L1:
    L1 (identity): system "wants" to return to itself.
    Two tones with ratio p/q: combined period = lcm(p,q) fundamentals.
    Short return → stable → consonant.
    Long return → unstable → dissonant.

    Pythagorean tuning = integer mode ratios on graph.
    Music theory = CONSEQUENCE of ToS.
*)

From Stdlib Require Import QArith Lia ZArith PeanoNat.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ================================================================ *)
(*  CONSONANCE MEASURE                                               *)
(* ================================================================ *)

Definition consonance (p q : nat) : Q :=
  1 / inject_Z (Z.of_nat (p * q)).

(** Musical intervals *)
Definition unison_ratio : Q := 1.
Definition octave_ratio : Q := 2.
Definition fifth_ratio : Q := 3 # 2.
Definition fourth_ratio : Q := 4 # 3.
Definition major_third_ratio : Q := 5 # 4.
Definition tritone_ratio : Q := 45 # 32.

(* ================================================================ *)
(*  CONSONANCE ORDERING                                              *)
(* ================================================================ *)

Lemma octave_most_consonant :
  consonance 2 1 > consonance 3 2.
Proof. unfold consonance. vm_compute. reflexivity. Qed.

Lemma fifth_more_than_tritone :
  consonance 3 2 > consonance 45 32.
Proof. unfold consonance. vm_compute. reflexivity. Qed.

Lemma consonance_ordering :
  consonance 1 1 > consonance 2 1 /\
  consonance 2 1 > consonance 3 2 /\
  consonance 3 2 > consonance 4 3 /\
  consonance 4 3 > consonance 5 4.
Proof.
  unfold consonance. repeat split; vm_compute; reflexivity.
Qed.

(* ================================================================ *)
(*  COMBINED PERIOD                                                  *)
(* ================================================================ *)

Definition combined_period_factor (p q : nat) : nat :=
  Nat.lcm p q.

Lemma octave_period : combined_period_factor 2 1 = 2%nat.
Proof. reflexivity. Qed.

Lemma fifth_period : combined_period_factor 3 2 = 6%nat.
Proof. reflexivity. Qed.

Lemma tritone_period : combined_period_factor 45 32 = 1440%nat.
Proof. reflexivity. Qed.

(* ================================================================ *)
(*  HARMONIC SERIES                                                  *)
(* ================================================================ *)

Definition harmonic_freq (n : nat) (fundamental : Q) : Q :=
  inject_Z (Z.of_nat n) * fundamental.

(** Harmonics of A=440 *)
Lemma harmonic_2 : harmonic_freq 2 440 == 880.
Proof. unfold harmonic_freq. vm_compute. reflexivity. Qed.

Lemma harmonic_3 : harmonic_freq 3 440 == 1320.
Proof. unfold harmonic_freq. vm_compute. reflexivity. Qed.

(** Octave = 2nd harmonic *)
Lemma octave_is_second_harmonic :
  harmonic_freq 2 440 == octave_ratio * 440.
Proof. unfold harmonic_freq, octave_ratio. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  SHARED HARMONICS                                                 *)
(* ================================================================ *)

Fixpoint shared_harmonics (p q K : nat) : nat :=
  match K with
  | O => 0%nat
  | S K' => ((if (K * q) mod p =? 0 then 1 else 0) +
              shared_harmonics p q K')%nat
  end.

Lemma shared_harmonics_octave :
  shared_harmonics 2 1 6 = 3%nat.
Proof. reflexivity. Qed.

Lemma shared_harmonics_fifth :
  shared_harmonics 3 2 6 = 2%nat.
Proof. reflexivity. Qed.

(* ================================================================ *)
(*  SYNTHESIS                                                        *)
(* ================================================================ *)

Theorem harmony_synthesis :
  (* Consonance ordering: unison > octave > fifth > fourth > major 3rd *)
  consonance 1 1 > consonance 2 1 /\
  consonance 2 1 > consonance 3 2 /\
  consonance 3 2 > consonance 4 3 /\
  (* Octave period = 2, tritone = 1440 *)
  combined_period_factor 2 1 = 2%nat /\
  combined_period_factor 45 32 = 1440%nat /\
  (* Octave = 2nd harmonic *)
  harmonic_freq 2 440 == octave_ratio * 440.
Proof.
  split; [vm_compute; reflexivity |
  split; [vm_compute; reflexivity |
  split; [vm_compute; reflexivity |
  split; [exact octave_period |
  split; [exact tritone_period |
  exact octave_is_second_harmonic]]]]].
Qed.
