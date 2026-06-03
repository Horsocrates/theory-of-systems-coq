(** * MusicTemperament.v — the Pythagorean comma and the irrationality of equal
      temperament: just-intonation intervals are rational (Element), but 12 perfect
      fifths do NOT close at 7 octaves (3¹² ≠ 2¹⁹, the comma), and equal temperament
      closes the octave only with the IRRATIONAL semitone 2^(1/12) (a role-limit).

    Elements: the rational ratios 3/2 (fifth), 2 (octave), 5/4 (third); the integers
              3¹², 2¹⁹; the comma 531441/524288 (L1 + P4)
    Roles:    just-intonation intervals (3/2, 5/4) = the Element side (rational); the
              12-fifth cycle's closure = a role-limit it cannot reach (the comma); the
              equal-tempered semitone 2^(1/12) = a role-limit (irrational, it forces
              closure by sacrificing rational intervals)
    Rules:    the just fifth 3/2 and octave 2; stacking 12 fifths (3/2)¹² vs 7 octaves
              2⁷ ⟺ 3¹² vs 2¹⁹; equal temperament's 12 equal steps, semitone 2^(1/12);
              the comma 3¹²/2¹⁹

    THE DEEP POINT — the same number-theoretic obstruction "powers of 3 cannot equal
    powers of 2" (cf. `DyadicBits.v`) appears in music as the Pythagorean comma.
    Just intonation uses small-integer ratios — a perfect fifth is 3/2, an octave is
    2 — and these are Element-side (rational).  But you cannot tile the octave with
    rational fifths: stacking 12 fifths multiplies by (3/2)¹² and 7 octaves by 2⁷, and
    these are equal iff 3¹² = 2¹⁹ — which is FALSE (`pythagorean_comma`: 531441 ≠
    524288; the 12 fifths OVERSHOOT, `comma_overshoots`).  So the cycle of fifths never
    closes — the Pythagorean comma.  Equal temperament forces closure by dividing the
    octave into 12 equal steps, each a semitone of 2^(1/12); but 2^(1/12) is
    IRRATIONAL (`equal_temperament_irrational`: no rational raised to the 12th is 2 —
    because its 6th power would be √2), a role-limit.  The fundamental tension of
    musical tuning is exactly the finitization boundary: rational intervals (Element)
    versus octave closure (which needs the role-limit 2^(1/12)).  You cannot have
    both, because powers of 3 and powers of 2 never coincide.

    ============ E/R/R разбор ============
      Rules (L5): чистая квинта 3/2, октава 2; 12 квинт (3/2)¹² vs 7 октав 2⁷ ⟺ 3¹² vs
                  2¹⁹; равномерная темперация — полутон 2^(1/12); комма 3¹²/2¹⁹.
      Roles (L4): чистая интонация (3/2, 5/4) = Element; замыкание 12-квинтового цикла =
                  role-limit (комма); полутон 2^(1/12) = role-limit (иррационален).
      Elements  : рац. отношения 3/2, 2, 5/4; целые 3¹², 2¹⁹; комма 531441/524288 (L1+P4).
    ДИАГНОСТИКА (P4): рациональные интервалы (Element) не замыкают октаву (3¹²≠2¹⁹, пифагорова
    комма); равномерная темперация замыкает иррациональным 2^(1/12) (role-limit). Напряжение
    строя = граница финитизации; та же обструкция «степени 3 ≠ степени 2», что у DyadicBits.

    STATUS: 4 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lia ZArith.
From ToS Require Import analysis.Sqrt2Irrational.

(* ================================================================= *)
(** ** The Pythagorean comma: 12 fifths do not close at 7 octaves     *)
(* ================================================================= *)

Open Scope Z_scope.

(** ★ 12 perfect fifths (3¹²) do NOT equal 7 octaves (2¹⁹): the cycle of rational
    fifths never closes — the Pythagorean comma. *)
Theorem pythagorean_comma : 3 ^ 12 <> 2 ^ 19.
Proof. vm_compute. discriminate. Qed.

(** The 12 fifths OVERSHOOT 7 octaves (3¹² > 2¹⁹): the comma 531441/524288 > 1. *)
Theorem comma_overshoots : 2 ^ 19 < 3 ^ 12.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(** ** Equal temperament: the semitone 2^(1/12) is irrational         *)
(* ================================================================= *)

Open Scope Q_scope.

Definition p6  (q : Q) : Q := q*q*q*q*q*q.
Definition p12 (q : Q) : Q := p6 q * p6 q.        (* q^12 *)

(** ★ The equal-tempered semitone 2^(1/12) is irrational: no rational q has q¹²=2,
    because then (q⁶)²=2 would make q⁶ a rational square root of 2.  So equal
    temperament's semitone is a role-limit. *)
Theorem equal_temperament_irrational : ~ (exists q : Q, p12 q == 2).
Proof.
  intros [q Hq]. unfold p12 in Hq.
  apply sqrt2_not_in_Q. exists (p6 q). exact Hq.
Qed.

(* ================================================================= *)
(** ** Synthesis                                                      *)
(* ================================================================= *)

(** Musical tuning split by the finitization boundary:
      (a) 12 rational fifths do not close at 7 octaves (3¹² ≠ 2¹⁹, the comma);
      (b) the fifths overshoot (3¹² > 2¹⁹);
      (c) equal temperament closes the octave with the irrational semitone 2^(1/12)
          (a role-limit) — rational intervals and octave closure cannot coexist. *)
Theorem temperament_synthesis :
  (3 ^ 12 <> 2 ^ 19)%Z
  /\ (2 ^ 19 < 3 ^ 12)%Z
  /\ ~ (exists q : Q, p12 q == 2).
Proof.
  split; [ exact pythagorean_comma | ].
  split; [ exact comma_overshoots | exact equal_temperament_irrational ].
Qed.
