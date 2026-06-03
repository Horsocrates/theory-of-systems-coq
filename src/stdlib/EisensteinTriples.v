(** * EisensteinTriples.v — integer triangles with a 60° angle (Eisenstein triples):
      a²−ab+b²=c² (the Eisenstein norm N(a,b)=|a+bω|², the ℤ[ω] analogue of the Pythagorean
      a²+b²=c² for ℤ[i]/90°).  Integer sides are Element side; but the AREA (√3/4)·ab is a
      role-limit (√3), because sin60°=√3/2.  The ANGLE decides: 90° gives a rational area,
      60° forces √3.  Cross-links EisensteinMUB.v (ℤ[ω]).

    Elements: the integer triples (3,8,7),(5,8,7),(5,21,19); the Eisenstein norm a²−ab+b²;
              ℤ[ω] (L1 + P4)
    Roles:    Element side = the integer 60°-triangles (solutions of a²−ab+b²=c², closed
              under Eisenstein-norm composition, like Pythagorean triples for 90°/ℤ[i]);
              role-limit = their AREA (√3/4·ab, irrational — sin60°=√3/2 forces √3)
    Rules:    the law of cosines with cos60°=1/2 ⟹ c²=a²+b²−ab; the Eisenstein norm
              N(a,b)=a²−ab+b²; its multiplicativity N(αβ)=N(α)N(β); area=(√3/4)·ab

    THE DEEP POINT — the angle decides whether the area is Element or role-limit.  A triangle
    with sides a,b and the included angle 60° has c²=a²+b²−2ab·cos60°=a²−ab+b² (the Eisenstein
    norm N(a,b)=|a+bω|², ω=e^{2πi/3}).  These integer 60°-triangles exist — (3,8,7),(5,8,7),
    (5,21,19) (`eisenstein_triples`) — and they are closed under the Eisenstein-norm
    multiplicativity N(a,b)·N(c,d)=N(ac−bd,ad+bc−bd) (`eisenstein_norm_mult`, a ring
    identity, the ℤ[ω] two-square law, exactly as the ℤ[i] two-square gives SO(2,ℚ)).  The
    equilateral triangle is a 60°-triangle (`equilateral_is_sixty`).  BUT the area of a
    60°-triangle is (√3/4)·ab, irrational: (4·Area)²=3·(ab)², a rational √3
    (`sixty_area_not_rational`).  Contrast the Pythagorean (90°) triangle, which has rational
    area ab/2 — the 90° angle (ℤ[i]) keeps the area rational, while the 60° angle (ℤ[ω])
    forces √3 (sin60°=√3/2).  Element = integer sides (the Eisenstein-norm solutions); role-
    limit = the area's √3.  The same √3 as the 60° point ①, the equilateral triangle, and
    the sphere's body diagonal; and the same ℤ[ω] as EisensteinMUB.v.

    ============ E/R/R разбор ============
      Rules (L5): косинусы при cos60°=1/2 ⟹ c²=a²+b²−ab; норма Эйзенштейна N(a,b)=a²−ab+b²;
                  мультипликативность N(αβ)=N(α)N(β); площадь=(√3/4)·ab.
      Roles (L4): Element = целые 60°-треугольники (решения a²−ab+b²=c², замкнуты под нормой Эйзенштейна,
                  как пифагоровы для 90°/ℤ[i]); role-limit = их ПЛОЩАДЬ (√3/4·ab, sin60°=√3/2 форсирует √3).
      Elements  : целые тройки (3,8,7),(5,8,7),(5,21,19); норма Эйзенштейна; ℤ[ω] (L1+P4).
    ДИАГНОСТИКА (P4): 60°-треугольники имеют целые стороны (Element, норм-форма), но площадь именует √3
    (role-limit, sin60°=√3/2); контраст: 90°-пифагоровы имеют рациональную площадь ab/2. Угол решает:
    90°→рациональна, 60°→√3. Тот же √3, что 60°-точка ①; та же ℤ[ω], что EisensteinMUB.

    STATUS: 5 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia.
From ToS Require Import analysis.Sqrt3Irrational.

Open Scope Z_scope.

(* ===================================================================== *)
(*  The Eisenstein norm and its multiplicativity (ℤ[ω] two-square law)     *)
(* ===================================================================== *)

(** The Eisenstein norm N(a,b) = |a+bω|² = a²−ab+b².  A triangle with sides a,b and a 60°
    included angle has c² = N(a,b) (law of cosines, cos60°=1/2). *)
Definition enorm (a b : Z) : Z := a*a - a*b + b*b.

(** ★ The Eisenstein norm is multiplicative: N(a,b)·N(c,d) = N(ac−bd, ad+bc−bd).  This is
    the ℤ[ω] two-square identity (from (a+bω)(c+dω) = (ac−bd)+(ad+bc−bd)ω), so 60°-triangles
    compose — exactly as the ℤ[i] two-square gives the rational rotation group. *)
Lemma eisenstein_norm_mult : forall a b c d : Z,
  enorm a b * enorm c d = enorm (a*c - b*d) (a*d + b*c - b*d).
Proof. intros a b c d. unfold enorm. ring. Qed.

(* ===================================================================== *)
(*  Integer 60°-triangles exist (Element side)                            *)
(* ===================================================================== *)

(** ★ Integer triangles with a 60° angle: a²−ab+b²=c² for (3,8,7),(5,8,7),(5,21,19). *)
Lemma eisenstein_triples :
  enorm 3 8 = 7*7 /\ enorm 5 8 = 7*7 /\ enorm 5 21 = 19*19.
Proof. repeat split; reflexivity. Qed.

(** The equilateral triangle (a,a,a) is a 60°-triangle: a²−a·a+a²=a²=c². *)
Lemma equilateral_is_sixty : forall a : Z, enorm a a = a*a.
Proof. intros a. unfold enorm. ring. Qed.

(* ===================================================================== *)
(*  Role-limit: the area of a 60°-triangle is irrational (√3)            *)
(* ===================================================================== *)

(** ★ The area of a 60°-triangle is (√3/4)·ab, never rational: 4·Area = √3·ab, so
    (4·Area)² = 3·(ab)² would make √3 = (4·Area)/(ab) ∈ ℚ (`sqrt3_irrational_Z`).  The 60°
    angle (sin60°=√3/2) forces √3 — unlike the 90° (Pythagorean) angle, whose area ab/2 is
    rational. *)
Theorem sixty_area_not_rational : forall a b m : Z,
  a <> 0 -> b <> 0 -> m * m <> 3 * (a*b * (a*b)).
Proof.
  intros a b m Ha Hb Heq.
  assert (Hab : a*b <> 0).
  { intro Hz. apply Z.mul_eq_0 in Hz. destruct Hz; [apply Ha | apply Hb]; assumption. }
  apply (sqrt3_irrational_Z m (a*b) Hab). nia.
Qed.

(* ===================================================================== *)
(*  Synthesis                                                            *)
(* ===================================================================== *)

(** Integer 60°-triangles (Eisenstein triples), split by the finitization boundary:
      (a) ELEMENT — the Eisenstein norm is multiplicative (60°-triangles compose);
      (b) integer 60°-triangles exist ((3,8,7),(5,8,7),(5,21,19));
      (c) the equilateral is a 60°-triangle;
      (d) ROLE-LIMIT — the area (√3/4·ab) is irrational (the 60° angle forces √3). *)
Theorem eisenstein_synthesis :
  (forall a b c d : Z, enorm a b * enorm c d = enorm (a*c - b*d) (a*d + b*c - b*d))
  /\ (enorm 3 8 = 7*7 /\ enorm 5 8 = 7*7 /\ enorm 5 21 = 19*19)
  /\ (forall a : Z, enorm a a = a*a)
  /\ (forall a b m : Z, a <> 0 -> b <> 0 -> m * m <> 3 * (a*b * (a*b))).
Proof.
  split; [ exact eisenstein_norm_mult | ].
  split; [ exact eisenstein_triples | ].
  split; [ exact equilateral_is_sixty | exact sixty_area_not_rational ].
Qed.
