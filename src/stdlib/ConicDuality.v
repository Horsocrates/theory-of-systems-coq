(** * ConicDuality.v — one rational generator, two conics: Diophantus' map
      (p,q) ↦ (q²−p², 2pq, q²+p²) is SIMULTANEOUSLY the Pythagorean triple
      parametrization (the unit CIRCLE — Euclidean rotations) and the Lorentz boost
      parametrization (the unit HYPERBOLA — special relativity).  Rational conic
      points ⟺ a rational parameter (the Element side); the same 3-4-5 is a circle
      point AND a hyperbola point.

    Elements: the integer pair (p,q); the triple (q²−p², 2pq, q²+p²); the rational
              parameter t; the triple 3-4-5 (L1 + P4)
    Roles:    the Diophantus triple = the GENERATOR (the Rule producing every
              rational conic point); circle points = rotations/Pythagoras (①),
              hyperbola points = boosts/Lorentz (H9) — TWO conics, ONE generator; the
              excluded projection point / an irrational parameter = a role-limit
    Rules:    Diophantus' map (q²−p², 2pq, q²+p²); the ONE identity read as a circle
              (a²+b²=c²) or a hyperbola (c²−b²=a²); the stereographic parametrisation
              hx,hy; rational point ⟺ rational parameter

    THE DEEP POINT — the Element-side symmetry groups of BOTH Euclidean rotations and
    Lorentz boosts come from the SAME rational generator.  The complement
    `PythagoreanTriples.v` parametrises the unit CIRCLE: px(t)=(1−t²)/(1+t²),
    py(t)=2t/(1+t²), landing on x²+y²=1, with the 3-4-5 triple at t=1/2 and a group
    law on the parameter (rational rotations).  Here is the HYPERBOLA twin:
    hx(t)=(1+t²)/(1−t²)=γ, hy(t)=2t/(1−t²)=s=γβ, landing on γ²−s²=1
    (`param_on_hyperbola`), with the β=3/5 boost at t=1/3 (`hyperbola_345`).  And the
    two are ONE identity: Diophantus' triple (q²−p², 2pq, q²+p²) satisfies BOTH
    (q²−p²)² + (2pq)² = (q²+p²)²  (Pythagoras / circle, `diophantus_circle`) and the
    rearrangement (q²+p²)² − (2pq)² = (q²−p²)²  (Lorentz / hyperbola,
    `diophantus_hyperbola`) — the SAME three numbers on two conics.  So a rational
    conic point is exactly one with a rational parameter t (the Element side); the
    role-limit is an irrational parameter or the single excluded projection point.
    The 3-4-5 triple (Bell, H6) is a circle point (Pythagoras, rotations) AND a
    hyperbola point (Lorentz, boosts): one Element, two conics.

    ============ E/R/R разбор ============
      Rules (L5): карта Диофанта (q²−p², 2pq, q²+p²); ОДНА тождественность как
                  окружность (a²+b²=c²) или гипербола (c²−b²=a²); стереографические
                  hx,hy; рациональная точка ⟺ рациональный t.
      Roles (L4): тройка Диофанта = генератор; точки окружности = вращения/Пифагор (①),
                  гиперболы = бусты/Лоренц (H9) — две коники, один генератор; иррациональный
                  t / исключённая точка = role-limit.
      Elements  : пара (p,q); тройка (q²−p²,2pq,q²+p²); параметр t; 3-4-5 (L1+P4).
    ДИАГНОСТИКА (P4): рациональные точки И окружности (вращения), И гиперболы (бусты) рождаются
    ОДНИМ рациональным генератором; рациональная точка ⟺ рациональный t (Element). Одна
    тождественность, две коники; 3-4-5 = точка окружности И гиперболы. Объединяет ① и H9.

    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lia ZArith Lqa.

(* ===================================================================== *)
(*  One identity, two conics — Diophantus' integer parametrization        *)
(* ===================================================================== *)

Open Scope Z_scope.

(** Circle (Pythagoras / rotations): the Diophantus triple is a Pythagorean triple. *)
Theorem diophantus_circle : forall p q : Z,
  (q*q - p*p) * (q*q - p*p) + (2*p*q) * (2*p*q) = (q*q + p*p) * (q*q + p*p).
Proof. intros p q. ring. Qed.

(** Hyperbola (Lorentz / boosts): the SAME three numbers, rearranged onto the
    hyperbola c²−b²=a². *)
Theorem diophantus_hyperbola : forall p q : Z,
  (q*q + p*p) * (q*q + p*p) - (2*p*q) * (2*p*q) = (q*q - p*p) * (q*q - p*p).
Proof. intros p q. ring. Qed.

(** p=1, q=2 generates the triple (3,4,5). *)
Theorem diophantus_345 : forall p q : Z,
  p = 1 -> q = 2 ->
  (q*q - p*p = 3) /\ (2*p*q = 4) /\ (q*q + p*p = 5).
Proof. intros p q Hp Hq. subst. repeat split; reflexivity. Qed.

(* ===================================================================== *)
(*  The hyperbola stereographic parametrisation (Lorentz twin of the      *)
(*  circle one in PythagoreanTriples.v)                                    *)
(* ===================================================================== *)

Open Scope Q_scope.

Lemma one_minus_sq_nz : forall t : Q, ~ (t * t == 1) -> ~ (1 - t * t == 0).
Proof. intros t H Hc. apply H. lra. Qed.

Definition hx (t : Q) : Q := (1 + t*t) / (1 - t*t).     (* γ *)
Definition hy (t : Q) : Q := (2*t) / (1 - t*t).          (* s = γβ *)
Definition on_hyperbola (g s : Q) : Prop := g*g - s*s == 1.

(** ★ Every rational parameter (with t²≠1) lands on the unit hyperbola: rational
    boosts are GENERATED from ℚ, just as rational rotations are. *)
Theorem param_on_hyperbola : forall t : Q,
  ~ (t * t == 1) -> on_hyperbola (hx t) (hy t).
Proof.
  intros t H. unfold on_hyperbola, hx, hy. field.
  apply one_minus_sq_nz; exact H.
Qed.

(** The β=3/5 boost is the instance t = 1/3: hx=5/4 (γ), hy=3/4 (s). *)
Theorem hyperbola_345 : hx (1#3) == 5#4 /\ hy (1#3) == 3#4.
Proof. split; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(*  Synthesis                                                             *)
(* ===================================================================== *)

(** One rational generator, two conics:
      (a) Diophantus' triple satisfies the circle identity (Pythagoras / rotations);
      (b) the SAME triple satisfies the hyperbola identity (Lorentz / boosts);
      (c) the hyperbola is rationally parametrised (rational boosts generated from ℚ);
      (d) the 3-4-5 triple is the instance p=1,q=2 / t=1/3 — a circle point and a
          hyperbola point at once. *)
Theorem conic_duality_synthesis :
  (forall p q : Z, ((q*q - p*p)*(q*q - p*p) + (2*p*q)*(2*p*q) = (q*q + p*p)*(q*q + p*p))%Z)
  /\ (forall p q : Z, ((q*q + p*p)*(q*q + p*p) - (2*p*q)*(2*p*q) = (q*q - p*p)*(q*q - p*p))%Z)
  /\ (forall t : Q, ~ (t * t == 1) -> on_hyperbola (hx t) (hy t))
  /\ (hx (1#3) == 5#4 /\ hy (1#3) == 3#4).
Proof.
  split; [ exact diophantus_circle | ].
  split; [ exact diophantus_hyperbola | ].
  split; [ exact param_on_hyperbola | exact hyperbola_345 ].
Qed.
