(** * RationalLorentz.v — special relativity over ℚ: a rational Lorentz boost is a
      rational point on the unit hyperbola γ²−(γβ)²=1 — i.e. a Pythagorean triple —
      and such boosts form a CLOSED GROUP under composition (the Lorentz invariant is
      a multiplicative norm form).  A generic boost has an irrational γ (a role-limit).

    Elements: the rational γ, s=γβ, β of a Pythagorean boost; the triples 3-4-5,
              8-15-17; the conserved invariant 1 (L1 + P4)
    Roles:    rational boosts (γ,s ∈ ℚ with γ²−s²=1) = the Element side — rational
              hyperbola points = Pythagorean triples, CLOSED under composition — vs a
              generic boost γ=1/√(1−β²) = a role-limit (irrational, √3 at β=½); the
              Lorentz invariant = the conserved Element; rapidity = the additive role
    Rules:    the invariant γ²−s²=1; composition (γ₁,s₁)·(γ₂,s₂) =
              (γ₁γ₂+s₁s₂, γ₁s₂+s₁γ₂); the norm form γ²−s²=(γ−s)(γ+s) is multiplicative;
              the duality 3²+4²=5² (circle) ⟺ 5²−3²=4² (hyperbola)

    THE DEEP POINT — special relativity is Element-side exactly at the "Pythagorean"
    boosts.  A 1+1-dimensional Lorentz boost is the matrix [[γ, s],[s, γ]] with
    s = γβ and the invariant γ²−s² = 1 (this is cosh²−sinh² = 1).  A boost is
    RATIONAL — both γ and the velocity β are rational — exactly when (γ, s) is a
    rational point on the unit hyperbola, which (clearing denominators) is a
    Pythagorean triple: the β=3/5 boost has γ=5/4, s=3/4, and (4s, 4, 4γ) = (3,4,5)
    with 5²−3²=4² ⟺ 3²+4²=5².  The SAME 3-4-5 that gives the rational Bell violation
    (H6) is a rational circle point (Pythagoras) AND a rational hyperbola point
    (Lorentz) — one Element, two conics.

    These rational boosts are CLOSED under composition (`boost_compose_valid`): the
    invariant γ²−s² = (γ−s)(γ+s) is a MULTIPLICATIVE norm form, so composing two
    boosts on the unit hyperbola lands on it again.  They form the Element-side
    relativistic velocity group — e.g. composing the 3-4-5 boost with itself gives the
    8-15-17 boost (`boost_compose_345`).  But a GENERIC boost is a role-limit: at
    β=1/2, γ²=4/3 has no rational root (`boost_half_role_limit`, via √3 — the same √3
    as the 60° point in ④).  So rational velocity ≠ rational boost: γ generically
    leaves ℚ, while the Pythagorean boosts stay finitely actual and group-closed.

    ============ E/R/R разбор ============
      Rules (L5): инвариант γ²−s²=1; композиция (γ₁γ₂+s₁s₂, γ₁s₂+s₁γ₂); норм-форма
                  γ²−s²=(γ−s)(γ+s) мультипликативна; 3²+4²=5² ⟺ 5²−3²=4².
      Roles (L4): рациональные бусты (γ²−s²=1) = Element (пифагоровы тройки, замкнутая
                  группа) vs обобщённый буст γ=1/√(1−β²) = role-limit (√3 при β=½).
      Elements  : рациональные γ,s,β; тройки 3-4-5, 8-15-17; инвариант 1 (L1+P4).
    ДИАГНОСТИКА (P4): СТО Element-сторонна на пифагоровых бустах (рациональная точка гиперболы =
    тройка); замкнутая группа (инвариант мультипликативен). Обобщённый буст = role-limit γ (√3, ④).
    Одна тройка 3-4-5 = точка окружности (Пифагор) и гиперболы (Лоренц).

    STATUS: 6 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lia ZArith Lqa.
From ToS Require Import analysis.Sqrt3Irrational.

Open Scope Q_scope.

(* ===================================================================== *)
(*  A boost is the pair (γ, s) with s = γβ; it is VALID iff γ²−s² = 1.    *)
(*  Composition is the matrix product of [[γ,s],[s,γ]].                    *)
(* ===================================================================== *)

(** The β=3/5 boost is a rational hyperbola point: γ=5/4, s=3/4, γ²−s²=1. *)
Lemma boost_345 : (5#4) * (5#4) - (3#4) * (3#4) == 1.
Proof. vm_compute. reflexivity. Qed.

(** ★ Rational boosts are CLOSED under composition: the invariant γ²−s²=1 is a
    multiplicative norm form, so composing two boosts on the unit hyperbola lands on
    it again.  This is the Element-side relativistic velocity group. *)
Theorem boost_compose_valid : forall g1 s1 g2 s2 : Q,
  g1 * g1 - s1 * s1 == 1 ->
  g2 * g2 - s2 * s2 == 1 ->
  (g1*g2 + s1*s2) * (g1*g2 + s1*s2) - (g1*s2 + s1*g2) * (g1*s2 + s1*g2) == 1.
Proof.
  intros g1 s1 g2 s2 H1 H2.
  assert (Key : (g1*g2 + s1*s2) * (g1*g2 + s1*s2) - (g1*s2 + s1*g2) * (g1*s2 + s1*g2)
              == (g1*g1 - s1*s1) * (g2*g2 - s2*s2)) by ring.
  rewrite Key, H1, H2. ring.
Qed.

(** Composing the 3-4-5 boost with itself gives the 8-15-17 boost: γ'=17/8, s'=15/8,
    still a rational hyperbola point. *)
Theorem boost_compose_345 :
  ((5#4)*(5#4) + (3#4)*(3#4) == 17#8)            (* γ' = γ₁γ₂+s₁s₂ *)
  /\ ((5#4)*(3#4) + (3#4)*(5#4) == 15#8)          (* s' = γ₁s₂+s₁γ₂ *)
  /\ ((17#8)*(17#8) - (15#8)*(15#8) == 1).        (* valid hyperbola point *)
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(*  A generic boost has an irrational γ — a role-limit (via √3)           *)
(* ===================================================================== *)

(** At β=1/2 the Lorentz factor satisfies γ²=4/3, which has no rational root: γ is a
    role-limit — the same √3 as the 60° point (④).  So rational velocity ≠ rational
    boost; γ generically leaves ℚ. *)
Theorem boost_half_role_limit : ~ (exists q : Q, q * q == 4#3).
Proof.
  intros [q Hq]. apply sqrt3_not_in_Q. exists (3 * q * (1#2)).
  assert (H : (3 * q * (1#2)) * (3 * q * (1#2)) == (9#4) * (q * q)) by ring.
  rewrite H, Hq. vm_compute. reflexivity.
Qed.

(* ===================================================================== *)
(*  The circle/hyperbola duality of the 3-4-5 triple                      *)
(* ===================================================================== *)

(** One triple, two conics: 3²+4²=5² (the Pythagorean CIRCLE point — rotations,
    Bell) and 5²−3²=4² (the Lorentz HYPERBOLA point — boosts). *)
Theorem pythagorean_lorentz_duality :
  (3 * 3 + 4 * 4 = 5 * 5)%Z /\ (5 * 5 - 3 * 3 = 4 * 4)%Z.
Proof. split; reflexivity. Qed.

(* ===================================================================== *)
(*  Synthesis                                                             *)
(* ===================================================================== *)

(** Special relativity split by the finitization boundary:
      (a) the β=3/5 boost is a rational hyperbola point (γ=5/4, γ²−s²=1);
      (b) rational boosts are CLOSED under composition (the Element-side group — the
          invariant is a multiplicative norm form);
      (c) a generic boost (β=1/2) has an irrational γ (γ²=4/3, a role-limit via √3);
      (d) the 3-4-5 triple is both a Pythagorean circle point and a Lorentz hyperbola
          point — one Element, two conics. *)
Theorem lorentz_synthesis :
  ((5#4) * (5#4) - (3#4) * (3#4) == 1)
  /\ (forall g1 s1 g2 s2 : Q,
        g1*g1 - s1*s1 == 1 -> g2*g2 - s2*s2 == 1 ->
        (g1*g2+s1*s2)*(g1*g2+s1*s2) - (g1*s2+s1*g2)*(g1*s2+s1*g2) == 1)
  /\ ~ (exists q : Q, q * q == 4#3)
  /\ (3*3 + 4*4 = 5*5)%Z /\ (5*5 - 3*3 = 4*4)%Z.
Proof.
  split; [ exact boost_345 | ].
  split; [ exact boost_compose_valid | ].
  split; [ exact boost_half_role_limit | ].
  exact pythagorean_lorentz_duality.
Qed.
