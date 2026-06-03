(** * RationalSphere.v — rational points on the unit sphere x²+y²+z²=1 (= integer
      Pythagorean quadruples a²+b²+c²=d²).  Stereographic projection constructs them from
      rational plane points (Element side, dense), while the cube's body-diagonal direction
      (1,1,1)/√3 is a role-limit (√3) — no rational point on the sphere has x=y=z.  This is
      the 3D analogue of the 45°/√2 point of the circle (PythagoreanTree.no_isosceles_pyth).

    Elements: the integer quadruples (1,2,2,3),(2,3,6,7); the stereographic formula; the
              rational coordinates (1/3,2/3,2/3) (L1 + P4)
    Roles:    Element side = the rational sphere points (the stereographic image of ℚ², a
              dense parametrized family of finite-actual rational points); role-limit = the
              irrational directions (the body-diagonal (1,1,1)/√3, no rational point with x=y=z)
    Rules:    the sphere x²+y²+z²=1; the Pythagorean quadruple a²+b²+c²=d²; stereographic
              projection (p,q) ↦ (2p,2q,p²+q²−1)/(p²+q²+1)

    THE DEEP POINT — the rational sphere points are an Element-side parametrized family, and
    the body-diagonal direction is a √3 role-limit.  Stereographic projection from the north
    pole sends a rational plane point (p,q) to the sphere point (2p,2q,p²+q²−1)/(p²+q²+1),
    and the numerators always form a Pythagorean quadruple:
      (2p)² + (2q)² + (p²+q²−1)² = (p²+q²+1)²     (`stereographic_on_sphere`, a ring identity)
    — so every (p,q) ∈ ℤ² gives a rational sphere point (Element side; dense, since
    stereographic projection covers all rational points but the pole).  Concrete points:
    (1/3,2/3,2/3) from (1,2,2,3), (2/7,3/7,6/7) from (2,3,6,7).  BUT no rational point on the
    sphere has x=y=z (`no_integer_diagonal_sphere`): that would force 3a²=d², i.e. √3 = d/a.
    So the cube's body-diagonal unit vector (1/√3,1/√3,1/√3) — on the sphere (3·⅓=1) — is a
    role-limit, never a rational point.  Element = the dense rational family; role-limit =
    the irrational directions (the body diagonal, √3).  Parallel to the circle: 45°/√2 is
    the role-limit there, the body-diagonal/√3 is the role-limit here (the SAME √3 as the
    60° point ① and the equilateral triangle).

    ============ E/R/R разбор ============
      Rules (L5): сфера x²+y²+z²=1; пифагорова четвёрка a²+b²+c²=d²; стереографическая проекция
                  (p,q)↦(2p,2q,p²+q²−1)/(p²+q²+1).
      Roles (L4): Element = рациональные точки сферы (образ ℚ² стереографически, плотный, параметризованный);
                  role-limit = иррациональные направления (телесная диагональ (1,1,1)/√3, нет рац. точки x=y=z).
      Elements  : целые четвёрки (1,2,2,3),(2,3,6,7); стереографическая формула; (1/3,2/3,2/3) (L1+P4).
    ДИАГНОСТИКА (P4): рациональные точки сферы = Element (строятся из рациональных данных); телесная диагональ
    именует √3 (role-limit). 3D-параллель окружности: 45°=√2 (PythagoreanTree) ↔ телесная диагональ=√3 (здесь);
    тот же √3, что 60°/равносторонний/LatticeEquilateral.

    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia QArith.
From ToS Require Import analysis.Sqrt3Irrational.

Open Scope Z_scope.

(* ===================================================================== *)
(*  Stereographic projection: every (p,q) gives a Pythagorean quadruple   *)
(* ===================================================================== *)

(** ★ The stereographic numerators form a Pythagorean quadruple: for ANY integers p,q,
    (2p, 2q, p²+q²−1, p²+q²+1) satisfies a²+b²+c²=d².  So (2p,2q,p²+q²−1)/(p²+q²+1) is a
    rational point of the unit sphere — the Element-side parametrization. *)
Lemma stereographic_on_sphere : forall p q : Z,
  (2*p)*(2*p) + (2*q)*(2*q) + (p*p + q*q - 1)*(p*p + q*q - 1)
  = (p*p + q*q + 1)*(p*p + q*q + 1).
Proof. intros p q. ring. Qed.

(** The stereographic denominator never vanishes, so the rational point is well-defined. *)
Lemma stereographic_denom_pos : forall p q : Z, p*p + q*q + 1 > 0.
Proof. intros p q. nia. Qed.

(* ===================================================================== *)
(*  Concrete rational sphere points (Pythagorean quadruples)              *)
(* ===================================================================== *)

(** (1/3,2/3,2/3) is on the sphere: 1²+2²+2²=3². *)
Lemma quad_122_3 : 1*1 + 2*2 + 2*2 = 3*3.
Proof. reflexivity. Qed.

(** (2/7,3/7,6/7) is on the sphere: 2²+3²+6²=7². *)
Lemma quad_236_7 : 2*2 + 3*3 + 6*6 = 7*7.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  Role-limit: the body-diagonal direction (1,1,1)/√3 is not rational    *)
(* ===================================================================== *)

(** ★ NO rational point on the sphere has x=y=z: that would force 3a²=d², i.e. √3 = d/a ∈ ℚ
    (`sqrt3_irrational_Z`).  The cube's body-diagonal unit vector (1/√3,1/√3,1/√3) — on the
    sphere since 3·⅓=1 — is a role-limit, never a rational point.  (The same √3 as the 60°
    point ① and the equilateral triangle.) *)
Theorem no_integer_diagonal_sphere : forall a d : Z, a <> 0 -> a*a + a*a + a*a <> d*d.
Proof.
  intros a d Ha Heq.
  apply (sqrt3_irrational_Z d a Ha). nia.
Qed.

(* ===================================================================== *)
(*  An explicit rational point of the sphere (over ℚ)                     *)
(* ===================================================================== *)

Open Scope Q_scope.

(** Explicitly: (1/3, 2/3, 2/3) is a rational point of the unit sphere. *)
Lemma rational_point_on_sphere :
  (1 # 3) * (1 # 3) + (2 # 3) * (2 # 3) + (2 # 3) * (2 # 3) == 1.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  Synthesis                                                            *)
(* ===================================================================== *)

(** Rational points of the unit sphere, split by the finitization boundary:
      (a) ELEMENT — stereographic projection sends every (p,q) to a Pythagorean quadruple
          (a dense parametrized family of rational sphere points);
      (b) concrete rational points (1/3,2/3,2/3) and (2/7,3/7,6/7);
      (c) ROLE-LIMIT — no rational point has x=y=z (the body-diagonal direction needs √3). *)
Theorem rational_sphere_synthesis :
  (forall p q : Z, ((2*p)*(2*p) + (2*q)*(2*q) + (p*p + q*q - 1)*(p*p + q*q - 1)
                    = (p*p + q*q + 1)*(p*p + q*q + 1))%Z)
  /\ ((1*1 + 2*2 + 2*2 = 3*3)%Z /\ (2*2 + 3*3 + 6*6 = 7*7)%Z)
  /\ (forall a d : Z, a <> 0%Z -> (a*a + a*a + a*a <> d*d)%Z)
  /\ ((1 # 3) * (1 # 3) + (2 # 3) * (2 # 3) + (2 # 3) * (2 # 3) == 1).
Proof.
  split; [ exact stereographic_on_sphere | ].
  split; [ split; [ exact quad_122_3 | exact quad_236_7 ] | ].
  split; [ exact no_integer_diagonal_sphere | exact rational_point_on_sphere ].
Qed.
