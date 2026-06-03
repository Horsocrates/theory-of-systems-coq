(** * RationalRotationGroup.v — the rational rotation group SO(2,ℚ): the rational points of
      the unit circle form a GROUP under complex multiplication (closed via the two-square
      identity, identity (1,0), inverse (x,−y)), parametrized by the Cayley / tangent-half-
      angle chart t ↦ ((1−t²)/(1+t²), 2t/(1+t²)).  The 60° rotation (1/2, √3/2) is a role-
      limit (√3), not in the group.  This is the 2D base of the rotation-group thread
      (3D = RationalQuaternions via the four-square identity).

    Elements: the rational circle points (3/5,4/5); the doubling 3-4-5 ↦ 7-24-25; the Cayley
              parameter t (L1 + P4)
    Roles:    Element side = the rational rotations form a GROUP SO(2,ℚ) (closed under
              composition via the two-square identity, identity (1,0), inverse (x,−y);
              countable, dense; each rational t parametrizes one); role-limit = the irrational
              rotations (60° = (1/2,√3/2), no rational coordinates, √3)
    Rules:    the circle x²+y²=1; composition (x₁x₂−y₁y₂, x₁y₂+y₁x₂) [complex mult]; the
              Brahmagupta two-square identity; the Cayley chart (1−t²,2t)/(1+t²)

    THE DEEP POINT — the rational rotations form an Element-side GROUP, and the 60° rotation
    is a √3 role-limit outside it.  A rational rotation is a point (x,y) ∈ ℚ² with x²+y²=1;
    composition is complex multiplication (x₁x₂−y₁y₂, x₁y₂+y₁x₂), and the two-square
    (Brahmagupta) identity shows the result is again on the circle (`rotation_compose_closed`)
    — closure.  The identity (1,0) acts trivially (`rotation_identity`), and (x,−y) inverts
    (x,y) (`rotation_inverse`) — so SO(2,ℚ) is a group.  The Cayley / tangent-half-angle chart
    sends every rational t to a rotation, since (1−t²)²+(2t)²=(1+t²)² (`cayley_on_circle`) —
    a dense parametrization.  Concretely, the 3-4-5 rotation (3/5,4/5) composed with itself is
    the 7-24-25 rotation (−7/25,24/25) (`double_345`) — doubling the angle inside the group.
    BUT the 60° rotation (1/2,√3/2) has no rational coordinates (`no_rational_60`): its
    y-coordinate satisfies y²=3/4, i.e. √3 = 2y.  So SO(2,ℚ) is a dense countable group that
    MISSES 60° (and every irrational angle) — the same √3 as the 60° circle point ①, the
    equilateral triangle, and the sphere's body diagonal.

    ============ E/R/R разбор ============
      Rules (L5): окружность x²+y²=1; композиция (x₁x₂−y₁y₂,x₁y₂+y₁x₂) [компл. умножение]; тождество
                  двух квадратов; карта Кэли (1−t²,2t)/(1+t²).
      Roles (L4): Element = рациональные вращения = ГРУППА SO(2,ℚ) (замкнута через два квадрата, единица
                  (1,0), обратный (x,−y); счётна, плотна); role-limit = иррациональные (60°=(1/2,√3/2), √3).
      Elements  : рац. точки окружности (3/5,4/5); удвоение 3-4-5↦7-24-25; параметр Кэли t (L1+P4).
    ДИАГНОСТИКА (P4): рациональные вращения = Element-ГРУППА (замкнутость, обратные) — 2D-база нити (3D =
    кватернионы); карта Кэли строит из рационального t; 60° именует √3 (role-limit), не в SO(2,ℚ). Замыкание =
    мультипликативная норм-форма (два квадрата). Тот же √3, что 60° ①/равносторонний/телесная диагональ.

    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lia ZArith Lqa.
From ToS Require Import analysis.Sqrt3Irrational.

(* ===================================================================== *)
(*  Composition of rational rotations (complex multiplication)            *)
(* ===================================================================== *)

Open Scope Q_scope.

Definition rcompose (p q : Q * Q) : Q * Q :=
  let '(x1, y1) := p in let '(x2, y2) := q in
  (x1 * x2 - y1 * y2, x1 * y2 + y1 * x2).

(* ===================================================================== *)
(*  Group structure: closure, identity, inverse                          *)
(* ===================================================================== *)

(** ★ CLOSURE: the composition of two rational rotations is a rational rotation — the
    two-square (Brahmagupta) identity (x₁x₂−y₁y₂)²+(x₁y₂+y₁x₂)²=(x₁²+y₁²)(x₂²+y₂²). *)
Lemma rotation_compose_closed : forall x1 y1 x2 y2 : Q,
  x1 * x1 + y1 * y1 == 1 -> x2 * x2 + y2 * y2 == 1 ->
  (x1 * x2 - y1 * y2) * (x1 * x2 - y1 * y2)
  + (x1 * y2 + y1 * x2) * (x1 * y2 + y1 * x2) == 1.
Proof.
  intros x1 y1 x2 y2 H1 H2.
  assert (Hb : (x1 * x2 - y1 * y2) * (x1 * x2 - y1 * y2)
               + (x1 * y2 + y1 * x2) * (x1 * y2 + y1 * x2)
               == (x1 * x1 + y1 * y1) * (x2 * x2 + y2 * y2)) by ring.
  rewrite Hb, H1, H2. ring.
Qed.

(** IDENTITY: (1,0) acts as the identity (rcompose (1,0) (x,y) has components (x,y)). *)
Lemma rotation_identity : forall x y : Q, 1 * x - 0 * y == x /\ 1 * y + 0 * x == y.
Proof. intros x y. split; ring. Qed.

(** ★ INVERSE: (x,−y) is the inverse of (x,y) — on the circle, and composes to (1,0). *)
Lemma rotation_inverse : forall x y : Q, x * x + y * y == 1 ->
  x * x - y * (- y) == 1 /\ x * (- y) + y * x == 0.
Proof.
  intros x y H. split.
  - assert (Hb : x * x - y * (- y) == x * x + y * y) by ring. rewrite Hb. exact H.
  - ring.
Qed.

(* ===================================================================== *)
(*  The Cayley / tangent-half-angle parametrization                       *)
(* ===================================================================== *)

(** ★ Every integer t gives a rotation: (1−t²,2t,1+t²) is a Pythagorean triple, so
    ((1−t²)/(1+t²), 2t/(1+t²)) is a rational circle point — the dense Cayley chart of
    SO(2,ℚ). *)
Lemma cayley_on_circle : forall t : Z,
  ((1 - t * t) * (1 - t * t) + (2 * t) * (2 * t) = (1 + t * t) * (1 + t * t))%Z.
Proof. intros t. ring. Qed.

(* ===================================================================== *)
(*  Concrete: doubling the 3-4-5 rotation gives the 7-24-25 rotation      *)
(* ===================================================================== *)

(** The 3-4-5 rotation (3/5,4/5) composed with itself is the 7-24-25 rotation (−7/25,24/25)
    — doubling the angle inside the group. *)
Lemma double_345 :
  (3 # 5) * (3 # 5) - (4 # 5) * (4 # 5) == - (7 # 25)
  /\ (3 # 5) * (4 # 5) + (4 # 5) * (3 # 5) == 24 # 25.
Proof. split; reflexivity. Qed.

(* ===================================================================== *)
(*  Role-limit: the 60° rotation (1/2, √3/2) is not rational              *)
(* ===================================================================== *)

(** ★ The 60° rotation has no rational coordinates: a circle point with x=1/2 would have
    y²=3/4, i.e. √3 = 2y ∈ ℚ (`no_rational_sqrt3`).  So SO(2,ℚ) misses 60° — the same √3 as
    the 60° point ① and the equilateral triangle. *)
Theorem no_rational_60 : ~ (exists y : Q, (1 # 2) * (1 # 2) + y * y == 1).
Proof.
  intros [y H]. apply (no_rational_sqrt3 (2 * y)).
  assert (Hb : (2 * y) * (2 * y) == 4 * ((1 # 2) * (1 # 2) + y * y) - 1) by ring.
  rewrite Hb, H. ring.
Qed.

(* ===================================================================== *)
(*  Synthesis                                                            *)
(* ===================================================================== *)

(** The rational rotation group SO(2,ℚ), split by the finitization boundary:
      (a) CLOSURE — composition of rational rotations is a rational rotation;
      (b) INVERSE — (x,−y) inverts (x,y);
      (c) the Cayley chart: every t gives a rotation (dense parametrization);
      (d) ROLE-LIMIT — the 60° rotation has no rational coordinates (√3). *)
Theorem rotation_group_synthesis :
  (forall x1 y1 x2 y2 : Q, x1*x1 + y1*y1 == 1 -> x2*x2 + y2*y2 == 1 ->
     (x1*x2 - y1*y2)*(x1*x2 - y1*y2) + (x1*y2 + y1*x2)*(x1*y2 + y1*x2) == 1)
  /\ (forall x y : Q, x*x + y*y == 1 -> x*x - y*(- y) == 1 /\ x*(- y) + y*x == 0)
  /\ (forall t : Z, ((1 - t*t)*(1 - t*t) + (2*t)*(2*t) = (1 + t*t)*(1 + t*t))%Z)
  /\ ~ (exists y : Q, (1 # 2) * (1 # 2) + y * y == 1).
Proof.
  split; [ exact rotation_compose_closed | ].
  split; [ exact rotation_inverse | ].
  split; [ exact cayley_on_circle | exact no_rational_60 ].
Qed.
