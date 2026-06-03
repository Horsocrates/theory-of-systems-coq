(** * LatticeEquilateral.v — NO equilateral triangle has all three vertices on the
      integer lattice ℤ².  A lattice triangle's area is rational (the shoelace formula
      gives integer/2 — Element side), but an equilateral triangle's area is (√3/4)·side²,
      which NAMES √3 (role-limit).  Over ℤ the two are incompatible: the equilateral
      conditions force (pt−rq)² = 3·(pr+qt)² with pr+qt ≠ 0, i.e. √3 ∈ ℚ — impossible.

      This is the 2D shadow of the crystallographic restriction (④): "no 3-/6-fold lattice
      symmetry" is the same √3 that forbids the rational 60° point (①) and makes the
      equilateral area irrational.

    Elements: the integer edge vectors (p,q)=B−A, (r,t)=C−A; the integer doubled area
              D=pt−rq; the integer S=pr+qt; the integer side² L=p²+q² (L1 + P4)
    Roles:    Element side = a lattice triangle's area is rational (shoelace = integer/2;
              lattice triangles exist, e.g. the unit right triangle, area 1/2); role-limit
              = the √3 in the equilateral area (√3/4)·L; their clash ⟹ NO lattice equilateral
    Rules:    the shoelace 2·Area = |pt−rq|; the Lagrange/Brahmagupta identity
              (pr+qt)²+(pt−rq)²=(p²+q²)(r²+t²); equilateral |AB|²=|AC|²=|BC|²; area=(√3/4)·side²

    THE DEEP POINT — the obstruction is a √3 role-limit.  For integer edge vectors the
    doubled area D=pt−rq is an integer (rational area — Element).  But the equilateral
    conditions |AB|²=|AC|² and |AB|²=|BC|² algebraically force (via the Lagrange identity
    and 2(pr+qt)=p²+q²) the relation
        (pt−rq)² = 3·(pr+qt)²     with pr+qt ≠ 0     (`equilateral_forces_3sq`)
    — exactly a rational square root of 3, which `sqrt3_irrational_Z` forbids.  So no
    equilateral triangle has integer (hence no rational) vertices (`no_lattice_equilateral`).
    Lattice triangles DO exist (the unit right triangle, `lattice_right_triangle`, doubled
    area 1 ⟹ area 1/2 — Element); only the equilateral one is barred, because its area
    (√3/4) is a role-limit (`equilateral_area_role_limit`: the unit equilateral's area² =
    3/16 is irrational, the same √3 as the 60° point ① and the crystallographic
    restriction ④).

    ============ E/R/R разбор ============
      Rules (L5): шнурки 2·Площадь=|pt−rq|; тождество Лагранжа (pr+qt)²+(pt−rq)²=(p²+q²)(r²+t²);
                  равносторонность |AB|²=|AC|²=|BC|²; площадь равностороннего=(√3/4)·сторона².
      Roles (L4): Element = решёточная площадь рациональна (шнурки=целое/2; решёточные треугольники
                  существуют); role-limit = √3 в площади равностороннего; столкновение ⟹ НЕТ равностороннего.
      Elements  : целые рёберные векторы (p,q),(r,t); целое D=pt−rq; целое S=pr+qt; целое L=p²+q² (L1+P4).
    ДИАГНОСТИКА (P4): решёточная площадь = Element (рациональна); площадь равностороннего именует √3 (role-limit);
    несовместимость ⟹ равносторонний треугольник не садится на ℤ². 2D-тень кристаллографического ограничения ④;
    тот же √3, что запрещает 60° ①. «Равносторонний на ℤ²?» = не-вопрос: форсировало бы √3∈ℚ.

    STATUS: 6 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia QArith.
From ToS Require Import analysis.Sqrt3Irrational.

Open Scope Z_scope.

(* ===================================================================== *)
(*  Shoelace and the Lagrange/Brahmagupta identity                        *)
(* ===================================================================== *)

(** The (signed) doubled area of a triangle with edge vectors (p,q), (r,t) from one
    vertex.  An integer ⟹ the area pt−rq /2 is rational (Element side). *)
Definition doubled_area (p q r t : Z) : Z := p * t - r * q.

(** The Lagrange / Brahmagupta–Fibonacci identity, by ring. *)
Lemma lagrange_identity : forall p q r t : Z,
  (p*r + q*t) * (p*r + q*t) + (p*t - r*q) * (p*t - r*q)
  = (p*p + q*q) * (r*r + t*t).
Proof. intros. ring. Qed.

(* ===================================================================== *)
(*  The geometry: equilateral conditions force (pt−rq)² = 3·(pr+qt)²       *)
(* ===================================================================== *)

(** ★ The heart, purely algebraic: for integer edge vectors, the equilateral conditions
    |AB|²=|AC|² and |AB|²=|BC|² (with a nondegenerate side) force
        (pt−rq)² = 3·(pr+qt)²     and     pr+qt ≠ 0.
    From H2 and H1, 2(pr+qt) = p²+q²; the Lagrange identity then gives S²+D² = (2S)², so
    D² = 3S². *)
Lemma equilateral_forces_3sq : forall p q r t : Z,
  p*p + q*q = r*r + t*t ->
  p*p + q*q = (r - p)*(r - p) + (t - q)*(t - q) ->
  p*p + q*q > 0 ->
  (p*t - r*q) * (p*t - r*q) = 3 * ((p*r + q*t) * (p*r + q*t))
  /\ p*r + q*t <> 0.
Proof.
  intros p q r t H1 H2 Hpos.
  assert (HS : 2 * (p*r + q*t) = p*p + q*q) by nia.
  pose proof (lagrange_identity p q r t) as HL.
  rewrite <- H1 in HL.
  rewrite <- !HS in HL.
  split.
  - nia.
  - intro Hz. rewrite Hz in HS. lia.
Qed.

(* ===================================================================== *)
(*  ★ No equilateral triangle has all vertices on ℤ²                       *)
(* ===================================================================== *)

(** ★ Main theorem: integer edge vectors cannot form an equilateral triangle.  The forced
    relation (pt−rq)²=3·(pr+qt)² with pr+qt≠0 is exactly a rational √3, which
    `sqrt3_irrational_Z` forbids. *)
Theorem no_lattice_equilateral : forall p q r t : Z,
  p*p + q*q = r*r + t*t ->
  p*p + q*q = (r - p)*(r - p) + (t - q)*(t - q) ->
  p*p + q*q > 0 ->
  False.
Proof.
  intros p q r t H1 H2 Hpos.
  destruct (equilateral_forces_3sq p q r t H1 H2 Hpos) as [Hkey Hne].
  exact (sqrt3_irrational_Z (p*t - r*q) (p*r + q*t) Hne Hkey).
Qed.

(* ===================================================================== *)
(*  Element side: lattice triangles DO exist (rational area)              *)
(* ===================================================================== *)

(** A lattice triangle exists: the unit right triangle (0,0),(1,0),(0,1) has doubled area
    1, i.e. area 1/2 — a rational area (Element).  Only the equilateral one is barred. *)
Lemma lattice_right_triangle : doubled_area 1 0 0 1 = 1.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  Role-limit: the equilateral area is irrational (√3)                   *)
(* ===================================================================== *)

Open Scope Q_scope.

(** ★ The unit equilateral triangle's area is √3/4, so area² = 3/16 — no rational squares
    to 3/16 (else (4a)²=3, the same √3 as the 60° point ① and ④). *)
Theorem equilateral_area_role_limit : ~ (exists a : Q, a * a == 3 # 16).
Proof.
  intros [a Ha]. apply (no_rational_sqrt3 (4 * a)).
  assert (H : (4 * a) * (4 * a) == 16 * (a * a)) by ring.
  rewrite H, Ha. vm_compute. reflexivity.
Qed.

(* ===================================================================== *)
(*  Synthesis                                                             *)
(* ===================================================================== *)

(** The lattice-equilateral obstruction, split by the finitization boundary:
      (a) ELEMENT — lattice triangles exist with rational area (unit right triangle);
      (b) GEOMETRY — equilateral conditions force (pt−rq)²=3·(pr+qt)², pr+qt≠0;
      (c) ★ NO lattice equilateral triangle (the forced rational √3 is impossible);
      (d) ROLE-LIMIT — the equilateral area² = 3/16 is irrational (√3). *)
Theorem lattice_equilateral_synthesis :
  (doubled_area 1 0 0 1 = 1)%Z
  /\ (forall p q r t : Z,
        p*p + q*q = r*r + t*t ->
        p*p + q*q = (r - p)*(r - p) + (t - q)*(t - q) ->
        p*p + q*q > 0 ->
        (p*t - r*q) * (p*t - r*q) = 3 * ((p*r + q*t) * (p*r + q*t)) /\ p*r + q*t <> 0)%Z
  /\ (forall p q r t : Z,
        p*p + q*q = r*r + t*t ->
        p*p + q*q = (r - p)*(r - p) + (t - q)*(t - q) ->
        p*p + q*q > 0 -> False)%Z
  /\ ~ (exists a : Q, a * a == 3 # 16).
Proof.
  split; [ reflexivity | ].
  split; [ exact equilateral_forces_3sq | ].
  split; [ exact no_lattice_equilateral | exact equilateral_area_role_limit ].
Qed.
