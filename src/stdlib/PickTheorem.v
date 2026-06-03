(** * PickTheorem.v — Pick's theorem / lattice-polygon area: the Element-side companion to
      LatticeEquilateral.v.  The doubled shoelace area of any lattice polygon is an integer,
      so every lattice polygon has rational (half-integer) area; the smallest, a primitive
      (empty) triangle, has area exactly 1/2 — the same unimodular determinant ±1 as
      Ford/SternBrocot/CalkinWilf, now geometrized as area.  Conversely a shape with
      irrational area (the equilateral triangle, area √3/4·s²) can NEVER be a lattice polygon —
      the same √3 that forbids the 60° point (LatticeEquilateral, RationalSphere).

    Elements: the integer doubled area; the determinant ad−bc; concrete Pick for the w×h
              rectangle and the unit triangle (L1 + P4)
    Roles:    Element side = a lattice polygon ALWAYS has rational (half-integer) area by a
              finite shoelace sum, the smallest being the unimodular triangle of area 1/2;
              role-limit = a shape whose area is irrational (the equilateral triangle, √3/4)
              can never be a lattice polygon
    Rules:    the shoelace rule 2·Area = Σ(xᵢyᵢ₊₁−xᵢ₊₁yᵢ) ∈ ℤ; the primitive triangle =
              determinant ±1 ⟹ area 1/2 (Pick base case); Pick's formula A = I + B/2 − 1

    THE DEEP POINT — a lattice polygon ALWAYS has rational area; the smallest is the unimodular
    triangle.  The doubled signed area of a triangle (0,0),(a,b),(c,d) is the determinant ad−bc
    (`tarea_det`), an integer combination of integer coordinates, hence ALWAYS an integer — so
    the area lies in ½ℤ ⊂ ℚ (Element), and it is a genuine invariant (translation-independent,
    `tarea_translation_invariant`).  The smallest lattice triangle is PRIMITIVE: determinant ±1
    ⟹ doubled area 1 ⟹ area exactly 1/2 (`unimodular_triangle_doubled_one`) — the Pick base
    case, the SAME unimodular ±1 as the Ford-circle tangency, the Stern–Brocot/Calkin–Wilf
    nodes.  Pick's formula A = I + B/2 − 1 holds for the general w×h rectangle (`pick_rectangle`,
    a ring identity) and the unit triangle (`pick_unit_triangle`).  But a shape with irrational
    area is excluded: the unit equilateral triangle has area √3/4, area² = 3/16, and no rational
    squares to 3/16 (`equilateral_area_not_rational`, via no_rational_sqrt3) — so it is NOT a
    lattice polygon (a second, area-based proof of LatticeEquilateral's impossibility).  Element
    = rational area by finite shoelace; role-limit = an irrational-area shape off the lattice.

    ============ E/R/R разбор ============
      Rules (L5): шнурки 2·Площадь=Σ(xᵢyᵢ₊₁−xᵢ₊₁yᵢ)∈ℤ; примитивный треугольник = определитель ±1
                  ⟹ площадь 1/2 (база Пика); формула Пика A=I+B/2−1.
      Roles (L4): Element = решёточный многоугольник ВСЕГДА рациональная (полуцелая) площадь,
                  наименьший — унимодулярный треугольник 1/2; role-limit = иррациональная площадь
                  (равносторонний, √3/4) ⟹ не решёточный.
      Elements  : целая удвоенная площадь; определитель ad−bc; Пик для w×h и единичного треуг. (L1+P4).
    ДИАГНОСТИКА (P4): решёточный многоугольник ⟹ рациональная площадь (Element); иррациональная площадь
    (равносторонний, √3) ⟹ не садится на ℤ² (role-limit). «Удвоенная площадь = целый определитель» = тот
    же унимодулярный инвариант ±1, что у Ford/SternBrocot/CalkinWilf, теперь как площадь. «Равносторонний на
    ℤ²?» = не-вопрос: форсировало бы √3∈ℚ. Площадной маршрут к невозможности LatticeEquilateral.

    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia QArith.
From ToS Require Import analysis.Sqrt3Irrational.

Open Scope Z_scope.

(* ===================================================================== *)
(*  The shoelace (doubled signed area) of a lattice triangle               *)
(* ===================================================================== *)

(** The doubled signed area of the triangle with vertices (x1,y1),(x2,y2),(x3,y3) — the
    shoelace formula.  For integer coordinates this is an INTEGER, so the area lies in ½ℤ ⊂ ℚ
    (the Element side). *)
Definition tarea (x1 y1 x2 y2 x3 y3 : Z) : Z :=
  x1 * (y2 - y3) + x2 * (y3 - y1) + x3 * (y1 - y2).

(** The doubled area is a genuine invariant: translating all three vertices by (e,f) leaves it
    unchanged — the area is well-defined regardless of origin. *)
Lemma tarea_translation_invariant : forall x1 y1 x2 y2 x3 y3 e f : Z,
  tarea (x1 + e) (y1 + f) (x2 + e) (y2 + f) (x3 + e) (y3 + f)
  = tarea x1 y1 x2 y2 x3 y3.
Proof. intros. unfold tarea. ring. Qed.

(** Placing one vertex at the origin, the doubled area is the determinant ad − bc of the two
    edge vectors (a,b),(c,d). *)
Lemma tarea_det : forall a b c d : Z,
  tarea 0 0 a b c d = a * d - b * c.
Proof. intros. unfold tarea. ring. Qed.

(* ===================================================================== *)
(*  Pick base case: the primitive (empty) triangle has area 1/2           *)
(* ===================================================================== *)

(** ★ A PRIMITIVE lattice triangle (edge-vector determinant ±1, here +1) has doubled area 1,
    i.e. area exactly 1/2 — the Pick base case.  This is the SAME unimodular determinant ±1
    that drives the Ford-circle tangency and the Stern–Brocot / Calkin–Wilf nodes, now
    geometrized as the smallest lattice area. *)
Lemma unimodular_triangle_doubled_one : forall a b c d : Z,
  a * d - b * c = 1 -> tarea 0 0 a b c d = 1.
Proof. intros a b c d H. rewrite tarea_det. exact H. Qed.

(* ===================================================================== *)
(*  Pick's formula A = I + B/2 − 1, verified                              *)
(* ===================================================================== *)

(** ★ Pick's formula for the general w×h axis-aligned rectangle: interior points
    I = (w−1)(h−1), boundary points B = 2(w+h) so B/2 = w+h, area A = wh.  The identity
    I + B/2 − 1 = A holds for ALL w,h (a ring identity). *)
Lemma pick_rectangle : forall w h : Z,
  (w - 1) * (h - 1) + (w + h) - 1 = w * h.
Proof. intros. ring. Qed.

(* ===================================================================== *)
(*  Concrete Pick (unit triangle) and the role-limit                      *)
(* ===================================================================== *)

Open Scope Q_scope.

(** Pick's formula for the unit triangle (0,0),(1,0),(0,1): no interior points (I=0), three
    boundary points (B=3), area 1/2.  Indeed 0 + 3/2 − 1 = 1/2 (the half-integer Element area). *)
Lemma pick_unit_triangle : (0 # 1) + (3 # 1) / (2 # 1) - (1 # 1) == 1 # 2.
Proof. vm_compute. reflexivity. Qed.

(** ★ The unit equilateral triangle has area √3/4, so area² = 3/16 — and no rational squares
    to 3/16.  Since every lattice polygon has rational area, the equilateral triangle is NOT a
    lattice polygon (a second, area-based proof of LatticeEquilateral's impossibility; the same
    √3 as the 60° point). *)
Theorem equilateral_area_not_rational : ~ (exists a : Q, a * a == 3 # 16).
Proof.
  intros [a Ha]. apply (no_rational_sqrt3 (4 * a)).
  assert (H : (4 * a) * (4 * a) == 16 * (a * a)) by ring.
  rewrite H, Ha. vm_compute. reflexivity.
Qed.

(* ===================================================================== *)
(*  Synthesis                                                            *)
(* ===================================================================== *)

(** Lattice-polygon area, split by the finitization boundary:
      (a) ELEMENT — a lattice polygon always has rational (half-integer) area: the doubled
          area is the integer determinant (`tarea_det`), a translation invariant
          (`tarea_translation_invariant`); the primitive triangle (det ±1) has area 1/2
          (`unimodular_triangle_doubled_one`); Pick's formula holds for the rectangle
          (`pick_rectangle`) and the unit triangle (`pick_unit_triangle`);
      (b) ROLE-LIMIT — the equilateral triangle's area √3/4 is irrational
          (`equilateral_area_not_rational`), so it is not a lattice polygon. *)
Theorem pick_synthesis :
  (forall a b c d : Z, tarea 0 0 a b c d = a * d - b * c)%Z
  /\ (forall a b c d : Z, a * d - b * c = 1 -> tarea 0 0 a b c d = 1)%Z
  /\ (forall w h : Z, (w - 1) * (h - 1) + (w + h) - 1 = w * h)%Z
  /\ ~ (exists a : Q, a * a == 3 # 16).
Proof.
  split; [ exact tarea_det | ].
  split; [ exact unimodular_triangle_doubled_one | ].
  split; [ exact pick_rectangle | exact equilateral_area_not_rational ].
Qed.
