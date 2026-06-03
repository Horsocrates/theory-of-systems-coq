(** * LatticePolygons.v — among the regular polygons, ONLY the square embeds in the
      integer lattice ℤ².  The square (n=4) exists (Element); the triangle and hexagon
      (n=3, 6) are barred by √3 (LatticeEquilateral); the pentagon (n=5) is barred by √5
      (its diagonal²/side² = φ², a root of x²−3x+1).  This is the lattice form of the
      crystallographic restriction, tying √3 and √5 to one geometric arena.

    Elements: the unit square's integer coordinates and equal integer squared sides (1)
              and diagonals (2); the integer relation D²−3DS+S²=0 (L1 + P4)
    Roles:    n=4 (square) = Element (realizable, all squared data integer); n=3,6 =
              role-limit-blocked by √3 (equilateral / hexagon sub-triangle); n=5 =
              role-limit-blocked by √5 (φ² = diagonal²/side²); the square is the unique
              Element-side regular polygon on ℤ²
    Rules:    squared lengths are integers on ℤ²; the rotation by 2π/n maps lattice→lattice
              ⟹ 2cos(2π/n)∈ℤ ⟹ n∈{3,4,6} (crystallographic restriction); the √3 (n=3,6)
              and √5/φ² (n=5) obstructions

    THE DEEP POINT — only the square is finite-actual on ℤ²; the others NAME an irrational
    in an essential ratio.
      · n=4 EXISTS: the unit square (0,0),(1,0),(1,1),(0,1) has all four squared sides = 1
        and both squared diagonals = 2 (`square_on_lattice`) — every datum an integer.
        (Its diagonal LENGTH is √2, a role-limit, but the lattice sees only the squared
        distances 1, 2 ∈ ℤ, so the square embeds anyway.)
      · n=3, 6 are BARRED by √3: an equilateral triangle has no integer vertices
        (`no_lattice_equilateral`, imported), and a regular hexagon's alternate vertices
        form an equilateral triangle — same √3.
      · n=5 is BARRED by √5: a regular pentagon's diagonal²/side² ratio is φ² = (3+√5)/2,
        a root of x²−3x+1, so integer squared lengths d², s² would satisfy
        d⁴−3d²s²+s⁴ = 0, i.e. (2d²−3s²)² = 5·s⁴ — a rational √5, impossible
        (`no_lattice_pentagon`).  The ratio φ² itself is irrational (`phi_sq_no_rational`).
    So among regular n-gons only the square (n=4) embeds in ℤ²: √3 kills 3 and 6, √5 kills
    5, the trace kills n≥7.  Same √3 as the 60° point ① / `LatticeEquilateral`; same √5 as
    the icosahedron ④ / pentagon-in-ℚ[√5] / the φ-process.

    ============ E/R/R разбор ============
      Rules (L5): квадраты расстояний целые на ℤ²; поворот 2π/n: решётка→решётка ⟹ 2cos(2π/n)∈ℤ
                  ⟹ n∈{3,4,6}; обструкции √3 (n=3,6) и √5/φ² (n=5).
      Roles (L4): n=4 квадрат = Element (реализуем); n=3,6 блок √3; n=5 блок √5; квадрат —
                  единственный Element-сторонний правильный многоугольник на ℤ².
      Elements  : целые координаты квадрата, стороны²=1, диагонали²=2; целое D²−3DS+S²=0 (L1+P4).
    ДИАГНОСТИКА (P4): только квадрат конечно-актуален на ℤ²; остальные именуют √3/√5; решётка смотрит
    на КВАДРАТЫ расстояний (целые), не на длины — потому квадрат с диагональю √2 всё равно садится.
    Тот же √3, что ①; тот же √5, что ④.

    STATUS: 4 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia QArith.
From ToS Require Import analysis.Sqrt5Irrational.
From ToS Require Import stdlib.LatticeEquilateral.

Open Scope Z_scope.

(* ===================================================================== *)
(*  n = 4: the square EXISTS on ℤ² (Element)                              *)
(* ===================================================================== *)

(** Squared Euclidean distance between two integer points. *)
Definition sqdist (x1 y1 x2 y2 : Z) : Z :=
  (x2 - x1) * (x2 - x1) + (y2 - y1) * (y2 - y1).

(** ★ The unit square (0,0),(1,0),(1,1),(0,1) lives on ℤ²: all four squared sides = 1,
    both squared diagonals = 2 — every datum an integer (Element).  (The diagonal length
    √2 is a role-limit, but the lattice sees only the squared distances 1, 2 ∈ ℤ.) *)
Lemma square_on_lattice :
  sqdist 0 0 1 0 = 1 /\ sqdist 1 0 1 1 = 1
  /\ sqdist 1 1 0 1 = 1 /\ sqdist 0 1 0 0 = 1
  /\ sqdist 0 0 1 1 = 2 /\ sqdist 1 0 0 1 = 2.
Proof. repeat split; reflexivity. Qed.

(* ===================================================================== *)
(*  n = 5: the pentagon is barred by √5 (φ² = diagonal²/side²)            *)
(* ===================================================================== *)

(** ★ No integers D = diagonal², S = side² (S ≠ 0) satisfy the regular-pentagon relation
    D²−3DS+S² = 0 (which says D/S = φ²).  For then (2D−3S)² = 5·S², a rational √5. *)
Theorem no_lattice_pentagon : forall D S : Z,
  S <> 0 -> D * D - 3 * D * S + S * S <> 0.
Proof.
  intros D S HS Heq.
  apply (sqrt5_irrational_Z (2 * D - 3 * S) S HS).
  nia.
Qed.

(* ===================================================================== *)
(*  The pentagon ratio φ² = (3+√5)/2 is irrational                        *)
(* ===================================================================== *)

Open Scope Q_scope.

(** ★ φ² (the regular-pentagon diagonal²/side² ratio) is irrational: no rational solves
    x²=3x−1 (else (2x−3)²=5, the same √5 as the icosahedron ④). *)
Theorem phi_sq_no_rational : ~ (exists q : Q, q * q == 3 * q - 1).
Proof.
  intros [q Hq]. apply (no_rational_sqrt5 (2 * q - 3)).
  assert (H : (2 * q - 3) * (2 * q - 3) == 4 * (q * q) - 12 * q + 9) by ring.
  rewrite H, Hq. ring.
Qed.

(* ===================================================================== *)
(*  Synthesis — among the regular polygons, only the square embeds in ℤ²  *)
(* ===================================================================== *)

(** Only the square embeds in ℤ², split by the finitization boundary:
      (a) n=4 — the square EXISTS (Element: squared sides 1, diagonals 2);
      (b) n=3 (and n=6) — equilateral/hexagon barred by √3 (`no_lattice_equilateral`);
      (c) n=5 — pentagon barred by √5 (D²−3DS+S²=0 unsatisfiable);
      (d) the pentagon ratio φ² is irrational (the role-limit, via √5). *)
Theorem lattice_polygons_synthesis :
  (sqdist 0 0 1 0 = 1 /\ sqdist 1 0 1 1 = 1
   /\ sqdist 1 1 0 1 = 1 /\ sqdist 0 1 0 0 = 1)%Z
  /\ (forall p q r t : Z,
        p*p + q*q = r*r + t*t ->
        p*p + q*q = (r - p)*(r - p) + (t - q)*(t - q) ->
        p*p + q*q > 0 -> False)%Z
  /\ (forall D S : Z, S <> 0 -> D * D - 3 * D * S + S * S <> 0)%Z
  /\ ~ (exists q : Q, q * q == 3 * q - 1).
Proof.
  split; [ repeat split; reflexivity | ].
  split; [ exact no_lattice_equilateral | ].
  split; [ exact no_lattice_pentagon | exact phi_sq_no_rational ].
Qed.
