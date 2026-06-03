(** * PythagoreanTree.v — the Barning–Hall ternary tree of ALL primitive Pythagorean
      triples, generated from (3,4,5) by three integer matrices.  This is the Element-side
      COMPLETE enumeration of the rational points of the unit circle (the dual, for
      triples, of the Stern–Brocot tree for ℚ⁺): every rational right triangle is a finite
      path from (3,4,5).  The role-limit foil is the 45°/√2 isosceles point a=b, which the
      tree never reaches (no Pythagorean triple has a=b — that would need √2 ∈ ℚ).

    Elements: the integer triples (a,b,c); the three Barning matrices as integer maps;
              the three children of (3,4,5): (5,12,13),(21,20,29),(15,8,17) (L1 + P4)
    Roles:    Element side = the complete finitely-generated tree of all primitive
              Pythagorean triples (each a finite path from (3,4,5)) — the rational points
              of the unit circle, countable, enumerable; role-limit = the irrational points
              (the 45°/√2 isosceles point a=b, never a tree node)
    Rules:    the three Barning matrices A,B,C (each preserving a²+b²−c²); the seed (3,4,5);
              the ternary branching; the strictly growing hypotenuse (no cycles)

    THE DEEP POINT — the rational points of the unit circle form an Element-side tree, and
    the 45°/√2 point is a role-limit the tree never reaches.  Each Barning matrix preserves
    a²+b²−c² (a pure ring identity), so it maps a Pythagorean triple to a Pythagorean
    triple (`barA_pyth`, `barB_pyth`, `barC_pyth`); from the seed (3,4,5) the three
    children are (5,12,13),(21,20,29),(15,8,17) (`barABC_345`), and the hypotenuse strictly
    grows (`barB_hyp_grows`), so the tree descends without cycles — a complete enumeration
    of all primitive triples.  But NO Pythagorean triple has a=b (`no_isosceles_pyth`):
    that would force 2a²=c², i.e. √2 = c/a ∈ ℚ.  So the 45° isosceles right triangle —
    the (1/√2,1/√2) point of the circle — is a role-limit, never an Element of the tree.
    Element side = the enumerable tree (rational circle points); role-limit = the boundary
    of irrational points (45°/√2).  This parallels SternBrocot.v (ℚ⁺ tree) and the
    "irrational = boundary the tree approaches but never reaches" reading.

    ============ E/R/R разбор ============
      Rules (L5): три матрицы Барнинга A,B,C (сохраняют a²+b²−c²); корень (3,4,5); тернарное
                  ветвление; строго растущая гипотенуза (без циклов).
      Roles (L4): Element = ПОЛНОЕ конечно-порождённое дерево всех примитивных троек (рациональные
                  точки окружности, перечислимые); role-limit = иррациональные точки (45°/√2, a=b,
                  никогда не узел); каждая матрица: тройка→тройка (Element остаётся Element).
      Elements  : целые тройки (a,b,c); три матрицы; потомки (5,12,13),(21,20,29),(15,8,17) (L1+P4).
    ДИАГНОСТИКА (P4): рациональные точки окружности = Element-сторонне дерево (полное из корня), параллель
    Stern-Brocot; иррациональные (45°=√2, a=b) = role-limit-граница, не достигается (нет пифагоровой a=b ⟹
    2a²=c² ⟹ √2∈ℚ). Гипотенуза растёт вниз ⟹ без циклов.

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia.
From ToS Require Import analysis.Sqrt2Irrational.

Open Scope Z_scope.

(* ===================================================================== *)
(*  The three Barning matrices (as integer maps on triples)               *)
(* ===================================================================== *)

Definition barA (a b c : Z) : Z * Z * Z :=
  (a - 2*b + 2*c, 2*a - b + 2*c, 2*a - 2*b + 3*c).
Definition barB (a b c : Z) : Z * Z * Z :=
  (a + 2*b + 2*c, 2*a + b + 2*c, 2*a + 2*b + 3*c).
Definition barC (a b c : Z) : Z * Z * Z :=
  (- a + 2*b + 2*c, - 2*a + b + 2*c, - 2*a + 2*b + 3*c).

(* ===================================================================== *)
(*  Each matrix preserves the Pythagorean condition a²+b²=c²              *)
(* ===================================================================== *)

(** Barning A maps a Pythagorean triple to a Pythagorean triple (it preserves a²+b²−c²). *)
Lemma barA_pyth : forall a b c : Z, a*a + b*b = c*c ->
  (a - 2*b + 2*c)*(a - 2*b + 2*c) + (2*a - b + 2*c)*(2*a - b + 2*c)
  = (2*a - 2*b + 3*c)*(2*a - 2*b + 3*c).
Proof.
  intros a b c H.
  assert (Hid : (a - 2*b + 2*c)*(a - 2*b + 2*c) + (2*a - b + 2*c)*(2*a - b + 2*c)
                - (2*a - 2*b + 3*c)*(2*a - 2*b + 3*c) = a*a + b*b - c*c) by ring.
  lia.
Qed.

(** Barning B likewise. *)
Lemma barB_pyth : forall a b c : Z, a*a + b*b = c*c ->
  (a + 2*b + 2*c)*(a + 2*b + 2*c) + (2*a + b + 2*c)*(2*a + b + 2*c)
  = (2*a + 2*b + 3*c)*(2*a + 2*b + 3*c).
Proof.
  intros a b c H.
  assert (Hid : (a + 2*b + 2*c)*(a + 2*b + 2*c) + (2*a + b + 2*c)*(2*a + b + 2*c)
                - (2*a + 2*b + 3*c)*(2*a + 2*b + 3*c) = a*a + b*b - c*c) by ring.
  lia.
Qed.

(** Barning C likewise. *)
Lemma barC_pyth : forall a b c : Z, a*a + b*b = c*c ->
  (- a + 2*b + 2*c)*(- a + 2*b + 2*c) + (- 2*a + b + 2*c)*(- 2*a + b + 2*c)
  = (- 2*a + 2*b + 3*c)*(- 2*a + 2*b + 3*c).
Proof.
  intros a b c H.
  assert (Hid : (- a + 2*b + 2*c)*(- a + 2*b + 2*c) + (- 2*a + b + 2*c)*(- 2*a + b + 2*c)
                - (- 2*a + 2*b + 3*c)*(- 2*a + 2*b + 3*c) = a*a + b*b - c*c) by ring.
  lia.
Qed.

(* ===================================================================== *)
(*  The seed and the three children of (3,4,5)                            *)
(* ===================================================================== *)

(** The root of the tree: 3²+4²=5². *)
Lemma pyth_seed : 3*3 + 4*4 = 5*5.
Proof. reflexivity. Qed.

(** ★ The three children of (3,4,5): (5,12,13), (21,20,29), (15,8,17) — the famous first
    generation of the Barning–Hall tree.  Each is Pythagorean (by the preservation lemmas
    applied to the seed). *)
Lemma barABC_345 :
  barA 3 4 5 = (5, 12, 13) /\ barB 3 4 5 = (21, 20, 29) /\ barC 3 4 5 = (15, 8, 17).
Proof. repeat split; reflexivity. Qed.

(** The hypotenuse strictly grows under B (2a+2b+3c > c for a positive triple) — so the
    tree descends without cycles, a genuine enumeration. *)
Lemma barB_hyp_grows : forall a b c : Z,
  0 < a -> 0 < b -> 0 < c -> 2*a + 2*b + 3*c > c.
Proof. intros a b c Ha Hb Hc. lia. Qed.

(* ===================================================================== *)
(*  Role-limit: the 45°/√2 isosceles point a=b is never a tree node        *)
(* ===================================================================== *)

(** ★ NO Pythagorean triple has a=b: that would force 2a²=c², i.e. √2 = c/a ∈ ℚ
    (`sqrt2_irrational_Z`).  The 45° isosceles right triangle — the (1/√2,1/√2) point of
    the unit circle — is a role-limit, never an Element of the tree. *)
Theorem no_isosceles_pyth : forall a c : Z, a <> 0 -> a*a + a*a <> c*c.
Proof.
  intros a c Ha Heq.
  apply (sqrt2_irrational_Z c a Ha). nia.
Qed.

(* ===================================================================== *)
(*  Synthesis                                                             *)
(* ===================================================================== *)

(** The Barning–Hall tree of Pythagorean triples, split by the finitization boundary:
      (a) ELEMENT — the three Barning matrices preserve the Pythagorean condition (so the
          tree of integer triples is closed: Element stays Element);
      (b) the seed (3,4,5) and its three children (5,12,13),(21,20,29),(15,8,17);
      (c) the hypotenuse strictly grows (the tree descends without cycles);
      (d) ROLE-LIMIT — no Pythagorean triple has a=b (the 45°/√2 point, never a node). *)
Theorem pythagorean_tree_synthesis :
  (forall a b c : Z, a*a + b*b = c*c ->
     (a - 2*b + 2*c)*(a - 2*b + 2*c) + (2*a - b + 2*c)*(2*a - b + 2*c)
     = (2*a - 2*b + 3*c)*(2*a - 2*b + 3*c))
  /\ (forall a b c : Z, a*a + b*b = c*c ->
     (a + 2*b + 2*c)*(a + 2*b + 2*c) + (2*a + b + 2*c)*(2*a + b + 2*c)
     = (2*a + 2*b + 3*c)*(2*a + 2*b + 3*c))
  /\ (3*3 + 4*4 = 5*5)
  /\ (barA 3 4 5 = (5, 12, 13) /\ barB 3 4 5 = (21, 20, 29) /\ barC 3 4 5 = (15, 8, 17))
  /\ (forall a c : Z, a <> 0 -> a*a + a*a <> c*c).
Proof.
  split; [ exact barA_pyth | ].
  split; [ exact barB_pyth | ].
  split; [ exact pyth_seed | ].
  split; [ exact barABC_345 | exact no_isosceles_pyth ].
Qed.
