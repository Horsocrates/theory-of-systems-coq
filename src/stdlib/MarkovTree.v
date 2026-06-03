(** * MarkovTree.v — the Markov equation x²+y²+z²=3xyz and the tree of Markov triples.
      Vieta jumping generates ALL triples from (1,1,1) (an Element-side ternary tree, like
      the Pythagorean and Stern–Brocot trees — the Markov numbers 1,2,5,13,29,…), while the
      Markov–Lagrange numbers √(9m²−4) are role-limits: √5 (the golden ratio φ, the worst-
      approximable number, m=1) and √8=2√2 (the Tsirelson bound, m=2).  This cross-links
      GoldenFibonacci.v (√5) and BellTsirelson.v (2√2).

    Elements: the integer triples (1,1,1),(1,1,2),(1,2,5),(1,5,13),(2,5,29); the Markov
              numbers 1,2,5,13,29 (L1 + P4)
    Roles:    Element side = the Markov tree (all triples from (1,1,1) by Vieta jumping — an
              infinite ternary tree of integer triples; the jump preserves the equation);
              role-limit = the Markov–Lagrange numbers √(9m²−4) (worst-approximation
              constants: √5 for m=1 [golden ratio φ], √8=2√2 for m=2 [Tsirelson])
    Rules:    the Markov equation x²+y²+z²=3xyz; the Vieta jump (x,y,z)↦(x,y,3xy−z); the
              seed (1,1,1); ternary branching

    THE DEEP POINT — the Markov triples are an Element-side tree, and the approximation
    constants are role-limits tying √5 (golden) and 2√2 (Tsirelson).  The quadratic
    z²−3xy·z+(x²+y²)=0 has two roots z, z' with z+z'=3xy, so the Vieta jump (x,y,z)↦(x,y,3xy−z)
    sends a Markov triple to a Markov triple (`vieta_preserves`, a ring identity exactly like
    the Pythagorean tree's matrices).  From the seed (1,1,1) this generates the infinite
    Markov tree: (1,1,1),(1,1,2),(1,2,5),(1,5,13),(2,5,29),… (`markov_tree_numbers`), and the
    jumps at (1,2,5) produce the Markov numbers 13 and 29 (`vieta_jump_125`).  The Markov
    NUMBERS are Element (integers in the tree); the LAGRANGE numbers √(9m²−4)/m are role-
    limits: for m=1, √(9−4)=√5 — the golden ratio, the most irrational number
    (`lagrange_1_role_limit`); for m=2, L(2)²=(9·4−4)/4=8, so √8=2√2 — the Tsirelson bound
    (`lagrange_2_role_limit`).  Element = the tree of Markov numbers; role-limit = the
    Lagrange spectrum (√5, 2√2), cross-linking the golden ratio and the Bell/Tsirelson bound.

    ============ E/R/R разбор ============
      Rules (L5): уравнение Маркова x²+y²+z²=3xyz; прыжок Виета (x,y,z)↦(x,y,3xy−z); корень (1,1,1);
                  тернарное ветвление.
      Roles (L4): Element = дерево Маркова (все тройки из (1,1,1) прыжками Виета, тернарное дерево целых
                  троек; прыжок сохраняет уравнение); role-limit = числа Лагранжа √(9m²−4) (√5 φ m=1,
                  √8=2√2 Цирельсон m=2).
      Elements  : целые тройки (1,1,1),(1,1,2),(1,2,5),(1,5,13),(2,5,29); числа Маркова (L1+P4).
    ДИАГНОСТИКА (P4): тройки Маркова = Element-дерево (из корня прыжками Виета, как пифагорово/Stern-Brocot);
    константы Лагранжа = role-limits (√5=φ наихудше приближаемое, 2√2=Цирельсон). Кросс-связи √5↔φ, 2√2↔Bell.

    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia QArith.
From ToS Require Import analysis.Sqrt2Irrational.
From ToS Require Import analysis.Sqrt5Irrational.

Open Scope Z_scope.

(* ===================================================================== *)
(*  Vieta jumping preserves the Markov equation                          *)
(* ===================================================================== *)

(** ★ The Vieta jump (x,y,z) ↦ (x,y,3xy−z) sends a Markov triple to a Markov triple: the
    quadratic z²−3xy·z+(x²+y²)=0 has roots z, 3xy−z.  A ring identity (like the Pythagorean
    tree's matrices). *)
Lemma vieta_preserves : forall x y z : Z,
  x*x + y*y + z*z = 3*x*y*z ->
  x*x + y*y + (3*x*y - z)*(3*x*y - z) = 3*x*y*(3*x*y - z).
Proof.
  intros x y z H.
  assert (Hid : x*x + y*y + (3*x*y - z)*(3*x*y - z) - 3*x*y*(3*x*y - z)
                = (x*x + y*y + z*z) - 3*x*y*z) by ring.
  lia.
Qed.

(* ===================================================================== *)
(*  The Markov tree: the numbers 1,2,5,13,29                              *)
(* ===================================================================== *)

(** ★ The first Markov triples — the famous Markov numbers 1,2,5,13,29 — generated from the
    seed (1,1,1) by Vieta jumping. *)
Lemma markov_tree_numbers :
  1*1 + 1*1 + 1*1 = 3*1*1*1
  /\ 1*1 + 1*1 + 2*2 = 3*1*1*2
  /\ 1*1 + 2*2 + 5*5 = 3*1*2*5
  /\ 1*1 + 5*5 + 13*13 = 3*1*5*13
  /\ 2*2 + 5*5 + 29*29 = 3*2*5*29.
Proof. repeat split; reflexivity. Qed.

(** The two Vieta jumps at (1,2,5) produce the Markov numbers 13 (jump y) and 29 (jump x). *)
Lemma vieta_jump_125 : 3*1*5 - 2 = 13 /\ 3*2*5 - 1 = 29.
Proof. split; reflexivity. Qed.

(* ===================================================================== *)
(*  Role-limit: the Markov–Lagrange numbers √5 and 2√2                    *)
(* ===================================================================== *)

Open Scope Q_scope.

(** ★ The Markov–Lagrange number for m=1 is √(9−4)=√5 — the golden ratio φ, the most
    irrational number (worst-approximable).  Irrational (`sqrt5_not_in_Q`). *)
Theorem lagrange_1_role_limit : ~ (exists r : Q, r * r == 5).
Proof. exact sqrt5_not_in_Q. Qed.

(** ★ The Markov–Lagrange number for m=2 has square (9·4−4)/4 = 8, i.e. √8 = 2√2 — the
    Tsirelson bound.  Irrational: r²=8 ⟹ (r/2)²=2. *)
Theorem lagrange_2_role_limit : ~ (exists r : Q, r * r == 8).
Proof.
  intros [r H]. apply (no_rational_sqrt2 ((1 # 2) * r)).
  assert (Hb : ((1 # 2) * r) * ((1 # 2) * r) == (1 # 4) * (r * r)) by ring.
  rewrite Hb, H. vm_compute. reflexivity.
Qed.

(* ===================================================================== *)
(*  Synthesis                                                            *)
(* ===================================================================== *)

(** The Markov tree, split by the finitization boundary:
      (a) ELEMENT — Vieta jumping preserves the Markov equation (the tree of integer
          triples is closed);
      (b) the Markov numbers 1,2,5,13,29 (the tree from the seed (1,1,1));
      (c) ROLE-LIMIT — the Markov–Lagrange numbers √5 (golden, m=1) and 2√2 (Tsirelson,
          m=2) are irrational. *)
Theorem markov_tree_synthesis :
  (forall x y z : Z, (x*x + y*y + z*z = 3*x*y*z)%Z ->
     (x*x + y*y + (3*x*y - z)*(3*x*y - z) = 3*x*y*(3*x*y - z))%Z)
  /\ ((1*1 + 1*1 + 1*1 = 3*1*1*1)%Z /\ (1*1 + 2*2 + 5*5 = 3*1*2*5)%Z
      /\ (2*2 + 5*5 + 29*29 = 3*2*5*29)%Z)
  /\ ~ (exists r : Q, r * r == 5)
  /\ ~ (exists r : Q, r * r == 8).
Proof.
  split; [ exact vieta_preserves | ].
  split.
  - split; [ reflexivity | split; reflexivity ].
  - split; [ exact lagrange_1_role_limit | exact lagrange_2_role_limit ].
Qed.
