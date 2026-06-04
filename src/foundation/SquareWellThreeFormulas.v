(** * SquareWellThreeFormulas.v — the infinite square well as an INSTANCE of the three-formula
      method, and a concrete crossing of the finitization boundary.

    First system built ON TOP of the reified method (ThreeFormulaMethod.v) + boundary
    (ThreeFormulaBoundary.v).  The point is no longer "here is another worked example" but
    "the method-as-theorem and its boundary criterion WORK on a fresh, iconic system".

    THE THREE FORMULAS of the infinite square well (particle in a box):
      E-formula (L1, ground):   E_1 != 0 — the CONFINEMENT zero-point (you cannot put a particle
                                in a box at rest; contrast the free particle / photon, E_0 = 0).
      R-formula (L4, spectrum): E_n = n^2 * E_1 — the n^2 ladder (here in natural units E_1 = 1,
                                so the levels are 1, 4, 9, ...).  Rational => ELEMENT.
      R-formula (L5, rule):     the box Hamiltonian / discrete Laplacian (standing-wave recurrence).

    THE BOUNDARY IN ACTION.  The CONTINUUM spectrum n^2 is Element (a rational ladder).  But the
    box's finite DISCRETIZATIONS (the tridiagonal Laplacian on N interior points) sit on EITHER
    side of the finitization boundary depending on N, decided by the SAME criterion
    spectrum_element_iff_square_disc:
      * N = 2 : Laplacian [[2,-1],[-1,2]], disc = 4 (square) -> spectrum {1, 3}, ELEMENT;
      * N = 3 : the nontrivial mode pair satisfies (2-l)^2 = 2, i.e. l = 2 +- sqrt 2 — captured by
                the companion [[4,-2],[1,0]] (char poly l^2 - 4l + 2), disc = 8 (= 16*... no, 8),
                NOT a square -> ROLE-LIMIT (sqrt 2, cited from the atlas / Sqrt2 thread).
    So discretizing the iconic Element system makes its spectrum oscillate across the boundary;
    the criterion from ThreeFormulaBoundary.v decides each case.

    Elements: the ground E_1; the levels 1,4,9; the discretization matrices box2, box3
    Roles:    the n^2 spectral ladder; the Element/role-limit status of each discretization
    Rules:    E_n = n^2 E_1 (rational, Element); a discretization is Element iff its disc is a square

    ============ E/R/R разбор ============
      Rules (L5): правило = лапласиан ящика; дискретизация N точек порождает спектр; статус Element
                  ⟺ disc — полный квадрат (критерий из ThreeFormulaBoundary).
      Roles (L4): лестница E_n=n²E₁; статус Element/role-limit дискретизации (N=2 Element, N=3 √2).
      Elements  : основание E₁≠0 (зероточка конфайнмента); уровни 1,4,9; матрицы box2/box3.
    ДИАГНОСТИКА (P4): континуум n² — Element; дискретизации осциллируют поперёк границы с N; теорема-
    как-метод работает на каноническом ящике; E₁≠0 = частицу нельзя запереть в покое (различение
    требует ненулевого основания).

    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith.
From Stdlib Require Import Lqa.
From ToS Require Import foundation.ThreeFormulaMethod.
From ToS Require Import foundation.ThreeFormulaBoundary.

Local Open Scope Q_scope.

(* ===================================================================== *)
(*  R-formula (continuum): E_n = n^2 * E_1, the rational ladder (Element)   *)
(* ===================================================================== *)

(** Levels in natural units E_1 = 1: E_n = n^2.  The spectrum stays in Q — ELEMENT. *)
Definition box_E (n : nat) : Q := inject_Z (Z.of_nat (n * n)).

(** E-formula: the confinement ground E_1 = 1 (NONZERO — no particle at rest in a box). *)
Lemma box_ground : box_E (S O) == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma box_E2 : box_E (S (S O)) == 4.
Proof. vm_compute. reflexivity. Qed.

Lemma box_E3 : box_E (S (S (S O))) == 9.
Proof. vm_compute. reflexivity. Qed.

(** ★ the n^2 law: E_2 = 2^2 E_1, E_3 = 3^2 E_1 (the R-formula). *)
Lemma box_law_2 : box_E (S (S O)) == 4 * box_E (S O).
Proof. vm_compute. reflexivity. Qed.

Lemma box_law_3 : box_E (S (S (S O))) == 9 * box_E (S O).
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  R-formula (rule) + boundary: discretizations across the boundary       *)
(* ===================================================================== *)

(** N = 2 discrete Laplacian [[2,-1],[-1,2]] (Dirichlet box, 2 interior points). *)
Definition box2 : Mat2 := mk2 2 (- (1)) (- (1)) 2.

Lemma box2_disc : disc box2 == 4.
Proof. unfold disc, tr, det, box2; simpl; ring. Qed.

(** disc = 4 is a perfect square -> the N=2 spectrum is ELEMENT. *)
Lemma box2_element : is_square (disc box2).
Proof. exists 2. rewrite box2_disc; ring. Qed.

(** Its eigenvalue 1 (the other is 3): rational, as the criterion guarantees. *)
Lemma box2_eigenvalue : char_poly box2 1 == 0.
Proof. unfold char_poly, tr, det, box2; simpl; ring. Qed.

Lemma box2_spectrum_element : exists x, char_poly box2 x == 0.
Proof. exists 1. exact box2_eigenvalue. Qed.

(** N = 3 box: the nontrivial mode pair satisfies (2-l)^2 = 2, i.e. char poly l^2 - 4l + 2,
    captured by the companion [[4,-2],[1,0]]; disc = 8. *)
Definition box3 : Mat2 := mk2 4 (- (2)) 1 0.

Lemma box3_disc : disc box3 == 8.
Proof. unfold disc, tr, det, box3; simpl; ring. Qed.

(** ★ the N=3 discretization meets the boundary: it has a rational eigenvalue iff is_square 8.
    Since sqrt 2 is irrational (8 = 4*2 not a perfect square; atlas page I / Sqrt2 thread), the
    N=3 box spectrum is ROLE-LIMIT — the discretization crossed the finitization boundary. *)
Lemma box3_eigenvalue_iff_square8 :
  (exists x, char_poly box3 x == 0) <-> is_square 8.
Proof.
  rewrite (spectrum_element_iff_square_disc box3).
  unfold is_square. split; intros [r Hr]; exists r.
  - rewrite <- box3_disc. exact Hr.
  - rewrite box3_disc. exact Hr.
Qed.

(* ===================================================================== *)
(*  Capstone: the square well, method + boundary together                  *)
(* ===================================================================== *)

(** The infinite square well as a three-formula system meeting the boundary:
      (E-formula) the confinement ground E_1 = 1 (nonzero);
      (R-formula) the n^2 ladder E_2 = 4E_1, E_3 = 9E_1 (rational, Element);
      (boundary)  the N=2 discretization is Element (disc 4 a square);
      (boundary)  the N=3 discretization is Element iff is_square 8 — i.e. role-limit (sqrt 2).
    The continuum spectrum is Element; its discretizations oscillate across the finitization
    boundary with N, the criterion spectrum_element_iff_square_disc deciding each. *)
Theorem square_well_three_formula :
  box_E (S O) == 1
  /\ (box_E (S (S O)) == 4 * box_E (S O)
      /\ box_E (S (S (S O))) == 9 * box_E (S O))
  /\ is_square (disc box2)
  /\ ((exists x, char_poly box3 x == 0) <-> is_square 8).
Proof.
  split; [ exact box_ground | ].
  split; [ split; [ exact box_law_2 | exact box_law_3 ] | ].
  split; [ exact box2_element | exact box3_eigenvalue_iff_square8 ].
Qed.
