(** * DescartesCircles.v — Descartes' four-tangent-circles theorem / Apollonian gaskets:
      the fourth curvature stays an Element (integer/rational) iff the discriminant
      k₁k₂+k₂k₃+k₃k₁ is a perfect square; otherwise it names a surd (role-limit).
      Fresh domain (circle packings / curvatures), same finitization boundary, and it ties
      back to the cluster's √3 thread (RationalSphere, LatticeEquilateral): three equal
      ("equilateral") unit circles force the inner Soddy curvature 3+2√3 — the same √3.

    Elements: the integer curvatures of a gasket; the bounded quadruple (−1,2,2,3); the
              Vieta pair of fourth curvatures (L1 + P4)
    Roles:    Element side = a square discriminant ⟹ the fourth curvature is integer/rational
              and the whole Apollonian packing stays integer FOREVER (e.g. (−1,2,2,3));
              role-limit = a non-square discriminant ⟹ the curvature is irrational, the
              canonical case being three unit circles → inner Soddy curvature 3+2√3 (√3)
    Rules:    the tangency rule = Descartes' identity (k₁+k₂+k₃+k₄)²=2(k₁²+k₂²+k₃²+k₄²);
              as a quadratic in k₄: k₄²−2s·k₄+(2Q−s²)=0; Vieta k₄+k₄'=2s (integer-preserving)

    THE DEEP POINT — the fourth curvature is an Element ⟺ the discriminant is a square.
    Descartes' rule k₄=k₁+k₂+k₃±2√(k₁k₂+k₂k₃+k₃k₁) hides ONE dial: the discriminant under the
    root.  Square ⟹ the new curvature is integer/rational and the Apollonian gasket stays
    all-integer forever (`descartes_form` with integer r; `gasket_integer_example` (−1,2,2,3);
    `gasket_vieta` — the two solutions sum to 2(k₁+k₂+k₃), so integer breeds integer).
    Non-square ⟹ role-limit: three mutually tangent UNIT circles (k₁=k₂=k₃=1) give discriminant
    1·1+1·1+1·1=3, so the inner Soddy curvature is 3+2√3 — but no rational squares to 3
    (`soddy_three_unit_role_limit`), exactly the √3 that forbids the 60° lattice point
    (RationalSphere, LatticeEquilateral, CliffordCapstone).  Element = the curvature closes into
    ℚ (square discriminant); role-limit = it names a surd (non-square discriminant).

    ============ E/R/R разбор ============
      Rules (L5): касание = тождество Декарта; квадрат по k₄: k₄²−2s·k₄+(2Q−s²)=0;
                  Виета k₄+k₄'=2s — целое рождает целое (правило размножения упаковки).
      Roles (L4): Element = квадратный дискриминант → k₄ целое/рационально, упаковка целая навсегда
                  (−1,2,2,3); role-limit = не-квадрат → k₄ иррационально, три единичных → 3+2√3.
      Elements  : целые кривизны гаскета; квадруплет (−1,2,2,3); пара корней Виеты (L1+P4).
    ДИАГНОСТИКА (P4): дискриминант k₁k₂+k₂k₃+k₃k₁ — единственный циферблат (как в QuadraticDiscriminant):
    квадрат ⟹ Element (целая аполлониева упаковка, счётно много целых кривизн); не-квадрат ⟹ role-limit
    (кривизна Содди = имя нетерминирующего процесса √3). «Точная кривизна вписанной в три единичных?» =
    не-вопрос: ответ 3+2√3 есть имя процесса. Виета k₄+k₄'=2s = алгебраическая форма «целое остаётся целым».
    Та же √3, что в RationalSphere / LatticeEquilateral / CliffordCapstone.

    STATUS: 6 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia QArith.
From ToS Require Import analysis.Sqrt3Irrational.

Open Scope Z_scope.

(* ===================================================================== *)
(*  Element: Descartes' identity holds when the discriminant is a square   *)
(* ===================================================================== *)

(** ★ Descartes' four-circle theorem in its constructive ("witness") form: whenever the
    discriminant k₁k₂+k₂k₃+k₃k₁ HAS a square root r (r·r = the discriminant), the fourth
    curvature k₄ = k₁+k₂+k₃+2r satisfies the Descartes identity exactly.  When r is an
    integer (square discriminant), k₄ is an integer — the Element side. *)
Lemma descartes_form :
  forall k1 k2 k3 r k4 : Z,
    r * r = k1*k2 + k2*k3 + k3*k1 ->
    k4 = k1 + k2 + k3 + 2*r ->
    (k1+k2+k3+k4)*(k1+k2+k3+k4) = 2*(k1*k1 + k2*k2 + k3*k3 + k4*k4).
Proof.
  intros k1 k2 k3 r k4 Hr Hk4. subst k4.
  assert (Hid :
    (k1+k2+k3+(k1+k2+k3+2*r)) * (k1+k2+k3+(k1+k2+k3+2*r))
    - 2*(k1*k1 + k2*k2 + k3*k3 + (k1+k2+k3+2*r)*(k1+k2+k3+2*r))
    = 4*(k1*k2 + k2*k3 + k3*k1) - 4*(r*r)) by ring.
  rewrite Hr in Hid. lia.
Qed.

(** A concrete all-integer Apollonian gasket: the bounded quadruple (−1,2,2,3) — the outer
    bounding circle has curvature −1 (it contains the others).  (−1+2+2+3)²=36=2·18. *)
Lemma gasket_integer_example :
  ((-1)+2+2+3) * ((-1)+2+2+3) = 2*((-1)*(-1) + 2*2 + 2*2 + 3*3).
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  Element: Vieta — integer breeds integer (the packing stays integral)   *)
(* ===================================================================== *)

(** ★ The two fourth-circles for given k₁,k₂,k₃ are the two roots of x²−2s·x+(2Q−s²)=0,
    s=k₁+k₂+k₃.  By Vieta they sum to 2s.  Hence if one solution and 2(k₁+k₂+k₃) are
    integers, so is the other: integer curvatures breed integer curvatures, and the whole
    Apollonian gasket stays all-integer forever (the Element side). *)
Lemma gasket_vieta :
  forall s C k4 k4' : Z,
    k4  * k4  - 2*s*k4  + C = 0 ->
    k4' * k4' - 2*s*k4' + C = 0 ->
    k4 <> k4' ->
    k4 + k4' = 2*s.
Proof.
  intros s C a b Ha Hb Hne.
  assert (Hfac : (a - b) * (a + b - 2*s) = 0).
  { assert (E : (a - b) * (a + b - 2*s)
              = (a*a - 2*s*a + C) - (b*b - 2*s*b + C)) by ring.
    rewrite Ha, Hb in E. lia. }
  apply Z.mul_eq_0 in Hfac. destruct Hfac as [H | H].
  - exfalso. apply Hne. lia.
  - lia.
Qed.

(** The discriminant of three unit circles (k₁=k₂=k₃=1) is exactly 3 — the number whose
    root the inner Soddy curvature 3±2√3 needs. *)
Lemma three_unit_discriminant : 1*1 + 1*1 + 1*1 = 3.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  Role-limit: three unit circles force √3 (non-square discriminant)      *)
(* ===================================================================== *)

Open Scope Q_scope.

(** ★ Three mutually tangent UNIT circles (k₁=k₂=k₃=1) have discriminant 3 (above), so the
    inner Soddy circle has curvature k₄ = 3 ± 2√3 — and no rational squares to 3.  The
    "equilateral" configuration of three equal circles names √3, the role-limit: the same √3
    that forbids the 60° lattice point and the lattice equilateral triangle (RationalSphere,
    LatticeEquilateral, CliffordCapstone). *)
Theorem soddy_three_unit_role_limit : ~ (exists r : Q, r * r == 3).
Proof. exact sqrt3_not_in_Q. Qed.

(* ===================================================================== *)
(*  Synthesis                                                            *)
(* ===================================================================== *)

(** Apollonian circle packing, split by the finitization boundary:
      (a) ELEMENT — square discriminant: the Descartes identity closes into ℚ
          (`descartes_form`), and Vieta makes integer breed integer forever
          (`gasket_vieta` — the two fourth curvatures sum to 2(k₁+k₂+k₃));
      (b) ROLE-LIMIT — non-square discriminant: three unit circles give discriminant 3
          (`three_unit_discriminant`), so the inner Soddy curvature 3+2√3 names √3, and no
          rational squares to 3 (`soddy_three_unit_role_limit`). *)
Theorem descartes_synthesis :
  (forall k1 k2 k3 r k4 : Z,
      r * r = k1*k2 + k2*k3 + k3*k1 ->
      k4 = k1 + k2 + k3 + 2*r ->
      (k1+k2+k3+k4)*(k1+k2+k3+k4) = 2*(k1*k1 + k2*k2 + k3*k3 + k4*k4))%Z
  /\ (forall s C k4 k4' : Z,
        k4*k4 - 2*s*k4 + C = 0 -> k4'*k4' - 2*s*k4' + C = 0 ->
        k4 <> k4' -> k4 + k4' = 2*s)%Z
  /\ (1*1 + 1*1 + 1*1 = 3)%Z
  /\ ~ (exists r : Q, r * r == 3).
Proof.
  split; [ exact descartes_form | ].
  split; [ exact gasket_vieta | ].
  split; [ exact three_unit_discriminant | exact soddy_three_unit_role_limit ].
Qed.
