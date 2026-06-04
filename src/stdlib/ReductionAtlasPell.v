(** * ReductionAtlasPell.v — the reduction atlas, page III: the NORM FORM x²−D·y² as the
      cluster primitive that carries BOTH sides of the finitization boundary.  Where page I
      (the surd engine m²=n·k²) is purely the OBSTRUCTION side and page II (the determinant
      ad−bc) is purely the Element/enumeration side, this page is the BRIDGE: the SAME integer
      N(p,q)=p²−D·q², via the SAME multiplicativity (Brahmagupta / norm multiplicativity in
      ℤ[√D]), yields the obstruction (N≠0, the granular floor = page I's surd theorem) AND the
      approach (N=±1, the Pell tower = the unbounded process that DEFINES the role-limit √D).

    Elements: the integer norm form N(x,y)=x²−D·y²; the composition identity; the concrete D=2
              instances — the unit (3,2), the seed (1,1), the tower (7,5),(41,29) (L1 + P4)
    Roles:    the norm N(p,q) — the single integer whose value plays two opposite roles: held at
              ±1 it is a Pell unit / best convergent (the role-limit's APPROACH process, q
              unbounded); barred from 0 it is the granular floor (the role-limit's OBSTRUCTION)
    Rules:    one generating rule — Brahmagupta / norm multiplicativity N(z₁)·N(z₂)=N(z₁·z₂);
              its two specializations: a unit N(u,v)=1 preserves N (the tower), and N∈ℤ barred
              from 0 gives |N|≥1 (the floor)

    THE DEEP POINT — one norm form, both sides of the dichotomy.  Page I (surd m²=n·k²) is the
    obstruction side alone; page II (determinant ad−bc) is the Element/enumeration side alone.
    This page bridges them: the SAME N(p,q), through the SAME multiplicativity (`brahmagupta`),
    gives (face 1) the Pell tower — a unit N(u,v)=1 preserves N (`pell_unit_preserves`), so the
    D=2 step (3p+4q,2p+3q) preserves N (`pell2_step_preserves`), generating the unbounded approach
    (1,1)→(7,5)→(41,29) to √2; and (face 2) the granular floor — for a non-square D, N never
    vanishes so |N|≥1 (`norm_form_floor`, reducing through GranularFloor to GeneralSqrt's surd
    theorem).  The "physics no-go" (GranularFloor) and the "unbounded process beats any cutoff"
    (FinitizationNoCutoff) are the TWO FACES OF ONE NORM FORM.  Cross-link to page II:
    N(x,y)=x·x−(D·y)·y is the determinant of the companion matrix [[x,Dy],[y,x]] of x+y√D
    (`norm2_is_companion_det`), so Brahmagupta IS det(MN)=det(M)det(N) — page III is page II
    applied to the regular representation of ℤ[√D].  The tower MEETS the floor: at (7,5),(41,29)
    the norm hits |N|=1 exactly (`pell2_meets_floor`) — the approach reaches the obstruction floor.
    Element = a rational config (|N|≥1); role-limit = √D, reached only by the unbounded N=±1 tower.

    ============ E/R/R разбор ============
      Rules (L5): одно правило — мультипликативность нормы Брахмагупты N(z₁)·N(z₂)=N(z₁·z₂); две
                  специализации: единица N(u,v)=1 сохраняет N (башня); N∈ℤ, отрезано от 0 ⟹ |N|≥1 (пол).
      Roles (L4): норма N(p,q) — одно целое, две роли: на ±1 — единица Пелля/сходящаяся (процесс-
                  приближение √D, q неограничено); отрезано от 0 — гранулярный пол (обструкция √D).
      Elements  : целая норм-форма x²−Dy²; тождество композиции; D=2: единица (3,2), затравка (1,1),
                  башня (7,5),(41,29).
    ДИАГНОСТИКА (P4): глубочайший движок — несёт ОБЕ стороны границы в ОДНОМ объекте. Стр.I (сурд) =
    только обструкция; стр.II (определитель) = только Element/перечисление; стр.III (норм-форма) = МОСТ:
    та же N через ту же мультипликативность даёт И обструкцию (N≠0, пол = теорема о сурдах) И приближение
    (N=±1, башня Пелля = неограниченный процесс). Кросс-связь: N=det[[x,Dy],[y,x]], Брахмагупта = det(MN)=
    det(M)det(N) — стр.III = стр.II на регулярном представлении ℤ[√D]. Башня ДОСТИГАЕТ пола (|N|=1 при (7,5)).

    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia.
From ToS Require Import stdlib.GranularFloor.

Open Scope Z_scope.

(* ===================================================================== *)
(*  THE ENGINE: the integer norm form of ℤ[√D] and its multiplicativity    *)
(* ===================================================================== *)

(** The integer norm form of x + y√D in ℤ[√D]. *)
Definition norm2 (D x y : Z) : Z := x * x - D * (y * y).

(** ★ The single rule the whole page runs on: Brahmagupta's identity = norm multiplicativity.
    The product of two norms is the norm of the product (x₁+y₁√D)(x₂+y₂√D) =
    (x₁x₂+Dy₁y₂) + (x₁y₂+y₁x₂)√D.  Every move below is a specialization of this ring identity. *)
Lemma brahmagupta : forall D x1 y1 x2 y2 : Z,
  norm2 D x1 y1 * norm2 D x2 y2
  = norm2 D (x1 * x2 + D * y1 * y2) (x1 * y2 + y1 * x2).
Proof. intros. unfold norm2. ring. Qed.

(** Cross-link to page II (the unimodular-determinant engine): the norm form IS the determinant
    of the companion matrix [[x, D*y],[y, x]] of x+y√D.  Hence Brahmagupta is det(MN)=det(M)det(N)
    for the regular representation of ℤ[√D] — page III is page II on that representation. *)
Lemma norm2_is_companion_det : forall D x y : Z,
  norm2 D x y = x * x - (D * y) * y.
Proof. intros. unfold norm2. ring. Qed.

(* ===================================================================== *)
(*  FACE 1 — the Pell tower: a unit N(u,v)=1 preserves the norm (approach)  *)
(* ===================================================================== *)

(** ★ The approach face.  A fundamental unit N(u,v)=1, composed with any solution (x,y), preserves
    its norm: N(u·x+D·v·y, u·y+v·x) = N(x,y).  This is Brahmagupta read with N(u,v)=1, and it
    generates the infinite Pell tower of best convergents to √D. *)
Theorem pell_unit_preserves : forall D u v x y : Z,
  norm2 D u v = 1 ->
  norm2 D (u * x + D * v * y) (u * y + v * x) = norm2 D x y.
Proof.
  intros D u v x y Hu.
  rewrite <- (brahmagupta D u v x y). rewrite Hu. ring.
Qed.

(** The D=2 fundamental unit (3,2): N(3,2) = 9 − 8 = 1 (the norm-+1 unit 3+2√2 = (1+√2)²). *)
Lemma pell2_unit : norm2 2 3 2 = 1.
Proof. reflexivity. Qed.

(** ★ The D=2 Pell step (p,q) ↦ (3p+4q, 2p+3q) preserves the norm — recovering
    FinitizationNoCutoff's invariant as the (3,2)-unit instance of `pell_unit_preserves`. *)
Theorem pell2_step_preserves : forall p q : Z,
  norm2 2 (3 * p + 4 * q) (2 * p + 3 * q) = norm2 2 p q.
Proof.
  intros p q.
  replace (3 * p + 4 * q) with (3 * p + 2 * 2 * q) by ring.
  replace (2 * p + 3 * q) with (3 * q + 2 * p) by ring.
  apply (pell_unit_preserves 2 3 2 p q pell2_unit).
Qed.

(** The seed and the tower for √2: N stays at −1 along (1,1) → (7,5) → (41,29), the convergents
    1/1, 7/5, 41/29 to √2 with q unbounded — the unbounded approach process. *)
Lemma pell2_seed : norm2 2 1 1 = -1.
Proof. reflexivity. Qed.

Lemma pell2_tower_7_5 : norm2 2 7 5 = -1.
Proof. reflexivity. Qed.

Lemma pell2_tower_41_29 : norm2 2 41 29 = -1.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  FACE 2 — the granular floor: N≠0 ⟹ |N|≥1 (obstruction, via GeneralSqrt) *)
(* ===================================================================== *)

(** The norm form is (minus) the granular gap of GranularFloor: N(p,q) = −(q²D − p²). *)
Lemma norm2_is_gap : forall D p q : Z, norm2 D p q = - (q * q * D - p * p).
Proof. intros. unfold norm2. ring. Qed.

(** ★ The obstruction face.  For a non-square D and q > 0, the norm form never vanishes and
    |N(p,q)| ≥ 1 — the granular floor.  This reduces (via GranularFloor's `granular_floor`,
    itself GeneralSqrt's surd theorem) to "D non-square ⟹ q²D ≠ p²": the SAME engine as page I,
    now read on the norm form. *)
Theorem norm_form_floor : forall D p q : Z,
  (forall m : Z, m * m <> D) -> 0 < q -> 1 <= Z.abs (norm2 D p q).
Proof.
  intros D p q Hns Hq.
  rewrite norm2_is_gap. rewrite Z.abs_opp.
  apply granular_floor; assumption.
Qed.

(** ★ The two faces MEET: the Pell tower reaches the floor exactly.  At (7,5) and (41,29) the
    norm hits |N| = 1 — the tight floor value — with q unbounded.  The approach (face 1) reaches
    the obstruction floor (face 2): one norm form, both sides, touching. *)
Lemma pell2_meets_floor : Z.abs (norm2 2 7 5) = 1 /\ Z.abs (norm2 2 41 29) = 1.
Proof. split; reflexivity. Qed.

(* ===================================================================== *)
(*  The atlas page: one norm form, both sides of the finitization boundary  *)
(* ===================================================================== *)

(** The norm-form atlas page:
      (engine) Brahmagupta / norm multiplicativity (`brahmagupta`);
      (face 1, approach) a unit preserves the norm (`pell_unit_preserves`) — the Pell tower;
      (face 2, obstruction) for non-square D the norm never vanishes, |N|≥1 (`norm_form_floor`)
        — the granular floor, = page I's surd theorem;
      (meeting) the tower reaches the floor exactly, |N|=1 at (7,5),(41,29) (`pell2_meets_floor`).
    One integer norm form carries both sides of the finitization boundary. *)
Theorem pell_atlas :
  (forall D x1 y1 x2 y2 : Z,
     norm2 D x1 y1 * norm2 D x2 y2
     = norm2 D (x1 * x2 + D * y1 * y2) (x1 * y2 + y1 * x2))
  /\ (forall D u v x y : Z, norm2 D u v = 1 ->
        norm2 D (u * x + D * v * y) (u * y + v * x) = norm2 D x y)
  /\ (forall D p q : Z, (forall m : Z, m * m <> D) -> 0 < q -> 1 <= Z.abs (norm2 D p q))
  /\ (Z.abs (norm2 2 7 5) = 1 /\ Z.abs (norm2 2 41 29) = 1).
Proof.
  split; [ exact brahmagupta | ].
  split; [ exact pell_unit_preserves | ].
  split; [ exact norm_form_floor | exact pell2_meets_floor ].
Qed.
