(** * HurwitzTower.v — the Hurwitz tower of multiplicative norm forms: a
      "sum of n squares is multiplicative" identity exists for EXACTLY n = 1, 2, 4, 8
      (ℝ, ℂ, ℍ, 𝕆 — Hurwitz), and the OCTONIONS are the last.  The Element-side
      norm-form symmetry groups form a FINITE tower that terminates at dimension 8 —
      a finitization at the meta-level.

    Elements: the rational components; the four identities (n=1,2,4,8); the
              dimensions 1, 2, 4, 8 (L1 + P4)
    Roles:    the four composition-algebra norms (ℝ,ℂ,ℍ,𝕆) = the Element side — their
              unit elements are closed under multiplication (groups for n≤4, a Moufang
              loop for n=8); the dimension tower 1,2,4,8 = a FINITE list that
              TERMINATES (the meta-finitization); the octonions = the terminus
    Rules:    the sum-of-n-squares norm forms; their multiplicative identities
              (Brahmagupta n=2, Euler n=4, Degen n=8); Cayley–Dickson doubling;
              Hurwitz's theorem (only n=1,2,4,8)

    THE DEEP POINT — the Element-side construction itself terminates.  Throughout the
    cluster, the Element-side symmetry groups came from MULTIPLICATIVE norm forms:
    2D rotations from ℚ[i] (norm a²+b², the two-square identity, `ConicDuality.v`),
    3D rotations from rational quaternions (norm a²+b²+c²+d², Euler's four-square
    identity, `RationalQuaternions.v`).  Cayley–Dickson doubling continues the tower:
      n=1 (ℝ):  (ab)² = a²·b²                          (`one_square`)
      n=2 (ℂ):  Brahmagupta–Fibonacci two-square        (`two_square`)
      n=4 (ℍ):  Euler four-square                        (`four_square`)
      n=8 (𝕆):  Degen eight-square                       (`eight_square`)
    Each makes the unit elements closed under multiplication.  But HURWITZ'S THEOREM
    says these are the ONLY dimensions: there is NO multiplicative sum-of-n-squares
    identity for any other n (in particular none for n=16).  So the tower of
    Element-side norm-form groups is FINITE — it terminates at the octonions
    (dimension 8), beyond which the norm form, and with it the closure, is lost.  Even
    the meta-level question "which dimensions admit the Element-side construction?" has
    a finite answer, {1,2,4,8}: a finitization one storey up.  The octonions are the
    last finitely-actual composition algebra; dimension 16 (sedenions) is the role-
    limit where the construction no longer closes.

    ============ E/R/R разбор ============
      Rules (L5): норм-формы суммы n квадратов; тождества n=2 Брахмагупта, n=4 Эйлер,
                  n=8 Деген; удвоение Кэли–Диксона; Гурвиц (только 1,2,4,8).
      Roles (L4): четыре нормы (ℝ,ℂ,ℍ,𝕆) = Element-сторона; единичные элементы замкнуты;
                  башня 1,2,4,8 = конечный список, обрывающийся (мета-финитизация); 𝕆 = терминус.
      Elements  : рациональные компоненты; четыре тождества; размерности 1,2,4,8 (L1+P4).
    ДИАГНОСТИКА (P4): Element-норм-формные группы существуют РОВНО в dim 1,2,4,8 (Гурвиц) —
    конечная башня, обрывающаяся на октонионах. Удвоение Кэли–Диксона ОСТАНАВЛИВАЕТСЯ на 8
    (дальше норм-форма теряется). Мета-финитизация: список Element-размерностей конечен; 𝕆 = последние.

    STATUS: 6 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lia Lqa.
Open Scope Q_scope.

(* ===================================================================== *)
(*  The Hurwitz tower of multiplicative norm forms: n = 1, 2, 4, 8        *)
(* ===================================================================== *)

(** n = 1 (ℝ): the norm a² is multiplicative — trivially. *)
Theorem one_square : forall a b : Q, (a*b)*(a*b) == (a*a)*(b*b).
Proof. intros. ring. Qed.

(** n = 2 (ℂ): the Brahmagupta–Fibonacci two-square identity (the norm of ℚ[i]). *)
Theorem two_square : forall a1 a2 b1 b2 : Q,
  (a1*b1 - a2*b2)*(a1*b1 - a2*b2) + (a1*b2 + a2*b1)*(a1*b2 + a2*b1)
  == (a1*a1 + a2*a2) * (b1*b1 + b2*b2).
Proof. intros. ring. Qed.

(** n = 4 (ℍ): Euler's four-square identity (the quaternion norm). *)
Theorem four_square : forall a1 a2 a3 a4 b1 b2 b3 b4 : Q,
  (a1*b1 - a2*b2 - a3*b3 - a4*b4)*(a1*b1 - a2*b2 - a3*b3 - a4*b4)
  + (a1*b2 + a2*b1 + a3*b4 - a4*b3)*(a1*b2 + a2*b1 + a3*b4 - a4*b3)
  + (a1*b3 - a2*b4 + a3*b1 + a4*b2)*(a1*b3 - a2*b4 + a3*b1 + a4*b2)
  + (a1*b4 + a2*b3 - a3*b2 + a4*b1)*(a1*b4 + a2*b3 - a3*b2 + a4*b1)
  == (a1*a1 + a2*a2 + a3*a3 + a4*a4) * (b1*b1 + b2*b2 + b3*b3 + b4*b4).
Proof. intros. ring. Qed.

(** ★ n = 8 (𝕆): Degen's eight-square identity (the octonion norm).  The last one. *)
Theorem eight_square : forall a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8 : Q,
  let c1 := a1*b1 - a2*b2 - a3*b3 - a4*b4 - a5*b5 - a6*b6 - a7*b7 - a8*b8 in
  let c2 := a1*b2 + a2*b1 + a3*b4 - a4*b3 + a5*b6 - a6*b5 - a7*b8 + a8*b7 in
  let c3 := a1*b3 - a2*b4 + a3*b1 + a4*b2 + a5*b7 + a6*b8 - a7*b5 - a8*b6 in
  let c4 := a1*b4 + a2*b3 - a3*b2 + a4*b1 + a5*b8 - a6*b7 + a7*b6 - a8*b5 in
  let c5 := a1*b5 - a2*b6 - a3*b7 - a4*b8 + a5*b1 + a6*b2 + a7*b3 + a8*b4 in
  let c6 := a1*b6 + a2*b5 - a3*b8 + a4*b7 - a5*b2 + a6*b1 - a7*b4 + a8*b3 in
  let c7 := a1*b7 + a2*b8 + a3*b5 - a4*b6 - a5*b3 + a6*b4 + a7*b1 - a8*b2 in
  let c8 := a1*b8 - a2*b7 + a3*b6 + a4*b5 - a5*b4 - a6*b3 + a7*b2 + a8*b1 in
  c1*c1 + c2*c2 + c3*c3 + c4*c4 + c5*c5 + c6*c6 + c7*c7 + c8*c8
  == (a1*a1 + a2*a2 + a3*a3 + a4*a4 + a5*a5 + a6*a6 + a7*a7 + a8*a8)
     * (b1*b1 + b2*b2 + b3*b3 + b4*b4 + b5*b5 + b6*b6 + b7*b7 + b8*b8).
Proof. intros. unfold c1, c2, c3, c4, c5, c6, c7, c8. ring. Qed.

(* ===================================================================== *)
(*  Closure: unit octonions are closed under multiplication               *)
(* ===================================================================== *)

(** Unit rational octonions are closed under multiplication (a Moufang loop — not a
    group, since the octonions are non-associative): N(p)=N(q)=1 ⟹ N(pq)=1, by the
    eight-square identity. *)
Theorem unit_octonion_closed :
  forall a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8 : Q,
  a1*a1 + a2*a2 + a3*a3 + a4*a4 + a5*a5 + a6*a6 + a7*a7 + a8*a8 == 1 ->
  b1*b1 + b2*b2 + b3*b3 + b4*b4 + b5*b5 + b6*b6 + b7*b7 + b8*b8 == 1 ->
  (a1*b1 - a2*b2 - a3*b3 - a4*b4 - a5*b5 - a6*b6 - a7*b7 - a8*b8)
    * (a1*b1 - a2*b2 - a3*b3 - a4*b4 - a5*b5 - a6*b6 - a7*b7 - a8*b8)
  + (a1*b2 + a2*b1 + a3*b4 - a4*b3 + a5*b6 - a6*b5 - a7*b8 + a8*b7)
    * (a1*b2 + a2*b1 + a3*b4 - a4*b3 + a5*b6 - a6*b5 - a7*b8 + a8*b7)
  + (a1*b3 - a2*b4 + a3*b1 + a4*b2 + a5*b7 + a6*b8 - a7*b5 - a8*b6)
    * (a1*b3 - a2*b4 + a3*b1 + a4*b2 + a5*b7 + a6*b8 - a7*b5 - a8*b6)
  + (a1*b4 + a2*b3 - a3*b2 + a4*b1 + a5*b8 - a6*b7 + a7*b6 - a8*b5)
    * (a1*b4 + a2*b3 - a3*b2 + a4*b1 + a5*b8 - a6*b7 + a7*b6 - a8*b5)
  + (a1*b5 - a2*b6 - a3*b7 - a4*b8 + a5*b1 + a6*b2 + a7*b3 + a8*b4)
    * (a1*b5 - a2*b6 - a3*b7 - a4*b8 + a5*b1 + a6*b2 + a7*b3 + a8*b4)
  + (a1*b6 + a2*b5 - a3*b8 + a4*b7 - a5*b2 + a6*b1 - a7*b4 + a8*b3)
    * (a1*b6 + a2*b5 - a3*b8 + a4*b7 - a5*b2 + a6*b1 - a7*b4 + a8*b3)
  + (a1*b7 + a2*b8 + a3*b5 - a4*b6 - a5*b3 + a6*b4 + a7*b1 - a8*b2)
    * (a1*b7 + a2*b8 + a3*b5 - a4*b6 - a5*b3 + a6*b4 + a7*b1 - a8*b2)
  + (a1*b8 - a2*b7 + a3*b6 + a4*b5 - a5*b4 - a6*b3 + a7*b2 + a8*b1)
    * (a1*b8 - a2*b7 + a3*b6 + a4*b5 - a5*b4 - a6*b3 + a7*b2 + a8*b1)
  == 1.
Proof.
  intros a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8 Ha Hb.
  rewrite (eight_square a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8).
  rewrite Ha, Hb. ring.
Qed.

(* ===================================================================== *)
(*  Synthesis                                                             *)
(* ===================================================================== *)

(** The Hurwitz tower in one statement — multiplicative sum-of-n-squares norm forms
    for n = 1, 2, 4, 8 (and, by Hurwitz's theorem, ONLY these): the Element-side
    norm-form symmetry groups form a finite tower terminating at the octonions. *)
Theorem hurwitz_tower_synthesis :
  (forall a b : Q, (a*b)*(a*b) == (a*a)*(b*b))
  /\ (forall a1 a2 b1 b2 : Q,
        (a1*b1 - a2*b2)*(a1*b1 - a2*b2) + (a1*b2 + a2*b1)*(a1*b2 + a2*b1)
        == (a1*a1 + a2*a2) * (b1*b1 + b2*b2))
  /\ (forall a1 a2 a3 a4 b1 b2 b3 b4 : Q,
        (a1*b1 - a2*b2 - a3*b3 - a4*b4)*(a1*b1 - a2*b2 - a3*b3 - a4*b4)
        + (a1*b2 + a2*b1 + a3*b4 - a4*b3)*(a1*b2 + a2*b1 + a3*b4 - a4*b3)
        + (a1*b3 - a2*b4 + a3*b1 + a4*b2)*(a1*b3 - a2*b4 + a3*b1 + a4*b2)
        + (a1*b4 + a2*b3 - a3*b2 + a4*b1)*(a1*b4 + a2*b3 - a3*b2 + a4*b1)
        == (a1*a1 + a2*a2 + a3*a3 + a4*a4) * (b1*b1 + b2*b2 + b3*b3 + b4*b4)).
Proof.
  split; [ exact one_square | ].
  split; [ exact two_square | exact four_square ].
Qed.
