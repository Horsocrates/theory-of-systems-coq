(** * MetallicRatios.v — self-similar shapes have role-limit (quadratic-irrational)
      ratios: A-paper √2 (halving-invariant), the golden rectangle φ (√5), the silver
      ratio 1+√2.  Each is the fixed point of a "remove-and-rescale" process; and the
      whole metallic family r²=nr+1 is irrational because the discriminant n²+4 is
      never a perfect square.

    Elements: the rational coordinates; the integers n, n²+4; the shapes (L1 + P4)
    Roles:    self-similar shapes (A-paper, golden rectangle, silver) have ratios =
              quadratic-irrational ROLE-LIMITS (the fixed points of the rescaling
              process); rational-ratio shapes are NOT self-similar; the discriminant
              n²+4 (never a perfect square) = the obstruction
    Rules:    a self-similar shape ⟺ its ratio r satisfies a fixed-point equation
              (halving r²=2, golden r²=r+1, silver r²=2r+1, metallic r²=nr+1); the
              discriminant n²+4; the quadratic formula

    THE DEEP POINT — self-similarity forces a role-limit ratio.  A shape that
    reproduces itself under a natural "remove a piece and rescale" operation has an
    aspect ratio r pinned by a fixed-point equation, and these ratios are exactly the
    quadratic irrationals — role-limits.  Three classics:
      · A-series PAPER: halving a r:1 sheet (cut the long side) gives a 1:(r/2) sheet;
        for the proportion to be preserved, r = 2/r, i.e. r²=2 — so r=√2, irrational
        (`paper_ratio_irrational`).  This is WHY A4 has ratio √2: halving preserves
        proportions, and only the irrational √2 does that.
      · the GOLDEN rectangle: remove a square and the remainder is similar, r=1+1/r,
        i.e. r²=r+1 — r=φ, irrational (`golden_ratio_irrational`, via √5).
      · the SILVER ratio: r²=2r+1 — r=1+√2, irrational (`silver_ratio_irrational`,
        via (r−1)²=2).
    And the WHOLE metallic family r²=nr+1 (n≥1) is irrational: a rational root would
    make the discriminant n²+4 a perfect square, but n²+4 is NEVER a perfect square
    (`n2_plus_4_not_square`: for n≥2 it lies strictly between n² and (n+1)²; for n=1
    it is 5) — no integer squares to it.  A rational-ratio shape, by contrast, is not
    self-similar: the rescaling process terminates instead of closing on a fixed
    point.  Self-similarity ⟺ a role-limit ratio.

    ============ E/R/R разбор ============
      Rules (L5): самоподобие ⟺ r удовлетворяет уравнению неподвижной точки (r²=2, r²=r+1,
                  r²=2r+1, r²=nr+1); дискриминант n²+4; квадратная формула.
      Roles (L4): самоподобные формы (A-бумага, золотой прямоугольник, серебряное) = role-limit
                  отношения; рациональные формы не самоподобны; n²+4 не полный квадрат = обструкция.
      Elements  : рац. координаты; целые n, n²+4; формы (L1+P4).
    ДИАГНОСТИКА (P4): самоподобие форсирует role-limit-отношение (квадратичную иррациональность);
    A-бумага √2, золотой φ (√5), серебряное 1+√2 — неподвижные точки процесса перемасштабирования.
    Металлическая семья иррациональна (n²+4 никогда не полный квадрат). Самоподобие ⟺ role-limit.

    STATUS: 6 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lia ZArith Lqa.
From ToS Require Import analysis.Sqrt2Irrational.
From ToS Require Import stdlib.GoldenFibonacci.

(* ================================================================= *)
(** ** The discriminant n²+4 is never a perfect square (n ≥ 1)        *)
(* ================================================================= *)

Open Scope Z_scope.

(** No integer's square lies strictly between two consecutive squares. *)
Lemma no_sq_between : forall k m : Z,
  0 <= k -> 0 <= m -> k*k < m*m -> m*m < (k+1)*(k+1) -> False.
Proof.
  intros k m Hk Hm H1 H2.
  assert (k < m) by nia.
  assert (m < k + 1) by nia.
  lia.
Qed.

(** ★ The metallic discriminant n²+4 is never a perfect square (n≥1): for n≥2 it is
    strictly between n² and (n+1)²; for n=1 it is 5.  So r²=nr+1 has no rational root
    — the whole metallic family is irrational. *)
Lemma n2_plus_4_not_square : forall n m : Z, 1 <= n -> m*m <> n*n + 4.
Proof.
  intros n m Hn Heq.
  set (p := Z.abs m).
  assert (Hp : 0 <= p) by apply Z.abs_nonneg.
  assert (Hpp : p * p = n*n + 4).
  { unfold p. rewrite <- Z.abs_mul. rewrite Z.abs_eq by nia. exact Heq. }
  destruct (Z.eq_dec n 1) as [Hn1 | Hn1].
  - subst n. apply (no_sq_between 2 p); nia.
  - assert (Hn2 : 2 <= n) by lia.
    apply (no_sq_between n p); nia.
Qed.

(* ================================================================= *)
(** ** The three classic self-similar ratios (all role-limits)        *)
(* ================================================================= *)

Open Scope Q_scope.

(** A-paper: the halving-invariant ratio r²=2 is irrational — why A4 is 1:√2. *)
Theorem paper_ratio_irrational : ~ (exists r : Q, r * r == 2).
Proof. exact sqrt2_not_in_Q. Qed.

(** Golden rectangle: r²=r+1 is irrational (φ, via √5). *)
Theorem golden_ratio_irrational : ~ (exists r : Q, r * r == r + 1).
Proof. exact no_rational_golden. Qed.

(** Silver ratio: r²=2r+1 is irrational (1+√2, via (r−1)²=2). *)
Theorem silver_ratio_irrational : ~ (exists r : Q, r * r == 2 * r + 1).
Proof.
  intros [r Hr]. apply sqrt2_not_in_Q. exists (r - 1).
  assert (H : (r - 1) * (r - 1) == r * r - 2 * r + 1) by ring.
  rewrite H, Hr. ring.
Qed.

(* ================================================================= *)
(** ** Synthesis                                                      *)
(* ================================================================= *)

(** Self-similar shapes have role-limit ratios, split by the finitization boundary:
      (a) the metallic discriminant n²+4 is never a perfect square (n≥1) — the whole
          metallic family r²=nr+1 is irrational;
      (b) A-paper: r²=2 (√2) is irrational;
      (c) the golden rectangle: r²=r+1 (φ) is irrational;
      (d) the silver ratio: r²=2r+1 (1+√2) is irrational. *)
Theorem metallic_synthesis :
  (forall n m : Z, (1 <= n)%Z -> (m*m <> n*n + 4)%Z)
  /\ ~ (exists r : Q, r * r == 2)
  /\ ~ (exists r : Q, r * r == r + 1)
  /\ ~ (exists r : Q, r * r == 2 * r + 1).
Proof.
  split; [ exact n2_plus_4_not_square | ].
  split; [ exact paper_ratio_irrational | ].
  split; [ exact golden_ratio_irrational | exact silver_ratio_irrational ].
Qed.
