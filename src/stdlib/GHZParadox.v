(** * GHZParadox.v — the Greenberger–Horne–Zeilinger (GHZ/Mermin) paradox over ℤ:
      quantum nonlocality at its most ELEMENT — perfect (probability-1) correlations,
      all outcomes ±1 (integers), an algebraic contradiction with NO inequality, NO
      statistics, and NO √2.  Zero continuum content.

    Elements: the ±1 measurement outcomes (integers!); the integer correlations;
              the contradiction 1 = −1 (L1 + P4)
    Roles:    the GHZ perfect correlations (Elements, ±1 exactly) vs a local-realistic
              (hidden-variable) assignment, which the three Y-correlations FORCE to
              predict XXX=−1 — opposite to the quantum XXX=+1; GHZ nonlocality =
              all-or-nothing, no statistics, no inequality, no √2 — the SHARPEST
              Element-side nonlocality (vs Bell, where √2 sat at the Tsirelson optimum)
    Rules:    the ±1 outcome constraint v²=1; the four GHZ stabiliser correlations
              (XXX=+1, XYY=YXY=YYX=−1); the product identity — the three Y-correlations
              multiply to XXX (the Y² factors cancel), forcing XXX=−1 classically

    THE DEEP POINT — GHZ is quantum nonlocality stripped to pure Element content.
    Bell (`BellTsirelson.v`, H6) already showed the violation is rational (an Element),
    with only the Tsirelson optimum 2√2 a role-limit.  GHZ goes further: there is NO
    inequality and NO optimum at all.  Three parties, each measuring X or Y with
    outcome ±1.  The quantum GHZ state forces FOUR perfect correlations:
      XXX = +1,   XYY = −1,   YXY = −1,   YYX = −1.
    A local hidden-variable model assigns definite ±1 values x_i, y_i.  Multiplying
    the three Y-correlations, the squares y_i² = 1 cancel and the product equals
    x1·x2·x3 — so the model FORCES XXX = (−1)·(−1)·(−1) = −1 (`ghz_lhv_forces_minus1`).
    But the quantum prediction is XXX = +1.  No local assignment reproduces all four
    (`ghz_no_lhv`).  Everything is ±1 and integer: the contradiction 1 = −1 is purely
    algebraic — not a violated inequality, not a statistical excess, and there is no √2
    anywhere (not even the Tsirelson one).  Quantum nonlocality is fully finite-actual;
    its continuum content is ZERO.

    ============ E/R/R разбор ============
      Rules (L5): v²=1 (исход ±1); GHZ-корреляции XXX=+1, XYY=YXY=YYX=−1; произведение
                  трёх Y-корреляций = XXX (квадраты Y сокращаются) ⟹ LHV форсирует XXX=−1.
      Roles (L4): совершенные GHZ-корреляции (Elements, ±1) vs LHV (форсирует XXX=−1,
                  против QM +1); GHZ = всё-или-ничего, без неравенства/статистики/√2 —
                  самая Element-нелокальность (резче Белла H6).
      Elements  : значения ±1 (целые); целочисленные корреляции; противоречие 1=−1 (L1+P4).
    ДИАГНОСТИКА (P4): GHZ — нелокальность в чистейшем Element-виде; всё ±1 (ℤ), противоречие
    алгебраическое; НОЛЬ континуум-содержания (даже √2 Цирельсона нет). Самодостаточно над ℤ.

    STATUS: 4 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

(* ===================================================================== *)
(*  A local hidden-variable model: each party i assigns ±1 values         *)
(*  x_i (its X outcome) and y_i (its Y outcome).                          *)
(* ===================================================================== *)

(** ★ The three Y-correlations being −1 FORCE the classical XXX = −1: multiplying
    them, the squares y_i² = 1 cancel and the product is x1·x2·x3. *)
Theorem ghz_lhv_forces_minus1 :
  forall x1 x2 x3 y1 y2 y3 : Z,
    y1 * y1 = 1 -> y2 * y2 = 1 -> y3 * y3 = 1 ->
    x1 * y2 * y3 = -1 -> y1 * x2 * y3 = -1 -> y1 * y2 * x3 = -1 ->
    x1 * x2 * x3 = -1.
Proof.
  intros x1 x2 x3 y1 y2 y3 Hy1 Hy2 Hy3 Hxyy Hyxy Hyyx.
  assert (Key : (x1 * y2 * y3) * (y1 * x2 * y3) * (y1 * y2 * x3)
              = (x1 * x2 * x3) * (y1 * y1) * (y2 * y2) * (y3 * y3)) by ring.
  rewrite Hxyy, Hyxy, Hyyx, Hy1, Hy2, Hy3 in Key.
  lia.
Qed.

(** ★ No local hidden-variable model reproduces the quantum GHZ correlations: the
    quantum XXX = +1 is incompatible with the three Y-correlations = −1. *)
Theorem ghz_no_lhv :
  forall x1 x2 x3 y1 y2 y3 : Z,
    y1 * y1 = 1 -> y2 * y2 = 1 -> y3 * y3 = 1 ->
    x1 * x2 * x3 = 1 ->
    x1 * y2 * y3 = -1 -> y1 * x2 * y3 = -1 -> y1 * y2 * x3 = -1 ->
    False.
Proof.
  intros x1 x2 x3 y1 y2 y3 Hy1 Hy2 Hy3 Hxxx Hxyy Hyxy Hyyx.
  pose proof (ghz_lhv_forces_minus1 x1 x2 x3 y1 y2 y3 Hy1 Hy2 Hy3 Hxyy Hyxy Hyyx) as H.
  rewrite Hxxx in H. discriminate.
Qed.

(** The local-realistic prediction is consistent and gives XXX = −1: an explicit
    ±1 assignment satisfying the three Y-correlations and (classically) XXX = −1.
    So the disagreement with quantum mechanics is exactly the sign of XXX. *)
Theorem ghz_lhv_predicts_minus1 :
  exists x1 x2 x3 y1 y2 y3 : Z,
    x1 * x1 = 1 /\ x2 * x2 = 1 /\ x3 * x3 = 1 /\
    y1 * y1 = 1 /\ y2 * y2 = 1 /\ y3 * y3 = 1 /\
    x1 * y2 * y3 = -1 /\ y1 * x2 * y3 = -1 /\ y1 * y2 * x3 = -1 /\
    x1 * x2 * x3 = -1.
Proof.
  exists 1, 1, (-1), 1, 1, (-1). repeat split; reflexivity.
Qed.

(* ===================================================================== *)
(*  Synthesis                                                             *)
(* ===================================================================== *)

(** GHZ over ℤ in one statement — the sharpest Element-side nonlocality:
      (a) any ±1 hidden-variable assignment satisfying the three Y=−1 correlations
          FORCES XXX = −1 (the classical prediction);
      (b) such an assignment exists (the classical prediction is consistent);
      (c) yet the quantum XXX = +1 is incompatible — no local model reproduces it.
    All correlations are ±1 integers; the contradiction is algebraic (1 = −1), with
    no inequality, no statistics, and no √2 — zero continuum content. *)
Theorem ghz_synthesis :
  (forall x1 x2 x3 y1 y2 y3 : Z,
     y1*y1=1 -> y2*y2=1 -> y3*y3=1 ->
     x1*y2*y3=-1 -> y1*x2*y3=-1 -> y1*y2*x3=-1 -> x1*x2*x3 = -1)
  /\ (exists x1 x2 x3 y1 y2 y3 : Z,
        x1*x1=1 /\ x2*x2=1 /\ x3*x3=1 /\ y1*y1=1 /\ y2*y2=1 /\ y3*y3=1 /\
        x1*y2*y3=-1 /\ y1*x2*y3=-1 /\ y1*y2*x3=-1 /\ x1*x2*x3=-1)
  /\ (forall x1 x2 x3 y1 y2 y3 : Z,
        y1*y1=1 -> y2*y2=1 -> y3*y3=1 -> x1*x2*x3=1 ->
        x1*y2*y3=-1 -> y1*x2*y3=-1 -> y1*y2*x3=-1 -> False).
Proof.
  split; [ exact ghz_lhv_forces_minus1 | ].
  split; [ exact ghz_lhv_predicts_minus1 | exact ghz_no_lhv ].
Qed.
