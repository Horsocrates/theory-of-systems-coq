(** * Sqrt3Pell.v — √3 as the canonical role-limit PROCESS: the Pell sequence
      x²−3y²=1.  Completes the triple — √2 ↔ Pell (⑤), √5 ↔ Fibonacci (Расш⁷),
      √3 ↔ Pell (here).

    Elements: the integers xₖ, yₖ (each finite, positive, growing); the rational
              invariant 1; the rational 3 (L1 + P4)
    Roles:    √3 = the ROLE-LIMIT (it forbids the rational 60°-point — there is no
              rational (½, √3/2) on the circle; the √3 that excluded cos=±½ in the
              capstone ①); xₖ/yₖ = the finite-actual Element approximants; the
              invariant =1 (never 0) = the witness of NON-TERMINATION; the unit
              2+√3 = the Rule driving the process
    Rules:    the norm-1 unit 2+√3 generating (x,y)↦(2x+3y, x+2y); the invariant
              x²−3y²=1; (√3)²=3

    THE DEEP POINT — each of the three quadratic role-limits has a canonical
    generating PROCESS, and for √3 it is the Pell sequence x²−3y²=1.  Multiplying by
    the fundamental unit 2+√3 (norm (2+√3)(2−√3)=1) sends (x,y) to (2x+3y, x+2y) and
    PRESERVES the form x²−3y² exactly, so starting from (1,0) every term satisfies
    xₖ²−3yₖ²=1 (`pell3_invariant`).  Since x²−3y²=−1 is unsolvable mod 4, the residual
    is ALWAYS +1 — even cleaner than the ±1 of √2 (Pell) and √5 (Cassini): it is
    NEVER 0 (`pell3_never_zero`), a formal proof that the convergents xₖ/yₖ never
    reach √3, i.e. √3 is a role-limit, not an Element.

    This completes the surd↔process family:
      · √2 ↔ Pell  pₖ²−2qₖ²=±1   (FinitistQM.v, ⑤)   — kills the T-gate
      · √5 ↔ Fibonacci  Fₙ₊₁²−FₙFₙ₊₂=(−1)ⁿ (GoldenFibonacci.v) — kills the icosahedron
      · √3 ↔ Pell  xₖ²−3yₖ²=1     (here)              — kills the rational 60°-point
    Three quadratic role-limits (√2/√3/√5), three obstructed finite structures
    (T-gate/60°/icosahedron), three canonical Pell-type processes.  "Is √3 a number?"
    is the non-question (P4): √3 IS the process; its terminus does not exist, and the
    invariant proves it.

    ============ E/R/R разбор ============
      Rules (L5): единица нормы 1 (2+√3), рекуррента (x,y)↦(2x+3y,x+2y); инвариант
                  x²−3y²=1; (√3)²=3.
      Roles (L4): √3 = role-limit (запрещает рациональную точку 60°, ①); xₖ/yₖ =
                  конечно-актуальные Element-приближенцы; инвариант =1 (≠0) =
                  свидетель незавершаемости.
      Elements  : целые xₖ,yₖ (конечны, положительны, растут); рац. 1; рац. 3 (L1+P4).
    ДИАГНОСТИКА (P4): √3 — role-limit (незавершающийся Pell-процесс), xₖ/yₖ — приближенцы;
    x²−3y²=1≠0 = формальная нетерминация. Замыкает тройку √2↔Pell/√5↔Fibonacci/√3↔Pell —
    каждый из трёх role-limit (T-гейт/икосаэдр/60°) имеет канонический процесс.

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia QArith Lqa.
From ToS Require Import analysis.Sqrt3Irrational.

Open Scope Z_scope.

(* ===================================================================== *)
(*  The Pell sequence for √3: (x,y) ↦ (2x+3y, x+2y), starting from (1,0)   *)
(* ===================================================================== *)

Fixpoint xy3 (k : nat) : Z * Z :=
  match k with
  | O => (1, 0)
  | S k' => let '(x, y) := xy3 k' in (2 * x + 3 * y, x + 2 * y)
  end.

Definition x3 (k : nat) : Z := fst (xy3 k).
Definition y3 (k : nat) : Z := snd (xy3 k).

(** The recurrence, exposed as a pair equation. *)
Lemma xy3_S : forall k, xy3 (S k) = (2 * x3 k + 3 * y3 k, x3 k + 2 * y3 k).
Proof. intro k. cbn [xy3]. unfold x3, y3. destruct (xy3 k) as [x y]. reflexivity. Qed.

Lemma x3_S : forall k, x3 (S k) = 2 * x3 k + 3 * y3 k.
Proof. intro k. unfold x3. rewrite xy3_S. reflexivity. Qed.

Lemma y3_S : forall k, y3 (S k) = x3 k + 2 * y3 k.
Proof. intro k. unfold y3. rewrite xy3_S. reflexivity. Qed.

(* ===================================================================== *)
(*  The Pell invariant x² − 3y² = 1, preserved by the norm-1 unit 2+√3    *)
(* ===================================================================== *)

(** Every term satisfies xₖ² − 3yₖ² = 1: the fundamental unit 2+√3 has norm 1,
    so multiplication by it preserves the form exactly. *)
Theorem pell3_invariant : forall k, x3 k * x3 k - 3 * (y3 k * y3 k) = 1.
Proof.
  induction k.
  - vm_compute. reflexivity.
  - rewrite x3_S, y3_S. rewrite <- IHk. ring.
Qed.

(** ★ The residual is NEVER 0: the convergents xₖ/yₖ never reach √3 — a formal
    proof of non-termination ⟹ √3 is a role-limit, not an Element. *)
Theorem pell3_never_zero : forall k, x3 k * x3 k - 3 * (y3 k * y3 k) <> 0.
Proof. intro k. rewrite pell3_invariant. discriminate. Qed.

(* ===================================================================== *)
(*  The Element approximants are positive and growing                     *)
(* ===================================================================== *)

Lemma x3_pos_y3_nonneg : forall k, 0 < x3 k /\ 0 <= y3 k.
Proof.
  induction k.
  - unfold x3, y3; simpl; split; lia.
  - destruct IHk as [Hx Hy]. rewrite x3_S, y3_S. split; lia.
Qed.

(** The denominators yₖ are positive from k≥1: the convergents xₖ/yₖ are genuine,
    growing rational Elements. *)
Lemma y3_pos : forall k, 0 < y3 (S k).
Proof.
  intro k. rewrite y3_S. destruct (x3_pos_y3_nonneg k) as [Hx Hy]. lia.
Qed.

(* ===================================================================== *)
(*  Synthesis                                                             *)
(* ===================================================================== *)

(** √3 as the canonical role-limit process, in one statement:
      (a) the Pell invariant xₖ²−3yₖ² = 1 (the norm-1 unit preserves it);
      (b) the residual is NEVER 0 — the process never terminates;
      (c) the denominators are positive — genuine growing convergents;
      (d) √3 itself is irrational — the role-limit forbidding the rational 60°-point. *)
Theorem sqrt3_pell_synthesis :
  (forall k, x3 k * x3 k - 3 * (y3 k * y3 k) = 1)
  /\ (forall k, x3 k * x3 k - 3 * (y3 k * y3 k) <> 0)
  /\ (forall k, 0 < y3 (S k))
  /\ ~ (exists r : Q, (r * r == 3)%Q).
Proof.
  split; [ exact pell3_invariant | ].
  split; [ exact pell3_never_zero | ].
  split; [ exact y3_pos | exact sqrt3_not_in_Q ].
Qed.
