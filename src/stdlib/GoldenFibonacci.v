(** * GoldenFibonacci.v — the golden ratio as the canonical role-limit PROCESS for
      √5: Fibonacci convergents are finite-actual Elements, φ is the role-limit, and
      Cassini's identity Fₙ₊₁²−FₙFₙ₊₂=(−1)ⁿ (always ±1, NEVER 0) is the machine-
      checked witness that the process never terminates.

    Elements: the integers Fₙ (each finite, computable, positive/growing); the
              rational convergents Fₙ₊₁/Fₙ; the rational 5; the sign ±1 (L1 + P4)
    Roles:    φ = the ROLE-LIMIT (the √5 of ④ — forbids order 5 / the icosahedron);
              Fₙ₊₁/Fₙ = the finite-actual Element approximants; Cassini's (−1)ⁿ
              (never 0) = the witness of NON-TERMINATION
    Rules:    the Fibonacci recurrence Fₙ₊₁=Fₙ+Fₙ₋₁; the defining φ²=φ+1; Cassini
              Fₙ₊₁²−FₙFₙ₊₂=(−1)ⁿ; the bridge (2φ−1)²=5

    THE DEEP POINT — every quadratic role-limit has a canonical generating PROCESS,
    and for √5 it is the Fibonacci sequence.  In FinitistQM.v (⑤) we gave √2 its
    process — the Pell convergents pₖ/qₖ with the error pₖ²−2qₖ²=±1 never 0
    (`pell_abs`).  Here is the EXACT √5/φ analogue:
      · φ = (1+√5)/2 is the role-limit.  It is the SAME √5 that excludes the
        order-5 / icosahedral symmetry in `CrystallographicRestriction.v` (④):
        no rational satisfies x²=x+1 (`no_rational_golden`), because (2x−1)²=5 has
        no rational root (`sqrt5_not_in_Q`).
      · Fₙ₊₁/Fₙ are the finite-actual Element approximants — each a rational built
        from two computable integers.
      · Cassini's identity Fₙ₊₁²−Fₙ·Fₙ₊₂ = (−1)ⁿ (`cassini`) is ALWAYS ±1 and NEVER
        0 (`golden_never_exact`).  The error of the convergent never vanishes — a
        FORMAL proof that the Fibonacci process does not terminate at any rational,
        i.e. φ is a genuine role-limit, not an Element.

    So ④'s order-5 obstruction gets its canonical process, completing the parallel:
    √2 ↔ Pell (⑤), √5 ↔ Fibonacci (here).  "Is φ a number?" is the non-question
    (P4): φ IS the process; its terminus (an Element) does not exist, and Cassini
    proves it.

    ============ E/R/R разбор ============
      Rules (L5): рекуррента Fₙ₊₁=Fₙ+Fₙ₋₁; φ²=φ+1; Кассини Fₙ₊₁²−FₙFₙ₊₂=(−1)ⁿ;
                  мост (2φ−1)²=5.
      Roles (L4): φ = role-limit (√5 из ④, запрещает икосаэдр); Fₙ₊₁/Fₙ = конечно-
                  актуальные Element-приближенцы; Кассини (−1)ⁿ (≠0) = свидетель
                  незавершаемости.
      Elements  : целые Fₙ (конечны, положительны, растут); конвергенты; рац. 5; ±1 (L1+P4).
    ДИАГНОСТИКА (P4): φ — role-limit (незавершающийся Fibonacci-процесс), Fₙ₊₁/Fₙ — его
    приближенцы; «число ли φ» = не-вопрос; Кассини ≠0 = формальное доказательство нетерминации.
    Та же форма, что √2-Pell (⑤); связывает ④ (√5 запрещает икосаэдр) с его процессом.

    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia QArith Lqa.
From ToS Require Import analysis.Sqrt5Irrational.

Open Scope Z_scope.

(* ===================================================================== *)
(*  The Fibonacci sequence over ℤ (nested match for the guard checker)    *)
(* ===================================================================== *)

Fixpoint fib (n : nat) : Z :=
  match n with
  | O => 0
  | S k => match k with
           | O => 1
           | S j => fib k + fib j
           end
  end.

(** The defining recurrence, definitionally: Fₙ₊₂ = Fₙ₊₁ + Fₙ. *)
Lemma fib_SS : forall n, fib (S (S n)) = fib (S n) + fib n.
Proof. reflexivity. Qed.

(** Fibonacci numbers are non-negative (carried as a pair for the two-step rec). *)
Lemma fib_nonneg_pair : forall n, 0 <= fib n /\ 0 <= fib (S n).
Proof.
  induction n.
  - split; simpl; lia.
  - destruct IHn as [H1 H2]. split.
    + exact H2.
    + rewrite fib_SS. lia.
Qed.

(** Fₙ₊₁ > 0: the process produces genuine (positive, growing) integer Elements. *)
Lemma fib_pos : forall n, 0 < fib (S n).
Proof.
  induction n.
  - simpl. lia.
  - rewrite fib_SS. destruct (fib_nonneg_pair n) as [H1 _]. lia.
Qed.

(* ===================================================================== *)
(*  The sign (−1)ⁿ                                                         *)
(* ===================================================================== *)

Lemma pow_neg1_S : forall n, (-1)^(Z.of_nat (S n)) = - ((-1)^(Z.of_nat n)).
Proof.
  intro n. rewrite Nat2Z.inj_succ, Z.pow_succ_r by apply Nat2Z.is_nonneg.
  ring.
Qed.

(** (−1)ⁿ is always ±1 — in particular never 0. *)
Lemma pow_neg1_pm1 : forall n, (-1)^(Z.of_nat n) = 1 \/ (-1)^(Z.of_nat n) = -1.
Proof.
  induction n.
  - left. reflexivity.
  - rewrite pow_neg1_S. destruct IHn as [H | H]; rewrite H.
    + right. reflexivity.
    + left. reflexivity.
Qed.

(* ===================================================================== *)
(*  Cassini's identity and the never-exact witness                        *)
(* ===================================================================== *)

(** Cassini: Fₙ₊₁² − Fₙ·Fₙ₊₂ = (−1)ⁿ. *)
Theorem cassini :
  forall n, fib (S n) * fib (S n) - fib n * fib (S (S n)) = (-1)^(Z.of_nat n).
Proof.
  induction n.
  - vm_compute. reflexivity.
  - rewrite pow_neg1_S, <- IHn, (fib_SS (S n)), (fib_SS n). ring.
Qed.

(** ★ The convergent error NEVER vanishes: Fₙ₊₁² − Fₙ·Fₙ₊₂ ≠ 0 for all n.  The
    Fibonacci process does not terminate at any rational — φ is a role-limit. *)
Theorem golden_never_exact :
  forall n, fib (S n) * fib (S n) - fib n * fib (S (S n)) <> 0.
Proof.
  intro n. rewrite cassini.
  destruct (pow_neg1_pm1 n) as [H | H]; rewrite H; discriminate.
Qed.

(* ===================================================================== *)
(*  φ is irrational: no rational satisfies x² = x + 1 (via √5)            *)
(* ===================================================================== *)

(** No rational is the golden ratio: x²=x+1 ⟹ (2x−1)²=5, impossible over ℚ.
    This is the SAME √5 that forbids the order-5 / icosahedral symmetry (④). *)
Theorem no_rational_golden : ~ (exists q : Q, (q * q == q + 1)%Q).
Proof.
  intros [q Hq]. apply sqrt5_not_in_Q. exists (2 * q - 1)%Q.
  assert (H : ((2*q - 1) * (2*q - 1) == 4 * (q * q) - 4 * q + 1)%Q) by ring.
  rewrite H, Hq. ring.
Qed.

(* ===================================================================== *)
(*  Synthesis                                                             *)
(* ===================================================================== *)

(** The golden ratio as the canonical role-limit process for √5, in one statement:
      (a) Cassini's identity Fₙ₊₁²−Fₙ·Fₙ₊₂ = (−1)ⁿ;
      (b) the convergent error is NEVER 0 — the process never terminates;
      (c) φ is irrational (no rational solves x²=x+1) — the role-limit;
      (d) √5 itself is irrational — the role-limit that forbids the icosahedron (④). *)
Theorem golden_fibonacci_synthesis :
  (forall n, fib (S n) * fib (S n) - fib n * fib (S (S n)) = (-1)^(Z.of_nat n))
  /\ (forall n, fib (S n) * fib (S n) - fib n * fib (S (S n)) <> 0)
  /\ ~ (exists q : Q, (q * q == q + 1)%Q)
  /\ ~ (exists r : Q, (r * r == 5)%Q).
Proof.
  split; [ exact cassini | ].
  split; [ exact golden_never_exact | ].
  split; [ exact no_rational_golden | exact sqrt5_not_in_Q ].
Qed.
