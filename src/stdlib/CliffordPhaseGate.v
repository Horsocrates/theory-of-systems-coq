(** * CliffordPhaseGate.v — direction ① (second brick): S vs T, formally.
      The Clifford phase S is a TERMINATING process (rational point i, order 4 —
      it closes into an Element); the non-Clifford T's phase is a NON-TERMINATING
      R-process (the Pell √2-process) — a role-limit. REUSES the repo's √2 result.

    Elements: rational approximants of the 45° point — the Pell triangles
              (3,4,5),(20,21,29),(119,120,169),… (PythagoreanDensity.v)
    Roles:    S-gate phase = i (a process that CLOSES at order 4 → an Element);
              T-gate phase = the 45° point = the √2 R-process (never closes)
    Rules:    i⁴ = 1 (S terminates); the Pell recurrence t_{n+1}=1/(2+t_n) generates
              the T-process; `no_rational_sqrt2` ⟹ it never terminates in an Element

    ============ E/R/R разбор: фаза T — это ПРОЦЕСС, не «иррациональное число» =====
    Ключ (как в FeigenbaumERR.v / AperyConstantERR.v): иррациональное в ToS — это
    R-ПРОЦЕСС (полный E/R/R-объект), а НЕ только «Правило, запрещающее Элемент».
    «Иррационально ли оно» — НЕ-ВОПРОС в P4 (FeigenbaumERR): никакой рациональный
    объект НЕ ЕСТЬ точка 45° изначально; есть лишь последовательность приближений.
      Elements (L1): рациональные приближения — тройки Пелля (3,4,5)→(20,21,29)→
        (119,120,169)→… (PythagoreanDensity.v); и/или сходимости √2 (Ньютон/цепная
        дробь). Каждое — конкретный Q-Element.
      Rules (L5): порождающее правило — рекуррентность Пелля t_{n+1}=1/(2+t_n)
        (PythagoreanDensity.v); эквивалентно Ньютон x→(x+2/x)/2 или алгебраическое
        x²=2 (√2 алгебраично, IrrationalsClassification.v). Скорость — свойство
        Правила, не предела.
      Roles (L4): диагональ единичного квадрата; гипотенуза равнобедренного; фаза
        T-гейта; нормировка Адамара H/√2.
    ВЫВОД: точка 45° = T-фаза ЕСТЬ этот R-процесс Пелля. `no_rational_sqrt2` — НЕ
    «доказательство иррациональности», а доказательство, что процесс НЕ ЗАВЕРШАЕТСЯ
    Элементом (только-процесс) — это КОРРЕКТНЫЙ P4-статус, не дефект. Поэтому
    role-limit = НЕЗАВЕРШАЮЩИЙСЯ процесс (положительно), а не «Роль без Элемента».
    КОНТРАСТ: фаза S = i — процесс, который ЗАВЕРШАЕТСЯ (замыкается на порядке 4 =
    Element). Граница Клиффорда = граница финитизации = ЗАВЕРШАЮЩИЙСЯ процесс
    (Element/Clifford/симулируемо) vs НЕЗАВЕРШАЮЩИЙСЯ процесс (role-limit/не-Clifford).
    ДИАГНОСТИКА (P4): не «T иррационален» (не-вопрос), а «T-фаза = незавершающийся
    R-процесс Пелля» (положительно); `no_rational_sqrt2` = не-завершаемость, не дефект.

    STATUS: 2 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import stdlib.PythagoreanTriples.
From ToS Require Import stdlib.FinitizationBoundary.
From ToS Require Import analysis.Sqrt2Irrational.
Open Scope Q_scope.

(* ===== The 45° point IS the non-terminating √2 process (reuses canonical √2) === *)

(** The 45° point (T-gate phase) IS the √2 R-process — Elements = the Pell
    triangles (PythagoreanDensity.v), Rule = the Pell recurrence. This lemma is
    NOT "proof of irrationality"; it is the proof that the process NEVER TERMINATES
    in an Element (no a∈ℚ with 2a²=1) — the P4-correct status of a genuine R-process,
    not a defect. Derived from `no_rational_sqrt2`: 2a²=1 ⟹ (2a)²=2, impossible. *)
Lemma no_rational_45 : ~ exists a : Q, 2 * a * a == 1.
Proof.
  intros [a Ha].
  apply (no_rational_sqrt2 (2 * a)).
  assert (H : (2 * a) * (2 * a) == 2 * (2 * a * a)) by ring.
  rewrite H, Ha. ring.
Qed.

(* ===== The formal S vs T separation across the finitization boundary ==== *)

(** Clifford S (phase i, order 4) is a TERMINATING process — it closes; its
    terminus is an Element (the ℚ-finite Clifford core). Non-Clifford T's phase
    (the 45° point) is a NON-TERMINATING process (the Pell √2-process) — a
    role-limit. The Clifford/non-Clifford divide IS the finitization boundary, by
    theorem: terminating process vs non-terminating process. *)
Theorem clifford_S_vs_T :
  (* S-phase = a TERMINATING process: i = (0,1) closes at order 4 → an Element *)
  (fst (cmul (cmul (cmul i_pt i_pt) i_pt) i_pt) == 1 /\
   snd (cmul (cmul (cmul i_pt i_pt) i_pt) i_pt) == 0)
  /\
  (* T-phase = a NON-TERMINATING process: no rational 45° point closes it (role-limit) *)
  (~ exists a : Q, 2 * a * a == 1).
Proof.
  split; [ exact quarter_turn_closes | exact no_rational_45 ].
Qed.
