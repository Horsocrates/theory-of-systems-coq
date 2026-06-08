# Database - cluster `log2`

_Generated from `log2.json` by `generate.ps1` - do not edit by hand; edit the JSON._

**2 files / 21 Qed.** Score distribution: s5=0 / s4=0 / s3=2 / s2=0 / s1=0 / s0=0

---

## #1830 - `src/Log2FunctionalEq.v` - score 3 (new-framing)

**The crest: log2(2^k)=k as a process-equality, H(1/2)=1 bit, functional-equation groundwork**

- **Topic.** ln_pow2 k := k*ln2 and log2_pow2 := (k*ln2)/ln2; the flagship log2_pow2_eq : log2(2^k) ~~ k (Element-collapse via assoc + self-cancellation ln2/ln2 + unit); corollaries k=0,1,3; H2_fair_one : H(1/2) ~~ 1 (fair-coin entropy = exactly one bit, via double negation); the +-algebra (1-(x(+)y)=(1-x)(1-y)), L(0) ~~ 0 (additive identity); and the deep functional equation written as a Prop horizon.
- **Role.** Crest of the log2-as-process pair (builds on Log2Process). Vein C. Self-contained on CauchyReal/RealField/SeriesConvergence/LogZeta.
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** ToS: CauchyReal; RealField; SeriesConvergence; zeta.LogZeta; Log2Process
- **E/R/R.** _Elements:_ процессы k·ln2, ln2, 1/ln2 — каждый Cauchy над Q, конечно-актуален на каждой стадии. _Roles:_ log2 как роль ln/ln2; на диадическом 2ᵏ роль СХЛОПЫВАЕТСЯ в целое k (Element). _Rules:_ ассоц. ·; самосокращение a·a⁻¹~~1; единица a·1~~a; функц. уравнение ln(ab)~~ln a+ln b (горизонт); 1−(x⊕y)=(1−x)(1−y). _P4:_ log2(2ᵏ)=k — Element-сторона границы финитизации: процесс-частное сходится к ЦЕЛОМУ, т.к. ln2 точно сокращается. 0-аксиомно (только classic).
- **Classical counterpart.** log(ab)=log a+log b and log2(2^k)=k are elementary; NEW is their formulation as Cauchy-PROCESS equalities over Q (~~): the Element-collapse (k*ln2)/ln2 ~~ k is PROVEN, while the deep series-additivity (Cauchy product / Mertens) is honestly written as a Prop (ln_mul_functional_equation), NOT faked with Admitted.
- **Tags.** log2, process, functional-equation, entropy, vein-C, new-framing

**Lemmas (9):**

| name | kind | role |
|---|---|---|
| `ln_pow2/log2_pow2` | Definition | ln(2ᵏ):=k·ln2; log2(2ᵏ):=(k·ln2)/ln2 |
| `log2_pow2_eq` | Theorem | ★ КРЕСТ: log2(2ᵏ) ~~ k для всех k (Element-схлопывание) |
| `log2_pow2_zero/one/three` | Corollary | конкретные k=0,1,3 |
| `oplus/oplus_comm/oplus_zero_l/one_minus_oplus` | Definition/Lemma | ★ алгебра ⊕: 1−(x⊕y)=(1−x)(1−y) |
| `log_series_term_zero/log_series_partial_zero/ln_proc_zero` | Lemma | ★ L(0) ~~ 0 (аддитивная единица функц. уравнения) |
| `cauchy_neg_neg` | Lemma | двойное отрицание процесса −(−a)~~a |
| `H2_fair/H2_fair_one` | Definition/Theorem | ★ H(½) ~~ 1 (энтропия честной монеты = 1 бит) |
| `ln_mul_functional_equation` | Definition (Prop) | ★ глубокая половина креста как ДОКУМЕНТ (горизонт, не Admitted) |
| `log2_functional_synthesis` | Theorem | капстоун: log2(2ᵏ)=k ∀k + k=0,3 + H(½)=1 |

**Key lemmas (deep):**

- **`log2_pow2_eq`** - КРЕСТ задачи: log2(2ᵏ) ~~ k как РАВЕНСТВО ПРОЦЕССОВ (~~), не численный факт (2ᵏ вне радиуса сходимости ряда). Доказано Element-схлопывание (k·ln2)/ln2 ~~ k через ассоциативность + самосокращение ln2/ln2 (log2_two) + единицу. На диадическом ln2 ТОЧНО сокращается → процесс схлопывается в целое; на не-диадическом (3) сокращения нет → role-limit. Один механизм объясняет оба полюса границы финитизации. Честно: ln(2ᵏ) здесь ОПРЕДЕЛЁН как k·ln2 (аддитивность взята как структура); вывод этого из ряда — горизонт. _(crest, log2-pow, process-equality, vein-C, element-collapse)_
- **`ln_mul_functional_equation`** - Глубокая половина креста, выписанная как Prop (документ, НЕ Admitted): аддитивность ln из РЯДА L(x)+L(y)~~L(x+y−xy) — теорема о произведении Коши/Мертенса (настоящий вещ. анализ над Q, в репо отсутствует). Образец честности: точная формулировка недоказанного рядом с доказанным, без фальсификации. _(functional-equation, horizon, cauchy-product, honest)_
- **`H2_fair_one`** - Энтропия честной монеты H(½) ~~ 1 — РОВНО один бит как process-equality (максимум бинарной энтропии по значению = log₂2). При p=1−p=½ оба ½-веса дают log₂½, поэтому H(½)=−log₂½ = −(−ln2/ln2) ~~ 1 через двойное отрицание. Общий H(p)≤H(½) (вогнутость) — горизонт. _(entropy, fair-coin, one-bit, process-equality)_

**Uniqueness - score 3 (new-framing).** log2(2ᵏ)=k как process-equality (Element-схлопывание (k·ln2)/ln2~~k) + H(½)=1 бит + алгебра функц. уравнения, 0-аксиомно; глубокая series-аддитивность честно выписана как Prop-горизонт.
> _Caveat:_ Сами тождества (log аддитивность, log2(2ᵏ)=k, H(½)=1) элементарны; уникальность — в P4-формулировке как равенств ПРОЦЕССОВ над Q и в честном разрезе доказано/горизонт (Коши-произведение не фейкается Admitted), не новый матфакт.

---

## #1831 - `src/Log2Process.v` - score 3 (new-framing)

**log2 in bits as a PROCESS (Cauchy over Q), not a wall: ln-series core, log2(2)=1, log2(3) is a process**

- **Topic.** ln_series_cauchy (the ln-series L(x)=Sum x^m/m is Cauchy over Q for 0<=x<1, via comparison with the geometric series + LogZeta domination, replaying exp_series_cauchy); ln_proc, ln2_process := L(1/2), ln3_process := L(2/3); a 1/2 lower bound (monotone); log2_of := /ln2; the flagship log2_two : log2(2) ~~ 1 (self-cancellation, k=1 base of the crest); and log2_3_process_not_wall — log2(3) IS a Cauchy process + the DyadicBits irrationality diagnostic.
- **Role.** Root of the log2-as-process pair. Reframes DyadicBits.v negatively-stated irrationality into a positive process object (vein C). Self-contained on CauchyReal/SeriesConvergence/RealField/LogZeta/DyadicBits.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** ToS: CauchyReal; SeriesConvergence; RealField; zeta.LogZeta; stdlib.DyadicBits
- **E/R/R.** _Elements:_ частичные суммы log_series_partial x M = Σ_{m=1}^M xᵐ/m — каждая стадия точна над Q; степени 2ᵏ; диадические аргументы. _Roles:_ ln-процесс = роль-величина (−ln(1−x) как Cauchy-объект); log2 = роль ln/ln2. Element=диадическое (схлопывается), role-limit=не-диадическое (предел иррационален). _Rules:_ ряд L(x)=Σxᵐ/m; доминирование log_series_term ≤ Qpow → сравнение → Cauchy; монотонность; рациональные границы. _P4:_ бит-мера ТОЧНА ⟺ диадическая (вена A), но не-диадическая сторона — именованный ПРОЦЕСС (вена C), не дыра. 0-аксиомно (только classic через SeriesConvergence).
- **Classical counterpart.** That log2(odd) is irrational (no a/b with 2^a=n^b) is classical (DyadicBits.v states it negatively, as a wall); NEW is supplying the POSITIVE object — log2 as a Cauchy PROCESS over Q (ln-series), so the irrationality becomes a role-limit DIAGNOSTIC of an actual process, not a non-existence statement. Vein C.
- **Tags.** log2, process, irrationality-as-process, vein-C, dyadicbits, new-framing

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `ln_series_cauchy` | Theorem | ★ ЯДРО: ln-серия Cauchy над Q для 0≤x<1 (сравнение с геометрическим) |
| `ln_proc/ln2_process/ln3_process` | Definition | ln-процесс; ln2=L(½); ln3=L(⅔) |
| `cs_seq_ln2/log2_half_partial_lower/ln2_partial_increasing/ln2_inv_lb` | Lemma | стадии ln2, нижняя граница ½, монотонность |
| `ln2_inv/log2_of` | Definition | 1/ln2; log2 := ln/ln2 |
| `log2_two` | Theorem | ★ log2(2) ~~ 1 (база креста k=1, самосокращение) |
| `log2_3_process_not_wall` | Theorem | ★ log2(3) = процесс (Cauchy) + role-limit-диагностика (не стена) |
| `log2_process_synthesis` | Theorem | капстоун трёх граней |

**Key lemmas (deep):**

- **`log2_3_process_not_wall`** - ПЕРЕОБРАМЛЕНИЕ DyadicBits и ответ на вопрос «иррациональность даёт процесс?» — ДА. Левое: ОБЪЕКТ существует (ln3-серия Cauchy над Q, доказано ядром), которого у DyadicBits не было. Правое: role-limit-ДИАГНОСТИКА сохранена (нет конечной битовой записи, log2_3_irrational). Вместе: иррациональность = процесс (вена C) + диагностика, а НЕ несуществование/стена. Завершает то, что DyadicBits оставил негативом. _(irrationality-as-process, vein-C, dyadicbits-reframe, role-limit)_
- **`ln_series_cauchy`** - Ядро: ряд L(x)=Σxᵐ/m сходится (Cauchy над Q) для 0≤x<1 — даёт сам ОБЪЕКТ-процесс log2. Доказательство — сравнение с геометрическим Σxᵐ через доминирование log_series_term ≤ Qpow (уже в LogZeta), реплея паттерна exp_series_cauchy. Это «процесс» из переобрамления: объект, которого у DyadicBits не было. _(ln-series, cauchy, comparison-test, core)_
- **`log2_two`** - log2(2) ~~ 1 как process-equality через самосокращение ln2/ln2 (cauchy_mul_inv_r_pos) — база креста (k=1 случай log2(2ᵏ)=k), без функц. уравнения. Поскольку ln(2)=ln2_process, log2(2)=ln2/ln2 ~~ 1. _(log2-2, self-cancellation, crest-base)_

**Uniqueness - score 3 (new-framing).** log2 в битах как Cauchy-ПРОЦЕСС над Q (ln-серия), переобрамляющий DyadicBits: иррациональность log2(нечёт) = процесс (вена C) + диагностика, а не стена-несуществование; log2(2)~~1 базой креста. 0-аксиомно.
> _Caveat:_ Иррациональность log2(нечёт) и сходимость ln-ряда классичны; уникальность — в P4-объекте (процесс вместо стены) и связке вена-A (точная граница диадического) ∩ вена-C (предел=процесс), не новый матфакт.

