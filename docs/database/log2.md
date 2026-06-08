# Database - cluster `log2`

_Generated from `log2.json` by `generate.ps1` - do not edit by hand; edit the JSON._

**6 files / 84 Qed.** Score distribution: s5=0 / s4=0 / s3=3 / s2=3 / s1=0 / s0=0

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

---

## #1832 - `src/CauchyProduct.v` - score 2 (methods)

**Mertens' theorem: Cauchy product of series ~~ product of limits, constructively over Q (the ln_mul engine)**

- **Topic.** conv a b n := Sum_{i<=n} a_i b_{n-i}; partial_sum_conv_swap (finite Fubini on the triangle, axiom-free); conv_cauchy (triangle-in-square => the Cauchy product of nonneg abs-bounded series converges); mertens_diff_eq (the difference identity A_n B_n - C_n == Sum a_i (B_n - B_{n-i}), axiom-free) turning the off-diagonal into a controllable block sum; partial_sum_split (the resurrected partial_sum_tail) splitting the off-diagonal at cutoff K; mertens_error_bound (block estimate: head i<=K bounded by small b-blocks at the end, tail i>K majorized by Mb*|a|-tail); and the capstone mertens_cauchy_product : series_limit (conv a b) ~~ cauchy_mul (series_limit a) (series_limit b) via the eps/2 argument.
- **Role.** The missing real-analysis engine the repo lacked (author Abort-ed partial_sum_tail). Grounds the ln_mul_functional_equation horizon documented in Log2FunctionalEq.v (ln of a product via the Cauchy product). Vein C support. Self-contained on CauchyReal/RealField/SeriesConvergence.
- **Counts.** Qed 19 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; Qabs; Lqa; Lia; ZArith; ToS: CauchyReal; RealField; SeriesConvergence
- **E/R/R.** _Elements:_ частичные суммы над Q; член свёртки conv a b n — каждая стадия N конечна и точна. _Roles:_ произведение Коши = роль-перемножение рядов; Fubini = перестановка ролей сумм; предел произведения = роль-предел (Мертенс). _Rules:_ partial_sum-рекуррентность; линейность; Nat.sub_succ_l; расщепление Σ по порогу K; Cauchy-хвосты Σ\|a\|, Σ\|b\| → 0; разностное тождество A_nB_n−C_n = Σ a_i(B_n−B_{n−i}). _P4:_ всё конечно на каждой стадии N (Element); предел произведения — role-limit (Мертенс), строится КАК ПРОЦЕСС, не завершённый объект. 0-аксиомно (только classic; swap и mertens_diff_eq аксиомо-СВОБОДНЫ).
- **Classical counterpart.** Mertens' theorem (1875): the Cauchy product of two convergent series, one absolutely convergent, converges to the product of the limits. Here proved CONSTRUCTIVELY over Q-Cauchy processes (no R, RealProcess := nat->Q), axiom-free except the global L3 `classic`, and recast as a process-equality (~~). It also RESURRECTS partial_sum_tail, which the repo author explicitly Abort-ed in SeriesConvergence.v:320.
- **Tags.** mertens, cauchy-product, process, vein-C, constructive-over-Q, methods, resurrected-abort

**Lemmas (12):**

| name | kind | role |
|---|---|---|
| `partial_sum_ext_le/partial_sum_plus/partial_sum_minus/partial_sum_scale_r` | Lemma | экстенсиональность + линейность частичной суммы |
| `partial_sum_conv_swap` | Lemma | ★ конечный Fubini: Σ_n Σ_i = Σ_i по столбцам (аксиомо-СВОБОДНА) |
| `conv` | Definition | член произведения Коши c_n = Σ_{i≤n} a_i b_{n−i} |
| `partial_sum_nonneg/partial_sum_le_upper/conv_nonneg` | Lemma | неотрицательность/монотонность |
| `conv_le_square` | Lemma | ★ треугольник ⊆ квадрат: Σconv ≤ (Σg)(Σh) |
| `conv_cauchy` | Lemma | ★ сходимость произведения Коши (неотр. абс-огранич. ряды) |
| `partial_sum_abs_le/partial_sum_block_abs/partial_sum_abs_cauchy` | Lemma | треугольные/блочные оценки модуля + abs-Cauchy |
| `mertens_diff_eq` | Lemma | ★ разностное тождество A_nB_n−C_n = Σ a_i(B_n−B_{n−i}) (аксиомо-СВОБОДНА) |
| `partial_sum_S/partial_sum_le_ext` | Lemma | одношаговое разворачивание + поточечная монотонность до N |
| `partial_sum_split` | Lemma | ★ ВОСКРЕШЁННЫЙ partial_sum_tail: Σ_{i≤n} = Σ_{≤K} + хвост за K |
| `mertens_error_bound` | Lemma | ★ блочная оценка: голова(≤K)·b-блок + Mb·\|a\|-хвост(>K) |
| `mertens_cauchy_product` | Theorem | ★★★ МЕРТЕНС: series_limit(conv a b) ~~ (s_l a)·(s_l b) |

**Key lemmas (deep):**

- **`mertens_cauchy_product`** - Теорема Мертенса как РАВЕНСТВО ПРОЦЕССОВ (~~) над Q: предел произведения Коши совпадает с произведением пределов. Капстоун ε/2 на mertens_error_bound: порог K (Коши для Σ\|a\|, хвост за K) и Nb (Коши для Σ\|b\|, блок у конца); при n≥SK+Nb+K обе части < ε/2. Зависит ТОЛЬКО от classic (L3) — конструктивно над Q, без вещественных чисел Coq. Это движок, отсутствовавший в репо: автор репо Abort-нул partial_sum_tail (SeriesConvergence:320), здесь он воскрешён (partial_sum_split) и доведён до полной теоремы. _(mertens, cauchy-product, process-equality, vein-C, constructive-over-Q, epsilon-half)_
- **`mertens_diff_eq`** - Разностное тождество A_nB_n − C_n == Σ_{i≤n} a_i·(B_n − B_{n−i}) — содержательный поворот, превращающий неуправляемую вне-диагональ Σ_{i+j>n} в БЛОЧНУЮ сумму (хвост B на (n−i,n]). Аксиомо-СВОБОДНА: из partial_sum_conv_swap (Fubini) + выноса множителя + линейности, чистая алгебра над Q. Именно эта переформулировка делает оценку Мертенса конечно-контролируемой. _(difference-identity, axiom-free, off-diagonal, fubini)_
- **`partial_sum_split`** - Воскрешённый partial_sum_tail: Σ_{i≤n} f == Σ_{i≤K} f + Σ_j f(S(K+j)) (хвост за K), при S K ≤ n. Автор репо явно Abort-нул его («tricky to state cleanly»), обойдя прямой оценкой Cauchy; здесь доказан индукцией по n с ключами Nat.sub_succ_l (S n−S K = S(n−S K)) и K+S(n−S K)=n. Структурный инструмент, без которого вне-диагональ не расщепить на голову/хвост. _(partial-sum-split, resurrected-abort, structural, induction)_

**Uniqueness - score 2 (methods).** Теорема Мертенса (произведение Коши = произведение пределов) КОНСТРУКТИВНО над Q-Cauchy-процессами (без вещественных чисел Coq), 0-аксиомно (только classic), как равенство ПРОЦЕССОВ (~~); воскрешает Abort-нутый автором partial_sum_tail и закрывает горизонт ln_mul.
> _Caveat:_ Сама теорема Мертенса классична (1875). Уникальность — в конструктивно-над-Q аксиомо-свободной формулировке как process-equality и в том, что движок заполняет реальный пробел репо (брошенный partial_sum_tail, документированный горизонт ln_mul), а НЕ новый матфакт.

---

## #1833 - `src/ExpFunctionalEquation.v` - score 2 (methods)

**Exponential addition theorem E(u+v) ~~ E(u)·E(v) over Q via Mertens (central domino of ln_mul)**

- **Topic.** exp_add_from_conv wires mertens_cauchy_product to exp: it closes ALL analysis (abs-bounds via cauchy_bounded+exp_term_abs, conv-Cauchy via is_cauchy_ext, limit via Mertens) and reduces the exp homomorphism to the pure-algebra identity conv(exp_term u)(exp_term v) n == exp_term(u+v) n. That identity (exp_conv_id) is proved by induction on n: base exp_conv_zero, step via exp_conv_rec — the convolution recurrence inject_Z(S n)*c_{S n} == (u+v)*c_n — from exp_term_ratio (u*A_i=(i+1)A_{i+1}, v*B_j=(j+1)B_{j+1}) plus a head/tail sum reindex (partial_sum_head) collecting the coefficient i+(n+1-i)=n+1. Cancel (n+1)>0 to finish. Capstone exp_add : exp_limit(u+v) ~~ cauchy_mul(exp_limit u)(exp_limit v).
- **Role.** Central domino of the ln_mul route (see E/R/R разбор): L(x)+L(y)~~L(x⊕y) is additive ⟹ routes through exp, and exp(u+v)=exp(u)exp(v) is exactly Mertens. First real consumer of CauchyProduct.mertens_cauchy_product. Also completes the RATIONAL exponential as a group homomorphism (Q,+,0,−)→(R,*,1,inv): exp_add (law) + exp_limit_zero (unit E(0)~~1) + exp_neg (inverses E(−u)*E(u)~~1) + exp_limit_wd (Qeq-respect). Vein C. Builds on PowerSeries (exp_term/exp_limit/exp_series_cauchy) + CauchyProduct (conv/mertens). Remaining ln_mul horizon needs REAL (process) exponential exp_R : CauchySeq→CauchySeq (ABSENT from repo — a major construction), its addition theorem, E∘L=1/(1−x), injectivity.
- **Counts.** Qed 17 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; Qabs; Lqa; Lia; ZArith; ToS: CauchyReal; RealField; SeriesConvergence; PowerSeries; CauchyProduct
- **E/R/R.** _Elements:_ exp_term x n = xⁿ/n! — каждая стадия точна над Q; свёртка conv. _Roles:_ E = роль-обратная к ln; теорема сложения = роль-гомоморфизм (+ → ·); Мертенс — движок, переносящий покоэффициентное conv в предельное равенство. _Rules:_ exp_term_ratio (u·Aᵢ=(i+1)Aᵢ₊₁); рекуррентность (n+1)cₙ₊₁=(u+v)cₙ; переиндексация сумм (голова/хвост); сокращение (n+1)>0; абс-границы из cauchy_bounded; is_cauchy по поточечному Qeq. _P4:_ E(u+v)~~E(u)E(v) — роль-предел (Мертенс), процесс, не завершённый объект; сведён к конечной покоэффициентной алгебре. 0-аксиомно (только classic).
- **Classical counterpart.** The exponential addition theorem exp(u+v)=exp(u)exp(v) (equivalently the binomial theorem (u+v)^n = sum C(n,i) u^i v^(n-i) inside the Cauchy product of exp-series). Here proved CONSTRUCTIVELY over Q-Cauchy processes (no R), axiom-free except global L3 `classic`, recast as a process-equality (~~), as the FIRST full application of mertens_cauchy_product. The convolution identity is proved via the factorial recurrence (n+1)c_{n+1}=(u+v)c_n (Vandermonde/Pascal) WITHOUT binomial coefficients.
- **Tags.** exp-addition, mertens-application, process, vein-C, constructive-over-Q, methods, central-domino

**Lemmas (12):**

| name | kind | role |
|---|---|---|
| `is_cauchy_ext` | Lemma | перенос is_cauchy по поточечному Qeq |
| `exp_term_abs/exp_term_nonneg/exp_abs_partial_bounded` | Lemma | \|exp_term x k\|=exp_term\|x\|k; неотрицательность; абс-границы (cauchy_bounded) |
| `exp_add_from_conv` | Lemma | ★ проводка Мертенса к exp: conv-тождество ⟹ exp-гомоморфизм (весь анализ закрыт) |
| `partial_sum_head` | Lemma | расщепление суммы с головы Σ_{≤S n}=f 0+Σ_{≤n}f(S i) |
| `exp_term_0` | Lemma | exp_term x 0 = 1 |
| `exp_conv_zero` | Lemma | база свёртки c₀=1 |
| `exp_conv_rec` | Lemma | ★ рекуррентность свёртки (n+1)cₙ₊₁=(u+v)cₙ (Vandermonde без C(n,i)) |
| `exp_conv_id` | Lemma | ★ биномиальное тождество conv(Eᵤ)(Eᵥ)n==E_{u+v}n (индукция+сокращение) |
| `exp_add` | Theorem | ★★★ E(u+v) ~~ E(u)·E(v) — безусловная теорема сложения экспоненты |
| `Qpow_wd/exp_term_wd/exp_limit_wd` | Lemma | корректность exp над Qeq (роль над классом Qeq) |
| `exp_partial_zero/exp_limit_zero` | Lemma | ★ единица гомоморфизма: E(0) ~~ 1 |
| `exp_neg` | Theorem | ★ обратимость: E(−u)·E(u) ~~ 1 (E(−u)=E(u)⁻¹) |

**Key lemmas (deep):**

- **`exp_add`** - Теорема сложения экспоненты как РАВЕНСТВО ПРОЦЕССОВ (~~) над Q: E(u+v)~~E(u)·E(v). ПЕРВОЕ полное применение mertens_cauchy_product — демонстрирует, что движок произведения Коши работает end-to-end. Зависит ТОЛЬКО от classic. Центральное домино маршрута к ln_mul: поскольку L(x)+L(y)~~L(x⊕y) аддитивно, оно идёт через exp, а exp(u+v)=exp(u)exp(v) — ровно Мертенс. _(exp-addition, mertens-application, process-equality, vein-C, central-domino, constructive-over-Q)_
- **`exp_conv_rec`** - Сердце: рекуррентность свёртки (n+1)·cₙ₊₁ == (u+v)·cₙ — доказательство теоремы сложения БЕЗ биномиальных коэффициентов. (u+v)cₙ распадается на u·cₙ+v·cₙ; exp_term_ratio даёт u·Aᵢ=(i+1)Aᵢ₊₁ и v·Bⱼ=(j+1)Bⱼ₊₁; голова/хвост-переиндексация (partial_sum_head) собирает у каждого члена коэффициент i+(n+1−i)=n+1. Чистая конечная алгебра над Q (Vandermonde/Pascal в факториальной форме), аксиомо-чисто. _(convolution-recurrence, vandermonde, factorial, reindex, finite-algebra)_
- **`exp_add_from_conv`** - Проводка Мертенса к exp: сводит ВЕСЬ анализ exp-гомоморфизма (сходимость, абс-границы, предел) к одному покоэффициентному тождеству. abs-границы — \|exp_term u k\|=exp_term\|u\|k + cauchy_bounded(exp_limit\|u\|); conv-Cauchy — is_cauchy_ext (перенос по поточечному Qeq на exp-ряд от u+v); предел — mertens_cauchy_product. Образец разделения анализ/алгебра: после этой леммы остаётся чистая комбинаторика. _(mertens-wiring, analysis-closed, reduction, cauchy-bounded)_

**Uniqueness - score 2 (methods).** Теорема сложения экспоненты E(u+v)~~E(u)·E(v) КОНСТРУКТИВНО над Q-Cauchy-процессами (без вещественных Coq), 0-аксиомно (только classic), как равенство ПРОЦЕССОВ — первое полное применение mertens_cauchy_product; conv-тождество доказано факториальной рекуррентностью (n+1)cₙ₊₁=(u+v)cₙ без биномиальных коэффициентов.
> _Caveat:_ Сама теорема сложения экспоненты (и биномиальное тождество) классична. Уникальность — в конструктивно-над-Q аксиомо-свободной формулировке как process-equality и в роли центрального домино маршрута к ln_mul (демонстрация движка Мертенса end-to-end), а НЕ новый матфакт. Горизонт ln_mul (E∘L, инъективность E) ещё открыт.

---

## #1834 - `src/ProcessExp.v` - score 2 (methods)

**Real (process) exponential exp_R : CauchySeq -> CauchySeq, constructively over Q via completeness**

- **Topic.** exp_R P := diagonal_limit (fun n => exp_limit (P n)) (exp_meta_cauchy P). The crux exp_meta_cauchy proves the sequence of processes is meta-Cauchy via two uniform pillars (P bounded by B = cauchy_bounded): equi-Cauchy = uniform exp-tail (exp_partial_tail_bound[_sym]: |Σexp_term x m − Σexp_term x n| ≤ |Σexp_term B m − Σexp_term B n| for |x|≤B, from exp_term_abs + Qpow_le_mono_base + partial_sum_block_abs/mono) + the exp-series Cauchy modulus at B; cross-closeness = argument-Lipschitz (exp_partial_lipschitz: |Σexp_term a − Σexp_term b| ≤ |a−b|·Σexp_term B(pred k), bounded by C=exp_term B 0+MB via exp_pred_sum_bound) + P's Cauchy modulus at eps/C. Analytic kernel: Qpow_diff_bound (|a^(Sk)−b^(Sk)| ≤ (k+1)B^k|a−b|, telescope) and exp_term_diff_bound (÷ factorial), both AXIOM-FREE.
- **Role.** The major missing construction for the ln_mul horizon: E(L(x)) requires exp of the PROCESS L(x), which exp_limit (rational-arg) cannot express. exp_R supplies it, AND exp_R_add proves it is a homomorphism exp_R(P+R)~~exp_R(P)*exp_R(R) (the addition theorem). First real consumer of Completeness.diagonal_limit/meta_cauchy and of CauchyProduct.mertens_error_bound at the diagonal. Vein C (real = process). Builds on PowerSeries (exp_limit/exp_term) + ExpFunctionalEquation (exp_term_0/partial_sum_head/exp_abs_partial_bounded/exp_term_nonneg/exp_conv_id) + CauchyProduct (partial_sum_block_abs/mertens_error_bound) + Completeness. Remaining for ln_mul: E∘L=1/(1−x), injectivity of exp_R.
- **Counts.** Qed 21 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; Qabs; Lqa; Lia; ZArith; ToS: CauchyReal; RealField; SeriesConvergence; PowerSeries; CauchyProduct; ExpFunctionalEquation; Completeness
- **E/R/R.** _Elements:_ рациональные приближения P n; exp_term (P n) k; диагональ exp_limit (P n) — каждая стадия точна над Q. _Roles:_ exp_R = роль-функция (вещественная экспонента); диагональ = роль-предел ПОСЛЕДОВАТЕЛЬНОСТИ процессов (completeness); ограниченность P = роль-граница B. _Rules:_ meta_cauchy = (равномерный хвост exp над \|·\|≤B: exp_partial_tail_bound) ∧ (Липшиц \|a^k−b^k\|≤k·B^{k-1}\|a−b\|: Qpow_diff_bound→exp_partial_lipschitz); diagonal_limit/diagonal_converges. _P4:_ exp_R(P) — role-limit ПОСЛЕДОВАТЕЛЬНОСТИ role-limit'ов (процесс процессов), но diagonal_limit делает один Cauchy-процесс. Аналитическое ядро 0-аксиомно; вся конструкция — только classic.
- **Classical counterpart.** The real exponential exp : R -> R, here built CONSTRUCTIVELY over Q-Cauchy processes: exp_R : CauchySeq -> CauchySeq (exp of a real number represented as a process), via the diagonal/completeness construction (Completeness.diagonal_limit) of the meta-Cauchy sequence n \|-> exp_limit (P n). The analytic core (power Lipschitz, uniform exp-tail) is axiom-FREE; the whole construction uses only the global L3 `classic`. No real exp existed in the repo (exp_limit was rational-argument only).
- **Tags.** process-exp, real-exponential, process, vein-C, constructive-over-Q, methods, completeness, diagonal-limit

**Lemmas (17):**

| name | kind | role |
|---|---|---|
| `Qpow_S/Qpow_le_mono_base` | Lemma | разворачивание + монотонность Qpow по основанию |
| `Qpow_diff_bound` | Lemma | ★ Липшиц-ядро степеней \|a^(Sk)−b^(Sk)\|≤(k+1)B^k\|a−b\| (АКСИОМО-СВОБОДНА) |
| `Qfact_S/exp_term_diff_bound` | Lemma | ★ перенос Липшица на член ряда ÷факториал (АКСИОМО-СВОБОДНА) |
| `exp_partial_lipschitz` | Lemma | ★ ПИЛОН cross-closeness: Липшиц частичных сумм по аргументу (АКСИОМО-СВОБОДНА) |
| `exp_pred_sum_bound` | Lemma | равномерная мажоранта Σexp_term B(pred k) ≤ exp_term B 0+MB |
| `partial_sum_block_mono` | Lemma | блочная монотонность (Σf на (n,m]) ≤ (Σg на (n,m]) |
| `exp_partial_tail_bound[_sym]` | Lemma | ★ ПИЛОН equi-Cauchy: равномерный хвост exp над \|·\|≤B (АКСИОМО-СВОБОДНА) |
| `exp_meta_cauchy` | Lemma | ★★ СБОРКА: (fun n => exp_limit (P n)) — meta-Cauchy (оба пилона + Cauchy-модули) |
| `exp_R` | Definition | ★★★ ВЕЩЕСТВЕННАЯ ЭКСПОНЕНТА: exp_R P := diagonal_limit (fun n => exp_limit (P n)) |
| `exp_term_abs_bound/exp_abs_partial_le_B` | Lemma | равномерная мажоризация \|exp_term x\|≤exp_term B, Σ\|exp_term x\|≤Σexp_term B |
| `exp_R_diag_mertens_bound` | Lemma | ★ диагональный Мертенс: per-n разностная оценка с равномерн. мажорантами (АКСИОМО-СВОБОДНА) |
| `exp_R_add` | Theorem | ★★★ ТЕОРЕМА СЛОЖЕНИЯ: exp_R(P+R) ~~ exp_R(P)·exp_R(R) (гомоморфизм) |
| `exp_R_wd` | Lemma | ★ корректность на реалах: P~~R ⟹ exp_R P ~~ exp_R R (setoid-морфизм) |
| `exp_R_zero/exp_R_neg` | Theorem | ★ единица E(0)~~1 + обратимость E(P)·E(−P)~~1 → ПОЛНЫЙ гомоморфизм групп |
| `exp_lower_bound` | Lemma | монотонная нижняя оценка Σexp_term t ≥ 1+t (t≥0) |
| `exp_R_inj_kernel` | Theorem | ★★ ядро инъективности: E(D)~~1 ⟹ D~~0 (через E(−D)~~1 + знак-расщепление) |
| `exp_R_inj` | Theorem | ★★★ ИНЪЕКТИВНОСТЬ: E(A)~~E(B) ⟹ A~~B |

**Key lemmas (deep):**

- **`exp_R_inj`** - Инъективность вещественной экспоненты: E(A)~~E(B) ⟹ A~~B. Сводится к ядру exp_R_inj_kernel (E(D)~~1 ⟹ D~~0) через D=A−B + exp_R_add/neg. Ядро РЕШАЕТ режимную проблему (конструктивно exp инъективна нетривиальна): из E(D)~~1 получаем E(−D)~~1 (exp_R_neg + сокращение), затем ЗНАКОВОЕ расщепление D n с монотонной нижней оценкой exp_lower_bound (Σexp_term t ≥ 1+t при t≥0) для D и −D — без квадратичного хвоста и анализа exp от отрицательных. Последний рычаг к ln_mul (E(L(x)+L(y))~~E(L(x⊕y)) ⟹ равенство аргументов). Только classic. _(injectivity, kernel, regime-free, sign-split, process-exp, vein-C)_
- **`exp_R_add`** - Теорема сложения вещественной экспоненты: exp_R(P+R) ~~ exp_R(P)·exp_R(R) — exp от ПРОЦЕССА является ГОМОМОРФИЗМОМ (Q-Cauchy реалы, +)→(·). Доказательство — ДИАГОНАЛЬНЫЙ Мертенс: на диагонали n разность Σexp_term(Pn)·Σexp_term(Rn) − Σexp_term(Pn+Rn) ЕСТЬ Мертенс-блок (через exp_conv_id: Σexp_term(a+b)=Σconv) и ограничена exp_R_diag_mertens_bound с РАВНОМЕРНЫМИ мажорантами exp_term BP/BR (\|Pn\|≤BP,\|Rn\|≤BR); капстоун ε/2 на Cauchy-модулях exp-рядов от BP,BR. Зависит только от classic. Это ключевое свойство для маршрута ln_mul (E(L(x)+L(y))=E(L(x))E(L(y))). _(addition-theorem, homomorphism, diagonal-mertens, process-exp, vein-C)_
- **`exp_R`** - Вещественная (процессная) экспонента exp от ПРОЦЕССА P : CauchySeq → CauchySeq — конструкция, отсутствовавшая в репо (был только exp_limit рационального аргумента). Определена как diagonal_limit последовательности exp_limit(P n) — exp от рациональных приближений. Это то, что нужно для E(L(x)) в маршруте ln_mul (L(x) — процесс). Зависит только от classic; аналитическое ядро аксиомо-свободно. Образец P4: вещественное = процесс, exp вещественного = role-limit последовательности процессов, сведённый completeness'ом к одному Cauchy-процессу. _(process-exp, real-exponential, diagonal-limit, completeness, vein-C, constructive-over-Q)_
- **`exp_meta_cauchy`** - Сборочный крест: доказывает meta_cauchy для (fun n => exp_limit (P n)) — два РАВНОМЕРНЫХ пилона. equi-Cauchy: хвост exp-ряда равномерно мал для всех аргументов \|P k\|≤B (exp_partial_tail_bound_sym мажорирует хвостом exp_term B, чей Cauchy-модуль даёт N1). cross-closeness: близкие аргументы → близкие суммы (exp_partial_lipschitz, мажоранта C=exp_term B 0+MB), P's Cauchy-модуль при ε/C даёт N2. N=N1+N2. Демонстрирует, что completeness-машина diagonal_limit реально применима. _(meta-cauchy, equi-cauchy, cross-closeness, uniform-bounds, assembly)_
- **`Qpow_diff_bound`** - Аналитический сердечник, АКСИОМО-СВОБОДНЫЙ: \|a^(k+1)−b^(k+1)\| ≤ (k+1)·B^k·\|a−b\| при \|a\|,\|b\|≤B. Телескоп степеней a^(k+2)−b^(k+2)=a(a^(k+1)−b^(k+1))+(a−b)b^(k+1), индукция по k. Это Липшиц-константа полинома-частичной-суммы exp по аргументу — фундамент пилона cross-closeness. Чистая алгебра над Q, без аксиом. _(power-difference, lipschitz-kernel, telescope, axiom-free)_

**Uniqueness - score 2 (methods).** Вещественная экспонента exp_R : CauchySeq→CauchySeq построена КОНСТРУКТИВНО над Q-Cauchy-процессами (exp вещественного=процесса) через diagonal_limit/completeness, 0-аксиомно (аналитическое ядро аксиомо-свободно, вся конструкция — только classic); снабжает маршрут ln_mul недостающим объектом E(L(x)).
> _Caveat:_ Вещественная экспонента, её сходимость и теорема сложения классичны. Уникальность — в конструктивно-над-Q аксиомо-свободной формулировке (P4: вещественное=процесс, exp=role-limit процессов через completeness; теорема сложения — диагональный Мертенс) и в роли недостающего движка маршрута ln_mul, а НЕ новый матфакт. ГОТОВО: exp_R + теорема сложения + гомоморфизм групп + ИНЪЕКТИВНОСТЬ. Остаётся ТОЛЬКО E∘L=1/(1−x) для замыкания ln_mul.

---

## #1835 - `src/FormalPowerSeries.v` - score 3 (new-framing)

**Function-as-process: formal power series = coefficient-process; H1 lifted to the function level**

- **Topic.** FPS := nat->Q reifies an analytic function f(x)=Sum c_n x^n as its Taylor-coefficient process. FPS algebra (fps_add/neg/sub/scale, fps_mul := conv [Cauchy product], fps_deriv); reified functions geom_fps (=1/(1-x), all c_n=1), exp_fps (=1/n!), log1m_fps (=-ln(1-x), c_{Sk}=1/(k+1)). The Element/role-limit boundary at the FUNCTION level via is_polynomial: fps_one/fps_X are polynomials (Element, terminating coefficient-process); geom_fps/exp_fps are NOT (role-limit, non-terminating) — direct H1-at-function-level witnesses. Flagship: geom_inverse_fps — the geometric's defining identity (1-X)*geom == fps_one proved FORMALLY at the coefficient level (convolution of (1,-1,0,..) with (1,1,1,..) = (1,0,0,..)). All axiom-free.
- **Role.** First deliverable of the function-reification layer (H59 roadmap step 1). Demonstrates 'function = process' concretely + the lifted H1 boundary. Self-contained on CauchyProduct (conv, partial_sum_ext_le) + PowerSeries (Qfact). NEXT: FPS composition + compose exp_fps log1m_fps = geom_fps (c_n=1 recurrence like exp_conv_id) = the formal heart of E∘L; then the analytic eval-bridge → ln_mul horizon.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; Qabs; Lqa; Lia; ZArith; ToS: CauchyReal; SeriesConvergence; CauchyProduct; PowerSeries
- **E/R/R.** _Elements:_ коэффициенты cₙ∈Q — конечные данные на каждой стадии n. _Roles:_ FPS = роль-ФУНКЦИЯ (реифицированная как коэффициент-процесс); fps_mul = роль-свёртка; (1−X)·geom=1 = определяющая роль обратной геометрической. _Rules:_ свёртка Коши (conv); многочлен ⟺ хвост коэф.≡0 (Element); role-limit ⟺ нет такого хвоста. _P4:_ функция-как-коэффициент-процесс: Element (многочлен) ⟺ терминирует, role-limit (трансцендентная) ⟺ не терминирует. То же H1, на уровень выше. 0-аксиомно.
- **Classical counterpart.** Formal power series and the identity (1-x)*(1/(1-x))=1 are classical. NEW: their use to REIFY an analytic function as a coefficient-PROCESS (nat->Q) inside the ToS process-ontology — the first step of H59's program (functions = the next finitization frontier), lifting the H1 Element/role-limit boundary one level up the object hierarchy number->function->functional (polynomial=Element, transcendental=role-limit).
- **Tags.** function-as-process, formal-power-series, coefficient-process, H59, vein-C, new-framing, element-role-limit

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `FPS/fps_eq/fps_zero/one/X/add/neg/sub/scale/mul/deriv` | Definition | реификация функции + FPS-алгебра (mul=conv) |
| `geom_fps/exp_fps/log1m_fps` | Definition | реифицированные функции 1/(1−x), exp, −ln(1−x) |
| `is_polynomial` | Definition | функция-процесс терминирует ⟺ многочлен (Element) |
| `fps_one_polynomial/fps_X_polynomial` | Lemma | Element-сторона: многочлены |
| `geom_not_polynomial/exp_fps_not_polynomial` | Lemma | ★ role-limit: геометрическая/exp НЕ многочлены (H1 на уровне функций) |
| `oneminusX_tail_zero` | Lemma | хвост Σ(1,−1,0,…) с индекса 1 = 0 |
| `geom_inverse_fps` | Lemma | ★★ (1−X)·(1/(1−x))=1 ФОРМАЛЬНО (коэффициент-уровень, аксиомо-своб.) |

**Key lemmas (deep):**

- **`geom_inverse_fps`** - Определяющее уравнение геометрической функции `(1−X)·(1/(1−x))=1`, доказанное на уровне КОЭФФИЦИЕНТ-ПРОЦЕССОВ: свёртка Коши (1,−1,0,…)*(1,1,1,…)=(1,0,0,…)=fps_one. Это «1/(1−x) реифицирована как процесс и её уравнение верифицировано формально» — первая конкретная демонстрация H59 (функция-как-процесс). Аксиомо-свободно. На этом же fps_mul=conv позже строится compose exp_fps log1m_fps=geom (cₙ=1) — формальное сердце E∘L. _(function-as-process, geometric, coefficient-process, vein-C, H59, formal-identity)_
- **`geom_not_polynomial`** - Прямой свидетель границы H1 НА УРОВНЕ ФУНКЦИЙ: геометрическая 1/(1−x) — НЕ многочлен (все cₙ=1≠0), т.е. функция-коэффициент-процесс НЕ терминирует ⟹ role-limit. Многочлен (fps_one/fps_X) терминирует ⟹ Element. Та же Element/role-limit граница, что рациональное/иррациональное у чисел, поднятая на уровень функций иерархии число→функция→функционал. Аксиомо-свободно. _(element-role-limit, function-level, H1-lifted, polynomial-vs-transcendental)_

**Uniqueness - score 3 (new-framing).** Реификация аналитической функции как коэффициент-ПРОЦЕССА (nat→Q) в процессной онтологии ToS — первый шаг программы H59 (функции = следующий фронтир финитизации), с подъёмом границы Element/role-limit на уровень функций (многочлен/трансцендентная) и формальным доказательством определяющего уравнения геометрической. 0-аксиомно.
> _Caveat:_ Формальные ряды и тождество (1−x)·1/(1−x)=1 классичны. Уникальность — в ToS-обрамлении (функция=процесс, H1 на уровень выше, машинный свидетель границы на уровне функций), а НЕ новый матфакт. Формальное сердце E∘L (composition, cₙ=1) и аналитический мост — ещё впереди.

