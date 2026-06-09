# Database - cluster `log2`

_Generated from `log2.json` by `generate.ps1` - do not edit by hand; edit the JSON._

**8 files / 157 Qed.** Score distribution: s5=0 / s4=0 / s3=5 / s2=3 / s1=0 / s0=0

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
- **Role.** Function-reification layer (H59 roadmap). Demonstrates 'function = process' concretely + the lifted H1 boundary + FPS calculus (exp'=exp, log1m'=geom), the ODE-uniqueness structural heart (ode_geom_unique), the Leibniz product rule (fps_deriv_mul), and the FPS COMMUTATIVE-RING structure: convolution is commutative (conv_comm), associative (conv_assoc — Cauchy-product associativity, the triple sum Σ_{j+t≤n} a·b·c, via a triangular Fubini swap partial_sum_triangle_swap the repo did not previously have), with unit fps_one (conv_one_l/r); and the POWER RULE (fps_pow_deriv: (g^{k+1})'=(k+1)·g^k·g', induction on fps_deriv_mul + ring — one associativity instance g·(g^k·g')=(g·g^k)·g' + commutativity to combine). And — the payoff of the whole H59 program — FPS COMPOSITION + CHAIN RULE + the FORMAL HEART of E.L: fps_compose f g (correct when g(0)=0: (f.g)_n=Sum_{k<=n} f_k (g^k)_n, finitely truncated because g(0)=0 => g^k has order >= k => (g^k)_n=0 for k>n, lemma fps_pow_low_order); the chain rule fps_chain_rule (f.g)'=(f'.g)·g' (via conv_compose_swap: a square<->triangle double-sum swap partial_sum_swap + the low-order vanishing); and compose_exp_log1m_is_geom: exp(-ln(1-x))=1/(1-x) at the coefficient-process level (h:=exp.log1m satisfies h'=h·geom by the chain rule with exp'=exp, log1m'=geom, and h(0)=1, so ode_geom_unique gives h=geom). The E.L obstruction (flagged in H58/H59 as a 'second-order finitization boundary') is now DISSOLVED formally, 0-axiom, exactly as the function-as-process reification predicted. All axiom-free. NEXT: the analytic eval-bridge eval(f.g) x ~~ exp_R(ln_proc x) ~~ geometric_limit x (formal series -> CauchyReal number-processes) -> the ln_mul horizon L(x)+L(y)~~L(x+y-xy).
- **Counts.** Qed 37 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; Qabs; Lqa; Lia; ZArith; ToS: CauchyReal; SeriesConvergence; CauchyProduct; ExpFunctionalEquation; PowerSeries
- **E/R/R.** _Elements:_ коэффициенты cₙ∈Q — конечные данные на каждой стадии n. _Roles:_ FPS = роль-ФУНКЦИЯ (реифицированная как коэффициент-процесс); fps_mul = роль-свёртка; (1−X)·geom=1 = определяющая роль обратной геометрической. _Rules:_ свёртка Коши (conv); многочлен ⟺ хвост коэф.≡0 (Element); role-limit ⟺ нет такого хвоста. _P4:_ функция-как-коэффициент-процесс: Element (многочлен) ⟺ терминирует, role-limit (трансцендентная) ⟺ не терминирует. То же H1, на уровень выше. 0-аксиомно.
- **Classical counterpart.** Formal power series and the identity (1-x)*(1/(1-x))=1 are classical. NEW: their use to REIFY an analytic function as a coefficient-PROCESS (nat->Q) inside the ToS process-ontology — the first step of H59's program (functions = the next finitization frontier), lifting the H1 Element/role-limit boundary one level up the object hierarchy number->function->functional (polynomial=Element, transcendental=role-limit).
- **Tags.** function-as-process, formal-power-series, coefficient-process, H59, vein-C, new-framing, element-role-limit

**Lemmas (28):**

| name | kind | role |
|---|---|---|
| `FPS/fps_eq/fps_zero/one/X/add/neg/sub/scale/mul/deriv` | Definition | реификация функции + FPS-алгебра (mul=conv) |
| `geom_fps/exp_fps/log1m_fps` | Definition | реифицированные функции 1/(1−x), exp, −ln(1−x) |
| `is_polynomial` | Definition | функция-процесс терминирует ⟺ многочлен (Element) |
| `fps_one_polynomial/fps_X_polynomial` | Lemma | Element-сторона: многочлены |
| `geom_not_polynomial/exp_fps_not_polynomial` | Lemma | ★ role-limit: геометрическая/exp НЕ многочлены (H1 на уровне функций) |
| `oneminusX_tail_zero` | Lemma | хвост Σ(1,−1,0,…) с индекса 1 = 0 |
| `geom_inverse_fps` | Lemma | ★★ (1−X)·(1/(1−x))=1 ФОРМАЛЬНО (коэффициент-уровень, аксиомо-своб.) |
| `exp_fps_deriv/log1m_deriv` | Lemma | ★ FPS-исчисление: exp'=exp, (−ln(1−x))'=1/(1−x) (реиф. функции уд. своим ОДУ) |
| `conv_ones/qcancel` | Lemma | conv·geom=Σ (умн. на 1); сокращение a·x=a⟹x=1 |
| `ode_geom_unique` | Lemma | ★★★ ОДУ h'=h·geom, h(0)=1 ⟹ h=geom (структурное сердце E∘L) |
| `geom_satisfies_ode` | Lemma | проверка: geom удовлетворяет h'=h·geom |
| `fps_deriv_mul` | Lemma | ★ ПРАВИЛО ЛЕЙБНИЦА (a·b)'=a'·b+a·b' (фундамент цепного правила; Vandermonde как exp_conv_rec; аксиомо-своб.) |
| `partial_sum_rev` | Lemma | разворот конечной суммы Σf(n−i)=Σf(i) (через partial_sum_head) |
| `conv_comm` | Lemma | ★ КОММУТАТИВНОСТЬ свёртки conv a b=conv b a (переиндекс i↦n−i); аксиомо-своб. |
| `conv_one_l/conv_one_r` | Lemma | ★ ЕДИНИЦА: conv fps_one f=f (fps_one — мультипликативная единица FPS) |
| `partial_sum_triangle_swap` | Lemma | ★ треугольный Fubini-своп ΣᵢΣⱼ≤ᵢ=ΣⱼΣₜ≤ₙ₋ⱼ (i=j+t); ядро ассоциативности |
| `conv_assoc` | Lemma | ★★ АССОЦИАТИВНОСТЬ свёртки (тройная сумма Коши Σ_{j+t≤n} a·b·c через triangle_swap); аксиомо-своб. |
| `fps_mul_comm/fps_mul_one_l/fps_mul_one_r/fps_mul_assoc` | Lemma | ★ FPS = коммутативное кольцо с единицей fps_one (обёртки conv_*) |
| `fps_pow` | Fixpoint | k-я степень ряда g⁰=1, gᵏ⁺¹=g·gᵏ |
| `fps_pow_deriv/fps_pow_deriv_eq` | Lemma | ★★ ПРАВИЛО СТЕПЕНИ (gᵏ⁺¹)'=(k+1)·gᵏ·g' (индукция поверх fps_deriv_mul + кольцо); аксиомо-своб. |
| `fps_pow_low_order` | Lemma | ★ зануление: g(0)=0 ⟹ (gᵏ)ᵢ=0 при i<k (gᵏ имеет порядок ≥k) |
| `partial_sum_extend_zero/partial_sum_swap` | Lemma | удлинение нулевым хвостом; квадратный Fubini ΣᵢΣₖ=ΣₖΣᵢ |
| `fps_compose` | Definition | ★ композиция f∘g при g(0)=0: (f∘g)ₙ=Σ_{k≤n} fₖ·(gᵏ)ₙ (усечена) |
| `fps_compose_zero/fps_deriv_compose_raw` | Lemma | (f∘g)(0)=f(0); сырая производная (f∘g)'ₙ=Σ_{k≤n+1} fₖ(gᵏ)'ₙ |
| `conv_congr_l/conv_congr_r/fps_compose_congr_l` | Lemma | конгруэнции свёртки/композиции по fps_eq |
| `conv_compose_swap` | Lemma | ★★ conv(f∘g)h=Σ_{k≤n} fₖ·conv(gᵏ)h (квадрат⟷треугольник + зануление); база цепного правила |
| `fps_chain_rule` | Lemma | ★★★ ЦЕПНОЕ ПРАВИЛО (f∘g)'=(f'∘g)·g' при g(0)=0; аксиомо-своб. |
| `compose_exp_log1m_is_geom` | Lemma | ★★★★ ФОРМАЛЬНОЕ СЕРДЦЕ E∘L: exp(−ln(1−x))=1/(1−x) на коэффициент-уровне (h'=h·geom + ode_geom_unique); аксиомо-своб. |

**Key lemmas (deep):**

- **`ode_geom_unique`** - Структурное сердце E∘L: ОДУ h'=h·geom (= (1−x)h'=h) с h(0)=1 имеет ЕДИНСТВЕННОЕ FPS-решение geom=1/(1−x). Чистый маршрут БЕЗ sparse-свёртки: since geom=ones, conv h geom = partial_sum h (conv_ones), поэтому h'=h·geom даёт рекуррентность (n+1)h(n+1)=Σ_{≤n}h; индукцией Σ_{≤n}h=n+1 ⟹ h(n)=1. Использует qcancel (сокращение). Это conditional-сердце: остаётся показать, что exp∘log1m удовлетворяет ОДУ (цепное правило FPS) ⟹ безусловно compose=geom. Аксиомо-свободно. Реализует растворение E∘L из H58/H59: обструкция была недостроенным объектом (функция-процесс), не стеной. _(ode-uniqueness, formal-heart, function-as-process, H59, E-circ-L, conv-ones)_
- **`geom_inverse_fps`** - Определяющее уравнение геометрической функции `(1−X)·(1/(1−x))=1`, доказанное на уровне КОЭФФИЦИЕНТ-ПРОЦЕССОВ: свёртка Коши (1,−1,0,…)*(1,1,1,…)=(1,0,0,…)=fps_one. Это «1/(1−x) реифицирована как процесс и её уравнение верифицировано формально» — первая конкретная демонстрация H59 (функция-как-процесс). Аксиомо-свободно. На этом же fps_mul=conv позже строится compose exp_fps log1m_fps=geom (cₙ=1) — формальное сердце E∘L. _(function-as-process, geometric, coefficient-process, vein-C, H59, formal-identity)_
- **`geom_not_polynomial`** - Прямой свидетель границы H1 НА УРОВНЕ ФУНКЦИЙ: геометрическая 1/(1−x) — НЕ многочлен (все cₙ=1≠0), т.е. функция-коэффициент-процесс НЕ терминирует ⟹ role-limit. Многочлен (fps_one/fps_X) терминирует ⟹ Element. Та же Element/role-limit граница, что рациональное/иррациональное у чисел, поднятая на уровень функций иерархии число→функция→функционал. Аксиомо-свободно. _(element-role-limit, function-level, H1-lifted, polynomial-vs-transcendental)_
- **`conv_assoc`** - Ассоциативность свёртки Коши conv(conv a b)c=conv a(conv b c) — обе стороны равны канонической тройной сумме Σ_{j+t≤n} a_j·b_t·c_{n−j−t}. Правая сторона — простым выносом a_j (partial_sum_scale); левая — выносом c_{n−i} (partial_sum_scale_r) плюс ТРЕУГОЛЬНЫЙ Fubini-своп partial_sum_triangle_swap (перегруппировка треугольника {(i,j):j≤i≤n} по столбцу j через i=j+t, индукция по n). Вместе с conv_comm и conv_one_l/r даёт: FPS — КОММУТАТИВНОЕ КОЛЬЦО с единицей fps_one. Этого в репозитории не было (была только Дирихле-свёртка). Фундамент power rule и цепного правила (нужна одна инстанция ассоциативности g·(gᵏ·g')=(g·gᵏ)·g'=gᵏ⁺¹·g'). Аксиомо-свободно. _(cauchy-product, associativity, commutative-ring, fubini-triangle, function-as-process, H59, E-circ-L)_
- **`fps_pow_deriv`** - Правило степени для FPS: (gᵏ⁺¹)'=(k+1)·gᵏ·g' на уровне коэффициентов. Индукция по k поверх правила Лейбница fps_deriv_mul: шаг (g·gᵏ⁺¹)'=g'·gᵏ⁺¹+g·(gᵏ⁺¹)', IH даёт g·((k+1)·gᵏ·g'), затем ВЫНОС СКАЛЯРА (partial_sum_scale, применённый под свёрткой к IH в точке n−i) + АССОЦИАТИВНОСТЬ conv_assoc (g·(gᵏ·g')=(g·gᵏ)·g'=gᵏ⁺¹·g') + КОММУТАТИВНОСТЬ conv_comm (g'·gᵏ⁺¹=gᵏ⁺¹·g'), сумма (1+(k+1))·gᵏ⁺¹·g'. Скомпилировался с первого раза после точного планирования. Это последний кусок ИСЧИСЛЕНИЯ перед композицией: имея power rule + линейность, цепное правило (f∘g)'=(f'∘g)·g' для exp∘log1m даёт ОДУ h'=h·geom ⟹ compose=geom (ode_geom_unique) = формальное сердце E∘L. Аксиомо-свободно. _(power-rule, calculus, induction, leibniz, function-as-process, H59, E-circ-L)_
- **`conv_compose_swap`** - База цепного правила: conv(f∘g)h = Σ_{k≤n} fₖ·conv(gᵏ)h при g(0)=0. conv(f∘g)h_n=Σ_{i≤n}(Σ_{k≤i} fₖ(gᵏ)ᵢ)h_{n−i} — ТРЕУГОЛЬНИК по (i,k). Поскольку при g(0)=0 ряд gᵏ имеет порядок ≥k (fps_pow_low_order: (gᵏ)ᵢ=0 при k>i), внутреннюю сумму k≤i можно УДЛИНИТЬ до k≤n нулями (partial_sum_extend_zero) — треугольник становится КВАДРАТОМ; затем меняем порядок суммирования (partial_sum_swap, квадратный Fubini) и выносим fₖ. Ровно та же геометрия квадрат⟷треугольник, что в conv_assoc/partial_sum_triangle_swap, но через зануление, а не переиндекс. Аксиомо-свободно. _(composition, double-sum, triangle-square, low-order-vanishing, function-as-process, H59, E-circ-L)_
- **`compose_exp_log1m_is_geom`** - ★ ФОРМАЛЬНОЕ СЕРДЦЕ E∘L, доказанное 0-АКСИОМНО: exp(−ln(1−x))=1/(1−x) на уровне коэффициент-процессов FPS. h:=fps_compose exp_fps log1m_fps удовлетворяет определяющему ОДУ геометрической h'=h·geom — по ЦЕПНОМУ ПРАВИЛУ fps_chain_rule (f∘g)'=(f'∘g)·g' с exp'=exp (exp_fps_deriv) и log1m'=geom (log1m_deriv) — и h(0)=exp(0)=1; откуда ode_geom_unique даёт h=geom. ЭТО РАСТВОРЕНИЕ обструкции E∘L, которую H58/H59 диагностировали как «финитизационную границу второго порядка» (функции ещё НЕ ставшие процессами): путь сквозь стену — реификация функции как коэффициент-процесса (FPS:=nat→Q), и тогда тождество обратной функции exp∘(−ln(1−·))=1/(1−·) становится process-рекуррентностью cₙ=1, доказуемой машинно. Классическая математика (FPS, exp/log) — но ToS-обрамление (функция=процесс, обструкция=недостроенный объект, не стена) + машинная 0-аксиомная проверка конкретной границы. Остаётся аналитический мост к процессам-числам (eval) → горизонт ln_mul. _(E-circ-L, formal-heart, chain-rule, function-as-process, H59, ode-uniqueness, 0-axiom, obstruction-dissolved)_

**Uniqueness - score 3 (new-framing).** Реификация аналитической функции как коэффициент-ПРОЦЕССА (nat→Q) в процессной онтологии ToS (программа H59), доведённая до ПОЛНОГО ИСЧИСЛЕНИЯ FPS (кольцо, производная, Лейбниц, степень, КОМПОЗИЦИЯ, ЦЕПНОЕ ПРАВИЛО) и до ФОРМАЛЬНОГО РАСТВОРЕНИЯ обструкции E∘L: exp(−ln(1−x))=1/(1−x) доказано 0-аксиомно на уровне коэффициент-процессов (compose_exp_log1m_is_geom). Граница Element/role-limit поднята на уровень функций (многочлен/трансцендентная). 0-аксиомно.
> _Caveat:_ Сама математика классична (формальные ряды, кольцо, цепное правило, exp/log-композиция). Уникальность — НЕ новый матфакт, а: (1) ToS-обрамление (функция=процесс, обструкция E∘L = недостроенный объект «функция ещё не ставшая процессом», а не стена — диагноз H58/H59 подтверждён конструктивно); (2) машинная 0-аксиомная проверка ВСЕЙ цепочки до конкретного тождества обратной функции. Остаётся аналитический мост от формальных рядов к процессам-числам (eval: FPS → CauchyReal) → горизонт ln_mul.

---

## #1836 - `src/FPSEval.v` - score 3 (new-framing)

**Analytic bridge: eval(formal series) -> number-process; the formal heart of E.L evaluated = 1/(1-x)**

- **Topic.** eval a x := series_limit (fun n => a_n * x^n) — evaluation of a formal power series (object-in-theory) as a Cauchy number-process. Convergence for |a_n|<=1, 0<=x<1 by absolute majorization with the geometric series (absolute_convergence + geometric_series_cauchy). eval_congr (equal coefficients => ~~ equal eval, via series_limit_wd). Anchor eval_geom: eval geom_fps x ~~ geometric_limit x (Sum 1*x^n = Sum x^n = 1/(1-x)). Flagship eval_compose_exp_log1m_geom: the FORMAL composition exp.log1m — whose coefficients we proved 0-axiom to be all 1 (compose_exp_log1m_is_geom) — EVALUATED as a real number-process IS the geometric series 1/(1-x). First analytic consequence of the formal heart.
- **Role.** Anchor + ring-homomorphism core of the analytic eval-bridge (the second, hard half of the ln_mul program). Crosses from the purely formal 0-axiom world (FormalPowerSeries) into the L3 Cauchy-real analysis world (hence inherits classic, like the rest of the analysis library — the FIRST file in this FPS chain to do so). DONE: eval + convergence; eval_geom + the formal heart evaluated = 1/(1-x); eval MULTIPLICATIVE (eval_mul: eval(a*b)=eval a * eval b) via mertens_cauchy_product + the identity (a*b)_n x^n = conv(a_i x^i)(b_j x^j)_n (eval_terms_mul) — the reusable ring-hom brick, giving eval(g^k)=(eval g)^k. The exp/log ANCHORS are also done: eval_exp (eval exp_fps t ~~ exp_limit t) and eval_log1m (eval log1m_fps x ~~ ln_proc x via an index shift) tie the formal basis objects to the existing analytic processes exp_limit/ln_proc. The eval RING-HOMOMORPHISM is also complete now: eval_add/zero/one/neg/sub/scale (eval preserves +,0,1,-,scalar) on top of eval_mul -- the algebraic ones are 0-AXIOM (pure partial-sum algebra; eval_add audit = Closed). The OBSTRUCTION diagnosed earlier is now RESOLVED: eval_mul_abs (eval multiplicative under an ABSOLUTE-CONVERGENCE hypothesis abs_conv instead of a uniform bound; bounds Ma/Mb extracted from abs_conv_bounded) + abs_conv_pow (abs-convergence closed under multiplication) make the POWER LAW eval_pow: eval(g^k) ~~ (eval g)^k iterate cleanly. NEXT (the boss): the composition law eval(f.g) x ~~ Sum_k f_k (eval g x)^k (double-series Fubini: Sum_n Sum_{k<=n} f_k (g^k)_n x^n = Sum_k f_k Sum_n (g^k)_n x^n, finite inner sum by low-order vanishing) -- now eval_pow supplies the Sum_n (g^k)_n x^n = (eval g x)^k step; remaining is the outer infinite-sum interchange. With f=exp, g=log1m the composition law gives eval(exp.log1m) x ~~ exp_R(ln_proc x); combined with eval_compose_exp_log1m_geom -> exp_R(L(x)) ~~ 1/(1-x) -> ln_mul horizon L(x)+L(y)~~L(x+y-xy).
- **Counts.** Qed 34 / Admitted 0 / axioms 1
- **Imports.** Stdlib: QArith; Qabs; Lqa; Lia; ZArith; ToS: CauchyReal; RealField; SeriesConvergence; CauchyProduct; ExpFunctionalEquation; PowerSeries; zeta.LogZeta; Log2Process; FormalPowerSeries
- **E/R/R.** _Elements:_ коэффициенты aₙ∈Q и значение x∈Q; на каждой стадии — конечная Q-сумма Σ_{k≤n} aₖxᵏ. _Roles:_ eval = роль-ВЫЧИСЛЕНИЕ формального ряда (объект-в-теории) в число-процесс (CauchySeq); мост двух процессных слоёв (формальный↔аналитический). _Rules:_ eval a x := series_limit (λn. aₙ·xⁿ); сходимость при \|aₙ\|≤1,0≤x<1 — абсолютная мажорация геометрическим (absolute_convergence). _P4:_ eval переводит формальную функцию-процесс (коэффициенты) в число-процесс (частичные суммы) — оба конечно-актуальны на каждой стадии. Унаследует classic (L3) — мост ВПЕРВЫЕ входит в L3-анализ Коши-вещественных (формальный слой был 0-аксиомен).
- **Classical counterpart.** Evaluating a formal power series at a point (Sum a_n x^n) and absolute convergence by geometric majorization are classical. NEW: eval as the explicit BRIDGE between the two process layers of ToS — the formal function-process (FPS coefficient-process, FormalPowerSeries.v) and the analytic number-process (CauchyReal series_limit) — transporting the 0-axiom formal heart of E.L into a real number-process identity.
- **Tags.** eval-bridge, formal-to-analytic, E-circ-L, function-as-process, H59, vein-C, new-framing, cauchy-real

**Lemmas (23):**

| name | kind | role |
|---|---|---|
| `is_cauchy_ext/series_limit_wd` | Lemma | конгруэнции: поточечно равные посл./ряды ⟹ Cauchy/~~ переносятся |
| `eval_terms/eval` | Definition | члены aₙxⁿ; eval a x := series_limit (с свидетелем сходимости) |
| `eval_terms_cauchy_le1` | Lemma | ★ сходимость eval при \|aₙ\|≤1, 0≤x<1 (мажорация Σxⁿ через absolute_convergence) |
| `eval_congr` | Lemma | равные коэффициенты ⟹ равный eval |
| `geom_coeff_le1/geom_eval_cauchy` | Lemma | коэф. geom ограничены 1; свидетель сходимости eval geom |
| `eval_geom` | Lemma | ★ АНКЕР: eval geom_fps x ~~ geometric_limit x (Σ1·xⁿ=Σxⁿ=1/(1−x)) |
| `compose_coeff_le1` | Lemma | коэф. формальной композиции exp∘log1m ограничены 1 (они ≡1 по сердцу) |
| `eval_compose_exp_log1m_geom` | Theorem | ★★ формальное сердце E∘L, ВЫЧИСЛЕННОЕ: eval(exp∘log1m) x ~~ 1/(1−x) |
| `Qpow_add` | Lemma | x^{i+j}=x^i·x^j (аддитивность степени) |
| `eval_terms_mul` | Lemma | ★ тождество (a·b)ₙxⁿ = conv(aᵢxⁱ)(bⱼxʲ)ₙ — мост к Мертенсу |
| `geom_partial_bound/eval_abs_bound` | Lemma | Σxᵏ≤1/(1−x); Σ\|aₖ\|xᵏ≤B/(1−x) (абс-границы для Мертенса) |
| `conv_eval_cauchy` | Lemma | сходимость свёртки eval-рядов (Hconv): \|conv\|≤conv\|·\| + conv_cauchy |
| `eval_mul` | Theorem | ★★ eval МУЛЬТИПЛИКАТИВЕН: eval(a·b) ~~ eval a · eval b (через mertens_cauchy_product) |
| `eval_exp` | Lemma | ★ АНКЕР: eval exp_fps t ~~ exp_limit t (члены (1/n!)tⁿ=tⁿ(1/n!), Qmult_comm; для любого t) |
| `eval_log1m` | Lemma | ★ АНКЕР: eval log1m_fps x ~~ ln_proc x (сдвиг индекса: partial_sum(S n)=log_series_partial n; Cauchy-сдвиг) |
| `cauchy_equiv_from_cs_eq/partial_sum_neg` | Lemma | хелперы: поточечно равные стадии ⟹ ~~; Σ(−f)=−Σf |
| `eval_add/eval_zero/eval_one/eval_neg/eval_sub/eval_scale` | Lemma | ★ ℚ-АЛГЕБРА-ГОМОМОРФИЗМ: eval сохраняет +,0,1,−,скаляр (АКСИОМО-СВОБОДНЫ — чистая алгебра частичных сумм; eval_add=Closed) |
| `abs_conv/abs_eval_terms/abs_conv_eval_cauchy` | Definition+Lemma | абсолютная сходимость Σ\|aₙ\|xⁿ; \|aₙxⁿ\|=\|aₙ\|xⁿ; abs⟹обычная сходимость |
| `abs_conv_bounded` | Lemma | ★ монотонные абс-частичные суммы Cauchy ⟹ ограничены сверху (извлекает Ma для Мертенса) |
| `eval_mul_abs` | Theorem | ★★ eval МУЛЬТИПЛИКАТИВЕН под АБС-сходимостью (ИТЕРИРУЕМАЯ версия — гипотеза abs_conv, не \|aₙ\|≤B) |
| `cauchy_pow/abs_conv_one/abs_conv_mul/abs_conv_pow` | Fixpoint+Lemma | k-я степень процесса; замкнутость abs-сходимости (·, 1, gᵏ) — делает power law итерируемым |
| `eval_pow` | Lemma | ★★ POWER LAW: eval(fps_pow g k) ~~ cauchy_pow (eval g) k (индукция через eval_mul_abs + abs_conv_pow) |
| `eval_compose_swap` | Lemma | ★★ КОНЕЧНЫЙ FUBINI композиции (0-АКСИОМЕН): partial_sum(eval_terms(f∘g)z)n = Σ_{k≤n} fₖ·partial_sum(eval_terms(gᵏ)z)n (квадрат⟷треугольник+зануление) — внутренняя половина босса |

**Key lemmas (deep):**

- **`eval_compose_exp_log1m_geom`** - Первое АНАЛИТИЧЕСКОЕ следствие 0-аксиомного формального сердца E∘L. Формальная композиция fps_compose exp_fps log1m_fps (которой мы машинно доказали коэффициенты ≡1 = compose_exp_log1m_is_geom, БЕЗ аксиом) ВЫЧИСЛЯЕТСЯ как число-процесс eval: eval(exp∘log1m) x ~~ eval geom_fps x (равные коэф., eval_congr) ~~ geometric_limit x (eval_geom) = Σxⁿ = 1/(1−x). Это перенос тождества коэффициентов в реальное равенство чисел-процессов для геометрической стороны. ЧЕСТНАЯ ГРАНИЦА: это ещё НЕ exp_R(ln_proc x)~~1/(1−x) — для этого нужен закон композиции (eval f∘g = eval f ∘ eval g, Fubini двойного ряда) + анкеры exp/log к exp_R/ln_proc; это трудная половина. Но мост от формального мира в число-процессы открыт и анкер geom доказан. Унаследует classic (L3-анализ). _(eval-bridge, E-circ-L, formal-to-analytic, geometric, function-as-process, H59, honest-boundary)_
- **`eval_mul`** - eval — КОЛЬЦЕВОЙ ГОМОМОРФИЗМ по умножению: eval(a·b) x ~~ cauchy_mul (eval a x)(eval b x). Доказано через ранее построенный mertens_cauchy_product (Cauchy-произведение) + КЛЮЧЕВОЕ тождество eval_terms_mul: (a·b)ₙ·xⁿ = conv(λi.aᵢxⁱ)(λj.bⱼxʲ)ₙ (т.к. xⁱ·x^{n−i}=xⁿ, Qpow_add) — т.е. члены произведения-ряда суть свёртка Коши взвешенных рядов. Для гипотез Мертенса: абс-границы Σ\|aₖ\|xᵏ≤B/(1−x) (eval_abs_bound через геом. оценку Σxᵏ≤1/(1−x)) и сходимость свёртки conv_eval_cauchy (\|conv â b̂\|≤conv\|â\|\|b̂\|, неотриц.+огранич. ⟹ conv_cauchy). Это самый переиспользуемый кирпич трудной половины моста: имея eval(a·b)=eval a·eval b, получаем eval(gᵏ)=（eval g)ᵏ — основу закона композиции eval(f∘g)=Σ fₖ(eval g)ᵏ. Унаследует classic (L3). _(eval-bridge, ring-homomorphism, mertens, cauchy-product, formal-to-analytic, H59, function-as-process)_
- **`eval_ring_hom`** - eval : FPS → ℝ_proc (CauchySeq) есть ГОМОМОРФИЗМ ℚ-АЛГЕБР: eval_add (eval(a+b)=eval a+eval b), eval_zero (=0), eval_one (=1), eval_neg (=−), eval_sub, eval_scale (eval(c·a)=c·eval a) — плюс eval_mul (мультипликативность, выше). Все АЛГЕБРАИЧЕСКИЕ леммы 0-АКСИОМНЫ (Print Assumptions eval_add = Closed under the global context) — это чистая алгебра частичных сумм (eval_terms аддитивны/масштабируемы термвайз + partial_sum_plus/scale/minus/neg), не затрагивающая classic-зависимую машину сходимости. Тонкое разделение: convergence-факты (eval_geom/mul/exp/log1m) наследуют classic (L3-анализ), а алгебра гомоморфизма — нет. КЛЮЧЕВОЙ НЮАНС для следующего шага (закон композиции): power law eval(gᵏ)=(eval g)ᵏ НЕ выводится итерацией текущего eval_mul, т.к. eval_mul требует РАВНОМЕРНУЮ границу коэффициентов \|aₙ\|≤B, а коэффициенты gᵏ РАСТУТ (число композиций n на k частей, полиномиально по n) — равномерной границы нет. Нужна ВЕРСИЯ eval_mul с гипотезой АБСОЛЮТНОЙ СХОДИМОСТИ eval-ряда (is_cauchy(partial_sum(λn.\|aₙ\|xⁿ))) вместо границы — она итерируема (Σ\|gᵏ_n\|xⁿ сходится как полином×геометрия). Это диагностированная обструкция, не стена. _(ring-homomorphism, eval-bridge, 0-axiom-algebra, convergence-insight, power-law-obstruction, H59)_
- **`eval_compose_swap`** - ВНУТРЕННЯЯ ПОЛОВИНА композиционной теоремы (босса), доказанная 0-АКСИОМНО (Closed): n-я стадия eval(f∘g) z = Σ_{k≤n} fₖ·(n-я стадия eval(gᵏ) z). Это конечный внешний Fubini — ТА ЖЕ геометрия квадрат⟷треугольник, что в conv_compose_swap (FormalPowerSeries), переиспользует partial_sum_swap + partial_sum_extend_zero + fps_pow_low_order (зануление (gᵏ)_m=0 при k>m, g(0)=0), но с весами zᵐ. Сводит композиционную теорему eval(f∘g)~~Σ fₖ(eval g)ᵏ к ДИАГОНАЛЬНОМУ переходу к пределу: partial_sum(eval_terms(gᵏ)z)n → (eval g z)ᵏ [eval_pow готов] при n→∞, а внешняя Σ_{k≤n} расширяется до ∞ — нужна РАВНОМЕРНОСТЬ (Tannery/равномерная сходимость двойной диагонали) + связь Σ(1/k!)vᵏ с exp_R(v) (диагональ exp_R). Чисто конечная алгебра ⟹ 0-аксиомна (в отличие от convergence-зависимых eval_*). _(composition-theorem, finite-fubini, 0-axiom, square-triangle, boss-inner-half, eval-bridge, H59)_
- **`eval_pow`** - POWER LAW eval(gᵏ) ~~ (eval g)ᵏ — снимает обструкцию, диагностированную на пред. шаге. Текущий eval_mul (равномерная граница \|aₙ\|≤B) НЕ итерируется на gᵏ (коэф. растут). Решение: eval_mul_abs — версия с гипотезой АБСОЛЮТНОЙ СХОДИМОСТИ abs_conv a := is_cauchy(partial_sum(λn.\|aₙ\|xⁿ)). Границы Ma/Mb для Мертенса извлекаются из abs_conv_bounded (монотонные неотриц. частичные суммы + Cauchy ⟹ ограничены сверху: для M≥N через \|s M−s N\|<1, для M<N через монотонность). Замкнутость абс-сходимости относительно умножения abs_conv_mul (\|（a·b)ₙ\|xⁿ≤(conv\|a\|\|b\|)ₙxⁿ=conv(\|a\|x^•)(\|b\|x^•)ₙ через eval_terms_mul для \|a\|,\|b\|, далее conv_cauchy) делает abs_conv_pow (abs_conv gᵏ) итерируемым. Тогда eval_pow — чистая индукция: g⁰=1 (eval_one), g·gᵏ через eval_mul_abs+IH (свидетели из abs_conv_eval_cauchy). Это основа закона композиции eval(f∘g)=Σ fₖ(eval g)ᵏ. Унаследует classic (Мертенс/анализ). _(power-law, absolute-convergence, iterable, mertens, eval-bridge, obstruction-resolved, H59)_
- **`eval_log1m`** - АНКЕР формального логарифма к существующему лог-процессу: eval log1m_fps x ~~ ln_proc x. Тонкость — СДВИГ ИНДЕКСА: log1m_fps имеет нулевой коэффициент в степени 0 (log1m_fps 0=0), поэтому eval_terms log1m_fps x несёт лишний нуль в начале, а далее ровно члены ln_proc (x^{S k}/(S k)). Следствие: partial_sum (eval_terms log1m_fps x) (S n) == log_series_partial x n (partial_sum_head убирает голову-нуль + поточечное совпадение хвоста). Две Cauchy-последовательности, сдвинутые на 1, эквивалентны (~~) — тот же предел; формально: для n=S m, \|cs(eval)(S m) − cs(ln_proc)(S m)\| = \|log_series_partial m − log_series_partial (S m)\| < eps по Cauchy-свойству ln_proc (ln_series_cauchy). Вместе с eval_exp (тривиальный анкер exp через Qmult_comm) это привязывает формальные базис-объекты exp_fps/log1m_fps к аналитическим процессам exp_limit/ln_proc — необходимый мост перед законом композиции и exp_R(L(x))~~1/(1−x). Унаследует classic. _(eval-bridge, anchor, index-shift, ln-proc, formal-to-analytic, H59, cauchy-shift)_

**Uniqueness - score 3 (new-framing).** eval как явный МОСТ между двумя процессными слоями ToS (формальный коэффициент-процесс ↔ аналитический число-процесс), переносящий 0-аксиомное формальное сердце E∘L в реальное равенство чисел-процессов: вычисленная формальная композиция exp∘(−ln(1−x)) = геометрический ряд 1/(1−x).
> _Caveat:_ Вычисление степенного ряда и абсолютная сходимость классичны. Уникальность — в ToS-обрамлении (два процессных слоя и явный мост между ними) и в переносе именно нашего 0-аксиомного формального результата. Это первый анкер; полный мост (eval-гомоморфизм через Мертенса + закон композиции → exp_R(L(x))~~1/(1−x)) — впереди. Файл ВПЕРВЫЕ в цепи наследует classic (вход в L3-анализ).

---

## #1837 - `src/LnMulReduction.v` - score 3 (new-framing)

**Endgame: the ln_mul horizon reduced to one key fact (exp_R o ln_proc = 1/(1-z))**

- **Topic.** Conditional theorem ln_mul_from_key: IF exp_R(ln_proc z) ~~ geometric_limit z (=1/(1-z)) for all z in [0,1), THEN the horizon ln_mul_functional_equation (Log2FunctionalEq) is proved. Built from: geom_inv ((1-z)*(1/(1-z)) ~~ 1, via geometric_sum_identity + Qpow_limit_zero), geom_mul (1/(1-x)*1/(1-y) ~~ 1/(1-(x+y-xy)), via (1-x)(1-y)=1-(x+y-xy) + cancellation cauchy_const_cancel + 4-factor swap cmul4_swap), and the assembly through exp_R_add (exp_R linearizes the log: exp_R(L(x)+L(y))=exp_R L(x)*exp_R L(y)) + exp_R_inj. NOT an Admit -- a genuine conditional theorem that honestly separates the finished endgame assembly from the one remaining boss (the composition theorem, built in FPSEval).
- **Role.** Endgame assembly of the ln_mul program. Independent of the FPS bridge file (uses only exp_R/ln_proc/geometric_limit), it proves everything EXCEPT the single key fact exp_R(ln_proc z)~~1/(1-z). That key fact is exactly the meeting point: FPSEval proves eval(exp.log1m) z ~~ geometric_limit z (done) and aims for eval(exp.log1m) z ~~ exp_R(ln_proc z) (the composition theorem, the boss); together they give the key fact, and ln_mul_from_key then closes the horizon. So the WHOLE ln_mul program now reduces to one lemma. Inherits classic (exp_R/analysis).
- **Counts.** Qed 8 / Admitted 0 / axioms 1
- **Imports.** Stdlib: QArith; Qabs; Lqa; Lia; ToS: CauchyReal; RealField; SeriesConvergence; ProcessExp; Log2Process; Log2FunctionalEq
- **E/R/R.** _Elements:_ частичные суммы геометрического/лог-ряда и их произведения — конечные Q на стадии n. _Roles:_ geom_inv = роль-обратная (1−z); geom_mul = роль-мультипликативность геометрической; ln_mul_from_key = роль-редукция горизонта к ключу. _Rules:_ geometric_sum_identity ((1−r)Σ=1−rⁿ⁺¹) + zⁿ→0; сокращение на cauchy_const≠0; exp_R_add/exp_R_inj. _P4:_ exp_R линеаризует логарифм-процесс: аддитивность L(x)+L(y) сводится к мультипликативности exp_R(L(x))·exp_R(L(y)), замкнутой на геометрической стороне. Унаследует classic.
- **Classical counterpart.** The logarithm functional equation ln(ab)=ln a+ln b and 1/(1-x)*1/(1-y)=1/(1-(x+y-xy)) are classical. NEW: the explicit machine-checked REDUCTION showing the ToS process-level horizon ln_mul_functional_equation (L(x)+L(y)~~L(x+y-xy) over the Cauchy-real processes ln_proc) follows from a SINGLE fact exp_R(ln_proc z)~~1/(1-z) -- isolating exactly the remaining work (the composition theorem) without any Admit.
- **Tags.** ln-mul, endgame, reduction, exp-R, process-ontology, H59, new-framing, conditional-theorem

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `cs_eq_equiv/cauchy_const_wd/cauchy_const_mul` | Lemma | хелперы: равные стадии ⟹ ~~; cauchy_const уважает Qeq и умножение |
| `geom_inv` | Lemma | ★ (1−z)·(1/(1−z)) ~~ 1 (процессная обратная геометрической; geometric_sum_identity + zⁿ→0) |
| `cauchy_const_cancel/cmul4_swap` | Lemma | сокращение на cauchy_const≠0 (единственность обратного); перестановка 4 множителей |
| `geom_mul` | Lemma | ★ 1/(1−x)·1/(1−y) ~~ 1/(1−(x⊕y)) (через (1−x)(1−y)=1−(x⊕y) + geom_inv + сокращение) |
| `ln_mul_from_key` | Theorem | ★★ ГОРИЗОНТ ln_mul_functional_equation ⟸ exp_R(ln_proc z)~~1/(1−z) (через exp_R_add + exp_R_inj + geom_mul) |

**Key lemmas (deep):**

- **`ln_mul_from_key`** - ★★ ЭНДШПИЛЬ ИЗОЛИРОВАН: весь горизонт ln_mul_functional_equation (L(x)+L(y)~~L(x⊕y) над процессами ln_proc) ДОКАЗУЕМО следует из ЕДИНСТВЕННОГО факта exp_R(ln_proc z)~~geometric_limit z (=1/(1−z)). Доказательство: exp_R_inj сводит L(x)+L(y)~~L(x⊕y) к exp-уровню; exp_R_add даёт exp_R(L(x))·exp_R(L(y)); KEY превращает каждый множитель в 1/(1−·); geom_mul даёт 1/(1−x)·1/(1−y)=1/(1−x⊕y) (через ключевое (1−x)(1−y)=1−(x⊕y) + сокращение на cauchy_const + перестановку 4 множителей); KEY обратно к exp_R(L(x⊕y)). ЭТО НЕ ADMIT — честная conditional-теорема, отделяющая СДЕЛАННУЮ сборку от оставшегося босса (закон композиции eval(exp∘log1m)=exp_R∘ln_proc, внешний Fubini, строится в FPSEval). Уникальность — машинно-проверяемая редукция конкретного функц. уравнения логарифма к одному мостовому факту в процессной онтологии; математика классична, изоляция/обрамление — нет. Унаследует classic. _(ln-mul, endgame, reduction, isolation, exp-R, log-functional-equation, H59, conditional-theorem)_
- **`geom_inv`** - Процессная версия определяющего уравнения геометрической: (1−z)·(1/(1−z)) ~~ 1. cs_seq(cauchy_mul (const(1−z))(geom z)) n = (1−z)·Σ_{≤n}zᵏ = 1−z^{n+1} (geometric_sum_identity); разность с cauchy_one = −z^{n+1} → 0 (Qpow_limit_zero). Аналитический аналог формального geom_inverse_fps ((1−X)·geom=1 на коэффициентах) — то же тождество, но на уровне ЧИСЕЛ-процессов. Основа geom_mul (через единственность обратного). Унаследует classic. _(geometric, inverse, process-level, geometric-sum-identity, ln-mul)_

**Uniqueness - score 3 (new-framing).** Машинно-проверяемая РЕДУКЦИЯ: процессный горизонт ln_mul (функц. уравнение логарифма над Коши-вещественными ln_proc) сведён к ЕДИНСТВЕННОМУ мостовому факту exp_R(ln_proc z)~~1/(1−z), с полной сборкой эндшпиля (geom_inv, geom_mul, exp_R_add/inj) — БЕЗ Admit. Изолирует оставшийся босс (закон композиции).
> _Caveat:_ Функц. уравнение логарифма и геометрическая алгебра классичны. Уникальность — НЕ матфакт, а: (1) честная conditional-структура, изолирующая ровно один недостающий мост (диагностический приём в духе E/R/R); (2) процессная онтология (всё над ln_proc/exp_R/geometric_limit как процессами-числами). Ключевой факт exp_R∘ln_proc=1/(1−z) — впереди (FPSEval, внешний Fubini).

