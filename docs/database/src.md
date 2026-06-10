# Database - cluster `src`

_Generated from `src.json` by `generate.ps1` - do not edit by hand; edit the JSON._

**81 files / 1710 Qed.** Score distribution: s5=1 / s4=6 / s3=14 / s2=46 / s1=11 / s0=3

---

## #17 - `src/AIInterface.v` - score 2 (methods)

**AI interface: verified-safe generation (well-typed => safe result)**

- **Topic.** An AIResult wrapping process/checking, ai_eval (and annotated), proofs that AI-verified outputs are well-typed and progress, errors mean ill-typed, end-to-end ai_generation_safe, and termination.
- **Role.** Type-theory application (safe AI generation). Combines Evaluator. Imports it. June 2026 wave-4 tail: ai_pipeline_terminates was the vacuous exists r -> None-or-Some (T, v) option dichotomy.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** ToS Evaluator
- **E/R/R.** _Elements:_ AI-генерация программ; результат AIResult. _Roles:_ интерфейс как роль безопасной генерации (принятое ⟹ type-safe). _Rules:_ ai_verified_well_typed; ai_error_means_ill_typed; ai_generation_safe. _P4:_ ★ всякая ПРИНЯТАЯ AI-программа type-safe end-to-end (Element): ошибка ⟺ ill-typed; безопасность гарантирована проверкой, не доверием.
- **Classical counterpart.** Wrapping a verified type-check-then-eval pipeline as a safe API (ill-typed => error, well-typed => safe result) is the standard 'verified frontend'; NEW is only the ToS framing: an AI-generation interface where every accepted program is type-safe end-to-end.
- **Tags.** AI-interface, verified-safe, type-safety, application, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `AIResult/process_ai_expr/ann/ai_eval/ai_verified_well_typed/ann_well_typed/progress` | Definition/Lemma | ★ AI-результат верифицированно well-typed |
| `ai_error_means_ill_typed/ai_eval_sound/progress/ann_sound/ai_generation_safe/pipeline_terminates` | Lemma | ★ ошибка ⟺ ill-typed; генерация безопасна end-to-end |

**Key lemmas (deep):**

- **`ai_generation_safe`** - End-to-end безопасность AI-генерации: всякая ПРИНЯТАЯ программа type-safe (well-typed ⟹ безопасный результат + progress), ошибка ⟺ ill-typed. Element-сторона: безопасность гарантируется ВЕРИФИЦИРОВАННОЙ проверкой (verified_pipeline), не доверием к генератору. Прикладная вершина type-safety цепочки. _(AI-interface, verified-safe, end-to-end)_

**Uniqueness - score 2 (methods).** Интерфейс безопасной AI-генерации: принятое ⟹ type-safe end-to-end (ошибка ⟺ ill-typed), на верифицированном конвейере.
> _Caveat:_ Verified frontend стандартен; вклад — ToS-применение (безопасная генерация программ), вершина type-safety цепочки.

---

## #66 - `src/Archimedean_ERR.v` - score 1 (exposition)

**Archimedean property over Q: 2^n unbounded, shrinking intervals Cauchy**

- **Topic.** Powers of 2 (monotone, unbounded, exceed any positive bound), the Archimedean width property, and that shrinking intervals are Cauchy -- the rate machinery beneath bisection/uncountability.
- **Role.** Archimedean/rate foundation (uncountability + analysis). Self-contained.
- **Counts.** Qed 14 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ степени 2; ширины интервалов. _Roles:_ архимедовость как роль (нет бесконечно малых); скорость убывания. _Rules:_ pow2 неограничена; width_shrinks; shrinking_interval_Cauchy. _P4:_ архимедовость аксиомо-свободна; 2^n превосходит любую границу — Element-сторона скорости (никаких бесконечно малых).
- **Classical counterpart.** The Archimedean property (no infinitesimals; 2^n exceeds any bound) is classical; NEW: nothing -- the pow2/Archimedean machinery (interval widths shrink, shrinking-interval Cauchy) underlying the uncountability/analysis files.
- **Tags.** archimedean, pow2, rate, foundation, exposition

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `pow2/Qpow2/pow2_mono/pow2_ge_Sn/pow2_exceeds_pos/pow2_unbounded` | Definition/Lemma | ★ степени 2 монотонны и неограничены |
| `Archimedean/Archimedean_width/width_shrinks/shrinking_interval_Cauchy` | Lemma | ★ архимедова ширина; сужающиеся интервалы — Cauchy |

**Key lemmas (deep):**

- **`pow2_unbounded`** - 2^n превосходит любую положительную границу над Q (архимедовость) — основа скорости сходимости всех бисекционных процессов (uncountability, IVT, EVT, Banach). Element-сторона: нет бесконечно малых, скорость явная. _(archimedean, pow2, rate)_

**Uniqueness - score 1 (exposition).** Архимедовость над Q (2^n неограничена, сужающиеся интервалы — Cauchy) — скоростной фундамент бисекций/несчётности/анализа.
> _Caveat:_ Архимедово свойство классично; ценность инфраструктурная (скорость для bisection-процессов).

---

## #83 - `src/CauchyProcessBridge.v` - score 1 (exposition)

**Bridge: RealProcess <-> CauchySeq, with multiplication**

- **Topic.** The is_Cauchy/is_cauchy equivalence, conversion to/from CauchySeq, process equivalence matching Cauchy equivalence, and process multiplication preserving Cauchy (commutative, associative).
- **Role.** Bridge between the process and Cauchy presentations of reals. Imports CauchyReal/ProcessCore-style. Self-contained.
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; CauchyReal
- **E/R/R.** _Elements:_ RealProcess и CauchySeq представления реала. _Roles:_ мост между двумя презентациями; умножение процессов. _Rules:_ is_Cauchy ⟺ is_cauchy; process_mul сохраняет Cauchy. _P4:_ две презентации реала-процесса эквивалентны; умножение замкнуто (Element).
- **Classical counterpart.** Equivalence of two constructive-real presentations and lifting multiplication across them is routine; NEW: nothing -- a bridge between RealProcess (ProcessCore) and CauchySeq with multiplication preserving Cauchy.
- **Tags.** bridge, real-process, cauchy, multiplication, exposition

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `is_Cauchy_iff_is_cauchy/to_CauchySeq/process_equiv_iff_cauchy_equiv` | Lemma | ★ эквивалентность презентаций |
| `process_mul/mul_preserves_Cauchy/process_mul_comm/assoc` | Definition/Lemma | ★ умножение процессов сохраняет Cauchy |

**Key lemmas (deep):**

- **`is_Cauchy_iff_is_cauchy`** - Две презентации реала (RealProcess из ProcessCore и CauchySeq) эквивалентны — мост, позволяющий процессной и аналитической веткам говорить об одних реалах. Element-сторона: умножение процессов сохраняет Cauchy, замыкая арифметику. _(bridge, real-process, cauchy)_

**Uniqueness - score 1 (exposition).** Мост RealProcess ↔ CauchySeq + умножение процессов (сохраняет Cauchy) — стыковка процессной и аналитической презентаций реала.
> _Caveat:_ Эквивалентность презентаций рутинна; ценность инфраструктурная (стыковка веток).

---

## #84 - `src/CauchyReal.v` - score 3 (new-framing)

**Real numbers as Cauchy processes: RealProcess := nat -> Q**

- **Topic.** The Cauchy predicate and CauchySeq, equivalence (an equivalence relation), addition/negation/subtraction/constants preserving Cauchy and respecting equivalence, ordering, and rational approximation -- reals as processes, never importing Coq's Reals.
- **Role.** THE definition of reals in ToS (vein C). RealProcess := nat->Q. Bottleneck for 333+ files via ProcessCore. Self-contained (QArith only).
- **Counts.** Qed 19 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ последовательности nat→Q; их Cauchy-свойство. _Roles:_ реал = Cauchy-ПРОЦЕСС (не завершённый объект); эквивалентность = равенство реалов. _Rules:_ арифметика поточечная, сохраняет Cauchy и уважает эквивалентность. _P4:_ ★ RealProcess := nat→Q ЕСТЬ определение реала; ℝ — процесс потенциальной, не актуальной бесконечности; Coq Reals НИКОГДА не импортируется (вена C).
- **Classical counterpart.** Constructive reals as Cauchy sequences of rationals (Bishop) are classical constructive analysis; NEW is only the ToS commitment: RealProcess := nat -> Q IS the definition of a real (no Coq Reals, ever), with arithmetic preserving the Cauchy property, 0-axiom.
- **Tags.** cauchy-real, real-process, vein-C, P4, foundation

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `is_cauchy/CauchySeq/cauchy_equiv/refl/sym/trans` | Definition/Lemma | Cauchy-предикат и эквивалентность реалов |
| `cauchy_add/neg/sub/const/add_compat/neg_compat/add_comm/assoc/zero_r/neg_r` | Definition/Lemma | ★ арифметика сохраняет Cauchy, уважает эквивалентность |
| `cauchy_pos/le/le_of_equiv/le_refl/pos_not_zero/rational_approx/complete_self/subsequence` | Definition/Lemma | порядок, рациональное приближение, полнота-к-себе |

**Key lemmas (deep):**

- **`cauchy_add_is_cauchy`** - Поточечная сумма двух Cauchy-процессов снова Cauchy — показывает, что арифметика реалов = арифметика ПРОЦЕССОВ, замкнутая в nat→Q. Element-сторона вены C: реал не вызывается из Coq.Reals, а ЕСТЬ процесс приближений; вся аналитика репо стоит на этом определении (333+ файлов). _(cauchy, real-process, vein-C, arithmetic)_

**Uniqueness - score 3 (new-framing).** ℝ ОПРЕДЕЛЕНО как Cauchy-процесс RealProcess := nat→Q (никогда Coq.Reals); арифметика сохраняет Cauchy — вена C, реал как потенциальная бесконечность-процесс, бутылочное горло 333+ файлов.
> _Caveat:_ Конструктивные реалы = Cauchy-последовательности ≈ Бишоп (~50 лет); уникальность — в систематической онтологической приверженности (ℝ=процесс, P4, отказ от Coq.Reals), не в конструкции.

---

## #85 - `src/CoinductiveSystems.v` - score 2 (new-framing)

**Coinductive systems: observables, no complete observation (P4)**

- **Topic.** Observable with finite-prefix observation, observational equivalence, observable maps preserving equivalence, no_complete_observation / observation_inexhaustibility (every observation is finite), and observables from functions.
- **Role.** Type-theory/systems (coinductive, vein C). Defines Observable. Imports Core_ERR.
- **Counts.** Qed 16 / Admitted 0 / axioms 0
- **Imports.** ToS Core_ERR
- **E/R/R.** _Elements:_ наблюдаемые Observable (потоки); их конечные префиксы. _Roles:_ наблюдение как роль; коиндуктивная неисчерпаемость. _Rules:_ obs_prefix/obs_equiv; no_complete_observation. _P4:_ ★ нет ПОЛНОГО наблюдения потока — каждое наблюдение конечно (observation_inexhaustibility); коиндукция = бесконечность как процесс (вена C).
- **Classical counterpart.** Coinductive/observable streams with finite-prefix observation and bisimulation (observational equivalence) are standard; NEW is only the ToS framing: Observable with no complete observation (observation_inexhaustibility) -- the P4 'infinity is a process' view of streams.
- **Tags.** coinductive, observable, vein-C, P4, new-framing

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `Observable/obs_at/obs_prefix/obs_equiv/refl/sym/trans/obs_map` | Definition/Lemma | наблюдаемые и наблюдательная эквивалентность |
| `no_complete_observation/obs_finite_prefix_exists/observation_inexhaustibility` | Theorem/Lemma | ★ нет полного наблюдения; каждое наблюдение конечно |
| `obs_from_function/obs_constant/obs_map_preserves_equiv` | Definition/Lemma | наблюдаемые из функций; константы |

**Key lemmas (deep):**

- **`observation_inexhaustibility`** - Нет ПОЛНОГО наблюдения коиндуктивного потока — всякое наблюдение конечно (префикс). P4 в коиндукции: бесконечный объект (поток) дан как НЕИСЧЕРПАЕМЫЙ ПРОЦЕСС наблюдений, не как завершённое целое. Вена C на стороне коданных. _(coinductive, observation, inexhaustibility, vein-C)_

**Uniqueness - score 2 (new-framing).** Коиндуктивные системы как неисчерпаемо-наблюдаемые потоки (нет полного наблюдения, каждое конечно) — P4/вена C на стороне коданных.
> _Caveat:_ Коиндукция/бисимуляция стандартны; вклад — P4-обрамление неисчерпаемости наблюдения, не новая коиндукция.

---

## #86 - `src/Completeness.v` - score 3 (new-framing)

**Completeness over Q: sup via bisection, nested-interval limit, meta-Cauchy diagonal**

- **Topic.** Monotone endpoints Cauchy, nested-interval limits, a sup-bisection state machine (sup_bisect_iter) building the supremum as a Cauchy process, and a meta-Cauchy diagonal converging when each row is Cauchy.
- **Role.** Calculus chain (completeness). Self-contained.
- **Counts.** Qed 24 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; CauchyReal
- **E/R/R.** _Elements:_ вложенные интервалы; sup-бисекционная машина; мета-Cauchy диагональ. _Roles:_ полнота как роль (sup существует как процесс); бисекция строит sup. _Rules:_ sup_bisect_iter сужает к sup; диагональ Cauchy при построчной Cauchy. _P4:_ полнота КОНСТРУКТИВНО: sup ЕСТЬ Cauchy-процесс бисекции (не аксиома полноты ℝ); вена C.
- **Classical counterpart.** The completeness of the reals (monotone-bounded converges; sup via bisection; nested intervals) is classical; NEW is only the constructive form: a sup-bisection state machine producing the supremum as a Cauchy process, plus a meta-Cauchy diagonal -- completeness as a process, no real-line axiom.
- **Tags.** completeness, sup-bisection, nested-intervals, vein-C, new-framing

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `increasing_mono/left_right_endpoints_cauchy/endpoints_equiv/nested_interval_limit` | Lemma | вложенные интервалы сходятся |
| `SupBisectState/sup_bisect_step/iter/valid/preserves_P/width_to_zero/cauchy` | Definition/Lemma | ★ sup-бисекция строит супремум как Cauchy-процесс |
| `meta_cauchy/diagonal_is_cauchy/diagonal_limit/diagonal_converges/meta_cauchy_each_cauchy` | Definition/Lemma | ★ мета-Cauchy диагональ сходится |

**Key lemmas (deep):**

- **`sup_bisect_cauchy`** - Супремум строится sup-бисекционной машиной как Cauchy-ПРОЦЕСС (а не постулируется аксиомой полноты ℝ). Element-сторона вены C: completeness = конструктивный процесс сужения интервалов, держащий предикат P. ℝ полно ПОТОМУ ЧТО процессы сходятся, не по аксиоме. _(completeness, sup-bisection, vein-C, process)_

**Uniqueness - score 3 (new-framing).** Полнота над Q конструктивно: sup как Cauchy-процесс бисекции + мета-Cauchy диагональ — completeness как процесс, без аксиомы полноты ℝ (вена C).
> _Caveat:_ Полнота через вложенные интервалы/бисекцию стандартна (Бишоп); вклад — процессное Q-исполнение, не новая теорема.

---

## #87 - `src/ConstitutionChecking.v` - score 2 (methods)

**Constitution checking: decidable combinators, L5 resolve on decidable**

- **Topic.** Decidable conjunction/disjunction/negation/implication/iff, nat/Q decidable constitutions, decidable systems being well-formed, L5 resolve on decidable, and sound/complete decidable filtering.
- **Role.** Type-theory/decidability (constitution checking). Imports L5Resolution. Self-contained.
- **Counts.** Qed 16 / Admitted 0 / axioms 0
- **Imports.** ToS L5Resolution
- **E/R/R.** _Elements:_ разрешимые конституции (предикаты); комбинаторы. _Roles:_ конституция как разрешимая роль; L5-резолв на разрешимом. _Rules:_ dec_conjunction/disjunction/...; l5_resolve_on_decidable; dec_filter sound/complete. _P4:_ конституция системы РАЗРЕШИМА (Element): комбинаторы сохраняют разрешимость; L5-резолв и фильтр вычислимы.
- **Classical counterpart.** Decidable propositional combinators (conjunction/disjunction/negation/implication) and decidable filtering are standard; NEW: nothing -- the ToS constitution checker (decidable systems, L5 resolve on decidable, decidable filters).
- **Tags.** constitution, decidable, L5, filter, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `dec_conjunction/disjunction/negation/implies_bool/dec_true/false_trivial` | Definition/Lemma | разрешимые комбинаторы |
| `decidable_system/well_formed/l5_resolve_on_decidable/dec_filter/sound/complete/dec_iff` | Lemma | ★ разрешимая система well-formed; фильтр sound/complete |

**Key lemmas (deep):**

- **`decidable_system_well_formed`** - Разрешимая конституция даёт well-formed систему, и L5-резолв на ней вычислим (dec_filter sound+complete). Element-сторона: когда критерий разрешим, вся E/R/R-структура (резолв ролей, фильтрация) становится алгоритмической — прямая связь с веной A (разрешимость = Element). _(constitution, decidable, L5)_

**Uniqueness - score 2 (methods).** Проверка конституций: разрешимые комбинаторы + L5-резолв на разрешимом + sound/complete фильтр — алгоритмическая E/R/R при разрешимом критерии.
> _Caveat:_ Разрешимые комбинаторы стандартны; вклад — связка с L5/well-formedness (вена A: разрешимость=Element).

---

## #88 - `src/Conversion.v` - score 3 (new-framing)

**Conversion: beta/eta for Pi/Sigma, convertibility, P3 not extensional**

- **Topic.** P3 convertibility (an equivalence), beta/eta laws for Pi and Sigma (surjective pairing), convertible systems share elements, P3 is not extensional, and deterministic L5 resolution preserves convertibility.
- **Role.** Type-theory core (conversion). Self-contained / Core_ERR.
- **Counts.** Qed 16 / Admitted 0 / axioms 0
- **Imports.** ToS Core_ERR
- **E/R/R.** _Elements:_ системы и их преобразования (beta/eta). _Roles:_ конвертируемость как роль-эквивалентность; P3 как интенсиональный критерий. _Rules:_ beta/eta для Pi/Sigma; surjective pairing; L5-резолв детерминирован. _P4:_ конвертируемые системы делят элементы, но P3 НЕ экстенсионален — конвертируемость уважает интенсиональную идентичность.
- **Classical counterpart.** Beta/eta conversion for Pi/Sigma and convertibility as an equivalence are standard type theory; NEW is only the P3 angle: convertible systems share elements yet P3 is NOT extensional, with deterministic L5 resolution.
- **Tags.** conversion, type-theory, beta-eta, P3, new-framing

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `P3_convertible/refl/sym/trans/P3_not_extensional/convertible_same_elements/conversion_chain` | Definition/Lemma | ★ конвертируемость = эквивалентность; не экстенсиональна |
| `beta_pi/eta_pi/beta_sigma_fst/snd/sigma_surjective_pairing` | Lemma | beta/eta для Pi/Sigma, surjective pairing |
| `l5_resolve_deterministic/system_eq_criterion/P3_convertible_element_transfer/same_level/beta_eta_pi_coherence` | Lemma | L5 детерминирован; перенос элементов; когерентность |

**Key lemmas (deep):**

- **`P3_not_extensional`** - Конвертируемость уважает P3-интенсиональность: конвертируемые системы делят элементы, НО P3 не экстенсионален — два конвертируемых выражения могут иметь разный критерий. Связывает редукцию (beta/eta) с интенсиональной онтологией IntensionalIdentity. _(conversion, P3, intensional, beta-eta)_

**Uniqueness - score 3 (new-framing).** Конвертируемость (beta/eta для Pi/Sigma) совмещена с P3-интенсиональностью: конвертируемые системы делят элементы, но P3 не экстенсионален; L5-резолв детерминирован.
> _Caveat:_ Beta/eta-конверсия — стандартная теория типов; вклад — стыковка с интенсиональной P3-идентичностью, не новая редукция.

---

## #89 - `src/CoordinateIntegers.v` - score 1 (exposition)

**Integers as formal differences of naturals (Grothendieck construction)**

- **Topic.** FormalDiff (pairs of nats), the equivalence a-b=c-d, conversion to/from Z, addition/negation/multiplication matching Z, the sign rule, and basic laws.
- **Role.** Number foundation (Z from N). Self-contained.
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** Stdlib: ZArith
- **E/R/R.** _Elements:_ формальные разности FormalDiff (пары nat); их классы. _Roles:_ Z как фактор пар nat (конструкция Гротендика). _Rules:_ fd_equiv = (a−b=c−d); add/opp/mul соответствуют Z. _P4:_ Z построено из N как фактор пар (Element); арифметика уважает классы — Z как процесс/конструкция, не примитив.
- **Classical counterpart.** The Grothendieck/formal-difference construction of Z from N (pairs up to a-b=c-d) with well-defined arithmetic is classical; NEW: nothing -- FormalDiff (Z as N-pairs) with add/opp/mul matching Z and the sign rule.
- **Tags.** integers, grothendieck, formal-difference, exposition

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `FormalDiff/fd_to_Z/fd_equiv/refl/sym/trans/fd_equiv_iff_Z/fd_of_Z` | Definition/Lemma | формальные разности и их классы |
| `fd_add/to_Z/fd_opp/fd_mul/to_Z/fd_sign_rule/add_comm/opp_involutive` | Definition/Lemma | ★ арифметика соответствует Z; правило знаков |

**Key lemmas (deep):**

- **`fd_mul_to_Z`** - Умножение формальных разностей соответствует умножению в Z — конструкция Гротендика Z из N как фактор пар (a−b). Element-сторона: целые построены, не примитивны; арифметика уважает классы эквивалентности. _(grothendieck, integers-from-naturals, well-defined)_

**Uniqueness - score 1 (exposition).** Z как формальные разности натуральных (конструкция Гротендика, арифметика соответствует Z, правило знаков).
> _Caveat:_ Конструкция Z из N классична (Гротендик); ценность — конструктивная реализация, не новый результат.

---

## #94 - `src/Countability_Q.v` - score 3 (new-framing)

**Q is countable via the Calkin-Wilf tree (explicit bijection)**

- **Topic.** The Calkin-Wilf tree (left/right children, coprime nodes), an enumeration of Q+ that hits each positive rational exactly once in lowest terms, injectivity/surjectivity, the index_of_Q inverse, and the full Q bijection (interleaving positives/negatives/zero).
- **Role.** Countability flagship (vein E counterpart). Provides Q_countable/Q_bijection. Self-contained.
- **Counts.** Qed 33 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ положительные рациональные QPos; узлы дерева Калкина-Вилфа. _Roles:_ счётность Q как ПРАВИЛО-биекция (дерево попадает в каждое q ровно раз). _Rules:_ cw_node coprime; enum_QPos сюръективно/инъективно; index_of_Q обратно. _P4:_ счётность Q аксиомо-свободно через ЯВНУЮ биекцию (дерево Калкина-Вилфа); счёт = правило-перечисление, каждое q — конечные данные (несократимая пара).
- **Classical counterpart.** The countability of Q is classical; NEW is only the explicit Calkin-Wilf construction: a bijection nat <-> Q+ via the Calkin-Wilf tree (each positive rational appears exactly once in lowest terms), extended to all of Q, axiom-free.
- **Tags.** countability, calkin-wilf, bijection, rationals, new-framing

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `QPos/cw_left/right/root/cw_node/enum_QPos/index_of_QPos` | Definition | дерево Калкина-Вилфа и перечисление |
| `cw_node_coprime/cw_left/right_injective/cw_node_injective/enum_injective` | Lemma | ★ узлы несократимы и инъективны |
| `enum_surjective/Q_positive_countable/cw_node_path_roundtrip/index_of_QPos_enum` | Lemma | ★ перечисление сюръективно (каждое q+ ровно раз) |
| `enum_Q/Q_countable/Q_bijection/index_of_Q/enum_Q_index_id/Qred_coprime` | Definition/Lemma | ★ полная биекция nat ↔ Q |

**Key lemmas (deep):**

- **`Q_bijection`** - Полная биекция nat ↔ Q через дерево Калкина-Вилфа: каждое положительное рациональное появляется РОВНО РАЗ в несократимом виде (cw_node_coprime + enum_surjective), затем интерливинг с отрицательными/нулём. Аксиомо-свободно, с явной обратной index_of_Q. Element-сторона счётности (контраст с несчётностью ShrinkingIntervals). _(countability, calkin-wilf, bijection, explicit)_

**Uniqueness - score 3 (new-framing).** Q счётно через ЯВНУЮ биекцию nat ↔ Q (дерево Калкина-Вилфа: каждое q+ ровно раз несократимо), аксиомо-свободно, с явной обратной — Element-сторона, парная к несчётности ℝ.
> _Caveat:_ Счётность Q классична; вклад — явная аксиомо-свободная Калкин-Вилф биекция (а не абстрактная), парная к несчётности по той же оси Element/role-limit.

---

## #122 - `src/Demo.v` - score 0 (infrastructure)

**Demo file (examples, 0 Qed)**

- **Topic.** A demonstration file showcasing the framework; no proved theorems.
- **Role.** Demonstration/exposition. 0 Qed.
- **Counts.** Qed 0 / Admitted 0 / axioms 0
- **Imports.** ToS (various)
- **E/R/R.** _Elements:_ демонстрационные примеры. _Roles:_ демо как роль экспозиции. _Rules:_ иллюстрация фреймворка. _P4:_ только демонстрация; 0 теорем.
- **Classical counterpart.** A demonstration/example file is exposition; NEW: nothing -- a demo file (0 Qed).
- **Tags.** demo, exposition, infrastructure

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `(demonstration only)` | Demo | иллюстрация, без доказанных теорем |

**Key lemmas (deep):**


**Uniqueness - score 0 (infrastructure).** Демонстрационный файл (0 теорем).
> _Caveat:_ Экспозиция/демо; не содержит результатов.

---

## #123 - `src/DependentSystems.v` - score 2 (methods)

**Dependent systems: Pi and Sigma as ToS systems**

- **Topic.** PiSystem with extensionality and application typing, SigmaElem with eta and pair injectivity, non-dependent Pi as a map, level preservation for Pi/Sigma projections, and respect for equivalence.
- **Role.** Type-theory/systems (dependent types). Defines PiSystem/SigmaElem. Imports Core_ERR.
- **Counts.** Qed 25 / Admitted 0 / axioms 0
- **Imports.** ToS Core_ERR
- **E/R/R.** _Elements:_ Pi-системы (зависимые функции); Sigma-элементы (зависимые пары). _Roles:_ Pi/Sigma как роли зависимых конструкций; уровень сохраняется. _Rules:_ pi_extensionality; sigma_eta/surjective pairing; level preservation. _P4:_ зависимые системы конечно-структурны; проекции сохраняют уровень — типовая дисциплина.
- **Classical counterpart.** Pi (dependent function) and Sigma (dependent pair) types with eta/surjective-pairing and level preservation are standard dependent type theory; NEW is only the ToS framing: PiSystem/SigmaElem as systems with extensionality and level-preservation, P-graded.
- **Tags.** dependent-types, pi-system, sigma, type-theory, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `PiSystem/pi_eq/pi_app_well_typed/pi_extensionality/pi_compose/pi_const_preserves_level` | Definition/Lemma | ★ Pi-системы (экстенсиональность, уровень) |
| `SigmaElem/sigma_eq/sigma_eta/pair_injective/fst_snd_preserves_level/sigma_projections_roundtrip` | Definition/Lemma | ★ Sigma-элементы (eta, проекции) |
| `fiber_equiv/pi_respects_equiv/sigma_respects_equiv/nat_pi_example/nat_sigma_example` | Lemma | уважение эквивалентности; примеры nat |

**Key lemmas (deep):**

- **`pi_extensionality`** - Pi-системы экстенсиональны (равны при поточечно равных действиях) и сохраняют уровень — формализует зависимые функции как ToS-системы. Element-сторона: Pi/Sigma встроены в уровневую дисциплину, проекции не нарушают иерархию. _(pi-system, dependent-types, extensionality)_

**Uniqueness - score 2 (methods).** Зависимые типы Pi/Sigma как ToS-системы (экстенсиональность, eta, сохранение уровня).
> _Caveat:_ Pi/Sigma — стандартная зависимая теория типов; вклад — встраивание в уровневую E/R/R-дисциплину.

---

## #124 - `src/DiagonalArgument_ERR.v` - score 2 (methods)

**Ternary digit-diagonal uncountability (superseded by ShrinkingIntervals)**

- **Topic.** Ternary expansions over Q, digit extraction, the ternary-flip diagonal differing structurally from each enumerated real, and uncountability -- the original digit approach later replaced by trisection intervals.
- **Role.** Uncountability (digit form, deprecated path). Self-contained. Decision-log 2026-01-18: superseded by ShrinkingIntervals.
- **Counts.** Qed 41 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ троичные разложения над Q; цифры; диагональ ternary_flip. _Roles:_ несчётность через цифровую диагональ (исторический путь). _Rules:_ ternary_flip отличает диагональ от каждого E_n по цифре. _P4:_ несчётность через цифры; ЗАМЕНЁН трисекцией (ShrinkingIntervals) из-за нестабильности Qfloor над Q.
- **Classical counterpart.** Cantor's diagonal on ternary digit expansions is classical; NEW: nothing -- a digit-based uncountability attempt SUPERSEDED by ShrinkingIntervals (the Qfloor digit instability over Q is why the interval/trisection form was adopted).
- **Tags.** uncountability, diagonal, ternary, superseded, methods
- **Notes.** Superseded by ShrinkingIntervals_ERR (trisection) per Decision Log 2026-01-18 (Qfloor digit instability over Q).

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `pow3/Qpow3/TernaryExp/digit_bounds/partial_sum/to_Q/tail_bound` | Definition/Lemma | троичные разложения и хвостовые оценки |
| `Qfloor/extract_digit/ternary_flip/flip_valid/flip_differs/flip_diff_ge_1` | Definition/Lemma | ★ извлечение цифр и flip-диагональ |
| `diagonal/diagonal_in_unit/diagonal_differs_structurally/diagonal_is_Cauchy/archimedean_pow3` | Definition/Lemma | ★ диагональ Cauchy, структурно отличается от E_n |

**Key lemmas (deep):**

- **`diagonal_differs_structurally`** - Цифровая диагональ отличается от каждого перечисленного реала структурно (по троичной цифре). Работает, но ИСТОРИЧЕСКИ ЗАМЕНЁН трисекционной формой (ShrinkingIntervals) — Qfloor разрывен над Q, что делало digit-стабильность хрупкой. Документирует дизайн-решение проекта (decision-log). _(diagonal, ternary-digits, superseded)_

**Uniqueness - score 2 (methods).** Несчётность через троичную цифровую диагональ над Q — рабочий, но замещённый путь (трисекция надёжнее из-за нестабильности Qfloor).
> _Caveat:_ Диагональ Кантора классична; СУПЕРСЕДЕД ShrinkingIntervals (decision-log 2026-01-18). Ценность — исторический контекст дизайн-решения.

---

## #125 - `src/Differentiation.v` - score 2 (methods)

**Differentiation over Q: rules, diff=>continuous, first-derivative test**

- **Topic.** has_derivative and continuous_at, differentiation rules (const/id/scale/neg/sum/product/power), differentiability implies continuity, derivative uniqueness, the first-derivative test, and the gradient-step connection.
- **Role.** Calculus chain (differentiation). Self-contained.
- **Counts.** Qed 18 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ функции Q→Q и производные has_derivative. _Roles:_ производная как роль локальной линеаризации; first-derivative test. _Rules:_ правила дифференцирования; diff ⟹ continuous; local_min ⟹ deriv=0. _P4:_ производная определена эпсилон-конструктивно над Q (Element); локальный минимум ⟹ нулевая производная (основа GradientDescent).
- **Classical counterpart.** The derivative, differentiation rules (constant/identity/scale/sum/product/power), differentiability implies continuity, and the first-derivative test (local min => zero derivative) are classical; NEW is only the constructive Q form (has_derivative with explicit bounds).
- **Tags.** differentiation, calculus, first-derivative-test, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `has_derivative/continuous_at/local_min/deriv_const/id/scale/neg/sum/sub` | Definition/Lemma | производная и базовые правила |
| `deriv_implies_continuous/deriv_square/product/power_succ/deriv_unique/affine` | Lemma | ★ дифференцируемость ⟹ непрерывность; правила произведения/степени |
| `local_min_zero_deriv/quadratic_loss_derivative/gradient_step_uses_derivative` | Lemma | ★ first-derivative test; связь с градиентным шагом |

**Key lemmas (deep):**

- **`local_min_zero_deriv`** - Тест первой производной: локальный минимум ⟹ производная = 0, конструктивно над Q. Element-сторона: оптимизация (GradientDescent) опирается на это; производная — эпсилон-локальная линеаризация, не вещественный предел. _(derivative, first-derivative-test, optimization)_

**Uniqueness - score 2 (methods).** Дифференцирование над Q (правила, diff⟹continuous, тест первой производной) эпсилон-конструктивно.
> _Caveat:_ Правила дифференцирования классичны; вклад — конструктивное Q-исполнение, основа оптимизации.

---

## #126 - `src/DomainTypes.v` - score 2 (new-framing)

**Domain types: the D1-D6 reasoning-pipeline schema**

- **Topic.** The E/R/R element/role/rule/status tags (decidable), the D1-D6 domain output records, gates and verdicts, the ASK and REFLECT outputs, the pipeline execution record, and well-formedness predicates.
- **Role.** Reasoning-architecture pipeline schema (data types). Self-contained. Underlies DomainValidation.
- **Counts.** Qed 20 / Admitted 0 / axioms 0
- **Imports.** Stdlib
- **E/R/R.** _Elements:_ типы данных конвейера рассуждения (D1-D6, gates, ASK/REFLECT). _Roles:_ схема конвейера как роль; теги E/R/R разрешимы. _Rules:_ записи D1-D6; gate_well_formed; pipeline_well_formed. _P4:_ схема конвейера рассуждения конечно-структурна (Element); теги E/R/R разрешимы.
- **Classical counterpart.** Data types for a structured reasoning pipeline (domains D1-D6, gates, ASK/REFLECT outputs, decidable tags) are domain modelling; NEW is only the ToS reasoning-pipeline schema (the D1-D6 + gates + ASK/REFLECT record types), 0 axioms.
- **Tags.** reasoning-pipeline, domain-types, schema, well-formedness, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `ERR_Element/Role/Rule/Status/D1..D6_Output/GateVerdict/ASK/REFLECT records` | Definition | типы данных конвейера D1-D6 |
| `elemlevel_eq_dec/roletag_eq_dec/.../gate_well_formed/reflect_well_formed/pipeline_well_formed` | Lemma | ★ разрешимое равенство тегов; well-formedness конвейера |

**Key lemmas (deep):**

- **`pipeline_well_formed`** - Well-formedness конвейера рассуждения (все D1-D6, gates, ASK, REFLECT присутствуют и согласованы) как разрешимый предикат над схемой. Element-сторона ветви Architecture_of_Reasoning: структура рассуждения формализована как проверяемая запись. _(pipeline, well-formedness, reasoning-schema)_

**Uniqueness - score 2 (new-framing).** Схема конвейера рассуждения D1-D6 (gates/ASK/REFLECT) как разрешимые типы данных + well-formedness — формализация структуры рассуждения (Architecture_of_Reasoning).
> _Caveat:_ Моделирование данных стандартно; ново — формализация конкретной D1-D6 методологии рассуждения, не новая теория.

---

## #127 - `src/DomainValidation.v` - score 2 (new-framing)

**Domain validation: the cumulative D1->D6 pipeline checks**

- **Topic.** Boolean validators for D1-D6, the cumulative implications (D2=>D1, ..., D5=>D4), gate passing, ASK/REFLECT validation, pipeline implies ASK/gates/REFLECT, and lemmas catching empty elements / no challenge / no chain.
- **Role.** Reasoning-architecture pipeline validation. Imports DomainTypes. Self-contained.
- **Counts.** Qed 32 / Admitted 0 / axioms 0
- **Imports.** ToS DomainTypes
- **E/R/R.** _Elements:_ валидаторы D1-D6; gates; цепь. _Roles:_ валидация как роль (каждый этап требует предыдущего); ловля ошибок. _Rules:_ validate_d2_implies_d1...d5_implies_d4; pipeline_implies_ask/gates/reflect. _P4:_ валидация конвейера КУМУЛЯТИВНА и разрешима (Element): каждый этап требует предыдущего; ошибки (пустые элементы/нет цепи) ловятся.
- **Classical counterpart.** Validating a staged pipeline (each stage requires the previous; gates; catches missing fields) is domain logic; NEW is only the ToS reasoning-pipeline validation: D2 requires D1, ..., D6 requires D5, gates, and the cumulative pipeline validity, with caught-error lemmas.
- **Tags.** reasoning-pipeline, validation, cumulative, new-framing

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `validate_d1..d5_bool/gate/ask/reflect/pipeline_bool` | Definition | булевы валидаторы этапов |
| `validate_d2_implies_d1/d3_implies_d2/d4_implies_d3/d5_implies_d4/gate_pass_all_four/validation_cumulative` | Lemma | ★ кумулятивная валидация (этап требует предыдущего) |
| `pipeline_implies_ask/gates/reflect/controls/catches_empty_elements/no_challenge/no_chain` | Lemma | ★ конвейер ⟹ ASK/gates/REFLECT; ловля ошибок |

**Key lemmas (deep):**

- **`validation_cumulative`** - Валидация конвейера рассуждения КУМУЛЯТИВНА: D5⟹D4⟹...⟹D1, плюс gates/ASK/REFLECT — каждый этап требует корректности предыдущего. catches_* ловят конкретные дефекты (пустые элементы, нет вызова, нет цепи). Element-сторона: методология рассуждения как проверяемый разрешимый протокол. _(validation, cumulative, pipeline)_

**Uniqueness - score 2 (new-framing).** Кумулятивная валидация конвейера рассуждения D1->D6 (каждый этап требует предыдущего, gates, ловля дефектов) — методология рассуждения как разрешимый протокол.
> _Caveat:_ Валидация пайплайна — обычная доменная логика; ново — формализация конкретной D1-D6 методологии (Architecture_of_Reasoning).

---

## #130 - `src/ErasureTheory.v` - score 2 (new-framing)

**Erasure theory: E/R/R relevance (Elements/Rules runtime, Roles compile-only)**

- **Topic.** A relevance annotation (runtime/compile), the default E/R/R relevance (elements/rules runtime, roles compile-only), erase, erasure preserving runtime and removing compile-only, idempotence, and a length bound.
- **Role.** Type-theory (erasure/extraction). Imports Core_ERR.
- **Counts.** Qed 16 / Admitted 0 / axioms 0
- **Imports.** ToS Core_ERR
- **E/R/R.** _Elements:_ аннотированные компоненты; релевантность (runtime/compile). _Roles:_ ★ Элементы/Правила = runtime, Роли = compile-only (E/R/R erasure). _Rules:_ erase удаляет compile-only, сохраняет runtime; идемпотентна. _P4:_ стирание сохраняет поведение (runtime), убирает только compile-only Роли — E/R/R-релевантность как дисциплина извлечения.
- **Classical counterpart.** Erasure of compile-time-only (irrelevant) annotations preserving runtime behaviour, idempotent, is standard in dependently-typed/irrelevance settings; NEW is only the E/R/R relevance assignment: Elements/Rules are runtime, Roles compile-only, erasure preserves runtime.
- **Tags.** erasure, relevance, ERR, extraction, new-framing
- **Notes.** PowerShell flagged Adm=1 but it is a comment mention; actual Admitted = 0.

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `Relevance/relevance_dec/AnnotatedComponent/default_relevance/is_runtime/erase` | Definition | релевантность и стирание |
| `elements_always_runtime/roles_always_compile/rules_always_runtime/erasure_preserves_runtime` | Lemma | ★ E/R/R-релевантность: Роли стираемы, Элементы/Правила — нет |
| `erasure_removes_compile_only/idempotent/runtime_subset_of_full/default_role_erased` | Lemma | стирание идемпотентно, убирает Роли |

**Key lemmas (deep):**

- **`erasure_preserves_runtime`** - Стирание сохраняет runtime-поведение, убирая compile-only компоненты — с E/R/R-релевантностью: Элементы и Правила runtime, РОЛИ compile-only (стираемы). Element-сторона извлечения: Роли (WHY) не нужны во время выполнения, в отличие от Элементов (WHAT) и Правил (HOW). Связь с extraction/Regulus. _(erasure, relevance, ERR, extraction)_

**Uniqueness - score 2 (new-framing).** Теория стирания с E/R/R-релевантностью: Элементы/Правила runtime, Роли compile-only (стираемы), стирание идемпотентно сохраняет поведение.
> _Caveat:_ Стирание нерелевантного стандартно; ново — привязка релевантности к триаде E/R/R (Роли стираемы). Слово 'Admitted' в комментарии (0 реальных).

---

## #131 - `src/ERR_Categorical.v` - score 3 (new-framing)

**ERR categorically: the Elements functor, P3 strictly stronger than iso**

- **Topic.** Elements as objects, morphisms as structure-preserving, P3_eq implies iso but iso does NOT imply P3, the faithful ElementsFunctor preserving/reflecting iso, the categorical P3-separation, and the err decomposition.
- **Role.** Category-of-systems core (P3 categorical separation). Imports Core_ERR/SystemCategory.
- **Counts.** Qed 24 / Admitted 0 / axioms 0
- **Imports.** ToS Core_ERR, SystemCategory
- **E/R/R.** _Elements:_ элементы как объекты; морфизмы, сохраняющие структуру. _Roles:_ ElementsFunctor как роль-вложение; P3-сепарация категориально. _Rules:_ P3_eq ⟹ iso, но iso ⇏ P3 (P3 строго сильнее). _P4:_ P3 строго сильнее изоморфизма — категориальное выражение интенсиональности: одинаковая структура (iso) не делает системы P3-равными.
- **Classical counterpart.** The category of elements / a faithful forgetful functor and iso-implies-equal-up-to-iso are standard category theory; NEW is only the P3 separation as a categorical statement: iso does NOT imply P3-equality (the Elements functor is faithful but P3 is strictly stronger than iso).
- **Tags.** category, P3, elements-functor, separation, new-framing

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `elements_are_objects/morphisms_are_structure_preserving/P3_eq_implies_iso/iso_implies_predicate_equiv/P3_strictly_stronger_than_iso` | Lemma | ★ P3 строго сильнее изоморфизма |
| `ElementsFunctor/_obj/_mor/_faithful/_preserves_iso/iso_not_implies_P3/P3_separation_categorical` | Definition/Lemma | ★ верный Elements-функтор; категориальная P3-сепарация |
| `embed_preserves_criterion*/embed_preserves_iso_categorical/reflects_iso/preserves_initial/err_decomposition` | Lemma | вложение сохраняет/отражает критерий и изо; E/R/R-декомпозиция |

**Key lemmas (deep):**

- **`P3_separation_categorical`** - P3-сепарация как категориальное утверждение: изоморфизм систем НЕ влечёт P3-равенства (P3 строго сильнее iso), хотя ElementsFunctor верен. Категориальная форма интенсиональности IntensionalIdentity — одинаковая структура не есть тождество критерия. _(P3, categorical, faithful-functor, separation)_

**Uniqueness - score 3 (new-framing).** Категориальная P3-сепарация: P3 строго сильнее изоморфизма (iso ⇏ P3), верный ElementsFunctor — интенсиональность ToS на языке теории категорий.
> _Caveat:_ Категория элементов и верные функторы стандартны; вклад — постановка P3-интенсиональности как категориальной сепарации, не новая категорная теорема.

---

## #134 - `src/Evaluator.v` - score 2 (methods)

**Safe evaluator: type-check then evaluate, verified end-to-end**

- **Topic.** safe_eval (typecheck then eval), result classification (value/partial/error), soundness, safety, determinism, the verified_pipeline (typecheck => preservation + progress), and the annotated safe_eval_ann.
- **Role.** Type-theory (verified evaluation pipeline). Combines TypeChecker + Reduction. Imports both. June 2026 wave-4 tail: safe_eval_terminates -> None-or-Some dichotomy; verified_pipeline_terminates -> valuehood decidability (both were vacuous exists r, _ = r).
- **Counts.** Qed 20 / Admitted 0 / axioms 0
- **Imports.** ToS TypeChecker, Reduction
- **E/R/R.** _Elements:_ safe_eval (проверка+вычисление); классификация результата. _Roles:_ верифицированный конвейер как роль (проверка ⟹ безопасное вычисление). _Rules:_ safe_eval_sound/safe; verified_pipeline; classify (value/partial/error). _P4:_ проверка типа ⟹ безопасное финитное вычисление (Element): verified_pipeline даёт preservation+progress end-to-end.
- **Classical counterpart.** A safe evaluator that type-checks then evaluates, sound and progress-respecting, is the standard 'verified pipeline'; NEW: nothing -- safe_eval combining the ToS checker and fuel evaluator with end-to-end soundness.
- **Tags.** evaluator, verified-pipeline, safe-eval, type-theory, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `safe_eval/typecheck_and_eval/classify_eval/safe_eval_sound/safe/terminates/deterministic` | Definition/Lemma | ★ безопасный вычислитель (sound, финитен) |
| `verified_pipeline/terminates/deterministic/typecheck_implies_progress/type_safety` | Lemma | ★ верифицированный конвейер (проверка ⟹ progress+preservation) |
| `safe_eval_ann/sound/safe/multi_step_type_preservation` | Lemma | аннотированный safe_eval |

**Key lemmas (deep):**

- **`verified_pipeline`** - Верифицированный конвейер: typecheck OK ⟹ eval сохраняет тип и прогрессирует (preservation+progress end-to-end). Element-сторона: проверка типа ГАРАНТИРУЕТ безопасное финитное вычисление; safe_eval классифицирует результат (value/partial/error). Мост к AIInterface (безопасная генерация). _(verified-pipeline, safe-eval, end-to-end)_

**Uniqueness - score 2 (methods).** Безопасный вычислитель ToS-языка (typecheck+eval, sound, верифицированный конвейер с preservation+progress end-to-end).
> _Caveat:_ Verified evaluation pipeline стандартен; вклад — ToS-инстанс, основа безопасной AI-генерации.

---

## #135 - `src/EVT_ERR.v` - score 2 (methods)

**EVT by grid argmax-by-VALUE (superseded by EVT_idx)**

- **Topic.** Grid maximization by max-of-values (max_list/argmax_on_grid), the sup process, and EVT_complete -- the value-based approach later replaced by index-based argmax to avoid Qeq.
- **Role.** EVT (value-based, deprecated path). Decision-log 2026-01-18: superseded by EVT_idx. Self-contained.
- **Counts.** Qed 35 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; CauchyReal
- **E/R/R.** _Elements:_ сетка; максимум по ЗНАЧЕНИЮ (Q). _Roles:_ argmax по значению как роль (исторический путь). _Rules:_ max_list/argmax_on_grid; sup_process. _P4:_ EVT по значению; ЗАМЕНЁН argmax-by-index из-за Qeq-vs-Leibniz (== не рефлексивно для выбора).
- **Classical counterpart.** The extreme value theorem approximated on a grid is classical; NEW: nothing -- a value-based argmax version SUPERSEDED by EVT_idx (the Qeq-vs-Leibniz obstruction is why argmax-by-index was adopted).
- **Tags.** EVT, argmax-by-value, superseded, methods
- **Notes.** Superseded by EVT_idx (argmax-by-index) per Decision Log 2026-01-18 (Qeq vs Leibniz).

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `grid_point/grid_list/argmax_list/argmax_on_grid/max_list/max_on_grid/sup_process` | Definition | сетка и argmax по значению |
| `argmax_is_max/max_list_attained/attained_classical/max_on_grid_attained/f_bounded_by_grid_max` | Lemma | ★ максимум сетки достигается (по значению) |
| `sup_process_is_Cauchy/EVT_complete` | Lemma/Theorem | ★ EVT по значению (sup Cauchy) |

**Key lemmas (deep):**

- **`EVT_complete`** - EVT через argmax по ЗНАЧЕНИЮ — работает, но ИСТОРИЧЕСКИ ЗАМЕНЁН индексной формой (EVT_idx): Qeq (==) не рефлексивно по Leibniz, что затрудняло выбор максимума по значению. Документирует дизайн-решение «ищи позицию, не значение» (decision-log). _(EVT, argmax-by-value, superseded)_

**Uniqueness - score 2 (methods).** EVT через argmax по значению над Q — рабочий, но замещённый путь (индексный надёжнее из-за Qeq-vs-Leibniz).
> _Caveat:_ EVT-аппроксимация стандартна; СУПЕРСЕДЕД EVT_idx (decision-log 2026-01-18). Ценность — контекст дизайн-решения вены B.

---

## #136 - `src/EVT_idx.v` - score 4 (synthesis+observation)

**EVT by argmax-by-INDEX: deterministic max selection dodging Qeq (vein B)**

- **Topic.** A grid over [a,b], find_max_idx (argmax by nat index, not Q value), proven to maximize and within bound, the sup process Cauchy, x_between_grid_points (classic only here), and EVT_strong_process -- the grid maximizer as a process.
- **Role.** Vein B FLAGSHIP (argmax-by-index, 0-axiom core). Defines grid_point/argmax_idx. The Qeq-vs-Leibniz avoidance. classic only in x_between_grid_points.
- **Counts.** Qed 26 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; CauchyReal
- **E/R/R.** _Elements:_ сетка grid_point над [a,b]; индексы (nat) максимума. _Roles:_ argmax-по-ИНДЕКСУ как роль селекции (позиция, не значение); sup как процесс. _Rules:_ find_max_idx ищет ПОЗИЦИЮ max (nat) ⟹ выбор по Leibniz-reflexivity, минуя Qeq. _P4:_ ★ выбор максимума ДЕТЕРМИНИРОВАН по индексу (nat), не по значению (Q): «ищи позицию, не значение» обходит Qeq-vs-Leibniz препятствие — селекция правилом без AC (вена B); classic нужен лишь в x_between_grid_points.
- **Classical counterpart.** The extreme value theorem (a continuous function on a compact attains its max) is classical and over Q must be approximated; NEW is the argmax-BY-INDEX device: seek the POSITION of the grid-max (a nat) not its value (a Q), so the max is selected by Leibniz-equality reflexivity, dodging the Qeq-vs-Leibniz obstruction -- a deterministic no-AC selection (vein B).
- **Tags.** EVT, argmax-by-index, vein-B, deterministic, qeq-avoidance, flagship

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `grid_point/grid_list/uniformly_continuous_on/find_max_idx_acc/argmax_idx/max_on_grid/sup_process` | Definition | ★ сетка и argmax по индексу |
| `find_max_idx_acc_invariant/bound/argmax_idx_bound/maximizes/max_on_grid_attained/grid_value_le_max` | Lemma | ★ argmax-индекс достигает максимума сетки |
| `grid_point_in_interval/n_is_b/pow2_unbounded/Archimedean_nat/sup_process_is_Cauchy/argmax_process/max_is_f_of_argmax` | Lemma | сетка в интервале; sup-процесс Cauchy |
| `x_between_grid_points/near_grid_point/EVT_strong_process` | Lemma/Theorem | ★ EVT как процесс (classic лишь в x_between_grid_points) |

**Key lemmas (deep):**

- **`argmax_idx_maximizes`** - Максимум на сетке выбран по ИНДЕКСУ (nat-позиция), а не по значению (Q): find_max_idx возвращает первую позицию с максимальным значением, и доказательство закрывается Leibniz-reflexivity по nat — обходя нерефлексивность Qeq (== vs =). Это ядро вены B: детерминированная селекция без AC, «ищи позицию, не значение». Дизайн-решение проекта (decision-log 2026-01-18). _(argmax-by-index, qeq-avoidance, vein-B, deterministic)_
- **`EVT_strong_process`** - EVT как процесс: grid-максимизатор уточняется по сетке, sup_process Cauchy. classic нужен ТОЛЬКО в x_between_grid_points (заполнение между узлами); сам argmax 0-аксиомный. Честная локализация цены — максимум-по-индексу свободен, интерполяция платит classic. _(EVT, process, honest-cost)_

**Uniqueness - score 4 (synthesis+observation).** EVT через argmax-по-ИНДЕКСУ: выбор максимума по nat-позиции (не Q-значению) закрывается Leibniz-reflexivity, обходя Qeq-vs-Leibniz — детерминированная no-AC селекция (вена B); classic лишь в интерполяции между узлами.
> _Caveat:_ Сеточная аппроксимация EVT стандартна; уникальность — в argmax-by-index приёме (позиция, не значение) как чистом образце детерминированной селекции вены B + честной локализации classic, не в теореме.

---

## #149 - `src/Expressions.v` - score 2 (methods)

**The ToS language: expression syntax, values, shift/subst**

- **Topic.** The Expr syntax (var/lam/app/pair/fst/snd/const/system/elem/observe/resolve), is_value, an expr_size with subterm-smaller lemmas, shift and subst, decidable equality, and size-based induction.
- **Role.** Type-theory core (the language's syntax). Defines Expr/step prerequisites. Self-contained. June 2026 wave-4 tail: expr_finite was the vacuous exists n, expr_size e = n -> successor form expr_size e = S n (via expr_size_positive).
- **Counts.** Qed 28 / Admitted 0 / axioms 0
- **Imports.** Stdlib
- **E/R/R.** _Elements:_ выражения Expr (var/lam/app/pair/system/elem/observe). _Roles:_ значения is_value; размер как фундированная мера. _Rules:_ shift/subst; expr_size; subterm strictly smaller. _P4:_ термы конечны (expr_finite); размер фундирован ⟹ индукция по подтермам; синтаксис ToS-языка.
- **Classical counterpart.** A lambda-calculus-style expression syntax with values, a size measure, shift/subst and decidable equality is standard PL metatheory; NEW: nothing -- the ToS language term syntax (with system/elem/observe/resolve) and well-founded subterm-size.
- **Tags.** syntax, expressions, type-theory, well-founded, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `Expr/is_value/expr_size/shift/subst/expr_eq_dec/is_value_dec` | Inductive/Definition/Lemma | синтаксис, значения, shift/subst |
| `app_fun_smaller/arg_smaller/lam_body_smaller/pair_fst_smaller/resolve_subterm_smaller` | Lemma | ★ подтермы строго меньше (фундированность) |
| `subst_const/system/pair/app/expr_finite/induction_size/lam_is_value/system_is_value` | Lemma | подстановка; индукция по размеру |

**Key lemmas (deep):**

- **`expr_finite`** - Термы ToS-языка конечны, размер фундирован (подтермы строго меньше) — основа индукции по структуре для всей метатеории (reduction, typing, safety). Element-сторона: синтаксис конечно-актуален (P4), включая системо-специфичные конструкции (system/elem/observe/resolve). _(syntax, well-founded, subterm-size)_

**Uniqueness - score 2 (methods).** Синтаксис ToS-языка (Expr с system/elem/observe/resolve, значения, shift/subst, фундированный размер) — основа верифицированной метатеории.
> _Caveat:_ Синтаксис лямбда-исчисления стандартен; вклад — ToS-специфичные конструкции + основа type-safety цепочки.

---

## #150 - `src/Extraction.v` - score 0 (infrastructure)

**Extraction directives (configuration only)**

- **Topic.** Coq extraction directives configuring OCaml output for the ToS language / certified gap modules. No theorems.
- **Role.** Build/extraction configuration. 0 Qed.
- **Counts.** Qed 0 / Admitted 0 / axioms 0
- **Imports.** Stdlib Extraction
- **E/R/R.** _Elements:_ директивы извлечения. _Roles:_ конфигурация извлечения как роль инфраструктуры. _Rules:_ Extraction Language OCaml; inline-директивы. _P4:_ только конфигурация извлечения; 0 теорем (инфраструктура).
- **Classical counterpart.** Coq extraction directives (Extraction Language / inline directives) producing OCaml are routine tooling; NEW: nothing -- extraction configuration only (0 Qed).
- **Tags.** extraction, build, infrastructure

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `(extraction directives only)` | Directive | конфигурация вывода OCaml, без теорем |

**Key lemmas (deep):**


**Uniqueness - score 0 (infrastructure).** Директивы извлечения в OCaml (конфигурация, 0 теорем).
> _Caveat:_ Чистая инфраструктура сборки; не содержит результатов.

---

## #159 - `src/FixedPoint.v` - score 3 (synthesis+observation)

**Banach fixed point over Q: contraction iterates Cauchy, unique fixed point**

- **Topic.** is_contraction (rate 0<r<1), iterates staying in interval, the iterate difference geometric bound, iterates Cauchy (Banach), approximate/unique fixed point, fixed-point independence of start, and composition of contractions.
- **Role.** Convergence HUB (vein C). iterate_is_cauchy used by ReasoningConvergence/Regulus. Self-contained.
- **Counts.** Qed 20 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ сжимающее отображение (rate 0<r<1); итераты. _Roles:_ неподвижная точка как role-limit процесса итераций; сжатие как роль. _Rules:_ \|f(x)−f(y)\|≤r\|x−y\|; итераты Cauchy с геом. скоростью; точка единственна. _P4:_ неподвижная точка = ПРЕДЕЛ процесса итераций (role-limit); каждая итерация актуальна (Element); скорость явная (геометрическая) — вена C, движок сходимости.
- **Classical counterpart.** The Banach fixed-point theorem (a contraction has a unique fixed point, geometric convergence) is classical; NEW is only the constructive Q form: contraction iterates are Cauchy with an explicit geometric rate, unique fixed point, composition of contractions -- the convergence hub.
- **Tags.** banach, fixed-point, contraction, convergence, vein-C, hub

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `is_contraction/iterate/iterate_in_interval/iterate_contraction/step_shrink` | Definition/Lemma | сжатие и его итераты |
| `iterate_diff_bound/iterate_is_cauchy/banach_fixed_point/approximate_fixed_point` | Lemma | ★ итераты Cauchy (Банах), неподвижная точка |
| `contraction_unique_fixed/fixed_point_independent/contraction_limit_in_interval/contraction_compose/iterate_is_contraction/geometric_ps_recurrence` | Lemma | ★ единственность, независимость от старта, композиция |

**Key lemmas (deep):**

- **`iterate_is_cauchy`** - Итераты сжатия образуют Cauchy-процесс с ЯВНОЙ геометрической скоростью (Банах) — движок сходимости всего репо (ReasoningConvergence, GradientDescent, Picard, Regulus-мост). Element/role-limit: каждая итерация актуальна, неподвижная точка — предел процесса; скорость вычислима, не постулируется. _(banach, contraction, cauchy, convergence-hub)_
- **`fixed_point_independent`** - Неподвижная точка НЕ зависит от стартовой — единственность (contraction_unique_fixed) + независимость делают предел детерминированным. Перекликается с веной B: сходимость как правило, а не выбор. _(uniqueness, start-independent)_

**Uniqueness - score 3 (synthesis+observation).** Банах над Q: итераты сжатия Cauchy с явной геометрической скоростью, единственная стартонезависимая неподвижная точка, композиция сжатий — движок сходимости репо (вена C).
> _Caveat:_ Банах классичен; уникальность — в роли переиспользуемого 0-аксиомного движка сходимости с явными скоростями (ReasoningConvergence/Regulus/Picard/GD), не в теореме.

---

## #160 - `src/FormationRules.v` - score 2 (new-framing)

**Formation rules: Pi/Sigma/layer formation tied to P1/P4**

- **Topic.** System formation with a P1 check and an L4 role principle, Pi/Sigma formation, application/pairing/projection rules, P4 observe (no collect), layer formation/projection, the L5 resolve rule, weakening and substitution typing.
- **Role.** Type-theory (formation rules). Imports Core_ERR.
- **Counts.** Qed 18 / Admitted 0 / axioms 0
- **Imports.** ToS Core_ERR
- **E/R/R.** _Elements:_ правила формации конструкторов (Pi/Sigma/layer). _Roles:_ формация как роль построения типов; связана с P1/P4. _Rules:_ sys_form с p1_check; pi/sigma_form; p4_observe/no_collect; l5_res_rule. _P4:_ ★ формация уважает P1 (нет самочленства) и P4 (observe, НЕ collect — нельзя собрать в завершённый объект); L5-резолв как правило.
- **Classical counterpart.** Formation rules for type constructors (Pi/Sigma/application/projection), weakening and substitution typing are standard; NEW: nothing -- the ToS formation rules tying constructor formation to P1/P4 and the L5 resolve rule.
- **Tags.** formation, P1, P4, type-theory, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `sys_form/p1_check/l4_role_principle/pi_form/sigma_form/pi_app_rule/sigma_pair_rule` | Definition/Lemma | ★ правила формации (Pi/Sigma) с p1_check |
| `p4_observe/p4_no_collect/layer_form/l5_res_rule/weakening/substitution_type` | Lemma | ★ P4: observe не collect; L5-резолв |

**Key lemmas (deep):**

- **`p4_no_collect`** - Правило формации p4_no_collect: можно НАБЛЮДАТЬ (observe) процесс, но НЕЛЬЗЯ собрать его в завершённый объект (collect) — P4 как синтаксическое правило формации. Element-сторона: типы строятся с уважением к P1/P4, реификация процесса в объект запрещена на уровне формации. _(formation, P4, observe-not-collect)_

**Uniqueness - score 2 (new-framing).** Правила формации, привязанные к P1/P4 (sys_form с p1_check, p4_observe-not-collect, L5-резолв) — типовая дисциплина E/R/R.
> _Caveat:_ Правила формации стандартны; ново — привязка к P1/P4 (observe-not-collect как правило), не новая теория типов.

---

## #547 - `src/GradientDescent.v` - score 2 (methods)

**Gradient descent over Q: contraction convergence, optimal learning rate**

- **Topic.** A valid learning rate making the update a contraction, the error/weight/loss iterates Cauchy and converging (geometrically), the convergence rate, optimal-lr one-step, and cumulative error.
- **Role.** Optimization (convergence, vein C). Builds on FixedPoint/Differentiation. Self-contained.
- **Counts.** Qed 18 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; FixedPoint
- **E/R/R.** _Elements:_ веса, ошибка, потеря; learning rate. _Roles:_ градиентный шаг как сжатие (rate 1−eta); сходимость как role-limit. _Rules:_ valid_lr ⟹ contraction; gd_error_cauchy; optimal_lr. _P4:_ градиентный спуск = процесс сжатия (Element-итерации); сходимость к минимуму = role-limit с явной геом. скоростью (опирается на FixedPoint).
- **Classical counterpart.** Gradient descent convergence for a strongly-convex/quadratic loss via a contraction with rate 1-eta and a geometric error bound is classical; NEW: nothing -- a constructive Q form (the weight iterates Cauchy, loss vanishes, convergence rate, optimal learning rate).
- **Tags.** gradient-descent, optimization, contraction, convergence, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `valid_lr/contraction/gd_error/weight/loss/contraction_abs_lt_1` | Definition/Lemma | сжатие при валидном lr |
| `gd_error_cauchy/weight_cauchy/converges/loss_decreasing/loss_converges_zero/convergence_rate` | Lemma | ★ итерации Cauchy, потеря →0 геометрически |
| `optimal_lr_contraction/one_step/gd_cumulative_error` | Lemma | оптимальный learning rate |

**Key lemmas (deep):**

- **`gd_weight_converges`** - Веса градиентного спуска образуют Cauchy-процесс, сходящийся к минимуму с явной геометрической скоростью (через FixedPoint.iterate_is_cauchy: шаг = сжатие с rate 1−eta). Element/role-limit: оптимизация как процесс сжатия; потеря →0 вычислимо, не постулировано. _(gradient-descent, contraction, convergence)_

**Uniqueness - score 2 (methods).** Сходимость градиентного спуска над Q (шаг=сжатие, веса Cauchy, потеря →0 геометрически, оптимальный lr) через Banach-движок.
> _Caveat:_ Сходимость GD для сильно-выпуклой потери классична; вклад — конструктивное Q-исполнение на FixedPoint-движке.

---

## #550 - `src/HeineBorel_ERR.v` - score 3 (new-framing)

**Heine-Borel over Q by depth + Lebesgue number (honest non-compactness)**

- **Topic.** Open covers and uniform covers over Q, a halving HBState, ball-covers-small-interval, coverability concatenation, and Heine-Borel by depth / uniform given a Lebesgue number -- with the genuine Q-non-compactness acknowledged.
- **Role.** Analysis (Heine-Borel, honest ERR form). Pairs with analysis/HeineBorelComplete. Self-contained.
- **Counts.** Qed 25 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ открытые покрытия над Q; HBState; число Лебега. _Roles:_ компактность как role-limit ([0,1]∩Q НЕ компактно); число Лебега = честная гипотеза. _Rules:_ hb_step делит; ball_covers_small_interval; Heine_Borel_by_depth. _P4:_ [0,1]∩Q genuinely НЕ компактно (role-limit); конечное подпокрытие — Element только при числе Лебега; ранее 2 Admitted, закрыты гипотезой (не подделкой).
- **Classical counterpart.** Heine-Borel (finite subcover) is classical and FAILS for [0,1] over Q; NEW is only the honest depth/Lebesgue-number form: a finite subcover extracted by depth given a Lebesgue number, with [0,1] cap Q genuinely non-compact acknowledged (previously 2 Admitted, now closed by the hypothesis).
- **Tags.** heine-borel, compactness, lebesgue-number, honest-limitation, new-framing

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `OpenCover/valid_cover/uniform_cover/covered_by/FiniteSubcover/has_lebesgue_number` | Definition | покрытия и число Лебега |
| `HBState/hb_step/halves/hb_width/ball_covers_small_interval/coverable_concat/not_coverable_half` | Definition/Lemma | ★ делящая машина, покрываемость по ширине |
| `Heine_Borel_by_depth/uniform/Heine_Borel/lipschitz_implies_uniform` | Theorem/Lemma | ★ Гейне-Борель по глубине при числе Лебега |

**Key lemmas (deep):**

- **`Heine_Borel`** - Гейне-Борель над Q ЧЕСТНО: конечное подпокрытие извлекается по глубине при гипотезе числа Лебега, потому что [0,1]∩Q genuinely НЕ компактно (нет R-полноты). Ранее имел 2 Admitted — закрыты ДОБАВЛЕНИЕМ гипотезы (число Лебега), а не подделкой. Образец честной работы с границей Q (CLAUDE.md invariant). _(heine-borel, lebesgue-number, honest-non-compactness)_

**Uniqueness - score 3 (new-framing).** Гейне-Борель над Q по глубине при гипотезе числа Лебега: [0,1]∩Q НЕ компактно (role-limit); 2 бывших Admitted закрыты честной гипотезой, не подделкой.
> _Caveat:_ Гейне-Борель классичен; вклад — честная локализация недостающей полноты (число Лебега) + закрытие Admitted гипотезой, не полный Гейне-Борель.

---

## #551 - `src/InductiveSystems.v` - score 2 (methods)

**Inductive systems: finitely-generated with a well-founded depth**

- **Topic.** FinitelyGenerated systems (nat/list/BTree) with a depth measure, depth = id/length, no infinite depth (well-founded), structural induction completeness, constructor disjointness, and base/step as elements.
- **Role.** Type-theory/systems (inductive). Defines FinitelyGenerated. Imports Core_ERR. June 2026 wave-4 tail: nat_no_infinite_depth was the vacuous exists k, nat_depth n = k -> zero-or-successor constructor dichotomy (genuine well-foundedness lives in nat_depth_pred_lt + induction completeness).
- **Counts.** Qed 26 / Admitted 0 / axioms 0
- **Imports.** ToS Core_ERR
- **E/R/R.** _Elements:_ индуктивные системы (nat/list/BTree); их глубина. _Roles:_ FinitelyGenerated как роль (конечно-порождённость); глубина как мера. _Rules:_ nat_no_infinite_depth (фундированность); induction_complete; constructors_disjoint. _P4:_ индуктивные системы конечно-порождены и фундированы (нет бесконечной глубины) — P4-актуальность; база/шаг = элементы.
- **Classical counterpart.** Inductive types (nat, list, binary trees) with a depth measure, structural induction completeness and constructor disjointness are standard; NEW is only the ToS framing: FinitelyGenerated systems with depth, base=element / step=element, well-founded depth.
- **Tags.** inductive, finitely-generated, well-founded, type-theory, methods
- **Notes.** PowerShell flagged Adm=1 but it is a comment mention; actual Admitted = 0 (verified by ^Admitted. grep returning none).

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `FinitelyGenerated/nat_depth/nat_fg/nat_no_infinite_depth/nat_induction_complete/constructors_disjoint` | Definition/Lemma | ★ nat: конечно-порождён, фундирован |
| `list_depth/fg/induction_complete/btree_depth/fg/induction_complete` | Definition/Lemma | list/BTree аналогично |
| `base_case_is_element_nat/step_case_is_element_nat/nat_depth_pred_lt/btree_depth_left_lt` | Lemma | база/шаг — элементы; глубина убывает |

**Key lemmas (deep):**

- **`nat_no_infinite_depth`** - Индуктивные системы фундированы: нет бесконечной глубины (nat/list/BTree) — P4-актуальность (конечно-порождённость). Структурная индукция полна, конструкторы дизъюнктны. Element-сторона: индуктивные типы как конечно-порождённые ToS-системы. _(inductive, finitely-generated, well-founded)_

**Uniqueness - score 2 (methods).** Индуктивные системы как конечно-порождённые с фундированной глубиной (nat/list/BTree), полнота индукции, дизъюнктность конструкторов.
> _Caveat:_ Индуктивные типы — стандарт; вклад — встраивание в E/R/R как FinitelyGenerated. Слово 'Admitted' встречается в комментарии (0 реальных Admitted).

---

## #552 - `src/InfoLayer.v` - score 2 (new-framing)

**Information layers: one substrate, many layers, P3-separated**

- **Topic.** InfoLayer with layer equivalence, decidable membership, multi-layer elements, layer composition (commutative/associative/idempotent), and P3 separating same-substrate different-layer objects.
- **Role.** ToS information-layer modelling. Imports Core_ERR/IntensionalIdentity. Self-contained.
- **Counts.** Qed 17 / Admitted 0 / axioms 0
- **Imports.** ToS Core_ERR, IntensionalIdentity
- **E/R/R.** _Elements:_ информационные слои над субстратом; объекты в слоях. _Roles:_ слой как роль организации информации; P3 разделяет слои. _Rules:_ compose_layers коммут./ассоц./идемпотентна; in_layer разрешим. _P4:_ один субстрат несёт МНОГО слоёв; P3 разделяет одинаковый-субстрат-разный-слой — интенсиональность на уровне информации.
- **Classical counterpart.** An information-layer view where one substrate carries multiple layers (with composition, decidable membership, P3 separation) is a modelling choice; NEW is only the ToS framing: layers over a substrate with P3 separating same-substrate different-layer objects.
- **Tags.** info-layer, P3, substrate, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `InfoLayer/layer_equiv/in_layer/decidable/element_multi_layer/compose_layers` | Definition/Lemma | слои, членство разрешимо, композиция |
| `compose_layers_comm/assoc/idempotent/same_substrate_different_layers/P3_layers_separation` | Lemma | ★ P3 разделяет одинаковый субстрат / разные слои |

**Key lemmas (deep):**

- **`P3_layers_separation`** - P3 разделяет объекты с ОДИНАКОВЫМ субстратом, но разными информационными слоями — интенсиональность (IntensionalIdentity) на уровне информации. Element-сторона: один носитель несёт много слоёв, различимых критерием (слоем), не субстратом. _(info-layer, P3, separation)_

**Uniqueness - score 2 (new-framing).** Информационные слои над субстратом (композиция коммут./ассоц./идемпотентна, разрешимое членство) с P3-разделением одинаковый-субстрат/разный-слой.
> _Caveat:_ Слоистое моделирование информации — выбор модели; ново — привязка к P3-интенсиональности, не новая теория.

---

## #555 - `src/IntegralApplications.v` - score 2 (methods)

**Integration by parts over Q with error bounds**

- **Topic.** Product telescoping/decomposition, the increment-product bound, IBP (ftc_product / integration_by_parts) with bounds, and antiderivative uniqueness.
- **Role.** Calculus chain (IBP applications). Self-contained.
- **Counts.** Qed 19 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ произведения функций; их приращения. _Roles:_ интегрирование по частям как роль (правило произведения для интегралов). _Rules:_ ftc_product; integration_by_parts с оценками; antiderivative_unique. _P4:_ IBP над Q в эпсилон-форме (Element); первообразная единственна с точностью до константы.
- **Classical counterpart.** Integration by parts and the antiderivative-uniqueness corollary are classical; NEW: nothing -- a constructive Q IBP via the product rule with explicit error bounds.
- **Tags.** IBP, integration, antiderivative, calculus, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `product_tele/decomp/triple_abs_bound/increment_product_bound/product_error_bound` | Lemma | телескоп и оценка произведения |
| `udiff_product/square/ftc_product/integration_by_parts/ibp_bound/antiderivative_unique` | Lemma | ★ интегрирование по частям + единственность первообразной |

**Key lemmas (deep):**

- **`integration_by_parts`** - Интегрирование по частям над Q через правило произведения с явной ошибкой — Element-сторона исчисления. Antiderivative_unique (первообразная единственна до константы) завершает картину интеграла как процесса с контролем. _(IBP, product-rule, antiderivative)_

**Uniqueness - score 2 (methods).** Интегрирование по частям над Q с оценками ошибки + единственность первообразной.
> _Caveat:_ IBP классично; вклад — конструктивное Q-исполнение.

---

## #556 - `src/IntensionalIdentity.v` - score 3 (new-framing)

**Intensional identity: P3 separation (extensional /=> intensional)**

- **Topic.** CriterionOver and extensional equivalence, P3_eq implies ext_equiv but not conversely, a concrete counterexample (two criteria, same elements, different criterion), and that criterion fixes level.
- **Role.** Core E/R/R (P3 intensional identity). Defines CriterionOver/ext_equiv/int_equiv. Imports Core_ERR.
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** ToS Core_ERR
- **E/R/R.** _Elements:_ критерии CriterionOver; их экстенсионалы. _Roles:_ интенсиональная идентичность (по критерию) против экстенсиональной (по элементам). _Rules:_ P3_eq ⟹ ext_equiv, но ext_equiv ⇏ P3_eq (контрпример). _P4:_ система — это критерий, не множество элементов; P3-сепарация: одинаковый экстенсионал не делает системы тождественными.
- **Classical counterpart.** Intensional vs extensional equality (same extension, different criterion) is a classical distinction (Frege sense/reference); NEW is only the P3 formalization: a CriterionOver with ext_equiv, proving extensional equality does NOT imply intensional (criterion) equality, with a concrete counterexample.
- **Tags.** intensional-identity, P3, ERR, extensional, new-framing

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `CriterionOver/ext_equiv/ext_equiv_refl/sym/trans/ext_equiv_element_transfer` | Definition/Lemma | критерий и экстенсиональная эквивалентность |
| `P3_eq_implies_ext/same_criterion_same_level/different_level_different_criterion` | Lemma | P3-равенство ⟹ экстенсиональное; критерий фиксирует уровень |
| `ext_equiv_counterexample/P3_neq_counterexample/extensional_not_implies_intensional/system_P3_separation` | Lemma | ★ контрпример: экстенсионально равны, интенсионально различны |

**Key lemmas (deep):**

- **`extensional_not_implies_intensional`** - P3-сепарация: две системы с ОДИНАКОВЫМ набором элементов, но разными критериями, интенсионально РАЗЛИЧНЫ (конкретный контрпример). Формализует «система = критерий, не множество» — фрегевское sense/reference в типах ToS. Ядро интенсиональной онтологии E/R/R. _(P3, intensional, extensional, separation)_

**Uniqueness - score 3 (new-framing).** P3 интенсиональная сепарация: экстенсиональное равенство НЕ влечёт интенсиональное (критериальное), с конкретным контрпримером — «система = критерий, не множество».
> _Caveat:_ Интенсиональность/экстенсиональность — классическое различие (Фреге); вклад — формализация как P3-принцип ToS, не новая логика.

---

## #559 - `src/IVT_CauchyReal.v` - score 3 (new-framing)

**IVT as a Cauchy real: bisection to an epsilon-root (exact root impossible over Q)**

- **Topic.** Bisection producing a Cauchy sequence in the interval, the composed function converging to zero, and the IVT real (ivt_cauchy_real) -- a CauchyReal where f is arbitrarily small, not an exact zero.
- **Role.** Calculus (IVT, Cauchy-real form). Imports CauchyReal. Self-contained.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; CauchyReal
- **E/R/R.** _Elements:_ бисекция при смене знака; составная функция. _Roles:_ IVT-корень как Cauchy-РЕАЛ (epsilon-корень), не точный нуль. _Rules:_ bisection_f_converges_to_zero; ivt_cauchy_real. _P4:_ точный f(x)=0 НЕВОЗМОЖЕН над Q (нет полноты); IVT даёт Cauchy-реал, где \|f\|<eps для любого eps — честный role-limit.
- **Classical counterpart.** The intermediate value theorem (a sign change forces a root) is classical and FAILS to give an exact root over Q; NEW is the honest epsilon-IVT: bisection converges to a Cauchy real where \|f\|<eps for every eps (exact f(x)=0 is impossible over Q).
- **Tags.** IVT, epsilon-root, cauchy-real, bisection, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `bisection_cauchy_seq/in_interval/continuous_compose_cauchy/compose_cauchy_seq` | Lemma | бисекция — Cauchy в интервале |
| `bisection_f_converges_to_zero/ivt_cauchy_real/ivt_cauchy_real_equiv` | Lemma | ★ IVT-реал: \|f\| произвольно мал (не точный нуль) |

**Key lemmas (deep):**

- **`ivt_cauchy_real`** - IVT даёт Cauchy-РЕАЛ, где f произвольно мал (\|f\|<eps для любого eps), а НЕ точный нуль — потому что точный корень невозможен над Q без полноты ℝ. Честная epsilon-форма (role-limit): корень = предел бисекционного процесса, наблюдаемый с любой точностью. _(IVT, epsilon-root, cauchy-real, honest-limitation)_

**Uniqueness - score 3 (new-framing).** IVT как Cauchy-реал: бисекция к epsilon-корню (|f|<eps для любого eps), точный f(x)=0 невозможен над Q — честный role-limit вместо ложного точного корня.
> _Caveat:_ IVT классичен; вклад — честная epsilon-Q-форма (корень как процесс/role-limit), а не точный нуль; фундаментально, не ограничение.

---

## #560 - `src/IVT_ERR.v` - score 2 (methods)

**IVT as a bisection process (ERR form, sign via Qlt_le_dec)**

- **Topic.** A bisection state machine choosing the sub-interval by sign (Qlt_le_dec), the process being Cauchy with halving width, sign preservation, and IVT_process producing the epsilon-root.
- **Role.** Calculus (IVT, ERR/process form). Self-contained.
- **Counts.** Qed 23 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ бисекционная машина; знак через Qlt_le_dec. _Roles:_ IVT как процесс бисекции; выбор половины по знаку. _Rules:_ bisection_step делит по знаку; ширина делится пополам; знаки сохраняются. _P4:_ IVT-корень = ПРОЦЕСС бисекции (epsilon-форма); выбор половины РАЗРЕШИМ (Qlt_le_dec) — детерминированно, не оракул.
- **Classical counterpart.** The intermediate value theorem via bisection is classical; NEW is the ERR/process form: a bisection process (sign-decided via Qlt_le_dec) yielding an epsilon-root as a process, with explicit width control.
- **Tags.** IVT, bisection, decidable, process, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `BisectionState/bisection_step/iter/process/step_halves/width/iter_bounds/nested` | Definition/Lemma | ★ бисекционная машина (ширина пополам) |
| `bisection_in_interval/shrinks/is_Cauchy/preserves_signs_weak/IVT_process` | Lemma | ★ процесс Cauchy, сохраняет знаки, даёт epsilon-корень |

**Key lemmas (deep):**

- **`IVT_process`** - IVT как детерминированный процесс бисекции: выбор половины РАЗРЕШИМ через Qlt_le_dec по знаку (не оракул), процесс Cauchy с делением ширины пополам, знаки сохраняются. Element/role-limit: корень = предел разрешимо-выбираемого процесса (перекликается с веной B — выбор правилом). _(IVT, bisection-process, decidable-sign)_

**Uniqueness - score 2 (methods).** IVT как детерминированный бисекционный процесс над Q (выбор половины разрешим через Qlt_le_dec), epsilon-корень с контролем ширины.
> _Caveat:_ Бисекционный IVT стандартен; вклад — процессное Q-исполнение с разрешимым выбором, перекликается с веной B.

---

## #561 - `src/Judgments.v` - score 2 (methods)

**Judgments: HasType / HasElem / SystemEquiv with contexts**

- **Topic.** Context entries and well-formedness, lookup (decidable), the HasType/HasElem/SystemEquiv judgments, has_type implies P1, has_elem satisfies criterion, weakening, type uniqueness, and P2.
- **Role.** Type-theory infrastructure (judgments). Imports Core_ERR. June 2026 wave-4 tail: ce_name_total was the vacuous exists n, ce_name e = n -> zero-or-successor dichotomy.
- **Counts.** Qed 23 / Admitted 0 / axioms 0
- **Imports.** ToS Core_ERR
- **E/R/R.** _Elements:_ контексты CtxEntry; суждения HasType/HasElem/SystemEquiv. _Roles:_ суждения как роли типизации/членства; контекст well-formed. _Rules:_ ctx_lookup; weakening; has_type ⟹ P1; has_elem ⟹ criterion. _P4:_ суждения связывают типизацию с принципами P1/P2; контекст конечно-проверяем (Element).
- **Classical counterpart.** Typing/membership judgments with a well-formed context, lookup, weakening and equivalence are standard PL infrastructure; NEW: nothing -- the ToS judgments (HasType/HasElem/SystemEquiv) tying typing to P1/P2.
- **Tags.** judgments, context, has-type, P1, type-theory, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `CtxEntry/Context/ctx_well_formed/ctx_lookup/wf_nil/cons/lookup_dec` | Definition/Lemma | контексты и lookup |
| `HasType/HasElem/SystemEquiv/has_type_implies_P1/has_elem_satisfies_criterion/has_type_P2` | Definition/Lemma | ★ суждения связаны с P1/P2 |
| `system_equiv_refl/sym/trans/has_type_weakening/level_unique/system_equiv_same_level` | Lemma | эквивалентность; weakening; уникальность уровня |

**Key lemmas (deep):**

- **`has_type_implies_P1`** - Суждение HasType влечёт P1 (нет самочленства) — связывает систему типизации с фундаментальным принципом иерархии. Element-сторона: типизация в контексте уважает P1/P2; основа Soundness (парадоксы нетипизуемы). _(judgments, has-type, P1)_

**Uniqueness - score 2 (methods).** Суждения ToS-языка (HasType/HasElem/SystemEquiv в контексте) связаны с P1/P2; weakening, уникальность уровня.
> _Caveat:_ Суждения и контексты стандартны; вклад — стыковка типизации с принципами E/R/R.

---

## #562 - `src/L5Resolution.v` - score 3 (synthesis+observation)

**L5 resolution: the deterministic constitutive-order resolve (fold-min)**

- **Topic.** A general L5 resolve over a decidable total order (fold-left min), proven sound, minimal, deterministic, with the singleton/specialization lemmas -- the constitutive selection rule behind EVT_idx and the no-AC selection thread.
- **Role.** Core L5 engine (vein B determinism). Defines DecTotalOrder/l5_resolve_gen. Reused by EVT_idx, Roles, ConstitutionChecking.
- **Counts.** Qed 18 / Admitted 0 / axioms 0
- **Imports.** Stdlib: List
- **E/R/R.** _Elements:_ список кандидатов; разрешимый тотальный порядок DecTotalOrder. _Roles:_ L5-резолв = роль конститутивного выбора (наименьший по порядку). _Rules:_ l5_resolve_gen = fold-left min; sound/minimal/deterministic. _P4:_ выбор разрешён ПРАВИЛОМ (наименьший = первый по порядку), детерминирован — движок вены B (argmax-by-index, no-AC селекция).
- **Classical counterpart.** Selecting the least element of a decidable total order (a minimum/fold) is elementary; NEW is only the L5 framing: a deterministic constitutive-order resolve (l5_resolve_gen = fold-min) that is sound/minimal/deterministic, the engine behind argmax-by-index and no-AC selection.
- **Tags.** L5, resolution, deterministic, fold-min, vein-B, constitutive-order

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `dto_le_refl/l5_min_step/l5_resolve_gen/nat_dto/nat_le_total/antisym/trans` | Definition/Lemma | тотальный порядок и шаг-минимум |
| `fold_left_min_le_init/elem/in/l5_resolve_gen_some/none_iff/in` | Lemma | fold-min корректен и попадает в список |
| `l5_resolve_gen_minimal/deterministic/singleton/specializes` | Lemma | ★ резолв минимален, детерминирован, специализируется |

**Key lemmas (deep):**

- **`l5_resolve_gen_deterministic`** - L5-резолв детерминирован и минимален: над разрешимым тотальным порядком fold-min даёт ЕДИНСТВЕННЫЙ наименьший результат. Это движок вены B — argmax-by-index (EVT_idx), детерминированная селекция без выбора, конститутивный порядок ролей (Roles). Выбор = правило, не оракул. _(L5, deterministic, fold-min, vein-B)_

**Uniqueness - score 3 (synthesis+observation).** Детерминированный L5-резолв (fold-min над разрешимым тотальным порядком, sound/minimal/deterministic) — конститутивный движок вены B (argmax-by-index, no-AC селекция, резолюция ролей).
> _Caveat:_ Выбор минимума — элементарен; уникальность — в роли переиспользуемого конститутивного движка детерминированной селекции по всему репо, не в самой операции.

---

## #592 - `src/LevelAdjunction.v` - score 2 (methods)

**The level adjunction: embed -| forget across levels**

- **Topic.** The forward/backward transpose, the level adjunction, unit and counit (natural), triangle identities, the counit an iso for forgettable systems, and embed faithful via the adjunction.
- **Role.** Category-of-systems capstone (level adjunction). Defines adj_forward/backward/level_adjunction. Imports LevelFunctors.
- **Counts.** Qed 25 / Admitted 0 / axioms 0
- **Imports.** ToS LevelFunctors, SystemCategory
- **E/R/R.** _Elements:_ системы на уровнях L и LS; транспонирования. _Roles:_ embed -\| forget как сопряжение уровней; unit/counit как роли. _Rules:_ adj_forward/backward — биекция; треугольные тождества; counit изо для забываемых. _P4:_ поднятие уровней СОПРЯЖЕНО забыванию (embed -\| forget); counit изо ровно на forgettable — структурная точность границы уровней.
- **Classical counterpart.** An adjunction between an embedding and a forgetful functor (unit/counit, triangle identities) is standard category theory; NEW is only the ToS instance: embed -\| forget across the level hierarchy with the counit an iso exactly on forgettable systems.
- **Tags.** category, adjunction, level, embed-forget, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `adj_forward/backward/forward_backward/backward_forward/level_adjunction/adj_bijection_compat` | Definition/Lemma | ★ транспонирование = биекция (сопряжение) |
| `adjunction_unit_component/natural/is_iso/counit_component/natural/is_iso_for_forgettable` | Lemma | ★ unit/counit естественны; counit изо для забываемых |
| `triangle_identity_1/2/embed_faithful_via_adjunction/adj_preserves_iso/reflects_iso` | Lemma | треугольные тождества; embed верен через сопряжение |

**Key lemmas (deep):**

- **`level_adjunction`** - embed -\| forget: поднятие систем по уровням СОПРЯЖЕНО забыванию, с естественными unit/counit и треугольными тождествами. counit — изоморфизм ровно на forgettable-системах (где забывание обратимо). Категорная вершина уровневой структуры ToS. _(adjunction, level, embed-forget)_

**Uniqueness - score 2 (methods).** Сопряжение уровней embed -| forget (unit/counit естественны, треугольные тождества, counit изо для забываемых) — категорная вершина уровневой структуры ToS.
> _Caveat:_ Сопряжения embed/forget стандартны; вклад — ToS-инстанс уровневой иерархии, не новая категорная теорема.

---

## #593 - `src/LevelFunctors.v` - score 2 (methods)

**Level functors: embedding and forgetful across the level hierarchy**

- **Topic.** An embed functor raising systems across levels (faithful, preserves embedding/surjection/iso), the forgettable predicate and forget functor, their roundtrips, and P1 obstructing total forgetting (a witness L-system that is not forgettable).
- **Role.** Category-of-systems (level functors). Defines embed_obj/EmbedFunctor/forget_obj. Imports SystemCategory.
- **Counts.** Qed 27 / Admitted 0 / axioms 0
- **Imports.** ToS SystemCategory, LevelFunctors deps
- **E/R/R.** _Elements:_ системы на разных уровнях; кросс-уровневые отображения. _Roles:_ EmbedFunctor (поднятие) и forget (забывание) как функторы между уровнями. _Rules:_ embed верен, сохраняет iso; forget_embed roundtrip; P1 препятствует тотальному забыванию. _P4:_ поднятие уровней верно и обратимо частично; P1 (нет самочленства) ОБСТРУКЦИЯ тотальному forget — структурная граница.
- **Classical counterpart.** Functors between subcategories (an embedding and a forgetful), faithfulness and iso preservation are standard; NEW is only the ToS instance: an embed functor across levels and a forgetful one, with P1 obstructing total forgetting.
- **Tags.** category, level-functor, forgetful, embedding, P1, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `embed_obj/mor/faithful/preserves_embedding/surjection/EmbedFunctor/preserves_iso` | Definition/Lemma | ★ верный функтор-вложение уровней, сохраняет iso |
| `is_forgettable/forget_obj/forget_mor/forget_faithful/forget_embed_roundtrip/embed_forget_roundtrip` | Definition/Lemma | забывающий функтор и roundtrip'ы |
| `witness_L_not_forgettable/P1_obstructs_total_forget/is_forgettable_dec/embed_empty_is_initial` | Lemma | ★ P1 препятствует тотальному забыванию |

**Key lemmas (deep):**

- **`P1_obstructs_total_forget`** - P1 (нет самочленства) — структурная ОБСТРУКЦИЯ тотальному забывающему функтору: есть L-система-свидетель, которую нельзя забыть на нижний уровень. Связывает категорную структуру уровней с фундаментальным P1, готовя сопряжение (LevelAdjunction). _(level-functor, forgetful, P1-obstruction)_

**Uniqueness - score 2 (methods).** Функторы уровней: верный embed (поднятие, сохраняет iso) и forgetful, с P1 как структурной обструкцией тотальному забыванию.
> _Caveat:_ Embed/forgetful функторы стандартны; вклад — ToS-инстанс + P1-обструкция, основа сопряжения уровней.

---

## #608 - `src/LinearAlgebra.v` - score 1 (exposition)

**Linear algebra over Q: vectors, dot product, matrix-vector multiply**

- **Topic.** map2-based componentwise vector ops, QVec with add/scale/dot product (commutative, distributive, vector-space laws), and QMat matrix-vector multiplication.
- **Role.** Linear algebra over Q (foundation for physics/spectral files). Self-contained.
- **Counts.** Qed 22 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith List
- **E/R/R.** _Elements:_ Q-векторы QVec; матрицы QMat. _Roles:_ векторное пространство над Q; скалярное произведение/умножение матриц. _Rules:_ qv_add/scale/dot_product; vector-space laws; mat_vec_mul. _P4:_ конечномерная линейная алгебра над Q точна (Element).
- **Classical counterpart.** Vectors/matrices over Q (componentwise ops, dot product, matrix-vector multiply) with the vector-space laws are standard; NEW: nothing -- a constructive Q vector/matrix library.
- **Tags.** linear-algebra, vector-space, matrix, Q, exposition

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `map2/QVec/qv_add/scale/dot_product/qv_eq` | Definition | Q-векторы и операции |
| `qv_add_comm/assoc/scale_distrib/assoc/dot_product_comm/zero_right` | Lemma | ★ аксиомы векторного пространства |
| `QMat/mat_vec_mul/mat_vec_mul_length` | Definition/Lemma | умножение матрица-вектор |

**Key lemmas (deep):**

- **`qv_add_comm`** - Q-векторы образуют векторное пространство (коммутативность/ассоциативность сложения, дистрибутивность скаляра) над точной рациональной арифметикой. Element-сторона: конечномерная линейная алгебра — фундамент для physics/linalg/spectral файлов. _(linear-algebra, vector-space, Q)_

**Uniqueness - score 1 (exposition).** Линейная алгебра над Q (векторы/матрицы, скалярное произведение, законы векторного пространства).
> _Caveat:_ Векторы/матрицы стандартны; ценность инфраструктурная (фундамент physics/spectral).

---

## #609 - `src/MeanValueTheorem.v` - score 2 (methods)

**Mean value theorem over Q via a bounded walk (grid form)**

- **Topic.** A walk over a grid with uniform-difference bounds, bounded-derivative-implies-bounded-increment, zero-derivative-near-constant, sign of derivative implies monotonicity, local Lipschitz, and a quadratic-midpoint MVT instance.
- **Role.** Calculus chain (MVT, grid/constructive form). Self-contained.
- **Counts.** Qed 18 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ функции и производные; прогулка walk по сетке. _Roles:_ MVT как роль связи среднего наклона и производной (приближённо над Q). _Rules:_ bounded_deriv ⟹ bounded_increment; pos_deriv ⟹ increases. _P4:_ MVT в эпсилон-форме над Q: точное равенство (∃c, f'(c)=среднее) невозможно над Q — приближённые оценки наклона (Element), не точная точка c.
- **Classical counterpart.** The mean value theorem and its corollaries (zero derivative => constant, sign of derivative => monotonicity) are classical; NEW is only a constructive Q grid-MVT via a 'walk' with explicit bounds (exact equality is impossible over Q).
- **Tags.** MVT, calculus, grid, monotonicity, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `walk_point/udiff_on/walk_point_in_interval/walk_step_small/udiff_pointwise` | Definition/Lemma | прогулка по сетке с оценками разности |
| `bounded_deriv_bounded_increment/zero_deriv_near_constant/pos_deriv_increases/neg_deriv_decreases` | Lemma | ★ MVT-следствия (монотонность, постоянство) |
| `bounded_deriv_lipschitz_local/quadratic_udiff/mvt_quadratic_midpoint` | Lemma | локальный Липшиц; квадратичный MVT-инстанс |

**Key lemmas (deep):**

- **`pos_deriv_increases`** - Положительная производная ⟹ функция возрастает (через прогулку по сетке с оценками) — конструктивная MVT-форма над Q. Точное ∃c с f'(c)=среднее невозможно над Q (нет полноты), потому даются приближённые оценки наклона с явной ошибкой. _(MVT, monotonicity, grid)_

**Uniqueness - score 2 (methods).** MVT над Q в сеточной форме (bounded-deriv⟹bounded-increment, знак производной⟹монотонность) с явными оценками; точная точка c недостижима над Q.
> _Caveat:_ MVT классичен; вклад — конструктивная сеточная Q-версия + честная невозможность точного c, не новая теорема.

---

## #610 - `src/Measure.v` - score 2 (methods)

**Step-function integral and interval measure over Q**

- **Topic.** Step functions, the step integral (additive/scalable/monotone/nonneg), total width, interval measure (nonneg, additive), and integral bounds.
- **Role.** Calculus/measure (step integral). Pairs with analysis/StepIntegral. Self-contained.
- **Counts.** Qed 15 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith List
- **E/R/R.** _Elements:_ ступенчатые функции; интеграл; мера интервала. _Roles:_ интеграл/мера как роли; аддитивность. _Rules:_ integral_step аддитивен/монотонен; interval_measure аддитивна. _P4:_ ступенчатый интеграл и мера интервала конечны над Q (Element); основа measure-from-integral.
- **Classical counterpart.** The integral of step functions, additivity/monotonicity and measure of an interval are the classical start of measure theory; NEW: nothing -- a constructive Q step integral with interval measure and integral bounds.
- **Tags.** measure, step-integral, interval-measure, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `StepFunc/integral_step/total_width/const_step/step_add/scale/neg/le/mono/nonneg` | Definition/Lemma | ★ ступенчатый интеграл (аддитивен/монотонен) |
| `interval_measure/measure_nonneg/additive/integral_constant/integral_bounds/abs_bound/app` | Definition/Lemma | ★ мера интервала (аддитивна) |

**Key lemmas (deep):**

- **`measure_additive`** - Мера интервала аддитивна и неотрицательна, выведена из ступенчатого интеграла над Q — Element-сторона теории меры (пара к analysis/LebesgueMeasure measure-from-integral). Конструктивно, без сигма-алгебры. _(measure, additivity, step-integral)_

**Uniqueness - score 2 (methods).** Ступенчатый интеграл и мера интервала над Q (аддитивность/монотонность) — конструктивная основа меры.
> _Caveat:_ Интеграл простых функций классичен; вклад — Q-исполнение, пара к measure-from-integral.

---

## #611 - `src/MonotoneConvergence.v` - score 2 (methods)

**Monotone convergence over Q: bounded monotone => Cauchy**

- **Topic.** Increasing/decreasing bounded sequences are Cauchy (via the Archimedean unbounded-jumps argument), the MCT limit as least upper bound, the squeeze theorem, and constant sequences.
- **Role.** Calculus chain (MCT). Self-contained.
- **Counts.** Qed 15 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; CauchyReal
- **E/R/R.** _Elements:_ монотонные ограниченные последовательности. _Roles:_ MCT как role-limit (ограниченная монотонная сходится); sup как наименьшая верхняя граница. _Rules:_ jumps_unbounded ⟹ ограниченная монотонная — Cauchy; squeeze. _P4:_ ограниченная монотонная — Cauchy-процесс (Element-стадии), предел = role-limit (sup); скорость через архимедовость.
- **Classical counterpart.** The monotone convergence theorem (a bounded monotone sequence converges) and the squeeze theorem are classical; NEW: nothing -- a constructive Q form (bounded monotone => Cauchy, least upper bound, squeeze).
- **Tags.** MCT, monotone, squeeze, convergence, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `inc_le/dec_le/nat_archimedean/jumps_unbounded/q_inc_bounded_cauchy/q_dec_bounded_cauchy` | Lemma | ★ ограниченная монотонная — Cauchy |
| `mct_limit_inc/dec/inc_upper_bound/inc_least/squeeze_equiv/squeeze_cauchy_le` | Lemma | ★ MCT-предел = sup; squeeze |

**Key lemmas (deep):**

- **`q_inc_bounded_cauchy`** - Ограниченная возрастающая последовательность — Cauchy (иначе бесконечно много прыжков ≥ε нарушают границу, jumps_unbounded). Element-сторона MCT: монотонность+ограниченность ⟹ процесс сходится; предел — наименьшая верхняя граница (role-limit). _(MCT, monotone-bounded, cauchy)_

**Uniqueness - score 2 (methods).** MCT над Q (ограниченная монотонная — Cauchy через архимедовость, предел=sup) + squeeze.
> _Caveat:_ MCT и squeeze классичны; вклад — конструктивное Q-исполнение.

---

## #656 - `src/PhaseA_Examples.v` - score 1 (exposition)

**Phase-A examples: concrete E/R/R instances**

- **Topic.** A nat system at L2, nat-to-Q as a process, a list system as a sigma, a Cauchy reciprocal sequence as observable, decidable evenness, the nat system's erasure, and an integration check.
- **Role.** Examples/exposition (instantiating the core). Imports many core files. Self-contained.
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** ToS (Core_ERR, CoinductiveSystems, ErasureTheory, ...)
- **E/R/R.** _Elements:_ конкретные примеры систем (nat, list, Cauchy-поток). _Roles:_ примеры как роль экспозиции (инстансы ядра E/R/R). _Rules:_ nat_system_L2; cauchy_is_observable; nat_system_erasure. _P4:_ конкретные E/R/R-инстансы демонстрируют ядро (Element); связывают системы, процессы, наблюдаемость, стирание.
- **Classical counterpart.** Worked examples instantiating the framework (a nat system, a list sigma, an observable Cauchy stream, erasure) are exposition; NEW: nothing -- concrete E/R/R instances demonstrating the core types.
- **Tags.** examples, ERR, exposition
- **Notes.** PowerShell flagged Adm=1 but it is a comment mention; actual Admitted = 0.

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `Q_system_L2/nat_to_Q/list_nat_system_L2/recip_seq/cauchy_is_observable/is_even` | Definition/Lemma | конкретные системы/процессы/наблюдаемые |
| `nat_components/nat_system_erasure/finitely_generated_observable/integration_check/pi_system_level_depth` | Lemma | ★ E/R/R-инстансы (стирание, наблюдаемость) |

**Key lemmas (deep):**

- **`cauchy_is_observable`** - Cauchy-последовательность (recip_seq) ЕСТЬ наблюдаемая (Observable) — конкретно связывает анализ (CauchyReal), коиндукцию (наблюдаемость) и E/R/R-ядро. Демонстрирует когерентность фреймворка на примере; integration_check проверяет сборку. _(examples, observable, cauchy)_

**Uniqueness - score 1 (exposition).** Конкретные E/R/R-инстансы (nat-система, list-sigma, Cauchy-наблюдаемая, стирание) — демонстрация когерентности ядра.
> _Caveat:_ Проработанные примеры — экспозиция; ценность — демонстрация сборки фреймворка. Слово 'Admitted' в комментарии (0 реальных).

---

## #686 - `src/PInterval_CROWN.v` - score 3 (methods)

**CROWN ReLU bounds over Q: sound and tighter than IBP**

- **Topic.** The Q ReLU, lower/upper linear relaxation bounds (sound for positive/negative/mixed cases), the CROWN backward propagation, and that CROWN is tighter than interval-bound-propagation (crown_tighter_ibp).
- **Role.** Neural-net verification over Q (CROWN). Pairs with RoundingSafety. Self-contained.
- **Counts.** Qed 25 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ ReLU над Q; линейные релаксации (нижняя/верхняя). _Roles:_ CROWN-границы как роль верификации нейросети; tighter than IBP. _Rules:_ relu_lower/upper_bound_sound; crown_backward_sound; crown_tighter_ibp. _P4:_ CROWN-границы ReLU КОРРЕКТНЫ и ТОЧНЕЕ IBP (Element): линейная релаксация точно над Q, верификация нейросети как доказательство.
- **Classical counterpart.** CROWN-style linear relaxation bounds for ReLU networks (lower/upper affine bounds, backward propagation) are standard neural-net verification; NEW is only the constructive Q form: sound CROWN ReLU bounds proven tighter than interval-bound-propagation (IBP).
- **Tags.** CROWN, relu, neural-verification, interval, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `relu_Q/relu_lower_pos/neg/mixed/lower_bound_sound/upper_bound_sound` | Definition/Lemma | ★ корректные нижние/верхние границы ReLU |
| `crown_backward_nonneg/neg/sound/crown_width_le_ibp_width_mixed/crown_tighter_ibp` | Lemma | ★ CROWN backward; CROWN точнее IBP |

**Key lemmas (deep):**

- **`crown_tighter_ibp`** - CROWN-границы ReLU КОРРЕКТНЫ и СТРОГО ТОЧНЕЕ interval-bound-propagation (меньшая ширина в смешанном случае) над Q. Element-сторона: верификация нейросети как машинное доказательство — линейная релаксация ReLU точна над рациональной арифметикой, превосходя наивный IBP. Прикладная верифицированная численность. _(CROWN, relu, tighter-than-IBP, neural-verification)_

**Uniqueness - score 3 (methods).** CROWN-границы ReLU над Q: корректны и СТРОГО точнее IBP (crown_tighter_ibp) — верификация нейросети как доказательство над точной арифметикой.
> _Caveat:_ CROWN-релаксация — известный метод верификации нейросетей; вклад — конструктивная Q-формализация с доказанной точностью vs IBP, не новый метод.

---

## #687 - `src/PipelineExtraction.v` - score 1 (exposition)

**Pipeline extraction: validators total and decidable**

- **Topic.** Totality of the pipeline/ASK/gate validators, gate-passed iff pass, convergence and paradigm-shift decidable, and extraction completeness.
- **Role.** Reasoning-architecture (extraction readiness). Imports PipelineSemantics/DomainValidation.
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** ToS PipelineSemantics, DomainValidation
- **E/R/R.** _Elements:_ валидаторы конвейера. _Roles:_ тотальность/разрешимость как роль извлекаемости. _Rules:_ validate_*_is_total; has_converged_decidable; extraction_completeness. _P4:_ валидаторы тотальны и разрешимы (Element) ⟹ извлекаемы в исполнимый код.
- **Classical counterpart.** That validators/decision procedures are total/decidable (extractable) is routine; NEW: nothing -- totality/decidability of the reasoning-pipeline validators for extraction.
- **Tags.** extraction, pipeline, decidable, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `validate_pipeline/ask/gate_is_total/gate_passed_iff_pass/has_converged_decidable/needs_paradigm_shift_decidable/extraction_completeness` | Lemma | ★ валидаторы тотальны и разрешимы (извлекаемы) |

**Key lemmas (deep):**

- **`extraction_completeness`** - Все валидаторы конвейера ТОТАЛЬНЫ и РАЗРЕШИМЫ ⟹ извлекаемы в исполнимый код (OCaml). Element-сторона: методология рассуждения не только формализована, но и АЛГОРИТМИЧНА — можно запускать как программу-проверяльщик. _(extraction, total, decidable)_

**Uniqueness - score 1 (exposition).** Тотальность/разрешимость валидаторов конвейера рассуждения ⟹ извлекаемость в исполнимый код.
> _Caveat:_ Тотальность валидаторов рутинна; ценность — извлекаемость D1-D6 методологии.

---

## #688 - `src/PipelineSemantics.v` - score 2 (new-framing)

**Pipeline semantics: bounded run, convergence detection, paradigm shift**

- **Topic.** A PipelineProcess, the pe_distance, convergence and paradigm-shift detection, gate passing, a fuel-bounded run_pipeline, convergence monotonicity, expansion triggering a shift, and shift preserving validation.
- **Role.** Reasoning-architecture pipeline operational semantics. Imports DomainTypes. Self-contained.
- **Counts.** Qed 17 / Admitted 0 / axioms 0
- **Imports.** ToS DomainTypes
- **E/R/R.** _Elements:_ итеративный конвейер рассуждения; расстояние pe_distance. _Roles:_ семантика прогона как роль; сходимость/paradigm-shift. _Rules:_ run_pipeline_bounded; has_converged; expanding_triggers_shift. _P4:_ прогон конвейера ФИНИТЕН (топливо); сходимость детектируется; расширение запускает сдвиг — рассуждение как финитный процесс (Element).
- **Classical counterpart.** Operational semantics for an iterative pipeline with convergence, gates, and a paradigm-shift trigger is domain modelling; NEW is only the ToS reasoning-pipeline run semantics (bounded fuel, convergence detection, shift on expansion).
- **Tags.** reasoning-pipeline, semantics, convergence, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `PipelineProcess/pe_distance/has_converged/needs_paradigm_shift/run_pipeline/bounded` | Definition/Lemma | ★ финитный прогон конвейера |
| `convergence_monotone/expanding_triggers_shift/shift_preserves_erfragte/bumps_complexity/all_gates_implies_each` | Lemma | ★ сходимость монотонна; расширение ⟹ сдвиг |

**Key lemmas (deep):**

- **`run_pipeline_bounded`** - Прогон конвейера рассуждения ФИНИТЕН (ограничен топливом), со сходимостью и детекцией paradigm-shift при расширении. Element-сторона: методология рассуждения исполнима как финитный процесс; перекликается с ReasoningConvergence (сходимость как сжатие). _(pipeline, bounded-run, convergence)_

**Uniqueness - score 2 (new-framing).** Операционная семантика конвейера рассуждения (финитный прогон, детекция сходимости, paradigm-shift при расширении).
> _Caveat:_ Семантика пайплайна — доменное моделирование; ново — формализация D1-D6 методологии как исполнимого процесса.

---

## #689 - `src/PowerSeries.v` - score 2 (methods)

**Power series over Q: ratio test, the exponential series**

- **Topic.** Partial-sum manipulation, geometric domination, the ratio test, power-series convergence (Cauchy), and the exponential series exp_series converging via its ratio bound.
- **Role.** Calculus chain (power series / exp). Self-contained.
- **Counts.** Qed 19 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ степенные ряды; частичные суммы; exp-ряд. _Roles:_ сходимость как role-limit; ratio test как роль критерия. _Rules:_ ratio_test_abs ⟹ Cauchy; геом. доминирование; exp_series сходится. _P4:_ степенной ряд = ПРОЦЕСС частичных сумм (Element-стадии); сходимость через геометрическую мажоранту, предел — role-limit.
- **Classical counterpart.** Convergence of power series via the ratio test and the exponential series are classical; NEW: nothing -- a constructive Q ratio test with geometric domination, applied to the exp series, 0-axiom.
- **Tags.** power-series, exp, ratio-test, convergence, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `partial_sum_scale/split/geometric_domination/ratio_test_abs/power_term_ratio_bound` | Lemma | ★ ratio test через геом. доминирование |
| `power_series_converges/limit/Qfact/exp_term/exp_series/exp_ratio_bound/exp_series_cauchy/exp_limit` | Definition/Lemma | ★ exp-ряд сходится (Cauchy) |

**Key lemmas (deep):**

- **`exp_series_cauchy`** - Экспоненциальный ряд сходится (Cauchy) через геометрическую мажоранту своего ratio-bound над Q — конкретный нетривиальный степенной ряд как процесс частичных сумм. Element-сторона: каждая частичная сумма актуальна, exp = role-limit. _(power-series, exp, ratio-test, cauchy)_

**Uniqueness - score 2 (methods).** Степенные ряды над Q (ratio test через геом. доминирование) + сходимость exp-ряда как процесса.
> _Caveat:_ Ratio test и exp-ряд классичны; вклад — конструктивное Q-исполнение.

---

## #690 - `src/Probability.v` - score 2 (new-framing)

**Probability and fallacy detection: Bayes, base-rate/conjunction/gambler**

- **Topic.** Conditional probability (nonneg, <=1), Bayes' rule, independence (symmetric), and the base-rate / conjunction / gambler's fallacies formalized as detectable absurdities.
- **Role.** Probability + reasoning-architecture link (fallacy detection). Self-contained.
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ условные вероятности; независимость. _Roles:_ Байес/независимость как роли; ошибки рассуждения как обнаружимые нарушения. _Rules:_ bayes_rule; conjunction_fallacy_absurd (P(A&B)>P(A) абсурд). _P4:_ вероятностные ошибки формализованы как ОБНАРУЖИМЫЕ нарушения (Element-проверка); мост к Architecture_of_Reasoning.
- **Classical counterpart.** Conditional probability, Bayes' rule, independence, and the base-rate/conjunction/gambler's fallacies are classical; NEW is only the ToS framing: the fallacies formalized as detectable violations (e.g. conjunction P(A&B)>P(A) is absurd), tying to the reasoning-architecture branch.
- **Tags.** probability, bayes, fallacy-detection, reasoning, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `cond_prob/nonneg/le_one/bayes_rule/independent/sym/cond` | Definition/Lemma | ★ Байес и независимость |
| `base_rate_fallacy_detected/conjunction_fallacy_detected/absurd/gamblers_fallacy_detected/absurd/bayes_asymmetry` | Lemma | ★ ошибки как обнаружимые абсурды |

**Key lemmas (deep):**

- **`conjunction_fallacy_absurd`** - Ошибка конъюнкции (P(A&B)>P(A)) формализована как АБСУРД — машинно-обнаружимое нарушение вероятностной логики. Связывает вероятность с ветвью Architecture_of_Reasoning (детектор ошибок): ошибка рассуждения = доказуемое противоречие, не эвристика. _(bayes, fallacy-detection, conjunction)_

**Uniqueness - score 2 (new-framing).** Вероятностные ошибки (база ставки/конъюнкция/игрок) формализованы как обнаружимые абсурды + Байес/независимость — мост к Architecture_of_Reasoning.
> _Caveat:_ Вероятность и эти ошибки классичны (Канеман-Тверски); вклад — формализация как доказуемые нарушения, не новая теория вероятностей.

---

## #1035 - `src/ProcessContinuumHypothesis.v` - score 4 (synthesis+observation)

**A process Continuum Hypothesis: enumerable XOR perfect subtree (structural dichotomy)**

- **Topic.** Closed collections of binary processes as pruned trees; a closed non-enumerable collection contains a perfect subtree (Cantor-Bendixson flavour); the structural dichotomy (enumerable or perfect, no intermediate) and process_continuum_hypothesis.
- **Role.** Uncountability/process capstone (vein C/E). Imports ProcessTypes/ProcessDiagonal. Uses ShrinkingIntervals exports.
- **Counts.** Qed 41 / Admitted 0 / axioms 0
- **Imports.** ToS ProcessTypes, ProcessDiagonal, ShrinkingIntervals_ERR
- **E/R/R.** _Elements:_ замкнутые коллекции бинарных процессов как pruned-деревья; совершенные поддеревья. _Roles:_ счётность против совершенного поддерева как дихотомия типов процесса. _Rules:_ замкнутая не-счётная коллекция содержит совершенное поддерево; промежуточного типа нет. _P4:_ ПРОЦЕССНАЯ дихотомия (счётно XOR совершенно), РАЗРЕШИМАЯ структурно — НЕ ZFC CH (та независима); континуум как процессное дерево, не кардинальный объект.
- **Classical counterpart.** The (set-theoretic) Continuum Hypothesis is independent of ZFC (Goedel/Cohen); NEW is a DIFFERENT, decidable statement: a structural dichotomy for binary-process collections -- every closed collection is either enumerable OR contains a perfect (non-enumerable) subtree, with no intermediate process-type. NOT the ZFC CH.
- **Tags.** continuum-hypothesis, process, dichotomy, perfect-subtree, vein-C, vein-E

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `is_closed/closed_has_tree/countable_union_from_fam/not_enum_superset` | Definition/Lemma | замкнутые коллекции и деревья |
| `perf_subtree/in_tree/not_enum/nonempty/has_child/is_perfect` | Definition/Lemma | ★ совершенное поддерево не-счётно |
| `chain/chain_process/chain_in_perf/pick_dir/perf_path_is_T_path` | Definition/Lemma | цепь-путь в совершенном поддереве |
| `path_classification/no_split_implies_enum/not_enum_has_perfect_subset` | Lemma | ★ не-счётность ⟹ совершенное подмножество |
| `process_continuum_hypothesis/no_intermediate_process_type/PCH_structural_dichotomy` | Theorem | ★ дихотомия: счётно XOR совершенно, без промежуточного типа |

**Key lemmas (deep):**

- **`PCH_structural_dichotomy`** - Структурная дихотомия: всякая замкнутая коллекция бинарных процессов либо СЧЁТНА, либо содержит СОВЕРШЕННОЕ (не-счётное) поддерево — промежуточного типа процесса НЕТ. Это РАЗРЕШИМОЕ структурное утверждение (Кантор-Бендиксон-аромат), в отличие от ZFC CH (независимой). Континуум как процессное дерево, не кардинал. _(continuum, dichotomy, perfect-subtree, vein-C)_
- **`not_enum_has_perfect_subset`** - Не-счётная замкнутая коллекция СОДЕРЖИТ совершенное подмножество (построенное как ветвящаяся цепь pick_dir) — конструктивное ядро дихотомии. Перекликается с settheory/CantorBendixsonFull (производная КБ) на процессных деревьях. _(perfect-subset, cantor-bendixson, constructive)_

**Uniqueness - score 4 (synthesis+observation).** Процессная Гипотеза Континуума: замкнутая коллекция бинарных процессов СЧЁТНА XOR содержит совершенное поддерево (структурная дихотомия, без промежуточного типа) — РАЗРЕШИМО, в отличие от независимой ZFC CH; континуум как дерево, не кардинал.
> _Caveat:_ Кантор-Бендиксон/совершенные множества классичны; ЯВНО не ZFC CH (честно помечено). Уникальность — в процессной переформулировке как разрешимой дихотомии, не в решении CH.

---

## #1036 - `src/ProcessDiagonal.v` - score 4 (synthesis+observation)

**Binary processes are not enumerable: the axiom-free flip diagonal**

- **Topic.** The flip (negation) diagonal of an enumeration of binary processes, its involutivity and difference at the diagonal point, binary_processes_not_enumerable, and the not-enumerable closure under supersets/injections.
- **Role.** Uncountability core (vein E). Defines diagonal/binary_processes_not_enumerable. Imports ProcessTypes.
- **Counts.** Qed 20 / Admitted 0 / axioms 0
- **Imports.** ToS ProcessTypes
- **E/R/R.** _Elements:_ перечисления бинарных процессов (nat→BinProcess); диагональ flip. _Roles:_ несчётность как правило (диагональ не в перечислении); flip = самоотрицание. _Rules:_ diagonal n = flip ((enum n) n); отличается от каждого enum n в точке n. _P4:_ несчётность бинарных процессов аксиомо-свободно (то же negb-семя, что cs/halting); BinProcess = nat→bool — процесс, не завершённое множество; БЕЗ Аксиомы Бесконечности.
- **Classical counterpart.** Cantor's diagonal showing 2^N uncountable is classical; NEW is only the axiom-free process form: binary processes (nat->bool) are not enumerable via the flip diagonal, with NO Axiom of Infinity -- the same negb seed as the cs branch.
- **Tags.** uncountability, diagonal, process, vein-E, no-AoI

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `flip/diagonal/flip_involutive/flip_neq/flip_eq_iff` | Definition/Lemma | flip-диагональ и её свойства |
| `diagonal_at_n/diagonal_ne_at_n/diagonal_differs/diagonal_constructive` | Lemma | ★ диагональ отличается от enum n в точке n |
| `binary_processes_not_enumerable/cantor_for_processes/full_collection_not_enumerable/subcollection_not_enumerable` | Theorem | ★ бинарные процессы не перечислимы (Кантор, 0-ax) |
| `not_enum_superset/inject/enum_subset` | Lemma | не-перечислимость замкнута под надмножествами/инъекциями |

**Key lemmas (deep):**

- **`binary_processes_not_enumerable`** - Бинарные процессы (nat→bool) не перечислимы через flip-диагональ, аксиомо-свободно — то же negb-семя, что в cs/HaltingRoleLimit и settheory/CantorTheoremGeneral. Несчётность как ПРАВИЛО над процессами, БЕЗ Аксиомы Бесконечности. Канторовская грань вены E в процессной онтологии. _(uncountability, diagonal, vein-E, no-AoI)_

**Uniqueness - score 4 (synthesis+observation).** Бинарные процессы не перечислимы через flip-диагональ, аксиомо-свободно, БЕЗ Аксиомы Бесконечности — то же negb-семя, что cs/halting и общий Кантор (одна диагональ, вена E).
> _Caveat:_ Диагональ Кантора классична; уникальность — в аксиомо-свободном процессном исполнении (без AoI) + явной унификации с cs/settheory-гранями, не в теореме.

---

## #1037 - `src/ProcessGeneral.v` - score 2 (new-framing)

**General processes: observe, finite prefixes, Cauchy-Q bridge**

- **Topic.** GenProcess with observe and prefixes, process equivalence, the is_cauchy_gen predicate bridging Cauchy-Q sequences to processes, process maps preserving equivalence/Cauchy, and constant processes.
- **Role.** Process-ontology core (vein C). Defines GenProcess/observe. Bridges CauchyReal to processes.
- **Counts.** Qed 16 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ общие процессы GenProcess; их конечные префиксы/наблюдения. _Roles:_ observe как роль наблюдения; процесс как роль (поток, не объект). _Rules:_ prefix/observe; process_equiv; is_cauchy_gen мостит Cauchy-Q. _P4:_ процесс наблюдается КОНЕЧНЫМИ префиксами (Element-стадии); общая абстракция вены C, связывающая Cauchy-Q с потоками.
- **Classical counterpart.** A general 'process = observation stream' with finite-prefix observation and a Cauchy structure is the constructive view of streams/reals; NEW: nothing -- the GenProcess abstraction with observe and Cauchy-Q bridge underlying the process ontology.
- **Tags.** process, observe, cauchy-bridge, vein-C, new-framing

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `GenProcess/observe/prefix/process_map/const_process/prefix_length/nth` | Definition/Lemma | общий процесс, наблюдение, префиксы |
| `process_equiv/refl/sym/trans/process_map_equiv` | Definition/Lemma | эквивалентность процессов |
| `is_cauchy_gen/cauchy_seq_is_gen_process/process_map_cauchy/compose/id` | Definition/Lemma | ★ мост Cauchy-Q ↔ процесс |

**Key lemmas (deep):**

- **`cauchy_seq_is_gen_process`** - Cauchy-Q последовательность ЕСТЬ общий процесс (GenProcess) — мост между анализом (CauchyReal) и процесс-онтологией. Element-сторона: процесс наблюдается конечными префиксами; вена C в общей форме (X = поток наблюдений, не завершённый объект). _(process, cauchy-bridge, vein-C)_

**Uniqueness - score 2 (new-framing).** Общая абстракция процесса (GenProcess/observe) с конечно-префиксным наблюдением и мостом Cauchy-Q ↔ процесс — основа процесс-онтологии (вена C).
> _Caveat:_ Потоки/конструктивные реалы как наблюдения известны (Bishop/коиндукция); вклад — общая GenProcess-абстракция как хаб вены C, не новая теория.

---

## #1038 - `src/ProcessTypes.v` - score 2 (methods)

**Binary processes and pruned trees: the Cantor-space substrate**

- **Topic.** BinProcess (nat->bool) with prefix agreement and decidable equality at depth, BinCollection enumerability/emptiness, PrunedTree with splitting/path/perfect/isolated, and the decidability of tree membership and splitting.
- **Role.** Substrate for ProcessDiagonal/ProcessContinuumHypothesis. Defines BinProcess/BinCollection/PrunedTree. Self-contained.
- **Counts.** Qed 29 / Admitted 0 / axioms 0
- **Imports.** Stdlib
- **E/R/R.** _Elements:_ бинарные процессы BinProcess=nat→bool; pruned-деревья; пути. _Roles:_ коллекции/деревья как роли пространства Кантора; совершенство/изолированность. _Rules:_ bp_prefix/agree; is_splitting/is_path/is_perfect; разрешимость членства в дереве. _P4:_ процессы и деревья конечно-наблюдаемы по префиксам (Element); пространство Кантора как процессный субстрат, не завершённое множество.
- **Classical counterpart.** Cantor space 2^N, pruned trees, perfect sets, paths and enumerability are classical descriptive set theory; NEW: nothing -- the constructive process/tree substrate (BinProcess, PrunedTree, is_perfect) underlying the process-uncountability files.
- **Tags.** cantor-space, pruned-tree, binary-process, decidable, methods

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `BinProcess/bp_eq/bp_prefix/bp_agree/BinCollection/is_enumerable/is_empty` | Definition | бинарные процессы и коллекции |
| `PrunedTree/is_tree/has_left/right/is_splitting/is_path/is_perfect/has_perfect_subset/is_isolated` | Definition | ★ pruned-деревья (совершенство/пути) |
| `bp_agree_*/bp_prefix_*/bp_eq_dec_at_n/tree_mem_dec/has_left_dec/is_splitting_dec` | Lemma | ★ префиксы и разрешимость членства/расщепления |
| `enumerable_empty/singleton_enumerable/enum_union_enum/not_enum_union/paths_extending` | Lemma | перечислимость замкнута под объединением; пути |

**Key lemmas (deep):**

- **`is_splitting_dec`** - Разрешимость расщепления/членства в pruned-дереве над конечными префиксами — Element-сторона субстрата: пространство Кантора наблюдается конечными префиксами, на которых строятся диагональ (ProcessDiagonal) и дихотомия (PCH). Совершенство/изолированность как процессные роли. _(pruned-tree, decidable, cantor-space)_

**Uniqueness - score 2 (methods).** Субстрат пространства Кантора как процессы/pruned-деревья над Q (BinProcess, PrunedTree, разрешимое членство/расщепление) — основа процессной несчётности.
> _Caveat:_ Пространство Кантора/совершенные множества классичны; вклад — конструктивный процессный субстрат под ProcessDiagonal/PCH.

---

## #1039 - `src/Progress.v` - score 2 (methods)

**Progress: a well-typed closed term is a value, steps, or benignly stuck**

- **Topic.** The progress result with a benign-stuck classification, no value has a process/layer type, benign-stuck not a value and no step, the general progress theorem, and per-construct progress (beta/fst/snd/resolve/observe).
- **Role.** Type-theory core (progress). Imports Typing_Expr/Reduction.
- **Counts.** Qed 17 / Admitted 0 / axioms 0
- **Imports.** ToS Typing_Expr, Reduction
- **E/R/R.** _Elements:_ замкнутые типизированные термы. _Roles:_ progress как роль безопасности (значение или шаг); benign-stuck. _Rules:_ well-typed closed ⟹ value ∨ steps ∨ benign-stuck. _P4:_ типизированный замкнутый терм НЕ застревает аварийно (Element): значение, шаг, или benign-stuck (безопасная нередуцируемость).
- **Classical counterpart.** Progress (a well-typed closed term is a value or steps) is the standard progress half of type safety; NEW: nothing -- progress for the ToS language with a 'benign stuck' classification for non-reducible-but-safe forms.
- **Tags.** progress, type-safety, benign-stuck, type-theory, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `is_benign_stuck/progress_result/no_value_has_process_type/layer_type/benign_stuck_no_step` | Definition/Lemma | классификация benign-stuck |
| `progress_general/progress/no_unexpected_stuck/progress_beta/fst_pair/snd_pair/resolve_const/observe_value` | Theorem/Lemma | ★ прогресс по каждой конструкции |

**Key lemmas (deep):**

- **`progress`** - Progress: всякий well-typed замкнутый терм — значение, шагает, или benign-stuck (безопасная нередуцируемость, напр. process/layer-тип). no_unexpected_stuck исключает аварийное застревание. Вторая половина type-safety; вместе с subject_reduction даёт tos_lang_main_theorem. _(progress, type-safety, benign-stuck)_

**Uniqueness - score 2 (methods).** Progress для ToS-языка (well-typed closed ⟹ значение/шаг/benign-stuck, без аварийного застревания).
> _Caveat:_ Progress — стандартная метатеория; вклад — ToS-инстанс с benign-stuck классификацией.

---

## #1047 - `src/RealField.v` - score 2 (methods)

**The field structure of Cauchy reals: multiplication and inverse**

- **Topic.** Multiplication of Cauchy processes (bounded, preserves Cauchy, commutative/associative/distributive), the inverse of a positive (apart-from-zero) real, and the field laws.
- **Role.** Calculus chain (field structure over CauchyReal). Self-contained.
- **Counts.** Qed 17 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; CauchyReal
- **E/R/R.** _Elements:_ Cauchy-процессы; их произведения/обратные. _Roles:_ поле реалов-процессов; обратный для apart-from-zero. _Rules:_ умножение сохраняет Cauchy; обратный для положительного; дистрибутивность. _P4:_ реалы-процессы образуют ПОЛЕ; обратный требует apart-from-zero (конструктивная положительность), не просто ≠0 — честная конструктивная граница.
- **Classical counterpart.** That the constructive reals form a field (multiplication, inverse of an apart-from-zero real) is classical constructive analysis; NEW: nothing -- multiplication/inverse on Cauchy processes preserving Cauchy, the field structure over RealProcess.
- **Tags.** real-field, multiplication, inverse, apartness, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `cauchy_bounded/cauchy_mul/mul_is_cauchy/mul_comm/assoc/one/distrib_l/distrib_r` | Lemma | ★ умножение сохраняет Cauchy, поле-законы |
| `cauchy_inv_is_cauchy/inv_pos/mul_inv_r_pos/pos_add/pos_mul` | Lemma | ★ обратный для положительного (apart-from-zero) |

**Key lemmas (deep):**

- **`cauchy_mul_inv_r_pos`** - Обратный Cauchy-реала существует для ПОЛОЖИТЕЛЬНОГО (apart-from-zero) реала и сохраняет Cauchy — конструктивная полевая структура. Честная граница: обратный требует конструктивной положительности (apart), не классического ≠0, что и есть P4-разрез поля реалов-процессов. _(field, inverse, apartness, constructive)_

**Uniqueness - score 2 (methods).** Полевая структура Cauchy-реалов (умножение/обратный сохраняют Cauchy, обратный для apart-from-zero) над RealProcess.
> _Caveat:_ Конструктивное поле реалов ≈ Бишоп; вклад — Q-исполнение над RealProcess, не новая алгебра.

---

## #1048 - `src/RealPointMetric.v` - score 2 (methods)

**The metric on real points: rp_dist (well-defined, triangle)**

- **Topic.** Cauchy operations (abs/sub) preserving Cauchy, the rp_dist distance well-defined on equivalence classes, nonnegativity, symmetry, dist=0 iff equal, and the triangle inequality.
- **Role.** Real-point (quotient) metric. Imports CauchyReal. Self-contained.
- **Counts.** Qed 18 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; CauchyReal
- **E/R/R.** _Elements:_ реал-точки (классы Cauchy-эквивалентности); расстояние rp_dist. _Roles:_ метрика на реал-точках как роль. _Rules:_ rp_dist корректна на классах; nonneg/sym/triangle/eq_zero_iff. _P4:_ метрика определена на классах Cauchy-процессов (Element); расстояние = Cauchy-процесс модуля разности.
- **Classical counterpart.** The metric on constructive reals (distance well-defined on equivalence classes, nonneg/sym/triangle) is classical constructive analysis; NEW: nothing -- the rp_dist metric on RealPoint (Cauchy-real quotient) with the metric axioms.
- **Tags.** metric, real-point, cauchy, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `cs_abs/cauchy_abs_is_cauchy/rp_dist/cs_rp_dist/rp_dist_compat` | Definition/Lemma | расстояние корректно на классах |
| `rp_dist_nonneg/sym/self_zero/eq_zero_iff/triangle` | Lemma | ★ аксиомы метрики (включая треугольное) |

**Key lemmas (deep):**

- **`rp_dist_triangle`** - Треугольное неравенство для rp_dist на реал-точках (классах Cauchy-эквивалентности), корректно определённое — делает реал-точки метрическим пространством. Element-сторона: метрика = Cauchy-процесс \|x−y\|, согласованный с эквивалентностью. _(metric, real-point, triangle)_

**Uniqueness - score 2 (methods).** Метрика rp_dist на реал-точках (классах Cauchy) — корректна на классах, аксиомы метрики включая треугольное.
> _Caveat:_ Метрика конструктивных реалов классична; вклад — Q-исполнение на фактор-классах.

---

## #1049 - `src/RealPointSetoid.v` - score 1 (exposition)

**Real points as a setoid: well-defined arithmetic on classes**

- **Topic.** RealPoint (the Cauchy-real setoid) with addition and multiplication shown well-defined on equivalence classes.
- **Role.** Real-point setoid (quotient structure). Imports CauchyReal. Self-contained.
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; CauchyReal
- **E/R/R.** _Elements:_ реал-точки как сетоид (фактор по Cauchy-эквивалентности). _Roles:_ RealPoint как сетоид; операции корректны на классах. _Rules:_ add/mul well-defined на классах. _P4:_ реал = класс эквивалентности Cauchy-процессов; арифметика уважает классы (сетоид).
- **Classical counterpart.** Constructive reals as a setoid (quotient by Cauchy equivalence) with well-defined operations is classical; NEW: nothing -- RealPoint as a setoid with addition/multiplication well-defined on classes.
- **Tags.** setoid, real-point, quotient, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `RealPoint/realpoint_add_well_defined/mul_well_defined` | Definition/Lemma | ★ арифметика корректна на классах эквивалентности |

**Key lemmas (deep):**

- **`realpoint_mul_well_defined`** - Умножение реал-точек корректно определено на классах Cauchy-эквивалентности — делает RealPoint настоящим сетоидом (фактор-структурой). Element-сторона: операции уважают эквивалентность процессов; реал = класс, не представитель. _(setoid, real-point, well-defined)_

**Uniqueness - score 1 (exposition).** RealPoint как сетоид: сложение/умножение корректны на классах Cauchy-эквивалентности.
> _Caveat:_ Сетоид конструктивных реалов стандартен; ценность инфраструктурная (фактор-структура).

---

## #1050 - `src/RealPointTopology.v` - score 1 (exposition)

**Topology of real points: open balls well-defined on classes**

- **Topic.** The rp_in_ball predicate well-defined on equivalence classes and the centre lying in its own ball.
- **Role.** Real-point topology (balls). Imports RealPointMetric. Self-contained.
- **Counts.** Qed 4 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; RealPointMetric
- **E/R/R.** _Elements:_ реал-точки; открытые шары rp_in_ball. _Roles:_ топология реал-точек (шары) как роль. _Rules:_ rp_in_ball корректен на классах; центр в своём шаре. _P4:_ топология на фактор-классах (Element); шар = Cauchy-условие на расстояние.
- **Classical counterpart.** Open balls and membership well-defined on the real-point quotient is classical; NEW: nothing -- rp_in_ball well-defined on classes with the centre in its own ball.
- **Tags.** topology, real-point, ball, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `rp_in_ball/well_defined/centre` | Definition/Lemma | ★ шар корректен на классах; центр в своём шаре |

**Key lemmas (deep):**

- **`rp_in_ball_well_defined`** - Принадлежность открытому шару корректно определена на классах реал-точек — основа топологии фактор-пространства. Element-сторона: шар = Cauchy-условие rp_dist < r, согласованное с эквивалентностью. _(topology, ball, well-defined)_

**Uniqueness - score 1 (exposition).** Открытые шары реал-точек корректны на классах (центр в своём шаре) — топология фактор-пространства.
> _Caveat:_ Топология конструктивных реалов стандартна; ценность инфраструктурная.

---

## #1051 - `src/ReasoningConvergence.v` - score 2 (methods)

**Reasoning convergence: pipeline as a contraction to a unique answer**

- **Topic.** A reasoning pipeline contraction, convergence to a unique fixed point, iteration bounds, start-independence, stall analysis (near fixed point), paradigm-shift resets, perturbation, and the confidence gap vanishing.
- **Role.** Convergence application (Regulus bridge). Builds on FixedPoint. Self-contained.
- **Counts.** Qed 19 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; FixedPoint
- **E/R/R.** _Elements:_ конвейер рассуждения как итеративный процесс; уверенность. _Roles:_ сходимость к единственному ответу как role-limit; paradigm shift как сброс. _Rules:_ pipeline contraction ⟹ converges; stall ⟹ near fixpoint; confidence_gap_vanishes. _P4:_ рассуждение = процесс сжатия к единственному ответу (role-limit); итерации актуальны (Element); скорость и независимость от старта явны (FixedPoint).
- **Classical counterpart.** A contraction-based iterative process converging to a unique fixed point (with stall/perturbation analysis) is classical; NEW is only the ToS application: a reasoning pipeline as a contraction converging to a unique answer, with paradigm-shift resets and confidence-gap vanishing.
- **Tags.** reasoning, convergence, contraction, regulus, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `is_pipeline/pipeline_in_range/initial_displacement_bounded/pipeline_converges/limit` | Definition/Lemma | ★ конвейер сходится |
| `convergence_iteration_bound/sufficient_iterations_exist/start_independent/unique_convergence/unique_fixpoint` | Lemma | ★ оценка итераций; единственный стартонезависимый предел |
| `stall_means_near_fixpoint/paradigm_shift_resets/in_range/perturbation/confidence_gap_vanishes` | Lemma | stall/paradigm-shift; уверенность сходится |

**Key lemmas (deep):**

- **`pipeline_unique_convergence`** - Конвейер рассуждения как сжатие сходится к ЕДИНСТВЕННОМУ ответу, независимо от старта (через FixedPoint). Stall = близость к неподвижной точке; paradigm_shift = сброс. role-limit: ответ = предел детерминированного процесса; мост к Regulus (extraction). Confidence_gap_vanishes связывает с уверенностью. _(reasoning, convergence, unique-fixpoint, regulus)_

**Uniqueness - score 2 (methods).** Конвейер рассуждения как сжатие к единственному стартонезависимому ответу (stall/paradigm-shift, confidence gap →0) — мост к Regulus.
> _Caveat:_ Сходимость сжатия классична (Banach); вклад — применение к pipeline рассуждения + Regulus-стыковка, не новая теорема.

---

## #1052 - `src/Reduction.v` - score 2 (methods)

**Operational semantics: deterministic small-step + fuel evaluation**

- **Topic.** The step relation (beta, fst/snd of pairs, resolve), multi_step, a try_step fuel evaluator, eval_fuel terminating, step determinism, value-no-step, and multi-step congruences.
- **Role.** Type-theory core (operational semantics). Defines step/eval_fuel. Imports Expressions. June 2026 wave-4 tail: eval_fuel_terminates was the vacuous exists v, eval_fuel fuel e = v -> valuehood decidability at every fuel stage (via is_value_dec).
- **Counts.** Qed 25 / Admitted 0 / axioms 0
- **Imports.** ToS Expressions
- **E/R/R.** _Elements:_ шаги редукции step; топливная оценка eval_fuel. _Roles:_ малый шаг как роль вычисления; детерминизм. _Rules:_ beta/fst/snd/resolve; step_deterministic; value_no_step. _P4:_ вычисление детерминировано и финитно (eval_fuel terminates); значение не шагает — нормальная форма (Element).
- **Classical counterpart.** Small-step operational semantics (beta, projections), fuel-based evaluation, determinism and value-no-step are standard; NEW: nothing -- the ToS language step relation with deterministic small-step and fuel evaluation that terminates.
- **Tags.** reduction, operational-semantics, deterministic, fuel, type-theory, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `step/multi_step/try_step/eval_fuel/eval_fuel_terminates/eval_fuel_value` | Definition/Lemma | ★ малый шаг и топливная оценка (финитна) |
| `step_deterministic/value_no_step_rel/try_step_none_value/l5_step_deterministic` | Lemma | ★ шаг детерминирован; значение не шагает |
| `multi_step_app_fun/arg/pair_left/fst/snd/step_implies_not_value` | Lemma | конгруэнции multi-step |

**Key lemmas (deep):**

- **`step_deterministic`** - Малый шаг ДЕТЕРМИНИРОВАН (включая l5-резолв) — каждое выражение шагает не более чем одним способом, и eval_fuel финитно завершается. Element-сторона: вычисление = детерминированный финитный процесс; значение = нормальная форма (не шагает). Основа subject reduction/progress. _(operational-semantics, deterministic, fuel)_

**Uniqueness - score 2 (methods).** Операционная семантика ToS-языка: детерминированный малый шаг + финитная топливная оценка (eval_fuel terminates), значение=нормальная форма.
> _Caveat:_ Малошаговая семантика и fuel стандартны; вклад — ToS-инстанс (incl. l5-резолв), основа type-safety.

---

## #1053 - `src/RiemannIntegration.v` - score 2 (methods)

**Riemann integration over Q: sums, telescoping, grid FTC**

- **Topic.** Riemann sums (constant/add/scale/nonneg/monotone/abs-bound), the telescope collapse, a grid FTC (ftc_grid), affine/constant integrals, and linearity/comparison.
- **Role.** Calculus chain (Riemann integration). Self-contained.
- **Counts.** Qed 18 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ Риман-суммы на сетке над Q. _Roles:_ интеграл как предел Риман-сумм; телескоп связывает с FTC. _Rules:_ линейность/монотонность сумм; telescope_collapse; ftc_grid. _P4:_ Риман-сумма конечна (Element-стадия); интеграл — предел процесса; FTC через телескоп с явной ошибкой.
- **Classical counterpart.** Riemann sums, their linearity/monotonicity/telescoping, and a grid FTC are classical; NEW: nothing -- a constructive Q Riemann sum with telescope-collapse FTC and explicit error bounds.
- **Tags.** riemann, integration, FTC, telescope, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `riemann_sum/tele_sum/const/add/scale/nonneg/monotone/abs_bound/width/global_bound` | Definition/Lemma | Риман-суммы и их свойства |
| `telescope_collapse/rs_tele_error_bound/ftc_grid/ftc_constant/affine/nonneg_integral/linearity/comparison` | Lemma | ★ телескоп-коллапс; сеточный FTC |

**Key lemmas (deep):**

- **`ftc_grid`** - Сеточный FTC через телескоп-коллапс: интеграл производной = приращение функции с явной ошибкой над Q. Element-сторона: интеграл = конечная Риман-сумма-процесс; телескопирование делает FTC вычислимым без вещественного предела. _(riemann, FTC, telescope)_

**Uniqueness - score 2 (methods).** Риман-интегрирование над Q (линейность/монотонность сумм, телескоп-FTC) с явными оценками ошибки.
> _Caveat:_ Риман-суммы и FTC классичны; вклад — конструктивное Q-исполнение.

---

## #1054 - `src/Roles.v` - score 4 (synthesis+observation)

**Roles: L4-grounded role assignment, ERR well-formedness, paradox = circular status dependency**

- **Topic.** Role assignment grounded in L4 (no orphans), the E/R/R category separation, deterministic role resolution, status functions, acyclic dependencies, and the unification: circular_dep_is_paradox with Russell/Liar exhibited as circular status dependencies; negb_no_fixpoint the seed.
- **Role.** Core E/R/R well-formedness + paradox unification (vein E). Defines RoleAssignment/ERR_WellFormed. Imports Core_ERR.
- **Counts.** Qed 30 / Admitted 0 / axioms 0
- **Imports.** ToS Core_ERR
- **E/R/R.** _Elements:_ роли, их кандидаты, назначения; статусы; зависимости. _Roles:_ RoleAssignment grounded в L4; ERR_WellFormed; статус как роль. _Rules:_ resolve_role детерминирован; зависимости ацикличны; circular status ⟹ парадокс. _P4:_ роль обоснована L4 (нет сирот); парадокс = циркулярная Status-зависимость s=f(s); negb_no_fixpoint — семя; реификация самоотрицающей роли запрещена.
- **Classical counterpart.** That self-referential paradoxes (Russell, Liar) are fixed points of a negation/self-application is the Tarski-Lawvere insight; NEW is only the in-repo unification: every paradox = a circular STATUS dependency (s = f(s)), blocked by L4-grounded acyclic role assignment, with negb_no_fixpoint the seed.
- **Tags.** roles, ERR, paradox, circular-status, L4, vein-E, well-formedness

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `RoleAssignment/L4_grounded/L4_grounded_implies_no_orphans/ERR_Category/CategorizedComponent/categories_exclusive` | Definition/Lemma | L4-обоснованное назначение ролей; E/R/R-категории исключительны |
| `resolve_role/resolve_role_deterministic/resolve_role_le_all_candidates` | Definition/Lemma | ★ детерминированный резолв роли (минимум кандидатов) |
| `StatusFunction/status_deterministic/status_context_independent/ERR_WellFormed/wf_has_L5` | Definition/Lemma | статус детерминирован; well-formedness |
| `zero_role/successor_role/nat_role_coverage/nat_roles_disjoint/err_category_exhaustive` | Definition/Lemma | конкретные роли nat; покрытие/дизъюнктность |
| `Dependency/deps_acyclic/strongly_acyclic/vertical_deps_acyclic/wf4_no_self_dep` | Definition/Lemma | ацикличные зависимости |
| `circular_status/circular_dep_is_paradox/russell_is_circular_status/liar_is_circular_status/no_fixpoint_no_status/negb_no_fixpoint/well_formed_no_paradox` | Definition/Lemma | ★ парадокс = циркулярный статус; Рассел/Лжец унифицированы; negb-семя |

**Key lemmas (deep):**

- **`circular_dep_is_paradox`** - Унификация: КАЖДЫЙ парадокс = циркулярная Status-зависимость s=f(s). Рассел и Лжец явно опознаны как её инстансы (russell/liar_is_circular_status), а well_formed_no_paradox показывает, что L4-обоснованное ацикличное назначение их исключает. Та же одна диагональ (negb_no_fixpoint), что в cs/ — вена E на уровне ядра ToS. _(paradox, circular-status, unification, vein-E)_
- **`resolve_role_deterministic`** - Резолв роли детерминирован (минимум по кандидатам, как L5) — роль назначается ПРАВИЛОМ, не выбором. Перекликается с веной B (детерминированная селекция): статус/роль фиксированы структурой. _(role-resolution, deterministic, L5)_

**Uniqueness - score 4 (synthesis+observation).** Унификация парадоксов на уровне ролей: всякий парадокс = циркулярная Status-зависимость s=f(s) (Рассел/Лжец — инстансы), исключаемая L4-обоснованным ацикличным назначением; negb_no_fixpoint — семя (вена E).
> _Caveat:_ Парадокс-как-неподвижная-точка известен (Тарский/Ловер); уникальность — в систематической привязке к E/R/R-статусам и well-formedness, не в новизне идеи.

---

## #1055 - `src/RoundingSafety.v` - score 2 (methods)

**Rounding safety: sound interval widening over Q**

- **Topic.** Interval widening (strictly larger, preserves containment), rounding-safe bounds, IBP rounding steps, CROWN-affine rounding, and double-rounding error -- sound numeric verification.
- **Role.** Verified numerics (interval rounding). Pairs with PInterval_CROWN. Self-contained.
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ интервалы; расширение (widening). _Roles:_ округление-безопасность как роль (расширение сохраняет вложение). _Rules:_ widen_strictly_larger; rounding_safe; interval_subset_widened. _P4:_ расширение интервала СОХРАНЯЕТ вложение (Element): округление безопасно (содержит истину), не теряет корректность.
- **Classical counterpart.** Sound interval rounding (widening preserves containment, idempotent up to error) for verified numerics is standard interval arithmetic; NEW: nothing -- a constructive Q widening with rounding-safe bounds tying to the CROWN neural-net verification.
- **Tags.** rounding-safety, interval-arithmetic, CROWN, verified-numerics, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `in_interval/widen_lo/hi/in_widened/widen_strictly_larger/interval_subset_widened` | Definition/Lemma | ★ расширение сохраняет вложение |
| `rounding_safe/ibp_safe/rounding_step/crown_affine_rounding/double_rounding_error` | Lemma | ★ округление безопасно (CROWN-аффинное) |

**Key lemmas (deep):**

- **`rounding_safe`** - Расширение интервала (widening) СОХРАНЯЕТ вложение истинного значения — округление безопасно (over-approximation). Element-сторона верифицированной численности: округление никогда не теряет корректность, лишь огрубляет границы; основа CROWN-верификации нейросетей (PInterval_CROWN). _(rounding-safe, interval, widening)_

**Uniqueness - score 2 (methods).** Безопасное расширение интервалов над Q (widening сохраняет вложение, CROWN-аффинное округление) — корректная верифицированная численность.
> _Caveat:_ Интервальная арифметика/округление стандартны; вклад — Q-исполнение для CROWN-верификации нейросетей.

---

## #1056 - `src/SchroederBernstein_ERR.v` - score 3 (new-framing)

**Schroeder-Bernstein constructively: back-and-forth via rooted depth**

- **Topic.** Partial inverses of two injections, the B-rooted depth classification of chains, the explicit bijection h built by the back-and-forth chain separation, and its injectivity/surjectivity.
- **Role.** Cardinality (Schroeder-Bernstein, constructive). Pairs with settheory/CardinalityWithoutChoice. Self-contained.
- **Counts.** Qed 16 / Admitted 0 / axioms 0
- **Imports.** Stdlib
- **E/R/R.** _Elements:_ две инъекции f,g; цепи и их корневая глубина. _Roles:_ биекция h как роль, построенная back-and-forth; B-rooted глубина классифицирует цепи. _Rules:_ chain_separation по корню; h инъективна и сюръективна. _P4:_ Шрёдер-Бернштейн КОНСТРУКТИВНО (явная h через корневую глубину цепей), без выбора — Element-сторона кардинальности.
- **Classical counterpart.** The Schroeder-Bernstein theorem (mutual injections => bijection) is classical; NEW is only the constructive back-and-forth (chain/rooted-depth) form over the ToS setting, with the bijection h built explicitly, no choice.
- **Tags.** schroeder-bernstein, cardinality, back-and-forth, no-AC, new-framing

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `f_inv/g_inv/f_inv_spec/g_inv_spec/no_f_preimage/no_g_preimage` | Definition/Lemma | частичные обратные инъекций |
| `B_rooted_depth/B_rooted/depth_A_to_B/B_to_A/g_preserves_B_rooted/chain_separation` | Definition/Lemma | ★ классификация цепей по корневой глубине |
| `h/h_injective/h_surjective/Schroeder_Bernstein` | Definition/Theorem | ★ явная биекция h (инъективна+сюръективна) |

**Key lemmas (deep):**

- **`Schroeder_Bernstein`** - Шрёдер-Бернштейн с ЯВНОЙ биекцией h, построенной back-and-forth через корневую глубину цепей (B_rooted_depth) — конструктивно, без выбора. Element-сторона кардинальности; пара к settheory/CardinalityWithoutChoice (где это antisymmetry без AC). _(schroeder-bernstein, back-and-forth, constructive, no-AC)_

**Uniqueness - score 3 (new-framing).** Шрёдер-Бернштейн конструктивно: явная биекция h через корневую глубину цепей (back-and-forth), без выбора — Element-сторона кардинальности.
> _Caveat:_ Шрёдер-Бернштейн классичен и конструктивизируем; вклад — явное back-and-forth исполнение в ToS-сеттинге, пара к no-AC кардинальности.

---

## #1057 - `src/SeriesConvergence.v` - score 2 (methods)

**Series convergence over Q: geometric, comparison, absolute**

- **Topic.** Qpow machinery (monotone, vanishing), Bernoulli's inequality, the geometric series Cauchy/limit, the comparison test, absolute convergence, and nonneg upper bounds.
- **Role.** Calculus chain (series). Self-contained.
- **Counts.** Qed 22 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ ряды; Qpow степени; частичные суммы. _Roles:_ сходимость как role-limit; comparison/absolute как критерии. _Rules:_ Qpow_vanish; geometric_series_cauchy; comparison_test. _P4:_ ряд = процесс частичных сумм (Element); геометрический ряд сходится с явной скоростью (Qpow_vanish).
- **Classical counterpart.** Geometric series, the comparison test, absolute convergence and Bernoulli's inequality are classical; NEW: nothing -- a constructive Q treatment (Qpow machinery, geometric Cauchy, comparison/absolute convergence).
- **Tags.** series, geometric, comparison-test, convergence, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `Qpow/nonneg/monotone_dec/vanish/cauchy/limit_zero/bernoulli_ineq` | Definition/Lemma | ★ Qpow убывает к нулю; неравенство Бернулли |
| `geometric_sum_identity/partial_sum_bound/geometric_series_cauchy/comparison_test/absolute_convergence/series_limit/geometric_limit` | Lemma | ★ геом. ряд Cauchy; comparison/absolute |

**Key lemmas (deep):**

- **`geometric_series_cauchy`** - Геометрический ряд сходится (Cauchy) с явной скоростью (Qpow_vanish) над Q — базовый сходящийся ряд, на котором стоят comparison/absolute тесты и PowerSeries. Element-сторона: частичные суммы — процесс, скорость вычислима. _(geometric-series, comparison-test, cauchy)_

**Uniqueness - score 2 (methods).** Сходимость рядов над Q (геометрический Cauchy, comparison, absolute, Бернулли) конструктивно.
> _Caveat:_ Тесты сходимости классичны; вклад — конструктивное Q-исполнение.

---

## #1068 - `src/ShrinkingIntervals_ERR.v` - score 4 (synthesis+observation)

**Uncountability of [0,1] cap Q via adaptive ternary trisection (axiom-free, no AoI)**

- **Topic.** The flagship uncountability file (167 Qed): bisection and trisection interval processes over Q, the Archimedean/pow2/pow3 machinery, a smart trisection that adaptively avoids each enumerated real E_n keeping a 2*delta < w/3 gap, the diagonal interval process Cauchy and in [0,1], and unit_interval_uncountable_trisect_v2.
- **Role.** Uncountability FLAGSHIP (vein E). Exports unit_interval_uncountable_trisect_v2 (used by PCH). Only the classic axiom. Invariant-heavy (~3600 lines).
- **Counts.** Qed 167 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; ToS_Axioms (classic)
- **E/R/R.** _Elements:_ вложенные интервалы над Q; трисекции; перечисление E реалов-процессов. _Roles:_ несчётность как ПРАВИЛО (диагональ-интервал избегает каждого E_n); трисекция как роль уклонения. _Rules:_ smart_trisect выбирает треть, держа зазор 2*delta < w/3 от E_n; диагональ-интервал — Cauchy в [0,1]. _P4:_ несчётность БЕЗ завершённой ℝ и БЕЗ Аксиомы Бесконечности: диагональ — конечно-стадийный процесс уклонения над Q; «избегает каждого перечисленного» — правило, не объект.
- **Classical counterpart.** Cantor's uncountability of [0,1] (a diagonal avoiding every enumerated point) is classical and usually phrased via decimal digits and the Axiom of Infinity; NEW is the ternary nested-interval form: a TRISECTION that adaptively avoids each enumerated real, axiom-free over Q (no completed real line, no AoI), with a synced 2*delta < w/3 invariant.
- **Tags.** uncountability, trisection, no-AoI, vein-E, diagonal, cauchy, flagship

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `RealProcess/is_Regular_Cauchy/IntervalProcess/pow2/pow3/pow10/Archimedean*/width_shrinks` | Definition/Lemma | процессы, регулярность Коши, архимедова машина (степени 2/3/10) |
| `BisectionState/bisect_*/bisect_is_Cauchy/midpoint_in_interval*` | Definition/Lemma | бисекционный процесс (Cauchy, вложенность) |
| `TrisectChoice/trisect_left/middle/right/trisect_*_valid/nested/smart_trisect_choice` | Definition/Lemma | ★ трисекция и умный выбор трети |
| `avoid_E_adaptive/diagonal_intervals_adaptive/E_n_excluded_from_next_interval*/diagonal_adaptive_in_interval` | Definition/Lemma | ★ адаптивное уклонение от E_n с зазором |
| `trisect_delta/third_width_gt_6_delta/gap_gt_third_implies_ge_6delta/trisect_iter_v2/diagonal_trisect_v2` | Lemma/Definition | ★ синхро-инвариант зазора 2*delta < w/3 |
| `diagonal_trisect_v2_is_Cauchy/in_unit/differs_from_E_n/unit_interval_uncountable_trisect_v2` | Lemma/Theorem | ★ диагональ Cauchy в [0,1], отличается от каждого E_n ⟹ несчётность |

**Key lemmas (deep):**

- **`unit_interval_uncountable_trisect_v2`** - [0,1]∩Q несчётно через АДАПТИВНУЮ ТЕРНАРНУЮ трисекцию: на каждом шаге диагональ-интервал выбирает треть, держащую зазор 2*delta < w/3 от перечисленного E_n, оставаясь Cauchy в [0,1]. Аксиомо-свободно (только classic), БЕЗ завершённой ℝ и БЕЗ Аксиомы Бесконечности. Ключевое решение: трисекция (не digit-диагональ) обходит нестабильность Qfloor над Q — вена E без онтологического долга. _(uncountability, trisection, no-AoI, vein-E)_
- **`E_n_excluded_from_next_interval_adaptive`** - Каждый перечисленный E_n ИСКЛЮЧАЕТСЯ из следующего интервала с явным зазором (6*delta) — несущий инвариант, делающий уклонение строгим. Локализует, ПОЧЕМУ диагональ отличается от всякого E_n: не предельное свойство, а конечно-проверяемый зазор на каждом шаге. _(exclusion, gap-invariant, adaptive)_

**Uniqueness - score 4 (synthesis+observation).** Несчётность [0,1]∩Q через адаптивную ТЕРНАРНУЮ трисекцию, аксиомо-свободно (только classic), БЕЗ завершённой ℝ и Аксиомы Бесконечности; трисекция обходит нестабильность Qfloor цифровой диагонали — несчётность как процесс-правило (вена E).
> _Caveat:_ Несчётность Кантора классична; уникальность — в трисекционном Q-исполнении без AoI/без ℝ + честном обходе digit-нестабильности, не в самой теореме. Огромный (167 Qed) инвариант-тяжёлый файл.

---

## #1069 - `src/SoftmaxProbability.v` - score 1 (exposition)

**Softmax over Q: probability bounds and monotonicity**

- **Topic.** A Q sum (nonneg, positive), order-preserving list comparison, the softmax probability soundness (bounds), and consistency of probability bounds.
- **Role.** ML/probability (softmax over Q). Self-contained.
- **Counts.** Qed 14 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith List
- **E/R/R.** _Elements:_ логиты; softmax-вероятности. _Roles:_ softmax как роль нормализации в распределение; монотонность. _Rules:_ Qsum положительна; softmax_probability_sound (границы). _P4:_ softmax над Q даёт корректное распределение (Element); границы вероятностей проверяемы.
- **Classical counterpart.** That softmax outputs are nonnegative, sum to 1 and are order-preserving (monotone in logits) is standard; NEW: nothing -- a constructive Q softmax with probability-bounds soundness and monotonicity.
- **Tags.** softmax, probability, ML, exposition

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `Qsum/app/nonneg/positive/list_le/length/nth/nonneg` | Definition/Lemma | Q-сумма и порядок списков |
| `cross_mul_lower/upper/softmax_probability_sound/probability_bounds_consistent` | Lemma | ★ корректность softmax-вероятностей (границы) |

**Key lemmas (deep):**

- **`softmax_probability_sound`** - Softmax над Q даёт корректные вероятности (в [0,1], согласованные границы) — Element-сторона ML над точной рациональной арифметикой. Монотонность по логитам сохраняет порядок. Связь с InfoLayer/ML-применениями репо. _(softmax, probability-bounds, ML)_

**Uniqueness - score 1 (exposition).** Softmax над Q (корректные вероятностные границы, монотонность по логитам).
> _Caveat:_ Свойства softmax стандартны; ценность — точная Q-формализация для ML-применений.

---

## #1070 - `src/Soundness.v` - score 3 (synthesis+observation)

**Soundness: typing blocks paradox -- Russell and Liar are untypable**

- **Topic.** Typing implies the level hierarchy, P2 and no-self-membership, hence safety; Russell's set and the Liar are untypable; circular dependencies blocked; preservation under P3/subsumption/weakening; type uniqueness; canonical forms.
- **Role.** Type-theory capstone (paradox blocking via typing, vein E). Imports Typing_Expr/Core_ERR.
- **Counts.** Qed 22 / Admitted 0 / axioms 0
- **Imports.** ToS Typing_Expr, Core_ERR
- **E/R/R.** _Elements:_ типизированные термы; парадоксальные конструкции (Рассел/Лжец). _Roles:_ типизация ⟹ безопасность; парадоксы как НЕтипизуемые. _Rules:_ typing ⟹ level hierarchy + no-self-membership; russell_untypable; liar_untypable. _P4:_ ★ Рассел и Лжец НЕТИПИЗУЕМЫ — система типов блокирует парадокс структурно (вена E); циркулярные зависимости заблокированы типизацией.
- **Classical counterpart.** That a sound type system blocks paradoxical self-reference is the design goal; NEW is only the ToS theorems: typing implies level hierarchy/no-self-membership, Russell and the Liar are UNTYPABLE, circular dependencies blocked by typing.
- **Tags.** soundness, paradox-blocking, russell-untypable, type-safety, vein-E

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `typing_implies_level_hierarchy/P2/no_self_membership/safe` | Lemma | ★ типизация ⟹ иерархия + нет самочленства ⟹ безопасность |
| `russell_untypable/liar_untypable/circular_dep_blocked/no_self_reference_by_P1` | Theorem/Lemma | ★ Рассел/Лжец НЕтипизуемы; циркулярность заблокирована |
| `preservation_under_P3/subsumption/weakening/type_uniqueness_P3/canonical_form/soundness_all_levels` | Lemma | preservation; уникальность типа; каноничность |

**Key lemmas (deep):**

- **`russell_untypable`** - Множество Рассела и парадокс Лжеца НЕТИПИЗУЕМЫ в ToS-языке — система типов блокирует парадокс СТРУКТУРНО (через level hierarchy + no-self-membership), а не патчем. Та же одна диагональ/самоотрицание (вена E), что в Roles.circular_dep_is_paradox и cs/. Соединяет type-safety с парадокс-блокировкой. _(soundness, russell-untypable, paradox-blocking, vein-E)_

**Uniqueness - score 3 (synthesis+observation).** Типизация ToS-языка СТРУКТУРНО блокирует парадокс: Рассел и Лжец НЕтипизуемы (через иерархию+no-self-membership), циркулярные зависимости заблокированы — связь type-safety с веной E.
> _Caveat:_ Типы против парадоксов — классическая идея (Рассел-Уайтхед); вклад — машинная демонстрация untypability в ToS-языке + стыковка с E/R/R-парадокс-унификацией, не новая логика.

---

## #1780 - `src/SubjectReduction.v` - score 2 (methods)

**Subject reduction: type preservation under step/multi-step/fuel**

- **Topic.** Type preservation for each step rule (beta/fst/snd/resolve/observe/layer), the congruence (xi) cases, subject_reduction, multi_step_preservation, and eval_fuel_preservation.
- **Role.** Type-theory core (preservation). Imports Typing_Expr/Reduction.
- **Counts.** Qed 17 / Admitted 0 / axioms 0
- **Imports.** ToS Typing_Expr, Reduction
- **E/R/R.** _Elements:_ типизированные термы; их редукты. _Roles:_ сохранение типа как роль безопасности (preservation). _Rules:_ e:T и e→e' ⟹ e':T (по каждому правилу шага). _P4:_ тип СОХРАНЯЕТСЯ при редукции (preservation) — половина type-safety; multi-step и fuel сохраняют тип.
- **Classical counterpart.** Subject reduction / type preservation (e:T and e->e' imply e':T) is the standard preservation half of type safety; NEW: nothing -- preservation for the ToS language step relation, multi-step and fuel evaluation.
- **Tags.** subject-reduction, preservation, type-safety, type-theory, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `step_beta_type/fst/snd/resolve/observe_nat/layer_type/xi_app_fun/arg_type` | Lemma | сохранение типа по каждому правилу шага |
| `subject_reduction/multi_step_preservation/eval_fuel_preservation/preservation_closed/reduces_to_value_preserves_type` | Theorem/Lemma | ★ сохранение типа (шаг/multi-step/fuel) |

**Key lemmas (deep):**

- **`subject_reduction`** - Subject reduction (e:T и e→e' ⟹ e':T) для ToS-языка — preservation-половина type-safety. Через substitution_preserves_typing (для beta) и инверсии типизации. Multi-step и eval_fuel наследуют сохранение. Element-сторона: типы устойчивы к вычислению. _(subject-reduction, preservation, type-safety)_

**Uniqueness - score 2 (methods).** Subject reduction (сохранение типа при шаге/multi-step/fuel) для ToS-языка — preservation-половина type-safety.
> _Caveat:_ Preservation — стандартная метатеория; вклад — ToS-инстанс, не новый результат.

---

## #1781 - `src/Subtyping.v` - score 2 (methods)

**Subtyping: subsystems, subsumption, Pi-contravariance / Sigma-covariance**

- **Topic.** The subsystem relation via embeddings (reflexive, transitive), subsumption, embedding preserves criterion/level, weak antisymmetry, Pi contravariant in domain, Sigma covariant, and a concrete nat-gt10 <: nat-gt5 example.
- **Role.** Type-theory (subtyping). Imports SystemMorphism. Self-contained.
- **Counts.** Qed 20 / Admitted 0 / axioms 0
- **Imports.** ToS SystemMorphism
- **E/R/R.** _Elements:_ подсистемы (вложения); subsumption. _Roles:_ subtyping как роль порядка систем; вариантность Pi/Sigma. _Rules:_ is_subsystem рефлексивен/транзитивен; Pi контравариантен, Sigma ковариантен. _P4:_ subtyping = вложение подсистем (Element); вариантность уважает направление стрелок.
- **Classical counterpart.** Subtyping via subsystem embeddings, subsumption, reflexivity/transitivity, and Pi-contravariance/Sigma-covariance is standard; NEW: nothing -- the ToS subsystem order with embedding-based subtyping and variance.
- **Tags.** subtyping, subsystem, variance, type-theory, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `is_subsystem/refl/trans/subsumption/embedding_preserves_criterion/preserves_level` | Definition/Lemma | ★ порядок подсистем + subsumption |
| `iso_implies_subsystem/antisym_weak/pi_contravariant_domain/sigma_covariant` | Lemma | ★ Pi контравариантен, Sigma ковариантен |
| `nat_gt10_subsystem_nat_gt5/gt10_to_gt5/embeds_in_gt5` | Lemma | конкретный пример подтипа |

**Key lemmas (deep):**

- **`pi_contravariant_domain`** - Pi контравариантен в области, Sigma ковариантен — стандартная вариантность субтипинга, выведенная из вложений подсистем. Element-сторона: subtyping = embedding, вариантность следует из направления морфизмов. Конкретно nat-gt10 <: nat-gt5. _(subtyping, variance, subsystem)_

**Uniqueness - score 2 (methods).** Субтипинг через вложения подсистем (subsumption, Pi-контравариантность, Sigma-ковариантность).
> _Caveat:_ Субтипинг и вариантность стандартны; вклад — ToS-инстанс через подсистемы.

---

## #1784 - `src/SystemCategory.v` - score 2 (methods)

**The category of ToS systems: SystemCat with initial/terminal**

- **Topic.** Systems at a level as objects, SystemMorphisms as arrows, SystemCat as a Category, iso iff isomorphism, embedding=>mono, surjection=>epi, the empty system initial, the unit terminal, and L1 vacuity.
- **Role.** Category-of-systems core. Defines SystemCat/empty_system/unit_system. Imports SystemMorphism.
- **Counts.** Qed 29 / Admitted 0 / axioms 0
- **Imports.** ToS SystemMorphism, Core_ERR
- **E/R/R.** _Elements:_ системы на уровне (объекты); морфизмы систем (стрелки). _Roles:_ SystemCat как категория; начальный/терминальный как универсальные роли. _Rules:_ композиция/тождество; iso ⟺ изоморфизм; пустая начальна, unit терминальна. _P4:_ системы образуют категорию; L1 вакуумен (нет системы с witness на L1) — типовая граница.
- **Classical counterpart.** Building a category (objects, morphisms, identity/composition, mono/epi, initial/terminal, iso) is standard; NEW is only the instance: ToS systems at a level form a category SystemCat with an initial empty and terminal unit, and the L1-vacuity observation.
- **Tags.** category, system-category, initial-terminal, methods

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `SystemCat/SystemCat_valid/comp_is_compose/id_is_id/iso_iff_isomorphism` | Definition/Lemma | ★ категория систем |
| `embedding_implies_mono/surjection_implies_epi/iso_compose/comp_mono/comp_epi` | Lemma | вложение=моно, сюръекция=эпи |
| `empty_system/empty_is_initial/unit_system/unit_is_terminal/initial_unique/terminal_unique` | Definition/Lemma | ★ начальный (пустой) и терминальный (unit) объекты |
| `no_system_at_L1_with_witness/L1_criterion_absurd/SystemCat_L1_vacuous/LS_has_initial_and_terminal` | Lemma | L1-вакуумность |

**Key lemmas (deep):**

- **`empty_is_initial`** - Пустая система начальна, unit терминальна в SystemCat — даёт категории систем универсальные объекты. Element-сторона: ToS-системы — настоящая категория, на которой строятся функторы уровней (LevelFunctors) и сопряжение (LevelAdjunction). _(category, initial, terminal)_

**Uniqueness - score 2 (methods).** Категория ToS-систем SystemCat (mono/epi, начальный пустой/терминальный unit, iso⟺изоморфизм) + наблюдение L1-вакуумности.
> _Caveat:_ Построение категории стандартно; вклад — инстанс для ToS-систем как основа функторов/сопряжения уровней.

---

## #1785 - `src/SystemMorphism.v` - score 1 (exposition)

**System morphisms: identity, composition, embeddings, isomorphisms**

- **Topic.** SystemMorphism with identity/composition (associative, unital), morphism equality, embeddings (injective) and surjections, isomorphism pairs and their symmetry, and predicate equivalence under iso.
- **Role.** Foundation of SystemCat. Defines SystemMorphism/compose_morphism. Imports Core_ERR.
- **Counts.** Qed 17 / Admitted 0 / axioms 0
- **Imports.** ToS Core_ERR
- **E/R/R.** _Elements:_ морфизмы систем; их композиции. _Roles:_ вложение (инъекция)/сюръекция/изоморфизм как роли морфизма. _Rules:_ композиция ассоциативна/унитальна; iso-пара симметрична. _P4:_ морфизмы конечно-структурны; изоморфизм = взаимное вложение+сюръекция.
- **Classical counterpart.** Structure-preserving maps with identity/composition, embeddings (mono), surjections (epi) and isomorphism pairs are standard; NEW: nothing -- the morphism layer the system category is built on.
- **Tags.** morphism, category, embedding, isomorphism, exposition

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `SystemMorphism/id_morphism/compose_morphism/morphism_eq/refl/sym/trans/compose_assoc/id_left/id_right` | Definition/Lemma | морфизмы, композиция (ассоц./унит.) |
| `is_embedding/is_surjection/embedding_injective/compose/surjection_compose/id_embedding` | Definition/Lemma | вложения и сюръекции замкнуты под композицией |
| `is_iso_pair/is_isomorphism/iso_pair_symmetric/iso_symmetric/iso_pair_implies_embedding/surjection/iso_pair_predicate_equiv` | Definition/Lemma | ★ изоморфизм-пары и их свойства |

**Key lemmas (deep):**

- **`compose_assoc`** - Композиция морфизмов систем ассоциативна и унитальна — категорные законы, делающие SystemMorphism основой SystemCat. Вложения/сюръекции замкнуты под композицией, изоморфизм = взаимное вложение+сюръекция. _(morphism, composition, category-laws)_

**Uniqueness - score 1 (exposition).** Морфизмы систем (композиция ассоц./унит., вложения=моно, сюръекции=эпи, изоморфизм-пары) — основа категории систем.
> _Caveat:_ Стандартный морфизменный слой; ценность инфраструктурная (под SystemCat).

---

## #1786 - `src/TaylorSeries.v` - score 2 (methods)

**Taylor approximation over Q: remainder bound, convexity, second-derivative test**

- **Topic.** First-order Taylor via FTC, the remainder bound, IBP-based remainder decomposition, Taylor convexity/concavity, the local-min (second-derivative) test, and the sandwich for constant-derivative.
- **Role.** Calculus chain (Taylor). Self-contained.
- **Counts.** Qed 18 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ функции и производные; Тейлор-остаток. _Roles:_ Тейлор-приближение как роль локальной аппроксимации; остаток как роль ошибки. _Rules:_ taylor1_ftc; remainder bound; convexity из 2-й производной. _P4:_ Тейлор в эпсилон-форме над Q (Element): приближение с явным остатком, не бесконечный ряд.
- **Classical counterpart.** Taylor's theorem with remainder, the remainder bound, convexity/concavity from the second derivative and the second-derivative test are classical; NEW: nothing -- a constructive Q first-order Taylor with explicit remainder bounds.
- **Tags.** taylor, remainder, convexity, calculus, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `udiff_const/bmt/taylor_remainder_udiff/taylor1_ftc/bound/affine/quadratic` | Lemma | ★ Тейлор-1 с остатком |
| `taylor_convexity/concavity/taylor_local_min/sandwich_const_deriv/sandwich` | Lemma | ★ выпуклость/тест второй производной |

**Key lemmas (deep):**

- **`taylor1_bound`** - Тейлор первого порядка с явной границей остатка над Q — Element-сторона: приближение функции линейным членом + контролируемая ошибка (не бесконечный ряд). Выпуклость и тест второй производной (taylor_local_min) выводятся отсюда. _(taylor, remainder-bound, convexity)_

**Uniqueness - score 2 (methods).** Тейлор-приближение над Q (остаток, выпуклость, тест второй производной) с явными границами.
> _Caveat:_ Теорема Тейлора классична; вклад — конструктивное Q-исполнение первого порядка.

---

## #1787 - `src/TernaryRepresentation_ERR.v` - score 2 (methods)

**Ternary representation over Q: digits, partial sums, structural separation**

- **Topic.** Ternary expansions, partial sums bounded in [0,1], digit extraction via Qfloor/Qfrac, the approximation error formula, structural digit separation, and the ternary-flip diagonal pieces.
- **Role.** Ternary substrate for DiagonalArgument_ERR. Self-contained.
- **Counts.** Qed 54 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ троичные разложения; цифры; частичные суммы. _Roles:_ троичное представление как роль кодирования реала в [0,1]. _Rules:_ partial_sum в [0,1]; extract_digit через Qfloor; structural separation. _P4:_ троичное представление — конечно-стадийный процесс над Q (Element); цифры извлекаются разрешимо.
- **Classical counterpart.** Ternary (base-3) positional representation of reals in [0,1] and digit extraction are classical; NEW: nothing -- the ternary machinery (partial sums, digit extraction via Qfloor, structural digit separation) over Q, supporting the digit-diagonal.
- **Tags.** ternary, representation, qfloor, digit-separation, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `pow3/TernaryExp/partial_sum/to_Q/term_bound/partial_sum_in_unit/tail_bound_strong` | Definition/Lemma | троичные суммы в [0,1] |
| `Qfloor/Qfrac/extract_digit/extract_digit_range/from_Q_raw/floor_approx_bound/extracted_equals_floor_exists` | Definition/Lemma | ★ извлечение цифр через Qfloor/Qfrac |
| `digits_differ_by_two/structural_digit_separation/ternary_flip/diagonal_digit/diagonal_Q_separation_structural` | Lemma | ★ структурное разделение цифр; flip |

**Key lemmas (deep):**

- **`structural_digit_separation`** - Структурное разделение троичных цифр (различие ≥1 в позиции) над Q — несущий механизм цифровой диагонали (DiagonalArgument_ERR). Element-сторона: цифры извлекаются разрешимо через Qfloor/Qfrac, разделение конечно-проверяемо. _(ternary, digit-separation, qfloor)_

**Uniqueness - score 2 (methods).** Троичное представление над Q (частичные суммы в [0,1], извлечение цифр через Qfloor/Qfrac, структурное разделение) — субстрат цифровой диагонали.
> _Caveat:_ Позиционное представление классично; вклад — конструктивный Q-субстрат, замещённый трисекцией для несчётности.

---

## #1788 - `src/TestNode.v` - score 0 (infrastructure)

**Test/scratch node (0 Qed)**

- **Topic.** A test or scratch file; no proved theorems.
- **Role.** Test/scratch. 0 Qed.
- **Counts.** Qed 0 / Admitted 0 / axioms 0
- **Imports.** 
- **E/R/R.** _Elements:_ тестовый узел. _Roles:_ тест как роль инфраструктуры. _Rules:_ scratch/тест. _P4:_ только тест; 0 теорем.
- **Classical counterpart.** A test/scratch file is infrastructure; NEW: nothing (0 Qed).
- **Tags.** test, scratch, infrastructure

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `(test/scratch only)` | Test | тест, без доказанных теорем |

**Key lemmas (deep):**


**Uniqueness - score 0 (infrastructure).** Тестовый/scratch-файл (0 теорем).
> _Caveat:_ Инфраструктура/тест; не содержит результатов.

---

## #1789 - `src/TheoryOfSystems_Core_ERR.v` - score 5 (synthesis+observation)

**The ToS core: Level hierarchy, P1-P4 principles, paradox blocking, the E/R/R FunctionalSystem**

- **Topic.** The Level inductive (L1/LS), level_lt well-founded and irreflexive, P1 (no self-membership), the Criterion/System types, P3 intensional separation, the L5 deterministic resolve, and the FunctionalSystem record bundling Elements/Roles/Rules. Russell and Cantor blocked structurally.
- **Role.** THE foundational hub of the whole repo (53+ downstream files). Defines Level/System/Criterion/ElemOf. Imports ToS_Axioms.
- **Counts.** Qed 36 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; ToS_Axioms
- **E/R/R.** _Elements:_ Level (L1/LS); System; Criterion; элементы ElemOf на уровне. _Roles:_ уровни как роли иерархии; Criterion как роль-различитель; FunctionalSystem собирает E/R/R. _Rules:_ level_lt фундирован/иррефлексивен; P1 нет самочленства; P3 интенсиональная сепарация; L5_resolve детерминированный минимум. _P4:_ иерархия конечно-актуальна; самочленство/Рассел/Кантор блокированы НА ТИПОВОМ уровне (level_lt_irrefl), не патчем — категориальная защита от реификации.
- **Classical counterpart.** A cumulative type/level hierarchy blocking self-membership (Russell) is the standard set-theoretic fix (ranks / Russell-Whitehead types); NEW is only the E/R/R framing: a minimal Level inductive with P1 (no self-membership), P3 (intensional separation) and the L5 deterministic resolve, paradoxes blocked at the TYPE level (level_lt_irrefl), 0-axiom.
- **Tags.** core, ERR, level-hierarchy, paradox-blocking, P1, P3, L5, foundation

**Lemmas (8):**

| name | kind | role |
|---|---|---|
| `Level/L2/L3/level_lt/level_depth` | Inductive/Definition | иерархия уровней и её порядок |
| `level_lt_irrefl/trans/level_lt_depth/L1_lt_L2/L2_lt_L3` | Lemma | ★ порядок фундирован и иррефлексивен (блок самочленства) |
| `P1_no_self_membership/russell_paradox_blocked/cantor_paradox_blocked_v1/cantor_no_system_of_all_L2_systems` | Theorem | ★ P1 + Рассел/Кантор блокированы структурно |
| `Criterion/P2_valid/P2_always_holds/System/example_nat_system` | Definition/Lemma | критерии, P2, системы |
| `P3_different_predicates/systems_intensionally_equal/distinguishable_by_predicate/L4_principle/L4_equiv_Difference` | Lemma | ★ P3 интенсиональная сепарация; L4 = различие |
| `L5_resolve/L5_resolve_le_all/le_default/StructuredSystem/element_at/PositionedAccess/positioned_access_unique` | Definition/Lemma | ★ L5 детерминированный резолв; позиционный доступ |
| `FunctionalSystem/get_Elements/get_Roles/get_Rules/NatOrderFunctionalSystem` | Definition | ★ E/R/R-запись (Элементы/Роли/Правила) |
| `ERR_Process/ERR_CauchyProcess/err_cauchy_equiv*/EnumerationFunctionalSystem/err_self_reference_blocked` | Definition/Lemma | процессные E/R/R-системы; самоссылка блокирована |

**Key lemmas (deep):**

- **`russell_paradox_blocked`** - Парадокс Рассела блокирован НА ТИПОВОМ уровне: level_lt_irrefl делает самочленство невыразимым, а не запрещённым патчем. Та же структурная защита покрывает Кантор (cantor_no_system_of_all_L2_systems). Ядро вены E на уровне самой системы типов ToS. _(russell, paradox-blocking, structural, vein-E)_
- **`FunctionalSystem`** - E/R/R как формальная запись: FunctionalSystem связывает get_Elements/get_Roles/get_Rules в один объект — структурная триада ToS (WHAT/WHY/HOW) как тип. Делает методологию E/R/R машинно-представимой, а не только прозаической. _(ERR, functional-system, core)_

**Uniqueness - score 5 (synthesis+observation).** Ядро ToS: минимальная Level-иерархия со структурным блоком Рассела/Кантора (level_lt_irrefl, не патч) + P1-P4 + детерминированный L5-резолв + E/R/R FunctionalSystem-запись, 0 аксиом. Хаб всего репо.
> _Caveat:_ Кумулятивная иерархия против самочленства — стандарт (типы/ранги); уникальность — в E/R/R/P4-обрамлении, структурном (типовом) блоке парадоксов и L5-детерминизме, не в новой теории множеств.

---

## #1793 - `src/ToS_Axioms.v` - score 4 (synthesis+observation)

**The two ToS axioms: classic (L3) and L4_witness (P4)**

- **Topic.** The repo's exactly-two axioms centralized: classic (excluded middle, ToS law L3) re-exported from Distinction, L4_witness (ex -> sig constructive witness, P4), and NNPP derived from classic.
- **Role.** Axiom centralization hub (foundation cluster). Imported wherever LEM or constructive witnesses are needed.
- **Counts.** Qed 2 / Admitted 0 / axioms 2
- **Imports.** foundation.Distinction (classic)
- **E/R/R.** _Elements:_ две аксиомы как именованные сущности. _Roles:_ classic = роль L3 (исключённое третье); L4_witness = роль P4 (конструктивный свидетель). _Rules:_ ex ⟹ sig (L4_witness); NNPP выводится из classic. _P4:_ ровно ДВЕ аксиомы, помеченные законами ToS; всё остальное — 0-аксиомно; честная централизация цены логики.
- **Classical counterpart.** Excluded middle (LEM) and the choice/constructive-indefinite-description bridge are classical logical axioms; NEW is only the deliberate MINIMALITY and ToS-law labelling: exactly two axioms (classic=L3, L4_witness=P4) centralized, with NNPP derived.
- **Tags.** axioms, LEM, L3, P4, minimality, foundation
- **Notes.** This file legitimately declares 2 axioms (the repo's only core axioms); axioms=2 here is correct, not a 0-axiom file.

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `L3_informative/L4_definite` | Definition | законы-метки для двух аксиом |
| `NNPP_from_L3` | Lemma | ★ двойное отрицание выводится из classic (L3) |

**Key lemmas (deep):**

- **`NNPP_from_L3`** - Двойное отрицание (NNPP) выведено из classic — показывает, что центральная логическая сила репо сведена к ОДНОЙ аксиоме L3 (плюс L4_witness для свидетелей). Минимальность axiom-базы = честность всего проекта (0-axiom повсюду, кроме этих двух). _(LEM, NNPP, axiom-minimality)_

**Uniqueness - score 4 (synthesis+observation).** РОВНО две аксиомы (classic=L3, L4_witness=P4) централизованы и помечены законами ToS; всё остальное в репо 0-аксиомно. Минимальность axiom-базы как принцип.
> _Caveat:_ LEM и конструктивное описание — стандартные аксиомы; уникальность — в дисциплине минимальности + ToS-маркировке, не в самих аксиомах.

---

## #1794 - `src/ToS_Lang_Extraction.v` - score 1 (exposition)

**ToS language extraction: checker/evaluator computable, structurally recursive**

- **Topic.** Constructor-dichotomy computability of typecheck/typecheck_ann/eval/classify/safe_eval/erase (option None-or-Some, EvalResult trichotomy, valuehood decidability, erased-size successor); structural recursion is certified by Coq's termination checker, not restated in-logic.
- **Role.** Type-theory (extraction readiness for the language). Imports TypeChecker/Evaluator. June 2026 wave-4 tail: all 6 computable-lemmas were the vacuous exists r, f x = r -> constructor dichotomies; the 2 structurally_recursive duplicates DELETED (vacuity documents nothing) — 8 Qed -> 6.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** ToS TypeChecker, Evaluator
- **E/R/R.** _Elements:_ проверяльщик/вычислитель ToS-языка. _Roles:_ вычислимость как конструкторная дихотомия результата (роль извлекаемости). _Rules:_ extraction_*_computable: option None-or-Some; EvalResult-трихотомия; разрешимость значения; размер стирания = successor. _P4:_ результат checker/evaluator инспектируем по конструкторам (Element) ⟹ извлекаемы в OCaml (tos_lang); структурная рекурсия сертифицируется при определении Fixpoint.
- **Classical counterpart.** That a type checker/evaluator is computable and structurally recursive (hence extractable to OCaml) is routine; NEW: nothing -- the computability/structural-recursion witnesses for the ToS language checker/evaluator.
- **Tags.** extraction, computable, type-checker, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `extraction_typecheck/ann/eval/classify/safe_eval/erase_computable` | Lemma | ★ конструкторные дихотомии результатов checker/eval |

**Key lemmas (deep):**

- **`extraction_classify_computable`** - Результат classify_eval инспектируем: ER_Value/ER_Partial/ER_TypeError — настоящая трихотомия (June 2026: была вакуумная exists r, _ = r). Element-сторона: верифицированный язык не только доказан безопасным, но и ИСПОЛНИМ — мост к extraction/tos_lang. _(extraction, computable, constructor-dichotomy)_

**Uniqueness - score 1 (exposition).** Вычислимость и структурная рекурсия checker/evaluator ToS-языка ⟹ извлекаемость в OCaml (tos_lang CLI).
> _Caveat:_ Извлекаемость структурно-рекурсивных функций рутинна; ценность — исполнимость верифицированного языка.

---

## #1795 - `src/TypeChecker.v` - score 2 (methods)

**The ToS type checker: sound, deterministic, with annotations**

- **Topic.** typecheck (sound, deterministic) with inversion lemmas per construct, the annotated typecheck_ann over ExprAnn with erase_ann, soundness of the annotated checker, and worked examples.
- **Role.** Type-theory (decidable checker). Defines typecheck/typecheck_ann. Imports Typing_Expr.
- **Counts.** Qed 26 / Admitted 0 / axioms 0
- **Imports.** ToS Typing_Expr
- **E/R/R.** _Elements:_ проверяльщик типов typecheck; аннотированные ExprAnn. _Roles:_ type checker как разрешающая роль (Some T корректно); аннотации с erasure. _Rules:_ typecheck_sound; deterministic; typecheck_ann_sound с erase_ann. _P4:_ типизация РАЗРЕШИМА (typecheck вычислим, sound, детерминирован) — Element-сторона; аннотации стираемы (erase_ann).
- **Classical counterpart.** A decidable bidirectional type checker, sound (typecheck=Some T => has type T) and deterministic, plus an annotated variant with erasure, is standard; NEW: nothing -- the ToS language checker (typecheck/typecheck_ann) sound and deterministic.
- **Tags.** type-checker, decidable, sound, annotations, type-theory, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `typecheck/typecheck_sound/var/const/system/app_inversion/pair_inversion/deterministic` | Definition/Lemma | ★ проверяльщик sound и детерминирован |
| `ExprAnn/erase_ann/typecheck_ann/typecheck_ann_sound/deterministic` | Definition/Lemma | ★ аннотированный проверяльщик + erasure |
| `typecheck_identity/app_identity/pair_example/nested_lam/resolve_example` | Lemma | проработанные примеры |

**Key lemmas (deep):**

- **`typecheck_sound`** - Проверяльщик типов КОРРЕКТЕН (typecheck G e = Some T ⟹ G ⊢ e:T) и детерминирован — типизация ToS-языка РАЗРЕШИМА. Element-сторона: типы вычисляются, не угадываются; аннотированный вариант (typecheck_ann) поддерживает erasure для извлечения. Основа Evaluator/AIInterface. _(type-checker, decidable, sound)_

**Uniqueness - score 2 (methods).** Разрешимый корректный детерминированный проверяльщик типов ToS-языка (typecheck/typecheck_ann + erasure).
> _Caveat:_ Бидирекциональная проверка типов стандартна; вклад — ToS-инстанс, основа safe_eval/AI-пайплайна.

---

## #1796 - `src/TypeSafety.v` - score 3 (methods)

**Type safety: tos_lang_main_theorem (well-typed never stuck) + no paradox**

- **Topic.** The combined type safety (preservation + progress), P4 evaluation terminates, no stuck state, determinism/confluence, multi-step safety, the main theorem tos_lang_main_theorem, and safety_implies_no_paradox.
- **Role.** Type-theory capstone. Combines SubjectReduction + Progress. Imports both. June 2026 wave-4 tail: P4_evaluation_terminates -> valuehood-decidability form, following the rewritten Reduction.eval_fuel_terminates.
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** ToS SubjectReduction, Progress
- **E/R/R.** _Elements:_ типизированные вычисления. _Roles:_ type-safety как роль (не застревает); безопасность ⟹ нет парадокса. _Rules:_ preservation + progress ⟹ safety; eval terminates; safety_implies_no_paradox. _P4:_ type-safe вычисление ФИНИТНО завершается без аварийного застревания (P4); безопасность ⟹ нет парадокса (стыковка с Soundness).
- **Classical counterpart.** Type safety (well-typed terms don't get stuck; preservation + progress) is the standard syntactic-safety theorem; NEW is only the ToS capstone tos_lang_main_theorem and the tie safety => no paradox.
- **Tags.** type-safety, main-theorem, no-paradox, type-theory, methods
- **Notes.** PowerShell flagged Adm=1 but it is a comment mention; actual Admitted = 0.

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `type_safety/P4_evaluation_terminates/no_stuck_state/eval_deterministic/step_confluence` | Theorem/Lemma | ★ type-safety (preservation+progress), финитность |
| `tos_lang_main_theorem/safety_implies_no_paradox/value_is_normal_form/type_safety_strong` | Theorem | ★ главная теорема языка; безопасность ⟹ нет парадокса |

**Key lemmas (deep):**

- **`tos_lang_main_theorem`** - Главная теорема ToS-языка: well-typed + топливо ⟹ well-typed результат без застревания (preservation+progress скомбинированы), вычисление финитно завершается (P4). safety_implies_no_paradox связывает с парадокс-блокировкой (Soundness). Капстоун верифицированного ядра языка. _(type-safety, main-theorem, no-paradox, P4)_

**Uniqueness - score 3 (methods).** Type-safety ToS-языка (tos_lang_main_theorem: well-typed никогда не застревает, финитно завершается) + стыковка safety ⟹ нет парадокса.
> _Caveat:_ Type-safety (preservation+progress) — стандартная метатеория; вклад — ToS-капстоун + связь с парадокс-блокировкой. Слово 'Admitted' в комментарии (0 реальных).

---

## #1797 - `src/Typing_Expr.v` - score 2 (methods)

**Typing for the ToS language: types, canonical forms, weakening/substitution**

- **Topic.** The Ty types (arrow/pair/nat/system), expr_has_type, canonical forms per type, type uniqueness, weakening, substitution preserves typing, and resolve/observe/app typing.
- **Role.** Type-theory core (the typing relation). Defines expr_has_type. Imports Expressions.
- **Counts.** Qed 22 / Admitted 0 / axioms 0
- **Imports.** ToS Expressions
- **E/R/R.** _Elements:_ типы Ty (arrow/pair/nat/system); контексты. _Roles:_ отношение типизации; канонические формы; уникальность типа. _Rules:_ weakening; substitution_preserves_typing; canonical forms. _P4:_ типизация конечно-проверяема; канонические формы и уникальность типа — типовая дисциплина (Element).
- **Classical counterpart.** A typing relation with arrow/pair/nat/system types, canonical forms, weakening and substitution-preserves-typing is standard; NEW: nothing -- the ToS language typing with system types and resolve/observe typing.
- **Tags.** typing, type-theory, canonical-forms, substitution, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `Ty/TyCtx/expr_has_type/ty_eq_dec/const_has_type_nat/lam_has_type_arrow/system_has_type_system` | Inductive/Definition/Lemma | типы и отношение типизации |
| `var_type_unique/canonical_arrow/pair/nat/system/value_has_type_inv` | Lemma | ★ канонические формы; уникальность типа |
| `weakening_general/expr/substitution_preserves_typing/resolve_preserves_type/app_type_arrow/observe_type` | Lemma | ★ weakening; подстановка сохраняет тип |

**Key lemmas (deep):**

- **`substitution_preserves_typing`** - Подстановка сохраняет типизацию — несущая лемма для subject reduction (preservation). Element-сторона: типы устойчивы к редукции; канонические формы (value_has_type_inv) питают progress. Основа type-safety ToS-языка. _(typing, substitution, preservation-lemma)_

**Uniqueness - score 2 (methods).** Типизация ToS-языка (arrow/pair/nat/system, канонические формы, weakening, подстановка сохраняет тип) — основа type-safety.
> _Caveat:_ Правила типизации стандартны; вклад — ToS-инстанс с system-типами, основа метатеории.

---

## #1798 - `src/UniformConvergence.v` - score 2 (methods)

**Uniform convergence over Q: continuity, limit-integral/derivative exchange, Dini**

- **Topic.** Uniform vs pointwise convergence, uniform Cauchy, uniform limit of continuous is continuous, integral/derivative limit exchange, uniform limit preserves derivative bounds, and Dini's monotone theorem.
- **Role.** Calculus chain (uniform convergence). Self-contained.
- **Counts.** Qed 20 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ последовательности функций; равномерная/точечная сходимость. _Roles:_ равномерный предел как роль (сохраняет непрерывность); обмен предела с интегралом/производной. _Rules:_ uniform_limit_continuous; integral/derivative_limit_exchange; Dini. _P4:_ равномерная сходимость с явным модулем (Element); обмен пределов обоснован равномерностью, не постулирован.
- **Classical counterpart.** Uniform convergence, uniform limit of continuous is continuous, exchange of limit with integral/derivative, and Dini's theorem are classical; NEW: nothing -- a constructive Q treatment with explicit moduli.
- **Tags.** uniform-convergence, continuity, dini, calculus, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `fun_seq/pointwise_converges/uniform_converges/uniform_cauchy/uniform_implies_pointwise/uniform_limit_unique` | Definition/Lemma | равномерная/точечная сходимость |
| `uniform_limit_continuous_at/on/integral_limit_exchange/derivative_limit_exchange/uniform_deriv_preserves_bound/dini_monotone` | Lemma | ★ непрерывность предела; обмен с интегралом/производной; Dini |

**Key lemmas (deep):**

- **`uniform_limit_continuous_on`** - Равномерный предел непрерывных функций непрерывен (с явным модулем) над Q — ядро равномерной сходимости. Обмен предела с интегралом/производной обоснован равномерностью; Dini связывает монотонную + точечную с равномерной. Element-сторона с вычислимыми модулями. _(uniform-convergence, continuity, limit-exchange)_

**Uniqueness - score 2 (methods).** Равномерная сходимость над Q (непрерывность предела, обмен с интегралом/производной, Dini) с явными модулями.
> _Caveat:_ Равномерная сходимость классична; вклад — конструктивное Q-исполнение.

---

## #1799 - `src/UniversePolymorphism.v` - score 2 (methods)

**Level arithmetic: addition, LS injective-not-surjective, trichotomy**

- **Topic.** Level addition (assoc, monotone), level depth additive/injective, LS injective but not surjective, forall-levels quantification and induction, L1 minimal, and level trichotomy.
- **Role.** Foundation (level/universe arithmetic). Imports Core_ERR.
- **Counts.** Qed 23 / Admitted 0 / axioms 0
- **Imports.** ToS Core_ERR
- **E/R/R.** _Elements:_ уровни и их арифметика (level_add). _Roles:_ сложение/преемник уровней как роли; L1 минимален. _Rules:_ level_add ассоц./монотонно; LS инъективен, не сюръективен; трихотомия. _P4:_ уровневая арифметика конечно-структурна; LS не сюръективен ⟹ иерархия растёт без верха (role-limit-узор).
- **Classical counterpart.** Level/universe arithmetic (addition, monotonicity, a successor that is injective but not surjective, trichotomy) is standard; NEW is only the ToS level instance: level_add, LS not surjective, forall-levels induction, L1 minimal.
- **Tags.** level-arithmetic, universe, successor, trichotomy, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `level_add/zero/succ/assoc/monotone/level_depth_add/injective` | Definition/Lemma | ★ сложение уровней (ассоц./монотонно) |
| `LS_injective/LS_not_surjective/level_lt_LS/L1_minimal/level_trichotomy/level_lt_dec` | Lemma | ★ LS инъективен не сюръективен; трихотомия; L1 минимален |
| `ForAllLevels/forall_levels_impl/conj/induction/LS_preserves_lt` | Definition/Lemma | квантификация и индукция по уровням |

**Key lemmas (deep):**

- **`LS_not_surjective`** - Преемник уровня LS инъективен, но НЕ сюръективен — иерархия уровней растёт без верха (тот же role-limit-узор no-maximum, что no_maximal_rung/cardinality). L1 минимален (низ). Element-сторона: уровневая арифметика разрешима, но восхождение неограниченно. _(level-arithmetic, successor, no-maximum)_

**Uniqueness - score 2 (methods).** Арифметика уровней (сложение ассоц./монотонно, LS инъективен-не-сюръективен, трихотомия, L1 минимален) — иерархия растёт без верха.
> _Caveat:_ Уровневая арифметика стандартна; вклад — ToS-инстанс + узор no-maximum.

