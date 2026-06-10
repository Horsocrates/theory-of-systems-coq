# Database - cluster `zeta`

_Generated from `zeta.json` by `generate.ps1` - do not edit by hand; edit the JSON._

**30 files / 692 Qed.** Score distribution: s5=0 / s4=0 / s3=4 / s2=16 / s1=10 / s0=0

---

## #1800 - `src/zeta/ApproximateZeros.v` - score 3 (new-framing)

**Approximate zeros over Q: RH as a three-way equivalence**

- **Topic.** is_approx_zero of partial zeta, an approx-zero tree (decidable, monotone, thin), margins decreasing, and RH_three_equiv (zeros <-> process <-> fixed-point).
- **Role.** Zeta/RH (epsilon framing). Self-contained. Book Part XIII.
- **Counts.** Qed 34 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ частичные суммы дзеты; приближённые нули. _Roles:_ RH как тройная эквивалентность (нули/процесс/неподвижная точка). _Rules:_ approx_zero_tree decidable/monotone; RH_three_equiv. _P4:_ RH переформулирована как РАЗРЕШИМОЕ дерево приближённых нулей + тройная эквивалентность (вена C/E); margins убывают как процесс.
- **Classical counterpart.** Approximate zeros of partial zeta sums and an epsilon-RH are an analytic-number-theory device; NEW is only the P4 framing: RH recast as a THREE-WAY equivalence (zeros / process / fixed-point), RH_three_equiv, axiom-free.
- **Tags.** zeta, RH, three-equivalence, fixed-point, new-framing

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `is_approx_zero approx_zero_tree_decidable RH_epsilon RH_three_equiv margin_decreasing/vanishes zeta_partial_positive integer_zeta_not_zero` | Definition/Lemma | приближённые нули, дерево, RH-эквивалентность |

**Key lemmas (deep):**

- **`RH_three_equiv`** - RH переформулирована как ТРОЙНАЯ эквивалентность: нули-на-линии ⟺ процесс ⟺ неподвижная точка отражения. Не доказательство RH, а её переобрамление как разрешимого/процессного вопроса (вена C/E). Margins убывают как процесс. _(RH, three-equivalence, fixed-point, P4)_

**Uniqueness - score 3 (new-framing).** RH как тройная эквивалентность (нули/процесс/неподвижная точка) + разрешимое дерево приближённых нулей, аксиомо-свободно.
> _Caveat:_ НЕ доказательство RH; переобрамление как процессный/неподвижно-точечный вопрос. RH остаётся open.

---

## #1801 - `src/zeta/ArithmeticCommutator.v` - score 2 (methods)

**Arithmetic commutator over Q: derived from the real operators + general nonpositivity (June 2026)**

- **Topic.** Finite matrix calculus on K-node truncations (sum_nodes/mat_mul_at), the commutator of mult_adj and add_adj, symmetry of both adjacencies, commutator antisymmetry, the general law Tr([M,A]^2) <= 0 for every K, and the concrete values -128/-268/-476 now DERIVED by vm_compute.
- **Role.** Zeta (arithmetic commutator, derived). Imports DivisibilityGraph (the real operators). June 2026 forward-fix: the hardcoded value table replaced by the actual matrix computation — values matched; + general theorem tr_comm_sq_nonpos.
- **Counts.** Qed 22 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ арифметический коммутатор. _Roles:_ некоммутативность как аналогия Гейзенберга. _Rules:_ comm_grows; noncomm; comm_monotone. _P4:_ след коммутатора ВЫЧИСЛЕН из настоящих операторов на конечном обрезе (P4); негативность — ОБЩАЯ теорема из антисимметрии; Гейзенберг-фрейминг остаётся аналогией (без неравенства неопределённости).
- **Classical counterpart.** Tr([M,A]^2) <= 0 for symmetric real matrices is standard linear algebra; NEW: nothing mathematically — but since June 2026 the file is honest machinery: the trace is COMPUTED from the actual divisibility/successor adjacency operators (was a hardcoded lookup; values verified to match: -128/-268/-476), with the general nonpositivity law derived from commutator antisymmetry.
- **Tags.** zeta, commutator, derived, methods

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `tr_comm_sq_arith comm_12/20/30 comm_grows noncomm comm_negative comm_monotone` | Definition/Lemma | коммутатор, рост, некоммутативность |

**Key lemmas (deep):**

- **`tr_comm_sq_nonpos`** - Tr([M,A]^2) <= 0 на КАЖДОМ обрезе K — выведено из антисимметрии коммутатора симметричных операторов (делимость и соседство), а конкретные -128/-268/-476 — vm_compute из настоящих матриц (June 2026: была захардкоженная таблица; значения совпали). Некоммутативность мультипликативной и аддитивной структур N — теперь теорема с инстансами. _(commutator, antisymmetry, derived, nonpositivity)_

**Uniqueness - score 2 (methods).** Коммутатор делимость×соседство ВЫЧИСЛЕН из операторов на Q-обрезах + общий закон Tr([M,A]^2)<=0 из антисимметрии; значения -128/-268/-476 выведены, не заявлены.
> _Caveat:_ Линейная алгебра стандартна; Гейзенберг-имя остаётся ФРЕЙМИНГОМ (нет неравенства неопределённости и связи с нулями) — честно помечено в шапке.

---

## #1802 - `src/zeta/ArithmeticHeisenbergSynthesis.v` - score 1 (exposition)

**Arithmetic Heisenberg synthesis**

- **Topic.** A synthesis tying noncommutative arithmetic, commutator growth, Mobius spin types, the critical hierarchy, Ising structure, and Mertens oscillation.
- **Role.** Zeta synthesis (Heisenberg analogies). Self-contained. June 2026 honest layering: commutator core DERIVED (real operators + general nonpositivity law, +commutator_trace_nonpositive), Mobius/Mertens real computations; Lee-Yang loci and critical exponents remain ANALOGY-DATA (enum labels + literature constants).
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** ToS zeta files
- **E/R/R.** _Elements:_ арифметические аналогии Гейзенберга. _Roles:_ синтез как роль сборки аналогий. _Rules:_ commutator_growth; mobius_spin; mertens_oscillation. _P4:_ сборка аналогий (Element); эвристика.
- **Classical counterpart.** Bundling the arithmetic-Heisenberg analogies (Mobius spin, commutator growth, Mertens) is exposition; NEW: nothing — a synthesis of the zeta toy-analogies.
- **Tags.** zeta, synthesis, heisenberg, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `arithmetic_heisenberg_synthesis noncommutative_arithmetic commutator_growth mobius_spin_types critical_hierarchy ising_structure mertens_oscillation` | Theorem | синтез Гейзенберг-аналогий |

**Key lemmas (deep):**

- **`arithmetic_heisenberg_synthesis`** - Сборка дзета-аналогий (некоммутативность, спин Мёбиуса, иерархия, Изинг, осцилляция Мертенса) в одну картину над Q. Эвристический синтез, не теорема. _(synthesis, heisenberg, zeta)_

**Uniqueness - score 1 (exposition).** Синтез арифметических Гейзенберг-аналогий дзеты.
> _Caveat:_ Эвристическая сборка; ценность — связная картина.

---

## #1803 - `src/zeta/ComplexZeta.v` - score 2 (new-framing)

**Complex zeta over Q: integer values, pole at 1**

- **Topic.** TComplex, harmonic = zeta(1) (divergent), zeta at integers (real, bounded, in [1,2]), pole strength unbounded, the zeta dichotomy (bounded process vs divergent at 1).
- **Role.** Zeta (complex values/pole). Self-contained. June 2026 wave-4 sweep: vacuous computability-shams (exists q, _ == q) replaced by the by-type finite-ratio form or real identities; see UNIQUENESS.md.
- **Counts.** Qed 29 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ комплексная дзета TComplex; гармонический ряд. _Roles:_ дзета как процесс; полюс в 1 как role-limit. _Rules:_ harmonic_diverges; zeta_integer bounded; zeta_dichotomy. _P4:_ дзета — процесс частичных сумм; полюс в s=1 (harmonic_diverges) = role-limit; иначе ограничен (Element).
- **Classical counterpart.** Zeta at integer points (harmonic divergence at 1, convergence and bounds elsewhere) is classical; NEW: nothing — exact Q complex-zeta values with a pole-strength dichotomy.
- **Tags.** zeta, complex, pole, process, new-framing

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `TComplex harmonic_eq_zeta_1 harmonic_diverges zeta_complex_at_integer zeta_integer_real/bounded zeta_dichotomy zeta_process_bounded zeta_1_unbounded pole_strength complex_zeta_summary` | Definition/Lemma | комплексная дзета, полюс, дихотомия June 2026 wave-4 sweep: vacuous computability-shams (exists q, _ == q) replaced by the by-type finite-ratio form or real identities; see UNIQUENESS.md. |

**Key lemmas (deep):**

- **`zeta_dichotomy`** - Дзета-дихотомия: при s≠1 процесс частичных сумм ограничен (Element), при s=1 расходится (полюс, role-limit). Дзета как процесс над Q, полюс = role-limit. Вена C в теории чисел. _(zeta, pole, dichotomy, process)_

**Uniqueness - score 2 (new-framing).** Комплексная дзета над Q как процесс с дихотомией ограничен/полюс-в-1 (harmonic_diverges).
> _Caveat:_ Значения дзеты и полюс классичны; ново — процессная дихотомия.

---

## #1804 - `src/zeta/ContractionZeros.v` - score 3 (synthesis+observation)

**Contraction & zeros: reflection is an isometry, NOT a contraction (the sharp RH obstruction)**

- **Topic.** A Euclidean critical metric, reflect_isometry and reflect_not_contraction_euclidean, a weighted distance, a corrected reflect-iterate moving toward Re=1/2, and the critical line minimizing reflect-distance.
- **Role.** Zeta/RH FLAGSHIP (vein C/E sharp observation). Book Part XIII flagship. Self-contained. June 2026: with the upstream FE axiom eliminated, reflect_zero_nontrivial / RH_critical_strip_symmetric are Closed under the global context (verified).
- **Counts.** Qed 43 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ критическая метрика; отражение reflect (s↦1−s). _Roles:_ отражение как ИЗОМЕТРИЯ (не сжатие); критическая линия как ось симметрии. _Rules:_ reflect_isometry; reflect_not_contraction_euclidean; critical_line_minimizes_reflect_dist. _P4:_ ★ отражение — ИЗОМЕТРИЯ, НЕ сжатие ⟹ RH НЕ наивная задача неподвижной точки/Банаха; критическая линия минимизирует reflect-расстояние.
- **Classical counterpart.** The functional-equation reflection s -> 1-s pairing zeros, and the critical line as the symmetry axis, are classical; NEW is the sharp observation: the reflection is an ISOMETRY (not a contraction) in the Euclidean metric, so RH is NOT a naive fixed-point/Banach problem — reflect_not_contraction_euclidean, with a corrected metric where the critical line minimizes reflect-distance.
- **Tags.** zeta, RH, isometry, fixed-point, sharp-observation, flagship

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `euclidean_dist_triangle reflect_isometry reflect_not_contraction_euclidean weighted_dist no_L1_contraction critical_line_minimizes_reflect_dist re_fixed_point_half reflect_critical_line corrected_re_moves_toward_half` | Definition/Lemma | ★ отражение изометрия не сжатие; критическая линия минимизирует |

**Key lemmas (deep):**

- **`reflect_not_contraction_euclidean`** - ★ Резкое наблюдение: отражение s↦1−s — ИЗОМЕТРИЯ (сохраняет расстояние), а НЕ сжатие. Значит RH НЕЛЬЗЯ свести к наивной банаховой неподвижной точке (как могла бы подсказать вена C). Критическая линия минимизирует reflect-расстояние, но без сжатия нет автоматической сходимости. Флагман Части XIII — честная граница процессного подхода к RH. _(RH, isometry-not-contraction, fixed-point, sharp-obstruction)_
- **`critical_line_minimizes_reflect_dist`** - Критическая линия Re=1/2 минимизирует расстояние до отражения (ось симметрии функционального уравнения) над Q. Объясняет, ПОЧЕМУ Re=1/2 особая — но изометрия (не сжатие) не даёт доказательства RH. _(critical-line, reflection, minimum)_

**Uniqueness - score 3 (synthesis+observation).** Резкое наблюдение: отражение функц. уравнения — ИЗОМЕТРИЯ, НЕ сжатие ⟹ RH не наивная банахова задача неподвижной точки; критическая линия минимизирует reflect-расстояние. Честная граница процессного подхода.
> _Caveat:_ НЕ доказательство RH; ценность — точное наблюдение, почему процессный/неподвижно-точечный подход НЕ замыкает RH (изометрия). Флагман Части XIII.

---

## #1805 - `src/zeta/DivisibilityGraph.v` - score 1 (exposition)

**Divisibility graph over the integers**

- **Topic.** Multiplication/addition adjacency, 1 as a hub, prime divisibility, chains, symmetry, degrees.
- **Role.** Zeta (arithmetic graph). Self-contained.
- **Counts.** Qed 19 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith
- **E/R/R.** _Elements:_ граф делимости/умножения; узел 1 как хаб. _Roles:_ делимость как роль рёбер. _Rules:_ one_hub; prime_div; chain. _P4:_ граф делимости конечно-проверяем (Element).
- **Classical counterpart.** A divisibility/multiplication graph on integers (1 as a hub, prime edges) is elementary; NEW: nothing — exact Q/nat divisibility-graph adjacency.
- **Tags.** zeta, divisibility, graph, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `divides mult_adj add_adj one_hub prime_div chain degree mult_symmetric coprime` | Definition/Lemma | граф делимости, хаб, цепи |

**Key lemmas (deep):**

- **`one_hub_1`** - 1 — хаб графа делимости (делит всё) над Q/nat. Element-сторона: арифметическая структура как граф (мост к дзета-аналогиям). _(divisibility, graph, hub)_

**Uniqueness - score 1 (exposition).** Граф делимости целых (1=хаб, простые рёбра, цепи).
> _Caveat:_ Элементарная теория чисел; ценность — графовая структура.

---

## #1806 - `src/zeta/EulerExtension.v` - score 2 (methods)

**Euler product extension over Q: process, no real zeros**

- **Topic.** Euler factor process, partial products (monotone, bounded, < 2), no real zeros, oscillation vanishing, the generalized Euler process Cauchy.
- **Role.** Zeta (Euler product process). Self-contained.
- **Counts.** Qed 36 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ эйлеровы множители; частичные произведения. _Roles:_ эйлеров продукт как процесс; нет вещественных нулей. _Rules:_ euler_partial monotone/bounded; no_real_zeros; euler_gen_cauchy. _P4:_ эйлеров продукт — процесс частичных произведений (Element); сходится (Cauchy), нет вещественных нулей.
- **Classical counterpart.** The Euler product partial sums (factor monotonicity, bounded deviation, no real zeros, oscillation) are classical analytic number theory; NEW: nothing — exact Q Euler-product process with Cauchy generation.
- **Tags.** zeta, euler-product, process, methods

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `euler_process euler_partial_mono/lt_2 no_real_zeros euler_oscillation/vanishes euler_gen_cauchy full_factor_formula` | Definition/Lemma | эйлеров продукт-процесс, нет нулей, Cauchy |

**Key lemmas (deep):**

- **`no_real_zeros`** - Эйлеров продукт не имеет вещественных нулей (множители > 1) над Q — частичные произведения сходятся как процесс (Cauchy). Element-сторона: дзета через эйлеров продукт как процесс. _(euler-product, no-zeros, process)_

**Uniqueness - score 2 (methods).** Эйлеров продукт над Q как Cauchy-процесс (множители>1, нет вещественных нулей, ограничен).
> _Caveat:_ Эйлеров продукт классичен; вклад — процессная Q-формализация.

---

## #1807 - `src/zeta/EulerProduct.v` - score 1 (exposition)

**Euler product over Q: zero-free factors**

- **Topic.** Qprod machinery, Euler factors (>1, <=2, monotone), partial products zero-free, the Euler process.
- **Role.** Zeta (Euler product core). Self-contained.
- **Counts.** Qed 26 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ эйлеровы множители; Qprod. _Roles:_ эйлеров продукт как роль (бесконечное произведение). _Rules:_ euler_factor_gt_1; zero_free_partial. _P4:_ эйлеровы множители > 1, частичные продукты zero-free (Element).
- **Classical counterpart.** The Euler product factors (>1, bounded, monotone in prime/exponent) are classical; NEW: nothing — exact Q Euler factors with zero-free partial products.
- **Tags.** zeta, euler-product, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `Qprod euler_factor euler_factor_gt_1/le_2 euler_partial zero_free_partial euler_factor_p/k_monotone euler_gen_process` | Definition/Lemma | эйлеровы множители, zero-free продукты |

**Key lemmas (deep):**

- **`zero_free_partial`** - Частичные эйлеровы продукты zero-free (каждый множитель > 1) над Q точно. Element-сторона: основа дзета-через-эйлеров-продукт. _(euler-product, zero-free)_

**Uniqueness - score 1 (exposition).** Эйлеровы множители над Q (>1, zero-free частичные продукты).
> _Caveat:_ Классика; ценность — Q-точность.

---

## #1808 - `src/zeta/ExplicitFormula.v` - score 2 (new-framing)

**Explicit formula over Q: RH = optimal PNT error**

- **Topic.** Zero contributions, RH vs de la Vallee-Poussin error (RH strictly better), pole correction, RH implies PNT-optimal implies half-line, zeros toward 1/2, and an axiom check.
- **Role.** Zeta/RH (explicit formula). Self-contained. June 2026 wave-4 sweep: vacuous computability-shams (exists q, _ == q) replaced by the by-type finite-ratio form or real identities; see UNIQUENESS.md.
- **Counts.** Qed 28 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ вклады нулей; ошибка ТРПЧ. _Roles:_ RH как критическая-линия-оптимальность. _Rules:_ rh_better_than_dvp; rh_implies_pnt_optimal; critical_line_optimal. _P4:_ RH ⟺ оптимальная ошибка ТРПЧ (критическая линия); explicit_formula_axiom_check — честный статус.
- **Classical counterpart.** The explicit formula linking zeros to the PNT error, and that RH gives the optimal (sqrt) error, is classical; NEW is only the framing: RH = critical-line-optimal, with an axiom_check showing the formula's status.
- **Tags.** zeta, explicit-formula, RH, PNT, new-framing

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `zero_contribution rh_contribution pnt_rh_error dvp_pnt_error rh_better_than_dvp rh_implies_pnt_optimal critical_line_optimal explicit_formula_axiom_check` | Definition/Lemma | вклады нулей, RH=оптимальная ошибка June 2026 wave-4 sweep: vacuous computability-shams (exists q, _ == q) replaced by the by-type finite-ratio form or real identities; see UNIQUENESS.md. |

**Key lemmas (deep):**

- **`rh_implies_pnt_optimal`** - RH ⟹ оптимальная (√x) ошибка ТРПЧ, и оптимальность ⟹ нули на половинной линии — переобрамление RH как критической-линии-оптимальности над Q. Не доказательство, а эквивалентная формулировка. _(explicit-formula, RH, PNT-optimal)_

**Uniqueness - score 2 (new-framing).** Явная формула над Q: RH ⟺ оптимальная ошибка ТРПЧ (критическая линия), RH лучше de-la-Vallee-Poussin.
> _Caveat:_ Связь нули↔ошибка ТРПЧ классична; ново — Q-формулировка эквивалентности, не доказательство RH.

---

## #1809 - `src/zeta/FunctionalEquation.v` - score 2 (new-framing)

**Functional equation over Q: reflection involution, zero quadruple (axiom eliminated 06.2026)**

- **Topic.** The reflection s -> 1-s (involutive), reflect on zeros, RH iff reflect-equiv, the zero quadruple {rho, 1-rho, conj} collapsing on the critical line — FE structure a 2-line Lemma since June 2026 (was the branch's one axiom).
- **Role.** Zeta/RH (functional equation). 0 axioms since June 2026: functional_equation_structure is a 2-line Lemma (is_nontrivial_zero = Cauchy + strip, both reflection-stable); the analytic FE stays in prose. Self-contained otherwise.
- **Counts.** Qed 14 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ отражение reflect (s↦1−s); нули. _Roles:_ функциональное уравнение как роль симметрии; четвёрка нулей. _Rules:_ reflect_involutive; RH_iff_reflect_equiv; RH_quadruple_collapses. _P4:_ ★ functional_equation_structure — ЛЕММА с June 2026 (is_nontrivial_zero = Коши∧полоса, оба отражательно-устойчивы; аналитическое ФУ о занулении — в прозе); четвёрка нулей коллапсирует на критической линии.
- **Classical counterpart.** The Riemann functional equation pairing a nontrivial zero rho with 1-rho (and the reflection involution) is classical; the structure WAS an axiom until June 2026; now a 2-line LEMMA — is_nontrivial_zero is formally Cauchy + critical strip (no vanishing condition), both conjuncts reflection-stable; the ANALYTIC FE (about actual zeta vanishing) stays unformalized in prose; NEW: only the P4 reading (zero quadruple collapses on the critical line).
- **Tags.** zeta, functional-equation, reflection, axiom, new-framing
- **Notes.** June 2026: axiom ELIMINATED — functional_equation_structure is a 2-line Lemma (Cauchy+strip both reflection-stable; the NAME promised the analytic FE, the statement was free). Print Assumptions of the reflection layer: Closed under the global context. axioms=0.

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `reflect reflect_involutive reflect_re/im on_critical_line_reflect_re RH_iff_reflect_equiv zero_quadruple quadruple_all_nontrivial RH_quadruple_collapses reflect_conj_commute` | Definition/Lemma | ★ отражение, RH⟺reflect-equiv, четвёрка нулей |

**Key lemmas (deep):**

- **`RH_quadruple_collapses`** - Нетривиальный ноль порождает четвёрку {ρ, 1−ρ, conj ρ, ...}, коллапсирующую в пару на критической линии (RH) над Q. Структура FE ДОКАЗАНА (June 2026, 2 строки): формальное определение нуля не содержит зануления, оба конъюнкта отражательно-устойчивы — имя аксиомы обещало больше, чем говорило утверждение; аналитическое ФУ честно в прозе. _(functional-equation, reflection, quadruple, axiom)_

**Uniqueness - score 2 (new-framing).** Функциональное уравнение над Q: отражение-инволюция, RH⟺reflect-equiv, коллапс четвёрки нулей на критической линии.
> _Caveat:_ ★ 0 аксиом с 2026-06-10: бывшая аксиома = 2-строчная лемма (over-branding имени вскрыт: is_nontrivial_zero формально без зануления); аналитическое ФУ Римана неформализовано — в прозе. НЕ доказательство RH.

---

## #1810 - `src/zeta/LeeYangAnalogy.v` - score 2 (new-framing)

**Lee-Yang analogy over Q: zeros-on-a-locus, RH vs Ising**

- **Topic.** Lee-Yang locus vs RH locus, product types (finite Ising vs infinite zeta), both codimension-1, Lee-Yang proven but RH open, different geometry.
- **Role.** Zeta/RH (Lee-Yang analogy). Self-contained.
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ Lee-Yang locus; RH locus; Изинг. _Roles:_ аналогия RH↔Lee-Yang как роль. _Rules:_ both_codim_1; ly_proven; rh_open; different_geometry. _P4:_ аналогия точна над Q; Lee-Yang доказан, RH open — честно разделено.
- **Classical counterpart.** The Lee-Yang theorem (Ising partition zeros on the unit circle) as an analogy for RH (zeros on a line) is a known heuristic; NEW: nothing — exact Q Lee-Yang vs RH comparison (different geometry, finite vs infinite product).
- **Tags.** zeta, lee-yang, RH, analogy, new-framing

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `ZeroLocus lee_yang_locus rh_locus ly_product rh_product both_codim_1 ly_proven rh_open different_geometry ising_Z lee_yang_theorem rh_theorem analogy_structure` | Definition/Lemma | Lee-Yang vs RH, геометрия, статус |

**Key lemmas (deep):**

- **`different_geometry`** - Lee-Yang (нули Изинга на окружности, конечное произведение, ДОКАЗАН) vs RH (нули на линии, бесконечное произведение, OPEN) — аналогия точна, но геометрия и статус РАЗНЫЕ над Q. Честное разделение: аналогия не доказательство. _(lee-yang, RH, analogy, honest)_

**Uniqueness - score 2 (new-framing).** Аналогия Lee-Yang↔RH над Q (оба codim-1), с ЧЕСТНЫМ различием (Lee-Yang доказан/конечен, RH open/бесконечен).
> _Caveat:_ Lee-Yang↔RH аналогия известна (эвристика); ново — формальное Q-сравнение с честным различием статуса.

---

## #1811 - `src/zeta/LiCoefficients.v` - score 2 (new-framing)

**Li coefficients over Q: RH-equivalent criterion (computable)**

- **Topic.** Binomials, Li modulus bounds, Li nonneg on the critical line, lambda lower bounds growing, the Li criterion (holds, computable), Li as a P4 process.
- **Role.** Zeta/RH (Li criterion). Self-contained. June 2026 wave-4 sweep: vacuous computability-shams (exists q, _ == q) replaced by the by-type finite-ratio form or real identities; see UNIQUENESS.md.
- **Counts.** Qed 35 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ коэффициенты Ли; биномы. _Roles:_ критерий Ли как RH-эквивалент. _Rules:_ li_on_line_nonneg; li_criterion_holds/computable. _P4:_ критерий Ли РАЗРЕШИМ (li_criterion_computable) над Q; Li-коэффициенты неотрицательны на линии (Element).
- **Classical counterpart.** Li's criterion (RH iff all Li coefficients nonnegative) is a classical equivalent of RH; NEW: nothing — exact Q Li-coefficient bounds, nonneg on the line, computable, structural.
- **Tags.** zeta, li-criterion, RH, computable, new-framing

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `binom li_modulus_sq li_contribution_bound li_bound_on_line lambda_lower li_growth_rate li_criterion li_criterion_holds/computable li_on_line_nonneg li_p4_process` | Definition/Lemma | ★ коэффициенты Ли, RH-критерий, разрешимость June 2026 wave-4 sweep: vacuous computability-shams (exists q, _ == q) replaced by the by-type finite-ratio form or real identities; see UNIQUENESS.md. |

**Key lemmas (deep):**

- **`li_criterion_computable`** - Критерий Ли (RH ⟺ все λ_n ≥ 0) РАЗРЕШИМ над Q: Li-коэффициенты неотрицательны на критической линии, вычислимы как P4-процесс. Переобрамление RH как разрешимого критерия (вена A/C); не доказательство (нули не на линии не исключены). _(li-criterion, RH, computable, P4)_

**Uniqueness - score 2 (new-framing).** Критерий Ли над Q: RH⟺λ_n≥0, Li-коэффициенты неотрицательны на линии, ВЫЧИСЛИМЫ как P4-процесс.
> _Caveat:_ Критерий Ли — классический RH-эквивалент; ново — разрешимая Q-формулировка, не доказательство RH.

---

## #1812 - `src/zeta/LiProcess.v` - score 2 (new-framing)

**Li process over Q: decidable RH/YM checks**

- **Topic.** li_process (rational, nonneg on the line), YM/RH checks decidable, the process Cauchy, P4 Li computable/verified.
- **Role.** Zeta/RH (Li as process). Self-contained. June 2026 wave-4 sweep: vacuous computability-shams (exists q, _ == q) replaced by the by-type finite-ratio form or real identities; see UNIQUENESS.md. June 2026 wave-4 sweep: vacuous computability-shams (exists q, _ == q) replaced by the by-type finite-ratio form or real identities; see UNIQUENESS.md.
- **Counts.** Qed 22 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ li_process; RH/YM проверки. _Roles:_ Li как процесс; разрешимые проверки. _Rules:_ rh_decidable; ym_decidable; process_cauchy. _P4:_ Li как Cauchy-процесс с РАЗРЕШИМЫМИ RH/YM проверками (Element).
- **Classical counterpart.** Li coefficients as a process (nonneg on the line, decidable RH/YM checks) is the P4 view; NEW: only the framing: li_process as a Cauchy process with decidable RH/YM checks.
- **Tags.** zeta, li-process, RH, decidable, new-framing

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `li_process li_nonneg_if_on_line ym_check rh_check ym/rh_decidable process_cauchy p4_li_computable/verified li_process_summary` | Definition/Lemma | Li-процесс, разрешимые проверки, Cauchy June 2026 wave-4 sweep: vacuous computability-shams (exists q, _ == q) replaced by the by-type finite-ratio form or real identities; see UNIQUENESS.md. |

**Key lemmas (deep):**

- **`rh_decidable`** - RH-проверка на конечной стадии РАЗРЕШИМА (li_process нонотрицателен на линии), процесс Cauchy над Q. P4: RH как разрешимый процессный вопрос на каждой стадии (не доказательство полной RH). _(li-process, RH, decidable, P4)_

**Uniqueness - score 2 (new-framing).** Li как Cauchy-процесс над Q с разрешимыми RH/YM проверками на стадиях.
> _Caveat:_ Переобрамление; RH-проверка стадийна, не полное доказательство.

---

## #1813 - `src/zeta/LogZeta.v` - score 1 (exposition)

**Log zeta over Q: prime-power sum, Mertens**

- **Topic.** Harmonic/log approximation, the log series, sum over primes / prime-power sum, the Euler-log leading term, the Mertens combination, log-zeta process.
- **Role.** Zeta (log zeta). Self-contained. June 2026 wave-4 sweep: vacuous computability-shams (exists q, _ == q) replaced by the by-type finite-ratio form or real identities; see UNIQUENESS.md.
- **Counts.** Qed 30 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ log zeta; сумма по простым. _Roles:_ log zeta как процесс; Мертенс. _Rules:_ euler_log_leading; mertens_via_primes; log_zeta_process. _P4:_ log zeta как процесс (Element); сумма по простым, тождество Мертенса.
- **Classical counterpart.** log zeta via the prime-power sum (Mertens identity, harmonic/log approximation) is classical; NEW: nothing — exact Q log-zeta process (nonneg, increasing).
- **Tags.** zeta, log-zeta, mertens, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `harmonic log_approx log_series_partial sum_over_primes prime_power_sum euler_log_leading log_zeta_process mertens_via_primes prime_sum_mertens_identity` | Definition/Lemma | log zeta, сумма по простым, Мертенс |

**Key lemmas (deep):**

- **`prime_sum_mertens_identity`** - Тождество Мертенса связывает log zeta с суммой по простым над Q; log-zeta — неубывающий процесс. Element-сторона аналитической теории чисел. _(log-zeta, mertens, prime-sum)_

**Uniqueness - score 1 (exposition).** Log zeta над Q (сумма по простым, тождество Мертенса, процесс).
> _Caveat:_ Классика; ценность — Q-процесс.

---

## #1814 - `src/zeta/MobiusSpin.v` - score 1 (exposition)

**Mobius spin over Q: Mertens and sign changes**

- **Topic.** Mobius values, Mertens at 10/20/30, bounded |mu|, up/down/zero counts (spin partition), Mertens sign change.
- **Role.** Zeta (Mobius/Mertens). Self-contained.
- **Counts.** Qed 20 / Admitted 0 / axioms 0
- **Imports.** Stdlib: ZArith
- **E/R/R.** _Elements:_ Мёбиус mu (спин ±1/0); Мертенс. _Roles:_ Мёбиус как спин; Мертенс как роль. _Rules:_ mobius_bounded; mertens_sign_change; spin_partition. _P4:_ Мёбиус/Мертенс точны над Q (Element); спин-аналогия.
- **Classical counterpart.** The Mobius function as a +-1/0 'spin', Mertens function and its sign changes, are classical; NEW: nothing — exact Q Mobius/Mertens values with a spin-partition analogy.
- **Tags.** zeta, mobius, mertens, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `mobius_val mertens mobius_1/2/4/6/30 mertens_10/20/30 mobius_bounded count_up/down/zero spin_partition_10 mertens_sign_change` | Definition/Lemma | Мёбиус-спин, Мертенс, смена знака |

**Key lemmas (deep):**

- **`mertens_sign_change`** - Функция Мертенса меняет знак (осцилляция) над Q точно; Мёбиус как ±1/0 спин с разбиением. Element-сторона; связь с RH (рост Мертенса). _(mobius, mertens, sign-change, spin)_

**Uniqueness - score 1 (exposition).** Мёбиус-спин и Мертенс над Q (смена знака, спин-разбиение).
> _Caveat:_ Классика; ценность — Q-точность + спин-аналогия.

---

## #1815 - `src/zeta/PartialSumZeros.v` - score 1 (exposition)

**Partial-sum zeros over Q: no zeros for Re>2, reflection**

- **Topic.** Lower bound on zeta for Re>=2 (no zeros), zeta monotone/strict interval, crude/refined zero counts, the reflection involution, zero squeeze.
- **Role.** Zeta/RH (partial-sum zeros). Self-contained.
- **Counts.** Qed 23 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ частичные суммы дзеты; нули. _Roles:_ нули частичных сумм; отражение. _Rules:_ no_zeros_re_gt_2; reflect_involution; zero_squeeze. _P4:_ нет нулей при Re>2 (Element); отражение-инволюция, зажатие нулей.
- **Classical counterpart.** Bounding zeros of partial zeta sums (no zeros for Re>2, reflection symmetry) is an analytic device; NEW: nothing — exact Q partial-sum zero bounds with reflection involution.
- **Tags.** zeta, zero-free, reflection, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `zeta_lower_at_2 no_zeros_re_gt_2 zeta_in_interval crude/refined_zero_count reflect_involution critical_line_fixed zero_squeeze` | Definition/Lemma | нет нулей Re>2, отражение, зажатие |

**Key lemmas (deep):**

- **`no_zeros_re_gt_2`** - Нет нулей дзеты при Re≥2 (нижняя оценка > 0) над Q точно. Element-сторона: zero-free регион справа, отражение даёт симметрию к зажатию нулей. _(zero-free, partial-sum, reflection)_

**Uniqueness - score 1 (exposition).** Нули частичных сумм над Q (нет нулей Re>2, отражение, зажатие).
> _Caveat:_ Стандартные оценки; ценность — Q-точность.

---

## #1816 - `src/zeta/PrimeCountingCritical.v` - score 1 (exposition)

**Prime counting critical exponents over Q**

- **Topic.** Box/hydrogen/walk/prime exponents (prime slowest, all positive), pi values, the PNT (li approximation) error small at 100/1000.
- **Role.** Zeta (prime counting). Self-contained.
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ показатели роста; pi(x); ошибка ТРПЧ. _Roles:_ критические показатели как роли. _Rules:_ prime_sublinear; pnt_error_small. _P4:_ показатели и pi точны над Q (Element).
- **Classical counterpart.** Comparing growth exponents (prime counting sublinear, PNT error small) is classical; NEW: nothing — exact Q exponent comparison (primes slowest) and pi/PNT values.
- **Tags.** zeta, prime-counting, PNT, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `prime_exponent primes_slowest prime_sublinear pi_10/100/1000 li_approx pnt_error error_small_100/1000` | Definition/Lemma | показатели, pi, ошибка ТРПЧ |

**Key lemmas (deep):**

- **`primes_slowest`** - Простые растут медленнее всех сравниваемых процессов (prime_sublinear), ошибка ТРПЧ мала над Q. Element-сторона распределения простых. _(prime-counting, exponent, PNT)_

**Uniqueness - score 1 (exposition).** Критические показатели простых над Q (простые медленнее всех, ошибка ТРПЧ мала).
> _Caveat:_ Стандартно; ценность — Q-сравнение.

---

## #1817 - `src/zeta/PrimeSumBounds.v` - score 1 (exposition)

**Prime sum bounds over Q: prime reciprocals, Chebyshev theta**

- **Topic.** Prime count <= N, prime reciprocal sum <= harmonic, Chebyshev theta bounds, PNT deviation, prime-zero duality.
- **Role.** Zeta (prime sums). Self-contained.
- **Counts.** Qed 27 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ счёт простых; обратные простых; Чебышёв theta. _Roles:_ простые суммы как роли; prime-zero дуальность. _Rules:_ prime_recip_le_harmonic; chebyshev_theta; prime_zero_duality. _P4:_ простые суммы и theta точны над Q (Element).
- **Classical counterpart.** Prime-counting and prime-reciprocal/Chebyshev-theta bounds, and a prime-zero duality, are classical; NEW: nothing — exact Q prime-sum bounds.
- **Tags.** zeta, prime-sum, chebyshev, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `prime_count prime_recip prime_recip_le_harmonic chebyshev_theta pnt_deviation prime_zero_duality prime_zero_duality_holds` | Definition/Lemma | счёт простых, обратные, theta, дуальность |

**Key lemmas (deep):**

- **`prime_zero_duality`** - Дуальность простые↔нули: оценки простых сумм (Чебышёв theta) связаны с zero-free регионом над Q. Element-сторона аналитической теории чисел. _(prime-sum, chebyshev, duality)_

**Uniqueness - score 1 (exposition).** Оценки простых сумм над Q (обратные ≤ гармонический, Чебышёв theta, prime-zero дуальность).
> _Caveat:_ Классика; ценность — Q-точность.

---

## #1818 - `src/zeta/RH_FinalAssessment.v` - score 3 (synthesis+observation)

**RH final assessment over Q: honest ledger of proved vs gap**

- **Topic.** Proved items (Li computable/nonneg on line, Weil-Li equiv, variance bounded, zeta converges, Mertens nonneg), the conditional RH, the_honest_gap, and the three-problems-one-framework view.
- **Role.** Zeta/RH (honest meta-assessment). Self-contained. June 2026 wave-4 sweep: vacuous computability-shams (exists q, _ == q) replaced by the by-type finite-ratio form or real identities; see UNIQUENESS.md.
- **Counts.** Qed 16 / Admitted 0 / axioms 0
- **Imports.** ToS zeta files
- **E/R/R.** _Elements:_ доказанные пункты к RH; честный пробел. _Roles:_ оценка как честная роль (что доказано/не доказано). _Rules:_ conditional_rh_proved; the_honest_gap. _P4:_ ★ честный реестр: доказано (Li-вычислимость, неотрицательность на линии), conditional RH, the_honest_gap явно назван.
- **Classical counterpart.** An honest assessment of what is and isn't proven toward RH (with YM/NS as siblings) is meta-commentary; NEW is only the explicit honest ledger: what is proved (Li computable, nonneg on line, ...), the conditional RH, and the_honest_gap.
- **Tags.** zeta, RH, honest-gap, assessment, synthesis

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `proved_li_computable/nonneg_on_line proved_weil_li_equiv proved_variance_bounded conditional_rh the_honest_gap three_problems_one_framework rh_grand_summary` | Definition/Lemma | ★ честный реестр доказанного и пробела June 2026 wave-4 sweep: vacuous computability-shams (exists q, _ == q) replaced by the by-type finite-ratio form or real identities; see UNIQUENESS.md. |

**Key lemmas (deep):**

- **`the_honest_gap`** - ★ Явно назван ЧЕСТНЫЙ ПРОБЕЛ: доказаны Li-вычислимость, неотрицательность на линии, ограниченность дисперсии, но НЕ полная RH (conditional только). Образец честности проекта — RH остаётся open, что доказано перечислено точно. _(RH, honest-gap, conditional)_

**Uniqueness - score 3 (synthesis+observation).** Честный реестр к RH над Q: что ДОКАЗАНО (Li-вычислимость/неотрицательность/Weil-Li-эквив./дисперсия) vs the_honest_gap (полная RH не доказана, conditional).
> _Caveat:_ НЕ доказательство RH; ценность — машинно-точная честная самооценка + единая рамка с YM/NS.

---

## #1819 - `src/zeta/RH_Phase1_Synthesis.v` - score 2 (new-framing)

**RH phase-1 synthesis over Q: the squeeze toward 1/2**

- **Topic.** Left/right walls, the squeeze, rh_gap approaching 1/2, rh_requires_gap_to_zero, P4 computability, three-millennium link.
- **Role.** Zeta/RH (phase-1 squeeze). Self-contained. June 2026 wave-4 sweep: vacuous computability-shams (exists q, _ == q) replaced by the by-type finite-ratio form or real identities; see UNIQUENESS.md.
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** ToS zeta files
- **E/R/R.** _Elements:_ левая/правая стены; зазор к 1/2. _Roles:_ зажатие к критической линии как роль. _Rules:_ squeeze; rh_requires_gap_to_zero. _P4:_ зажатие как процесс; rh_requires_gap_to_zero честно — нужен предел зазора 0.
- **Classical counterpart.** A squeeze toward the critical line (left/right walls, gap to 1/2) is a heuristic; NEW: nothing — exact Q phase-1 squeeze with honest 'requires gap to zero'.
- **Tags.** zeta, RH, squeeze, honest, new-framing

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `left_wall right_wall squeeze rh_gap rh_gap_approaches_half rh_requires_gap_to_zero p4_computability three_millennium rh_phase1_complete` | Definition/Lemma | зажатие, зазор, честное требование June 2026 wave-4 sweep: vacuous computability-shams (exists q, _ == q) replaced by the by-type finite-ratio form or real identities; see UNIQUENESS.md. |

**Key lemmas (deep):**

- **`rh_requires_gap_to_zero`** - Зажатие к Re=1/2 (стены) приближает зазор, но RH ТРЕБУЕТ зазор→0 — честно помечено, что зажатие не замыкает. Образец честности: процесс приближается, но не достигает. _(RH, squeeze, honest)_

**Uniqueness - score 2 (new-framing).** Фаза-1 зажатие к критической линии над Q (стены, зазор) с честным rh_requires_gap_to_zero.
> _Caveat:_ Не доказательство RH; зажатие не замыкает (честно).

---

## #1820 - `src/zeta/RH_Phase2_Synthesis.v` - score 2 (new-framing)

**RH phase-2 synthesis over Q: unconditional results + the wall**

- **Topic.** Three faces of RH (PNT error, critical value, reflection symmetry), unconditional results (zero-free Re=1, squeeze, Mertens, log-zeta nonneg), and the_wall / wall_holds.
- **Role.** Zeta/RH (phase-2 unconditional + wall). Self-contained. June 2026 wave-4 sweep: vacuous computability-shams (exists q, _ == q) replaced by the by-type finite-ratio form or real identities; see UNIQUENESS.md. June 2026 wave-4 sweep: vacuous computability-shams (exists q, _ == q) replaced by the by-type finite-ratio form or real identities; see UNIQUENESS.md.
- **Counts.** Qed 22 / Admitted 0 / axioms 0
- **Imports.** ToS zeta files
- **E/R/R.** _Elements:_ безусловные результаты; стена. _Roles:_ три грани RH; безусловное vs стена. _Rules:_ unconditional_*; the_wall; wall_holds. _P4:_ ★ безусловные результаты (zero-free Re=1, Мертенс) отделены от the_wall (RH-остаток) — честно.
- **Classical counterpart.** Listing unconditional results (zero-free Re=1, Mertens, log-zeta nonneg) and the remaining 'wall' is meta; NEW: only the explicit unconditional/wall ledger (three faces of RH).
- **Tags.** zeta, RH, unconditional, wall, new-framing

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `rh_three_faces unconditional_zero_free_re1 unconditional_squeeze unconditional_mertens unconditional_log_zeta_nonneg the_wall wall_holds wall_breaker rh_phase2_complete` | Definition/Lemma | ★ три грани, безусловное, стена June 2026 wave-4 sweep: vacuous computability-shams (exists q, _ == q) replaced by the by-type finite-ratio form or real identities; see UNIQUENESS.md. |

**Key lemmas (deep):**

- **`the_wall`** - ★ Явно назван the_wall — остаток RH за безусловными результатами (zero-free Re=1, Мертенс, log-zeta нонотр.). Честное разделение: что доказано безусловно vs где стена. Три грани RH (ошибка ТРПЧ/критич. значение/симметрия). _(RH, unconditional, wall, honest)_

**Uniqueness - score 2 (new-framing).** Фаза-2 над Q: безусловные результаты (zero-free Re=1, Мертенс, log-zeta≥0) отделены от the_wall (RH-остаток); три грани RH.
> _Caveat:_ Не доказательство RH; честное разделение безусловное/стена.

---

## #1821 - `src/zeta/RH_Statement.v` - score 3 (new-framing)

**RH statement over Q: zeros <-> process <-> fixed-point**

- **Topic.** RH_zeros / RH_process / RH_fixed, their equivalences (RH_all_equivalent), conjugate on the line, Re-Cauchy, the deviation bound, critical strip width.
- **Role.** Zeta/RH (the statement, P4 form). Self-contained. June 2026 wave-4 sweep: vacuous computability-shams (exists q, _ == q) replaced by the by-type finite-ratio form or real identities; see UNIQUENESS.md.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ формулировки RH (нули/процесс/неподвижная точка). _Roles:_ RH как тройная эквивалентность. _Rules:_ RH_zeros_iff_process; RH_process_implies_fixed; RH_all_equivalent. _P4:_ ★ RH переформулирована как нули⟺процесс⟺неподвижная точка (RH_all_equivalent), аксиомо-свободно — вена C/E.
- **Classical counterpart.** The Riemann Hypothesis statement (all nontrivial zeros on Re=1/2) is classical; NEW is only the P4 reformulation: RH as the equivalence zeros <-> process <-> fixed-point (RH_all_equivalent), axiom-free.
- **Tags.** zeta, RH, three-equivalence, fixed-point, new-framing

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `RH_zeros RH_process RH_fixed RH_zeros_iff_process RH_process_implies_fixed RH_fixed_implies_process RH_all_equivalent RH_conj_on_line RH_re_cauchy RH_deviation_bound` | Definition/Lemma | ★ три формулировки RH и их эквивалентность |

**Key lemmas (deep):**

- **`RH_all_equivalent`** - ★ RH переформулирована как ТРОЙНАЯ эквивалентность: нули-на-линии ⟺ процесс-свойство ⟺ неподвижная-точка-отражения, аксиомо-свободно над Q. Книжный флагман Части XIII: RH как процессный/неподвижно-точечный вопрос (вена C/E). НЕ доказательство — переобрамление. _(RH, three-equivalence, fixed-point, flagship)_

**Uniqueness - score 3 (new-framing).** RH как тройная эквивалентность нули⟺процесс⟺неподвижная точка (RH_all_equivalent), аксиомо-свободно — книжный флагман Части XIII.
> _Caveat:_ НЕ доказательство RH; переобрамление формулировки как процессного/неподвижно-точечного вопроса (с честной границей в ContractionZeros: отражение — изометрия не сжатие).

---

## #1822 - `src/zeta/TrigInequality.v` - score 2 (methods)

**Trig inequality over Q: the zero-free-region inequality**

- **Topic.** The Mertens function f, its trig form, the algebraic inequality (via a square), double-angle form, weighted Mertens nonneg, the product lower bound, Mertens preventing a zero.
- **Role.** Zeta (zero-free trig inequality). Self-contained.
- **Counts.** Qed 34 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ триг-неравенство; Мертенс f. _Roles:_ неравенство как роль zero-free региона. _Rules:_ trig_inequality_algebraic (через квадрат); mertens_prevents_zero. _P4:_ триг-неравенство доказано АЛГЕБРАИЧЕСКИ (через квадрат ≥0) над Q (Element); полюс бьёт ноль.
- **Classical counterpart.** The classical 3+4cos+cos2theta>=0 trig inequality behind the zero-free region (and a Mertens form) is classical; NEW: nothing — exact Q algebraic/double-angle proof of the inequality.
- **Tags.** zeta, trig-inequality, zero-free, algebraic, methods

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `mertens_f trig_form_eq_mertens trig_inequality_algebraic mertens_f_nonneg double_angle_form trig_inequality_double_angle weighted_mertens_nonneg product_lower_bound mertens_prevents_zero pole_beats_zero_order` | Definition/Lemma | ★ триг-неравенство (через квадрат), Мертенс ≥0 |

**Key lemmas (deep):**

- **`trig_inequality_algebraic`** - Классическое неравенство 3+4cosθ+cos2θ≥0 (за zero-free регионом) доказано АЛГЕБРАИЧЕСКИ над Q — как квадрат (1+cosθ)²·2 ≥0, без вещественной тригонометрии. Element-сторона: ключевое неравенство ТЧ как рациональное тождество. mertens_prevents_zero: полюс бьёт порядок нуля. _(trig-inequality, zero-free, algebraic, mertens)_

**Uniqueness - score 2 (methods).** Триг-неравенство zero-free региона доказано АЛГЕБРАИЧЕСКИ над Q (через квадрат ≥0, без вещественной тригонометрии) + форма Мертенса.
> _Caveat:_ Неравенство 3+4cos+cos2θ≥0 классично; вклад — алгебраическое Q-доказательство (квадрат), не вещественный анализ.

---

## #1823 - `src/zeta/WeilPositivity.v` - score 2 (new-framing)

**Weil positivity over Q: RH-equivalent PSD criterion**

- **Topic.** Weil entries (symmetric, rational), 1x1/diagonal PSD, PSD on the line, Weil = Li, PSD computable, the three-criteria equivalence.
- **Role.** Zeta/RH (Weil positivity = Li). Self-contained. June 2026 wave-4 sweep: vacuous computability-shams (exists q, _ == q) replaced by the by-type finite-ratio form or real identities; see UNIQUENESS.md.
- **Counts.** Qed 22 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ Weil-форма; PSD-условие. _Roles:_ Weil-позитивность как RH-эквивалент (=Li). _Rules:_ weil_equals_li; psd_on_line; p4_weil_deterministic. _P4:_ Weil-критерий РАЗРЕШИМ (p4_weil_deterministic) над Q; PSD на линии; Weil=Li (три эквивалентных критерия).
- **Classical counterpart.** Weil's positivity criterion (RH iff a certain quadratic form is positive semidefinite), equivalent to Li, is classical; NEW: nothing — exact Q Weil entries, PSD-on-line, Weil=Li, computable.
- **Tags.** zeta, weil, li, RH, new-framing

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `weil_entry weil_symmetric psd_diagonal psd_on_line weil_equals_li psd_computable three_criteria_equivalence p4_weil_on_line/deterministic weil_positivity_summary` | Definition/Lemma | ★ Weil-форма PSD, =Li, разрешимо June 2026 wave-4 sweep: vacuous computability-shams (exists q, _ == q) replaced by the by-type finite-ratio form or real identities; see UNIQUENESS.md. |

**Key lemmas (deep):**

- **`three_criteria_equivalence`** - Weil-позитивность = Li-критерий = RH (три эквивалентных критерия) над Q, с PSD на линии и разрешимой проверкой (p4_weil_deterministic). Переобрамление RH как разрешимого PSD-критерия; не доказательство. _(weil, li, RH, PSD, equivalence)_

**Uniqueness - score 2 (new-framing).** Weil-позитивность над Q: RH⟺PSD-форма, Weil=Li (три эквивалентных критерия), PSD на линии, ВЫЧИСЛИМО.
> _Caveat:_ Weil-критерий — классический RH-эквивалент; ново — разрешимая Q-формулировка + явная Weil=Li, не доказательство RH.

---

## #1824 - `src/zeta/ZeroCountingProcess.v` - score 2 (new-framing)

**Zero counting process over Q: RH = zero variance**

- **Topic.** Zero-count bounds (monotone, asymptotic, linear), density exponents, zero pairs averaging to 1/2, pair involution, RH = zero variance (no deviation), zero count computable.
- **Role.** Zeta/RH (zero counting, P4). Self-contained. June 2026 wave-4 sweep: vacuous computability-shams (exists q, _ == q) replaced by the by-type finite-ratio form or real identities; see UNIQUENESS.md. June 2026 wave-4 sweep: vacuous computability-shams (exists q, _ == q) replaced by the by-type finite-ratio form or real identities; see UNIQUENESS.md.
- **Counts.** Qed 33 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ счёт нулей; пары нулей. _Roles:_ счёт нулей как процесс; RH = нулевая дисперсия. _Rules:_ pair_average_half; rh_zero_variance; zero_count_computable. _P4:_ ★ счёт нулей как процесс; RH ⟺ нулевая дисперсия отклонения пар от 1/2 (rh_zero_variance) над Q.
- **Classical counterpart.** Riemann-von Mangoldt zero-counting bounds and density, with zero pairs averaging to 1/2 (RH = zero variance), are classical; NEW: only the P4 framing: zero count as a process, RH = zero variance of the pair-deviation.
- **Tags.** zeta, RH, zero-counting, variance, new-framing

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `zero_count_bound zero_count_asymptotic density_exponent zero_pair_re pair_average_half pair_involution rh_zero_variance rh_implies_no_deviation zero_count_process zero_count_computable` | Definition/Lemma | ★ счёт нулей-процесс, RH=нулевая дисперсия June 2026 wave-4 sweep: vacuous computability-shams (exists q, _ == q) replaced by the by-type finite-ratio form or real identities; see UNIQUENESS.md. |

**Key lemmas (deep):**

- **`rh_zero_variance`** - RH переформулирована как НУЛЕВАЯ ДИСПЕРСИЯ: пары нулей {ρ, 1−ρ} усредняются к Re=1/2, и RH ⟺ отклонение каждой пары = 0 (нулевая дисперсия). P4: счёт нулей как процесс, RH как статистическое нулевое-отклонение над Q. Не доказательство. _(RH, zero-variance, zero-counting, P4)_

**Uniqueness - score 2 (new-framing).** Счёт нулей как процесс над Q; RH ⟺ нулевая дисперсия отклонения пар нулей от 1/2 (rh_zero_variance).
> _Caveat:_ Счёт нулей и пары классичны; ново — RH как нулевая-дисперсия процессная формулировка, не доказательство.

---

## #1825 - `src/zeta/ZeroFreeRegion.v` - score 1 (exposition)

**Zero-free region over Q: pole repulsion**

- **Topic.** Pole lower bound (unbounded), Mertens from trig, zeta cube unbounded, DVP width decreasing toward 1, pole drives repulsion, zeta positive on integers.
- **Role.** Zeta/RH (zero-free region). Self-contained. June 2026 wave-4 sweep: vacuous computability-shams (exists q, _ == q) replaced by the by-type finite-ratio form or real identities; see UNIQUENESS.md.
- **Counts.** Qed 21 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ полюс; DVP-ширина; отталкивание. _Roles:_ zero-free регион как роль (отталкивание полюсом). _Rules:_ pole_drives_repulsion; dvp_boundary_approaches_1. _P4:_ полюс отталкивает нули (zero-free) над Q (Element); три элементарных неравенства.
- **Classical counterpart.** The de la Vallee-Poussin zero-free region (pole repulsion, three elementary inequalities) is classical; NEW: nothing — exact Q zero-free region via pole repulsion.
- **Tags.** zeta, zero-free, DVP, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `pole_lower_bound pole_large mertens_from_trig zeta_cube_unbounded dvp_width dvp_boundary_approaches_1 pole_drives_repulsion zeta_positive_all three_elementary_inequalities` | Definition/Lemma | полюс отталкивает, DVP-граница |

**Key lemmas (deep):**

- **`pole_drives_repulsion`** - Полюс дзеты в s=1 ОТТАЛКИВАЕТ нули (zero-free регион де ла Валле-Пуссена) через три элементарных неравенства над Q. Element-сторона: классический zero-free регион рационально. _(zero-free, pole-repulsion, DVP)_

**Uniqueness - score 1 (exposition).** Zero-free регион над Q через отталкивание полюсом (DVP-ширина → 1, три неравенства).
> _Caveat:_ DVP zero-free регион классичен; ценность — Q-формализация.

---

## #1826 - `src/zeta/ZeroMigration.v` - score 2 (new-framing)

**Zero migration over Q: unbiased, centered at 1/2**

- **Topic.** Perturbation bounds (decreasing), cumulative perturbation, pair deviation antisymmetric, paired deviation zero, variance bounded, unbiased migration centered at 1/2.
- **Role.** Zeta/RH (zero migration process). Self-contained. June 2026 wave-4 sweep: vacuous computability-shams (exists q, _ == q) replaced by the by-type finite-ratio form or real identities; see UNIQUENESS.md.
- **Counts.** Qed 28 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ миграция нулей; отклонение пар. _Roles:_ миграция как процесс; несмещённость к 1/2. _Rules:_ paired_deviation_zero; unbiased_migration; cumulative_variance_bounded. _P4:_ миграция нулей как процесс с НЕСМЕЩЁННЫМ (к 1/2) отклонением и ограниченной дисперсией над Q.
- **Classical counterpart.** Tracking how perturbed zeros migrate (bounded perturbation, pairs centered at 1/2, unbiased migration) is a heuristic; NEW: only the P4 framing: zero migration as a process with unbiased (centered-at-1/2) deviation and bounded cumulative variance.
- **Tags.** zeta, zero-migration, unbiased, new-framing

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `perturbation_bound cumulative_perturbation reflect_involution average_is_half deviation_antisymmetric paired_deviation_zero variance_term cumulative_variance_bounded unbiased_migration/holds/centered` | Definition/Lemma | миграция, несмещённость, ограниченная дисперсия June 2026 wave-4 sweep: vacuous computability-shams (exists q, _ == q) replaced by the by-type finite-ratio form or real identities; see UNIQUENESS.md. |

**Key lemmas (deep):**

- **`unbiased_migration`** - Миграция нулей НЕСМЕЩЕНА (центрирована на Re=1/2): отклонения пар антисимметричны, сумма = 0, кумулятивная дисперсия ограничена над Q. P4-процессное переобрамление статистики нулей; согласуется с RH=нулевая-дисперсия, не доказательство. _(zero-migration, unbiased, variance, P4)_

**Uniqueness - score 2 (new-framing).** Миграция нулей как несмещённый (к 1/2) процесс над Q с ограниченной кумулятивной дисперсией.
> _Caveat:_ Эвристика статистики нулей; P4-переобрамление, не доказательство RH.

---

## #1827 - `src/zeta/ZeroStructure.v` - score 2 (new-framing)

**Zero structure over Q: empty / discrete / continuum dichotomy**

- **Topic.** A zero collection, its dichotomy (empty enumerable / singleton discrete / continuum has perfect subset), encoding, conjugate/bp-closed, zero classification.
- **Role.** Zeta/RH (zero structure, vein C/E). Reuses ProcessTypes dichotomy. Self-contained. June 2026 wave-4 sweep: vacuous computability-shams (exists q, _ == q) replaced by the by-type finite-ratio form or real identities; see UNIQUENESS.md.
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; ProcessTypes-style dichotomy
- **E/R/R.** _Elements:_ коллекция нулей; её тип (пусто/дискретно/континуум). _Roles:_ структура нулей как дихотомия (как PCH). _Rules:_ zero_dichotomy; continuum_has_perfect; discrete_is_enumerable. _P4:_ структура нулей подчиняется ТОЙ ЖЕ дихотомии (счётно/совершенно), что ProcessContinuumHypothesis — связь RH с процессной несчётностью.
- **Classical counterpart.** Classifying a zero collection as empty/discrete/continuum (with a perfect-subset dichotomy) mirrors descriptive set theory; NEW is only the link to the process-uncountability dichotomy (zeros empty/enumerable/perfect).
- **Tags.** zeta, zero-structure, dichotomy, vein-C, new-framing

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `zero_collection zero_dichotomy empty_zeros_enumerable singleton_zero_discrete zero_collection_conj zero_structure discrete_is_enumerable continuum_has_perfect` | Definition/Lemma | дихотомия нулей (пусто/дискретно/континуум) |

**Key lemmas (deep):**

- **`zero_dichotomy`** - Коллекция нулей дзеты подчиняется дихотомии пусто/дискретно(счётно)/континуум(совершенное подмножество) — ТА ЖЕ структурная дихотомия, что ProcessContinuumHypothesis. Связывает RH-структуру нулей с процессной несчётностью (вена C/E). _(zero-structure, dichotomy, perfect-subset, vein-C)_

**Uniqueness - score 2 (new-framing).** Структура нулей дзеты как дихотомия пусто/дискретно/континуум (совершенное подмножество) — та же, что PCH; связь RH с процессной несчётностью.
> _Caveat:_ Дескриптивная классификация известна; ново — связь нулей дзеты с процессной дихотомией PCH.

---

## #1828 - `src/zeta/ZetaProcess.v` - score 2 (new-framing)

**Zeta as a process over Q: Cauchy for Re>=2, diverges at 1**

- **Topic.** Zeta term/partial/process, terms positive/<=1/monotone, shifted-telescope bound, partial bounded, the process Cauchy, zeta_1 not Cauchy (diverges), the generalized zeta process.
- **Role.** Zeta (zeta as process, vein C). Self-contained.
- **Counts.** Qed 25 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ дзета-члены; частичные суммы; процесс. _Roles:_ дзета как Cauchy-процесс; полюс в 1 как role-limit. _Rules:_ zeta_process_cauchy; zeta_diverges_at_1. _P4:_ ★ дзета ЕСТЬ процесс частичных сумм (Element); Cauchy для Re≥2, расходится при s=1 (полюс, role-limit).
- **Classical counterpart.** Zeta(s) as a Cauchy process of partial sums (convergent for s>=2, divergent at 1) is the constructive view; NEW is only the P4 framing: zeta IS a process, monotone, Cauchy for Re>=2, diverging at 1.
- **Tags.** zeta, process, cauchy, vein-C, new-framing

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `zeta_term zeta_partial zeta_process zeta_term_le_1 zeta_partial_bounded zeta_process_cauchy zeta_process_monotone_k zeta_1_not_cauchy zeta_diverges_at_1 zeta_gen_cauchy` | Definition/Lemma | ★ дзета-процесс Cauchy, расходимость при 1 |

**Key lemmas (deep):**

- **`zeta_process_cauchy`** - Дзета(s) ЕСТЬ Cauchy-процесс частичных сумм (через сдвинутый телескоп) для Re≥2 над Q, монотонный; при s=1 расходится (zeta_diverges_at_1, полюс). Вена C в теории чисел: дзета как процесс, полюс = role-limit. _(zeta, process, cauchy, vein-C)_

**Uniqueness - score 2 (new-framing).** Дзета как Cauchy-процесс частичных сумм над Q (сходится Re≥2, расходится при 1=полюс) — вена C.
> _Caveat:_ Дзета как ряд классична; ново — явное P4/процесс-обрамление.

---

## #1829 - `src/zeta/ZetaZeros.v` - score 1 (exposition)

**Zeta zeros over Q: Cauchy-complex, critical strip/line, conjugates**

- **Topic.** CauchyComplex, is_cauchy_complex, nontrivial/trivial zeros, the critical strip and line, conjugate zeros (involutive), trivial zeros real.
- **Role.** Zeta/RH (zeros as Cauchy-complex). Self-contained.
- **Counts.** Qed 14 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ комплексные Коши-числа; нули. _Roles:_ нули как Cauchy-комплексные; критическая полоса/линия. _Rules:_ is_nontrivial_zero; on_critical_line; conj_zero_involutive. _P4:_ нули как Cauchy-комплексные процессы над Q (Element); сопряжённый ноль — инволюция.
- **Classical counterpart.** Nontrivial/trivial zeros, the critical strip/line, and conjugate symmetry over Cauchy-complex numbers are classical; NEW is only the constructive Q form: zeros as Cauchy-complex with decidable critical-strip/line predicates.
- **Tags.** zeta, zeros, cauchy-complex, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `CauchyComplex is_cauchy_complex is_nontrivial_zero on_critical_line trivial_zero conj_zero conj_zero_involutive trivial_zero_real` | Definition/Lemma | Cauchy-комплексные нули, полоса/линия |

**Key lemmas (deep):**

- **`conj_zero_involutive`** - Сопряжение нулей дзеты инволютивно над Cauchy-комплексными Q-числами; нетривиальные/тривиальные нули, критическая полоса/линия определены конструктивно. Element-сторона: нули как Cauchy-комплексные процессы. _(zeta-zeros, cauchy-complex, conjugate)_

**Uniqueness - score 1 (exposition).** Нули дзеты как Cauchy-комплексные над Q (критическая полоса/линия, сопряжение инволютивно).
> _Caveat:_ Структура нулей классична; ценность — конструктивная Cauchy-комплексная Q-форма.

