# Database - cluster `fermions`

_Generated from `fermions.json` by `generate.ps1` - do not edit by hand; edit the JSON._

**5 files / 52 Qed.** Score distribution: s5=0 / s4=0 / s3=0 / s2=1 / s1=4 / s0=0

---

## #154 - `src/fermions/DiracOnGraph.v` - score 2 (methods)

**Dirac operator on a graph over Q: zero mode, mass gap, doublers**

- **Topic.** Squared Dirac eigenvalue and fermion propagator on a graph, the massless zero mode, a massive gap, heavy doublers, chirality from L2, Dirac antisymmetry, and an N=4 spectrum check.
- **Role.** Leaf of the fermions (SM-from-graph) branch. Self-contained (QArith). SM-from-distinction is OVER-BRANDED. June 2026 rollback: 2 True-stubs (chirality_from_L2, dirac_antisymmetric) REMOVED — need spinor structure; replaced by GENERAL bounds eigenvalue_sq_nonneg / eigenvalue_gap_general (m^2 <= E^2 at ALL momenta) / propagator_positive.
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ решёточный оператор Дирака; собственные значения; пропагатор. _Roles:_ нулевая мода = безмассовый фермион (роль); киральность из L2. _Rules:_ massless_zero_mode; massive_gap; doubler_heavy; chirality_from_L2. _P4:_ конечный решёточный спектр над Q (Element); НЕ вывод физического Дирака — over-branded ветвь.
- **Classical counterpart.** The lattice Dirac operator, fermion doubling, the massless zero mode and chirality are standard lattice gauge theory; here only a small Q instance — NOT a derivation of the physical Dirac equation.
- **Tags.** fermions, dirac, lattice, over-branded, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `dirac_eigenvalue_sq/fermion_propagator_sq/massless_zero_mode/massive_gap/doubler_heavy` | Definition/Theorem | ★ спектр Дирака, нулевая мода, дублёры June 2026 rollback: 2 True-stubs (chirality_from_L2, dirac_antisymmetric) REMOVED — need spinor structure; replaced by GENERAL bounds eigenvalue_sq_nonneg / eigenvalue_gap_general (m^2 <= E^2 at ALL momenta) / propagator_positive. |
| `eigenvalue_k1_N4/propagator_value/eigenvalue_grows_with_k/_with_mass/chirality_from_L2` | Theorem | рост собственных значений, киральность June 2026 rollback: 2 True-stubs (chirality_from_L2, dirac_antisymmetric) REMOVED — need spinor structure; replaced by GENERAL bounds eigenvalue_sq_nonneg / eigenvalue_gap_general (m^2 <= E^2 at ALL momenta) / propagator_positive. |
| `dirac_antisymmetric/n4_spectrum_check/dirac_on_graph_synthesis` | Theorem | антисимметрия, проверка спектра June 2026 rollback: 2 True-stubs (chirality_from_L2, dirac_antisymmetric) REMOVED — need spinor structure; replaced by GENERAL bounds eigenvalue_sq_nonneg / eigenvalue_gap_general (m^2 <= E^2 at ALL momenta) / propagator_positive. |

**Key lemmas (deep):**

- **`massless_zero_mode`** - Безмассовая нулевая мода и тяжёлые дублёры — корректная решёточная картина фермионного удвоения над Q. Но это стандартная решёточная конструкция, не вывод физического Дирака; SM-from-graph здесь OVER-BRANDED. _(dirac, zero-mode, doubling, over-branded)_

**Uniqueness - score 2 (methods).** Оператор Дирака на графе над Q: нулевая мода, массовый зазор, тяжёлые дублёры, киральность из L2.
> _Caveat:_ Решёточный Дирак и удвоение фермионов классичны; вклад — Q-инстанс; формулировка SM-из-графа OVER-BRANDED.

---

## #155 - `src/fermions/GaugeLoops.v` - score 1 (exposition)

**Gauge loops over Q: Higgs mass corrections (signs)**

- **Topic.** A 4-mode gauge loop sum, gauge and self-energy contributions to the Higgs mass, the total correction and its sign, with gauge positive and top negative.
- **Role.** Leaf of the fermions/Higgs-correction branch (with TopLoop, HiggsDiagnostic). Self-contained.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ петлевые вклады в массу Хиггса (gauge/self/top). _Roles:_ петля = роль-поправка; знак вклада как роль. _Rules:_ gauge_positive; self_positive; top_negative; total_sign. _P4:_ конечные петлевые суммы над Q (Element); знаковая бухгалтерия поправок.
- **Classical counterpart.** Gauge and self-energy loop corrections to the Higgs mass (positive gauge, sign structure) are standard radiative-correction bookkeeping; here only small Q sign computations.
- **Tags.** fermions, gauge-loop, higgs, exposition

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `gauge_loop_sum_4/delta_mH_gauge/delta_mH_self/our_delta_total` | Definition | петлевые суммы и вклады |
| `gauge_loop_value/gauge_positive/gauge_correction_value/self_positive/self_correction_value` | Theorem | ★ gauge-вклад положителен |
| `top_negative/total_sign/total_correction_value/gauge_loops_synthesis` | Theorem | top отрицателен, суммарный знак |

**Key lemmas (deep):**

- **`gauge_positive`** - Gauge-петля даёт положительный вклад в массу Хиггса, top — отрицательный — простая знаковая бухгалтерия радиационных поправок над Q. Содержательной уникальности нет. _(gauge-loop, higgs, sign)_

**Uniqueness - score 1 (exposition).** Gauge-петли над Q: знаки вкладов в массу Хиггса (gauge+, top−).
> _Caveat:_ Знаковая структура радиационных поправок стандартна; Q-вычисление без нового содержания.

---

## #156 - `src/fermions/HiggsDiagnostic.v` - score 1 (exposition)

**Higgs diagnostic over Q: top drives negative, gauge positive**

- **Topic.** The top loop drives the Higgs mass-squared negative, gauge drives positive, the total correction positive, a finite propagator, the mass hierarchy, Dirac spectrum from the graph, and Yukawa from L2.
- **Role.** Diagnostic leaf of the fermions/Higgs branch. Self-contained. June 2026 rollback: 2 True-stubs (dirac_spectrum_from_graph, yukawa_from_L2) REMOVED; replaced by re-statements of the real general facts: dirac_gap_at_all_momenta, yukawa_ratio_law.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ вклады top/gauge в массу Хиггса; пропагатор. _Roles:_ диагностика знака массы² Хиггса как роль. _Rules:_ top_drives_negative; gauge_drives_positive; total_correction_positive. _P4:_ конечные оценки над Q (Element); диагностический узел.
- **Classical counterpart.** That the top loop drives the Higgs mass-squared negative (hierarchy/naturalness bookkeeping) and gauge loops drive it positive is standard; here a small Q diagnostic.
- **Tags.** fermions, higgs, diagnostic, exposition

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `top_drives_negative/gauge_drives_positive/total_correction_positive/propagator_finite` | Theorem | ★ top−, gauge+, итог положителен June 2026 rollback: 2 True-stubs (dirac_spectrum_from_graph, yukawa_from_L2) REMOVED; replaced by re-statements of the real general facts: dirac_gap_at_all_momenta, yukawa_ratio_law. |
| `mass_hierarchy/dirac_gap_at_all_momenta/yukawa_ratio_law/higgs_diagnostic_synthesis` | Theorem | иерархия масс, June 2026: щель на всех импульсах + закон отношения юкав (вместо удалённых заглушек) June 2026 rollback: 2 True-stubs (dirac_spectrum_from_graph, yukawa_from_L2) REMOVED; replaced by re-statements of the real general facts: dirac_gap_at_all_momenta, yukawa_ratio_law. |

**Key lemmas (deep):**

- **`top_drives_negative`** - Top-петля тянет массу² Хиггса вниз, gauge — вверх (диагностика натуральности) — стандартная бухгалтерия над Q, без нового результата. _(higgs, top, naturalness)_

**Uniqueness - score 1 (exposition).** Диагностика Хиггса над Q: top тянет массу² вниз, gauge вверх, суммарная поправка положительна.
> _Caveat:_ Бухгалтерия натуральности Хиггса стандартна; диагностический Q-узел без нового содержания.

---

## #157 - `src/fermions/TopLoop.v` - score 1 (exposition)

**Top loop over Q: color-factor correction to the Higgs mass**

- **Topic.** The number of colors N_c, a 4-mode top loop sum, the Higgs mass-squared correction, tree mass, the loop positive then the correction negative, growth with N_c, and the need for gauge loops.
- **Role.** Leaf of the fermions/Higgs-correction branch. Self-contained. June 2026 rollback: 2 True-stubs (grows_with_N — no N-parametric sum exists; need_gauge) REMOVED; replaced by loop_sum_decreasing_in_mass (DECOUPLING, general, via Qdiv_lt_pos) + top_alone_negative_mass (tree+top = -3/8 < 0 — the quantitative 'need gauge').
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ цветовой фактор N_c; петлевая сумма top. _Roles:_ top-петля = роль-поправка (∝ N_c); древесная масса. _Rules:_ top_loop_sum_4; top_correction negative; grows_with_N. _P4:_ конечная петлевая сумма над Q (Element); поправка растёт с N_c.
- **Classical counterpart.** The top-quark loop correction to the Higgs mass (proportional to N_c colors, negative) is a standard one-loop result; here only a small Q instance.
- **Tags.** fermions, top-loop, higgs, exposition

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `N_c/top_loop_sum_4/delta_mH_sq/mH_sq_tree` | Definition | цвета, петлевая сумма, древесная масса June 2026 rollback: 2 True-stubs (grows_with_N — no N-parametric sum exists; need_gauge) REMOVED; replaced by loop_sum_decreasing_in_mass (DECOUPLING, general, via Qdiv_lt_pos) + top_alone_negative_mass (tree+top = -3/8 < 0 — the quantitative 'need gauge'). |
| `top_loop_positive/top_loop_value/top_loop_negative/top_correction_value/tree_plus_top` | Theorem | ★ значение и знак top-поправки June 2026 rollback: 2 True-stubs (grows_with_N — no N-parametric sum exists; need_gauge) REMOVED; replaced by loop_sum_decreasing_in_mass (DECOUPLING, general, via Qdiv_lt_pos) + top_alone_negative_mass (tree+top = -3/8 < 0 — the quantitative 'need gauge'). |
| `top_loop_at_m1/top_correction_at_m1/top_loop_positive_m1/grows_with_N/need_gauge/top_loop_synthesis` | Theorem | рост с N_c, нужны gauge-петли June 2026 rollback: 2 True-stubs (grows_with_N — no N-parametric sum exists; need_gauge) REMOVED; replaced by loop_sum_decreasing_in_mass (DECOUPLING, general, via Qdiv_lt_pos) + top_alone_negative_mass (tree+top = -3/8 < 0 — the quantitative 'need gauge'). |

**Key lemmas (deep):**

- **`grows_with_N`** - Top-поправка растёт с числом цветов N_c — корректный цветовой фактор одной петли над Q. Стандартный результат, не новый. _(top-loop, color-factor, higgs)_

**Uniqueness - score 1 (exposition).** Top-петля над Q: поправка к массе Хиггса ∝ N_c, растёт с числом цветов.
> _Caveat:_ Одно-петлевая top-поправка стандартна; Q-инстанс без нового содержания.

---

## #158 - `src/fermions/YukawaCoupling.v` - score 1 (exposition)

**Yukawa coupling over Q: top dominance**

- **Topic.** Top/bottom Yukawa values as DATA inputs, dominance arithmetic, mass = y·v. June 2026: yukawa_is_L2:True REMOVED; added GENERAL mass_ratio_is_yukawa_ratio (v cancels) and yukawa_values_are_data (any 0<y<1/10 satisfies the same dominance facts — values are data-selected).
- **Role.** Leaf of the fermions branch (mass generation). June 2026 honesty rollback: 'mass hierarchy FROM distinction-graph' RETIRED — y_top=1, y_bottom=1/40 are hardcoded observation-shaped inputs; proven content = dominance/ratio arithmetic GIVEN the inputs + the general ratio law + value-underdetermination. Self-contained.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ Юкава-константы (top/bottom); массы фермионов. _Roles:_ Юкава = роль-связь массы (из L2); top доминирует. _Rules:_ top_yukawa_one; bottom_negligible; mass_from_yukawa. _P4:_ конечные Q-значения констант (Element); Юкава как L2-роль.
- **Classical counterpart.** That the top Yukawa coupling is ~1 and dominates the fermion mass spectrum (bottom negligible) is standard SM phenomenology; here a small Q instance with 'Yukawa from L2'.
- **Tags.** fermions, yukawa, top, exposition

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `y_top_observed/y_bottom/top_dominance/fermion_mass` | Definition | Юкава-константы, масса |
| `top_yukawa_one/bottom_negligible/top_dominates/mass_from_yukawa` | Theorem | ★ top Юкава ~1, доминирует |
| `bottom_mass_small/mass_ratio/top_dominance_positive/yukawa_coupling_synthesis` | Theorem | малость bottom; June 2026: yukawa_is_L2:True УДАЛЕНА |
| `mass_ratio_is_yukawa_ratio / yukawa_values_are_data` | Theorem | ★ ОБЩИЙ слой (June 2026): отношение масс = отношение юкав (v сокращается, field); значения юкав = ДАННЫЕ (любое 0<y<1/10 даёт те же факты доминирования — nra) |

**Key lemmas (deep):**

- **`top_dominates`** - Top-Юкава ~1 доминирует над bottom — стандартная феноменология масс СМ над Q. Привязка «Юкава=L2» — модельная, не вывод. _(yukawa, top-dominance)_

**Uniqueness - score 1 (exposition).** Юкава над Q: top-связь ~1 доминирует, bottom пренебрежимо мала, Юкава=L2-роль.
> _Caveat:_ Доминирование top-Юкавы — стандартная феноменология СМ; Q-инстанс без нового содержания.

