# Database - cluster `navier_stokes`

_Generated from `navier_stokes.json` by `generate.ps1` - do not edit by hand; edit the JSON._

**35 files / 872 Qed.** Score distribution: s5=0 / s4=0 / s3=2 / s2=12 / s1=21 / s0=0

---

## #612 - `src/navier_stokes/AdvectionEnergyConservation.v` - score 1 (exposition)

**Advection conserves energy over Q (flux telescopes)**

- **Topic.** Energy flux for transport/Burgers, the flux telescoping (sums cancel), advection energy conservation derived.
- **Role.** NS (energy conservation of advection). Self-contained.
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ поток энергии адвекции. _Roles:_ сохранение энергии адвекцией как роль. _Rules:_ transport/burgers_flux_telescopes; conserves_energy. _P4:_ телескоп потока даёт сохранение точно над Q (Element).
- **Classical counterpart.** That the advection (transport/Burgers) term conserves energy (the flux telescopes) is standard NS structure; NEW: nothing — exact Q telescoping energy conservation.
- **Tags.** navier-stokes, energy-conservation, advection, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `energy_flux_transport/burgers transport_flux_telescopes burgers_conserves_energy advection_energy_conservation_derived` | Lemma | поток адвекции телескопирует ⟹ сохранение энергии |

**Key lemmas (deep):**

- **`advection_energy_conservation_derived`** - Адвективный член сохраняет энергию (поток телескопирует, суммы сокращаются) над Q — структурное свойство NS, ВЫВЕДЕННОЕ, а не постулированное. Element-сторона (связь с антисимметрией B). _(advection, energy-conservation, telescope)_

**Uniqueness - score 1 (exposition).** Сохранение энергии адвекцией над Q (телескоп потока).
> _Caveat:_ Стандартная структура NS; ценность — Q-вывод.

---

## #613 - `src/navier_stokes/AttackSynthesis.v` - score 2 (new-framing)

**NS attack synthesis over Q (three attacks, honest gap)**

- **Topic.** Three attacks (splitting, Ep interpolation, helicity/conditional), unconditional 2D/energy/Gronwall results, the millennium gap precise, the alpha gap.
- **Role.** NS (regularity attacks synthesis). Self-contained.
- **Counts.** Qed 33 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ три атаки на регулярность; безусловные/условные результаты. _Roles:_ синтез атак как роль; честный gap. _Rules:_ unconditional_2d; the_gap; millennium_gap_precise. _P4:_ безусловные результаты (2D, энергия) отделены от условного 3D — честный gap (Element).
- **Classical counterpart.** Multiple proof 'attacks' on NS regularity (splitting, interpolation, depletion) with unconditional 2D and conditional 3D results is the standard regularity toolbox; NEW: only the honest synthesis bundling them + the explicit alpha-gap.
- **Tags.** navier-stokes, attacks, honest, new-framing

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `attack_a/b/c three_attacks_summary unconditional_energy/2d/gronwall the_gap millennium_gap_precise attack_synthesis_main` | Definition/Lemma | три атаки, безусловные результаты, точный gap |

**Key lemmas (deep):**

- **`millennium_gap_precise`** - Три атаки на NS-регулярность дают безусловные 2D/энергия-результаты, но 3D остаётся УСЛОВНЫМ — gap назван точно (millennium_gap_precise). Честное разделение доказанного и стены. _(navier-stokes, attacks, honest-gap)_

**Uniqueness - score 2 (new-framing).** Синтез NS-атак над Q (безусловные 2D/энергия vs условный 3D), с ТОЧНО названным millennium gap.
> _Caveat:_ Регулярностные атаки стандартны; ново — честная сборка + явный gap (3D conditional).

---

## #614 - `src/navier_stokes/BKMCriterion.v` - score 1 (exposition)

**BKM criterion over Q**

- **Topic.** Blowup vs no-blowup, the BKM integral (monotone, bounded => regularity), vorticity bounded, bootstrap, finite Galerkin BKM.
- **Role.** NS (BKM criterion). Self-contained.
- **Counts.** Qed 18 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ BKM-интеграл; завихренность. _Roles:_ BKM как критерий регулярности. _Rules:_ bkm_bounded_implies_regularity; bkm_process_finite. _P4:_ BKM-интеграл конечен ⟹ регулярность (Element); галёркинский BKM финитен.
- **Classical counterpart.** The Beale-Kato-Majda criterion (no blowup iff the vorticity time-integral is finite) is classical; NEW: nothing — exact Q BKM with a bootstrap and finite Galerkin BKM.
- **Tags.** navier-stokes, BKM, vorticity, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `blowup_at no_blowup bkm_integral bkm_bounded_implies_regularity vorticity_bounded_bkm bootstrap_regularity galerkin_bkm_finite bkm_main` | Definition/Lemma | BKM-критерий, bootstrap, финитность |

**Key lemmas (deep):**

- **`bkm_bounded_implies_regularity`** - BKM: ограниченный интеграл завихренности ⟹ регулярность над Q; галёркинская версия финитна. Element-сторона критерия регулярности NS. _(BKM, vorticity, regularity)_

**Uniqueness - score 1 (exposition).** BKM-критерий над Q (ограниченный интеграл завихренности ⟹ регулярность, финитный галёркин).
> _Caveat:_ BKM классичен; ценность — Q-формализация.

---

## #615 - `src/navier_stokes/ClassicalRegularity.v` - score 2 (methods)

**Classical NS regularity over Q (Clay formulation)**

- **Topic.** Sobolev regularity/embedding, Serrin condition, uniqueness, the Clay initial data / nine steps, analyticity in time, higher regularity.
- **Role.** NS (classical regularity, Clay). Self-contained.
- **Counts.** Qed 30 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ Соболев-регулярность; условие Серрина. _Roles:_ классическая регулярность как роль (Clay). _Rules:_ serrin_condition; solution_unique; clay_nine_steps. _P4:_ классическая регулярность собрана над Q; Clay-формулировка (Element).
- **Classical counterpart.** Classical NS regularity (Sobolev embedding, Serrin condition, uniqueness, the Clay nine-step formulation) is the standard partial-regularity theory; NEW: nothing — a constructive Q assembly toward the Clay statement.
- **Tags.** navier-stokes, regularity, clay, methods

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `sobolev_regularity/embedding_3d serrin_condition solution_unique clay_nine_steps clay_formulation analyticity_in_time higher_regularity classical_regularity_main` | Definition/Lemma | Соболев, Серрин, единственность, Clay |

**Key lemmas (deep):**

- **`clay_formulation`** - Классическая NS-регулярность (Соболев, Серрин, единственность) собрана к Clay-формулировке (nine steps) над Q. Element-сторона; результат УСЛОВНЫЙ (опирается на оценки, см. TriadicInteraction axioms). _(regularity, clay, serrin)_

**Uniqueness - score 2 (methods).** Классическая NS-регулярность над Q (Соболев/Серрин/единственность, Clay nine steps).
> _Caveat:_ Классическая теория регулярности стандартна; результат УСЛОВНЫЙ (зависит от B_coeff_bounded в TriadicInteraction). Не безусловное решение Clay.

---

## #616 - `src/navier_stokes/ConcentrationBound.v` - score 1 (exposition)

**Concentration bound over Q**

- **Topic.** Max amplitude squared, single-mode energy bound, worst-pair forcing, uniform forcing bound, concentration does not help, conditional regularity.
- **Role.** NS (concentration estimate). Self-contained.
- **Counts.** Qed 20 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ концентрация мод; форсинг. _Roles:_ оценка концентрации как роль. _Rules:_ concentration_does_not_help; uniform_forcing_bound. _P4:_ концентрация не помогает blowup'у (Element); равномерная оценка форсинга.
- **Classical counterpart.** Bounding concentrated forcing / worst-case mode amplitude (concentration doesn't help blowup) is a standard regularity estimate; NEW: nothing — exact Q concentration bounds.
- **Tags.** navier-stokes, concentration, regularity, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `max_amplitude_sq single_mode_energy_bound worst_pair_forcing uniform_forcing_bound concentration_does_not_help conditional_regularity_theorem concentration_bound_main` | Definition/Lemma | оценка концентрации, равномерный форсинг |

**Key lemmas (deep):**

- **`concentration_does_not_help`** - Концентрация энергии в моде НЕ помогает blowup'у (равномерная оценка форсинга) над Q. Element-сторона условной регулярности NS. _(concentration, forcing, regularity)_

**Uniqueness - score 1 (exposition).** Оценка концентрации над Q (концентрация не помогает blowup'у, равномерный форсинг).
> _Caveat:_ Стандартная оценка; условная регулярность.

---

## #617 - `src/navier_stokes/Depletion.v` - score 1 (exposition)

**Depletion over Q**

- **Topic.** Alignment parameter, depletion factor, depleted stretching, conditional depletion regularity, modal helicity, full 2D depletion regularity.
- **Role.** NS (depletion). Self-contained.
- **Counts.** Qed 15 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ выравнивание; фактор истощения. _Roles:_ истощение нелинейности как роль. _Rules:_ depleted_stretching; depletion_2d_regularity. _P4:_ истощение даёт 2D-регулярность над Q (Element).
- **Classical counterpart.** Nonlinearity depletion (alignment reducing stretching, conditional regularity) and 2D depletion are standard; NEW: nothing — exact Q depletion factor and 2D regularity.
- **Tags.** navier-stokes, depletion, regularity, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `alignment_param depletion_factor depleted_stretching conditional_depletion_regularity modal_helicity depletion_2d_complete/regularity depletion_main` | Definition/Lemma | истощение, 2D-регулярность, спиральность |

**Key lemmas (deep):**

- **`depletion_2d_regularity`** - Истощение нелинейности (выравнивание уменьшает растяжение) даёт 2D NS-регулярность над Q; 3D условно. Element-сторона. _(depletion, 2D-regularity, helicity)_

**Uniqueness - score 1 (exposition).** Истощение нелинейности над Q (фактор истощения, 2D-регулярность, спиральность).
> _Caveat:_ Депление стандартно; 3D условно.

---

## #618 - `src/navier_stokes/EnergyConstraint.v` - score 1 (exposition)

**Energy constraint over Q: E-Omega-P triangle**

- **Topic.** Enstrophy/energy/palinstrophy as inner products, Ep interpolation, palinstrophy lower bound, optimal Young, the full norm hierarchy, time-integrated enstrophy bound.
- **Role.** NS (energy/enstrophy interpolation). Self-contained.
- **Counts.** Qed 20 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ энергия/энстрофия/палинстрофия. _Roles:_ E-Ω-P интерполяция как роль. _Rules:_ ep_interpolation; full_norm_hierarchy. _P4:_ интерполяционные оценки точны над Q (Element).
- **Classical counterpart.** The E-Omega-P interpolation triangle (Cauchy-Schwarz Omega^2<=EP, Young, the Sobolev hierarchy) is standard NS analysis; NEW: nothing — exact Q interpolation constraints.
- **Tags.** navier-stokes, interpolation, enstrophy, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `ep_interpolation palinstrophy_lower_bound optimal_young_parameter full_norm_hierarchy time_integrated_enstrophy_bound energy_constraint_main` | Definition/Lemma | E-Ω-P интерполяция, иерархия норм |

**Key lemmas (deep):**

- **`ep_interpolation`** - Интерполяция Ω²≤E·P (Коши-Шварц) и иерархия норм над Q точно — ядро NS-оценок энстрофии. Element-сторона. _(interpolation, enstrophy, sobolev)_

**Uniqueness - score 1 (exposition).** E-Ω-P интерполяция над Q (Ω²≤EP, Young, иерархия норм).
> _Caveat:_ Интерполяция стандартна; ценность — Q-точность.

---

## #619 - `src/navier_stokes/EnergyEstimate.v` - score 1 (exposition)

**Energy estimate over Q: monotone decay**

- **Topic.** Time series energy (decreasing, bounded by initial, monotone), enstrophy, integrated enstrophy, 2D full regularity, dissipation rate, exponential decay.
- **Role.** NS (energy estimate). Self-contained.
- **Counts.** Qed 25 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ энергия во времени; диссипация. _Roles:_ энергетическая оценка как роль. _Rules:_ energy_decreasing; dissipation_rate; energy_exponential_decay. _P4:_ энергия убывает, ограничена начальной над Q (Element).
- **Classical counterpart.** The basic NS energy estimate (energy decreasing, bounded by initial, dissipation rate, exponential decay) is classical; NEW: nothing — exact Q energy/enstrophy estimates with telescoping.
- **Tags.** navier-stokes, energy-estimate, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `energy_decreasing energy_bounded_by_initial enstrophy_decreasing_2d full_regularity_2d dissipation_rate energy_exponential_decay_rate energy_estimate_main` | Definition/Lemma | убывание энергии, диссипация, 2D-регулярность |

**Key lemmas (deep):**

- **`energy_bounded_by_initial`** - Энергия NS убывает и ограничена начальной (телескоп диссипации) над Q; 2D полностью регулярна. Element-сторона базовой оценки энергии. _(energy-estimate, dissipation, 2D)_

**Uniqueness - score 1 (exposition).** Энергетическая оценка над Q (энергия убывает/ограничена начальной, диссипация, 2D-регулярность).
> _Caveat:_ Базовая оценка энергии классична; ценность — Q-точность.

---

## #620 - `src/navier_stokes/EnstrophyConvergence.v` - score 1 (exposition)

**Enstrophy convergence over Q**

- **Topic.** Enstrophy tail bound, partial enstrophy (monotone), bootstrap improving decay, thermalization time, self-consistent bound, convergence.
- **Role.** NS (enstrophy convergence). Self-contained.
- **Counts.** Qed 26 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ энстрофия; хвостовые оценки. _Roles:_ сходимость энстрофии как роль. _Rules:_ enstrophy_tail_bound; bootstrap_improves_decay. _P4:_ энстрофия сходится как процесс над Q (Element).
- **Classical counterpart.** Enstrophy tail bounds, Cauchy diagnostics, thermalization-time and bootstrap decay are standard NS estimates; NEW: nothing — exact Q enstrophy convergence.
- **Tags.** navier-stokes, enstrophy, convergence, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `enstrophy_tail_bound partial_enstrophy_monotone bootstrap_improves_decay thermalization_time self_consistent_bound enstrophy_convergence_main` | Definition/Lemma | хвост энстрофии, bootstrap, сходимость |

**Key lemmas (deep):**

- **`bootstrap_improves_decay`** - Bootstrap улучшает затухание энстрофии (хвостовая оценка убывает) над Q; термализация конечна. Element-сторона сходимости энстрофии NS. _(enstrophy, bootstrap, convergence)_

**Uniqueness - score 1 (exposition).** Сходимость энстрофии над Q (хвостовые оценки, bootstrap-затухание, термализация).
> _Caveat:_ Стандартные оценки; ценность — Q-точность.

---

## #621 - `src/navier_stokes/EnstrophyProduction.v` - score 2 (new-framing)

**Enstrophy production over Q: the quadratic wall**

- **Topic.** Stretching interpolation, the effective quadratic constant, the enstrophy ODE rhs, blowup time, the quadratic wall, small-energy regularity.
- **Role.** NS (enstrophy production). Self-contained.
- **Counts.** Qed 17 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ производство энстрофии; квадратичная стена. _Roles:_ ODE энстрофии как роль. _Rules:_ the_quadratic_wall; small_energy_regularity. _P4:_ ODE энстрофии точна над Q; квадратичная стена (Element).
- **Classical counterpart.** The enstrophy ODE (stretching interpolation, the quadratic wall, blowup time, small-energy regularity) is standard NS; NEW: nothing — exact Q enstrophy production ODE.
- **Tags.** navier-stokes, enstrophy, quadratic-wall, new-framing

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `stretching_interpolation effective_quadratic_constant enstrophy_ode_rhs ode_blowup_time the_quadratic_wall small_energy_regularity enstrophy_production_main` | Definition/Lemma | растяжение, квадратичная стена, малая энергия |

**Key lemmas (deep):**

- **`the_quadratic_wall`** - ODE энстрофии имеет КВАДРАТИЧНУЮ стену (производство ~ Ω²) над Q; малая энергия даёт регулярность. Element-сторона: структурное препятствие 3D-регулярности. _(enstrophy, quadratic-wall, ODE)_

**Uniqueness - score 2 (new-framing).** Производство энстрофии над Q: квадратичная стена (Ω²) ODE, малоэнергетическая регулярность.
> _Caveat:_ Энстрофия-ODE стандартна; ново — явное обрамление 'стены' (структурное препятствие).

---

## #622 - `src/navier_stokes/FatouRegularity.v` - score 2 (methods)

**Fatou regularity over Q: a.e. regular (blowup measure zero)**

- **Topic.** Integrated enstrophy bound (uniform, all time), time-average enstrophy bounded, Markov fraction vanishing, blowup measure zero, a.e. regularity, stronger than Leray.
- **Role.** NS (a.e./partial regularity). Self-contained.
- **Counts.** Qed 23 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ интегрированная энстрофия; мера blowup. _Roles:_ п.в.-регулярность как роль (мера 0). _Rules:_ blowup_measure_zero; ae_regularity. _P4:_ blowup имеет меру 0 (Element); регулярность почти всюду.
- **Classical counterpart.** Almost-everywhere (Fatou/Markov) partial regularity — blowup set of measure zero — is classical (Caffarelli-Kohn-Nirenberg flavour); NEW: nothing — exact Q a.e.-regularity via Markov.
- **Tags.** navier-stokes, fatou, ae-regularity, methods

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `integrated_enstrophy_bound time_average_enstrophy markov_fraction fraction_vanishes blowup_measure_zero ae_regularity stronger_than_leray fatou_regularity_main` | Definition/Lemma | п.в.-регулярность, мера blowup 0 |

**Key lemmas (deep):**

- **`blowup_measure_zero`** - Множество blowup имеет меру 0 (через Марков + ограниченную интегрированную энстрофию) над Q ⟹ регулярность почти всюду, сильнее Лере. Element-сторона частичной регулярности (CKN-аромат). _(fatou, ae-regularity, measure-zero)_

**Uniqueness - score 2 (methods).** П.в.-регулярность над Q (blowup имеет меру 0 через Марков, сильнее Лере).
> _Caveat:_ Частичная регулярность (CKN) классична; вклад — конструктивная Q-форма через Марков, не полная регулярность.

---

## #623 - `src/navier_stokes/FiniteDifference.v` - score 1 (exposition)

**Finite differences over Q (NS machinery)**

- **Topic.** The difference operator fd (linear), the second difference dd, gradient norm, Abel summation, periodicity, Poincare constant, mode eigenvalue bounds.
- **Role.** NS infrastructure (finite differences). Self-contained.
- **Counts.** Qed 41 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ конечные разности fd/dd; периодическая сетка. _Roles:_ разностный оператор как роль (машина NS). _Rules:_ fd_linear; abel_summation; poincare_const. _P4:_ конечные разности точны над Q (Element); машина для Galerkin/NS.
- **Classical counterpart.** Finite differences (linearity, product rule, Abel summation, Poincare, mode eigenvalues) on a periodic grid are standard numerical analysis; NEW: nothing — the Q finite-difference machinery underlying the Galerkin/NS files.
- **Tags.** navier-stokes, finite-difference, infrastructure, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `fd fd_linear dd discrete_product_rule abel_summation is_periodic poincare_const mode_eigenvalue_bound finite_difference_main` | Definition/Lemma | разности, Абель, Пуанкаре, моды |

**Key lemmas (deep):**

- **`abel_summation`** - Суммирование по Абелю (дискретное интегрирование по частям) над Q точно — несущая лемма для оценок энергии/энстрофии NS. Element-сторона: разностная машина. _(finite-difference, abel-summation, poincare)_

**Uniqueness - score 1 (exposition).** Машина конечных разностей над Q (Абель, Пуанкаре, моды) — фундамент Galerkin/NS.
> _Caveat:_ Конечные разности стандартны; ценность инфраструктурная.

---

## #624 - `src/navier_stokes/FrequencySplit.v` - score 1 (exposition)

**Frequency split over Q: low/high enstrophy**

- **Topic.** Low/high enstrophy split, low-mode energy uniform/finite, high-mode viscous rate, critical frequency, high modes controlled, small-energy condition.
- **Role.** NS (frequency split). Self-contained.
- **Counts.** Qed 20 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ низкие/высокие моды энстрофии. _Roles:_ частотное разбиение как роль. _Rules:_ low_mode_uniform; high_modes_controlled. _P4:_ частотное разбиение точно над Q (Element).
- **Classical counterpart.** Splitting enstrophy into low/high modes (low uniform, high viscously controlled) is standard NS analysis; NEW: nothing — exact Q frequency split.
- **Tags.** navier-stokes, frequency-split, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `enstrophy_low/high enstrophy_split low_mode_uniform high_mode_rate_viscosity critical_frequency high_modes_controlled frequency_split_main` | Definition/Lemma | низкие/высокие моды, вязкий контроль |

**Key lemmas (deep):**

- **`high_modes_controlled`** - Высокие моды вязко контролируются, низкие равномерно ограничены над Q (частотное разбиение энстрофии). Element-сторона условной регулярности. _(frequency-split, viscous, modes)_

**Uniqueness - score 1 (exposition).** Частотное разбиение энстрофии над Q (низкие равномерны, высокие вязко контролируются).
> _Caveat:_ Стандартный приём; ценность — Q-точность.

---

## #625 - `src/navier_stokes/FullRegularity.v` - score 2 (methods)

**Full NS regularity over Q (per-mode, CONDITIONAL)**

- **Topic.** navier_stokes_regularity, per-mode bound stronger than energy, the key inequality driving regularity, the millennium regularity chain, 'argument is elementary'.
- **Role.** NS (full regularity, conditional). Self-contained but rests on TriadicInteraction's coupling bound.
- **Counts.** Qed 25 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; TriadicInteraction (coupling bound)
- **E/R/R.** _Elements:_ per-mode оценки; цепь регулярности. _Roles:_ полная регулярность как роль (УСЛОВНАЯ). _Rules:_ key_inequality_drives_regularity; millennium_regularity_chain. _P4:_ полная регулярность собрана как per-mode процесс над Q — но УСЛОВНА (опирается на B_coeff_bounded).
- **Classical counterpart.** The full (conditional) NS regularity chain (per-mode bound, self-consistency, the millennium statement) is the target theorem; NEW: only the per-mode/process framing — but the result is CONDITIONAL (rests on the coupling bound).
- **Tags.** navier-stokes, full-regularity, conditional, methods
- **Notes.** Conditional on TriadicInteraction's load-bearing axiom B_coeff_bounded; NOT an unconditional Millennium solution.

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `navier_stokes_regularity key_inequality_drives_regularity per_mode_is_stronger millennium_regularity_chain millennium_statement argument_is_elementary full_regularity_main` | Definition/Lemma | per-mode регулярность, millennium-цепь |

**Key lemmas (deep):**

- **`millennium_regularity_chain`** - Полная NS-регулярность собрана как per-mode цепь над Q (key inequality ведёт регулярность). КРИТИЧНО: результат УСЛОВНЫЙ — опирается на B_coeff_bounded (TriadicInteraction, load-bearing axiom). НЕ безусловное решение Millennium. _(full-regularity, per-mode, conditional)_

**Uniqueness - score 2 (methods).** Полная NS-регулярность над Q как per-mode цепь (key inequality) — УСЛОВНАЯ (на B_coeff_bounded).
> _Caveat:_ ★ УСЛОВНЫЙ результат: опирается на load-bearing axiom B_coeff_bounded (TriadicInteraction). НЕ безусловное решение Millennium NS.

---

## #626 - `src/navier_stokes/GalerkinConvergence.v` - score 1 (exposition)

**Galerkin convergence over Q**

- **Topic.** Weak residual, the bilinear/nonlinear estimate, the limit solving NS, strong H1 convergence, the limit energy/enstrophy/Sobolev bounded, convergence rate.
- **Role.** NS (Galerkin convergence). Self-contained.
- **Counts.** Qed 35 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ галёркинская аппроксимация; слабое решение. _Roles:_ сходимость к слабому решению как роль. _Rules:_ limit_solves_ns; strong_h1_convergence. _P4:_ галёркинский предел решает NS над Q (Element).
- **Classical counterpart.** Galerkin approximation converging to a weak NS solution (bilinear estimate, limit solves NS, energy/enstrophy bounded) is standard; NEW: nothing — exact Q Galerkin convergence.
- **Tags.** navier-stokes, galerkin, convergence, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `weak_residual bilinear_estimate limit_solves_ns strong_h1_convergence limit_energy/enstrophy_bounded convergence_rate galerkin_convergence_main` | Definition/Lemma | галёркинская сходимость, предел решает NS |

**Key lemmas (deep):**

- **`limit_solves_ns`** - Галёркинский предел решает NS (билинейная оценка, сильная H1-сходимость) над Q; энергия/энстрофия предела ограничены. Element-сторона конструкции слабого решения. _(galerkin, convergence, weak-solution)_

**Uniqueness - score 1 (exposition).** Галёркинская сходимость над Q (предел решает NS, H1-сходимость, ограниченные нормы).
> _Caveat:_ Галёркин классичен; ценность — Q-формализация.

---

## #627 - `src/navier_stokes/GalerkinSystem.v` - score 2 (methods)

**Galerkin system over Q: modal ODE (1 Parameter; B_antisym axiom eliminated 06.2026)**

- **Topic.** Modal state/coefficient, modal energy/enstrophy, viscous decay, the nonlinear energy rate zero (via antisymmetry), energy rate = dissipation, Galerkin smooth/global — with B_antisym a Lemma (antisymmetrization, June 2026) and B_raw a parameter.
- **Role.** NS (Galerkin ODE system). 0 axioms + 1 Parameter (B_raw) since June 2026: B_coeff := antisymmetrization of B_raw, B_antisym is a Lemma (ring). Self-contained otherwise.
- **Counts.** Qed 30 / Admitted 0 / axioms 1
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ модальное состояние; коэффициент mode. _Roles:_ галёркинская ODE как роль; антисимметрия B. _Rules:_ nonlinear_energy_zero (через B_antisym); energy_rate_equals_dissipation. _P4:_ ★ нелинейный член сохраняет энергию через антисимметрию ПО ПОСТРОЕНИЮ (June 2026: B_coeff = антисимметризация Parameter B_raw, B_antisym = Lemma); 1 допущение (Parameter B_raw).
- **Classical counterpart.** The Galerkin ODE system for the modal coefficients (energy rate = dissipation, the advection antisymmetry conserving energy) is standard NS; the antisymmetry B(k,l,m)=-B(k,m,l) WAS an axiom until June 2026; now B_coeff := B_raw k l m - B_raw k m l (antisymmetrization of an abstract raw Parameter), so antisymmetry is a Lemma by ring — the file carries 1 assumption (Parameter B_raw).
- **Tags.** navier-stokes, galerkin, axiom, methods
- **Notes.** June 2026: axiom B_antisym ELIMINATED — B_coeff is now the antisymmetrization of Parameter B_raw, antisymmetry a Lemma (ring). Print Assumptions of NS millennium capstones: C_B_positive + Parameter C_B only. Remaining assumption here: Parameter B_raw. axioms=1.

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `modal_state mode_coeff modal_energy/enstrophy viscous_energy_decay nonlinear_energy_zero energy_rate_equals_dissipation galerkin_smooth/global critical_enstrophy galerkin_main` | Definition/Lemma | галёркинская ODE, антисимметрия, диссипация |

**Key lemmas (deep):**

- **`energy_rate_equals_dissipation`** - Галёркинская энергия убывает со скоростью диссипации: нелинейный член НЕ производит энергию (nonlinear_energy_zero через антисимметрию B). June 2026: антисимметрия более НЕ постулат — B_coeff определён как антисимметризация Parameter B_raw, B_antisym = Lemma (ring); грид-спуск содержания: AdvectionEnergyConservation. _(galerkin, energy-conservation, antisymmetry, axiom)_

**Uniqueness - score 2 (methods).** Галёркинская ODE над Q (энергия=диссипация, нелинейный член сохраняет энергию через антисимметрию B).
> _Caveat:_ ★ Несёт 1 допущение: Parameter B_raw (сырое сопряжение). Axiom B_antisym УСТРАНЁН 2026-06-10 (Lemma по построению — антисимметризация). axioms=1.

---

## #628 - `src/navier_stokes/GridFunction.v` - score 1 (exposition)

**Grid functions over Q (discrete L2 for NS)**

- **Topic.** sum_ns machinery, grid functions (add/scale/mul, vector-space laws), the inner product/norm, Cauchy-Schwarz, the telescope.
- **Role.** NS infrastructure (grid-function L2). Self-contained.
- **Counts.** Qed 43 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ grid-функции; дискретное L2. _Roles:_ grid-L2 как роль (машина NS). _Rules:_ gf_inner; cauchy_schwarz_sq; sum_ns_telescope. _P4:_ дискретное L2 точно над Q (Element); машина NS.
- **Classical counterpart.** Grid functions over Q with inner product, norm, Cauchy-Schwarz (the discrete L2 space) are standard; NEW: nothing — the Q grid-function L2 scaffolding for NS.
- **Tags.** navier-stokes, grid-function, L2, infrastructure, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `grid_fn gf_add/scale/mul gf_inner gf_norm_sq cauchy_schwarz_sq sum_ns_telescope grid_function_main` | Definition/Lemma | grid-L2, скалярное произведение, CS |

**Key lemmas (deep):**

- **`cauchy_schwarz_sq`** - Дискретное L2 grid-функций с Коши-Шварцем над Q — фундамент всех NS-оценок (энергия/энстрофия). Element-сторона: discrete L2. _(grid-function, L2, cauchy-schwarz)_

**Uniqueness - score 1 (exposition).** Grid-функции (дискретное L2) над Q (скалярное произведение, CS, телескоп) — фундамент NS.
> _Caveat:_ Дискретное L2 стандартно; ценность инфраструктурная.

---

## #629 - `src/navier_stokes/GronwallAnalysis.v` - score 1 (exposition)

**Gronwall analysis over Q**

- **Topic.** Growth factor, iterated growth (monotone), linear Gronwall bound, discrete Gronwall, blowup step, the exponent gap, log correction, corrected rate strictly better.
- **Role.** NS (discrete Gronwall). Self-contained.
- **Counts.** Qed 20 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ факторы роста; Гронуолл. _Roles:_ дискретный Гронуолл как роль. _Rules:_ discrete_gronwall; log_correction; the_exponent_gap. _P4:_ дискретный Гронуолл точен над Q (Element).
- **Classical counterpart.** Discrete Gronwall (growth factors, iterated growth, blowup step, log-correction) is standard; NEW: nothing — exact Q discrete Gronwall with a log-corrected rate.
- **Tags.** navier-stokes, gronwall, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `growth_factor iterated_growth linear_gronwall_bound discrete_gronwall blowup_step the_exponent_gap log_correction corrected_strictly_better gronwall_main` | Definition/Lemma | Гронуолл, log-коррекция, exponent gap |

**Key lemmas (deep):**

- **`the_exponent_gap`** - Дискретный Гронуолл с log-коррекцией над Q; назван the_exponent_gap (структурное препятствие). Element-сторона NS-оценок роста. _(gronwall, exponent-gap, log-correction)_

**Uniqueness - score 1 (exposition).** Дискретный Гронуолл над Q (log-коррекция, exponent gap).
> _Caveat:_ Гронуолл классичен; ценность — Q-точность + honest gap.

---

## #630 - `src/navier_stokes/HonestAssessment.v` - score 3 (synthesis+observation)

**Honest assessment over Q: the NS wall is structural (the alpha gap)**

- **Topic.** Three faces of the wall (alpha sharp, per-mode threshold, RDT failure), Young/CS/interpolation preserve the degree, Gronwall alpha 1 vs 2, the_alpha_gap, condition is sharp, solved vs not-solved, wall_is_structural.
- **Role.** NS (honest meta-assessment). Self-contained.
- **Counts.** Qed 26 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ три грани стены; alpha-gap. _Roles:_ оценка как честная роль (стена структурна). _Rules:_ the_alpha_gap; condition_is_sharp; wall_is_structural. _P4:_ ★ NS-стена СТРУКТУРНА (the_alpha_gap, alpha=2 sharp); честно: что решено (2D/условно) vs не решено (3D безусловно).
- **Classical counterpart.** An honest assessment of the NS regularity 'wall' (the alpha-gap, three faces, what is/isn't solved) is meta-commentary; NEW is only the explicit honest ledger: the wall is STRUCTURAL, alpha=2 sharp, the alpha gap named, conditional vs unconditional.
- **Tags.** navier-stokes, wall, alpha-gap, honest, synthesis

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `wall_face_1_alpha alpha_two_sharp the_alpha_gap condition_is_sharp solved_results not_solved p4_contribution wall_is_structural honest_assessment_main` | Definition/Lemma | ★ три грани стены, alpha-gap, структурность |

**Key lemmas (deep):**

- **`wall_is_structural`** - ★ NS-стена СТРУКТУРНА: alpha=2 (квадратичная стена) sharp, the_alpha_gap назван точно, three faces одной стены. Честный реестр: что доказано (безусловное 2D/энергия, условное 3D) vs что НЕ решено (безусловное 3D). Образец честности проекта. _(navier-stokes, wall, alpha-gap, honest)_

**Uniqueness - score 3 (synthesis+observation).** Честная оценка NS-стены над Q: стена СТРУКТУРНА (alpha=2 sharp, the_alpha_gap), три грани, явно solved (2D/условно) vs not-solved (3D безусловно).
> _Caveat:_ НЕ решение Millennium NS; ценность — машинно-точная честная самооценка структурной стены + P4-вклад.

---

## #631 - `src/navier_stokes/InvariantRegion.v` - score 1 (exposition)

**Invariant region over Q**

- **Topic.** The invariant amplitude A_inv, the region (convex, contains zero), boundary damping/flow nonpositive, region invariant under the Euler step, region implies per-mode/energy bounds.
- **Role.** NS (invariant region). Self-contained.
- **Counts.** Qed 28 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ инвариантная область; граничный поток. _Roles:_ инвариантная область как роль (условная регулярность). _Rules:_ boundary_flow_nonpositive; region_invariant. _P4:_ область инвариантна под Эйлер-шагом над Q (Element).
- **Classical counterpart.** Constructing an invariant region (boundary flow nonpositive, region invariant under the Euler step) for conditional regularity is standard dynamical-systems analysis; NEW: nothing — exact Q invariant region.
- **Tags.** navier-stokes, invariant-region, regularity, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `A_inv in_region region_convex boundary_flow_nonpositive region_invariant euler_step invariance_by_induction region_implies_energy_bound invariant_region_main` | Definition/Lemma | инвариантная область, граничный поток, индукция |

**Key lemmas (deep):**

- **`region_invariant`** - Область инвариантна под дискретным Эйлер-шагом (граничный поток неположителен) над Q ⟹ per-mode/энергия ограничены. Element-сторона условной регулярности NS (динамическая система). _(invariant-region, boundary-flow, regularity)_

**Uniqueness - score 1 (exposition).** Инвариантная область над Q (граничный поток ≤0, инвариантна под Эйлером ⟹ ограниченность).
> _Caveat:_ Инвариантные области стандартны; условная регулярность.

---

## #632 - `src/navier_stokes/LowModeControl.v` - score 1 (exposition)

**Low mode control over Q**

- **Topic.** The energy ball (invariant, bounded), the finite ODE (energy preserved, global, smooth, no blowup), low/high mode complete, no finite-time singularity, low modes analytic.
- **Role.** NS (low-mode control). Self-contained.
- **Counts.** Qed 32 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ энергетический шар; низкие моды. _Roles:_ контроль низких мод как роль. _Rules:_ finite_ode_no_blowup; no_finite_time_singularity. _P4:_ низкие моды контролируются, конечная ODE без blowup над Q (Element).
- **Classical counterpart.** Controlling low modes (energy ball invariant, finite ODE global/smooth, no finite-time singularity) is standard; NEW: nothing — exact Q low-mode control.
- **Tags.** navier-stokes, low-mode, regularity, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `in_energy_ball energy_ball_invariant finite_ode_global/smooth/no_blowup low_modes_energy_bounded no_finite_time_singularity low_modes_analytic low_mode_control_main` | Definition/Lemma | энергетический шар, конечная ODE без blowup |

**Key lemmas (deep):**

- **`no_finite_time_singularity`** - Низкие моды контролируются (энергетический шар инвариантен), конечная ODE глобальна без blowup над Q. Element-сторона: низко-модовая часть NS регулярна. _(low-mode, energy-ball, no-blowup)_

**Uniqueness - score 1 (exposition).** Контроль низких мод над Q (энергетический шар инвариантен, конечная ODE без blowup).
> _Caveat:_ Стандартно; ценность — Q-точность.

---

## #633 - `src/navier_stokes/MillenniumComplete.v` - score 2 (synthesis+observation)

**Millennium complete over Q (NS+YM chain, CONDITIONAL, with axiom list)**

- **Topic.** The phase/layer chain, ns_galerkin_bound_chain, the key inequality / integer minimum, A=exists, regularity unconditional? (with an explicit axiom_list and file_count), the thirty-file chain.
- **Role.** NS (Millennium assembly, conditional). Lists its own axioms. Self-contained.
- **Counts.** Qed 34 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; NS chain
- **E/R/R.** _Elements:_ фазовая/слойная цепь NS+YM. _Roles:_ Millennium-сборка как роль (УСЛОВНАЯ). _Rules:_ ns_galerkin_bound_chain; axiom_list; key_inequality. _P4:_ ★ Millennium-цепь собрана над Q с ЯВНЫМ axiom_list — NS-регулярность УСЛОВНА (зависит от B_coeff_bounded).
- **Classical counterpart.** A complete NS+YM Millennium proof chain (phases, layers, key inequality, A=exists) is the target; NEW: only the assembled chain + the explicit axiom_list/file_count — but NS regularity is CONDITIONAL (the axiom list includes the load-bearing bound).
- **Tags.** navier-stokes, millennium, conditional, honest, synthesis

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `chain_phase1..6 ns_galerkin_bound_chain key_inequality key_integer_minimum a_equals_exists axiom_list file_count thirty_file_chain millennium_reading2_capstone` | Definition/Lemma | Millennium-цепь, явный axiom_list |

**Key lemmas (deep):**

- **`ns_galerkin_bound_chain`** - NS+YM Millennium-цепь собрана над Q (фазы/слои, key inequality, A=exists) с ЯВНЫМ axiom_list и file_count. КРИТИЧНО: NS-регулярность УСЛОВНА — axiom_list честно включает load-bearing допущения (B_coeff_bounded). НЕ безусловное решение. _(millennium, conditional, axiom-list, honest)_

**Uniqueness - score 2 (synthesis+observation).** Millennium NS+YM цепь над Q с ЯВНЫМ axiom_list/file_count — собрана, но УСЛОВНА (NS зависит от B_coeff_bounded).
> _Caveat:_ ★ НЕ безусловное решение Millennium; честно перечисляет свои аксиомы. NS-регулярность conditional на load-bearing bound.

---

## #634 - `src/navier_stokes/NSComplete.v` - score 3 (synthesis+observation)

**NS complete over Q: unconditional vs conditional ledger**

- **Topic.** Unconditional results (energy, 2D, integrated, Fatou, Galerkin, resolution), conditional results (invariant, bootstrap, Sobolev, Galerkin, smooth), the_wall, closing the gap, ns_axiom_count.
- **Role.** NS (results ledger). Self-contained. June 2026 wave-4 sweep: vacuous computability-shams (exists q, _ == q) replaced by the by-type finite-ratio form or real identities; see UNIQUENESS.md.
- **Counts.** Qed 22 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; NS files
- **E/R/R.** _Elements:_ безусловные/условные NS-результаты. _Roles:_ реестр результатов как честная роль. _Rules:_ ns_unconditional; ns_conditional; the_wall; ns_axiom_count. _P4:_ ★ безусловные (u1-u6) отделены от условных (c1-c5) и the_wall; ns_axiom_count явно — честный реестр.
- **Classical counterpart.** Stating the NS results (unconditional u1-u6, conditional c1-c5, the wall, publication framing) is meta; NEW is only the explicit unconditional/conditional ledger + ns_axiom_count.
- **Tags.** navier-stokes, ledger, wall, honest, synthesis

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `ns_u1..u6 ns_unconditional ns_c1..c5 ns_conditional the_wall closing_the_gap ns_axiom_count ns_synthesis_main` | Definition/Lemma | ★ безусловное vs условное vs стена, счёт аксиом June 2026 wave-4 sweep: vacuous computability-shams (exists q, _ == q) replaced by the by-type finite-ratio form or real identities; see UNIQUENESS.md. |

**Key lemmas (deep):**

- **`ns_conditional`** - ★ Честный реестр NS: безусловные результаты (энергия, 2D, Fatou, Galerkin) ОТДЕЛЕНЫ от условных (c1-c5) и the_wall; ns_axiom_count явно перечислен. Образец честности: что доказано безусловно vs где стена/аксиомы. _(navier-stokes, unconditional-conditional, wall, honest)_

**Uniqueness - score 3 (synthesis+observation).** NS-реестр над Q: безусловные (u1-u6) vs условные (c1-c5) vs the_wall, с явным ns_axiom_count — честное разделение.
> _Caveat:_ НЕ решение Millennium; ценность — машинно-точный честный реестр доказанного/условного/аксиом.

---

## #635 - `src/navier_stokes/NSProcessFinal.v` - score 2 (new-framing)

**NS process final over Q: the P4 view**

- **Topic.** NS energy bounded/monotone as a process, 2D regular, 3D conditional, the quadratic bound, finite-K linear, attacks fail, finite-K well-behaved, K-limit difficulty, p4_process_is_physics.
- **Role.** NS (P4 process view). Self-contained. June 2026 wave-4 sweep: vacuous computability-shams (exists q, _ == q) replaced by the by-type finite-ratio form or real identities; see UNIQUENESS.md.
- **Counts.** Qed 22 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ NS-результаты как процесс. _Roles:_ P4-взгляд на NS как роль. _Rules:_ ns_process_energy; finite_K_wellbehaved; k_limit_difficulty. _P4:_ ★ NS как процесс: конечный-K хорошо ведёт себя (Element), K→∞ предел = трудность (role-limit); p4_process_is_physics.
- **Classical counterpart.** Viewing the NS results through the P4 process lens (energy bounded, 2D regular, 3D conditional, finite-K well-behaved) is the project's framing; NEW: only the P4 process reading.
- **Tags.** navier-stokes, P4, process, new-framing

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `ns_energy_bounded ns_process_energy ns_2d_process ns_3d_process_smooth finite_K_wellbehaved k_limit_difficulty p4_process_is_physics navier_stokes_complete` | Definition/Lemma | NS как процесс, конечный-K vs K-предел |

**Key lemmas (deep):**

- **`k_limit_difficulty`** - NS как P4-процесс: при КОНЕЧНОМ K всё хорошо ведёт себя (Element), трудность — в пределе K→∞ (role-limit). p4_process_is_physics: конечно-актуальная физика регулярна, континуум-предел = стена. Честная P4-локализация. _(navier-stokes, P4, finite-K, K-limit)_

**Uniqueness - score 2 (new-framing).** NS через P4-процесс: конечный-K хорошо ведёт себя (Element), K→∞ = role-limit-трудность; p4_process_is_physics.
> _Caveat:_ P4-переобрамление NS; не решение. Локализует трудность в континуум-пределе.

---

## #636 - `src/navier_stokes/PerModeBound.v` - score 1 (exposition)

**Per-mode bound over Q**

- **Topic.** Per-mode amplitude (positive, decreasing), enstrophy contribution, harmonic sums/bounds, convolution bound, self-consistent amplitude, bootstrap closing, iterated bound.
- **Role.** NS (per-mode bound). Self-contained.
- **Counts.** Qed 28 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ per-mode амплитуды; гармонические суммы. _Roles:_ per-mode оценка как роль. _Rules:_ bootstrap_closes; self_consistent_amplitude. _P4:_ per-mode оценки точны над Q (Element).
- **Classical counterpart.** Per-mode amplitude bounds (harmonic sums, convolution bound, bootstrap closing, self-consistent amplitude) are standard NS estimates; NEW: nothing — exact Q per-mode bounds.
- **Tags.** navier-stokes, per-mode, bootstrap, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `per_mode_amplitude enstrophy_contribution harmonic_sum/bound convolution_bound self_consistent_amplitude bootstrap_closes iterated_bound_crude per_mode_main` | Definition/Lemma | per-mode амплитуда, bootstrap, свёртка |

**Key lemmas (deep):**

- **`bootstrap_closes`** - Per-mode bootstrap ЗАМЫКАЕТСЯ (самосогласованная амплитуда) над Q — ключевой шаг условной регулярности NS. Element-сторона. _(per-mode, bootstrap, self-consistent)_

**Uniqueness - score 1 (exposition).** Per-mode оценки над Q (гармонические суммы, свёртка, bootstrap замыкается).
> _Caveat:_ Стандартные оценки; условная регулярность.

---

## #637 - `src/navier_stokes/ProcessNS.v` - score 1 (new-framing)

**Process NS over Q: the Galerkin process**

- **Topic.** The Galerkin process, energy bounded/monotone at each stage, smooth per stage, 2D regular, 3D conditional, well-formed energy/dissipation.
- **Role.** NS (process view). Self-contained.
- **Counts.** Qed 21 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ галёркинский процесс {a_K}. _Roles:_ NS как процесс {a_K}. _Rules:_ process_smooth_per_stage; regularity_2d_full. _P4:_ NS как галёркинский процесс: каждая стадия гладкая/ограниченная (Element).
- **Classical counterpart.** The Galerkin process {a_K} with bounded energy/enstrophy, 2D regular, 3D conditional, as a P4 process is the project framing; NEW: only the process reading.
- **Tags.** navier-stokes, process, galerkin, new-framing

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `galerkin_process process_energy_bounded process_smooth_per_stage regularity_2d_full process_conditionally_regular process_wellformed process_navier_stokes` | Definition/Lemma | галёркинский процесс, 2D-регулярность, условное 3D |

**Key lemmas (deep):**

- **`process_smooth_per_stage`** - NS как галёркинский процесс {a_K}: каждая стадия гладкая, энергия ограничена, 2D регулярна над Q. P4: NS-решение как процесс приближений (Element-стадии); 3D условно. _(process-NS, galerkin, P4)_

**Uniqueness - score 1 (new-framing).** NS как галёркинский процесс над Q (стадии гладкие/ограниченные, 2D регулярно, 3D условно).
> _Caveat:_ P4-обрамление; не решение. 3D условно.

---

## #638 - `src/navier_stokes/ProcessVorticity.v` - score 1 (new-framing)

**Process vorticity over Q**

- **Topic.** Process vorticity norm/palinstrophy, the norm hierarchy, process BKM sum (bounded, 2D), the exponent gap, p4_vorticity_resolution.
- **Role.** NS (process vorticity). Self-contained.
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ процессная завихренность/палинстрофия. _Roles:_ завихренность как процесс. _Rules:_ process_bkm_bounded; exponent_gap_summary. _P4:_ завихренность как процесс над Q (Element); 2D BKM ограничен.
- **Classical counterpart.** Process vorticity/palinstrophy with a BKM sum and the exponent gap is the project framing; NEW: only the process reading.
- **Tags.** navier-stokes, process-vorticity, new-framing

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `process_vorticity_norm process_palinstrophy process_norm_hierarchy process_bkm_sum/bounded/2d exponent_gap_summary p4_vorticity_resolution` | Definition/Lemma | процессная завихренность, BKM, exponent gap |

**Key lemmas (deep):**

- **`p4_vorticity_resolution`** - Завихренность как процесс: 2D BKM-сумма ограничена над Q; exponent_gap назван. P4-разрешение завихренности (Element-стадии); 3D = gap. Честно. _(process-vorticity, BKM, exponent-gap)_

**Uniqueness - score 1 (new-framing).** Процессная завихренность над Q (2D BKM ограничен, exponent gap).
> _Caveat:_ P4-обрамление; 3D gap.

---

## #639 - `src/navier_stokes/RegularitySynthesis.v` - score 1 (exposition)

**Regularity synthesis over Q**

- **Topic.** The per-mode chain (energy, forcing, self-consistent, iterated, enstrophy, monotone), balance point, cascade damping, BKM at level, Gronwall applies.
- **Role.** NS (regularity synthesis). Self-contained.
- **Counts.** Qed 19 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ per-mode цепь регулярности. _Roles:_ синтез регулярности как роль. _Rules:_ cascade_damping; balance_point; per_mode_chain. _P4:_ per-mode цепь регулярности собрана над Q (Element).
- **Classical counterpart.** Assembling the per-mode regularity chain (balance point, cascade damping, Gronwall) is the standard regularity synthesis; NEW: nothing — the assembled per-mode chain.
- **Tags.** navier-stokes, regularity, synthesis, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `chain_step1..7 per_mode_chain balance_point cascade_damping bkm_at_level gronwall_applies ns_final_assessment` | Definition/Lemma | per-mode цепь, баланс, каскад-затухание |

**Key lemmas (deep):**

- **`cascade_damping`** - Каскадное затухание (высокие моды демпфированы) + точка баланса собирают per-mode цепь регулярности над Q. Element-сторона условной регулярности NS. _(regularity, cascade, per-mode)_

**Uniqueness - score 1 (exposition).** Синтез регулярности над Q (per-mode цепь, каскад-затухание, баланс).
> _Caveat:_ Стандартная сборка; условная регулярность.

---

## #640 - `src/navier_stokes/ResolutionRegularity.v` - score 2 (new-framing)

**Resolution regularity over Q: exact rational DNS**

- **Topic.** Euler step/evolve (rational solution), refinement energy monotone, resolution convergence, the physicist's criterion, p4 global existence/smoothness, DNS validation.
- **Role.** NS (resolution/DNS). Self-contained. June 2026 wave-4 sweep: vacuous computability-shams (exists q, _ == q) replaced by the by-type finite-ratio form or real identities; see UNIQUENESS.md.
- **Counts.** Qed 22 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ Эйлер-эволюция; разрешение DNS. _Roles:_ разрешение как процесс (точное рациональное решение). _Rules:_ solution_is_rational; resolution_convergence; p4_exact_solution. _P4:_ ★ на каждом разрешении решение ТОЧНО РАЦИОНАЛЬНО (Element); уточнение сходится — DNS как P4-процесс.
- **Classical counterpart.** Resolution-by-Euler-method with rational arithmetic (physicist's DNS criterion, refinement convergence) is standard numerics; NEW: only the constructive 'exact rational solution at each resolution' framing.
- **Tags.** navier-stokes, resolution, DNS, P4, new-framing

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `euler_step/evolve solution_is_rational refinement_energy resolution_convergence p4_global_existence/smoothness p4_exact_solution dns_validation resolution_regularity_main` | Definition/Lemma | Эйлер-эволюция, точное рациональное решение, DNS June 2026 wave-4 sweep: vacuous computability-shams (exists q, _ == q) replaced by the by-type finite-ratio form or real identities; see UNIQUENESS.md. |

**Key lemmas (deep):**

- **`p4_exact_solution`** - На каждом разрешении NS-решение ТОЧНО РАЦИОНАЛЬНО (Эйлер над Q), уточнение сходится (DNS как процесс). P4: конечно-разрешённая физика точна (Element); континуум-предел отдельно. Конструктивный DNS. _(resolution, DNS, exact-rational, P4)_

**Uniqueness - score 2 (new-framing).** Разрешение/DNS над Q: на каждом разрешении решение ТОЧНО РАЦИОНАЛЬНО (Эйлер), уточнение сходится — DNS как P4-процесс.
> _Caveat:_ Эйлер/DNS стандартны; ново — точное-рациональное-решение P4-обрамление.

---

## #641 - `src/navier_stokes/SmoothInitialData.v` - score 1 (exposition)

**Smooth initial data over Q**

- **Topic.** Smooth/very-smooth initial data, finite energy/enstrophy, smooth in the region (high modes), rescaling puts in region, smooth stays smooth.
- **Role.** NS (smooth initial data). Self-contained. June 2026 wave-4 vacuity rollback: smooth_stays_smooth carried a vacuous True-conjunct standing for unproven all-time regularity -> dropped; conclusion = entry into invariant region; all-time chain honestly deferred to ResolutionRegularity/NSComplete (conditional on NS-wall axioms).
- **Counts.** Qed 19 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ гладкие начальные данные; область. _Roles:_ гладкие данные как роль (вход в область). _Rules:_ rescaling_puts_in_region; smooth_stays_smooth. _P4:_ гладкие данные конечно-энергичны, входят в область над Q (Element).
- **Classical counterpart.** Smooth (Fourier-decaying) initial data entering the invariant region (after rescaling) is standard; NEW: nothing — exact Q smooth-data conditions.
- **Tags.** navier-stokes, smooth-data, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `smooth_initial very_smooth_implies_smooth smooth_has_finite_energy/enstrophy rescaling_puts_in_region smooth_stays_smooth smooth_initial_data_main` | Definition/Lemma | гладкие данные, вход в область, рескейлинг June 2026 wave-4 vacuity rollback: smooth_stays_smooth carried a vacuous True-conjunct standing for unproven all-time regularity -> dropped; conclusion = entry into invariant region; all-time chain honestly deferred to ResolutionRegularity/NSComplete (conditional on NS-wall axioms). |

**Key lemmas (deep):**

- **`rescaling_puts_in_region`** - Гладкие начальные данные (после рескейлинга) входят в инвариантную область над Q; остаются гладкими. Element-сторона условной регулярности (вход в область). _(smooth-data, region, rescaling)_

**Uniqueness - score 1 (exposition).** Гладкие начальные данные над Q (конечная энергия, вход в область после рескейлинга).
> _Caveat:_ Стандартно; условная регулярность.

---

## #642 - `src/navier_stokes/TransientClosure.v` - score 2 (methods)

**Transient closure over Q (the conditional chain)**

- **Topic.** Steps 1-7 (smooth enters region, invariant, per-mode, bootstrap, enstrophy converges, higher regularity, smooth for all time), all Sobolev bounded, the regularity chain.
- **Role.** NS (transient closure, conditional). Self-contained. June 2026 wave-4 vacuity rollback: smooth_stays_smooth carried a vacuous True-conjunct standing for unproven all-time regularity -> dropped; conclusion = entry into invariant region; all-time chain honestly deferred to ResolutionRegularity/NSComplete (conditional on NS-wall axioms).
- **Counts.** Qed 19 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ 7-шаговая цепь регулярности. _Roles:_ замыкание переходного процесса как роль. _Rules:_ step7_smooth_for_all_time; regularity_chain. _P4:_ 7-шаговая цепь даёт гладкость на все времена над Q (УСЛОВНО).
- **Classical counterpart.** The full conditional-regularity chain (smooth enters region, invariant, per-mode, bootstrap, enstrophy converges, higher regularity, smooth for all time) is the assembled argument; NEW: only the assembled transient-closure chain.
- **Tags.** navier-stokes, transient-closure, conditional, methods

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `step1..7 regularity_chain enstrophy_bounded_in_R all_sobolev_bounded energy_controls_enstrophy transient_closure_main` | Definition/Lemma | 7-шаговая цепь, гладкость на все времена |

**Key lemmas (deep):**

- **`step7_smooth_for_all_time`** - 7-шаговая цепь (вход в область → инвариантность → per-mode → bootstrap → энстрофия сходится → высшая регулярность → гладкость) даёт гладкость на все времена над Q. УСЛОВНО (опирается на оценки/B_coeff_bounded). _(transient-closure, regularity-chain, conditional)_

**Uniqueness - score 2 (methods).** Замыкание переходного процесса над Q (7-шаговая цепь → гладкость на все времена) — УСЛОВНОЕ.
> _Caveat:_ Сборка условной регулярности; зависит от load-bearing оценок. Не безусловное решение.

---

## #643 - `src/navier_stokes/TriadicInteraction.v` - score 2 (methods)

**Triadic interaction over Q (3 assumptions incl. the LOAD-BEARING coupling bound)**

- **Topic.** Triad count/bound, coupling for sum-triad, the nonlinear term bounded, mode forcing, clean forcing bound, damping rate, steady-state bound, damping exceeds forcing — resting on B_coeff_bounded (load-bearing), C_B_positive, C_B.
- **Role.** NS (triadic coupling). CARRIES the LOAD-BEARING axiom B_coeff_bounded + C_B_positive axiom + C_B parameter (3). The conditional-regularity linchpin.
- **Counts.** Qed 36 / Admitted 0 / axioms 3
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ триады; коэффициент связи B; форсинг. _Roles:_ триадная связь как роль; коэффициентная оценка (НЕСУЩАЯ). _Rules:_ coupling_bound; damping_exceeds_forcing; steady_state_bound. _P4:_ ★ вся условная регулярность NS ПОКОИТСЯ на B_coeff_bounded (\|B\|≤C_B·max(k,l,m)) — ПОСТУЛИРОВАНО (load-bearing axiom) + C_B_positive + C_B param; 3 допущения.
- **Classical counterpart.** Triad counting, the coupling bound and the damping-exceeds-forcing steady state are standard NS spectral analysis; CRITICALLY the coupling bound \|B(k,l,m)\| <= C_B*max(k,l,m) is the LOAD-BEARING AXIOM (B_coeff_bounded) on which the whole conditional regularity rests, plus C_B_positive (harmless) and C_B (parameter) — 3 assumptions.
- **Tags.** navier-stokes, triadic, load-bearing-axiom, conditional, methods
- **Notes.** Declares B_coeff_bounded (LOAD-BEARING axiom — NS regularity is CONDITIONAL on it) + C_B_positive axiom + C_B parameter. axioms=3 per CLAUDE.md.

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `triad_count coupling_for_sum_triad nonlinear_term_bounded mode_forcing clean_forcing_bound damping_rate steady_state_bound damping_exceeds_forcing triadic_interaction_main` | Definition/Lemma | ★ триадная связь, демпфирование > форсинг (на B_coeff_bounded) |

**Key lemmas (deep):**

- **`damping_exceeds_forcing`** - ★ Демпфирование превосходит форсинг (steady state ограничен) над Q — НО это ПОКОИТСЯ на B_coeff_bounded (\|B(k,l,m)\|≤C_B·max(k,l,m)), ПОСТУЛИРОВАННОМ load-bearing axiom'е. CLAUDE.md: вся NS-регулярность УСЛОВНА на этой оценке. Самый load-bearing файл NS. _(triadic, coupling-bound, load-bearing-axiom)_

**Uniqueness - score 2 (methods).** Триадная связь над Q (демпфирование > форсинг, steady state) — но на ПОСТУЛИРОВАННОЙ load-bearing оценке B_coeff_bounded.
> _Caveat:_ ★ Несёт 3 допущения: B_coeff_bounded (LOAD-BEARING — вся NS-регулярность conditional на ней), C_B_positive (harmless), C_B (parameter). axioms=3. Это линчпин условности NS.

---

## #644 - `src/navier_stokes/TwoMillennium.v` - score 2 (synthesis+observation)

**Two Millennium over Q: YM + NS unified**

- **Topic.** The YM key (gap positive, integer minimum), the NS key (amplitude positive, induction step), both elementary, the unified framework, both number theory.
- **Role.** NS+YM (two-Millennium unification). Self-contained.
- **Counts.** Qed 20 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ два ключевых неравенства (YM gap, NS amplitude). _Roles:_ объединение двух Millennium как роль. _Rules:_ yang_mills_key; navier_stokes_key; both_number_theory. _P4:_ YM и NS сведены к двум элементарным неравенствам над Q (Element); оба УСЛОВНЫ.
- **Classical counterpart.** Unifying YM (gap) and NS (regularity) under two key inequalities (both 'number theory', both elementary) is the project's framing; NEW: only the unified two-inequality view.
- **Tags.** navier-stokes, two-millennium, unification, synthesis

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `yang_mills_key yang_mills_gap_positive navier_stokes_key both_elementary unified_framework both_number_theory two_millennium_main` | Definition/Lemma | два ключевых неравенства, объединение |

**Key lemmas (deep):**

- **`unified_framework`** - YM (gap) и NS (regularity) сведены к ДВУМ элементарным неравенствам (оба 'теория чисел') над Q. Объединяющая рамка проекта; оба результата УСЛОВНЫ (YM gap для конкретной решётки, NS на B_coeff_bounded). _(two-millennium, YM, NS, unification)_

**Uniqueness - score 2 (synthesis+observation).** YM+NS объединены под двумя элементарными неравенствами над Q ('оба теория чисел').
> _Caveat:_ Объединяющая рамка; оба результата условны/над-брендированы (YM gap, NS на B_coeff_bounded).

---

## #645 - `src/navier_stokes/UniformBounds.v` - score 1 (exposition)

**Uniform bounds over Q (Galerkin compactness)**

- **Topic.** Uniform energy/per-mode/enstrophy/palinstrophy/Sobolev bounds (independent of K), time-derivative bounds, equicontinuity, compactness, strong-convergence key.
- **Role.** NS (uniform bounds for compactness). Self-contained.
- **Counts.** Qed 37 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ равномерные оценки (energy/enstrophy/Sobolev). _Roles:_ равномерность по K как роль (компактность). _Rules:_ all_bounds_uniform; equicontinuity; compactness. _P4:_ оценки равномерны по K над Q (Element) ⟹ компактность.
- **Classical counterpart.** Uniform-in-K bounds (energy, per-mode, enstrophy, palinstrophy, Sobolev, time-derivative, equicontinuity, compactness) for Galerkin compactness are standard; NEW: nothing — exact Q uniform bounds.
- **Tags.** navier-stokes, uniform-bounds, compactness, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `uniform_energy uniform_per_mode uniform_enstrophy uniform_palinstrophy uniform_sobolev equicontinuity compactness all_bounds_uniform uniform_bounds_main` | Definition/Lemma | равномерные оценки, равностепенная непрерывность, компактность |

**Key lemmas (deep):**

- **`all_bounds_uniform`** - Все оценки (energy/enstrophy/Sobolev/time-derivative) РАВНОМЕРНЫ по K над Q ⟹ равностепенная непрерывность ⟹ компактность (для галёркинской сходимости). Element-сторона. _(uniform-bounds, compactness, equicontinuity)_

**Uniqueness - score 1 (exposition).** Равномерные по K оценки над Q (energy/enstrophy/Sobolev) ⟹ компактность.
> _Caveat:_ Стандартные оценки компактности; ценность — Q-точность.

---

## #646 - `src/navier_stokes/Vorticity.v` - score 1 (exposition)

**Vorticity over Q: 2D stretching vanishes**

- **Topic.** Vorticity = enstrophy, palinstrophy, the norm hierarchy, 2D stretching vanishing, enstrophy production rate (2D dissipative), max vorticity bound, BKM sum.
- **Role.** NS (vorticity). Self-contained.
- **Counts.** Qed 26 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ завихренность/палинстрофия. _Roles:_ завихренность как роль; 2D-растяжение исчезает. _Rules:_ stretching_vanishes_2d; enstrophy_dissipation_2d. _P4:_ 2D-растяжение исчезает ⟹ 2D-диссипация над Q (Element).
- **Classical counterpart.** Vorticity/palinstrophy, the norm hierarchy, 2D stretching vanishing, the enstrophy production rate, max-vorticity/BKM are standard; NEW: nothing — exact Q vorticity analysis (2D stretching vanishes).
- **Tags.** navier-stokes, vorticity, 2D, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `vorticity_equals_enstrophy palinstrophy norm_hierarchy stretching_vanishes_2d enstrophy_dissipation_2d max_vorticity_bound bkm_sum vorticity_main` | Definition/Lemma | завихренность, 2D-растяжение исчезает, BKM |

**Key lemmas (deep):**

- **`stretching_vanishes_2d`** - В 2D растяжение вихря ИСЧЕЗАЕТ (нет vortex stretching) ⟹ энстрофия диссипативна ⟹ 2D-регулярность над Q. Element-сторона: структурная причина, почему 2D NS регулярна, а 3D нет. _(vorticity, 2D-stretching, enstrophy)_

**Uniqueness - score 1 (exposition).** Завихренность над Q (2D-растяжение исчезает ⟹ 2D-диссипация, иерархия норм, BKM).
> _Caveat:_ Структура завихренности классична; ценность — Q-точность (2D vs 3D).

