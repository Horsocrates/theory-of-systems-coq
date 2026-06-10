# Database - cluster `smalldirs`

_Generated from `smalldirs.json` by `generate.ps1` - do not edit by hand; edit the JSON._

**29 files / 292 Qed.** Score distribution: s5=0 / s4=0 / s3=0 / s2=15 / s1=14 / s0=0

---

## #67 - `src/arrow/ArrowFromModes.v` - score 2 (new-framing)

**Arrow from modes over Q: arrow of time = compression**

- **Topic.** Counting modes above a cutoff, total modes, information loss, tracked entropy, a full state, all modes tracked = reversible, partial tracking = irreversible, minimal tracking loss, the arrow as compression, and entropy monotone.
- **Role.** Leaf of the arrow-of-time branch (parallels physics/ThermodynamicArrow). Self-contained.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ моды выше отсечки; отслеживаемая энтропия; потеря информации. _Roles:_ стрела времени = роль из потери информации (сжатия); полное отслеживание обратимо. _Rules:_ all_tracked_reversible; partial_tracked_irreversible; arrow_is_compression; entropy_monotone. _P4:_ конечное число мод над Q (Element); стрела времени = необратимость огрубления (сжатия).
- **Classical counterpart.** The thermodynamic arrow of time as monotone entropy from information loss / coarse-graining (tracking fewer modes) is standard; NEW only as the framing 'arrow = compression' over Q.
- **Tags.** arrow-of-time, compression, entropy, new-framing

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `count_above/total_modes/info_loss/tracked_entropy/full_state` | Definition | счёт мод, потеря информации, энтропия |
| `all_modes_tracked/total_modes_full/all_tracked_reversible/partial_tracked_irreversible/minimal_tracking_loss` | Theorem | ★ полное=обратимо, частичное=необратимо |
| `arrow_is_compression/entropy_monotone/arrow_from_modes_synthesis` | Theorem | ★ стрела = сжатие; энтропия монотонна |

**Key lemmas (deep):**

- **`arrow_is_compression`** - Стрела времени отождествлена со сжатием/огрублением: полное отслеживание мод обратимо, частичное (потеря информации) необратимо → монотонная энтропия. Содержательное переобрамление «стрела=сжатие» над Q (связь с crown/CompressionIsPhysics), не вывод. _(arrow-of-time, compression, irreversible, entropy)_

**Uniqueness - score 2 (new-framing).** Стрела времени из мод над Q: полное отслеживание обратимо, частичное (потеря информации) необратимо, стрела = сжатие, энтропия монотонна.
> _Caveat:_ Термодинамическая стрела из огрубления/потери информации стандартна; вклад — переобрамление «стрела=сжатие», не новый результат.

---

## #68 - `src/casimir_branch/CasimirConvergence.v` - score 1 (exposition)

**Casimir convergence over Q: energy density converges with mode count**

- **Topic.** Energy density, densities at C2/C4/C8, the density converging, the process at N=2/4/8, linear growth, and the Casimir coefficient.
- **Role.** Leaf of the casimir_branch (parallels experimental/CasimirProcess). Self-contained.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ плотность энергии; число мод. _Roles:_ плотность Казимира = роль-предел процесса по числу мод. _Rules:_ density_converges; linear_growth; casimir_coefficient. _P4:_ конечные плотности над Q (Element); плотность как сходящийся процесс.
- **Classical counterpart.** The Casimir energy density converging as the mode count grows is standard; here a small Q instance (densities at C2/C4/C8 converging).
- **Tags.** casimir, convergence, exposition

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `energy_density/density_C2/_C4/_C8/process_N2/_N4/_N8/casimir_coefficient` | Definition | плотности, процесс, коэффициент |
| `density_converges/linear_growth/casimir_convergence_synthesis` | Theorem | ★ плотность сходится |

**Key lemmas (deep):**

- **`density_converges`** - Плотность энергии Казимира сходится с ростом числа мод (C2→C4→C8) над Q — корректный сходящийся процесс. Стандартное содержание (ср. experimental/CasimirProcess). _(casimir, convergence, density)_

**Uniqueness - score 1 (exposition).** Сходимость Казимира над Q: плотность энергии сходится с числом мод.
> _Caveat:_ Сходимость плотности Казимира стандартна; Q-инстанс без нового содержания (см. experimental/CasimirProcess).

---

## #69 - `src/casimir_branch/CasimirFromGraph.v` - score 2 (new-framing)

**Casimir from a graph over Q: vacuum always finite, force from energy**

- **Topic.** Vacuum energy squared, squared frequencies at C2/C4/C8, vacuum energies, positivity, vacuum grows, the Casimir energy and force approximation, the C4-C2 and C8-C4 differences, and vacuum always finite.
- **Role.** Leaf of the casimir_branch (vacuum-finiteness framing). Self-contained. June 2026 wave-4 sweep: vacuous finiteness-shams (exists q, _ = q) replaced by the by-type finite-ratio form (num#den); see UNIQUENESS.md.
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ вакуумная энергия (квадраты частот); моды графа. _Roles:_ Казимир = роль-разность энергий; вакуум всегда конечен. _Rules:_ vacuum_always_finite; casimir_force_approx; vacuum_grows. _P4:_ конечные вакуумные энергии над Q (Element); «вакуум всегда конечен» — нет расходимости на графе.
- **Classical counterpart.** Casimir energy from vacuum modes (finite after regularization, force from energy difference) is standard; NEW only as the P4 framing 'vacuum always finite' over a graph.
- **Tags.** casimir, vacuum-finite, new-framing

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `vacuum_energy_sq/omega_sq_C4/_C2/_C8_approx/E_vac_C2/_C4/_C8` | Definition | вакуумная энергия, частоты June 2026 wave-4 sweep: vacuous finiteness-shams (exists q, _ = q) replaced by the by-type finite-ratio form (num#den); see UNIQUENESS.md. |
| `vacuum_positive_C4/vacuum_grows/vacuum_grows_more/casimir_energy/casimir_force_approx` | Theorem | вакуум растёт, сила Казимира June 2026 wave-4 sweep: vacuous finiteness-shams (exists q, _ = q) replaced by the by-type finite-ratio form (num#den); see UNIQUENESS.md. |
| `casimir_C4_C2/_C8_C4/vacuum_always_finite/_C8/casimir_from_graph_synthesis` | Theorem | ★ вакуум всегда конечен June 2026 wave-4 sweep: vacuous finiteness-shams (exists q, _ = q) replaced by the by-type finite-ratio form (num#den); see UNIQUENESS.md. |

**Key lemmas (deep):**

- **`vacuum_always_finite`** - Вакуумная энергия на графе ВСЕГДА конечна (vacuum_always_finite_C8) — нет расходимости, сила Казимира из разности энергий. Перекликается с experimental/VacuumEnergy (там расходимость снимается регуляризацией; здесь граф конечен по построению). Вена-C-смежно. _(casimir, vacuum-finite, force)_

**Uniqueness - score 2 (new-framing).** Казимир из графа над Q: вакуумная энергия всегда конечна, сила Казимира из разности энергий мод.
> _Caveat:_ Энергия Казимира из вакуумных мод стандартна; вклад — графовая формулировка «вакуум всегда конечен», не новая физика.

---

## #90 - `src/cosmological/LambdaFromGraph.v` - score 2 (new-framing)

**Lambda from a graph over Q: no vacuum catastrophe (P4 resolves)**

- **Topic.** A vacuum density, densities at N=2/4/8 (all bounded), the density converging, no vacuum catastrophe, and 'P4 resolves'.
- **Role.** Leaf of the cosmological branch (vacuum-catastrophe dissolution, vein-C-adjacent). Self-contained.
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ плотность вакуума; число мод графа. _Roles:_ Lambda = роль-плотность вакуума; P4 как роль-разрешитель катастрофы. _Rules:_ density_bounded; density_converges; no_vacuum_catastrophe; P4_resolves. _P4:_ плотность вакуума ОГРАНИЧЕНА и сходится над Q (Element); катастрофа вакуума РАСТВОРЕНА — расходимости нет (вена C).
- **Classical counterpart.** The cosmological-constant (vacuum-catastrophe) problem is the huge mismatch between predicted and observed vacuum energy; NEW only as the P4 framing 'no vacuum catastrophe' over a graph — the vacuum density is bounded and converges (a process), so P4 dissolves the divergence.
- **Tags.** cosmological, vacuum-catastrophe, P4, new-framing

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `vacuum_density/density_2/_4/_8` | Definition/Theorem | плотность вакуума по N |
| `density_positive_concrete/density_bounded_2/_4/_8/density_converges` | Theorem | ★ плотность ограничена и сходится |
| `no_vacuum_catastrophe/P4_resolves/lambda_from_graph_synthesis` | Theorem | ★ нет катастрофы вакуума; P4 разрешает |

**Key lemmas (deep):**

- **`no_vacuum_catastrophe`** - «Нет катастрофы вакуума»: плотность вакуума на графе ограничена и сходится (density_bounded, density_converges) → P4_resolves растворяет расходимость космологической постоянной. Вена-C-смежно: вакуум как конечный сходящийся процесс, не расходящийся объект. Модельное, но честно сформулированное растворение. _(vacuum-catastrophe, lambda, P4-resolves, vein-C)_

**Uniqueness - score 2 (new-framing).** Lambda из графа над Q: плотность вакуума ограничена/сходится, «нет катастрофы вакуума» (P4 разрешает) — вена-C-смежное растворение расходимости.
> _Caveat:_ Проблема космологической постоянной реальна; здесь графовая модель с конечной сходящейся плотностью — P4-переобрамление, не разрешение физической проблемы Lambda.

---

## #91 - `src/cosmology_ext/BigBangProcess.v` - score 2 (new-framing)

**Big Bang as a process over Q: no singularity, first distinction**

- **Topic.** Initial graph size/energy/density (all finite), density over time, an entropy proxy, no singularity, the big bang as the first distinction, density decreasing, entropy increasing, and the arrow from growth.
- **Role.** Leaf of the cosmology extension (vein-C-adjacent: no singular initial object). Self-contained.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ начальный граф (конечный размер/энергия/плотность). _Roles:_ Большой взрыв = первое различение (роль); рост графа как стрела времени. _Rules:_ no_singularity; initial_energy_finite; entropy_increases; arrow_from_growth. _P4:_ начальное состояние КОНЕЧНО (Element), не сингулярная точка; космология как процесс роста (role-limit).
- **Classical counterpart.** Big-Bang cosmology with finite initial conditions and increasing entropy is standard; NEW only as the P4 framing 'no singularity' — the big bang is the first distinction, the initial energy/density finite (a process, not a singular point).
- **Tags.** cosmology, big-bang, no-singularity, process, new-framing

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `initial_graph_size/initial_energy/initial_density/density_at/entropy_proxy` | Definition | начальные величины, плотность, энтропия |
| `no_singularity/big_bang_is_first_distinction/initial_density_positive/initial_energy_finite` | Theorem | ★ нет сингулярности; взрыв = первое различение |
| `density_decreases/entropy_increases/arrow_from_growth/big_bang_process_synthesis` | Theorem | плотность падает, энтропия растёт |

**Key lemmas (deep):**

- **`no_singularity`** - «Нет сингулярности»: начальная энергия/плотность КОНЕЧНЫ (initial_energy_finite), Большой взрыв = первое различение, а не сингулярная точка. Вена-C-смежно: космология как процесс роста графа, без расходящегося начального объекта. _(no-singularity, big-bang, process, vein-C)_

**Uniqueness - score 2 (new-framing).** Большой взрыв как процесс над Q: нет сингулярности (конечные начальные величины), взрыв = первое различение, стрела времени из роста графа.
> _Caveat:_ Конечные начальные условия и рост энтропии — стандартная космология; вклад — P4-формулировка «нет сингулярности», не новая космологическая модель.

---

## #92 - `src/cosmology_ext/DarkEnergy.v` - score 1 (exposition)

**Dark energy over Q: cosmological constant from vacuum, no fine tuning**

- **Topic.** Vacuum density, lambda from vacuum, matter density, total energy, expansion rate, lambda positive, inflation from a small graph, no fine tuning, vacuum dominates at large N.
- **Role.** Leaf of the cosmology extension. Self-contained.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ плотности вакуума/материи; Lambda. _Roles:_ Lambda = роль (тёмная энергия); вакуум доминирует при большом N. _Rules:_ lambda_positive; no_fine_tuning; vacuum_dominates_large_N. _P4:_ конечные плотности над Q (Element); расширение как роль-следствие.
- **Classical counterpart.** A cosmological constant from vacuum energy driving expansion is standard cosmology; here only a small Q instance ('no fine tuning', lambda positive, vacuum dominates at large N).
- **Tags.** cosmology, dark-energy, lambda, exposition

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `vacuum_density/lambda_from_vacuum/matter_density/total_energy/expansion_rate` | Definition | плотности, Lambda, расширение |
| `lambda_positive/lambda_value/inflation_from_small_graph/no_fine_tuning` | Theorem | ★ Lambda>0, без тонкой настройки |
| `lambda_monotone/expansion_rate_positive/vacuum_dominates_large_N/total_geq_vacuum/lambda_linear/dark_energy_synthesis` | Theorem | вакуум доминирует, расширение |

**Key lemmas (deep):**

- **`no_fine_tuning`** - Lambda положительна без тонкой настройки в этой графовой модели — модельное утверждение над Q, не разрешение реальной проблемы космологической постоянной (ср. cosmological/LambdaFromGraph). Иллюстративно. _(dark-energy, lambda, no-fine-tuning)_

**Uniqueness - score 1 (exposition).** Тёмная энергия над Q: положительная Lambda из вакуума, без тонкой настройки, вакуум доминирует при большом N.
> _Caveat:_ Космологическая постоянная из вакуума стандартна; графовый Q-инстанс иллюстративен, не разрешение проблемы Lambda.

---

## #93 - `src/cosmology_ext/ExpandingGraph.v` - score 1 (exposition)

**Expanding graph over Q: Hubble proxy, matter dilutes, vacuum dominates late**

- **Topic.** A Hubble proxy, cosmological matter/vacuum/total densities, positive expansion, matter dilutes, vacuum constant, dark energy dominates late while matter dominates early, and vacuum fraction grows.
- **Role.** Leaf of the cosmology extension. Self-contained.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ плотности материи/вакуума; параметр Хаббла. _Roles:_ расширение = роль; материя разбавляется, вакуум постоянен. _Rules:_ matter_dilutes; vacuum_constant; dark_energy_dominates_late. _P4:_ конечные плотности над Q (Element); расширение как процесс.
- **Classical counterpart.** An expanding universe with matter diluting and vacuum/dark energy dominating late is standard FRW cosmology; here only a small Q instance with a Hubble proxy.
- **Tags.** cosmology, expansion, hubble, exposition

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `hubble/matter_density_cosm/vacuum_density_cosm/total_density_cosm` | Definition | Хаббл, плотности |
| `expansion_positive/matter_dilutes/vacuum_constant/dark_energy_dominates_late/matter_dominates_early` | Theorem | ★ материя разбавляется, вакуум доминирует поздно |
| `hubble_concrete/total_density_100/_2/vacuum_fraction_grows/expanding_graph_synthesis` | Theorem | доля вакуума растёт |

**Key lemmas (deep):**

- **`dark_energy_dominates_late`** - Материя разбавляется, вакуум постоянен → тёмная энергия доминирует на поздних временах — корректная FRW-картина над Q. Стандартная космология, без нового результата. _(expansion, dark-energy, dilution)_

**Uniqueness - score 1 (exposition).** Расширяющийся граф над Q: Хаббл, материя разбавляется, вакуум доминирует поздно, доля вакуума растёт.
> _Caveat:_ Разбавление материи и позднее доминирование тёмной энергии — стандартная FRW-космология; Q-инстанс без нового содержания.

---

## #95 - `src/crown/BornIsParseval.v` - score 2 (new-framing)

**Born is Parseval over Q: probability = spectral fraction = normalization**

- **Topic.** Sum of squares, a normalized state, Born probability at a mode, the Born total, a spectral fraction, energy above a cutoff, compression error, measurement miss, a normalized example, Born = spectral fraction, Born sums to one, Parseval is normalization, and compression-error = measurement-miss.
- **Role.** Leaf of the crown branch (the Born<->Parseval identity). Self-contained.
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ нормированное состояние; вероятности Борна; спектральная доля. _Roles:_ правило Борна = роль = равенство Парсеваля = нормировка. _Rules:_ born_equals_spectral; parseval_is_normalization; error_equals_miss. _P4:_ конечные суммы квадратов над Q (Element); Борн ≡ Парсеваль ≡ нормировка — точное тождество.
- **Classical counterpart.** That the Born rule equals Parseval's identity (probabilities = squared amplitudes summing to the norm) is a known observation in QM/signal processing; here an exact Q instance making 'Born = Parseval = normalization' explicit, with measurement-miss = compression-error.
- **Tags.** crown, born-rule, parseval, new-framing

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `sum_sq/normalized_state/born_prob_at/born_total/spectral_fraction/energy_above/compression_error/measurement_miss` | Definition | квадраты, Борн, спектральная доля |
| `psi_35_45/psi_normalized/psi_is_normalized/born_mode0/born_mode1/spectral_mode0/spectral_mode1` | Theorem | пример, значения Борна/спектра |
| `born_equals_spectral/born_sums_to_one/parseval_is_normalization/comp_error_M1/meas_miss_M1/error_equals_miss/born_is_parseval_synthesis` | Theorem | ★ Борн=Парсеваль=нормировка; ошибка=промах |

**Key lemmas (deep):**

- **`parseval_is_normalization`** - Правило Борна ≡ тождество Парсеваля ≡ нормировка состояния — одно равенство квадратов амплитуд, точно над Q. Плюс compression_error = measurement_miss: спектральная доля выше отсечки = вероятность «промаха» измерения. Аккуратное тождество-наблюдение (вена-C-смежно: измерение=сжатие), не новый результат. _(born-parseval, normalization, identity)_

**Uniqueness - score 2 (new-framing).** Борн = Парсеваль = нормировка над Q (одно тождество квадратов амплитуд); ошибка сжатия = промах измерения.
> _Caveat:_ Связь Борна и Парсеваля известна в КМ/обработке сигналов; вклад — явное Q-тождество и отождествление ошибка-сжатия=промах, не новый результат.

---

## #96 - `src/crown/CompressionIsPhysics.v` - score 1 (exposition)

**Compression is physics over Q: a dictionary (framing)**

- **Topic.** A compression-physics dictionary, the dictionary complete, compression as a process, compression = physical process, physics energy = compression energy, physics spectrum = compression spectrum, sound and light same type, all four same N, and resolution levels.
- **Role.** Leaf of the crown branch (the compression<->physics framing). Self-contained.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ словарь сжатие↔физика; энергия/спектр. _Roles:_ сжатие = роль-процесс = физический процесс (отождествление). _Rules:_ compression_is_pp; energy_is_energy; physics_spectrum=compression_spectrum. _P4:_ конечные словарные соответствия над Q (Element); отождествление-переобрамление.
- **Classical counterpart.** The analogy between data compression and physical mode truncation (same energy/spectrum) is a framing; here a small Q 'dictionary' tying compression to physics.
- **Tags.** crown, compression, framing, exposition

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `CPDictionary/the_dictionary/dictionary_complete/compression_process/compression_is_pp` | Definition/Theorem | ★ словарь сжатие↔физика |
| `physics_energy/compression_energy/energy_is_energy/physics_spectrum/compression_spectrum/sound_and_light_same_type` | Theorem | энергия=энергия, спектр=спектр |
| `all_four_same_N/resolution/half_resolution/full_resolution/compression_is_physics_synthesis` | Theorem | уровни разрешения |

**Key lemmas (deep):**

- **`compression_is_pp`** - Сжатие отождествлено с физическим процессом через словарь (энергия=энергия, спектр=спектр) — переобрамление-аналогия над Q, не вывод. Иллюстративно (связь с crown/BornIsParseval). _(compression, physics, framing)_

**Uniqueness - score 1 (exposition).** Словарь «сжатие = физика» над Q: энергия/спектр совпадают, звук и свет одного типа.
> _Caveat:_ Аналогия сжатие↔усечение мод — переобрамление, не вывод; иллюстративный словарь.

---

## #120 - `src/decoherence/DecoherenceFromModes.v` - score 1 (exposition)

**Decoherence from modes over Q: off-diagonal decay, diagonal preserved**

- **Topic.** A power helper, a decohere step, coherence after steps, no decoherence without coupling, full coupling instant, partial decoherence monotone, the diagonal element preserved, and n-step decay.
- **Role.** Leaf of the decoherence branch (parallels physics/Decoherence). Self-contained.
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ когерентность; вне-диагональные элементы; связь. _Roles:_ декогеренция = роль-затухание вне-диагонали; диагональ сохраняется. _Rules:_ no_coupling_no_decoherence; full_coupling_instant; diagonal_preserved. _P4:_ конечные шаги затухания над Q (Element); декогеренция как процесс затухания вне-диагонали.
- **Classical counterpart.** Decoherence as exponential decay of off-diagonal density-matrix elements (diagonal preserved, rate from coupling) is standard open-quantum-systems theory; here a small Q instance.
- **Tags.** decoherence, open-system, exposition

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `qpow/_0/_1/decohere_step/coherence_after` | Definition | шаг декогеренции, когерентность |
| `no_coupling_no_decoherence/no_coupling_after_3/_preserves/full_coupling_instant/_after_1/partial_step1/_step2/partial_monotone` | Theorem | ★ нет связи — нет декогеренции; полная — мгновенно |
| `diagonal_element/diagonal_preserved/n_step_decay/decoherence_from_modes_synthesis` | Theorem | ★ диагональ сохраняется, n-шаговое затухание |

**Key lemmas (deep):**

- **`diagonal_preserved`** - Декогеренция гасит вне-диагональные элементы (n_step_decay), сохраняя диагональ — корректная картина открытой квантовой системы над Q. Стандартное содержание. _(decoherence, off-diagonal, diagonal-preserved)_

**Uniqueness - score 1 (exposition).** Декогеренция из мод над Q: затухание вне-диагонали, диагональ сохраняется, скорость из связи.
> _Caveat:_ Декогеренция как затухание вне-диагонали — стандартная теория открытых систем; Q-инстанс без нового содержания.

---

## #121 - `src/decoherence/DecoherenceSynthesis.v` - score 1 (exposition)

**Decoherence synthesis over Q: decoherence is damping (summary)**

- **Topic.** Decoherence rate from coupling, stronger coupling = faster decay, trace preserved, irreversible, decoherence connects to damping, and decoherence is damping.
- **Role.** Summary node of the decoherence branch. Self-contained.
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ скорость декогеренции; связь; затухание. _Roles:_ узел-синтез: декогеренция = затухание. _Rules:_ decoherence_irreversible; decoherence_preserves_trace; decoherence_is_damping. _P4:_ агрегатор (Element); декогеренция отождествлена с затуханием.
- **Classical counterpart.** That decoherence is irreversible, trace-preserving and identifiable with damping (rate from coupling) is standard; here a 7-lemma summary.
- **Tags.** decoherence, summary, exposition

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `decoherence_rate_from_coupling/stronger_coupling_faster_decay/decoherence_preserves_trace` | Theorem | скорость из связи, след сохраняется |
| `decoherence_irreversible/decoherence_connects_to_damping/decoherence_grand_synthesis/decoherence_is_damping` | Theorem | ★ декогеренция = затухание, необратима |

**Key lemmas (deep):**

- **`decoherence_is_damping`** - Узел-синтез: декогеренция отождествлена с затуханием (необратима, сохраняет след). Собственной уникальности нет — агрегатор. _(summary, decoherence, damping)_

**Uniqueness - score 1 (exposition).** Сводка декогеренции над Q: декогеренция = затухание, необратима, сохраняет след.
> _Caveat:_ Узел-агрегатор; стандартные свойства декогеренции без нового результата.

---

## #128 - `src/entanglement/EntanglementFromModes.v` - score 2 (methods)

**Entanglement from modes over Q: Bell is rank-2, determinant witness**

- **Topic.** Product states, a matrix element, the 2x2 determinant, rank-1 vs entangled, a Bell state, product states have zero determinant (separable), the Bell determinant nonzero (entangled), Schmidt rank 2x2, and product = rank 1, Bell = rank 2.
- **Role.** Leaf of the entanglement branch (parallels physics/Entanglement). Self-contained.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ состояния (произведение/Белл); 2x2 определитель. _Roles:_ запутанность = роль-нефакторизуемость; det как роль-свидетель сепарабельности. _Rules:_ product_separable; bell_entangled; schmidt_rank_bell=2. _P4:_ конечные 2x2 состояния над Q (Element); запутанность = ненулевой определитель.
- **Classical counterpart.** Entanglement as non-factorizability (a Bell state is rank-2 / not a product, Schmidt rank), with the 2x2 determinant as a separability witness, is standard QM; here an exact Q instance.
- **Tags.** entanglement, bell, schmidt-rank, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `ProductState/mat_elem/det2/is_rank1/is_entangled/bell_state/product_00/product_plus` | Definition | состояния, определитель, ранг |
| `bell_det/bell_not_rank1/bell_entangled/product_00_det/product_separable/product_plus_det/product_plus_separable` | Theorem | ★ Белл запутан (det≠0), произведение сепарабельно |
| `schmidt_rank_2x2/schmidt_rank_product/schmidt_rank_bell/entanglement_from_modes_synthesis` | Theorem | ★ ранг Шмидта: произведение=1, Белл=2 |

**Key lemmas (deep):**

- **`bell_entangled`** - Состояние Белла имеет ненулевой 2x2 определитель (ранг Шмидта 2) → запутано, тогда как произведение сепарабельно (det=0) — точный определительный критерий запутанности над Q. Стандартная картина. _(entanglement, bell, schmidt-rank, determinant)_

**Uniqueness - score 2 (methods).** Запутанность из мод над Q: Белл = ранг 2 (det≠0), произведение сепарабельно (det=0), определитель как свидетель.
> _Caveat:_ Запутанность как нефакторизуемость/ранг Шмидта классична; вклад — точный 2x2 Q-критерий, не новый результат.

---

## #129 - `src/entanglement/EntanglementSynthesis.v` - score 1 (exposition)

**Entanglement synthesis over Q: determinant is a witness (summary)**

- **Topic.** Partial entanglement (determinant, entangled), nearly-separable states (small determinant, separable), observation collapses, and the determinant as a witness.
- **Role.** Summary node of the entanglement branch. Self-contained.
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ частично запутанные/почти сепарабельные состояния; определитель. _Roles:_ узел-синтез: det = свидетель запутанности. _Rules:_ partial_ent_entangled; nearly_sep_separable; det_is_witness. _P4:_ агрегатор (Element); определитель как непрерывный свидетель.
- **Classical counterpart.** That the determinant witnesses entanglement (partial entanglement, nearly-separable states, observation collapses) is standard; here a 7-lemma summary.
- **Tags.** entanglement, summary, exposition

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `partial_ent/_det/_entangled/nearly_sep/_det/_separable` | Theorem | частичная запутанность, почти сепарабельность |
| `observation_collapses/det_is_witness/entanglement_grand_synthesis` | Theorem | ★ det = свидетель; наблюдение коллапсирует |

**Key lemmas (deep):**

- **`det_is_witness`** - Узел-синтез: определитель — непрерывный свидетель запутанности (от почти-сепарабельных до сильно запутанных). Собственной уникальности нет — агрегатор EntanglementFromModes. _(summary, entanglement, witness)_

**Uniqueness - score 1 (exposition).** Сводка запутанности над Q: определитель как свидетель, наблюдение коллапсирует.
> _Caveat:_ Узел-агрегатор; определитель-свидетель уже доказан в EntanglementFromModes.

---

## #132 - `src/error_correction/CodeFromGraph.v` - score 2 (methods)

**Codes from a graph over Q: repetition/Hamming, rate, distance, Singleton**

- **Topic.** Repetition and Hamming code sizes/data/rate, Hamming distance, a general code distance, repetition detects 1 error, Hamming has a better rate, bounded rates, positive distance, a compression-error-correction duality, redundancy, and the Singleton bound.
- **Role.** Leaf of the error-correction branch. Self-contained.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ коды (повторения/Хэмминга); скорость/расстояние. _Roles:_ код = роль-защита; расстояние/скорость как роли-параметры. _Rules:_ hamming_better_rate; singleton_bound_hamming; compression_ec_duality. _P4:_ конечные коды над Q (Element); скорость/расстояние вычислимы.
- **Classical counterpart.** Repetition/Hamming codes, code rate/distance, the Singleton bound and a compression-duality are standard coding theory; here a small Q instance ('codes from a graph').
- **Tags.** error-correction, coding, singleton, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `repetition_code_size/_data/_rate/hamming_code_size/_data/_rate/hamming_distance/code_distance_gen` | Definition | коды, скорость, расстояние |
| `repetition_detects_1/hamming_better_rate/rate_bounded/distance_positive` | Theorem | ★ Хэмминг лучше по скорости |
| `compression_ec_duality/rates_positive/hamming_redundancy/singleton_bound_hamming/rate_ordering/code_from_graph_synthesis` | Theorem | ★ дуальность сжатие/ECC, граница Синглтона |

**Key lemmas (deep):**

- **`compression_ec_duality`** - Дуальность сжатия и коррекции ошибок (rate vs distance) над Q + граница Синглтона — корректная картина теории кодирования. Связь с crown/CompressionIsPhysics. Стандартное содержание. _(coding, singleton, compression-duality)_

**Uniqueness - score 2 (methods).** Коды из графа над Q: повторение/Хэмминг, скорость/расстояние, дуальность сжатие↔коррекция, граница Синглтона.
> _Caveat:_ Коды Хэмминга и граница Синглтона — учебная теория кодирования; вклад — Q-инстанс, не новый результат.

---

## #133 - `src/error_correction/ModeProtection.v` - score 1 (exposition)

**Mode protection over Q: rate-distance tradeoff**

- **Topic.** Boundary overlap, code distance/rate, distance as a rational, low modes protected, more redundancy = more protection, the rate-distance tradeoff, protection monotone, bounded overlap, and positive distance.
- **Role.** Leaf of the error-correction branch. Self-contained.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ перекрытие границы; расстояние/скорость кода. _Roles:_ защита мод = роль; компромисс скорость-расстояние. _Rules:_ more_redundancy_more_protection; rate_distance_tradeoff; protection_monotone. _P4:_ конечные параметры кода над Q (Element); защита растёт с избыточностью.
- **Classical counterpart.** The code rate-distance tradeoff (more redundancy = more protection) is standard coding theory; here a small Q instance about protecting low modes.
- **Tags.** error-correction, rate-distance, exposition

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `boundary_overlap/code_distance/code_rate/distance_as_Q` | Definition | перекрытие, расстояние, скорость |
| `low_modes_protected/more_redundancy_more_protection/rate_distance_tradeoff/protection_monotone` | Theorem | ★ компромисс скорость-расстояние |
| `overlap_bounded/zero_overlap/full_overlap/rate_bounded/distance_positive_3_8/mode_protection_synthesis` | Theorem | ограниченность перекрытия |

**Key lemmas (deep):**

- **`rate_distance_tradeoff`** - Компромисс между скоростью кода и расстоянием (больше избыточности → больше защиты) над Q — стандартная картина ECC. Уникальности нет. _(rate-distance, protection)_

**Uniqueness - score 1 (exposition).** Защита мод над Q: компромисс скорость-расстояние, больше избыточности — больше защиты.
> _Caveat:_ Компромисс скорость-расстояние — учебная теория кодирования; Q-инстанс без нового содержания.

---

## #151 - `src/extraction/GapCertificate.v` - score 2 (methods)

**Gap certificate over Q: certified-positive mass gap with decreasing error**

- **Topic.** A certificate guaranteeing the gap is positive and improves, a strictly decreasing error bound (3-step example), universality over beta, the gap always above epsilon, multi-beta positivity, convergence, and an interval bracket.
- **Role.** Certified-numerics leaf bridging the gauge mass-gap to OCaml extraction (with GapCompute/GapExtraction). Self-contained.
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ сертификат зазора; убывающая граница ошибки. _Roles:_ сертификат = роль-гарантия положительности зазора. _Rules:_ cert_guarantees_positive; error_bound_strict_decrease; gap_always_above_eps. _P4:_ конечный вычислимый сертификат над Q (Element); зазор как role-limit с гарантированной нижней границей.
- **Classical counterpart.** A computable certificate with a strictly-decreasing error bound guaranteeing a positive limit is a standard interval-arithmetic / certified-numerics device; here applied over Q to the Yang-Mills mass gap.
- **Tags.** extraction, mass-gap, certificate, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `cert_guarantees_positive/cert_improves/error_bound_strict_decrease/error_bound_3steps` | Theorem | ★ сертификат гарантирует положительность |
| `cert_pmg_universal/gap_always_above_eps/multi_beta_gap_pos/gap_converges` | Theorem | универсальность по beta, зазор > eps |
| `gap_upper_bound/gap_in_interval/error_at_0/_5/_10` | Theorem | интервальная скобка зазора |

**Key lemmas (deep):**

- **`gap_always_above_eps`** - Сертификат гарантирует, что масс-зазор всегда выше epsilon с убывающей границей ошибки — сертифицированная нижняя оценка зазора (role-limit) над Q, готовая к извлечению. Привязка к gauge/ массовому зазору. _(mass-gap, certificate, positive)_

**Uniqueness - score 2 (methods).** Сертификат масс-зазора над Q: гарантированная положительность с убывающей границей ошибки, универсальность по beta, интервальная скобка.
> _Caveat:_ Сертифицированные интервальные оценки — стандартная техника; вклад — применение к YM масс-зазору с извлечением, не новый численный метод.

---

## #152 - `src/extraction/GapCompute.v` - score 2 (methods)

**Gap compute over Q: the mass gap as a certified Cauchy computation**

- **Topic.** A compute_gap function (nonneg, equals the process, positive at beta=1), a quarter-power error bound (nonneg, telescoping, strong/valid/abs), Cauchy step, lower bound, monotonicity, and a gap certificate from the process.
- **Role.** Computational core of the extraction branch (mass gap). Self-contained.
- **Counts.** Qed 25 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ compute_gap; граница ошибки (степени 1/4). _Roles:_ вычисление зазора = роль-процесс; граница ошибки как роль-контроль. _Rules:_ compute_gap_eq_process; error_bound_quarter; compute_gap_cauchy_step. _P4:_ каждый шаг вычисления конечен над Q (Element); зазор = Cauchy-процесс с телескопической границей.
- **Classical counterpart.** Computing a Cauchy-convergent quantity with a telescoping/geometric (quarter-power) error bound is standard certified numerics; here applied over Q to the mass gap.
- **Tags.** extraction, mass-gap, compute, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `compute_gap/_beta1_M0/_nonneg/_eq_process/_pos/_beta1_M1/_beta1_M2` | Definition/Theorem | ★ compute_gap = процесс, положителен |
| `error_bound/_nonneg/_quarter/_0/_1/_2/step_le_error_bound/compute_gap_cauchy_step/_lower_bound/_monotone/qpow_quarter_le/_telescoping/_diff_nonneg/step_eq_error_diff/error_bound_strong/_valid/_abs` | Theorem | ★ граница ошибки (1/4), Cauchy-шаг |
| `GapCertificate/cert_value_positive/try_certify/cert_from_pmg/cert_pmg_valid/gap_minus_small_error/cert_beta1_pmg` | Definition/Theorem | сертификат из процесса |

**Key lemmas (deep):**

- **`compute_gap_eq_process`** - Вычислимая функция compute_gap СОВПАДАЕТ с процессом масс-зазора и Cauchy-сходится с телескопической границей ошибки (степени 1/4) — делает зазор исполнимо вычислимым над Q с гарантией. Питает извлечение в OCaml. _(mass-gap, compute, cauchy, error-bound)_

**Uniqueness - score 2 (methods).** Вычисление масс-зазора над Q: compute_gap = процесс, Cauchy-сходимость с телескопической границей ошибки (1/4), сертификат из процесса.
> _Caveat:_ Cauchy-вычисление с геометрической границей ошибки стандартно; вклад — применение к YM масс-зазору с извлечением, не новый метод.

---

## #153 - `src/extraction/GapExtraction.v` - score 2 (methods)

**Gap extraction over Q: an OCaml-ready certified gap calculator**

- **Topic.** A gap calculator and certified gap, calculator values/error/nonneg/positive/consistency at beta=1, and extraction-ready compute/error/calc with exact arithmetic.
- **Role.** Extraction wrapper of the mass-gap branch (OCaml-ready). Self-contained.
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ калькулятор зазора; сертифицированный зазор. _Roles:_ извлекаемая обёртка = роль (OCaml); точная Q-арифметика. _Rules:_ gap_calculator_consistent; extraction_ready_compute; exact_arithmetic. _P4:_ конечный извлекаемый калькулятор над Q (Element); точная арифметика без вещественных чисел.
- **Classical counterpart.** Wrapping a certified computation as an extractable calculator with exact rational arithmetic is standard program extraction; here for the mass gap.
- **Tags.** extraction, mass-gap, ocaml, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `gap_calculator/certified_gap/gap_calculator_beta1_M0/_error/_nonneg/_pos/_consistent/_beta1_error` | Definition/Theorem | ★ калькулятор зазора, согласованность |
| `extraction_ready_compute/_error/_calc/exact_arithmetic` | Theorem | ★ готово к извлечению, точная арифметика |

**Key lemmas (deep):**

- **`extraction_ready_calc`** - Калькулятор масс-зазора готов к извлечению в OCaml с точной рациональной арифметикой — делает сертифицированный зазор исполнимой программой. Чисто инфраструктурная обёртка над GapCompute. _(extraction, mass-gap, ocaml, exact)_

**Uniqueness - score 2 (methods).** Извлекаемый калькулятор масс-зазора над Q: готов к экспорту в OCaml с точной рациональной арифметикой.
> _Caveat:_ Извлечение сертифицированных вычислений стандартно; вклад — обёртка для YM масс-зазора, не новый метод.

---

## #548 - `src/gravity/CurvatureFromGraph.v` - score 2 (methods)

**Curvature from a graph over Q: Forman curvature, handshaking, mass creates curvature**

- **Topic.** Average degree, curvature at a vertex, scalar curvature, cycle-4 vs dense degrees, regular = flat, mass creates curvature, total curvature zero on a 4-cycle, denser = more curved, deficit = negative curvature, curvature detects inhomogeneity, and the handshaking lemma.
- **Role.** Leaf of the gravity branch (discrete curvature). Self-contained.
- **Counts.** Qed 15 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ степени вершин; кривизна; скалярная кривизна. _Roles:_ кривизна = роль из степеней; масса как роль-источник кривизны. _Rules:_ regular_flat; mass_creates_curvature; handshaking_cycle4. _P4:_ конечный граф над Q (Element); кривизна = дискретная функция степеней.
- **Classical counterpart.** Discrete (Forman/combinatorial) curvature from degrees, the handshaking lemma and curvature detecting inhomogeneity are standard discrete differential geometry; here a small Q instance ('mass creates curvature').
- **Tags.** gravity, curvature, forman, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `sum_Q/avg_degree/curvature_at/curvatures/scalar_curvature/cycle4_degrees/dense_degrees/fold_left_Qplus_shift/_acc/sum_Q_cons` | Definition/Lemma | степени, кривизна, скаляр |
| `regular_flat/mass_creates_curvature/total_curvature_zero_cycle4/_dense/denser_more_curved` | Theorem | ★ регулярный=плоский; масса создаёт кривизну |
| `avg_degree_regular/_dense_gt_2/deficit_negative_curvature/curvature_detects_inhomogeneity/handshaking_cycle4/_dense/curvature_from_graph_synthesis` | Theorem | ★ дефицит=отрицательная кривизна; handshaking |

**Key lemmas (deep):**

- **`mass_creates_curvature`** - Регулярный граф плоский, неоднородность степеней (масса) создаёт кривизну (Forman/комбинаторную) над Q; total_curvature_zero на 4-цикле = дискретный Гаусс-Бонне-отголосок, handshaking как сумма степеней. Корректная дискретная геометрия, переобрамляющая «массу→кривизну». _(curvature, forman, handshaking, gravity)_

**Uniqueness - score 2 (methods).** Кривизна из графа над Q: Forman-кривизна из степеней, регулярный=плоский, масса создаёт кривизну, handshaking, дефицит=отрицательная кривизна.
> _Caveat:_ Дискретная кривизна (Forman) и handshaking — стандартная дискретная геометрия; вклад — Q-инстанс «масса→кривизна», не новый результат.

---

## #549 - `src/gravity/GeodesicDeviation.v` - score 1 (exposition)

**Geodesic deviation over Q: curvature shortens, gravitational redshift (analogy)**

- **Topic.** Geodesic length along a path vs a cycle, metric deviation, a frequency ratio, flat geodesic, the cycle shorter, zero deviation when flat, curvature shortens, the local equivalence principle, gravitational redshift, and no shift at equal curvature.
- **Role.** Leaf of the gravity branch (geodesics/redshift analogy). Self-contained.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ длины геодезических; метрическое отклонение; частотное отношение. _Roles:_ кривизна = роль-укорачиватель; красное смещение как роль. _Rules:_ curvature_shortens; gravitational_redshift; equivalence_principle_local. _P4:_ конечные длины путей над Q (Element); геодезическая аналогия, не вывод ОТО.
- **Classical counterpart.** Geodesic deviation, gravitational redshift and the local equivalence principle are GR; here only a small graph analogy (curvature shortens, redshift, no shift at equal curvature).
- **Tags.** gravity, geodesic, redshift, exposition

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `geodesic_length_path/_cycle/metric_deviation/freq_ratio` | Definition | длины, отклонение, частота |
| `flat_geodesic/cycle_shorter/zero_deviation_flat/curvature_shortens` | Theorem | ★ кривизна укорачивает геодезическую |
| `equivalence_principle_local/gravitational_redshift/no_shift_equal_curvature/geodesic_deviation_synthesis` | Theorem | красное смещение, эквивалентность |

**Key lemmas (deep):**

- **`curvature_shortens`** - Кривизна укорачивает геодезическую, даёт красное смещение; нет смещения при равной кривизне — графовая аналогия ОТО над Q, не вывод. Иллюстративно. _(geodesic, redshift, curvature, analogy)_

**Uniqueness - score 1 (exposition).** Геодезическое отклонение над Q: кривизна укорачивает геодезическую, красное смещение, локальный принцип эквивалентности.
> _Caveat:_ Геодезическое отклонение и красное смещение — ОТО; графовая Q-аналогия иллюстративна, не вывод.

---

## #553 - `src/information/InformationFromModes.v` - score 2 (methods)

**Information from modes over Q: purity, linear entropy, entropy ordering**

- **Topic.** Sum of squared probabilities, sum of probabilities, purity, linear entropy, a pure state (purity 1, zero entropy), a uniform state (max entropy), a partial state, mixed = higher entropy, uniform = max entropy, the entropy ordering, and purity one for pure.
- **Role.** Leaf of the information branch. Self-contained.
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ вероятности; чистота; линейная энтропия. _Roles:_ энтропия = роль-мера смешанности; чистота как роль. _Rules:_ pure_zero_entropy; uniform_max_entropy; entropy_ordering. _P4:_ конечные распределения над Q (Element); энтропия/чистота вычислимы точно.
- **Classical counterpart.** Purity, linear entropy and the entropy ordering (pure < partial < uniform/maximal) are standard quantum information; here an exact Q instance.
- **Tags.** information, entropy, purity, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `sum_sq_probs/sum_probs/purity/linear_entropy` | Definition | чистота, линейная энтропия |
| `pure_state_4/pure_purity/pure_zero_entropy/uniform_state_4/uniform_purity/uniform_entropy/partial_state_4/partial_purity/partial_entropy` | Theorem | чистое/равномерное/частичное состояния |
| `mixed_higher_entropy/uniform_max_entropy/entropy_ordering/purity_one_for_pure/information_from_modes_synthesis` | Theorem | ★ упорядочение энтропии, чистота=1 для чистого |

**Key lemmas (deep):**

- **`entropy_ordering`** - Упорядочение энтропии (чистое < частичное < равномерное/максимальное) и purity=1 для чистого состояния над Q — корректная квантово-информационная картина. Стандартное содержание. _(entropy, purity, ordering)_

**Uniqueness - score 2 (methods).** Информация из мод над Q: чистота, линейная энтропия, упорядочение чистое<частичное<равномерное, purity=1 для чистого.
> _Caveat:_ Чистота и линейная энтропия — стандартная квантовая информация; вклад — точный Q-инстанс, не новый результат.

---

## #554 - `src/information/LandauerConnection.v` - score 2 (methods)

**Landauer connection over Q: erasure cost proportional to temperature**

- **Topic.** A Landauer cost, erasure energy (positive), erasure scales, cost proportional to temperature, zero cost at zero temperature, erasure uniform->pure and partial->pure.
- **Role.** Leaf of the information branch bridging to thermodynamics. Self-contained.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ стоимость Ландауэра; энергия стирания; температура. _Roles:_ стирание = роль-затрата (∝ T); связь информации и термодинамики. _Rules:_ cost_proportional_to_T; zero_temp_zero_cost; erasure_uniform_to_pure. _P4:_ конечная стоимость над Q (Element); стирание = термодинамическая затрата.
- **Classical counterpart.** Landauer's principle (erasure has a thermodynamic cost proportional to temperature, zero at zero temperature) is standard; here a small Q instance tying erasure to the thermal branch.
- **Tags.** information, landauer, thermodynamics, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `landauer_cost/erasure_energy/erasure_positive/_concrete/erasure_scales` | Definition/Theorem | стоимость, энергия стирания |
| `cost_proportional_to_T/zero_temp_zero_cost/erasure_uniform_to_pure/erasure_partial_to_pure/landauer_connection_synthesis` | Theorem | ★ стоимость ∝ T, ноль при T=0 |

**Key lemmas (deep):**

- **`cost_proportional_to_T`** - Стоимость стирания пропорциональна температуре (ноль при T=0) — принцип Ландауэра над Q, связывающий информацию с термодинамикой. Стандартное содержание. _(landauer, erasure, thermodynamics)_

**Uniqueness - score 2 (methods).** Связь Ландауэра над Q: стоимость стирания ∝ температуре, ноль при T=0, стирание переводит распределение в чистое.
> _Caveat:_ Принцип Ландауэра стандартен; вклад — Q-инстанс, связывающий стирание с термальной ветвью, не новый результат.

---

## #557 - `src/ionization/CoulombOnGraph.v` - score 1 (exposition)

**Coulomb on a graph over Q: bound vs free levels, ionization**

- **Topic.** Four effective energies, the nth energy, counting negatives, a bound count, ionization energy, the ground state negative, excited positive, a Coulomb potential whose magnitude decreases, ordered energies, and positive ionization.
- **Role.** Leaf of the ionization branch (parallels linalg/IonizationThreshold). Self-contained.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ эффективные энергии; кулоновский потенциал. _Roles:_ связанное (E<0) / свободное (E>0) = роли; ионизация как роль-порог. _Rules:_ ground_state_negative; excited_positive; ionization_positive. _P4:_ конечные уровни над Q (Element); связанность = отрицательная энергия.
- **Classical counterpart.** Bound (negative) vs free (positive) energy levels for a Coulomb potential and counting bound states is standard; here a small graph instance.
- **Tags.** ionization, coulomb, bound-free, exposition

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `effective_energies_4/nth_energy/count_negatives/n_bound/ionization_energy/coulomb_potential` | Definition | энергии, счёт связанных, потенциал |
| `ground_state_negative/excited_positive/potential_magnitude_decreases/potential_at_origin/n_bound_is_1/ionization_energy_half` | Theorem | ★ основное E<0, возбуждённое E>0 |
| `energies_ordered/second_excited_positive/ionization_positive/coulomb_on_graph_synthesis` | Theorem | упорядочение, ионизация>0 |

**Key lemmas (deep):**

- **`ground_state_negative`** - Основное состояние связано (E<0), возбуждённые свободны (E>0); счёт связанных состояний над Q — корректная кулоновская картина. Стандартное содержание. _(coulomb, bound-free, ionization)_

**Uniqueness - score 1 (exposition).** Кулон на графе над Q: связанное (E<0) vs свободное (E>0), счёт связанных, положительная ионизация.
> _Caveat:_ Дихотомия связанное/свободное стандартна; графовый Q-инстанс без нового содержания.

---

## #558 - `src/ionization/IonizationThreshold.v` - score 2 (methods)

**Ionization threshold over Q: a decidable bound/free test**

- **Topic.** A threshold, is_bound/is_free, a decidable bound test, ionization cost, the threshold separating bound from free, bound needs energy, a concrete ionization, free already ionized, bound/free complementary and exclusive, and deeper = more energy.
- **Role.** Leaf of the ionization branch with a decidable boundary. Self-contained.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ порог; связанное/свободное; стоимость ионизации. _Roles:_ порог = роль-граница; РАЗРЕШИМЫЙ тест связанности. _Rules:_ is_bound_dec; threshold_separates; bound_free_exclusive. _P4:_ конечный разрешимый тест над Q (Element); граница bound/free вычислима (вена A-смежно).
- **Classical counterpart.** The bound/free threshold with a decidable test and ionization cost is standard; NEW only as a small Q instance with a DECIDABLE bound-state test (vein-A-flavoured: a decidable boundary).
- **Tags.** ionization, decidable, bound-free, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `threshold/is_bound/is_free/is_bound_dec/ionization_cost` | Definition | ★ разрешимый тест связанности |
| `threshold_separates/bound_needs_energy/concrete_ionization/free_already_ionized` | Theorem | ★ порог разделяет bound/free |
| `bound_free_complement/bound_free_exclusive/deeper_more_energy/ionization_threshold_synthesis` | Theorem | комплементарность, глубже=больше энергии |

**Key lemmas (deep):**

- **`is_bound_dec`** - РАЗРЕШИМЫЙ тест связанности состояния (is_bound_dec) над Q: граница bound/free вычислима, состояния комплементарны и взаимоисключающи. Слабый отголосок вены A (разрешимая граница финитизации), но на стандартном содержании. _(decidable, bound-free, vein-A-adjacent)_

**Uniqueness - score 2 (methods).** Порог ионизации над Q с РАЗРЕШИМЫМ тестом связанности: граница bound/free вычислима, состояния комплементарны/взаимоисключающи.
> _Caveat:_ Порог связанное/свободное стандартен; вклад — разрешимый Q-тест (вена-A-смежно), не новый результат.

---

## #1782 - `src/synthesis/DeeperPhysicsSynthesis.v` - score 1 (exposition)

**Deeper physics synthesis: four directions, one tree (summary node)**

- **Topic.** An 8-lemma synthesis tying error-correction, ionization, general-relativity and cosmology branches into one full-physics tree.
- **Role.** Summary node connecting physics sub-branches. Self-contained.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ ветви физики (4 направления). _Roles:_ узел-синтез: четыре направления — одно дерево. _Rules:_ four_directions_connected; full_physics_tree. _P4:_ агрегатор (Element); собственного содержания нет.
- **Classical counterpart.** A summary node connecting four physics directions (error correction, ionization, GR, cosmology) to one tree; no new content.
- **Tags.** synthesis, summary, exposition

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `branch1_error_correction/branch2_ionization/branch3_general_relativity/branch4_cosmology` | Theorem | четыре направления |
| `four_directions_connected/full_physics_tree/project_total/deeper_physics_grand_synthesis` | Theorem | ★ единое дерево физики |

**Key lemmas (deep):**

- **`full_physics_tree`** - Узел-агрегатор четырёх физических направлений в одно дерево. Собственной уникальности нет. _(summary, physics)_

**Uniqueness - score 1 (exposition).** Сводка: коррекция ошибок, ионизация, ОТО и космология — одно дерево физики.
> _Caveat:_ Чистый узел-агрегатор; собственного результата нет.

---

## #1783 - `src/synthesis/PhysicsInformationSynthesis.v` - score 1 (exposition)

**Physics-information synthesis: five extensions, one root (summary node)**

- **Topic.** A 7-lemma synthesis tying decoherence, cosmological, arrow-of-time, entanglement and information branches to one physics-information root.
- **Role.** Summary node connecting physics/information sub-branches. Self-contained.
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ пять расширений (декогеренция, космология, стрела, запутанность, информация). _Roles:_ узел-синтез: пять расширений — один корень. _Rules:_ five_extensions_from_one_root. _P4:_ агрегатор (Element); собственного содержания нет.
- **Classical counterpart.** A summary node tying five extensions (decoherence, cosmological, arrow, entanglement, information) to one root; no new content.
- **Tags.** synthesis, summary, exposition

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `ext1_decoherence/ext2_cosmological/ext3_arrow/ext4_entanglement/ext5_information` | Theorem | пять расширений |
| `physics_information_grand_synthesis/five_extensions_from_one_root` | Theorem | ★ один корень пяти расширений |

**Key lemmas (deep):**

- **`five_extensions_from_one_root`** - Узел-агрегатор пяти физико-информационных расширений. Собственной уникальности нет. _(summary, information)_

**Uniqueness - score 1 (exposition).** Сводка: декогеренция/космология/стрела/запутанность/информация из одного корня.
> _Caveat:_ Чистый узел-агрегатор; собственного результата нет.

---

## #1790 - `src/thermal/SecondLaw.v` - score 2 (methods)

**Second law over Q: entropy increases under coupling, equilibrium has zero flow**

- **Topic.** A coupled step vs no flow when uncoupled, energy flow under coupling, the gap decreasing, entropy before/after coupling, entropy increasing, and equilibrium with zero variance and no flow.
- **Role.** Leaf of the thermal branch (parallels physics/ThermodynamicArrow). Self-contained.
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ связанные моды; энергетический поток; энтропия. _Roles:_ второй закон = роль-монотонность энтропии; равновесие как роль-фикс. _Rules:_ coupled_flow; entropy_increases; equilibrium_no_flow. _P4:_ конечные шаги над Q (Element); энтропия монотонна; равновесие — нулевой поток.
- **Classical counterpart.** The second law (entropy increases under coupling toward equilibrium, zero flow at equilibrium) is classical thermodynamics; here only a small coupled-mode Q instance.
- **Tags.** thermal, second-law, entropy, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `coupled_step/uncoupled_no_flow/coupled_flow/gap_decreases` | Definition/Theorem | связанный шаг, поток, зазор падает |
| `before_coupling_entropy/after_coupling_entropy/entropy_increases` | Theorem | ★ энтропия растёт при связывании |
| `equilibrium_zero_variance/equilibrium_no_flow/second_law_synthesis` | Theorem | равновесие: нулевой поток |

**Key lemmas (deep):**

- **`entropy_increases`** - Энтропия растёт при связывании мод, равновесие = нулевой поток/дисперсия — корректная Q-формализация второго начала на малой модели. Стандартная термодинамика. _(second-law, entropy, equilibrium)_

**Uniqueness - score 2 (methods).** Второе начало над Q: энтропия растёт при связывании мод, равновесие = нулевой поток и нулевая дисперсия.
> _Caveat:_ Второе начало термодинамики классично; вклад — Q-формализация на связанных модах, не новый результат.

---

## #1791 - `src/thermal/ThermalFromModes.v` - score 1 (exposition)

**Thermal from modes over Q: temperature, entropy, variance**

- **Topic.** Total mode energy, temperature, a pure tone vs a thermal spread, active-mode counting, more active modes = more entropy, energy variance, low (thermal) vs high (pure tone) variance, temperature from energy, and same energy / different distribution.
- **Role.** Leaf of the thermal branch. Self-contained.
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ энергии мод; температура; занятость мод. _Roles:_ температура = роль (средняя энергия); энтропия из числа активных мод. _Rules:_ more_active_more_entropy; thermal_low_variance; pure_tone_high_variance. _P4:_ конечные распределения мод над Q (Element); температура/энтропия как роли.
- **Classical counterpart.** Temperature as average mode energy, entropy from mode occupation and energy variance is standard statistical mechanics; here only a small Q instance (pure tone vs thermal).
- **Tags.** thermal, temperature, entropy, exposition

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `total_energy_modes/temperature/pure_tone_4/thermal_4/omega_4/active_modes_aux/active_modes/sum_sq/sum_list/energy_variance_simple` | Definition | энергия, температура, занятость, дисперсия |
| `pure_tone_one_active/thermal_all_active/more_active_more_entropy` | Theorem | ★ больше активных мод — больше энтропии |
| `thermal_low_variance/pure_tone_high_variance/variance_ordering/temperature_from_energy/temperature_zero/pure_tone_energy/thermal_energy/same_energy_different_distribution/thermal_from_modes_synthesis` | Theorem | дисперсия, температура, одна энергия — разные распределения |

**Key lemmas (deep):**

- **`same_energy_different_distribution`** - Одна и та же энергия может иметь разное распределение по модам (чистый тон vs термальное) → разная энтропия — корректная стат-мех картина над Q. Иллюстративно. _(temperature, entropy, distribution)_

**Uniqueness - score 1 (exposition).** Термальность из мод над Q: температура=средняя энергия, энтропия из числа активных мод, чистый тон vs термальное при равной энергии.
> _Caveat:_ Температура и энтропия из мод — стандартная стат-механика; Q-инстанс без нового содержания.

---

## #1792 - `src/thermal/ThermalSynthesis.v` - score 1 (exposition)

**Thermal synthesis: heat is equilibrium sound (summary node)**

- **Topic.** A tiny grand synthesis: heat is equilibrium sound, zero-point energy is positive.
- **Role.** Summary node of the thermal branch. Self-contained.
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ результаты термальной ветви. _Roles:_ узел-синтез: тепло = равновесный звук. _Rules:_ heat_is_equilibrium_sound; zero_point_positive. _P4:_ агрегатор (Element); собственного содержания нет.
- **Classical counterpart.** A 3-lemma summary node: heat is equilibrium sound, zero-point energy positive; no new content.
- **Tags.** thermal, summary, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `thermal_grand_synthesis/zero_point_4/zero_point_positive/heat_is_equilibrium_sound` | Theorem | ★ тепло = равновесный звук |

**Key lemmas (deep):**

- **`heat_is_equilibrium_sound`** - Узел-агрегатор: тепло отождествлено с равновесным звуком (модами). Собственной уникальности нет. _(summary, thermal)_

**Uniqueness - score 1 (exposition).** Сводка термальной ветви: тепло = равновесный звук, нулевая энергия положительна.
> _Caveat:_ Чистый узел-агрегатор; собственного результата нет.

