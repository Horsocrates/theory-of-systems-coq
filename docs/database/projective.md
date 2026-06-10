# Database - cluster `projective`

_Generated from `projective.json` by `generate.ps1` - do not edit by hand; edit the JSON._

**7 files / 210 Qed.** Score distribution: s5=0 / s4=0 / s3=4 / s2=3 / s1=0 / s0=0

---

## #1040 - `src/projective/ConnectionTheorems.v` - score 3 (new-framing)

**Everything is a projective system: Cauchy reals, Q-states, levels, intervals, Banach — one P4 framing**

- **Topic.** Connection theorems showing the major ToS process-constructions are projective: Cauchy sequences are projective-compatible, the Q-tower is complete, quantum states/normalization are projective observables, the level hierarchy and nested intervals are projective systems, Banach iterations are projective-Cauchy, and P4_is_projective / projective_avoids_paradoxes.
- **Role.** Synthesis hub of the projective branch (vein C): unifies CauchyReal, QState, Level, Banach under one projective umbrella. Self-contained.
- **Counts.** Qed 22 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; ToS: projective modules (local)
- **E/R/R.** _Elements:_ проективные системы; совместимые семейства (Cauchy, состояния, уровни, интервалы). _Roles:_ проективный предел = роль (X как процесс); проекции связывают стадии. _Rules:_ cauchy_as_projective; levels_as_projective; banach_as_projective; P4_is_projective. _P4:_ P4 ЕСТЬ проективная система: каждая стадия конечна/актуальна (Element), объект — совместимый процесс (role-limit); projective_avoids_paradoxes — почему нет актуальной бесконечности.
- **Classical counterpart.** Inverse/projective limits in topology and category theory are classical; NEW is the unifying observation that ToS's Cauchy reals, quantum states, level hierarchy, intervals AND Banach iterations are ALL instances of one projective (P4) system — and that this is why P4 avoids the actual-infinity paradoxes.
- **Tags.** projective, P4, vein-C, cauchy, synthesis, new-framing

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `cauchy_is_proj_compatible/Q_tower_id_proj/cauchy_as_projective/Q_tower_complete/cauchy_equivuiv_is_proj_equiv` | Theorem | ★ числа Коши как проективная система |
| `qstate_as_projective_obs/ip_agrees_at_dim/qstate_normalization_obs` | Theorem | квантовые состояния как проективные наблюдаемые |
| `level_projection_obs/levels_as_finite_proj_sys/levels_as_projective` | Theorem | иерархия уровней как проективная система |
| `intervals_as_projective/interval_arithmetic_consistent/nested_interval_inc_cauchy/dec_cauchy` | Theorem | вложенные интервалы как проективные |
| `banach_iterations_cauchy_obs/_cauchy/banach_as_projective/fixed_point_uniqueness_projective` | Theorem | итерации Банаха как проективные |
| `P4_is_projective/projective_avoids_paradoxes/projective_framework_summary` | Theorem | ★ P4=проективно; избегает парадоксов |

**Key lemmas (deep):**

- **`P4_is_projective`** - Центральное наблюдение: принцип P4 (конечная актуальность) ЕСТЬ проективная система — конечные стадии + совместимые проекции, объект существует как процесс, не как завершённый предел. Объединяет вену C (ℝ/состояние/уровень/интервал = процесс) под одной категорной структурой. _(P4, projective, vein-C, synthesis)_
- **`projective_avoids_paradoxes`** - Проективная формулировка ОБЪЯСНЯЕТ, почему P4 избегает парадоксов актуальной бесконечности: ни одна стадия не содержит завершённого бесконечного объекта (ср. вена E, no_banach_tarski в ProcessMeasure). Связывает онтологию процесса с разрешением парадоксов. _(paradox, no-actual-infinity, vein-E-adjacent)_

**Uniqueness - score 3 (new-framing).** Cauchy-реалы, квантовые состояния, иерархия уровней, интервалы и итерации Банаха — ВСЕ суть один проективный (P4) объект; projective_avoids_paradoxes объясняет отсутствие актуальной бесконечности. Вена C, узел-синтез.
> _Caveat:_ Проективные/обратные пределы — классика топологии и теории категорий; вклад — наблюдение, что разрозненные ToS-конструкции суть одна проективная система, не новая математика пределов.

---

## #1041 - `src/projective/ProcessMeasure.v` - score 3 (new-framing)

**Measure as a process over Q: refinement system, consistent totals, no Banach-Tarski**

- **Topic.** Finite measures with cells and totals, uniform/point measures, pair-summing under dyadic refinement preserving the total, a compatible ProcessMeasure with constant total, stage integrals (monotone, scale, Lipschitz, Cauchy), finite additivity, and an explicit no_banach_tarski.
- **Role.** Measure/integration leaf of the projective branch (vein C). Self-contained (QArith).
- **Counts.** Qed 32 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ конечные меры (ячейки+тотал); дискретные веса; рефайнмент-разбиения. _Roles:_ мера = роль-предел процесса рефайнмента; интеграл как предел ступенчатых. _Rules:_ refine_preserves_total; pm_total_constant; stage_integral_cauchy; finite_additivity. _P4:_ каждая стадия меры конечна и точна (Element); мера — совместимый процесс рефайнмента (role-limit); no_banach_tarski — нет неизмеримых множеств/парадоксов выбора.
- **Classical counterpart.** Finitely-additive measures, refinement of partitions, and integration as a limit of step functions are classical; NEW is the P4/projective framing of measure as a refinement PROCESS with consistent totals — explicitly excluding Banach-Tarski (no non-measurable choice paradoxes).
- **Tags.** measure, process, no-banach-tarski, vein-C, new-framing

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `pow2/_pos/_S/FiniteMeasure/fm_total/fm_cell/_nonneg` | Definition/Lemma | конечная мера, ячейки |
| `uniform_weights/_length/_nonneg/uniform_measure/point_weights/_length/_nonneg/point_measure` | Definition/Theorem | равномерная и точечная меры |
| `sum_pairs/_nonneg/_half_length/_pow2_length/refine_proj/fold_left_Qplus_app/_cons/sum_pairs_total/refine_preserves_total` | Definition/Theorem | ★ рефайнмент сохраняет тотал |
| `fm_compatible/ProcessMeasure/pm_total_consistent/_constant` | Definition/Theorem | ★ совместимая мера-процесс, тотал постоянен |
| `sample_values/_length/stage_integral/_scale/_const_obs/_mono_obs/is_lipschitz/integral_diff_bound_obs/process_integral_cauchy_obs/_nonneg_obs` | Definition/Theorem | интеграл как процесс (Коши) |
| `no_banach_tarski/refine_monotone/fm_to_step/_widths_nonneg/fm_step_integral_obs/uniform_compatible_obs/uniform_pm_exists_obs/P4_measure_as_process/finite_additivity/pm_convex_obs` | Theorem | ★ нет Банаха-Тарского; мера=процесс; конечная аддитивность |

**Key lemmas (deep):**

- **`P4_measure_as_process`** - Мера ЕСТЬ процесс рефайнмента с совместимыми (сохраняющими тотал) стадиями — вена C. Интеграл — Cauchy-процесс ступенчатых функций. Никаких сигма-алгебр/полной аддитивности как завершённых объектов: только конечная аддитивность на актуальных стадиях. _(measure, process, vein-C, refinement)_
- **`no_banach_tarski`** - Явно исключает парадокс Банаха-Тарского: процессная мера не допускает неизмеримых множеств (нет AC-выбора неизмеримых кусков). Связь вены C (мера=процесс) с веной E (нет парадоксов) и с settheory/ChoicePriceMap. _(banach-tarski, no-AC, vein-E-adjacent)_

**Uniqueness - score 3 (new-framing).** Мера над Q как процесс рефайнмента с сохранением тотала + интеграл-Коши + конечная аддитивность, явно БЕЗ Банаха-Тарского — вена C (мера=процесс) на стыке с веной E (нет парадоксов выбора).
> _Caveat:_ Конечно-аддитивные меры и интеграл ступенчатыми функциями классичны; вклад — P4/проективное переобрамление меры как процесса и явное исключение неизмеримых множеств, не новая теория меры.

---

## #1042 - `src/projective/ProcessOperator.v` - score 2 (methods)

**Operators as processes over Q: CCR, unbounded position/momentum, operator algebra**

- **Topic.** Process operators with apply/eq/zero/id/scale/add, observables as process operators, position (unbounded, symmetric) and momentum (unbounded) operators, the commutator (antisymmetric, linear, Jacobi), CCR structure, position-momentum non-commutation, bounded operators, and P4_operators_are_processes.
- **Role.** Operator-theory leaf of the projective branch; parallels physics/QObservable. Self-contained (QArith).
- **Counts.** Qed 29 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ процессные операторы (действуют постадийно); наблюдаемые. _Roles:_ оператор = роль-преобразование процесса; коммутатор как роль-некоммутативность. _Rules:_ po_apply/po_add/po_scale; commutator_antisym; ccr_structural; position_unbounded. _P4:_ ограниченные операторы — Element (действуют на каждой стадии); неограниченность позиции/импульса — role-limit (растёт со стадией); CCR постадийно.
- **Classical counterpart.** Linear operators on Hilbert space, the CCR [x,p]=i, unbounded position/momentum, and the operator algebra are standard QM; NEW only as a projective/process formalization over Q where operators act stagewise and unboundedness is a role-limit.
- **Tags.** operator, CCR, process, quantum, methods

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `ProcessOp/po_apply/po_eq/_refl/_sym/_trans/po_zero/po_id/po_scale/po_add` | Definition/Lemma | процессные операторы и операции |
| `po_id_action/_zero_action/_scale_zero/_scale_one/_add_comm/_scale_distrib` | Theorem | алгебра операторов |
| `obs_to_po/diag_po/obs_to_po_action` | Definition/Theorem | наблюдаемые как операторы |
| `pos_eigenval/pos_eigenvec/position_op/pos_eigenval_nonneg/position_unbounded/_symmetric` | Definition/Theorem | ★ позиция: неограничена, симметрична |
| `momentum_scale/_nonneg/momentum_unbounded` | Definition/Theorem | ★ импульс неограничен |
| `commutator/_antisym_obs/map2_plus_neg_zero/_self_zero/_linear_obs/jacobi_identity_observation/ccr_structural/position_momentum_noncommuting` | Definition/Theorem | ★ коммутатор, CCR, некоммутативность x,p |
| `is_bounded_op/zero_bounded/id_bounded/scale_bounded/tobs_is_process_op/bounded_preserves_normalizable/P4_operators_are_processes/process_op_algebra` | Definition/Theorem | ★ операторы=процессы |

**Key lemmas (deep):**

- **`P4_operators_are_processes`** - Операторы действуют ПОСТАДИЙНО на процессных состояниях — ограниченные операторы суть Element, тогда как неограниченные (позиция/импульс) корректно живут как role-limit (растущая норма). CCR [x,p] выражается структурно без завершённого бесконечномерного гильбертова пространства. _(operator, process, P4, CCR)_
- **`position_momentum_noncommuting`** - Позиция и импульс не коммутируют (ccr_structural) — источник принципа неопределённости, формализованный над Q постадийно. Перекликается с heisenberg/ кластером и physics/InnerProductSpace. _(non-commuting, uncertainty, CCR)_

**Uniqueness - score 2 (methods).** Квантовые операторы как процессы над Q: CCR и некоммутативность x,p постадийно, неограниченность как role-limit, ограниченные операторы как Element.
> _Caveat:_ Операторы, CCR и неограниченность x,p — стандартная КМ; вклад — проективно-процессная Q-формализация, не новая операторная теория.

---

## #1043 - `src/projective/ProjectiveLimit.v` - score 3 (new-framing)

**Projective limit over Q: Frechet metric system, stagewise convergence, Banach on the limit**

- **Topic.** Metric projective systems with non-expanding projections, a per-stage and Frechet (weighted-sum) distance proven to be a metric, Cauchy/convergence in the projective sense, the limit element converging downward, projective contractions with a Banach principle and unique fixed point, and Q/QVec towers as instances.
- **Role.** Core construction of the projective branch; consumed by ConnectionTheorems, QuantumTower. Self-contained (QArith).
- **Counts.** Qed 38 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ метрические проективные системы; стадии с неэкспансивными проекциями. _Roles:_ проективный предел = роль-объект; Fréchet-метрика как роль-расстояние. _Rules:_ proj_dist_partial_triangle; frechet_controls_stage; proj_banach_principle; proj_fixed_unique. _P4:_ каждая стадия конечна (Element); предел — Cauchy-процесс совместимых элементов (role-limit); Банах на самой проективной системе.
- **Classical counterpart.** The projective (inverse) limit of a metric/Frechet system and the Banach fixed-point principle on it are classical; NEW is the explicit Q construction where the Frechet partial distances are Cauchy, the limit element converges stagewise, and the Banach principle is proven on the projective system itself.
- **Tags.** projective-limit, frechet, banach, process, vein-C, new-framing

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `MetricProjSys/mps_proj_nonexpand_iter/mps_dist_eq_zero/mps_elem_dist_zero` | Definition/Lemma | метрическая проективная система |
| `proj_dist_term/_partial/_nonneg/_bounded/_sym/_triangle/_zero/_compat` | Definition/Theorem | ★ Fréchет-метрика на системе |
| `proj_dist_partial_nonneg/_inc/_bounded/_sym/partial_sum_plus/_triangle/_zero` | Theorem | свойства частичной метрики |
| `is_cauchy_proj/converges_proj/convergent_is_cauchy_proj/frechet_partials_cauchy/stage_dist_le_frechet/frechet_controls_stage` | Definition/Theorem | ★ Cauchy/сходимость в проективном смысле |
| `proj_limit_elem/_converges/stage_convergence_downward/compat_limit_from_above/proj_shrinks_distance/frechet_bounds_stages/_tail_vanishes/agree_term_zero/agree_up_to_N_close` | Theorem | ★ предельный элемент сходится постадийно |
| `ProjContraction/pc_iterate/_contract/_compat/_commute/_elem/_stagewise_cauchy/proj_banach_principle/proj_fixed_unique` | Definition/Theorem | ★ Банах на проективной системе |
| `Q_is_metric_proj_sys/QVec_tower_is_metric_proj_sys/P4_limit_as_process/cauchy_seq_in_const_tower` | Theorem | Q/QVec как инстансы; P4-предел=процесс |

**Key lemmas (deep):**

- **`proj_banach_principle`** - Принцип Банаха ДОКАЗАН на проективной системе: проективное сжатие имеет единственную неподвижную точку, построенную как Cauchy-процесс совместимых стадий. Переносит теорию неподвижной точки в процессную онтологию (ср. FixedPoint.v, RH=fixed-point в zeta/). _(banach, fixed-point, projective, process)_
- **`P4_limit_as_process`** - Проективный предел ЕСТЬ процесс: Fréchet-метрика контролирует стадии (frechet_controls_stage), предельный элемент сходится сверху без завершённого предела. Математическое ядро вены C — формальная замена «предел-объект» на «совместимый процесс». _(projective-limit, process, frechet, vein-C)_

**Uniqueness - score 3 (new-framing).** Проективный предел над Q: Fréchet-метрика как настоящая метрика, постадийная сходимость, принцип Банаха на самой проективной системе — формальное ядро вены C (предел=процесс).
> _Caveat:_ Обратные пределы метрических/фреше-систем и Банах на них классичны; вклад — явное Q-построение как процессная онтология, не новая теория пределов.

---

## #1044 - `src/projective/ProjectiveStrengthened.v` - score 2 (methods)

**Projective system, strengthened: finite-stage elements, commutators, unbounded spectra**

- **Topic.** Strengthening lemmas: the constant Q-system projection is identity, P4 projective elements are finite at each stage and compatible, constant processes are projective elements, the self-commutator is zero, position spectrum is unbounded with growing eigenvalues, and norm-boundedness at stages.
- **Role.** Auxiliary strengthening leaf for the projective branch. Self-contained (QArith). June 2026 wave-4 tail: position_eigenvalues_grow was the vacuous exists lambda == inject_Z n (never stated growth) -> strict monotone growth inject_Z n < inject_Z (S n).
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ проективные элементы (конечны на стадии); постоянные процессы. _Roles:_ усиливающие леммы — роль-поддержка системы. _Rules:_ P4_projective_element_finite_at_stage; commutator_self_is_zero; position_spectrum_unbounded. _P4:_ проективный элемент конечен на каждой стадии (Element); неограниченный спектр позиции — role-limit.
- **Classical counterpart.** Strengthened/auxiliary projective-system lemmas; standard once ProjectiveSystem/ProjectiveLimit are in place.
- **Tags.** projective, P4, strengthening, methods

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `Q_const_sys_projection/const_sys_proj_id` | Definition/Theorem | проекция постоянной системы = id |
| `P4_projective_element_finite_at_stage/_compatibility/const_process_is_proj_elem` | Theorem | ★ проективный элемент конечен на стадии |
| `commutator_self_is_zero/_structural` | Theorem | [a,a]=0, структура |
| `position_spectrum_unbounded/position_eigenvalues_grow` | Theorem | ★ спектр позиции неограничен |
| `is_norm_bounded/norm_sq_nonneg_at/zero_norm_at/eigenstate_at_stage/projective_strengthened_synthesis` | Definition/Theorem | ограниченность нормы, итог |

**Key lemmas (deep):**

- **`P4_projective_element_finite_at_stage`** - Усиление: каждый проективный (P4) элемент конечен на любой стадии и совместим между стадиями — формальная гарантия, что вена C никогда не требует завершённого бесконечного объекта. _(P4, finite-stage, projective)_

**Uniqueness - score 2 (methods).** Усиливающие леммы проективной системы: конечность элементов на стадии, [a,a]=0, неограниченный спектр позиции как role-limit.
> _Caveat:_ Вспомогательные леммы поверх ProjectiveSystem/ProjectiveLimit; стандартны при наличии базовой конструкции.

---

## #1045 - `src/projective/ProjectiveSystem.v` - score 3 (new-framing)

**The projective system as a category over Q: objects, morphisms, products, towers; P4 principle**

- **Topic.** Projective systems and elements with a setoid equality, observe_at, projective morphisms with identity/composition/associativity, constant/trivial/product/shift systems, the Q-tower and Cauchy-as-projective-element, truncations, an InfVec type with stable nth, interval/level towers as projective, fixed points as projective elements, and the P4_projective_principle.
- **Role.** Root/definitional file of the projective branch (vein C); every other projective file builds on it. Self-contained (QArith).
- **Counts.** Qed 41 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ проективные системы ProjSys; элементы ProjElem; морфизмы ProjMor. _Roles:_ категория проективных систем — роль-каркас; observe_at = наблюдение стадии. _Rules:_ proj_compose_assoc; product/shift системы; cauchy_is_proj_elem; P4_projective_principle. _P4:_ проективный элемент = совместимое семейство конечных стадий (Element-процесс); P4_projective_principle — формальное ядро онтологии процесса (вена C).
- **Classical counterpart.** The category of projective (inverse) systems with objects, morphisms, identity/composition/associativity, products, and the inverse limit is classical category theory; NEW is the explicit Q/QVec instantiation casting CauchyReal, the level tower, intervals and fixed points as projective elements (the P4 projective principle).
- **Tags.** projective-system, category, P4, vein-C, root, new-framing

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `ProjSys/ProjElem/proj_elem_eq/_refl/_sym/_trans/observe_at/ps_proj_iter/_compat/pe_compat_iter` | Definition/Lemma | проективные системы и элементы (сетоид) |
| `ProjMor/proj_id/proj_compose/proj_mor_eq/_refl/_sym/_trans/_compose_id_l/_id_r/_assoc/proj_mor_apply/_elem_compat/_compose_apply/_id_apply` | Definition/Theorem | ★ морфизмы: категориальные законы |
| `const_sys/const_elem/_all_eq/_eq/trivial_sys/trivial_elem/process_is_trivial_elem` | Definition/Theorem | постоянная/тривиальная системы |
| `prod_sys/prod_elem/prod_fst/_snd/_fst_elem/_snd_elem/shift_sys/shift_elem_observation` | Definition/Theorem | произведение и сдвиг систем |
| `Q_tower/Q_const_elem/cauchy_is_proj_elem/cauchy_first_term_elem/firstn_length_eq/nth_firstn_eq/qvec_truncate/_nth/_compat/nth_map2_Qplus/qv_add_nth_eq` | Definition/Theorem | ★ Q-башня, Cauchy как проективный элемент |
| `QVec_tower/InfVec/infvec_nth/_stable/_eq_iff_nth/_zero/_zero_nth/_add/_add_nth/qv_scale_nth_eq/infvec_scale/_scale_nth` | Definition/Theorem | башня QVec, бесконечные векторы |
| `interval_sys/level_tower_is_projective/intervals_are_projective/endo_sys/fixed_point_is_proj_elem/observation_coherent/mor_observation_commute/prod_observe/P4_projective_principle` | Definition/Theorem | ★ уровни/интервалы/неподвижные точки как проективные; P4-принцип |

**Key lemmas (deep):**

- **`P4_projective_principle`** - Корневой принцип ветви: P4-объект = проективный элемент = совместимое семейство конечных наблюдений observe_at. Даёт ToS-онтологии процесса формальную категориальную опору — обратный предел. Все остальные projective-файлы и связь с CauchyReal/Level/интервалами идут отсюда. _(P4, projective-principle, vein-C, root)_
- **`cauchy_is_proj_elem`** - Cauchy-последовательность (= вещественное число в ToS) ЕСТЬ проективный элемент Q-башни — конкретная привязка вены C (ℝ=процесс) к категории проективных систем. observe_at извлекает конечную стадию. _(cauchy, real, projective-element)_

**Uniqueness - score 3 (new-framing).** Категория проективных систем над Q (объекты/морфизмы/произведения/башни) с P4_projective_principle: P4-объект = проективный элемент. Корень вены C, формальная опора онтологии процесса.
> _Caveat:_ Категория обратных систем и обратный предел — классика теории категорий; вклад — Q-инстанцирование, кладущее CauchyReal/уровни/интервалы/неподвижные точки в одну проективную рамку, не новая категорная теория.

---

## #1046 - `src/projective/QuantumTower.v` - score 2 (methods)

**Quantum tower over Q: Hilbert space as a projective process with a capped metric**

- **Topic.** A capped truncation distance on QVec (a metric: nonneg, sym, triangle, bounded), infinite vectors with stable nth, tower inner products and norms, normalizability, tower Cauchy-Schwarz, tower quantum states and observables (self-adjoint), eigenstates, and that the QVec tower is a projective system.
- **Role.** Quantum-Hilbert leaf of the projective branch; uses ProjectiveSystem/Limit. Self-contained (QArith).
- **Counts.** Qed 35 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ QVec-башня; бесконечные векторы; усечения. _Roles:_ гильбертово пространство = роль-предел башни; наблюдаемая как self-adjoint роль. _Rules:_ capped_QVec_dist (метрика); tower_cauchy_schwarz; qvec_tower_is_proj_sys. _P4:_ каждое усечение конечномерно (Element); гильбертово пространство — проективный процесс (role-limit); нормируемость постадийно.
- **Classical counterpart.** Hilbert space as a completion/inverse limit of finite-dimensional spaces, with Cauchy-Schwarz and self-adjoint observables, is standard; NEW only as the explicit Q 'tower' with a capped truncation metric making the QM Hilbert space a projective process.
- **Tags.** hilbert, tower, projective, quantum, methods

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `firstn_length_le/qvec_trunc/_nth/capped_QVec_dist/_nonneg/_sym/_bounded/_zero_refl/qmin1_triangle/_triangle/list_max_dist_firstn_le/trunc_nonexpand/_compat_eq` | Definition/Theorem | ★ усечённая метрика (метрические аксиомы) |
| `InfVec/iv_nth/_stable/iv_zero/iv_eq/_refl/_sym/_trans` | Definition/Lemma | бесконечные векторы (сетоид) |
| `tower_ip_at/tower_norm_sq_at/_sym/_nonneg/_zero/is_normalizable/zero_is_normalizable/norm_sq_seq_nonneg` | Definition/Theorem | скалярное произведение и норма башни |
| `tower_cauchy_schwarz/Qsq_abs/Qabs_le_sq_plus_1/tower_ip_bounded` | Theorem | ★ Коши-Шварц башни |
| `TowerQState/tqs_ip_at/_bounded/tqs_equiv/_refl/_sym/_trans` | Definition/Lemma | состояния башни |
| `TowerObservable/tobs_action_at/is_tower_eigenstate/tobs_self_adjoint_observation/qvec_tower_is_proj_sys/normalizable_sub_system/dim1_tower_is_cauchy/tqs_zero/_zero_ip/zero_eigenstate_observation/eigen_norm_sq_observation` | Definition/Theorem | ★ наблюдаемые, башня=проективная система |

**Key lemmas (deep):**

- **`qvec_tower_is_proj_sys`** - Гильбертово пространство КМ построено как проективная башня конечномерных Q-пространств — capped_QVec_dist даёт метрику, tower_cauchy_schwarz и self-adjoint наблюдаемые живут постадийно. Конкретизация вены C для квантовой механики: бесконечномерность — role-limit, не завершённый объект. _(hilbert, tower, projective, vein-C)_
- **`tower_cauchy_schwarz`** - Неравенство Коши-Шварца доказано на башне (для нормируемых элементов) — обеспечивает корректность скалярного произведения в проективном пределе без обращения к завершённому бесконечномерному пространству. _(cauchy-schwarz, inner-product, tower)_

**Uniqueness - score 2 (methods).** Гильбертово пространство КМ как проективная Q-башня: усечённая метрика, Коши-Шварц и self-adjoint наблюдаемые постадийно, башня — проективная система.
> _Caveat:_ Гильбертово пространство как пополнение/предел конечномерных стандартно; вклад — явная Q-башня с усечённой метрикой как процесс, не новая функан-конструкция.

