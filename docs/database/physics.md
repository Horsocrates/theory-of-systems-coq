# Database - cluster `physics`

_Generated from `physics.json` by `generate.ps1` - do not edit by hand; edit the JSON._

**29 files / 556 Qed.** Score distribution: s5=0 / s4=0 / s3=0 / s2=6 / s1=23 / s0=0

---

## #657 - `src/physics/AlphaBareLattice.v` - score 1 (exposition)

**Bare lattice alpha over Q**

- **Topic.** Cayley re/im eigenvalue lists, weighted averages, beta/alpha at N=2,3, alpha decreasing, unitarity, bounds.
- **Role.** Lattice physics (bare alpha). Self-contained.
- **Counts.** Qed 26 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ Cayley-собственные значения; alpha. _Roles:_ тонкая структура из решётки как роль. _Rules:_ weighted_avg; alpha_decreasing; unitarity. _P4:_ alpha точна над Q (Element).
- **Classical counterpart.** A bare lattice fine-structure alpha from Cayley eigenvalue averages is a modelling choice; NEW: nothing — exact Q alpha (decreasing, positive, bounded) at N=2,3.
- **Tags.** physics, alpha, lattice, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `cayley_re/im weighted_avg beta_Z3 alpha_Z3 alpha_decreasing unitarity_N2/N3 alpha_bound alpha_bare_lattice_synthesis` | Definition/Lemma | alpha из Cayley-спектра, убывание, унитарность |

**Key lemmas (deep):**

- **`alpha_decreasing`** - Решёточная alpha убывает с измельчением (Cayley-спектр) над Q; унитарность сохранена. Element-сторона, эвристическая модель. _(alpha, cayley, lattice)_

**Uniqueness - score 1 (exposition).** Решёточная alpha над Q (Cayley-спектр, убывание, унитарность).
> _Caveat:_ Моделирование; ценность — Q-точность.

---

## #658 - `src/physics/BetaFunctionLattice.v` - score 1 (exposition)

**Lattice beta function over Q: alpha_inv running**

- **Topic.** alpha_inv at N=2,3,4, deltas small, Cauchy convergence, alpha_inv tree, SM b1, RG at K=14.
- **Role.** Lattice RG (beta/alpha_inv). Self-contained.
- **Counts.** Qed 15 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ alpha_inv при N=2,3,4. _Roles:_ beta-функция как роль RG. _Rules:_ delta small; cauchy; b1_SM. _P4:_ alpha_inv сходится как Cauchy над Q (Element).
- **Classical counterpart.** alpha_inv running at N=2,3,4 (Cauchy convergence, SM b1) is standard RG; NEW: nothing — exact Q alpha_inv with small deltas (Cauchy).
- **Tags.** physics, RG, beta-function, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `alpha_inv_N2/N3/N4 delta_23/34 cauchy_23/34 alpha_inv_tree b1_SM rg_at_K14 beta_function_lattice_synthesis` | Definition/Lemma | alpha_inv бег, Cauchy, b1 |

**Key lemmas (deep):**

- **`cauchy_34`** - alpha_inv при N=2,3,4 сходится (малые delta, Cauchy) над Q к SM-значению b1. Element-сторона RG как процесса. _(beta-function, alpha-inv, cauchy)_

**Uniqueness - score 1 (exposition).** Решёточная beta-функция над Q (alpha_inv сходится Cauchy, b1_SM).
> _Caveat:_ RG-бег стандартен; ценность — Q-сходимость.

---

## #659 - `src/physics/BornRule.v` - score 1 (exposition)

**Born rule over Q: probabilities and expectations**

- **Topic.** born_prob (nonneg, Cauchy-Schwarz, symmetric, orthogonal), Born expectation, identity/diagonal expectations.
- **Role.** Quantum physics (Born rule). Self-contained.
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ амплитуды; Born-вероятности. _Roles:_ Born-правило как роль (\|amp\|²). _Rules:_ born_nonneg; born_cauchy_schwarz; born_expectation. _P4:_ Born-вероятности точны над Q (Element).
- **Classical counterpart.** The Born rule (\|amplitude\|^2, nonneg, Cauchy-Schwarz, orthogonality) and expectation are standard QM; NEW: nothing — exact Q Born probabilities and expectations.
- **Tags.** physics, born-rule, quantum, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `born_prob born_nonneg born_cauchy_schwarz born_orthogonal born_expectation expectation_diag_basis` | Definition/Lemma | Born-вероятность, ожидание |

**Key lemmas (deep):**

- **`born_cauchy_schwarz`** - Born-вероятности ограничены через Коши-Шварц (≤1) над Q; ортогональные состояния дают 0. Element-сторона QM над точной арифметикой. _(born-rule, cauchy-schwarz, probability)_

**Uniqueness - score 1 (exposition).** Born-правило над Q (вероятности нонотр./CS-ограничены, ожидания).
> _Caveat:_ Born-правило классично; ценность — Q-точность.

---

## #660 - `src/physics/BornRuleFromUnitarity.v` - score 2 (methods)

**Born exponent = 2 from unitarity over Q (uniqueness)**

- **Topic.** The p=2 Born rule, p=1 exceeding one (not normalized), p=4 below one, on Z3 too, and born_rule_unique_exponent.
- **Role.** Quantum physics (Born exponent uniqueness). Self-contained.
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ Born-показатель p; нормировка. _Roles:_ единственность показателя 2 как роль. _Rules:_ p1_exceeds_one; p4_below_one; born_rule_unique_exponent. _P4:_ ★ показатель Born = 2 ЕДИНСТВЕН (p≠2 нарушает нормировку) над Q (Element) — аргумент типа Глисона.
- **Classical counterpart.** That the Born EXPONENT is 2 (p1 fails: exceeds 1; p4 fails: below 1) — a Gleason/unitarity-flavoured uniqueness argument — is a known result; NEW: only the constructive Q demonstration that exponents != 2 violate normalization.
- **Tags.** physics, born-rule, exponent, methods

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `born_rule_p2 not_born_p1 p1_exceeds_one not_born_p4 p4_below_one born_rule_Z3 born_rule_unique_exponent` | Definition/Lemma | ★ показатель 2 единствен (p1/p4 нарушают нормировку) |

**Key lemmas (deep):**

- **`born_rule_unique_exponent`** - Показатель Born = 2 ЕДИНСТВЕН над Q: p=1 даёт сумму вероятностей > 1, p=4 < 1, только p=2 нормирует. Конструктивный Глисон-подобный аргумент единственности (нормировка ⟹ exponent 2). Element-сторона; честно — для конкретных состояний. _(born-rule, exponent-uniqueness, unitarity)_

**Uniqueness - score 2 (methods).** Единственность показателя Born = 2 над Q (p1 превышает 1, p4 ниже 1, только p2 нормирует).
> _Caveat:_ Единственность Born-показателя (Глисон-флейвор) известна; вклад — конструктивная Q-демонстрация на состояниях, не общий Глисон.

---

## #661 - `src/physics/CausalStructure.v` - score 1 (exposition)

**Causal structure from a distinction graph**

- **Topic.** CausalGraph, is_ancestor/causal_depth, spacelike pairs, concrete causal/spacelike examples, ancestor reflexive.
- **Role.** Physics (emergent causality). Self-contained.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib
- **E/R/R.** _Elements:_ причинный граф; события. _Roles:_ причинность как роль из distinction. _Rules:_ is_ancestor; is_spacelike; causal_depth. _P4:_ причинная структура конечно-проверяема (Element).
- **Classical counterpart.** A causal graph (ancestor/depth, spacelike) over events is standard causal-set modelling; NEW: nothing — exact causal relations from a distinction graph.
- **Tags.** physics, causality, graph, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `CausalGraph is_ancestor causal_depth is_spacelike events_spacelike depth_1/2/3 ancestor_refl causal_structure_synthesis` | Definition/Lemma | причинность, глубина, spacelike |

**Key lemmas (deep):**

- **`events_1_2_spacelike`** - Причинная структура (ancestor/spacelike/depth) выведена из distinction-графа над событиями. Element-сторона: причинность как граф (causal-set-аромат). _(causality, graph, spacelike)_

**Uniqueness - score 1 (exposition).** Причинная структура из distinction-графа (ancestor/spacelike/depth).
> _Caveat:_ Causal-set моделирование; ценность — связь с distinction.

---

## #662 - `src/physics/Decoherence.v` - score 2 (new-framing)

**Decoherence as a monotone process over Q**

- **Topic.** Binary-string state trees, decohere steps (monotone, no spontaneous coherence), the decoherence kernel surviving, fully/partially decohered dichotomy, surviving-nodes bounds.
- **Role.** Quantum physics (decoherence process). Self-contained.
- **Counts.** Qed 25 / Admitted 0 / axioms 0
- **Imports.** Stdlib
- **E/R/R.** _Elements:_ деревья состояний; шаги декогеренции. _Roles:_ декогеренция как монотонный процесс; дихотомия. _Rules:_ no_spontaneous_coherence; decohere_steps_monotone; decoherence_dichotomy. _P4:_ декогеренция как МОНОТОННЫЙ процесс (Element-стадии); нет спонтанной когерентности.
- **Classical counterpart.** Decoherence as a monotone process toward a pointer basis (no spontaneous re-coherence, kernel survives) is standard; NEW is only the P4/dichotomy framing: decoherence as a monotone tree process with a fully/partially-decohered dichotomy.
- **Tags.** physics, decoherence, process, P4, new-framing

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `state_tree decohere_step/steps decohere_steps_monotone no_spontaneous_coherence decoherence_kernel kernel_survives_all decoherence_dichotomy surviving_bounded` | Definition/Lemma | декогеренция-процесс, ядро, дихотомия |

**Key lemmas (deep):**

- **`no_spontaneous_coherence`** - Декогеренция монотонна: нет спонтанного восстановления когерентности, ядро выживает все шаги над Q. P4: декогеренция как необратимый процесс (стрелка); дихотомия полностью/частично-декогерентно. _(decoherence, monotone, irreversible, P4)_

**Uniqueness - score 2 (new-framing).** Декогеренция как монотонный необратимый процесс над Q (нет спонтанной когерентности, дихотомия полностью/частично).
> _Caveat:_ Декогеренция классична; ново — P4/процесс-обрамление с дихотомией.

---

## #663 - `src/physics/EnergyDeterminesGraph.v` - score 1 (exposition)

**Energy determines the graph: mass slows propagation**

- **Topic.** Enhanced degree, propagation time, flat vs curved (mass) propagation, mass slows propagation, dilation ratio > 1.
- **Role.** Physics (energy↔graph). Self-contained.
- **Counts.** Qed 15 / Admitted 0 / axioms 0
- **Imports.** Stdlib
- **E/R/R.** _Elements:_ граф; степень-усиление; время распространения. _Roles:_ масса замедляет распространение (аналогия дилатации). _Rules:_ mass_slows_propagation; dilation_ratio_gt_1. _P4:_ времена распространения точны на графе (Element).
- **Classical counterpart.** Mass/energy slowing propagation (gravitational time dilation flavour) on a graph is a modelling analogy; NEW: nothing — exact propagation times from graph-degree enhancement.
- **Tags.** physics, dilation, graph, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `enhanced_degree propagation_time mass_degree mass_slows_propagation propagation_curved dilation_ratio_gt_1 zero_mass_flat` | Definition/Lemma | масса замедляет распространение, дилатация |

**Key lemmas (deep):**

- **`mass_slows_propagation`** - Масса (степень-усиление графа) замедляет распространение, дилатация > 1 над Q — графовая аналогия гравитационной дилатации. Element-сторона, эвристика. _(dilation, graph, mass)_

**Uniqueness - score 1 (exposition).** Энергия определяет граф: масса замедляет распространение (дилатация > 1) над Q.
> _Caveat:_ Графовая аналогия дилатации; ценность — связь с distinction.

---

## #664 - `src/physics/Entanglement.v` - score 2 (new-framing)

**Entanglement over Q: separable/entangled dichotomy**

- **Topic.** Tensor states, separable/entangled, the Bell state entangled, entangled/separable collections bp-closed, the entanglement dichotomy (empty/discrete/continuum), 2-qubit has entangled.
- **Role.** Quantum info (entanglement). Self-contained.
- **Counts.** Qed 21 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ тензорные состояния; Bell. _Roles:_ запутанность/сепарабельность как дихотомия. _Rules:_ bell_entangled; entanglement_dichotomy; bp_closed. _P4:_ запутанность дихотомична (сепарабельно/запутано) над Q; коллекции bp-замкнуты (Element).
- **Classical counterpart.** Separable vs entangled states (Bell state entangled, Schmidt/rank witness) and a dichotomy are standard QI; NEW is only the dichotomy/structural framing: entangled collection bp-closed, empty/discrete/continuum classification.
- **Tags.** physics, entanglement, dichotomy, quantum-info, new-framing

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `state_tensor is_separable/entangled bell_state bell_entangled entangled_collection entanglement_dichotomy two_qubit_has_entangled` | Definition/Lemma | запутанность, Bell, дихотомия |

**Key lemmas (deep):**

- **`bell_entangled`** - Bell-состояние запутано (не тензорно-сепарабельно) над Q; коллекции сепарабельных/запутанных bp-замкнуты, дихотомия пусто/дискретно/континуум (как PCH). Element/вена C-аромат в QI. _(entanglement, bell, dichotomy)_

**Uniqueness - score 2 (new-framing).** Запутанность над Q как дихотомия сепарабельно/запутано (Bell запутан, коллекции bp-замкнуты, классификация пусто/дискретно/континуум).
> _Caveat:_ Запутанность/Bell классичны; ново — процессная дихотомия (связь с PCH).

---

## #665 - `src/physics/FineStructureProcess.v` - score 1 (exposition)

**Fine-structure process over Q: alpha_inv bracketed**

- **Topic.** alpha_inv process (monotone, increasing), alpha at K0..K14, bracket around the observed value, rg step positive.
- **Role.** Physics (fine-structure process). Self-contained.
- **Counts.** Qed 15 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ alpha_inv процесс; RG-шаг. _Roles:_ тонкая структура как процесс. _Rules:_ alpha_monotone; alpha_bracket. _P4:_ alpha_inv как монотонный процесс, зажимающий наблюдение (Element).
- **Classical counterpart.** alpha_inv running as a process (monotone, bracketed near 137) is standard RG; NEW: only the P4 framing: fine-structure as a monotone Cauchy process bracketing the observed value.
- **Tags.** physics, fine-structure, process, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `alpha_inv_process alpha_K0/K14 alpha_monotone alpha_bracket rg_step alpha_strictly_increasing` | Definition/Lemma | alpha_inv процесс, зажатие наблюдения |

**Key lemmas (deep):**

- **`alpha_bracket`** - alpha_inv как монотонный процесс зажимает наблюдаемое ~137 над Q. P4: тонкая структура как процесс, не фиксированное число. Честно — зажатие, не точный вывод. _(fine-structure, process, bracket)_

**Uniqueness - score 1 (exposition).** Тонкая структура как монотонный процесс над Q (alpha_inv зажимает наблюдение).
> _Caveat:_ RG-бег классичен; P4-обрамление, зажатие не вывод.

---

## #666 - `src/physics/FineStructureSynthesis.v` - score 1 (exposition)

**Fine-structure synthesis over Q (GUT couplings)**

- **Topic.** Tree sin^2, b1/b2/b3, alpha_inv at GUT, coupling hierarchy, our prediction vs standard, Weinberg accuracy.
- **Role.** Physics (fine-structure synthesis). Self-contained.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ GUT-связи b1/b2/b3. _Roles:_ синтез тонкой структуры как роль. _Rules:_ alpha_inv_gut; coupling_hierarchy; weinberg_accuracy. _P4:_ GUT-связи точны над Q (Element); честное сравнение.
- **Classical counterpart.** GUT-scale coupling unification (b1/b2/b3, alpha_inv_gut) compared to data is standard; NEW: nothing — exact Q couplings with honest comparison (our prediction vs standard).
- **Tags.** physics, fine-structure, GUT, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `b1/b2/b3 alpha_inv_gut alpha1/2/3_inv coupling_hierarchy our_prediction_superior weinberg_accuracy fine_structure_synthesis` | Definition/Lemma | GUT-связи, иерархия, точность |

**Key lemmas (deep):**

- **`coupling_hierarchy`** - Иерархия связей b1/b2/b3 к GUT-масштабу над Q точно; сравнение с наблюдением. Element-сторона RG-унификации, эвристика. _(GUT, coupling, hierarchy)_

**Uniqueness - score 1 (exposition).** Синтез тонкой структуры над Q (GUT-связи b1/b2/b3, иерархия, Weinberg-точность).
> _Caveat:_ RG-унификация стандартна; ценность — Q-сравнение.

---

## #667 - `src/physics/GraphCurvature.v` - score 1 (exposition)

**Graph curvature over Q: Forman curvature**

- **Topic.** Degree, common neighbors, Forman curvature; chain flat, K4 positive, triangle positive, star negative.
- **Role.** Physics/geometry (graph curvature). Self-contained.
- **Counts.** Qed 15 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ граф; кривизна Формана. _Roles:_ кривизна как роль (положит./отриц.). _Rules:_ k4_positive; star_negative; chain_flat. _P4:_ кривизна Формана точна над Q (Element).
- **Classical counterpart.** Forman/Ollivier-style combinatorial curvature on a graph (positive for cliques, negative for stars, flat for chains) is standard discrete geometry; NEW: nothing — exact Q Forman curvature for K4/triangle/star/chain.
- **Tags.** physics, curvature, graph, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `degree common_neighbors forman_curvature chain_flat k4_curvature/positive tri_positive star_curvature/negative` | Definition/Lemma | кривизна Формана: клика+, звезда−, цепь плоская |

**Key lemmas (deep):**

- **`star_negative`** - Кривизна Формана: клика K4 положительна, звезда отрицательна, цепь плоская над Q — дискретная кривизна из distinction-графа. Element-сторона (как DiscreteGaussBonnet). _(curvature, forman, graph)_

**Uniqueness - score 1 (exposition).** Кривизна Формана над Q (клика+, звезда−, цепь плоская).
> _Caveat:_ Комбинаторная кривизна стандартна; ценность — связь с distinction-графом.

---

## #668 - `src/physics/HarmonicOscillator.v` - score 1 (exposition)

**Harmonic oscillator over Q: discrete spectrum, zero-point energy**

- **Topic.** HO energies/eigenvalues (positive, increasing, equispaced), ground minimum, normalization/orthogonality, superposition expectations and probabilities, zero-point energy, quantized energy.
- **Role.** Quantum physics (HO). Self-contained.
- **Counts.** Qed 35 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ HO-энергии/состояния. _Roles:_ осциллятор как роль (дискретный спектр). _Rules:_ ho_level_spacing; ho_zero_point_energy; ho_energy_quantized. _P4:_ HO-спектр дискретен и точен над Q (Element).
- **Classical counterpart.** The quantum harmonic oscillator (discrete equispaced spectrum, ground state, zero-point energy, superposition expectations) is textbook QM; NEW: nothing — exact Q HO spectrum and Born expectations.
- **Tags.** physics, harmonic-oscillator, quantum, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `ho_energy ho_eigenvals ho_E0..E3 ho_level_spacing ho_energy_increasing ho_ground_minimum ho_normalization ho_orthogonality ho_zero_point_energy ho_energy_quantized` | Definition/Lemma | HO дискретный спектр, нулевая энергия |

**Key lemmas (deep):**

- **`ho_energy_quantized`** - HO-спектр дискретен, равноотстоящий (level_spacing), с нулевой энергией над Q точно. Element-сторона: квантование как конечно-проверяемая дискретность спектра. _(harmonic-oscillator, discrete-spectrum, zero-point)_

**Uniqueness - score 1 (exposition).** Гармонический осциллятор над Q (дискретный равноотстоящий спектр, нулевая энергия, ожидания).
> _Caveat:_ HO — учебная QM; ценность — Q-точность.

---

## #669 - `src/physics/InnerProductSpace.v` - score 1 (exposition)

**Inner product space over Q (quantum scaffolding)**

- **Topic.** Q-vector inner product (bilinear, scale/add laws), norm_sq, Cauchy-Schwarz, triangle, the process inner product Cauchy.
- **Role.** Quantum physics foundation (inner product). Underlies QState/QObservable. Self-contained.
- **Counts.** Qed 36 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ Q-векторы; скалярное произведение. _Roles:_ гильбертова структура как роль. _Rules:_ dot bilinear; cauchy_schwarz; process_ip_cauchy. _P4:_ конечномерное скалярное произведение точно над Q; процессное — Cauchy (Element).
- **Classical counterpart.** A finite-dim inner-product space over Q (bilinearity, Cauchy-Schwarz, triangle, process inner product Cauchy) is standard; NEW: nothing — the Q Hilbert-space scaffolding for the quantum files.
- **Tags.** physics, inner-product, hilbert, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `dot_product_scale/add norm_sq cauchy_schwarz norm_sq_triangle process_ip process_ip_cauchy norm_sq_process_cauchy` | Definition/Lemma | билинейность, CS, процессное ск. произведение |

**Key lemmas (deep):**

- **`process_ip_cauchy`** - Процессное скалярное произведение (для бесконечномерных состояний) — Cauchy над Q, с CS и треугольным. Element-сторона: гильбертово пространство QM как процесс; основа QState/QObservable. _(inner-product, hilbert, cauchy)_

**Uniqueness - score 1 (exposition).** Скалярное произведение над Q (билинейность, CS, треугольное, процессное Cauchy) — каркас QM.
> _Caveat:_ Гильбертова структура стандартна; ценность — каркас для quantum-файлов.

---

## #670 - `src/physics/MeasurementProcess.v` - score 1 (exposition)

**Measurement process over Q**

- **Topic.** Measurement outcomes (valid, prob nonneg/Cauchy), post-measurement eigenstate, repeatability, the measurement dichotomy (finite outcomes discrete), basis measurement complete.
- **Role.** Quantum physics (measurement). Self-contained.
- **Counts.** Qed 19 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ исходы измерения; пост-измеренное состояние. _Roles:_ измерение как процесс; дихотомия исходов. _Rules:_ post_measurement_is_eigenstate; measurement_repeatability; measurement_dichotomy. _P4:_ измерение как процесс над Q; конечные исходы дискретны (Element).
- **Classical counterpart.** Quantum measurement (outcome probabilities, post-measurement eigenstate, repeatability, dichotomy) is standard QM; NEW is only the P4 framing: measurement as a process with finite-outcomes-discrete dichotomy.
- **Tags.** physics, measurement, process, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `outcome_prob post_measurement_is_eigenstate measurement_repeatability measurement_dichotomy finite_outcomes_discrete basis_measurement_complete` | Definition/Lemma | исходы, пост-измерение, повторяемость, дихотомия |

**Key lemmas (deep):**

- **`measurement_repeatability`** - Повторное измерение даёт тот же исход (пост-измеренное = собственное состояние) над Q; конечные исходы дискретны. P4: измерение как процесс с дискретной дихотомией исходов. _(measurement, repeatability, dichotomy)_

**Uniqueness - score 1 (exposition).** Измерение как процесс над Q (повторяемость, пост-измеренное собственное, дихотомия исходов).
> _Caveat:_ Квантовое измерение классично; P4-обрамление.

---

## #671 - `src/physics/MinkowskiFromDistinction.v` - score 1 (exposition)

**Minkowski signature from a distinction graph**

- **Topic.** Interval classification (timelike positive, spacelike negative, lightlike zero), the Minkowski sign, concrete examples.
- **Role.** Physics (emergent Minkowski). Self-contained.
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib
- **E/R/R.** _Elements:_ причинный граф; интервалы. _Roles:_ сигнатура Минковского как роль из distinction. _Rules:_ timelike_positive; spacelike_negative; lightlike_zero. _P4:_ сигнатура интервала из графа точна (Element).
- **Classical counterpart.** A Minkowski signature (timelike/spacelike/lightlike sign) emerging from a causal graph is causal-set modelling; NEW: nothing — exact interval classification from distinction.
- **Tags.** physics, minkowski, causal-graph, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `classify_interval minkowski_sign timelike_positive spacelike_negative lightlike_zero minkowski_from_distinction` | Definition/Lemma | классификация интервала, сигнатура |

**Key lemmas (deep):**

- **`minkowski_from_distinction`** - Сигнатура Минковского (±/0 интервала) выведена из причинного distinction-графа над событиями. Element-сторона: пространство-время из distinction (causal-set-аромат). _(minkowski, causal-graph, signature)_

**Uniqueness - score 1 (exposition).** Сигнатура Минковского из distinction-графа (timelike+/spacelike−/lightlike 0).
> _Caveat:_ Causal-set моделирование; ценность — связь с distinction.

---

## #672 - `src/physics/NewtonFromGraph.v` - score 1 (exposition)

**Newton from a graph: 1/r force over Q**

- **Topic.** Gravitational potential/force, force positive and decreasing, inverse-square approx, potential well negative.
- **Role.** Physics (emergent Newton). Self-contained.
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ граф; потенциал/сила. _Roles:_ ньютоновская сила как роль из графа. _Rules:_ force_decreases; inverse_square_approx. _P4:_ сила точна над Q (Element); аналогия 1/r.
- **Classical counterpart.** A 1/r gravitational potential/force (well, decreasing, inverse-square approx) from a graph is a modelling analogy; NEW: nothing — exact Q force values approximating inverse-square.
- **Tags.** physics, newton, graph, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `grav_potential grav_force force_decreases potential_well inverse_square_approx_10 newton_synthesis` | Definition/Lemma | потенциал/сила, обратный квадрат |

**Key lemmas (deep):**

- **`inverse_square_approx_10`** - Сила из графа приближает закон обратного квадрата над Q; потенциальная яма отрицательна. Element-сторона, графовая аналогия Ньютона. _(newton, inverse-square, graph)_

**Uniqueness - score 1 (exposition).** Ньютоновская сила 1/r из графа над Q (убывает, обратный квадрат приближённо).
> _Caveat:_ Графовая аналогия; ценность — связь с distinction.

---

## #673 - `src/physics/ObserverStructure.v` - score 1 (exposition)

**Observer structure over a distinction graph**

- **Topic.** L5 observers, first appearance, two observers disagreeing on order but agreeing on a common event, first-appearance stable.
- **Role.** Physics (observer/L5). Self-contained.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib
- **E/R/R.** _Elements:_ наблюдатели (L5); первое появление. _Roles:_ наблюдатель как роль L5; относительный порядок. _Rules:_ O1_O2_disagree_on_order; agree_on_3. _P4:_ порядок наблюдателя-относителен (Element); согласие на общей точке.
- **Classical counterpart.** An L5 observer with a first-appearance order (observers disagreeing on order, agreeing on a common point) is ToS-specific modelling; NEW: only the ToS framing of observer-relative order.
- **Tags.** physics, observer, L5, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `Observer is_L5_observer first_appearance O1_O2_disagree_on_order O1_O2_agree_on_3 first_appearance_stable observer_structure_synthesis` | Definition/Lemma | L5-наблюдатели, относительный порядок |

**Key lemmas (deep):**

- **`O1_O2_disagree_on_order`** - Два L5-наблюдателя расходятся в порядке событий, но согласны на общей точке над distinction-графом. Element-сторона: относительность порядка из наблюдателя (L5). _(observer, L5, relative-order)_

**Uniqueness - score 1 (exposition).** Структура L5-наблюдателей (относительный порядок, согласие на общем) над distinction.
> _Caveat:_ ToS-моделирование наблюдателя; ценность — связь L5/относительность.

---

## #674 - `src/physics/Orthogonality.v` - score 1 (exposition)

**Orthogonality over Q: projection, Pythagoras, Bessel**

- **Topic.** Orthogonal/pairwise-orthogonal, projection and residual (orthogonal), Pythagoras, the projection norm decomposition, Bessel's inequality, a Gram-Schmidt step.
- **Role.** Quantum physics (orthogonality). Self-contained.
- **Counts.** Qed 27 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ Q-векторы; проекции/остатки. _Roles:_ ортогональность/проекция как роли. _Rules:_ residual_orthogonal; pythagorean_theorem; bessel_inequality. _P4:_ ортогонализация точна над Q (Element).
- **Classical counterpart.** Gram-Schmidt, projection/residual, Pythagoras, Bessel's inequality over an inner-product space are standard; NEW: nothing — exact Q Gram-Schmidt and Bessel.
- **Tags.** physics, orthogonality, bessel, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `orthogonal project residual residual_orthogonal pythagorean_theorem norm_sq_decomposition bessel_inequality gs_step gs_step_orthogonal` | Definition/Lemma | проекция, Пифагор, Бессель, Грам-Шмидт |

**Key lemmas (deep):**

- **`bessel_inequality`** - Неравенство Бесселя (сумма квадратов проекций ≤ норма²) над Q точно, с Пифагором и Грам-Шмидтом. Element-сторона гильбертовой геометрии QM. _(orthogonality, bessel, gram-schmidt)_

**Uniqueness - score 1 (exposition).** Ортогональность над Q (проекция/остаток, Пифагор, Бессель, Грам-Шмидт).
> _Caveat:_ Гильбертова геометрия стандартна; ценность — Q-точность.

---

## #675 - `src/physics/QObservable.v` - score 1 (exposition)

**Quantum observables over Q: symmetric matrices, eigenstates**

- **Topic.** Matrix-vector action, symmetric observables, the identity/diagonal observables, basis extraction, diagonal eigenstates, observable equivalence.
- **Role.** Quantum physics (observables). Self-contained.
- **Counts.** Qed 16 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ наблюдаемые QObservable; симметричные матрицы. _Roles:_ наблюдаемая как роль (самосопряжённая). _Rules:_ obs_symmetric; diag_eigenstate. _P4:_ наблюдаемые точны над Q (Element).
- **Classical counterpart.** Symmetric (self-adjoint) observables, identity/diagonal matrices, eigenstates of a diagonal observable, over an inner-product space, are standard; NEW: nothing — exact Q observables.
- **Tags.** physics, observable, quantum, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `QObservable obs_action obs_symmetric id_observable diag_observable is_eigenstate diag_eigenstate obs_equiv` | Definition/Lemma | симметричные наблюдаемые, собственные состояния |

**Key lemmas (deep):**

- **`diag_eigenstate`** - Диагональная наблюдаемая имеет базисные собственные состояния над Q; симметричность (самосопряжённость) проверена. Element-сторона: наблюдаемые QM над точной арифметикой. _(observable, self-adjoint, eigenstate)_

**Uniqueness - score 1 (exposition).** Квантовые наблюдаемые над Q (симметричные, собственные состояния диагональной).
> _Caveat:_ Наблюдаемые стандартны; ценность — Q-точность.

---

## #676 - `src/physics/QState.v` - score 1 (exposition)

**Quantum states over Q: basis, inner product, normalization**

- **Topic.** QState, basis vectors (orthogonal, normalized, distinct), state inner product (Cauchy, linear), Cauchy-Schwarz.
- **Role.** Quantum physics (states). Underlies Qubit/SpinChain. Self-contained.
- **Counts.** Qed 19 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ квантовые состояния QState; базис. _Roles:_ состояние как роль; базис ортонормирован. _Rules:_ basis_orthogonal; basis_state_normalized. _P4:_ состояния точны над Q (Element).
- **Classical counterpart.** Quantum states (basis vectors, inner product, orthonormality, normalization) over Q are standard; NEW: nothing — exact Q state scaffolding.
- **Tags.** physics, quantum-state, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `QState basis_vec basis_state basis_orthogonal basis_state_normalized state_ip state_cauchy_schwarz` | Definition/Lemma | состояния, ортонормированный базис |

**Key lemmas (deep):**

- **`basis_orthogonal`** - Базисные состояния ортогональны и нормированы над Q точно. Element-сторона: каркас состояний QM (для Qubit/SpinChain). _(quantum-state, basis, orthonormal)_

**Uniqueness - score 1 (exposition).** Квантовые состояния над Q (ортонормированный базис, скалярное произведение).
> _Caveat:_ Состояния стандартны; ценность — каркас.

---

## #677 - `src/physics/QuantumDynamics.v` - score 1 (exposition)

**Quantum dynamics over Q: norm-preserving evolution, conservation**

- **Topic.** Time evolution, static evolution preserving norm/expectation, eigenstate stationary, conserved quantities, transition probabilities symmetric.
- **Role.** Quantum physics (dynamics). Self-contained.
- **Counts.** Qed 24 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ эволюция во времени; состояния. _Roles:_ динамика как роль (сохранение нормы). _Rules:_ norm_preserving; eigenstate_stationary; conservation. _P4:_ эволюция сохраняет норму точно над Q (Element).
- **Classical counterpart.** Unitary (here static) time evolution preserving norm/expectation, eigenstate stationarity, conservation, transition probabilities, is standard; NEW: nothing — exact Q dynamics.
- **Tags.** physics, dynamics, quantum, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `TimeEvolution static_evolution is_norm_preserving eigenstate_stationary is_conserved hamiltonian_conserved transition_prob_at_time` | Definition/Lemma | сохранение нормы, стационарность, сохранение |

**Key lemmas (deep):**

- **`eigenstate_stationary`** - Собственные состояния стационарны (постоянное ожидание), эволюция сохраняет норму над Q. Element-сторона унитарной динамики QM. _(dynamics, stationary, conservation)_

**Uniqueness - score 1 (exposition).** Квантовая динамика над Q (сохранение нормы, стационарные собственные состояния, сохранение).
> _Caveat:_ Унитарная динамика стандартна; ценность — Q-точность.

---

## #678 - `src/physics/Qubit.v` - score 1 (exposition)

**Qubit over Q: Pauli operators, complementarity**

- **Topic.** Qubit states, Pauli Z/X (eigenvalues, eigenstates, symmetric), expectations, normalization, z-x complementarity, z-basis measurement complete.
- **Role.** Quantum physics (qubit). Self-contained.
- **Counts.** Qed 42 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ кубит; Паули X/Z. _Roles:_ кубит как роль (2-уровневая система). _Rules:_ pauli_z/x_eigenstate; complementarity_z_x. _P4:_ кубит-алгебра точна над Q (Element).
- **Classical counterpart.** The qubit (\|0>,\|1>,\|+>,\|->, Pauli X/Z, eigenstates, expectations, z-x complementarity) is textbook QM; NEW: nothing — exact Q qubit algebra.
- **Tags.** physics, qubit, pauli, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `qubit_0/1/plus/minus pauli_z/x pauli_z_eigenstate pauli_x_eigenstate_plus expectation_z complementarity_z_x z_basis_measurement_complete` | Definition/Lemma | кубит, Паули, дополнительность |

**Key lemmas (deep):**

- **`complementarity_z_x`** - Z-X дополнительность кубита (\|+> равновероятен в Z-базисе) над Q точно; Паули-собственные состояния. Element-сторона: кубит-алгебра над точной арифметикой. _(qubit, pauli, complementarity)_

**Uniqueness - score 1 (exposition).** Кубит над Q (Паули X/Z, собственные состояния, Z-X дополнительность).
> _Caveat:_ Кубит — учебная QM; ценность — Q-точность.

---

## #679 - `src/physics/RGConsistency.v` - score 1 (exposition)

**RG consistency over Q (tree Weinberg matches)**

- **Topic.** Tree sin^2/kappa/alpha_inv, b1 SM, alpha_inv running K0..K14, observed values bracketed, tree Weinberg error small.
- **Role.** Physics (RG consistency). Self-contained.
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ древесные значения; бег alpha_inv. _Roles:_ RG-согласованность как роль. _Rules:_ running brackets observed; tree_weinberg_error_small. _P4:_ древесные значения и бег точны над Q (Element).
- **Classical counterpart.** Checking tree-level Weinberg consistency against running couplings is standard; NEW: nothing — exact Q RG consistency (tree matches within small error).
- **Tags.** physics, RG, weinberg, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `tree_sin2 tree_alpha_inv b1_SM alpha_inv_running running_K13_lt_obs obs_lt_running_K14 tree_weinberg_matches tree_weinberg_error_small` | Definition/Lemma | RG-согласованность, зажатие наблюдения |

**Key lemmas (deep):**

- **`tree_weinberg_matches`** - Древесный Weinberg согласован с бегущим alpha_inv (наблюдение зажато K13<obs<K14) над Q, ошибка мала. Element-сторона RG-согласованности. _(RG, weinberg, consistency)_

**Uniqueness - score 1 (exposition).** RG-согласованность над Q (древесный Weinberg зажимает наблюдение, малая ошибка).
> _Caveat:_ RG-проверки стандартны; ценность — Q-точность.

---

## #680 - `src/physics/RunningCouplings.v` - score 1 (exposition)

**Running couplings over Q: U(1) grows, SU(2)/SU(3) asymptotically free**

- **Topic.** b1/b2/b3, alpha_inv at GUT, U(1) growing, SU(2)/SU(3) shrinking (asymptotic freedom), SU(3) faster, ordering at K=1.
- **Role.** Physics (running couplings). Self-contained.
- **Counts.** Qed 15 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ три связи SM; их бег. _Roles:_ бег связей как роль (AF). _Rules:_ U1_grows; SU2/SU3_AF; ordering_K1. _P4:_ бег трёх связей точен над Q (Element).
- **Classical counterpart.** The running of the three SM couplings (U(1) grows, SU(2)/SU(3) shrink, AF), and unification, is standard; NEW: nothing — exact Q coupling running with AF for SU(2)/SU(3).
- **Tags.** physics, running, asymptotic-freedom, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `b1/b2/b3 alpha_inv_gut U1_grows SU2_shrinks SU3_strong_AF asymptotic_freedom_SU3/SU2 ordering_K1 beta_sum` | Definition/Lemma | бег связей, асимптотическая свобода |

**Key lemmas (deep):**

- **`asymptotic_freedom_SU3`** - SU(3) асимптотически свободна (связь убывает с энергией, быстрее SU(2)), U(1) растёт над Q точно. Element-сторона RG SM. _(running, asymptotic-freedom, SM)_

**Uniqueness - score 1 (exposition).** Бег связей SM над Q (U(1) растёт, SU(2)/SU(3) асимпт. свободны, упорядочение).
> _Caveat:_ RG SM стандартен; ценность — Q-точность.

---

## #681 - `src/physics/SpectralDichotomy.v` - score 2 (new-framing)

**Spectral dichotomy over Q: discrete XOR continuous (honest: framing not theorem)**

- **Topic.** Eigenspaces, the spectral dichotomy (discrete enumerable / continuous perfect, no intermediate), discrete/continuous spectrum, finite-dim discrete, the full Cantor space perfect.
- **Role.** Quantum physics (spectral dichotomy, vein C/E). Reuses PCH dichotomy. Honestly framing-level (audit rejected over-claim).
- **Counts.** Qed 30 / Admitted 0 / axioms 0
- **Imports.** Stdlib; ProcessTypes-style dichotomy
- **E/R/R.** _Elements:_ собственные пространства; спектр. _Roles:_ спектр как дихотомия (дискретно/непрерывно). _Rules:_ spectral_dichotomy; no_intermediate_spectrum. _P4:_ спектр подчиняется ТОЙ ЖЕ дихотомии (счётно/совершенно), что PCH — дискретно XOR непрерывно (вена C/E).
- **Classical counterpart.** A spectrum being either discrete (enumerable eigenspace) or continuous (perfect/non-enumerable), with no intermediate, mirrors descriptive set theory; NEW is only the process-dichotomy framing (same as PCH) — but an Explore agent OVER-CLAIMED this as a novelty; per the audit it is a new-FRAMING, not a new theorem.
- **Tags.** physics, spectral-dichotomy, PCH, vein-C, new-framing
- **Notes.** Audit (project-uniqueness-map): an Explore agent over-claimed spectral_dichotomy as novelty; it is new-framing (PCH dichotomy), not a new theorem.

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `eigenspace spectral_dichotomy has_discrete/continuous_spectrum no_intermediate_spectrum discrete_spectrum_all_enum continuous_spectrum_witness finite_dim_discrete full_cantor_space_perfect` | Definition/Lemma | ★ дихотомия спектра (дискретно/непрерывно) |

**Key lemmas (deep):**

- **`spectral_dichotomy`** - Спектр либо ДИСКРЕТЕН (счётное собственное пространство), либо НЕПРЕРЫВЕН (совершенное/несчётное), без промежуточного — ТА ЖЕ структурная дихотомия, что ProcessContinuumHypothesis. Честно: это переобрамление PCH-дихотомии в спектральный язык (вена C/E), а НЕ новая теорема (audit отверг over-claim). _(spectral-dichotomy, discrete-continuous, PCH, vein-C)_

**Uniqueness - score 2 (new-framing).** Спектральная дихотомия над Q: спектр дискретен XOR непрерывен (совершенное подмножество), без промежуточного — спектральное переобрамление PCH (вена C/E).
> _Caveat:_ ★ Audit отверг over-claim: это new-FRAMING (= PCH-дихотомия в спектре), НЕ новая теорема. Дискретно/непрерывный спектр классичен.

---

## #682 - `src/physics/SpinChain.v` - score 1 (exposition)

**Spin chain over Q: Bell states, Ising spectrum**

- **Topic.** Spin states, Bell phi+/psi+ (entangled, orthogonal), the Ising Hamiltonian eigenvalues/eigenstates, Bell anticorrelation, antiferro/ferro ground, energy gap.
- **Role.** Quantum physics (spin chain). Self-contained.
- **Counts.** Qed 32 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ спиновая цепь; Bell-состояния; Изинг. _Roles:_ спин-цепь как роль; Bell-запутанность. _Rules:_ bell_entangled; ising_eigenvals; bell_anticorrelation. _P4:_ спин-спектр и Bell-состояния точны над Q (Element).
- **Classical counterpart.** A spin chain with Bell states, the Ising Hamiltonian spectrum, Bell anticorrelation, antiferro/ferro ground states, is standard QM/condensed matter; NEW: nothing — exact Q spin-chain spectrum and Bell states.
- **Tags.** physics, spin-chain, bell, ising, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `bell_phi_plus/psi_plus bell_entangled bell_states_orthogonal ising_eigenvals ising_hamiltonian bell_anticorrelation antiferro_ground ferro_ground ising_energy_gap` | Definition/Lemma | Bell, Изинг-спектр, антикорреляция |

**Key lemmas (deep):**

- **`bell_anticorrelation`** - Bell-состояния антикоррелированы, ортогональны, запутаны; Изинг-спектр с энергетической щелью над Q точно. Element-сторона спиновой цепи QM. _(spin-chain, bell, ising)_

**Uniqueness - score 1 (exposition).** Спиновая цепь над Q (Bell-состояния, Изинг-спектр, антикорреляция, основные состояния).
> _Caveat:_ Спин-цепь/Изинг стандартны; ценность — Q-точность.

---

## #683 - `src/physics/ThermodynamicArrow.v` - score 2 (new-framing)

**Thermodynamic arrow over Q: monotone disorder, second law**

- **Topic.** Process disorder (monotone, bounded, max at death), the time arrow (monotone), thermal equilibrium, the second law, full decoherence kills, equilibrium stable.
- **Role.** Physics (arrow of time). Self-contained.
- **Counts.** Qed 17 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ беспорядок процесса; стрелка времени. _Roles:_ стрелка как монотонный процесс; второй закон. _Rules:_ disorder_monotone; arrow_of_time; second_law. _P4:_ стрелка времени = МОНОТОННЫЙ рост беспорядка (Element-стадии); второй закон как монотонность.
- **Classical counterpart.** An arrow of time from monotone disorder (second law, full decoherence kills, equilibrium stable) on a graph is standard; NEW is only the P4 framing: the arrow as monotone process disorder, second-law as monotonicity.
- **Tags.** physics, arrow-of-time, second-law, P4, new-framing

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `process_disorder disorder_monotone disorder_max_at_death time_arrow arrow_monotone second_law full_decoherence_kills equilibrium_stable` | Definition/Lemma | монотонный беспорядок, второй закон |

**Key lemmas (deep):**

- **`second_law`** - Второй закон = монотонный рост беспорядка процесса над Q; полная декогеренция = «смерть» (макс. беспорядок), равновесие устойчиво. P4: стрелка времени как монотонный процесс. _(arrow-of-time, second-law, monotone)_

**Uniqueness - score 2 (new-framing).** Стрелка времени над Q как монотонный рост беспорядка (второй закон = монотонность, равновесие устойчиво).
> _Caveat:_ Второй закон/стрелка классичны; ново — P4/процесс-обрамление.

---

## #684 - `src/physics/TimeDilation.v` - score 2 (new-framing)

**Time dilation over Q via Pythagorean triples**

- **Topic.** Proper time squared, dilation factor, rest no dilation, lightspeed zero proper time, the 3-4-5 / 5-12-13 Pythagorean triples, Minkowski sign, dilation monotone.
- **Role.** Physics (time dilation). Self-contained.
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ собственное время; дилатация. _Roles:_ дилатация как роль (через пифагоровы тройки). _Rules:_ proper_time_sq; pythagorean_triple; dilation_monotone. _P4:_ дилатация через ТОЧНЫЕ пифагоровы тройки над Q (Element); rest=без дилатации.
- **Classical counterpart.** Time dilation from a Minkowski proper-time (Pythagorean 3-4-5, rest no dilation, lightspeed zero) is standard SR; NEW: only the constructive Q form using exact integer sqrt (Pythagorean triples).
- **Tags.** physics, time-dilation, pythagorean, SR, new-framing

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `proper_time_sq dilation_factor rest_no_dilation lightspeed_zero pythagorean_triple concrete_3_4_5 pythagorean_13_5_12 dilation_monotone` | Definition/Lemma | дилатация, пифагоровы тройки |

**Key lemmas (deep):**

- **`concrete_3_4_5`** - Дилатация времени через ТОЧНЫЕ пифагоровы тройки (3-4-5, 5-12-13) над Q — собственное время рационально на этих скоростях (sqrt точен). Element-сторона SR (связь с RationalLorentz/q-kinematics). _(time-dilation, pythagorean, SR)_

**Uniqueness - score 2 (new-framing).** Дилатация времени над Q через ТОЧНЫЕ пифагоровы тройки (3-4-5/5-12-13) — собственное время рационально на этих скоростях.
> _Caveat:_ Дилатация классична; ново — рациональные (пифагоровы) точки, связь с RationalLorentz.

---

## #685 - `src/physics/WeinbergAngleRunning.v` - score 1 (exposition)

**Weinberg angle running over Q (honest comparison)**

- **Topic.** Tree sin^2, observed sin^2, GUT-standard prediction, our prediction (closer), standard error large, our error smaller, match without running.
- **Role.** Physics (Weinberg running, honest). Self-contained.
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ sin2 древесный/наблюдаемый/GUT. _Roles:_ Weinberg-бег как роль (честное сравнение). _Rules:_ our_closer; standard_error_large; match_no_running. _P4:_ sin2 точен над Q; честно — наше ближе, но без бега.
- **Classical counterpart.** The Weinberg angle running vs the GUT/standard prediction is standard EW; NEW: nothing — exact Q sin^2 with an HONEST comparison (our closer than standard, but no running).
- **Tags.** physics, weinberg, honest, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `sin2_tree/observed/gut_standard our_prediction standard_off our_closer our_error_smaller match_no_running` | Definition/Lemma | sin2, честное сравнение с GUT |

**Key lemmas (deep):**

- **`our_closer`** - Наш древесный sin²θ_W ближе к наблюдению, чем стандартное GUT-предсказание, БЕЗ бега над Q — честное сравнение (но 3/13 над-брендирован per audit). Element-сторона. _(weinberg, honest, comparison)_

**Uniqueness - score 1 (exposition).** Weinberg-угол над Q с честным сравнением (наше ближе GUT-стандарта, без бега).
> _Caveat:_ Weinberg классичен/над-брендирован (3/13); ценность — честное Q-сравнение.

