# Database - cluster `lattice`

_Generated from `lattice.json` by `generate.ps1` - do not edit by hand; edit the JSON._

**29 files / 281 Qed.** Score distribution: s5=0 / s4=0 / s3=0 / s2=7 / s1=22 / s0=0

---

## #563 - `src/lattice/ActionFromTransfer.v` - score 1 (exposition)

**Lattice action from the transfer matrix (Boltzmann weights)**

- **Topic.** Transfer-matrix traces, partition functions Z, one-step weights shown positive (Boltzmann form), over Q.
- **Role.** Lattice QFT from distinction (transfer→action). Self-contained.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ transfer-матрица T; веса. _Roles:_ действие из transfer как роль. _Rules:_ trace_TK; partition Z; weight positive (Boltzmann). _P4:_ конечные точные Q-вычисления transfer/partition (Element).
- **Classical counterpart.** Recovering a lattice action from a transfer matrix (Boltzmann weights) is standard lattice QFT; NEW: nothing — exact Q transfer/partition computations.
- **Tags.** lattice, transfer-matrix, action, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `trace_TK U00..U11 partition_Z1/Z2 weight_one_step/positive T_is_boltzmann` | Definition/Lemma | следы transfer, partition, положительные веса |

**Key lemmas (deep):**

- **`T_is_boltzmann`** - Веса transfer-матрицы положительны (Больцмановская форма) над Q — действие восстановлено из transfer. Element-сторона: точное конечное вычисление. _(transfer-matrix, boltzmann, lattice)_

**Uniqueness - score 1 (exposition).** Действие из transfer-матрицы (Больцмановские веса) точно над Q.
> _Caveat:_ Стандартная решёточная QFT; ценность — точная Q-формализация.

---

## #564 - `src/lattice/BetaFromDecimation.v` - score 2 (methods)

**Beta function from block decimation over Q**

- **Topic.** RG decimation data, effective coupling, the one-step beta, coupling/mass decreasing, beta positive (asymptotic-freedom direction), linear extrapolation.
- **Role.** Lattice RG (beta from decimation). Self-contained.
- **Counts.** Qed 15 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ RG-данные; эффективная связь. _Roles:_ beta-функция как роль течения связи. _Rules:_ decimation; coupling_decreased; beta_positive. _P4:_ RG-течение как конечный процесс decimation (Element); связь убывает (асимпт. свобода).
- **Classical counterpart.** Extracting the RG beta function by block-spin decimation (coupling decreases under coarse-graining) is standard RG; NEW: nothing — exact Q decimation with a beta value and asymptotic-freedom sign.
- **Tags.** lattice, RG, beta-function, decimation, methods

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `RGData rg0/rg1 eff_coupling alpha_inv beta_1step coupling_decreased beta_value beta_positive linear_extrapolation beta_from_decimation_synthesis` | Definition/Lemma | RG-decimation, beta, убывание связи |

**Key lemmas (deep):**

- **`beta_from_decimation_synthesis`** - Beta-функция извлечена decimation'ом: связь убывает при огрублении (направление асимптотической свободы), beta>0, над Q точно. Element-сторона RG как процесса. _(RG, beta-function, decimation, asymptotic-freedom)_

**Uniqueness - score 2 (methods).** Beta-функция из block-decimation над Q (связь убывает, beta>0, экстраполяция).
> _Caveat:_ Block-spin RG классичен; вклад — точная Q-формализация течения.

---

## #565 - `src/lattice/BlockDecimation1D.v` - score 1 (exposition)

**1D block decimation: effective hopping and mass over Q**

- **Topic.** Effective 2x2 block matrices, coarse hopping/mass, hopping decreasing, mass positive, diagonal dominance across two decimation steps.
- **Role.** Lattice RG (1D decimation). Self-contained.
- **Counts.** Qed 15 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ блок-матрицы 2x2; эффективные hopping/mass. _Roles:_ decimation как роль огрубления. _Rules:_ hopping_decreased; mass_positive; diagonal_dominant. _P4:_ эффективные связи вычислены точно над Q (Element).
- **Classical counterpart.** 1D block-spin decimation (effective hopping/mass under coarse-graining) is standard real-space RG; NEW: nothing — exact Q effective couplings, diagonal dominance.
- **Tags.** lattice, decimation, RG, 1D, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `Mii_det Meff_00/01 hopping_coarse mass_eff hopping_decreased mass_positive diagonal_dominant block_decimation_synthesis` | Definition/Lemma | эффективные блок-связи, убывание hopping |

**Key lemmas (deep):**

- **`hopping_decreased`** - Эффективный hopping убывает при decimation (1D), масса положительна — реал-спейс RG над Q точно. Element-сторона. _(decimation, hopping, 1D)_

**Uniqueness - score 1 (exposition).** 1D block-decimation над Q (эффективные hopping/mass, diagonal dominance).
> _Caveat:_ Реал-спейс RG стандартен; ценность — Q-точность.

---

## #566 - `src/lattice/BlockDecimation3D.v` - score 1 (exposition)

**3D block decimation: high-mode sigma over Q**

- **Topic.** 3D Laplacian high modes, sigma_high (positive, small, < 1/4), effective 3D mass greater, coarse alpha.
- **Role.** Lattice RG (3D decimation). Self-contained.
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ 3D лапласиан высокие моды; sigma_high. _Roles:_ 3D decimation как роль. _Rules:_ sigma_high positive/small; m_eff_greater. _P4:_ 3D эффективные величины точны над Q (Element).
- **Classical counterpart.** 3D decimation with high-mode sigma and effective mass is standard RG; NEW: nothing — exact Q 3D block sigma bounds.
- **Tags.** lattice, decimation, 3D, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `lap3D_high sigma_high m_sq_eff_3D sigma_high_positive/small m_eff_3D_m1 m_eff_greater alpha_coarse block_decimation_3D_synthesis` | Definition/Lemma | 3D high-mode sigma, эффективная масса |

**Key lemmas (deep):**

- **`sigma_high_less_than_quarter`** - 3D high-mode sigma < 1/4 (мало, положительно) над Q — контролируемое огрубление. Element-сторона 3D RG. _(decimation, 3D, sigma)_

**Uniqueness - score 1 (exposition).** 3D block-decimation над Q (sigma_high < 1/4, эффективная масса).
> _Caveat:_ 3D RG стандартен; ценность — Q-точность.

---

## #567 - `src/lattice/CorrelationFunctions.v` - score 1 (exposition)

**Free-field correlation functions via Wick (over Q)**

- **Topic.** Wick 4-point as a sum over pairings (double factorial count), connected 4-point of a free field, Wick symmetry, cluster property.
- **Role.** Lattice QFT (correlations/Wick). Self-contained.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ n-точечные функции; парности (Wick). _Roles:_ Wick как роль свободного поля; кластер. _Rules:_ wick_4pt = сумма по парностям; cluster. _P4:_ Wick-корреляции точны над Q (Element).
- **Classical counterpart.** Free-field n-point functions via Wick's theorem (pairings, double factorial) and cluster decomposition are standard; NEW: nothing — exact Q Wick computations on small chains.
- **Tags.** lattice, wick, correlation, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `wick_4pt double_factorial num_pairings G_chain2 connected_4pt_free_field wick_is_cluster wick_symmetry correlation_synthesis` | Definition/Lemma | Wick-парности, связные корреляции, кластер |

**Key lemmas (deep):**

- **`connected_4pt_free_field`** - Связная 4-точечная функция свободного поля = 0 (Wick: только полные парности) над Q — стандартная теорема Вика, проверенная вычислением. Element-сторона. _(wick, correlation, free-field)_

**Uniqueness - score 1 (exposition).** Свободно-полевые корреляции через Wick (парности, кластер) точно над Q.
> _Caveat:_ Теорема Вика классична; ценность — Q-формализация.

---

## #568 - `src/lattice/CouplingRunning.v` - score 1 (exposition)

**Coupling running over Q**

- **Topic.** alpha running at two scales, beta per step, alpha_inv difference, extrapolation, running positive and decreasing.
- **Role.** Lattice RG (coupling running). Self-contained.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ бегущая связь alpha. _Roles:_ running как роль RG. _Rules:_ beta_per_step; running_decreasing. _P4:_ бег связи как конечный RG-процесс (Element).
- **Classical counterpart.** Running of a coupling (alpha decreasing/increasing under RG) is standard; NEW: nothing — exact Q running with positivity/monotonicity.
- **Tags.** lattice, RG, running, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `alpha_running_0/1 alpha_inv_0/1 beta_per_step coupling_ratio extrapolate_14 running_positive/decreasing coupling_running_synthesis` | Definition/Lemma | бегущая связь, beta, экстраполяция |

**Key lemmas (deep):**

- **`running_decreasing`** - Связь убывает при RG-беге (асимпт. свобода) над Q точно. Element-сторона RG. _(running, RG, coupling)_

**Uniqueness - score 1 (exposition).** Бег связи над Q (beta per step, убывание, экстраполяция).
> _Caveat:_ Running couplings классичны; ценность — Q-точность.

---

## #569 - `src/lattice/DeltaSynthesis.v` - score 2 (methods)

**Weinberg-angle correction delta (honest synthesis)**

- **Topic.** Tree sin^2, observed sin^2, the needed delta (exact, positive, with correct sign), tree accuracy, honest synthesis.
- **Role.** Lattice EW (Weinberg delta). Self-contained. Honestly framed.
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ sin2 tree/obs; нужная поправка delta. _Roles:_ delta как роль согласования с наблюдением. _Rules:_ delta_needed_exact; sign_correct; honest_synthesis. _P4:_ древесный sin2 и нужная delta точны над Q; honest_synthesis — честная пометка (не вывод 3/13).
- **Classical counterpart.** The Weinberg angle sin^2(theta_W) and the loop correction needed to match observation are standard EW physics; NEW: nothing — exact Q tree value + needed delta, HONESTLY flagged (the 3/13 result is proof-closure under assumed dims, over-branded per audit).
- **Tags.** lattice, weinberg-angle, honest, over-branded, methods

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `sin2_tree/obs delta_needed delta_needed_exact/positive tree_accuracy sign_correct chain_complete honest_synthesis` | Definition/Lemma | sin2, нужная поправка, честный синтез |

**Key lemmas (deep):**

- **`honest_synthesis`** - Честная пометка: древесный sin²θ_W и нужная поправка вычислены точно над Q, но это НЕ вывод 3/13 (over-branded per audit — закрытие при ПРЕДПОЛОЖЕННЫХ размерностях). Образец честности проекта. _(weinberg-angle, honest, over-branded)_

**Uniqueness - score 2 (methods).** Древесный sin²θ_W + нужная поправка точно над Q, ЧЕСТНО помечено как согласование (не вывод 3/13).
> _Caveat:_ Weinberg-угол классичен; 3/13 над-брендирован (audit). Ценность — честная Q-постановка.

---

## #570 - `src/lattice/DistinctionLattice.v` - score 1 (exposition)

**The distinction lattice: coordination, vertices, spacing**

- **Topic.** Coordination number per dimension, vertex counts, lattice spacing decreasing, spacing positive (1D/2D/3D).
- **Role.** Lattice geometry from distinction. Self-contained.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ решётка из distinction-графа; координационное число. _Roles:_ геометрия решётки как роль. _Rules:_ coord_d; vertices_d; spacing_decreases. _P4:_ конечная решёточная геометрия точна (Element).
- **Classical counterpart.** Lattice coordination number / vertex count / spacing in 1D/2D/3D is elementary geometry; NEW: nothing — exact Q lattice geometry from a distinction graph.
- **Tags.** lattice, geometry, distinction, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `coord_number num_vertices lattice_spacing coord_1d/2d/3d vertices_*_4 spacing_decreases/positive` | Definition/Lemma | координация, вершины, шаг решётки |

**Key lemmas (deep):**

- **`spacing_decreases`** - Шаг решётки убывает с измельчением (континуум-предел как процесс) над Q. Element-сторона: решётка из distinction-графа. _(lattice, geometry, distinction)_

**Uniqueness - score 1 (exposition).** Геометрия решётки из distinction (координация/вершины/шаг, 1D-3D).
> _Caveat:_ Элементарная геометрия; ценность — связь с distinction-онтологией.

---

## #571 - `src/lattice/FeynmanRules.v` - score 2 (methods)

**Feynman rules over Q: propagator, vertices, finite one-loop**

- **Topic.** Feynman propagator (Cayley coeff), vertex factors, symmetry factors (factorial), one-loop sigma, and no UV divergence (finite lattice).
- **Role.** Lattice perturbative QFT (Feynman rules). Self-contained.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ пропагатор, вершины, symmetry factors. _Roles:_ Feynman-правила как роль теории возмущений. _Rules:_ propagator; vertex; one_loop_sigma; no_UV_divergence. _P4:_ одна петля КОНЕЧНА на решётке (no UV) над Q (Element).
- **Classical counterpart.** Feynman rules (propagator, vertices, symmetry factors, one-loop, no UV divergence on a finite lattice) are standard perturbative QFT; NEW: nothing — exact Q one-loop with finite (no-UV) sums.
- **Tags.** lattice, feynman, one-loop, no-UV, methods

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `feynman_propagator cayley_coeff vertex_factor symmetry_factor one_loop_sigma vertex_3pt/4pt no_UV_divergence feynman_rules_synthesis` | Definition/Lemma | пропагатор, вершины, конечная одна петля |

**Key lemmas (deep):**

- **`no_UV_divergence`** - Одна петля КОНЕЧНА (нет УФ-расходимости) на конечной решётке над Q — решётка как УФ-регулятор. Element-сторона: P4-финитность убирает расходимость. _(feynman, one-loop, no-UV, P4)_

**Uniqueness - score 2 (methods).** Feynman-правила над Q с КОНЕЧНОЙ одной петлёй (решётка=УФ-регулятор, no_UV_divergence).
> _Caveat:_ Решёточная регуляризация классична; вклад — точная Q-конечность одной петли.

---

## #572 - `src/lattice/FreeEnergy.v` - score 1 (exposition)

**Free energy: mass gap and correlation length over Q**

- **Topic.** Mass gaps for chain-2/chain-4, xi^2, gap positive, xi growing as mass decreases.
- **Role.** Lattice QFT (free energy / xi). Self-contained.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ mass gap; корреляционная длина xi. _Roles:_ xi как роль масштаба. _Rules:_ gap_positive; xi_grows_as_mass_decreases. _P4:_ gap и xi точны над Q (Element).
- **Classical counterpart.** Mass gap and correlation length xi (xi grows as mass decreases) are standard; NEW: nothing — exact Q mass gap / xi for short chains.
- **Tags.** lattice, mass-gap, correlation-length, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `mass_gap_chain2/4 xi_squared gap_positive xi_grows_as_mass_decreases free_energy_synthesis` | Definition/Lemma | mass gap, xi, рост xi |

**Key lemmas (deep):**

- **`xi_grows_as_mass_decreases`** - Корреляционная длина xi растёт при убывании массы (критический предел) над Q. Element-сторона. _(mass-gap, correlation-length)_

**Uniqueness - score 1 (exposition).** Mass gap и xi над Q (xi растёт при убывании массы).
> _Caveat:_ Стандартно; ценность — Q-точность.

---

## #573 - `src/lattice/GaugeFieldFromConnection.v` - score 1 (exposition)

**Gauge field from a connection: unitary links over Q**

- **Topic.** Link variables unitary (column orthogonality), det 1, orthogonal, the transfer T, T^2 trace, trivial Wilson loop.
- **Role.** Lattice gauge theory (gauge from connection). Self-contained.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ линк-переменные U; связность. _Roles:_ калибровочное поле из связности как роль. _Rules:_ link_unitary; det_one; wilson_loop_trivial. _P4:_ унитарные линки точны над Q (Element).
- **Classical counterpart.** Link variables as unitary/orthogonal SU(2) connections, det 1, trivial Wilson loop are standard lattice gauge theory; NEW: nothing — exact Q link unitarity and a trivial Wilson loop.
- **Tags.** lattice, gauge, link-variables, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `U00..U11 link_unitary_col0/1 link_det_one link_orthogonal trace_T T_sq wilson_loop_trivial connection_is_gauge_synthesis` | Definition/Lemma | унитарные линки, det 1, Wilson loop |

**Key lemmas (deep):**

- **`link_det_one`** - Линк-переменные унитарны с det=1 (SU(2)-связность) над Q точно; Wilson loop тривиален. Element-сторона решёточной калибровки. _(lattice-gauge, link-variables, SU2)_

**Uniqueness - score 1 (exposition).** Калибровочное поле из связности (унитарные линки, det 1, тривиальный Wilson loop) над Q.
> _Caveat:_ Решёточная калибровка классична; ценность — Q-точность.

---

## #574 - `src/lattice/HiggsMechanism.v` - score 1 (exposition)

**Higgs mechanism over Q: mW/mZ/mH (with honest disagreement)**

- **Topic.** lambda_3/4, breaking mass, vev=1, mH/mW/mZ squared, ratios, mH lighter than mW, and an explicit higgs_disagreement.
- **Role.** Lattice EW (Higgs). Self-contained. Honestly flags a mismatch.
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ Higgs-потенциал; vev; массы W/Z/H. _Roles:_ механизм Хиггса как роль нарушения симметрии. _Rules:_ mH/mW/mZ_squared; ratios; higgs_disagreement. _P4:_ массы точны над Q; higgs_disagreement честно помечает расхождение.
- **Classical counterpart.** The Higgs mechanism (symmetry breaking, mW/mZ/mH from the vev and couplings) is standard EW; NEW: nothing — exact Q masses, with a HONEST 'higgs_disagreement' flag where the prediction misses.
- **Tags.** lattice, higgs, honest, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `lambda_3/4 m_sq_breaking v_squared mH/mW/mZ_squared ratios mH_lighter_than_mW higgs_disagreement` | Definition/Lemma | массы W/Z/H, отношения, честное расхождение |

**Key lemmas (deep):**

- **`higgs_disagreement`** - Явная честная пометка: предсказанная mH расходится с наблюдением (mH_lighter_than_mW неверно физически) — проект НЕ скрывает промах. Образец честности. _(higgs, honest, disagreement)_

**Uniqueness - score 1 (exposition).** Механизм Хиггса над Q (mW/mZ/mH, отношения) с ЧЕСТНОЙ пометкой расхождения.
> _Caveat:_ Механизм Хиггса классичен; предсказание промахивается (честно). Ценность — честность.

---

## #575 - `src/lattice/InteractionFromGraph.v` - score 1 (exposition)

**Interaction couplings from the graph: lambda_3, lambda_4 over Q**

- **Topic.** Cayley coefficients, lambda_3/lambda_4 values and ratio, couplings synthesis.
- **Role.** Lattice QFT (interactions from graph). Self-contained.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ Cayley-коэффициенты; связи lambda. _Roles:_ взаимодействие из графа как роль. _Rules:_ lambda_3/4_val; lambda_ratio. _P4:_ связи вычислены точно над Q (Element).
- **Classical counterpart.** Deriving phi^3/phi^4 couplings from a Cayley-coefficient expansion is a modelling choice; NEW: nothing — exact Q couplings lambda_3/lambda_4 and their ratio.
- **Tags.** lattice, interaction, coupling, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `cayley_coeff lambda_3/4 cayley_0..5 lambda_3/4_val lambda_ratio couplings_synthesis` | Definition/Lemma | Cayley-коэффициенты, lambda-связи, отношение |

**Key lemmas (deep):**

- **`lambda_ratio`** - Отношение связей lambda_4/lambda_3 вычислено из Cayley-разложения графа над Q. Element-сторона: взаимодействие из distinction-графа. _(interaction, coupling, graph)_

**Uniqueness - score 1 (exposition).** Связи lambda_3/lambda_4 из графа над Q (Cayley-коэффициенты, отношение).
> _Caveat:_ Моделирование; ценность — связь с distinction-графом.

---

## #576 - `src/lattice/Lattice3DPropagator.v` - score 1 (exposition)

**3D lattice propagator over Q**

- **Topic.** 3D Laplacian, the Green function G_3D over modes, self-propagator positive and < 1, weighted mode sum.
- **Role.** Lattice QFT (3D propagator). Self-contained.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ 3D пропагатор G_3D; моды. _Roles:_ пропагатор как роль. _Rules:_ G_3D по модам; self_prop positive/< 1. _P4:_ 3D пропагатор точен над Q (Element).
- **Classical counterpart.** The 3D lattice scalar propagator (Fourier sum over modes, positive, < 1) is standard; NEW: nothing — exact Q 3D propagator values.
- **Tags.** lattice, propagator, 3D, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `lap3D_N2 G_3D self_prop_3D G_3D_zero/four/eight/twelve weighted_sum_N2 self_prop_positive/less_than_1 lattice_3D_propagator_synthesis` | Definition/Lemma | 3D Green-функция, self-propagator |

**Key lemmas (deep):**

- **`self_prop_less_than_1`** - 3D self-пропагатор положителен и < 1 над Q точно (конечная сумма по модам). Element-сторона. _(propagator, 3D, green-function)_

**Uniqueness - score 1 (exposition).** 3D решёточный пропагатор над Q (G по модам, self-prop в (0,1)).
> _Caveat:_ Стандартно; ценность — Q-точность.

---

## #577 - `src/lattice/LatticeFieldEquations.v` - score 1 (exposition)

**Lattice field equations: Klein-Gordon = graph Laplacian + mass**

- **Topic.** The 1D Laplacian (zero on constants, linear, quadratic), Klein-Gordon as Laplacian+mass, massless = graph Laplacian.
- **Role.** Lattice QFT (field equations). Self-contained.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ лапласиан; уравнение Клейна-Гордона. _Roles:_ полевое уравнение как роль. _Rules:_ kg = laplacian + mass; massless = graph laplacian. _P4:_ полевое уравнение = граф-лапласиан (Element).
- **Classical counterpart.** The lattice Klein-Gordon equation as graph-Laplacian + mass is standard; NEW: nothing — exact Q Laplacian identities (massless = pure Laplacian).
- **Tags.** lattice, klein-gordon, laplacian, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `laplacian_1d klein_gordon_1d laplacian_constant_zero/linear/quadratic kg_massless kg_is_laplacian_plus_mass laplacian_is_graph_laplacian` | Definition/Lemma | лапласиан, Клейн-Гордон, безмассовый случай |

**Key lemmas (deep):**

- **`kg_is_laplacian_plus_mass`** - Уравнение Клейна-Гордона = граф-лапласиан + масса над Q; безмассовый случай = чистый граф-лапласиан. Element-сторона: динамика поля из distinction-графа. _(klein-gordon, laplacian, graph)_

**Uniqueness - score 1 (exposition).** Полевые уравнения как граф-лапласиан + масса над Q (безмассовый = граф-лапласиан).
> _Caveat:_ Стандартно; ценность — связь с графом.

---

## #578 - `src/lattice/LoopNormalization.v` - score 1 (exposition)

**Loop normalization over Q: 4D one-loop delta**

- **Topic.** 4D effective Green function, self-propagator, sigma_4D, delta_4D positive and small (N=2).
- **Role.** Lattice one-loop (4D normalization). Self-contained.
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ 4D Green-функция; одна петля sigma/delta. _Roles:_ нормировка петли как роль. _Rules:_ sigma_4D; delta_4D positive/small. _P4:_ 4D одна петля точна над Q (Element).
- **Classical counterpart.** One-loop self-energy normalization (effective 4D Green function, sigma, delta correction) is standard; NEW: nothing — exact Q 4D one-loop delta (small, positive).
- **Tags.** lattice, one-loop, 4D, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `lap3D_N2 G_eff_4D self_prop_4D sigma_4D delta_4D G_eff_zero/four/eight self_prop_4D_exact delta_4D_positive/small` | Definition/Lemma | 4D Green-функция, sigma, delta поправка |

**Key lemmas (deep):**

- **`delta_4D_small`** - 4D одно-петлевая поправка delta мала и положительна над Q точно (N=2). Element-сторона: контролируемая петля. _(one-loop, 4D, delta)_

**Uniqueness - score 1 (exposition).** 4D одно-петлевая нормировка над Q (sigma_4D, delta мала/положительна).
> _Caveat:_ Стандартно; ценность — Q-точность.

---

## #579 - `src/lattice/LoopRefinementN4.v` - score 1 (exposition)

**Loop refinement N=4 over Q: delta convergence**

- **Topic.** N=4 effective Green function, sigma_4D_N4, delta_N4 positive/small and < delta_N2, convergence synthesis.
- **Role.** Lattice one-loop (N=4 refinement). Self-contained.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ N=4 Green-функция; delta_N4. _Roles:_ уточнение петли как процесс. _Rules:_ delta_N4 < delta_N2 (сходимость). _P4:_ уточнение петли сходится как процесс (Element-стадии).
- **Classical counterpart.** Refining the one-loop sum to N=4 modes (convergence of delta) is a standard refinement; NEW: nothing — exact Q N=4 delta smaller than N=2 (convergence).
- **Tags.** lattice, one-loop, refinement, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `lap3D_N4 G_eff_4D weighted_G_N4 sigma_4D_N4 delta_4D_N4_positive/small delta_N4_less_than_N2 convergence_synthesis` | Definition/Lemma | N=4 уточнение, сходимость delta |

**Key lemmas (deep):**

- **`delta_N4_less_than_N2`** - delta при N=4 меньше, чем при N=2 — петлевая поправка СХОДИТСЯ при измельчении (процесс). Element/role-limit: уточнение как процесс над Q. _(one-loop, refinement, convergence)_

**Uniqueness - score 1 (exposition).** Уточнение петли N=4 над Q (delta сходится: delta_N4 < delta_N2).
> _Caveat:_ Стандартное уточнение; ценность — Q-сходимость.

---

## #580 - `src/lattice/MassFromSpectrum.v` - score 2 (methods)

**Mass from spectrum over Q: mW/mZ ratio**

- **Topic.** Re of Cayley eigenvalues, mass proxy, physical mass squared, mW/mZ predicted vs observed (close), exact mass ratios.
- **Role.** Lattice spectrum (mass extraction). Self-contained.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ спектр (Re Cayley); масса. _Roles:_ масса из спектра как роль. _Rules:_ mW/mZ_prediction; mass_ratio_exact. _P4:_ масса из спектра точна над Q (Element).
- **Classical counterpart.** Extracting a physical mass from the spectrum (Re of a Cayley eigenvalue) and mW/mZ ratios is standard; NEW: nothing — exact Q mass ratios (mW/mZ close to SM).
- **Tags.** lattice, mass, spectrum, methods

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `Re_cayley mass_proxy phys_mass_sq mW_over_mZ_squared mW_mZ_prediction/close mass_ratio_exact` | Definition/Lemma | спектр, масса, mW/mZ |

**Key lemmas (deep):**

- **`mW_mZ_close`** - Предсказанное mW/mZ близко к наблюдаемому над Q точно (из спектра Cayley). Element-сторона; честно — отношение, не вывод абсолютных масс. _(mass, mW-mZ, spectrum)_

**Uniqueness - score 2 (methods).** Масса из спектра над Q (mW/mZ близко к SM, точные отношения).
> _Caveat:_ Стандартное извлечение массы; ценность — Q-точность отношения.

---

## #581 - `src/lattice/MassSpectrumSynthesis.v` - score 1 (exposition)

**Mass spectrum synthesis over Q (honest: WZ good, HW bad)**

- **Topic.** W/Z, H/W, rho predictions, with explicit WZ_good, HW_bad, rho_exact, and 'WZ_not_independent'/'HW_is_prediction' honesty.
- **Role.** Lattice EW phenomenology (honest synthesis). Self-contained.
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ предсказания W/Z, H/W, rho. _Roles:_ спектр-синтез как честная роль сравнения. _Rules:_ WZ_good; HW_bad; rho_exact. _P4:_ предсказания точны над Q; честно помечено что хорошо/плохо.
- **Classical counterpart.** Comparing W/Z, H/W, rho predictions to data is standard EW phenomenology; NEW: nothing — exact Q predictions with HONEST flags (WZ good, HW bad, rho exact).
- **Tags.** lattice, mass-spectrum, honest, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `MassPrediction WZ_prediction HW_prediction rho_prediction WZ_good HW_bad rho_exact WZ_not_independent HW_is_prediction` | Definition/Lemma | предсказания масс с честными пометками |

**Key lemmas (deep):**

- **`HW_bad`** - Честная пометка: предсказание H/W ПЛОХОЕ (HW_bad), W/Z хорошее но не независимое, rho точное. Проект явно различает удачи и промахи. Образец честности. _(mass-spectrum, honest, HW-bad)_

**Uniqueness - score 1 (exposition).** Спектр масс над Q с ЧЕСТНЫМИ пометками (WZ good, HW bad, rho exact).
> _Caveat:_ EW-феноменология стандартна; ценность — честное различение удач/промахов.

---

## #582 - `src/lattice/OneLoop3D.v` - score 1 (exposition)

**3D one-loop over Q (honest negative delta)**

- **Topic.** 3D self-propagator, sigma_3D, tree sin^2/cos^2, b_gauge/b_metric difference (negative), raw delta (negative), physical 3D mass.
- **Role.** Lattice one-loop (3D, honest). Self-contained.
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ 3D одна петля; b_gauge/b_metric. _Roles:_ 3D петля как роль; знак delta. _Rules:_ b_diff_negative; delta_raw_negative; sigma < bare. _P4:_ 3D петля точна над Q; знак честно помечен.
- **Classical counterpart.** 3D one-loop self-energy with a (negative) b-difference and delta is standard; NEW: nothing — exact Q 3D one-loop with an HONEST negative-sign note.
- **Tags.** lattice, one-loop, 3D, honest, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `sigma_3D b_gauge/b_metric b_diff delta_raw sigma_3D_positive/small b_diff_negative delta_raw_negative phys_mass_3D one_loop_3D_synthesis` | Definition/Lemma | 3D петля, b-разность, знак delta |

**Key lemmas (deep):**

- **`delta_raw_negative`** - 3D raw delta ОТРИЦАТЕЛЬНА (b_diff_negative) над Q — честно помечено (позже исправлено в WeinbergCorrectionFixed). Документирует процесс отладки знака. _(one-loop, 3D, sign, honest)_

**Uniqueness - score 1 (exposition).** 3D одна петля над Q с честной пометкой отрицательного знака delta.
> _Caveat:_ Стандартно; ценность — честный учёт знака (исправлен позже).

---

## #583 - `src/lattice/OneLoopScalar.v` - score 1 (exposition)

**Scalar one-loop over Q**

- **Topic.** Chain sigma, physical mass, sigma decreasing, small mass shift, sigma positive.
- **Role.** Lattice one-loop (scalar). Self-contained.
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ скалярная одна петля sigma. _Roles:_ петля как роль сдвига массы. _Rules:_ sigma_decreases; mass_shift_small. _P4:_ скалярная петля точна над Q (Element).
- **Classical counterpart.** Scalar one-loop self-energy (sigma decreasing, small mass shift) is standard; NEW: nothing — exact Q scalar one-loop.
- **Tags.** lattice, one-loop, scalar, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `sigma_chain phys_mass sigma_chain2/4_m1 phys_mass_chain2 sigma_decreases mass_shift_small one_loop_synthesis` | Definition/Lemma | скалярная петля, сдвиг массы |

**Key lemmas (deep):**

- **`mass_shift_small`** - Скалярный одно-петлевой сдвиг массы мал над Q точно. Element-сторона. _(one-loop, scalar, mass-shift)_

**Uniqueness - score 1 (exposition).** Скалярная одна петля над Q (sigma убывает, малый сдвиг массы).
> _Caveat:_ Стандартно; ценность — Q-точность.

---

## #584 - `src/lattice/PartitionFunction.v` - score 1 (exposition)

**Partition function over Q: det of the mass matrix**

- **Topic.** Laplacian eigenvalues, the mass-matrix determinant via list product, a zero mode, det positive, det growing with mass.
- **Role.** Lattice QFT (partition function). Self-contained.
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ mass-матрица; det = произведение собственных значений. _Roles:_ partition как роль (det). _Rules:_ det = product(eigs); zero_mode; det_grows_with_mass. _P4:_ det точен над Q (Element); нулевая мода учтена.
- **Classical counterpart.** The partition function as det of the mass matrix (product of Laplacian eigenvalues + mass), with a zero mode, is standard; NEW: nothing — exact Q determinants growing with mass.
- **Tags.** lattice, partition, determinant, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `laplacian_eigs_2/3/4 mass_matrix_eigs list_product det_mass_matrix zero_mode det_positive det_grows_with_mass partition_synthesis` | Definition/Lemma | собственные значения, det, нулевая мода |

**Key lemmas (deep):**

- **`det_grows_with_mass`** - Определитель mass-матрицы (= произведение собственных значений лапласиана + масса) растёт с массой над Q; нулевая мода учтена. Element-сторона partition-функции. _(partition, determinant, zero-mode)_

**Uniqueness - score 1 (exposition).** Partition-функция как det mass-матрицы над Q (произведение собств. значений, рост с массой).
> _Caveat:_ Стандартно; ценность — Q-точность.

---

## #585 - `src/lattice/PerturbationExpansion.v` - score 1 (exposition)

**Perturbation expansion over Q: T^2 path counting**

- **Topic.** Transfer entries T00..T11, T^2 entries and trace, free-is-exact (order 0), K=2 path counts, T^2 diagonal equal.
- **Role.** Lattice perturbation theory (T^2). Self-contained.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ transfer T; T^2; пути. _Roles:_ теория возмущений как роль. _Rules:_ T2 entries; path_count_K2; free_is_exact. _P4:_ T^2 и пути точны над Q (Element).
- **Classical counterpart.** Perturbative expansion of the transfer matrix (T^2 path counting, free is exact at order 0) is standard; NEW: nothing — exact Q T^2 entries and path counts.
- **Tags.** lattice, perturbation, transfer, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `T00..T11 T2_00..T2_11 T2_trace free_is_exact perturbation_order_0 path_count_K2 T2_diagonal_equal` | Definition/Lemma | T^2, счёт путей, свободный порядок |

**Key lemmas (deep):**

- **`free_is_exact`** - Свободная теория точна на порядке 0 (T^2 path counting) над Q. Element-сторона теории возмущений на решётке. _(perturbation, transfer, path-counting)_

**Uniqueness - score 1 (exposition).** Перт. разложение над Q (T^2 счёт путей, свободное точно на порядке 0).
> _Caveat:_ Стандартно; ценность — Q-точность.

---

## #586 - `src/lattice/Propagator.v` - score 1 (exposition)

**Propagator over Q: positive, decaying, inverse-checked**

- **Topic.** prop_00/01, the Green function G_k (zero/first mode), Fourier sum, propagator positive and decaying with distance, mass-matrix det, inverse check.
- **Role.** Lattice QFT (propagator). Self-contained.
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ пропагатор; Green G_k. _Roles:_ пропагатор как роль. _Rules:_ prop_positive; decays_with_distance; inverse_check. _P4:_ пропагатор точен над Q, обратная проверка (Element).
- **Classical counterpart.** The 2-point function / propagator (Fourier sum, positive, decaying with distance, inverse-check) is standard; NEW: nothing — exact Q propagator with an inverse-consistency check.
- **Tags.** lattice, propagator, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `prop_00/01 G_k fourier_sum prop_positive_m1 prop_decays_with_distance mass_matrix_det inverse_check_00/01 propagator_synthesis` | Definition/Lemma | пропагатор, Green, обратная проверка |

**Key lemmas (deep):**

- **`prop_decays_with_distance`** - Пропагатор положителен и убывает с расстоянием над Q точно, с проверкой обратимости (inverse_check). Element-сторона. _(propagator, decay, inverse-check)_

**Uniqueness - score 1 (exposition).** Пропагатор над Q (положителен, убывает, проверка обратной матрицы).
> _Caveat:_ Стандартно; ценность — Q-точность + inverse check.

---

## #587 - `src/lattice/RGFlowProcess.v` - score 2 (new-framing)

**RG flow as a P4 process over Q: toward the Gaussian fixed point**

- **Topic.** RG data, the Gaussian fixed point (coupling zero), flow steps decreasing toward the GFP, flow bounded, and rg_is_process.
- **Role.** Lattice RG (flow as process, vein C). Self-contained.
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ RG-данные; гауссова неподвижная точка. _Roles:_ RG-течение как ПРОЦЕСС (P4); GFP как role-limit. _Rules:_ flow_toward_gfp; flow_bounded; rg_is_process. _P4:_ ★ RG-течение ЕСТЬ процесс (rg_is_process), ограничен, к GFP — вена C в RG.
- **Classical counterpart.** RG flow toward a Gaussian fixed point (coupling decreasing, flow bounded) as a discrete process is standard; NEW is only the P4 framing: the RG flow IS a process (rg_is_process), bounded, toward the Gaussian FP.
- **Tags.** lattice, RG, process, vein-C, new-framing

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `RGData gaussian_fp gfp_coupling_zero flow_decreasing flow_toward_gfp flow_bounded rg_is_process rg_flow_synthesis` | Definition/Lemma | течение к GFP, ограниченность, процесс |

**Key lemmas (deep):**

- **`rg_is_process`** - RG-течение ЕСТЬ процесс (P4): дискретные шаги, ограничен, монотонно к гауссовой неподвижной точке над Q. Вена C в применении к RG: течение = процесс, не завершённая траектория. _(RG, process, gaussian-FP, vein-C)_

**Uniqueness - score 2 (new-framing).** RG-течение как P4-ПРОЦЕСС над Q (к гауссовой неподвижной точке, ограничен) — вена C в RG.
> _Caveat:_ RG-течение к GFP классично; ново — P4/процесс-обрамление.

---

## #588 - `src/lattice/ScalarField.v` - score 1 (exposition)

**Scalar field action over Q**

- **Topic.** ScalarField, the 1D kinetic term (symmetric, zero on constants, positive), mass term, the 1D action, scaling examples.
- **Role.** Lattice QFT (scalar action). Self-contained.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ скалярное поле; кинетический/массовый член. _Roles:_ действие как роль. _Rules:_ kinetic_symmetric/positive; action_1d. _P4:_ скалярное действие точно над Q (Element).
- **Classical counterpart.** A lattice scalar field action (kinetic + mass, kinetic symmetric/positive) is standard; NEW: nothing — exact Q scalar action.
- **Tags.** lattice, scalar-field, action, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `ScalarField kinetic_1d mass_term action_1d kinetic_symmetric/zero_const/positive_step mass_single_nonneg action_zero_trivial` | Definition/Lemma | кинетический/массовый член, действие |

**Key lemmas (deep):**

- **`kinetic_positive_step`** - Кинетический член положителен (за исключением констант) над Q — корректное скалярное действие на решётке. Element-сторона. _(scalar-field, action, kinetic)_

**Uniqueness - score 1 (exposition).** Скалярное действие над Q (кинетический симметричен/положителен, массовый член).
> _Caveat:_ Стандартно; ценность — Q-точность.

---

## #589 - `src/lattice/WeinbergCorrection.v` - score 1 (exposition)

**Weinberg correction over Q (honest sign mismatch)**

- **Topic.** Tree sin^2, observed sin^2, needed delta (positive, small), our delta (negative), honest_sign_mismatch, tree relative accuracy.
- **Role.** Lattice EW (Weinberg correction, honest). Superseded by WeinbergCorrectionFixed. Self-contained.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ sin2; нужная/наша delta. _Roles:_ поправка Вайнберга; знак. _Rules:_ delta_needed_positive; our_delta_negative; honest_sign_mismatch. _P4:_ древесный sin2 точен; honest_sign_mismatch честно помечает промах знака.
- **Classical counterpart.** The loop correction to the Weinberg angle is standard EW; NEW: nothing — exact Q delta with an HONEST sign-mismatch flag (our_delta negative vs needed positive).
- **Tags.** lattice, weinberg, sign-mismatch, honest, exposition
- **Notes.** Sign issue fixed in WeinbergCorrectionFixed.v.

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `sin2_tree/observed delta_needed our_delta delta_needed_positive/small our_delta_negative honest_sign_mismatch tree_relative_accuracy` | Definition/Lemma | sin2, поправки, честный промах знака |

**Key lemmas (deep):**

- **`honest_sign_mismatch`** - Честная пометка: наша delta ОТРИЦАТЕЛЬНА, а нужна положительная — промах знака (исправлен в WeinbergCorrectionFixed). Проект явно фиксирует ошибку. Образец честности/отладки. _(weinberg, sign-mismatch, honest)_

**Uniqueness - score 1 (exposition).** Поправка Вайнберга над Q с ЧЕСТНОЙ пометкой промаха знака (исправлено позже).
> _Caveat:_ Стандартно; СУПЕРСЕДЕД WeinbergCorrectionFixed. Ценность — честность отладки.

---

## #590 - `src/lattice/WeinbergCorrectionFixed.v` - score 2 (methods)

**Weinberg correction FIXED over Q (sign corrected, still short)**

- **Topic.** Tree sin^2/cos^2, the wrong (negative) b-difference flipped to a correct positive effective b, physical delta positive and small, both positive but our < needed.
- **Role.** Lattice EW (corrected Weinberg). Fixes WeinbergCorrection. Self-contained.
- **Counts.** Qed 15 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ sin2/cos2; исправленный b_effective. _Roles:_ исправленная поправка Вайнберга. _Rules:_ fixed_flipped_sign; delta_phys_positive; our_less_than_needed. _P4:_ знак исправлен (delta>0), но our < needed — честно: согласование неполное.
- **Classical counterpart.** The corrected loop contribution to the Weinberg angle is standard EW; NEW: nothing — exact Q delta with the sign FIXED (now positive), both-positive but still smaller than needed (honest).
- **Tags.** lattice, weinberg, sign-fixed, honest, methods

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `sin2_tree/cos2_tree b_diff_wrong correct_sign b_effective delta_raw_fixed delta_physical delta_phys_positive/small our_less_than_needed both_same_sign weinberg_correction_fixed` | Definition/Lemma | исправленный знак, физическая delta, честная нехватка |

**Key lemmas (deep):**

- **`our_less_than_needed`** - Знак delta ИСПРАВЛЕН (теперь положителен, both_same_sign), но наша delta всё ещё МЕНЬШЕ нужной — честно: согласование улучшено, но неполное. Точная Q-арифметика + честная самооценка. _(weinberg, sign-fixed, honest)_

**Uniqueness - score 2 (methods).** Исправленная поправка Вайнберга над Q (знак положителен), но честно our < needed — улучшено, не завершено.
> _Caveat:_ Weinberg-угол классичен/над-брендирован (3/13); ценность — точная отладка знака + честная самооценка.

---

## #591 - `src/lattice/WZMassRatio.v` - score 2 (methods)

**W/Z mass ratio over Q: within 1% of data**

- **Topic.** cos^2_W, predicted mW/mZ squared vs observed (within 1%), cos^2+sin^2=1, rho parameter, prediction close to SM.
- **Role.** Lattice EW (W/Z ratio). Self-contained.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ cos2_W; mW/mZ. _Roles:_ W/Z отношение как роль. _Rules:_ mW_mZ_sq_predicted vs observed; match_within_1pct. _P4:_ mW/mZ точно над Q, в пределах 1% наблюдения (Element).
- **Classical counterpart.** The W/Z mass ratio from cos^2(theta_W) (rho=1) matching data within a percent is standard EW; NEW: nothing — exact Q mW/mZ within 1% of observation.
- **Tags.** lattice, mW-mZ, ratio, methods

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `cos2_W mW_mZ_sq_predicted/observed prediction match_within_1pct cos2_plus_sin2 rho_parameter prediction_close_to_SM` | Definition/Lemma | cos2, mW/mZ, согласие 1% |

**Key lemmas (deep):**

- **`match_within_1pct`** - Предсказанное mW/mZ совпадает с наблюдением в пределах 1% над Q точно (из cos²θ_W, rho=1). Element-сторона; честно — отношение при rho=1, не независимый вывод. _(mW-mZ, ratio, 1-percent)_

**Uniqueness - score 2 (methods).** Отношение mW/mZ над Q в пределах 1% наблюдения (cos²θ_W, rho=1).
> _Caveat:_ W/Z-отношение классично (rho=1 на дереве); ценность — Q-точность согласия.

