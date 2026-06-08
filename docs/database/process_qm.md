# Database - cluster `process_qm`

_Generated from `process_qm.json` by `generate.ps1` - do not edit by hand; edit the JSON._

**4 files / 38 Qed.** Score distribution: s5=0 / s4=0 / s3=0 / s2=3 / s1=1 / s0=0

---

## #1031 - `src/process_qm/HilbertAsProcess.v` - score 2 (methods)

**Hilbert space as a process over Q: finite states, growing spectrum**

- **Topic.** A state with N components is finite, inner-product commutativity and Pythagoras, non-negative self inner product, an eigenvalue count, trace = eigensum, the N=2/N=4 spectrum and that the spectrum grows.
- **Role.** Leaf of the process-QM branch (parallels projective/QuantumTower, physics/QState). Self-contained (QArith).
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ состояния с N компонентами (конечны); спектр. _Roles:_ гильбертово пространство = роль-процесс; спектр растёт со стадией. _Rules:_ state_is_finite; trace_equals_eigensum; spectrum_grows. _P4:_ состояние конечно на каждой стадии (Element); гильбертово пространство — процесс (role-limit).
- **Classical counterpart.** Finite-dimensional Hilbert space, the inner-product axioms, trace = sum of eigenvalues and a growing spectrum are standard QM; NEW only as the P4 framing (the state is finite at each stage, the spectrum grows as a process).
- **Tags.** process-qm, hilbert, process, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `state_has_N_components/state_is_finite` | Theorem | ★ состояние конечно |
| `ip_commutativity/ip_pythagoras/ip_nonneg_self_concrete` | Theorem | аксиомы скалярного произведения |
| `eigenvalue_count_4/trace_equals_eigensum/spectrum_N2/spectrum_N4/spectrum_grows/hilbert_as_process_synthesis` | Theorem | ★ trace=сумма с.з., спектр растёт |

**Key lemmas (deep):**

- **`state_is_finite`** - Квантовое состояние конечно на каждой стадии, гильбертово пространство = процесс (spectrum_grows) — вена C для КМ. Бесконечномерность не актуальна, а предельна. _(hilbert, process, finite, vein-C)_

**Uniqueness - score 2 (methods).** Гильбертово пространство как процесс над Q: конечные состояния, trace=сумма собственных значений, растущий спектр.
> _Caveat:_ Конечномерное гильбертово пространство и trace=eigensum стандартны; вклад — P4-переобрамление как процесс, не новая КМ.

---

## #1032 - `src/process_qm/MeasurementProcess.v` - score 2 (methods)

**Measurement as a process over Q: collapse, uncertainty shrinks with resolution**

- **Topic.** Post-measurement state (collapse, normalized, certain, zero on others), exact inner products (ground/orthogonal), a minimum uncertainty, uncertainty at N=4/N=8, and that finer resolution gives less uncertainty.
- **Role.** Leaf of the process-QM branch (parallels physics/MeasurementProcess). Self-contained (QArith).
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ пост-измерительное состояние; неопределённость. _Roles:_ измерение = роль-коллапс; разрешение как роль-параметр. _Rules:_ post_meas_certain; min_uncertainty; finer_less_uncertainty. _P4:_ коллапс на конечной стадии (Element); уменьшение неопределённости с разрешением — процесс (role-limit).
- **Classical counterpart.** Projective measurement (collapse to an eigenstate, Born certainty on eigenstates, the minimum-uncertainty relation) is standard QM; NEW only as the P4 framing where finer resolution gives less uncertainty (a process).
- **Tags.** process-qm, measurement, uncertainty, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `post_measurement/post_meas_0/_2/_normalized/_certain/_zero_other` | Definition/Theorem | ★ коллапс, определённость |
| `inner_product/ip_self_ground/_orthogonal/_exact` | Theorem | точные скалярные произведения |
| `min_uncertainty/uncertainty_N4/_N8/finer_less_uncertainty/measurement_synthesis` | Theorem | ★ неопределённость убывает с разрешением |

**Key lemmas (deep):**

- **`finer_less_uncertainty`** - Более тонкое разрешение даёт меньшую неопределённость (uncertainty_N4 > N8) — измерение как процесс приближения, вена C. Коллапс корректен на каждой конечной стадии. _(measurement, uncertainty, process, vein-C)_

**Uniqueness - score 2 (methods).** Измерение как процесс над Q: коллапс на собственное состояние, определённость по Борну, неопределённость убывает с разрешением.
> _Caveat:_ Проективное измерение и минимальная неопределённость стандартны; вклад — P4-формулировка как процесс, не новая КМ.

---

## #1033 - `src/process_qm/ProcessQMSynthesis.v` - score 1 (exposition)

**Process-QM synthesis: three branches, one root (summary node)**

- **Topic.** A 4-lemma synthesis: thermal, Casimir and quantum branches all stem from one process root.
- **Role.** Summary node of the process-QM branch. Self-contained.
- **Counts.** Qed 4 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ ветви thermal/casimir/quantum. _Roles:_ узел-синтез: один процессный корень трёх ветвей. _Rules:_ three_branches_one_root. _P4:_ агрегатор (Element); собственного содержания нет.
- **Classical counterpart.** A summary node tying the thermal/Casimir/quantum branches to one process root; no new content.
- **Tags.** process-qm, summary, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `branch_thermal/branch_casimir/branch_quantum/three_branches_one_root` | Theorem | ★ три ветви — один процессный корень |

**Key lemmas (deep):**

- **`three_branches_one_root`** - Узел-агрегатор: thermal, Casimir и quantum ветви сходятся к одному процессному корню. Собственной уникальности нет. _(summary, process)_

**Uniqueness - score 1 (exposition).** Сводка: thermal/Casimir/quantum ветви из одного процессного корня.
> _Caveat:_ Чистый узел-агрегатор; собственного результата нет.

---

## #1034 - `src/process_qm/QuantumFromVibration.v` - score 2 (methods)

**Quantum from vibration over Q: Born rule from modes**

- **Topic.** A QState with norm and normalization, measurement probability, expected value, ground/mode-1/superposition states (all normalized), Born probabilities for ground/superposition summing to one, Laplacian eigenvalues, and expected values.
- **Role.** Root leaf of the process-QM branch ('quantum from vibration'). Self-contained (QArith).
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ QState (моды вибрации); вероятности Борна. _Roles:_ квантовая амплитуда = роль из вибрационной моды; Лапласиан как роль-гамильтониан. _Rules:_ born_probabilities_sum; superposition_norm; laplacian_eigenvalues. _P4:_ конечные моды над Q (Element); квантовые амплитуды из вибраций — модельное переобрамление.
- **Classical counterpart.** The Born rule, normalization, expectation values and Laplacian eigenvalues for a vibrating-mode model are standard QM; NEW only as the framing that quantum amplitudes emerge from vibration modes over Q.
- **Tags.** process-qm, born-rule, vibration, methods

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `QState/norm_sq/is_normalized/measurement_probability/expected_value_aux/expected_value` | Definition | состояние, норма, ожидание |
| `ground_state/mode1_state/superposition_01/ground_normalized/mode1_normalized/superposition_norm` | Definition/Theorem | состояния нормированы |
| `born_ground_mode0/_mode1/born_superposition_mode0/_mode1/born_probabilities_sum` | Theorem | ★ вероятности Борна суммируются в 1 |
| `laplacian_eigenvalues/expected_ground/expected_mode1/quantum_from_vibration_synthesis` | Theorem | собственные значения Лапласиана, ожидания |

**Key lemmas (deep):**

- **`born_probabilities_sum`** - Вероятности Борна суммируются в 1 для вибрационных состояний над Q — корректная нормировка. Модельная связь «квант из вибрации», не вывод правила Борна (ср. physics/BornRuleFromUnitarity). _(born-rule, vibration, normalization)_

**Uniqueness - score 2 (methods).** Квант из вибрации над Q: правило Борна и нормировка для вибрационных мод, собственные значения Лапласиана.
> _Caveat:_ Правило Борна и нормировка стандартны; вклад — модельное переобрамление «квант из вибрации», не вывод.

