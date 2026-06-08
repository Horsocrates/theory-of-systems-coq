# Database - cluster `linalg`

_Generated from `linalg.json` by `generate.ps1` - do not edit by hand; edit the JSON._

**6 files / 130 Qed.** Score distribution: s5=0 / s4=0 / s3=0 / s2=5 / s1=1 / s0=0

---

## #602 - `src/linalg/EigenvalueSynthesis.v` - score 2 (methods)

**Eigenvalue synthesis over Q: localization tied to ionization**

- **Topic.** Localized diagonal eigenvalues, the power method finding eigenvalues, hydrogen eigenvalue bounds, the ground-state spectral gap, eigenvalue<->ionization connection, Rayleigh variational bound, Gershgorin for hydrogen, 2x2 verifications, and a verified/open list.
- **Role.** Synthesis node of the linalg branch, bridging to atomic ionization. Self-contained (QArith).
- **Counts.** Qed 15 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ собственные значения; диагональные матрицы; спектральный зазор. _Roles:_ локализация = роль (Гершгорин/Рэлей); ионизация как роль-накопление спектра. _Rules:_ power_method_finds_eigenvalue; rayleigh_variational_bound; ionization_from_accumulation. _P4:_ конечные собственные значения над Q (Element); ионизация = точка накопления спектра (role-limit).
- **Classical counterpart.** Eigenvalue localization (Gershgorin, Rayleigh, power method) is standard numerical linear algebra; NEW only as a synthesis tying eigenvalue accumulation to the atomic ionization threshold over Q.
- **Tags.** eigenvalue, ionization, synthesis, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `eigenvalue_localized_diag/power_method_finds_eigenvalue/hydrogen_eigenvalues_bound/spectral_gap_ground` | Theorem | локализация, степенной метод, зазор |
| `process_eigenvalue_connection/rayleigh_variational_bound/rayleigh_extracts_diagonal/ionization_from_accumulation/gershgorin_hydrogen_diag` | Theorem | ★ ионизация из накопления спектра |
| `verification_2x2_diag/_2x2_symmetric/verified_results/open_questions/eigenvalue_ionization_main/total_count` | Theorem | верификации, итог |

**Key lemmas (deep):**

- **`ionization_from_accumulation`** - Связывает накопление собственных значений с порогом ионизации — спектральная точка накопления как граница связанных/свободных состояний (role-limit). Содержательная привязка линалгебры к атомной ветви, но на стандартных методах. _(eigenvalue, ionization, accumulation)_

**Uniqueness - score 2 (methods).** Синтез собственных значений над Q: локализация (Гершгорин/Рэлей) + связь накопления спектра с порогом ионизации.
> _Caveat:_ Локализация собственных значений — стандартная числ. линалгебра; вклад — привязка к ионизации, не новый спектральный результат.

---

## #603 - `src/linalg/EigenvalueTheory.v` - score 2 (methods)

**Eigenvalue theory over Q: char poly, discriminant, Pauli eigenvalues**

- **Topic.** Matrix-vector linearity, eigenvector/eigenvalue definitions, eigenvalues of diagonal/identity/zero/scaled/shifted matrices, the 2x2 determinant, characteristic polynomial and discriminant, symmetric 2x2 has real discriminant, and Pauli sigma_z/sigma_x eigenvalues.
- **Role.** Core eigenvalue definitions of the linalg branch. Self-contained (QArith).
- **Counts.** Qed 24 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ матрицы над Q; собственные векторы/значения. _Roles:_ собственное значение = роль-инвариант действия; характеристический многочлен. _Rules:_ char_poly_2x2; discriminant_2x2; symmetric_2x2_disc_nonneg. _P4:_ конечные 2x2-матрицы над Q, всё вычислимо (Element); симметрия → неотрицательный дискриминант.
- **Classical counterpart.** Eigenvectors/eigenvalues, the 2x2 characteristic polynomial and discriminant, eigenvalues of diagonal/identity/zero matrices and Pauli matrices are textbook linear algebra; here an exact Q formalization.
- **Tags.** eigenvalue, discriminant, pauli, methods

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `mat_vec_mul_add/_scale/is_eigenvector/is_eigenvalue/eigenvector_nonzero` | Definition/Lemma | линейность, собственные векторы |
| `eigenvalue_of_diag/_of_id/eigenvectors_scale/eigenvalue_shift/_scale_mat/_of_zero_mat/zero_eigenvalue_kernel/eigenvectors_add_same` | Theorem | собственные значения базовых матриц |
| `det_2x2/char_poly_2x2/discriminant_2x2/det_2x2_id/_diag/_symmetric/symmetric_2x2_disc_nonneg` | Definition/Theorem | ★ det, char poly, дискриминант |
| `qvec2/_nth_0/_nth_1/qmat2x2/eigenvalue_sigma_z_plus/_z_minus/_x_plus/_x_minus/eigenvalue_2x2_example_3/_1/diag_eigenstate_eigenvalue` | Definition/Theorem | Pauli-собственные значения |

**Key lemmas (deep):**

- **`symmetric_2x2_disc_nonneg`** - Симметричная 2x2-матрица имеет неотрицательный дискриминант → вещественные собственные значения — точная Q-формализация спектральной теоремы в размерности 2. Связь дискриминанта (вена A) с симметрией. _(discriminant, symmetric, spectral)_

**Uniqueness - score 2 (methods).** Теория собственных значений над Q: char poly/дискриминант 2x2, неотрицательный дискриминант симметричной матрицы, Pauli-собственные значения.
> _Caveat:_ 2x2 спектральная теория — учебная линалгебра; вклад — точная Q-формализация, не новый результат.

---

## #604 - `src/linalg/GershgorinDiscs.v` - score 2 (methods)

**Gershgorin discs over Q: 2x2 eigenvalue localization**

- **Topic.** Existence of a nonzero eigenvector component, eigenvalue 2x2 equations, the Gershgorin disc containing the diagonal center, Gershgorin for identity/diagonal, a max helper, spectral-radius bound, strict diagonal dominance excludes zero eigenvalue, and eigenvalues in an interval.
- **Role.** Eigenvalue-localization leaf of the linalg branch (feeds EigenvalueSynthesis). Self-contained (QArith).
- **Counts.** Qed 19 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ 2x2-матрицы; диски Гершгорина (центр+радиус). _Roles:_ диск Гершгорина = роль-локализатор собственных значений. _Rules:_ gershgorin_2x2; spectral_radius_bound_2x2; strictly_diag_dominant_no_zero_ev. _P4:_ конечные диски над Q (Element); локализация спектра без решения характеристического уравнения.
- **Classical counterpart.** The Gershgorin disc theorem (eigenvalues lie in discs centered at diagonal entries) and the spectral-radius / diagonal-dominance corollaries are classical; here a 2x2 Q instance.
- **Tags.** gershgorin, spectral-radius, localization, methods

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `nonzero_component_exists/_positive_abs/eigenvalue_component/dot_product_2/eigenvalue_2x2_equations` | Lemma | компонента собственного вектора |
| `gershgorin_2x2/gershgorin_disc_contains_center/gershgorin_id/gershgorin_diag` | Theorem | ★ диск Гершгорина содержит спектр |
| `Qmax2/_le_l/_le_r/spectral_radius_bound_2x2/_correct/is_strictly_diag_dominant_2x2/strictly_diag_dominant_no_zero_ev` | Definition/Theorem | ★ спектральный радиус, диаг. доминирование |
| `eigenvalue_in_interval_2x2/gershgorin_2x2_example/gershgorin_shift_2x2/col_sum_equals_row_sum_symmetric/diag_dominant_positive_eigenvalues_2x2/gershgorin_summary` | Theorem | интервал собственных значений, итог |

**Key lemmas (deep):**

- **`strictly_diag_dominant_no_zero_ev`** - Строгая диагональная доминантность исключает нулевое собственное значение (матрица обратима) — классическое следствие Гершгорина, точно над Q. Локализация спектра без решения характеристического уравнения. _(gershgorin, diagonal-dominance, invertible)_

**Uniqueness - score 2 (methods).** Диски Гершгорина над Q (2x2): локализация спектра, оценка спектрального радиуса, диагональное доминирование исключает нулевое собственное значение.
> _Caveat:_ Теорема Гершгорина классична; вклад — точный 2x2 Q-инстанс, не новый результат локализации.

---

## #605 - `src/linalg/IonizationThreshold.v` - score 2 (methods)

**Ionization threshold over Q: bound/free dichotomy, ionization as supremum**

- **Topic.** Ionization energy, bound vs free states, energy levels, all states bound below threshold, increasing energies, the ground-state minimum and gaps, decreasing spacing, ionization as a supremum, finitely many bound states, infinite accumulation, and an honest limitation.
- **Role.** Spectral leaf bridging linalg to atomic ionization. Self-contained (QArith).
- **Counts.** Qed 22 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ уровни энергии; связанные/свободные состояния. _Roles:_ порог ионизации = роль-граница (bound/free); ионизация как супремум. _Rules:_ is_bound_state/is_free_state; ionization_is_supremum; finite_bound_states_below. _P4:_ конечное число связанных состояний (Element); точка накопления спектра (континуум) — role-limit; honest_limitation фиксирует границу.
- **Classical counterpart.** The bound/free dichotomy at the ionization threshold, the spectrum accumulating at the continuum, and ionization as a supremum are standard spectral theory; here a Q formalization with an honest limitation about the continuum accumulation.
- **Tags.** ionization, spectrum, bound-free, honest-limitation, methods

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `ionization_energy/is_bound_state/is_free_state/energy_level/ionization_energy_value` | Definition/Theorem | энергия ионизации, дихотомия |
| `ground_state_energy/first_excited_energy/second_excited_energy/all_states_bound/ground_state_bound/energy_increasing/ground_state_minimum` | Theorem | уровни, минимум, монотонность |
| `energy_spacing_positive/ground_state_gap/first_excited_gap/energy_spacing_decreases/ionization_at_zero` | Theorem | зазоры убывают |
| `ionization_is_supremum/finite_bound_states_below/infinite_accumulation/energy_3d_converges/centrifugal_vanishes/energy_ratio/spectral_transition/honest_limitation/ionization_main_theorem` | Theorem | ★ ионизация=супремум; honest_limitation |

**Key lemmas (deep):**

- **`ionization_is_supremum`** - Энергия ионизации = супремум связанных уровней (точка накопления спектра): конечно много состояний ниже порога (finite_bound_states_below), бесконечное накопление к континууму (role-limit). honest_limitation честно фиксирует, что континуум — предельный, не актуальный объект. _(ionization, supremum, accumulation, honest)_

**Uniqueness - score 2 (methods).** Порог ионизации над Q: дихотомия bound/free, ионизация как супремум уровней, конечно связанных состояний с накоплением к континууму + honest_limitation.
> _Caveat:_ Спектральная дихотомия и порог ионизации стандартны; вклад — Q-формализация-процесс с честной фиксацией предельного континуума, не новая спектральная теория.

---

## #606 - `src/linalg/MatrixOps.v` - score 1 (infrastructure)

**Matrix operations over Q: algebra, transpose, multiplication, trace**

- **Topic.** Zero matrix, columns, add/scale/sub (entrywise), commutativity/associativity, transpose (involutive, symmetric), matrix multiplication (id/zero/scale/distribute laws), trace (additive, scaling, of identity/diagonal), and a shift matrix.
- **Role.** Infrastructure of the linalg branch (matrix algebra). Self-contained (QArith).
- **Counts.** Qed 32 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ матрицы над Q; строки/столбцы; след. _Roles:_ операции-матрицы как роли-преобразования; транспонирование/умножение. _Rules:_ mat_mul_id_l/r; mat_transpose_involutive; mat_trace_add/scale. _P4:_ конечные матрицы над Q, все законы алгебры (Element); чистая инфраструктура.
- **Classical counterpart.** Matrix addition/scaling/transpose/multiplication, trace, identity/zero laws over a field are textbook; here a clean Q formalization (infrastructure).
- **Tags.** matrix, algebra, trace, infrastructure

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `zero_mat/_entry/mat_col/_nth/mat_add/_scale/_sub/_add_entry/_scale_entry/_sub_entry` | Definition/Theorem | нулевая матрица, поэлементные операции |
| `mat_add_comm/_assoc/mat_scale_one/_assoc/_distrib_add/mat_transpose/_entry/_involutive/_symmetric` | Theorem | ★ законы сложения, транспонирование инволютивно |
| `mat_mul_row_vec/_nth/mat_mul/_entry/dot_product_ext/_r/mat_mul_id_l/_id_r/_zero_l/_zero_r/_scale_l/_distrib_r` | Definition/Theorem | ★ умножение: id/zero/scale/распределение |
| `sum_Q/mat_trace/sum_Q_ext/_plus/_scale/mat_trace_add/_scale/_id/_diag/mat_shift/_entry/_symmetric` | Definition/Theorem | след: аддитивность, масштаб |

**Key lemmas (deep):**

- **`mat_mul_id_l`** - Единичная матрица — нейтраль умножения (id_l/id_r) с полным набором законов (zero/scale/distribute) — корректная Q-формализация матричной алгебры. Инфраструктура для остальной линалгебры. _(matrix-algebra, identity, infrastructure)_

**Uniqueness - score 1 (infrastructure).** Матричная алгебра над Q: сложение/масштаб/транспонирование/умножение/след со всеми законами.
> _Caveat:_ Учебная матричная алгебра; чистая инфраструктура без собственного результата.

---

## #607 - `src/linalg/PowerMethod.v` - score 2 (methods)

**Power method over Q: Rayleigh quotient and convergence rate**

- **Topic.** The Rayleigh quotient (scale-invariant, of identity/diagonal basis), power iteration (zero/step/identity/diagonal/scale/add), the Rayleigh quotient constant on a diagonal basis, self-adjoint Rayleigh, a diagonal convergence-rate bound, and decreasing power ratios.
- **Role.** Iterative-eigenvalue leaf of the linalg branch. Self-contained (QArith).
- **Counts.** Qed 18 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ степенные итерации; отношение Рэлея. _Roles:_ степенной метод = роль-процесс приближения доминирующего собственного значения. _Rules:_ rayleigh_scale_invariant; power_iterate_diag_basis; convergence_rate_diag_bound. _P4:_ каждая итерация конечна над Q (Element); сходимость к собственному значению — role-limit процесса.
- **Classical counterpart.** The power iteration and the Rayleigh quotient (scale-invariant, extracts the dominant eigenvalue, self-adjoint) are standard numerical linear algebra; here a Q formalization with a diagonal convergence-rate bound.
- **Tags.** power-method, rayleigh, convergence, methods

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `rayleigh_quotient/_eigenvalue/_scale_invariant/_of_id/_of_diag_basis` | Definition/Theorem | ★ отношение Рэлея, масштаб-инвариантность |
| `power_iterate/_zero/_step/_id/diag_row_dot_basis/_diag_basis/Qpow_nonzero` | Definition/Theorem | степенная итерация |
| `rayleigh_diag_basis_constant/power_iterate_scale/_add/rayleigh_symmetric_selfadjoint/_nonneg_diag_basis` | Theorem | Рэлей постоянен на базисе, self-adjoint |
| `convergence_rate_diag_bound/power_ratio_decreasing/power_method_summary` | Theorem | ★ скорость сходимости |

**Key lemmas (deep):**

- **`convergence_rate_diag_bound`** - Степенной метод сходится к доминирующему собственному значению с оценённой скоростью (power_ratio_decreasing) — собственное значение как role-limit итерационного процесса. Стандартный численный метод, формализованный над Q. _(power-method, convergence, rayleigh)_

**Uniqueness - score 2 (methods).** Степенной метод над Q: отношение Рэлея (масштаб-инвариантно, self-adjoint) + оценка скорости сходимости к доминирующему собственному значению.
> _Caveat:_ Степенной метод и отношение Рэлея — стандартная числ. линалгебра; вклад — Q-формализация-процесс, не новый алгоритм.

