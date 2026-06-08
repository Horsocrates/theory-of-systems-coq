# Database - cluster `experimental`

_Generated from `experimental.json` by `generate.ps1` - do not edit by hand; edit the JSON._

**12 files / 337 Qed.** Score distribution: s5=0 / s4=0 / s3=2 / s2=6 / s1=4 / s0=0

---

## #137 - `src/experimental/AbelRegularization.v` - score 2 (methods)

**Abel regularization over Q: Abel = Bernoulli, consistent with Casimir**

- **Topic.** Abel-damped partial sums, geometric closed forms (half/third powers), and the consistency check that Abel regularization agrees with the Bernoulli/Casimir value in 1D and 3D.
- **Role.** Regularization-consistency leaf of the experimental (Casimir) branch. Self-contained (QArith).
- **Counts.** Qed 23 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ Abel-демпфированные частичные суммы; геометрические хвосты. _Roles:_ регуляризатор = роль, превращающая расходящуюся сумму в конечное Q-число. _Rules:_ abel_energy/geometric_partial; abel_and_bernoulli_agree (1D и 3D). _P4:_ расходящийся ряд не Element; РЕГУЛЯРИЗОВАННОЕ значение рационально и вычислимо (Element); согласие двух регуляризаторов = свидетельство корректности.
- **Classical counterpart.** Abel summation and zeta/Bernoulli regularization of divergent series are classical; NEW only as an exact Q-arithmetic instance showing Abel and Bernoulli regularizers AGREE and match the Casimir coefficient.
- **Tags.** regularization, abel, casimir, methods

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `abel_partial/abel_energy/geometric_partial` | Definition | Abel-сумма, энергия, геометрический ряд |
| `geometric_half_3/third_2/qpow_abs_step/half_pow_4/half_pow_8/third_pow_4` | Lemma | значения степеней 1/2, 1/3 |
| `abel_energy_1_half/_at_3/_0_is_geometric_tail` | Lemma | Abel-энергия при beta=1 |
| `geometric_half_at_5/_10/_below_2_at_5/_below_2_at_10/third_at_5` | Lemma | оценки геометрических хвостов |
| `abel_k1_half_10/_20/closed_form_half/closed_form_third` | Lemma | замкнутые формы Abel |
| `abel_and_bernoulli_agree_1d/_3d` | Theorem | ★ Abel = Bernoulli (1D, 3D) |
| `regularization_consistency/casimir_framework_complete/casimir_matches_experiment` | Theorem | согласованность регуляризаций, рамка Казимира |

**Key lemmas (deep):**

- **`abel_and_bernoulli_agree_3d`** - Два разных регуляризатора (Abel-демпфирование и Bernoulli/zeta) дают ОДНО рациональное значение в 3D — свидетельство, что конечный ответ не артефакт схемы. P4: расходимость снимается правилом, результат — Element. _(regularization, abel, bernoulli, consistency)_

**Uniqueness - score 2 (methods).** Abel-регуляризация над Q совпадает с Bernoulli/Casimir-значением (1D и 3D) — точная Q-проверка согласованности регуляризаторов.
> _Caveat:_ Abel-суммирование и регуляризация расходящихся рядов классичны; вклад — лишь точная Q-проверка согласия, не новый результат.

---

## #138 - `src/experimental/AtomicSynthesis.v` - score 1 (exposition)

**Atomic synthesis: atoms are bound, have ionization energy (summary node)**

- **Topic.** A tiny synthesis tying the atomic-physics leaves together: hydrogen is bound, atoms have ionization energy, repulsion at the nucleus.
- **Role.** Summary leaf of the atomic sub-branch. Self-contained.
- **Counts.** Qed 5 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ связанные состояния атомов; энергия ионизации. _Roles:_ узел-синтез, собирающий результаты атомной ветви. _Rules:_ hydrogen_bound; atoms_have_ionization; repulsion_at_nucleus. _P4:_ конечные оценки энергий (Element); чисто резюмирующий файл.
- **Classical counterpart.** That atoms are bound systems with a positive ionization energy is textbook QM; here only a 5-lemma Q-summary node, no new content.
- **Tags.** atomic, summary, exposition

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `hydrogen_bound/atoms_are_bound/atoms_have_ionization` | Theorem | атомы связаны, есть ионизация |
| `repulsion_at_nucleus/atomic_physics_summary` | Theorem | отталкивание у ядра; итог |

**Key lemmas (deep):**

- **`atomic_physics_summary`** - Резюмирующий узел: атомы связаны и имеют положительную энергию ионизации. Содержательной уникальности нет — агрегатор результатов соседних файлов. _(summary, atomic)_

**Uniqueness - score 1 (exposition).** Сводка атомной ветви: связанность атомов и энергия ионизации над Q.
> _Caveat:_ Полностью учебное содержание; узел-агрегатор без собственного результата.

---

## #139 - `src/experimental/BernoulliNumbers.v` - score 2 (methods)

**Bernoulli numbers over Q: recursion, Faulhaber, zeta(-n)**

- **Topic.** Rational Bernoulli numbers B0..B8 via the binomial recursion, odd Bernoulli vanish (B3=B5=B7=0), sign pattern, Faulhaber power sums, and negative-argument zeta values zeta(-0..-3).
- **Role.** Arithmetic engine of the Casimir/zeta-regularization branch (feeds CasimirProcess, ZetaNegative, VacuumEnergy). Self-contained (QArith).
- **Counts.** Qed 34 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ рациональные числа Бернулли B_n; биномы/факториалы. _Roles:_ B_n как коэффициенты-роли в Фаульхабере и zeta(-n). _Rules:_ биномиальная рекурсия Бернулли; нечётные B=0; zeta_neg n = −B_{n+1}/(n+1). _P4:_ каждое B_n — точное Q-число (Element); расходящиеся степенные суммы — role-limit, регуляризованные через B_n.
- **Classical counterpart.** Bernoulli numbers, the recursion, Faulhaber power-sum formulas and zeta(-n) = -B_{n+1}/(n+1) are classical; NEW only as an exact rational Coq instance (B0..B8, odd-vanishing, Faulhaber, zeta_neg values).
- **Tags.** bernoulli, faulhaber, zeta-negative, methods

**Lemmas (8):**

| name | kind | role |
|---|---|---|
| `qbinom/qfact/qfact_pos/qbinom_0_r/_n_n/_gt` | Definition/Lemma | рациональные биномы и факториалы |
| `bernoulli_list/bernoulli/bernoulli_list_length` | Definition | список чисел Бернулли |
| `B0_value..B8_value` | Theorem | значения B0..B8 |
| `B_odd_3/_5/_7` | Theorem | ★ нечётные числа Бернулли = 0 |
| `B2_pos/B4_neg/B6_pos` | Theorem | знаковый паттерн |
| `bernoulli_recursion_1..4` | Theorem | рекурсия Бернулли |
| `power_sum/power_sum_1_example/faulhaber_1/power_sum_grows_1/_3/qpow_ge_1/power_sum_diverges` | Definition/Theorem | степенные суммы Фаульхабера, расходимость |
| `zeta_neg/zeta_neg_0/_1/_2/_3` | Definition/Theorem | ★ zeta(-n) через Бернулли |

**Key lemmas (deep):**

- **`zeta_neg_1`** - zeta(-1) = -B2/2 = -1/12 как ТОЧНОЕ Q-число через числа Бернулли — расходящаяся сумма 1+2+3+... регуляризуется в рациональное значение. Питает Casimir/Vacuum-ветвь. P4: правило (Бернулли) даёт Element там, где наивная сумма — role-limit. _(zeta-negative, bernoulli, -1/12)_
- **`B_odd_3`** - Нечётные числа Бернулли зануляются (B3=B5=B7=0) — отвечает за тривиальные нули zeta при отрицательных чётных аргументах (см. ZetaNegative). Структурный факт, доказанный над Q. _(odd-vanishing, trivial-zeros)_

**Uniqueness - score 2 (methods).** Числа Бернулли над Q (рекурсия, нечётные=0, Фаульхабер) и zeta(-n)=−B_{n+1}/(n+1) точно — арифметический движок ветви регуляризации.
> _Caveat:_ Числа Бернулли, Фаульхабер и zeta(-n) — классика анализа; вклад — точная рациональная формализация, не новый результат.

---

## #140 - `src/experimental/CasimirProcess.v` - score 3 (new-framing)

**Casimir energy as a Bernoulli/zeta process: raw sum diverges, regularized value is rational**

- **Topic.** Casimir energies in 1D/3D as rational multiples of zeta(-3); the raw vacuum sum diverges (exceeds 1000), the regularized Casimir value is exactly rational; sign/force (1D negative, 3D positive, attractive), the 240/720 factors, and dimensional vanishing at d=5,9.
- **Role.** Flagship of the experimental Casimir branch; consumes BernoulliNumbers, parallels VacuumEnergy. Self-contained (QArith).
- **Counts.** Qed 33 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ моды вакуума; сырая энергия (расходящаяся); регуляризованная энергия Казимира. _Roles:_ регуляризация = роль; zeta(-3)/Бернулли как источник конечного значения. _Rules:_ casimir = рацио·zeta(-3); raw_energy diverges; casimir_is_bernoulli; force attractive. _P4:_ сырая сумма мод — role-limit (расходится, >1000); значение Казимира — РАЦИОНАЛЬНЫЙ Element через Бернулли; дивергенция дисциплинирована правилом.
- **Classical counterpart.** The Casimir energy via zeta-regularization (E ~ -zeta(-3), the 1/240 and 1/720 factors, attractive force) is classical; NEW is the P4 framing: the raw mode sum is an honestly-divergent role-limit and the finite Casimir value is the Bernoulli-regularized Element, exactly over Q.
- **Tags.** casimir, zeta-regularization, bernoulli, vein-C, new-framing

**Lemmas (8):**

| name | kind | role |
|---|---|---|
| `casimir_1d/casimir_3d/casimir_rational_factor` | Definition | энергии Казимира и рациональный множитель |
| `casimir_1d_verified/_3d_verified/six_times_zeta_neg_3/casimir_720_factor/_rational_factor_verified` | Theorem | значения через zeta(-3), факторы 240/720 |
| `raw_energy_1d/_3d/_diverges/_3d_diverges/raw_1d_exceeds_1000/_at_3/_3d_at_3/_1d_at_9` | Definition/Theorem | ★ сырая энергия расходится |
| `casimir_process_1d/_3d/casimir_is_bernoulli_1d/_3d/casimir_1d_is_rational/_3d_is_rational` | Definition/Theorem | ★ Казимир как процесс = Бернулли, рационален |
| `linear_damping/damping_nonneg/_at_0/damped_energy_1d/damped_1d_example` | Definition/Theorem | демпфирование |
| `casimir_ratio_3d_1d/_1d_negative/_3d_positive/casimir_force_attractive/casimir_240_from_zeta` | Theorem | знаки, притягивающая сила |
| `energy_vanishes_d5/_d9/energy_nonzero_d3/_d7/zeta_neg_1_sign/_3_sign/_5_sign` | Theorem | зануление по размерности; знаки zeta(-n) |
| `casimir_main_theorem` | Theorem | ★ итог ветви Казимира |

**Key lemmas (deep):**

- **`casimir_is_bernoulli_3d`** - Энергия Казимира в 3D = рациональное кратное zeta(-3) = выражается через число Бернулли B4 — конечный Element там, где raw_energy_3d_diverges (role-limit). Классическая zeta-регуляризация переобрамлена как P4-процесс: сумма-правило вместо завершённой расходящейся суммы. _(casimir, zeta-regularization, bernoulli, vein-C-adjacent)_
- **`casimir_force_attractive`** - Сила Казимира притягивающая (знак из zeta(-3)) — содержательное физическое следствие, полученное точной Q-арифметикой. casimir_matches_experiment в AbelRegularization подтверждает значение. _(attractive, force, physical)_

**Uniqueness - score 3 (new-framing).** Энергия Казимира как Bernoulli/zeta-процесс над Q: сырая сумма мод честно расходится (role-limit), регуляризованное значение рационально (Element), сила притягивающая — P4-переобрамление zeta-регуляризации.
> _Caveat:_ Casimir-эффект и zeta-регуляризация классичны (zeta(-3), 1/240); уникальность — в честном P4-разделении расходящегося правила и конечного значения, не в новой физике.

---

## #141 - `src/experimental/CoulombFull3D.v` - score 2 (methods)

**3D Coulomb on a lattice: hydrogen spectrum as a process, honest about degeneracy**

- **Topic.** Scaled 3D Coulomb energies with a centrifugal term, the hydrogen limit, the n^2 degeneracy as a sum, energy ordering by angular momentum, convergence of the s-wave, ionization, and an explicit honest limitation that accidental degeneracy is only partial on the lattice.
- **Role.** Atomic leaf (3D Coulomb) of the experimental branch; parallels CoulombTower. Self-contained (QArith).
- **Counts.** Qed 50 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ масштабированные энергии 3D-Кулона; центробежный член l(l+1). _Roles:_ предел сетки = роль (водородный спектр); вырождение n² как роль-кратность. _Rules:_ scaled_energy_3d; hydrogen_limit_3d; degeneracy_sum = n²; energy_ordering по l. _P4:_ конечная сетка точна (Element); водородный спектр — role-limit процесса (degeneracy_is_cauchy → 0); ПОЛНОЕ (случайное) вырождение НЕ воспроизводится — честное ограничение.
- **Classical counterpart.** The hydrogen 3D Coulomb spectrum E_n ~ -1/n^2, the n^2 degeneracy and centrifugal l(l+1) term are textbook; NEW only as a finite Q-lattice approximation that recovers the spectrum as a convergent PROCESS and is HONEST that full (accidental) degeneracy is not reproduced on the lattice.
- **Tags.** coulomb, hydrogen, honest-limitation, process, methods

**Lemmas (8):**

| name | kind | role |
|---|---|---|
| `centrifugal_scaled/scaled_energy_3d/hydrogen_limit_3d/principal_n/degeneracy_process/sum_nat` | Definition | энергии, центробежный член, кратность |
| `centrifugal_scaled_l0/_nonneg/_positive/_at_l1/_at_l2` | Theorem | свойства центробежного члена |
| `degeneracy_sum_1/_2/_3/_general` | Theorem | ★ кратность уровня = n² |
| `energy_3d_3_0_0/_3_0_1/_3_1_0/_9_0_1/hydrogen_limit_3d_ground/_eq_1d` | Theorem | значения энергий, предел = 1D |
| `partial_degeneracy/no_false_degeneracy/limit_3d_negative/s_wave_ratios/angular_momentum_raises/energy_ordering_s_wave/ground_state_minimum/ground_negative_3d` | Theorem | вырождение, упорядочение по l |
| `p4_finiteness_3d/finite_splitting/principal_n_examples/energy_at_principal/deviation_3d_formula/_positive` | Theorem | конечность, расщепление, отклонение |
| `degeneracy_process_formula/_l0/_positive/centrifugal_upper_bound/Q_bound_over_K/convergence_3d/splitting_vanishes/splitting_rate/degeneracy_is_cauchy/degeneracy_limit_zero/convergence_3d_s_wave` | Theorem | ★ сходимость спектра как процесс |
| `ionization_3d/coulomb_3d_summary/coulomb_3d_honest_limitation/principal_energy_ratio/no_accidental_degeneracy/partial_vs_full_degeneracy/coulomb_3d_complete/process_view_degeneracy/coulomb_3d_main_theorem` | Theorem | ★ ионизация, ЧЕСТНОЕ ограничение про вырождение |

**Key lemmas (deep):**

- **`coulomb_3d_honest_limitation`** - ЧЕСТНОЕ ограничение: диагональная сетка воспроизводит главный спектр −1/n² и n²-кратность, но НЕ полное «случайное» вырождение водорода (no_accidental_degeneracy). Файл явно фиксирует, что именно НЕ доказано — образец калибровки, а не over-claim. _(honest-limitation, degeneracy, hydrogen)_
- **`degeneracy_is_cauchy`** - Водородный спектр восстанавливается как СХОДЯЩИЙСЯ процесс (splitting → 0, degeneracy_limit_zero) на измельчающейся сетке — вена C: спектр есть role-limit правила, а не завершённый объект. _(process, convergence, vein-C)_

**Uniqueness - score 2 (methods).** 3D-Кулон на конечной Q-сетке: спектр −1/n² и n²-кратность как сходящийся процесс, с ЯВНЫМ честным ограничением о невоспроизведении полного вырождения.
> _Caveat:_ Водородный спектр — учебная классика; вклад — конечная Q-аппроксимация-процесс + честная фиксация того, что не доказано, не новая спектроскопия.

---

## #142 - `src/experimental/CoulombTower.v` - score 2 (methods)

**Coulomb tower over Q: hydrogen spectrum as a convergent diagonalization process**

- **Topic.** A grid Coulomb Hamiltonian with kinetic/Coulomb coefficients, optimal grid length, scaled energies, the hydrogen limit matching textbook -1/n^2 with positive but decreasing deviation, ionization, and explicit diagonal-limitation honesty.
- **Role.** Atomic leaf (1D Coulomb tower); parallels CoulombFull3D. Self-contained (QArith).
- **Counts.** Qed 42 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ сеточный гамильтониан Кулона; диагональные энергии. _Roles:_ башня сеток = роль (водородный предел); оптимальная длина сетки. _Rules:_ diag_energy; scaled_energy; hydrogen_limit; deviation_decreases. _P4:_ каждая сетка конечна и точна (Element); водородный спектр — role-limit (convergence_uniform); диагональная аппроксимация имеет честную ошибку.
- **Classical counterpart.** The 1D hydrogen-like spectrum and variational diagonalization are standard; NEW only as a finite Q 'tower' that recovers the textbook spectrum as a convergent process, honest about diagonal-approximation error.
- **Tags.** coulomb, hydrogen, process, honest-limitation, methods

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `inject_Z_S_pos/_neq_0/pos_Q_mul_nonzero/four_n_neq_0/Q_div_swap` | Lemma | Q-арифметические леммы |
| `grid_dx/kinetic_coeff/coulomb_coeff/diag_energy/optimal_L/energy_at_opt/scaled_energy/hydrogen_limit/textbook_hydrogen` | Definition | сетка, коэффициенты, энергии |
| `grid_dx_example/diag_energy_2_9_0/optimal_L_2/energy_at_opt_2_0/scaled_energy_1_0/_3_0/_9_0/_3_1/_formula` | Theorem | конкретные значения |
| `ground_scaled/_negative/excited_scaled/energy_increases_with_n/_closer_with_N` | Theorem | основное/возбуждённые, монотонность |
| `deviation_formula/_positive/_decreases/convergence_general/_uniform` | Theorem | ★ отклонение убывает, равномерная сходимость |
| `hydrogen_limit_ground/_excited/_n2/limit_negative/_increases/ionization/limit_ratio/textbook_ground/_excited/_ratio` | Theorem | ★ водородный предел = учебный −1/n² |
| `diagonal_honest/both_ground_negative/p4_finiteness/hydrogen_convergence_theorem/diagonal_limitation_theorem/hydrogen_summary/coulomb_tower_complete/process_well_defined` | Theorem | ★ честность диагональной аппроксимации |

**Key lemmas (deep):**

- **`hydrogen_convergence_theorem`** - Водородный спектр −1/n² восстанавливается как РАВНОМЕРНО СХОДЯЩИЙСЯ процесс измельчения сетки (deviation_decreases, convergence_uniform) — вена C. Спектр — role-limit правила-диагонализации, не платонистский объект. _(process, convergence, hydrogen, vein-C)_
- **`diagonal_limitation_theorem`** - Честно фиксирует, что диагональная (без вне-диагональных членов) аппроксимация имеет систематическое отклонение — diagonal_honest. Образец калибровки: что воспроизводится (отношения уровней) и что нет. _(honest-limitation, diagonal)_

**Uniqueness - score 2 (methods).** Кулоновская башня над Q: водородный спектр −1/n² как равномерно сходящийся процесс диагонализации сеток, с честной фиксацией ошибки диагонального приближения.
> _Caveat:_ 1D-водородный спектр и вариационная диагонализация стандартны; вклад — конечная Q-башня-процесс + честность, не новая модель.

---

## #143 - `src/experimental/HeliumLattice.v` - score 1 (exposition)

**Helium on a lattice: ground-state estimate and ionization over Q**

- **Topic.** A Z=2 diagonal Coulomb estimate for helium: ground-state energy at small grids, ionization energy, and that adding repulsion raises the energy.
- **Role.** Atomic leaf (helium). Self-contained (QArith).
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ Z=2 диагональные энергии гелия; отталкивание электронов. _Roles:_ оценка основного состояния как роль; ионизация. _Rules:_ he_diagonal; he_ground_estimate; repulsion_raises_energy. _P4:_ конечные оценки на малых сетках (Element); без вне-диагональных членов.
- **Classical counterpart.** Helium ground-state estimation and the role of electron repulsion are textbook; here only a tiny Q-lattice estimate with positive ionization.
- **Tags.** helium, atomic, exposition

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `Z_He/he_diagonal` | Definition | заряд, диагональ гамильтониана |
| `he_diag_K3_00/_11/_02` | Theorem | элементы диагонали |
| `he_ground_estimate/he_ground_K3/_K4` | Definition/Theorem | оценка основного состояния |
| `he_ionization/_K3/_positive_K3/he_ground_below_ion` | Theorem | ионизация положительна |
| `he_no_repulsion/_K3/repulsion_raises_energy/he_first_verified` | Theorem | ★ отталкивание повышает энергию |

**Key lemmas (deep):**

- **`repulsion_raises_energy`** - Электрон-электронное отталкивание повышает энергию гелия (he_no_repulsion vs с отталкиванием) — простое, но корректное следствие на конечной сетке. Содержательной уникальности нет. _(helium, repulsion)_

**Uniqueness - score 1 (exposition).** Оценка основного состояния гелия и положительная ионизация на Q-сетке; отталкивание повышает энергию.
> _Caveat:_ Учебная оценка гелия; конечная диагональная аппроксимация без нового содержания.

---

## #144 - `src/experimental/LambShiftTower.v` - score 2 (methods)

**Lamb-shift tower over Q: honest that the splitting is a lattice artifact, not QED**

- **Topic.** 2S/2P energies and their splitting as a convergent process; the splitting is order-one and nonzero, but the file explicitly argues it is an artifact of breaking accidental degeneracy on the diagonal lattice — the off-diagonal coupling that would give the real Lamb shift is zero.
- **Role.** Atomic leaf (Lamb shift) with an explicit honest-assessment; phase-3 experimental. Self-contained (QArith).
- **Counts.** Qed 42 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ энергии 2S/2P; расщепление как процесс. _Roles:_ расщепление = роль; но здесь — АРТЕФАКТ снятия случайного вырождения, не физический сдвиг Лэмба. _Rules:_ energy_2S/2P; lamb_splitting; off_diagonal_is_zero; splitting_artifact_not_lamb_shift. _P4:_ конечные энергии (Element); расщепление сходится, но честно помечено как артефакт — нужен вне-диагональный член (full_hamiltonian_needed).
- **Classical counterpart.** The Lamb shift is a genuine QED effect splitting the (accidentally degenerate) 2S/2P levels; this file is HONEST that its diagonal lattice splitting is an ARTIFACT of breaking accidental degeneracy, NOT the physical Lamb shift (off-diagonal coupling is zero here).
- **Tags.** lamb-shift, honest, negative-result, atomic, methods

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `energy_2S/energy_2P/lamb_splitting/splitting_limit/off_diagonal_coupling` | Definition | энергии, расщепление, вне-диагональный член |
| `energy_2S_at_3/2P_at_3/splitting_at_1/_3/_9/_19/_0/_computable/_limit_value` | Theorem | значения расщепления |
| `centrifugal_01/splitting_formula/_deviation/_converges/_is_cauchy/_nonzero/_monotone` | Theorem | ★ сходимость расщепления |
| `energy_2S_converges/2P_converges/limits_differ/2S_nonpositive/splitting_deviation_abs/_rate_bound/our_splitting_is_order_one` | Theorem | сходимость энергий, порядок величины |
| `textbook_2S_2P_degenerate/diagonal_breaks_accidental/splitting_artifact_not_lamb_shift/off_diagonal_is_zero/full_hamiltonian_needed` | Theorem | ★ ЧЕСТНО: расщепление = артефакт, не сдвиг Лэмба |
| `p4_splitting_computable/energy_gap_shrinks/splitting_crosses_zero/framework_established/lamb_shift_convergence_theorem/_honest_assessment/_process_view/_framework_theorem` | Theorem | ★ честная оценка, рамка |
| `phase3_verified_results/phase3_open_questions/lamb_shift_complete/experimental_phase3_main/verification_table_entry_partial_degeneracy/_centrifugal_splitting` | Theorem | верифицированное vs открытое |

**Key lemmas (deep):**

- **`splitting_artifact_not_lamb_shift`** - ЯРКИЙ образец честности: файл доказывает, что наблюдаемое расщепление 2S/2P — артефакт снятия случайного вырождения диагональной сеткой, а НЕ физический сдвиг Лэмба (off_diagonal_is_zero, full_hamiltonian_needed). Отрицательный результат с явной формулировкой того, чего не хватает. _(honest, negative-result, lamb-shift, artifact)_
- **`phase3_open_questions`** - Явно перечисляет открытые вопросы фазы 3 рядом с verified-результатами — встроенная калибровка над-claim против реально доказанного. _(honest, open-questions)_

**Uniqueness - score 2 (methods).** Башня сдвига Лэмба над Q со СХОДЯЩИМСЯ расщеплением 2S/2P, но с явным доказательством, что оно — артефакт диагональной сетки, не физический сдвиг Лэмба (нужен вне-диагональный член).
> _Caveat:_ Сдвиг Лэмба — настоящий КЭД-эффект; здесь его НЕТ — ценность файла в честной фиксации артефакта и открытых вопросов, а не в воспроизведении физики.

---

## #145 - `src/experimental/LithiumLattice.v` - score 1 (exposition)

**Lithium on a lattice: Slater screening and effective charge over Q**

- **Topic.** Z=3 lithium with Slater 1s screening, an inner-electron count, effective charge Z_eff, outer/inner/total energies (all negative) and a positive ionization energy.
- **Role.** Atomic leaf (lithium). Self-contained (QArith).
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ Z=3; экранирование Слейтера; эффективный заряд Z_eff. _Roles:_ экранирование = роль (уменьшает эффективный заряд внешнего электрона). _Rules:_ Z_effective_Li = Z − sigma; энергии отрицательны; ионизация положительна. _P4:_ конечные оценки (Element); экранирование как простое правило.
- **Classical counterpart.** Lithium via Slater screening and an effective nuclear charge Z_eff is textbook atomic physics; here only a tiny Q instance.
- **Tags.** lithium, screening, atomic, exposition

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `Z_Li/slater_1s_screen/n_inner_Li/sigma_Li/Z_effective_Li` | Definition | заряд, экранирование, Z_eff |
| `Z_eff_Li_value/_positive` | Theorem | значение Z_eff |
| `li_outer_energy/_value/li_inner_energy/_value/li_total_energy` | Definition/Theorem | энергии внешнего/внутреннего/всего |
| `li_inner_negative/li_outer_negative/li_ionization/_positive` | Theorem | знаки энергий, ионизация |

**Key lemmas (deep):**

- **`Z_eff_Li_value`** - Эффективный заряд лития Z_eff = Z − sigma по Слейтеру — стандартная оценка экранирования над Q. Уникальности нет. _(lithium, screening, z-eff)_

**Uniqueness - score 1 (exposition).** Литий на Q-сетке: экранирование Слейтера, эффективный заряд, отрицательные энергии, положительная ионизация.
> _Caveat:_ Учебная модель экранирования; конечный Q-инстанс без нового содержания.

---

## #146 - `src/experimental/TwoParticleLattice.v` - score 1 (exposition)

**Two-particle lattice over Q: tensor index, nuclear attraction, electron repulsion**

- **Topic.** A two-particle Coulomb lattice: the product dimension (quadratic in grid), an injective flatten index, nuclear potential at center, electron repulsion (same-site/adjacent), and per-particle kinetic energy.
- **Role.** Atomic-composition infrastructure (two-electron). Self-contained (QArith).
- **Counts.** Qed 14 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ двухчастичное пространство (тензор); индекс flatten. _Roles:_ flatten = роль-кодирование пары в один индекс; потенциалы как роли. _Rules:_ two_particle_dim = K²; flatten_injective; nuclear/repulsion потенциалы. _P4:_ конечная двухчастичная сетка (Element); размерность растёт квадратично.
- **Classical counterpart.** Two-particle Hilbert space as a tensor product with nuclear attraction + electron repulsion is standard; here only a small Q-lattice with an explicit flatten index.
- **Tags.** two-particle, tensor, atomic, exposition

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `two_particle_dim/flatten/nat_dist/nuclear_potential/electron_repulsion/kinetic_per_particle/two_particle_diag` | Definition | размерность, индекс, потенциалы |
| `dim_K3/_K4/_K5/dim_quadratic` | Theorem | размерность = K² |
| `flatten_bound/_injective/_origin` | Theorem | ★ flatten инъективен |
| `nuclear_He_at_center/repulsion_same/_adjacent/_same_site/_symmetric/kinetic_at_K3/nat_dist_sym` | Theorem | потенциалы, симметрия |

**Key lemmas (deep):**

- **`flatten_injective`** - Инъективное кодирование пары частиц в один индекс (flatten) — корректная тензорная индексация над конечной сеткой. Инфраструктура для двухэлектронных оценок. _(tensor, flatten, injective)_

**Uniqueness - score 1 (exposition).** Двухчастичная Q-сетка: квадратичная размерность, инъективный flatten-индекс, ядерное притяжение и электронное отталкивание.
> _Caveat:_ Стандартная тензорная конструкция двухчастичного пространства; инфраструктура без нового результата.

---

## #147 - `src/experimental/VacuumEnergy.v` - score 3 (new-framing)

**Vacuum energy dissolved over Q: raw ZPE diverges, regularized value is rational (no infinity)**

- **Topic.** Zero-point energy in 1D/3D as half a power sum: the raw vacuum energy is increasing and NOT Cauchy (diverges), but it equals the Casimir/Bernoulli rational value after regularization; 'the vacuum-energy problem is dissolved' and 'no infinity' are proven.
- **Role.** Companion to CasimirProcess; the 'problem dissolution' statement of the vacuum branch. Self-contained (QArith).
- **Counts.** Qed 44 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ нулевая энергия (ZPE) 1D/3D; половина степенной суммы. _Roles:_ регуляризация = роль; Казимир/Бернулли как конечное значение. _Rules:_ zpe = ½·power_sum; vacuum_not_cauchy (расходится); vacuum_casimir; no_infinity. _P4:_ сырая ZPE — role-limit (НЕ Коши, расходится); регуляризованное значение — РАЦИОНАЛЬНЫЙ Element; «проблема вакуумной энергии РАСТВОРЕНА» — теорема (vein C).
- **Classical counterpart.** Zero-point/vacuum energy and its zeta-regularization to a finite Casimir value are classical; NEW is the P4 framing: the divergence is DISSOLVED — the raw ZPE sum is honestly not Cauchy (role-limit), the regularized value is a rational Element, so 'no infinity' is a theorem.
- **Tags.** vacuum-energy, zeta-regularization, no-infinity, vein-C, new-framing

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `Qpow_exp_1/partial_sum_scale_local/_ext/Qle_Qabs` | Lemma | Q-арифметические леммы |
| `zpe_1d/vacuum_energy_1d/zpe_3d/vacuum_energy_3d/find_stage_1d` | Definition | ZPE и вакуумная энергия |
| `vacuum_1d_at_0/_1/_2/_9/3d_at_0/_3/zpe_1d_pos/3d_nonneg/_pos` | Theorem | значения, положительность |
| `vacuum_1d_is_half_power_sum/3d_is_half_power_sum/_increasing/_nonneg/_diverges/3d_diverges/1d_faulhaber` | Theorem | ★ ½ степенной суммы; расходится |
| `vacuum_1d_not_cauchy/3d_not_cauchy` | Theorem | ★ сырая ZPE НЕ Коши |
| `vacuum_casimir_1d/3d/vacuum_finite_1d/3d/vacuum_step_zpe_1d/3d/vacuum_three_level_1d/3d/vacuum_casimir_bridge/1d_positive/3d_positive` | Theorem | ★ регуляризованное = Казимир, конечно |
| `vacuum_problem_dissolved/_proof/dissolution_1d/3d/no_infinity_1d/3d/vacuum_energy_summary_1d/3d/vacuum_main_theorem` | Theorem | ★ ПРОБЛЕМА РАСТВОРЕНА, нет бесконечности |

**Key lemmas (deep):**

- **`vacuum_problem_dissolved`** - Флагман: «проблема вакуумной энергии растворена» как ТЕОРЕМА. Связка vacuum_1d_not_cauchy (сырая ZPE расходится = role-limit) + vacuum_casimir (регуляризованное значение рационально = Element) делает «нет бесконечности» доказанным фактом, а не риторикой. Чистая вена C: правило-сумма заменяет завершённый расходящийся объект. _(vacuum-dissolved, no-infinity, vein-C)_
- **`vacuum_1d_not_cauchy`** - Сырая нулевая энергия ЧЕСТНО не Коши (расходится) — файл не прячет расходимость, а доказывает её, затем дисциплинирует регуляризацией. Образец честного P4-разделения. _(divergence, not-cauchy, honest)_

**Uniqueness - score 3 (new-framing).** Вакуумная энергия над Q: сырая ZPE доказуемо расходится (role-limit), регуляризованное значение рационально (Element=Казимир), «нет бесконечности / проблема растворена» — теоремы. Вена C.
> _Caveat:_ Нулевая энергия и её zeta-регуляризация классичны; уникальность — в P4-формулировке «растворения» как теоремы (расходимость + конечное значение раздельно), не в новой физике вакуума.

---

## #148 - `src/experimental/ZetaNegative.v` - score 2 (methods)

**Negative-argument zeta over Q: zeta(-n) via Bernoulli, trivial zeros, finite vs divergent**

- **Topic.** zeta(-4..-8) via Bernoulli, the trivial zeros at -2,-4,-6,-8 (from odd Bernoulli vanishing), Faulhaber power sums, the contrast that naive natural/cube sums diverge while zeta(-1),zeta(-3) are finite, and that zeta(-1),zeta(-3) are nonzero.
- **Role.** Companion to BernoulliNumbers; the trivial-zeros leaf. Self-contained (QArith).
- **Counts.** Qed 32 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ значения zeta(-n); числа Бернулли B_{n+1}. _Roles:_ тривиальный нуль = роль (zeta(-2k)=0 из B_odd=0); регуляризованное конечное значение. _Rules:_ zeta_neg n = −B_{n+1}/(n+1); trivial_zero_at_2/4/6/8; naive_sum_diverges vs zeta_neg_finite. _P4:_ наивные суммы — role-limit (расходятся); zeta(-n) — конечный Element через Бернулли; тривиальные нули — точные рациональные нули.
- **Classical counterpart.** zeta(-n) = -B_{n+1}/(n+1), the trivial zeros at negative even integers, and Faulhaber sums are classical; NEW only as exact rational Coq values plus the honest contrast that naive sums diverge while regularized zeta(-n) is finite.
- **Tags.** zeta-negative, bernoulli, trivial-zeros, methods

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `zeta_neg_4/_5/_6/_7/_8/B9_odd_zero` | Theorem | значения zeta(-4..-8) |
| `trivial_zero_at_2/_4/_6/_8/_via_bernoulli_3/_5/_7` | Theorem | ★ тривиальные нули из B_odd=0 |
| `power_sum_2_example/faulhaber_2_at_3/3_at_2/3_square/3_square_5` | Theorem | суммы Фаульхабера |
| `harmonic_diverges/sum_of_naturals_diverges/sum_of_cubes_diverges/naive_sum_exceeds_100` | Theorem | ★ наивные суммы расходятся |
| `zeta_neg_1_is_finite/_3_is_finite/zeta_2_converges/_3_converges/_neg_1_uses_B2/_neg_3_uses_B4/zeta_2_bounded` | Theorem | ★ регуляризованные конечны |
| `zeta_neg_1_nonzero/_neg_3_nonzero/_neg_5_nonzero` | Theorem | zeta(-1),(-3),(-5) ≠ 0 |

**Key lemmas (deep):**

- **`trivial_zero_at_2`** - Тривиальный нуль zeta(-2)=0 выводится из зануления нечётных чисел Бернулли (B3=0) — точный рациональный нуль, а не приближение. Связывает арифметику Бернулли с нулями дзеты (ср. zeta/ кластер). _(trivial-zero, bernoulli, zeta)_
- **`sum_of_cubes_diverges`** - Наивная сумма кубов расходится (role-limit), тогда как zeta(-3) конечна через B4 — честный контраст «расходящееся правило vs регуляризованный Element». Питает Casimir/Vacuum. _(divergence, honest, regularization)_

**Uniqueness - score 2 (methods).** zeta(-n) над Q через Бернулли: тривиальные нули из B_odd=0, точные конечные значения против расходящихся наивных сумм.
> _Caveat:_ zeta(-n)=−B_{n+1}/(n+1) и тривиальные нули — классика; вклад — точные Q-значения + честный контраст конечного и расходящегося, не новый результат.

