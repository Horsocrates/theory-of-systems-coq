# Database - cluster `analysis`

_Generated from `analysis.json` by `generate.ps1` - do not edit by hand; edit the JSON._

**37 files / 612 Qed.** Score distribution: s5=0 / s4=1 / s3=10 / s2=15 / s1=11 / s0=0

---

## #29 - `src/analysis/BolzanoWeierstrass.v` - score 4 (synthesis+observation)

**Bolzano-Weierstrass without Dependent Choice: deterministic bisection (vein B)**

- **Topic.** A bounded sequence's cluster point is built by a deterministic bisection state machine (bw_step/bw_iter: always take the half with infinitely many terms), giving nested intervals whose endpoints are Cauchy; the limit is a cluster point. Monotone-bounded and decreasing-bounded Cauchy as corollaries.
- **Role.** Vein B FLAGSHIP (no-DC selection). The strongest no-AC result in the repo (per uniqueness-map). Uses classic only for the pigeonhole (infinitely_many_in), NOT for the subsequence.
- **Counts.** Qed 26 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; CauchySeq (CauchyReal)
- **E/R/R.** _Elements:_ ограниченная последовательность s; интервалы-состояния BWState (lo,hi). _Roles:_ точка сгущения как role-limit; выбор половины = роль ПРАВИЛА (а не DC-оракула). _Rules:_ bw_step: брать половину с бесконечно многими членами; bw_iter итерирует; ширина →0. _P4:_ подпоследовательность заменена ДЕТЕРМИНИРОВАННЫМ правилом (одна Fixpoint bw_iter), не выбором; честно: classic нужен для НЕРАЗРЕШИМОГО критерия «бесконечно много в [lo,hi]» (pigeonhole) — вена B локализует цену.
- **Classical counterpart.** Bolzano-Weierstrass (every bounded sequence has a convergent subsequence) classically uses Dependent Choice to pick the subsequence; NEW is replacing DC by a DETERMINISTIC bisection rule ('go left if the left half holds infinitely many terms') -- one Fixpoint bw_iter, not a choice-extracted subsequence. Honest cost: classic for the undecidable 'infinitely-many-in' pigeonhole.
- **Tags.** bolzano-weierstrass, no-DC, no-AC, vein-B, bisection, deterministic, P4

**Lemmas (12):**

| name | kind | role |
|---|---|---|
| `bounded_seq/infinitely_many_in` | Definition | ограниченность; бесконечно много членов в интервале |
| `infinite_pigeonhole` | Lemma | бесконечно много в [a,b] ⟹ в одной из половин (использует classic) |
| `BWState/bw_mid/bw_step_left/bw_step/bw_iter` | Record/Definition/Fixpoint | ★ детерминированная машина бисекции |
| `bw_step_valid/width/nested_left/nested_right/preserves_infinite` | Lemma | шаг корректен, делит ширину, вложен, сохраняет бесконечность |
| `bw_iter_valid/left_inc/right_dec/preserves_infinite` | Lemma | итерация: валидна, монотонна, сохраняет бесконечность |
| `bw_left_mono/right_mono/width_bound/width_to_zero` | Lemma | концы монотонны, ширина →0 |
| `bw_left_cauchy/right_cauchy/trapped_seq_cauchy/endpoints_equiv` | Lemma | ★ концы — последовательности Коши, эквивалентны |
| `bw_infinitely_many/bw_term_exists` | Lemma | в каждом интервале есть член последовательности |
| `is_cluster_point` | Definition | точка сгущения как CauchySeq |
| `bolzano_weierstrass` | Theorem | ★ всякая ограниченная последовательность имеет точку сгущения (без DC) |
| `monotone_bounded_cauchy/decreasing_bounded_cauchy` | Theorem | монотонная ограниченная — Коши |
| `bw_left_bounded/right_bounded` | Lemma | концы ограничены |

**Key lemmas (deep):**

- **`bolzano_weierstrass`** - Bolzano-Weierstrass БЕЗ Dependent Choice: вместо извлечения подпоследовательности оракулом — ОДНА детерминированная Fixpoint bw_iter, которая на каждом шаге берёт половину с бесконечно многими членами. Точка сгущения = предел концов вложенных интервалов (Cauchy). Сильнейший no-AC результат репо: DC заменён правилом, цена (classic) локализована РОВНО в неразрешимом pigeonhole-критерии. _(bolzano-weierstrass, no-DC, vein-B, deterministic-bisection)_
- **`infinite_pigeonhole`** - Бесконечно много членов в [a,b] ⟹ бесконечно много в одной из половин — единственное место, где нужен classic (критерий «infinitely-many-in» неразрешим, Π-предикат). Честная граница: всё ОСТАЛЬНОЕ (само правило, цепи Коши) аксиомо-свободно. _(pigeonhole, classic, honest-cost)_

**Uniqueness - score 4 (synthesis+observation).** Bolzano-Weierstrass с заменой Dependent Choice ДЕТЕРМИНИРОВАННЫМ правилом бисекции (одна Fixpoint, не выбор подпоследовательности); цена classic локализована в неразрешимом pigeonhole — сильнейший no-AC результат репо (вена B).
> _Caveat:_ Бисекционное доказательство BW стандартно (Bishop); уникальность — в систематической замене DC правилом + честной локализации цены, не в теореме.

---

## #30 - `src/analysis/CauchySchwarz.v` - score 2 (methods)

**Cauchy-Schwarz over rational vectors**

- **Topic.** Dot product and squared norm on list Q, the Cauchy-Schwarz inequality via the nonnegative quadratic norm_sq(t u - v), and concrete 2D/3D examples.
- **Role.** Analysis foundation (inner-product inequality over Q). Self-contained.
- **Counts.** Qed 17 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith List
- **E/R/R.** _Elements:_ рациональные векторы list Q; скалярное произведение dot. _Roles:_ норма/скалярное произведение как роли; CS-неравенство. _Rules:_ \|u−t·v\|²≥0 ⟹ дискриминантное CS-неравенство. _P4:_ конечномерные Q-векторы, всё вычислимо (Element); CS через неотрицательность квадрата.
- **Classical counterpart.** The Cauchy-Schwarz inequality is classical; NEW: nothing -- an explicit Q-vector (list Q) proof via the discriminant of \|u - t v\|^2 >= 0, with concrete examples.
- **Tags.** cauchy-schwarz, inner-product, Q-vectors, methods

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `dot/norm_sq/scalar_mult/vec_sub/vec_add` | Fixpoint/Definition | операции над Q-векторами |
| `sq_nonneg/norm_sq_nonneg/dot_nil_l/r/dot_comm` | Lemma | квадраты неотрицательны, dot коммутативен |
| `length_scalar_mult/vec_sub/dot_scale/dot_sub_l/norm_sq_sub_expand` | Lemma | линейность и раскрытие нормы разности |
| `norm_sq_zero_dot_zero/Qmult_Qdiv_nonneg_helper` | Lemma | вспомогательные |
| `cauchy_schwarz` | Theorem | ★ неравенство Коши-Шварца (через дискриминант) |
| `cs_concrete_34_10/11_11/12_34/3d` | Lemma | конкретные примеры (включая 3-4-5) |

**Key lemmas (deep):**

- **`cauchy_schwarz`** - Коши-Шварц над Q-векторами через неотрицательность квадрата нормы \|u−t·v\|²≥0 (дискриминантный аргумент). Element-сторона: конечномерное, точная Q-арифметика. Та же дискриминантная идея, что в вене A (квадрат ⟺ свойство). _(cauchy-schwarz, discriminant, Q-vectors)_

**Uniqueness - score 2 (methods).** Коши-Шварц над рациональными векторами через дискриминант нормы разности + конкретные примеры.
> _Caveat:_ CS — фундаментальная классика; вклад — явная Q-формализация, не новый результат.

---

## #31 - `src/analysis/CompactOperator.v` - score 2 (methods)

**Self-adjoint 2x2 operators over Q: eigenpairs, orthogonality, trace/det**

- **Topic.** Linear operators as list-of-lists over Q, trace/det, self-adjointness, eigenpairs of diagonal and symmetric 2x2 matrices, orthogonal eigenvectors, and trace=sum/det=product of eigenvalues.
- **Role.** Finite-dim spectral theory over Q (toward SpectralTheoremCompact). Self-contained.
- **Counts.** Qed 20 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith List
- **E/R/R.** _Elements:_ операторы list(list Q); 2x2 матрицы; собственные пары. _Roles:_ самосопряжённость как роль; собственное значение/вектор как роли спектра. _Rules:_ trace=сумма, det=произведение собственных значений; ортогональность собственных векторов. _P4:_ конечномерный спектр над Q вычислим точно (Element); связь дискриминанта 2x2 с рациональностью собственных значений (вена A).
- **Classical counterpart.** Self-adjoint operators, real eigenvalues, orthogonal eigenvectors, and trace=sum/det=product of eigenvalues are classical; NEW: nothing -- explicit 2x2 Q-matrix eigenpairs (diagonal and symmetric) with computed orthogonality.
- **Tags.** spectral, self-adjoint, eigenvalue, 2x2, methods

**Lemmas (9):**

| name | kind | role |
|---|---|---|
| `l2_inner/l2_norm_sq/vec_scale/vec_add` | Fixpoint/Definition | L2 скалярное произведение над Q |
| `LinOp/apply_op/mat_entry/mat_trace/det_2x2` | Definition | операторы, след, определитель 2x2 |
| `is_self_adjoint/is_eigenpair_q` | Definition | самосопряжённость, собственная пара |
| `trace_2x2/det_2x2_compute` | Lemma | вычисление следа/определителя |
| `diagonal_self_adjoint/symmetric_self_adjoint` | Lemma | диагональные/симметричные самосопряжены |
| `eigenvalue_diagonal_1/2/eigenvectors_orthogonal_diagonal` | Lemma | собственные пары диагональной + ортогональность |
| `eigenvalue_sum_trace/eigenvalue_prod_det` | Lemma | ★ след=сумма, det=произведение собственных значений |
| `eigenpair_symmetric_3/1/eigenvectors_orthogonal_symmetric/trace_det_eigenvalues` | Lemma | собственные пары симметричной 2x2 |
| `rotation_90_apply/projection_x_apply/eigenpair_tail_q` | Lemma | конкретные операторы |

**Key lemmas (deep):**

- **`eigenvalue_sum_trace`** - След = сумма собственных значений (и det=произведение) для 2x2 над Q — конечномерное ядро спектральной теории, точно вычислимое. Дискриминант tr²−4det решает рациональность собственных значений (прямая связь с веной A / BoundaryDecidability). _(spectral, trace, discriminant-link)_

**Uniqueness - score 2 (methods).** Самосопряжённые 2x2 операторы над Q: собственные пары, ортогональность, след=сумма/det=произведение — конечномерный спектр точно.
> _Caveat:_ Спектральные факты 2x2 классичны; вклад — явная Q-формализация, связь дискриминанта с веной A.

---

## #32 - `src/analysis/Continuity.v` - score 1 (exposition)

**Continuity, uniform continuity, Lipschitz over Q**

- **Topic.** Pointwise/uniform continuity and Lipschitz on an interval over Q; Lipschitz implies uniform continuity, identity is Lipschitz, constants/sums uniformly continuous.
- **Role.** Analysis foundation (continuity over Q). Self-contained.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ функции Q→Q на интервале [a,b]; константы Липшица. _Roles:_ непрерывность/равномерная/Липшиц как роли регулярности. _Rules:_ Lipschitz_on K ⟹ uniformly_continuous; замкнутость по сумме. _P4:_ регулярность определена эпсилон-дельта над Q (Element); Липшиц даёт явный модуль.
- **Classical counterpart.** Continuity, uniform continuity, the Lipschitz condition and Lipschitz=>uniform continuity are classical; NEW: nothing -- Q-formalized definitions and basic closure (sum, identity, constants).
- **Tags.** continuity, lipschitz, uniform-continuity, exposition

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `continuous_on/uniformly_continuous_on/Lipschitz_on` | Definition | непрерывность, равномерная, Липшиц над Q |
| `lipschitz_uniform/uniformly_continuous_pointwise` | Theorem | ★ Липшиц ⟹ равномерная ⟹ точечная |
| `uniformly_continuous_const/identity_lipschitz/identity_uniformly_continuous/uniformly_continuous_sum` | Theorem | константы/тождество/сумма |

**Key lemmas (deep):**

- **`lipschitz_uniform`** - Липшицевость даёт равномерную непрерывность с ЯВНЫМ модулем (delta = eps/K) над Q — Element-сторона: регулярность с вычислимым свидетелем, основа всех оценок ошибок в calculus-цепочке (FTC/Picard). _(lipschitz, uniform-continuity, explicit-modulus)_

**Uniqueness - score 1 (exposition).** Непрерывность/равномерная/Липшиц над Q + базовая замкнутость; Липшиц ⟹ равномерная с явным модулем.
> _Caveat:_ Стандартные определения; ценность инфраструктурная (под calculus-цепочку).

---

## #33 - `src/analysis/DominatedConvergence.v` - score 2 (methods)

**Dominated convergence for step functions over Q**

- **Topic.** Step functions over Q, their L1 integral/norm, boundedness and domination, L1 convergence/Cauchy, a dominated-convergence theorem for step functions, monotone-bounded L1-Cauchy, and a worked DCT example.
- **Role.** Constructive integration over Q (DCT, step-function side). Self-contained.
- **Counts.** Qed 20 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith List
- **E/R/R.** _Elements:_ ступенчатые функции StepFun (list Step); их L1-интеграл/норма. _Roles:_ доминирование как роль-мажоранта; L1-сходимость как роль предела. _Rules:_ dominated M; l1_converges/l1_cauchy; DCT для ступенчатых. _P4:_ DCT на ступенчатых функциях конструктивен (Element); полный DCT для измеримых — role-limit.
- **Classical counterpart.** Lebesgue's dominated convergence theorem is classical and measure-theoretic; NEW: only a step-function (constructive) version over Q with L1 convergence and a worked DCT instance.
- **Tags.** DCT, integration, step-functions, L1, methods

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `Step/StepFun/step_integral/step_fun_integral/abs/norm/diff/bounded` | Record/Definition/Fixpoint | ступенчатые функции и L1-операции |
| `dominated/l1_converges/l1_cauchy/integral_converges/integral_cauchy` | Definition | доминирование и сходимость |
| `bounded_nil/singleton/step_integral/total_width/norm_bounded_by_width/norm_nonneg` | Lemma | оценки интеграла через ширину |
| `constant_integral_converges/cauchy/constant_converges/dominated` | Lemma | константный случай сходится/доминирован |
| `dominated_convergence_step` | Theorem | ★ DCT для ступенчатых функций |
| `monotone_increasing/monotone_bounded_cauchy` | Definition/Lemma | монотонная ограниченная — L1-Коши |
| `example_constant_convergence/dominated/integral_stable/example_dct/zero_fun_integral/bounded_zero_norm/integral_converges_refl` | Lemma | проработанные примеры |

**Key lemmas (deep):**

- **`dominated_convergence_step`** - DCT в конструктивной форме для ступенчатых функций над Q: при общей мажоранте M L1-сходимость функций даёт сходимость интегралов. Element-сторона теории интеграла; полный DCT для измеримых — role-limit. _(DCT, step-functions, L1, constructive)_

**Uniqueness - score 2 (methods).** Доминированная сходимость для ступенчатых функций над Q (L1-сходимость ⟹ сходимость интегралов) + проработанный пример.
> _Caveat:_ DCT классична (Лебег); вклад — конструктивная ступенчатая версия над Q, не полный DCT.

---

## #34 - `src/analysis/FourierApplications.v` - score 1 (exposition)

**DFT applications on the 4-cycle over Q: heat kernel, convolution**

- **Topic.** DFT-4 basis, heat-kernel eigenvalues per mode, the convolution-impulse identity, adjacency-squared eigenvalues, normalized heat kernel and the zero-mode spectral gap -- all exact over Q.
- **Role.** Fourier sub-thread (DFT on Z/4 applications). Self-contained.
- **Counts.** Qed 14 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ сигналы nat→Q на 4-цикле; ДПФ-базис phi_k. _Roles:_ собственные значения теплового ядра/смежности как роли мод. _Rules:_ dft_4; heat_eigenvalue; свёртка = умножение в частотной области. _P4:_ ДПФ на Z/4 — конечное точное вычисление над Q (Element).
- **Classical counterpart.** The discrete Fourier transform on Z/4, the heat-kernel eigenvalues, convolution-as-multiplication and the impulse identity are classical signal processing; NEW: nothing -- exact Q computations on the 4-cycle.
- **Tags.** fourier, DFT, heat-kernel, convolution, exposition

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `cycle_eigenvalue_4/heat_eigenvalue_4/phi_0..3/inner4/dft_4/cycle_adj_4/adj_action_4` | Definition | ДПФ-4 базис, тепловое ядро, смежность |
| `heat_eigen0_step1/2/eigen1_vanishes/eigen3_vanishes/eigen2_step1/2` | Lemma | собственные значения теплового ядра по модам |
| `heat_impulse_4/heat_K0_is_impulse/K1_is_adj` | Definition/Lemma | тепловое ядро как импульс/смежность при малом K |
| `conv_4/conv_impulse_identity` | Definition/Lemma | ★ свёртка с импульсом = тождество |
| `adj2_action_4/adj_squared_eigen0/2/heat_K2_via_adj2` | Definition/Lemma | квадрат смежности |
| `normalized_heat_4/normalized_heat_even_j0/spectral_gap_zero_modes` | Definition/Lemma | нормированное ядро, нулевая мода |

**Key lemmas (deep):**

- **`conv_impulse_identity`** - Свёртка с импульсом = тождество — конкретная проверка теоремы о свёртке на Z/4 над Q (свёртка во времени = умножение в частоте). Element-сторона ДПФ: всё точно, конечно. _(DFT, convolution, exact)_

**Uniqueness - score 1 (exposition).** Приложения ДПФ на 4-цикле над Q (тепловое ядро, свёртка-импульс) — точные конечные вычисления.
> _Caveat:_ ДПФ и свёртка классичны; ценность — точная Q-формализация подветки, не новый результат.

---

## #35 - `src/analysis/FourierBasis.v` - score 1 (exposition)

**The DFT eigenbasis on Z/4 over Q: orthogonality and the adjacency spectrum**

- **Topic.** The four DFT modes phi_0..3, the adjacency eigenvalues per mode, pairwise orthogonality, norms, DFT of test signals, IDFT inverts DFT, adjacency symmetric, trace = sum of eigenvalues.
- **Role.** Fourier sub-thread (the eigenbasis). Self-contained.
- **Counts.** Qed 19 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ ДПФ-моды phi_0..3 на Z/4; оператор смежности. _Roles:_ ДПФ-базис как собственный базис циркулянта; ортогональность. _Rules:_ adj_action; eigenvalue per mode; inner4 ортогональность. _P4:_ собственный базис конечен и точен над Q (Element).
- **Classical counterpart.** The DFT eigenbasis of a circulant (adjacency) operator, orthogonality, Parseval and trace=sum-of-eigenvalues are classical; NEW: nothing -- exact Q verification on Z/4.
- **Tags.** fourier, DFT, eigenbasis, orthogonality, exposition

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `cycle_adj_4/adj_action_4/cycle_eigenvalue_4/phi_0..3/inner4/dft_4/idft_4` | Definition | смежность, ДПФ-базис, прямое/обратное ДПФ |
| `eigenvalue_0_site0/1/all/eigenvalue_2/1/3_all` | Lemma | ★ phi_k — собственные векторы смежности |
| `ortho_01..23/norm_phi0/1` | Lemma | ★ попарная ортогональность и нормы |
| `dft_constant_3/alternating_1/idft_inverts_dft_concrete` | Lemma | ДПФ тестовых сигналов; обратимость |
| `adj_symmetric/trace_equals_eigensum` | Lemma | смежность симметрична; след = сумма с.з. |

**Key lemmas (deep):**

- **`eigenvalue_0_all`** - ДПФ-моды phi_k — собственные векторы оператора смежности (циркулянта) над Q, точно. Element-сторона спектральной теории на конечном цикле: диагонализация циркулянта ДПФ-базисом проверена вычислением. _(DFT, eigenbasis, circulant)_

**Uniqueness - score 1 (exposition).** ДПФ-собственный базис циркулянта на Z/4 над Q: ортогональность, спектр смежности, обратимость ДПФ.
> _Caveat:_ Диагонализация циркулянтов ДПФ классична; ценность — точная Q-проверка.

---

## #36 - `src/analysis/FourierBranchSynthesis.v` - score 1 (exposition)

**Fourier branch grand synthesis**

- **Topic.** A six-step synthesis (eigenvalues, Laplacian diagonalized, dispersion, vacuum, reconstruction, transfer) culminating in a grand synthesis theorem over the Fourier sub-branch.
- **Role.** Fourier sub-thread synthesis (cites the other Fourier files). Self-contained.
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** ToS analysis.Fourier* files
- **E/R/R.** _Elements:_ результаты Fourier-подветки. _Roles:_ синтез-цепочка как роль-сборка. _Rules:_ six steps собраны в grand synthesis. _P4:_ сборка уже доказанных конечных результатов (Element).
- **Classical counterpart.** Assembling DFT diagonalization + dispersion + vacuum energy + reconstruction into one chain is exposition; NEW: nothing -- a synthesis theorem over the Fourier sub-branch results.
- **Tags.** fourier, synthesis, exposition

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `step1_eigenvalues/step2_laplacian_diagonalized/step3_dispersion/step4_vacuum/step5_reconstruction/step6_transfer` | Theorem | шесть шагов Fourier-подветки |
| `fourier_branch_grand_synthesis` | Theorem | ★ гранд-синтез подветки |

**Key lemmas (deep):**

- **`fourier_branch_grand_synthesis`** - Сборка всей Fourier-подветки в одну цепочку (собственные значения → диагонализация лапласиана → дисперсия → вакуум → реконструкция → передача). Чисто синтез уже доказанных конечных результатов. _(synthesis, fourier)_

**Uniqueness - score 1 (exposition).** Гранд-синтез Fourier-подветки (6 шагов в одну цепочку).
> _Caveat:_ Чистая сборка экспозиции; 0 нового содержания.

---

## #37 - `src/analysis/FourierCayleyConnection.v` - score 2 (new-framing)

**Cayley transform linking Fourier eigenvalues to transfer/Green spectra over Q**

- **Topic.** The Cayley eigenvalue map, its values (rational, e.g. 3/5, -5/13), the 4-cycle relation, the transfer eigenvalue, a 2-circulant trace/det, the Green spectral function, and a synthesis.
- **Role.** Fourier sub-thread bridge to Cayley (rational spectra). Self-contained.
- **Counts.** Qed 16 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ собственные значения; Cayley-отображение лямбда. _Roles:_ Cayley-преобразование как мост лапласиан↔передача/Грин. _Rules:_ cayley_eigenvalue; transfer/green spectral. _P4:_ Cayley-образы РАЦИОНАЛЬНЫ (3/5, −5/13 — пифагоровы!) — Element; связь с RationalSO3/3-4-5.
- **Classical counterpart.** The Cayley transform of an eigenvalue (lambda -> (1-lambda/...)) relating Laplacian and transfer/Green spectra is standard; NEW: only exact Q values linking the Fourier branch to the Cayley/SO transform.
- **Tags.** fourier, cayley, rational-spectrum, new-framing

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `cayley_eigenvalue/qpow_conn/transfer_eigenvalue/circ2_ev_plus/minus/green_spectral` | Definition | Cayley, передача, Грин-спектр |
| `cayley_zero/two/at_0_is_1/at_1/at_1_le_1/at_3/cycle4_0/1/2` | Lemma | ★ значения Cayley (3/5, −5/13 — рациональны) |
| `transfer_K0/K1/circ2_trace/det/green_K0/K1` | Lemma | передача и Грин при малом K |
| `fourier_cayley_synthesis` | Theorem | синтез связи |

**Key lemmas (deep):**

- **`cayley_at_3`** - Cayley-образ собственного значения = −5/13 (и 3/5 при lambda=1) — РАЦИОНАЛЬНЫЕ значения, причём пифагоровы (3/5, 5/13). Связывает Fourier-спектр с рациональными SO-вращениями (RationalSO3/3-4-5): Element-сторона. _(cayley, rational-spectrum, pythagorean)_

**Uniqueness - score 2 (new-framing).** Cayley-преобразование связывает Fourier-собственные значения с передаточным/Грин-спектром РАЦИОНАЛЬНЫМИ (пифагоровыми) значениями — мост к RationalSO3.
> _Caveat:_ Cayley-преобразование спектра стандартно; интересна лишь рациональность/пифагоровость значений.

---

## #38 - `src/analysis/FourierCoefficients.v` - score 1 (exposition)

**DFT-2 coefficients, Parseval, and the i-power cycle over Q**

- **Topic.** DFT-2 of delta/const/oscillating signals, DFT-2 squared, Parseval on Z/2, and the real/imag parts of i^n with period 4.
- **Role.** Fourier sub-thread (smallest DFT + i-powers). Self-contained.
- **Counts.** Qed 16 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ ДПФ-2 коэффициенты; степени i (re/im). _Roles:_ коэффициенты ДПФ; периодичность i^n. _Rules:_ dft2_apply; parseval_dft2; i_power period 4. _P4:_ ДПФ-2 и цикл i^n — конечные точные вычисления над Q (Element).
- **Classical counterpart.** DFT-2 coefficients, Parseval, and the powers of i (period 4) are classical; NEW: nothing -- exact Q/integer computations on Z/2 and the i-power cycle.
- **Tags.** fourier, DFT-2, parseval, exposition

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `dft2/dft2_apply` | Definition | ДПФ на Z/2 |
| `dft2_delta_0/1/const_0/1/osc_0/1/sq_00/01/11` | Lemma | ДПФ-2 конкретных сигналов и квадратов |
| `parseval_dft2` | Lemma | ★ Парсеваль на Z/2 |
| `i_power_re/im/i_pow_0/1/2/3/period` | Definition/Lemma | степени i, период 4 |
| `fourier_coefficients_synthesis` | Theorem | синтез |

**Key lemmas (deep):**

- **`parseval_dft2`** - Тождество Парсеваля на Z/2 (энергия во времени = энергия в частоте) — точно над Q. Простейший случай сохранения энергии ДПФ, Element-сторона. _(parseval, DFT-2)_

**Uniqueness - score 1 (exposition).** ДПФ-2 коэффициенты, Парсеваль на Z/2 и цикл i^n (период 4) — точные конечные вычисления.
> _Caveat:_ Классика ДПФ; ценность — точная Q-формализация.

---

## #39 - `src/analysis/FourierConvergence.v` - score 1 (exposition)

**Parseval, Bessel and reconstruction on Z/4 over Q**

- **Topic.** DFT-4 of test signals, Parseval for each, Bessel's inequality for partial frequency energy, exact DFT coefficients, time-energy nonnegativity, reconstruction, and DFT linearity.
- **Role.** Fourier sub-thread (convergence/energy). Self-contained.
- **Counts.** Qed 16 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ сигналы на Z/4; энергии во времени/частоте. _Roles:_ Парсеваль/Бессель как роли сохранения/оценки энергии. _Rules:_ time_energy=freq_energy (Парсеваль); partial ≤ total (Бессель). _P4:_ энергетические тождества точны над Q на конечном цикле (Element).
- **Classical counterpart.** Parseval, Bessel's inequality and Fourier reconstruction are classical; NEW: nothing -- exact Q verification on Z/4 for several test signals.
- **Tags.** fourier, parseval, bessel, exposition

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `phi_0..3/inner4/dft_4/time_energy_4/freq_energy_4` | Definition | ДПФ-4 и энергии |
| `f_const/impulse/alt/ramp/mixed` | Definition | тестовые сигналы |
| `parseval_constant/impulse/alternating/ramp/mixed` | Lemma | ★ Парсеваль для каждого сигнала |
| `partial_freq_1/2/bessel_impulse_1/ramp_2` | Definition/Lemma | ★ неравенство Бесселя (частичная ≤ полная) |
| `dft_impulse_0/1/ramp_0/time_energy_nonneg_const/impulse` | Lemma | коэффициенты и неотрицательность энергии |
| `reconstruct_4/impulse/ramp/mixed/f_sum/dft_linearity_mode0` | Definition/Lemma | реконструкция и линейность |

**Key lemmas (deep):**

- **`bessel_ramp_2`** - Неравенство Бесселя: частичная частотная энергия ≤ полной — проверено над Q для конкретных сигналов. Element-сторона сходимости Фурье: монотонный рост частичных сумм к полной энергии. _(bessel, energy, DFT)_

**Uniqueness - score 1 (exposition).** Парсеваль, Бессель и реконструкция на Z/4 над Q для нескольких сигналов — точные вычисления.
> _Caveat:_ Классика Фурье; ценность — точная Q-проверка.

---

## #40 - `src/analysis/FourierDispersion.v` - score 1 (exposition)

**Lattice dispersion omega^2(k) on Z/4 over Q: massless zero mode**

- **Topic.** omega^2 per mode = Laplacian eigenvalue, the zero mode is massless, the Brillouin cutoff value, nonnegativity, a speed-squared proxy, and a zero mass gap.
- **Role.** Fourier sub-thread (dispersion/physics). Builds on FourierLaplacian.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; ToS analysis.FourierLaplacian
- **E/R/R.** _Elements:_ моды k на Z/4; omega²(k). _Roles:_ дисперсия как роль частота↔мода; нулевая мода = безмассовая. _Rules:_ omega²=лапласиан-собственное значение; mass_gap=omega²(0)=0. _P4:_ дисперсия точна над Q (Element); нулевая мода безмассова.
- **Classical counterpart.** The lattice dispersion relation omega^2(k) from the Laplacian spectrum, the massless zero mode and the Brillouin cutoff are classical lattice physics; NEW: nothing -- exact Q values on Z/4.
- **Tags.** fourier, dispersion, lattice, massless, exposition

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `omega_sq_4/mode0/1/2/3` | Definition/Lemma | дисперсия по модам |
| `zero_mode_massless/brillouin_cutoff/omega_sq_nonneg` | Theorem/Lemma | ★ нулевая мода безмассова; Бриллюэн-обрезание |
| `speed_sq_proxy/speed_sq_value/mass_gap_4/massless_particle` | Definition/Lemma | скорость²; нулевой mass gap |
| `fourier_dispersion_synthesis` | Theorem | синтез |

**Key lemmas (deep):**

- **`zero_mode_massless`** - omega²(0)=0 — нулевая мода безмассова (Goldstone-подобная) на решёточной дисперсии Z/4 над Q. Element-сторона решёточной физики: дисперсия = спектр лапласиана, точно. _(dispersion, massless, lattice)_

**Uniqueness - score 1 (exposition).** Решёточная дисперсия omega²(k) на Z/4 над Q: безмассовая нулевая мода, Бриллюэн-обрезание.
> _Caveat:_ Решёточная дисперсия классична; ценность — точная Q-формализация.

---

## #41 - `src/analysis/FourierGeneralN.v` - score 2 (methods)

**General-N DFT over Q: Hadamard basis, Parseval**

- **Topic.** A general-N Signal type, inner product, DFT/IDFT, time/freq energy, the Hadamard basis with orthogonality, Parseval for N=2, adjacency-squared eigenvalues, and the cycle-4 eigenvalue list.
- **Role.** Fourier sub-thread (general N). Self-contained.
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ сигналы nat→Q общей длины N; базис Адамара. _Roles:_ ДПФ/Адамар-базис общего N; ортогональность. _Rules:_ inner_N; had_basis ортогонален; Парсеваль N=2. _P4:_ общий N параметризует, но каждый конкретный N — конечное точное вычисление (Element).
- **Classical counterpart.** The general-N DFT, the Hadamard/Walsh basis orthogonality, Parseval and circulant eigenvalues are classical; NEW: nothing -- a general-N signal type with N=2 Hadamard worked out exactly over Q.
- **Tags.** fourier, DFT, hadamard, general-N, methods

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `Signal/inner_N/dft_N/idft_N/time_energy/freq_energy` | Definition | общий-N ДПФ и энергии |
| `had_basis/had_norm_sq` | Definition | базис Адамара |
| `had_inner_00/11/01/10/had_orthogonal/parseval_N2` | Lemma | ★ ортогональность Адамара; Парсеваль N=2 |
| `adj2/adj2_dft_eigenvalue/_1/cycle4_eigenvalues/ev_count/sum/sq_sum` | Definition/Lemma | квадрат смежности; список собственных значений Z/4 |
| `fourier_general_synthesis` | Theorem | синтез |

**Key lemmas (deep):**

- **`had_orthogonal`** - Ортогональность базиса Адамара (общий N) над Q — связь с Walsh-Hadamard нитью q-kinematics (n-кубитный Element-базис). Element-сторона: ортогональность точна, без √2 (норма²=2, не норма). _(hadamard, orthogonality, walsh)_

**Uniqueness - score 2 (methods).** Общий-N ДПФ над Q + базис Адамара (ортогональность, Парсеваль N=2), связь с Walsh-Hadamard нитью.
> _Caveat:_ Общий ДПФ и Адамар классичны; вклад — параметризация по N + Q-точность.

---

## #42 - `src/analysis/FourierLaplacian.v` - score 1 (exposition)

**The discrete Laplacian on Z/4 over Q: eigenvalues, trace=2N**

- **Topic.** The Z/4 Laplacian action and eigenvalues (0,2,4,2), the DFT modes as eigenvectors, row sums zero, eigenvalue sum, and trace = 2N.
- **Role.** Fourier sub-thread (the Laplacian; feeds dispersion). Self-contained.
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ лапласиан на Z/4; моды phi_k. _Roles:_ собственные значения лапласиана по модам; phi_k собственные. _Rules:_ laplacian_eigenvalue; row_sum_zero; trace=2N. _P4:_ лапласиан-спектр точен над Q (Element).
- **Classical counterpart.** The discrete Laplacian on a cycle, its eigenvalues 2-2cos(2pi k/N), row sums zero and trace=2N are classical; NEW: nothing -- exact Q values on Z/4.
- **Tags.** fourier, laplacian, spectrum, exposition

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `laplacian_action_4/laplacian_eigenvalue_4` | Definition | лапласиан и его собственные значения |
| `lap_ev_0/1/2/3` | Lemma | ★ собственные значения (0,2,4,2) |
| `laplacian_phi0/1/2/3/row_sum_zero` | Lemma | phi_k собственные; сумма строки = 0 |
| `lap_eigenvalue_sum/trace_eq_2N` | Lemma | сумма с.з. = след = 2N |
| `fourier_laplacian_synthesis` | Theorem | синтез |

**Key lemmas (deep):**

- **`lap_ev_2`** - Собственные значения лапласиана Z/4 = (0,2,4,2) — точно над Q, диагонализованы ДПФ-модами. Element-сторона: дискретный лапласиан = циркулянт, спектр вычислен. Питает дисперсию (omega²=lap-eigenvalue). _(laplacian, spectrum, circulant)_

**Uniqueness - score 1 (exposition).** Дискретный лапласиан на Z/4 над Q: собственные значения (0,2,4,2), след=2N, диагонализация ДПФ.
> _Caveat:_ Дискретный лапласиан классичен; ценность — точная Q-проверка.

---

## #43 - `src/analysis/FourierProcess.v` - score 2 (new-framing)

**The DFT as a finite P4 process (staged, no infinite sums)**

- **Topic.** Staged signals, staged inner products and DFT coefficients shown finite, energy monotonicity, the DFT as a finite computation, P4 compatibility, and classical-vs-P4 contrast.
- **Role.** Fourier sub-thread with explicit P4 framing. Self-contained.
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ поэтапные сигналы StagedSignal N; конечные суммы. _Roles:_ ДПФ как конечный поэтапный процесс (P4). _Rules:_ dft_process финитен; энергия монотонна; classical_vs_p4. _P4:_ ★ ДПФ — КОНЕЧНОЕ поэтапное вычисление, не бесконечная сумма (Element); явный P4-контраст с классикой.
- **Classical counterpart.** The DFT as a finite computation (no infinite sums) is the constructive view; NEW is only the explicit P4 framing: the DFT is a finite staged process, contrasting classical-vs-P4.
- **Tags.** fourier, DFT, P4, process, new-framing

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `StagedSignal/inner_stage/dft_coeff/dft_process` | Definition/Fixpoint | поэтапный ДПФ |
| `dft_process_finite/inner_stage_self_nonneg/comm/zero` | Lemma | финитность и свойства скалярного произведения |
| `time_energy_N/nonneg/zero/monotone` | Definition/Lemma | энергия монотонна по стадии |
| `dft_is_finite_computation/dft_p4_compatible/classical_vs_p4` | Lemma/Theorem | ★ ДПФ конечен, P4-совместим |
| `fourier_process_synthesis` | Theorem | синтез |

**Key lemmas (deep):**

- **`dft_p4_compatible`** - ДПФ — конечное поэтапное вычисление (StagedSignal), не бесконечная сумма: явная P4-формулировка, отделяющая Element-вычислимое от классического предельного. Связь с процесс-онтологией (вена C) в анализе. _(P4, finite-computation, DFT)_

**Uniqueness - score 2 (new-framing).** ДПФ как конечный поэтапный P4-процесс (не бесконечная сумма), с явным classical-vs-P4 контрастом.
> _Caveat:_ Конечность ДПФ очевидна; ново лишь явное P4-обрамление подветки.

---

## #44 - `src/analysis/FourierSpectralDecomp.v` - score 1 (exposition)

**Spectral decomposition and Green function on Z/4 over Q**

- **Topic.** Spectral components, reconstruction (identity), transfer spectral diagonal/offdiagonal, the Green spectral function, and a synthesis.
- **Role.** Fourier sub-thread (spectral decomposition/resolvent). Self-contained.
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ спектральные компоненты; передаточная/Грин функции. _Roles:_ спектральное разложение/реконструкция; резольвента (Грин). _Rules:_ spectral_recon = тождество; transfer/green spectral. _P4:_ спектральное разложение точно над Q на конечном цикле (Element).
- **Classical counterpart.** Spectral decomposition / reconstruction and the resolvent (Green function) of a circulant are classical; NEW: nothing -- exact Q reconstruction and transfer/Green values on Z/4.
- **Tags.** fourier, spectral-decomposition, green-function, exposition

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `spectral_comp/spectral_recon/test_sig` | Definition | спектральные компоненты и реконструкция |
| `recon_test_0/1/2/3/reconstruction_identity` | Lemma/Theorem | ★ реконструкция = тождество |
| `transfer_spectral/K0_diag/offdiag/green_spectral_4/green_K1_j0` | Definition/Lemma | передаточная и Грин функции |
| `fourier_spectral_synthesis` | Theorem | синтез |

**Key lemmas (deep):**

- **`reconstruction_identity`** - Спектральная реконструкция = тождество (сигнал восстанавливается из спектральных компонент) над Q. Element-сторона: разложение по собственному базису полно и точно на конечном цикле. _(spectral-decomposition, reconstruction)_

**Uniqueness - score 1 (exposition).** Спектральное разложение и Грин-функция на Z/4 над Q: реконструкция-тождество, резольвента.
> _Caveat:_ Спектральное разложение классично; ценность — точная Q-проверка.

---

## #45 - `src/analysis/FourierSynthesis.v` - score 1 (exposition)

**Fourier grand synthesis: 2-circulant eigenvalues, Ising transfer over Q**

- **Topic.** A 2-circulant, its eigenvalues, the Green function and its growth, an Ising-circulant with concrete plus/minus eigenvalues, and a grand synthesis.
- **Role.** Fourier sub-thread synthesis (2-circulant + Ising). Self-contained.
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ 2-циркулянт; Грин-функция; Изинг-передача. _Roles:_ собственные значения циркулянта; передаточная матрица Изинга. _Rules:_ circ2_eigenvalue; green_circ2 растёт; ising eigenvalue. _P4:_ циркулянт-спектр и Грин точны над Q (Element).
- **Classical counterpart.** Circulant eigenvalues, the resolvent/Green function and the Ising transfer matrix are classical; NEW: nothing -- exact Q values tying a 2-circulant to an Ising-like transfer eigenvalue.
- **Tags.** fourier, circulant, ising, exposition

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `circ2/circ2_eigenvalue_0/1/qpow/green_circ2` | Definition/Lemma | 2-циркулянт, собственные значения, Грин |
| `green_circ2_K0/K1/K2/grows` | Lemma | Грин растёт с K |
| `ising_circ_a/b/ising_eigenvalue_plus/minus` | Definition/Lemma | Изинг-циркулянт собственные значения |
| `fourier_grand_synthesis` | Theorem | ★ гранд-синтез |

**Key lemmas (deep):**

- **`ising_eigenvalue_plus`** - Собственные значения Изинг-подобного 2-циркулянта точно над Q — связь Фурье-диагонализации с передаточной матрицей статфизики. Element-сторона: конечный спектр. _(circulant, ising, transfer-matrix)_

**Uniqueness - score 1 (exposition).** 2-циркулянт, Грин-функция и Изинг-передача над Q — точные конечные вычисления.
> _Caveat:_ Циркулянты и передаточные матрицы классичны; ценность — Q-формализация.

---

## #46 - `src/analysis/FourierTransform.v` - score 1 (exposition)

**2-point cyclic convolution over Q**

- **Topic.** The 2-point convolution conv2 with delta/const/oscillating cases.
- **Role.** Fourier sub-thread (smallest convolution). Self-contained.
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ 2-точечная свёртка conv2. _Roles:_ свёртка как роль; конкретные случаи. _Rules:_ conv2 на дельте/константе/осцилляции. _P4:_ 2-точечная свёртка — конечное точное вычисление (Element).
- **Classical counterpart.** Cyclic convolution and its DFT diagonalization are classical; NEW: nothing -- a tiny 2-point convolution with concrete cases.
- **Tags.** fourier, convolution, exposition

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `conv2` | Definition | 2-точечная циклическая свёртка |
| `conv2_delta/const/osc` | Lemma | ★ конкретные свёртки |

**Key lemmas (deep):**

- **`conv2_delta`** - Свёртка с дельтой = тождество (2-точечный случай) над Q — простейшая проверка теоремы о свёртке. Element-сторона: конечно, точно. _(convolution, delta)_

**Uniqueness - score 1 (exposition).** 2-точечная циклическая свёртка над Q с конкретными случаями.
> _Caveat:_ Тривиальный случай свёртки; ценность минимальна (часть подветки).

---

## #47 - `src/analysis/FourierVacuumEnergy.v` - score 2 (new-framing)

**Vacuum energy on Z/4 as a finite P4 process over Q**

- **Topic.** The summed mode omega^2 (=2), nonzero mode count, average omega^2, the vacuum energy as a RealProcess of partial sums (monotone, finite at each stage), energy density, contrast with 1D Casimir, and P4 framing.
- **Role.** Fourier sub-thread with P4 vacuum-energy framing. Self-contained.
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; RealProcess (ProcessCore-style)
- **E/R/R.** _Elements:_ моды omega²; частичные суммы вакуумной энергии. _Roles:_ вакуумная энергия как RealProcess частичных сумм (P4). _Rules:_ partial_omega_sq_sum монотонна; vacuum_process финитен на стадии. _P4:_ ★ вакуумная энергия — КОНЕЧНЫЙ поэтапный процесс (Element), не завершённая расходящаяся сумма; контраст с 1D Casimir.
- **Classical counterpart.** Zero-point (vacuum) energy as a sum of mode frequencies and energy density are classical; NEW is only the P4 framing: the vacuum energy is a finite staged process (partial sums), not a completed divergent sum, contrasted with 1D Casimir.
- **Tags.** fourier, vacuum-energy, P4, process, new-framing

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `vacuum_energy_sq_4/value/nonzero_modes_count/avg_omega_sq_4/value` | Definition/Lemma | суммарное omega², число мод, среднее |
| `partial_omega_sq_sum/vacuum_process/finite/partial_sum_monotone` | Fixpoint/Definition/Lemma | ★ вакуумная энергия как монотонный конечный процесс |
| `energy_density_4/value/density_not_casimir_1d` | Definition/Lemma | плотность энергии; контраст с Casimir |
| `vacuum_energy_p4/fourier_vacuum_synthesis` | Theorem | ★ P4-формулировка вакуумной энергии |

**Key lemmas (deep):**

- **`vacuum_energy_p4`** - Вакуумная энергия как КОНЕЧНЫЙ поэтапный процесс частичных сумм (RealProcess), монотонный и финитный на каждой стадии — P4-разрешение «расходящейся суммы нулевых колебаний». Вена C в физике анализа: энергия = процесс, не завершённый расходящийся объект. _(vacuum-energy, P4, process, finite)_

**Uniqueness - score 2 (new-framing).** Вакуумная энергия как конечный поэтапный P4-процесс (монотонные частичные суммы), не завершённая расходящаяся сумма — вена C в физике.
> _Caveat:_ Нулевая энергия мод классична; ново лишь P4/процесс-обрамление + контраст с Casimir.

---

## #48 - `src/analysis/FTC.v` - score 3 (new-framing)

**Fundamental theorem of calculus over Q via Lipschitz bounds**

- **Topic.** Lipschitz calculus (const/identity/scale/add/sub/compose), FTC increment bound, monotonicity from a nonnegative derivative, u-substitution (affine), and Riemann-sum manipulation -- all with explicit epsilon control over Q.
- **Role.** Calculus chain core (FTC over Q). Self-contained.
- **Counts.** Qed 28 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ функции Q→Q и их производные f'; константы Липшица; Риман-суммы. _Roles:_ ФТА как роль связи производной и приращения; Липшиц как роль регулярности. _Rules:_ ftc_increment_bound; монотонность из f'≥0; u-подстановка; epsilon-контроль. _P4:_ ФТА в эпсилон-форме над Q (Element): приближённое приращение с явной ошибкой, не точный интеграл.
- **Classical counterpart.** The Fundamental Theorem of Calculus and the differentiation rules (sum, scale, chain, u-substitution) are classical; NEW is only the constructive Q form: FTC via Lipschitz increment bounds and Riemann sums with explicit epsilon error control, no real analysis.
- **Tags.** FTC, calculus, lipschitz, riemann-sum, new-framing

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `Lipschitz_on/uniformly_continuous_on` | Definition | Липшиц и равномерная непрерывность |
| `lipschitz_const/identity/scale/add/sub/negate/compose/uniform_cont/bounded/affine` | Lemma | алгебра Липшица (замкнутость) |
| `ftc_increment_bound/monotone/strict_monotone/difference/absolute_value_bound` | Lemma | ★ ФТА-оценки приращения и монотонность |
| `ftc_sum_rule/constant_function/scale_rule` | Lemma | правила интегрирования |
| `udiff_chain_affine/neg/ftc_u_substitution_affine/sub_interval` | Lemma | ★ u-подстановка (аффинная) |
| `riemann_sum_negate_fn/sub/sandwich/bound_below` | Lemma | манипуляции Риман-сумм |
| `udiff_approx_lipschitz/implies_bounded` | Lemma | связь равномерной дифференцируемости и Липшица |

**Key lemmas (deep):**

- **`ftc_increment_bound`** - ФТА в конструктивной форме: приращение f(b)−f(a) оценивается интегралом f' с явной epsilon-ошибкой через Липшиц. Element-сторона исчисления над Q: вместо точного равенства (требующего R) — приближение с вычислимым контролем ошибки. Ядро calculus-цепочки. _(FTC, lipschitz, epsilon-control)_
- **`ftc_u_substitution_affine`** - Замена переменной (аффинная) с контролем ошибки — нетривиальное правило исчисления, доказанное над Q без вещественных. Демонстрирует, что вся машина дифференцирования работает в эпсилон-форме. _(u-substitution, calculus)_

**Uniqueness - score 3 (new-framing).** ФТА и правила дифференцирования над Q через Липшиц-оценки и Риман-суммы с явным epsilon-контролем (без вещественного анализа) — конструктивное исчисление.
> _Caveat:_ ФТА и правила классичны; ново — систематическое эпсилон-конструктивное исполнение над Q (как вся calculus-цепочка), не новая теорема.

---

## #49 - `src/analysis/FubiniProcess.v` - score 2 (methods)

**Fubini for 2D step functions over Q**

- **Topic.** 1D and 2D step-function integrals over rectangles, iterated xy/yx integrals, Fubini on a single rectangle and on lists (iterated xy = yx = double), with concrete examples, plus a trace-commute synthesis.
- **Role.** Constructive integration over Q (Fubini, step-function side). Self-contained.
- **Counts.** Qed 20 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith List
- **E/R/R.** _Elements:_ 2D ступенчатые функции (списки прямоугольников); итерированные интегралы. _Roles:_ Фубини как роль перестановки порядка интегрирования. _Rules:_ iterated_xy = iterated_yx = double для прямоугольников и списков. _P4:_ Фубини на ступенчатых функциях точен над Q (Element); полный Фубини для измеримых — role-limit.
- **Classical counterpart.** Fubini's theorem (iterated = double integral) is classical and measure-theoretic; NEW: only a step-function (2D rectangle) version over Q where iterated xy = iterated yx = double, exactly.
- **Tags.** fubini, integration, step-functions, 2D, methods

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `Step/StepFun/step_integral/Rectangle/StepFun2D/rect_integral/integral_2d` | Record/Definition/Fixpoint | 1D/2D ступенчатые интегралы |
| `iterated_xy/yx/_list` | Definition/Fixpoint | итерированные интегралы |
| `fubini_rectangle/iterated_eq_double/yx_eq_double` | Lemma | ★ Фубини на прямоугольнике |
| `fubini_step/iterated_xy_eq_2d/yx_eq_2d` | Theorem/Lemma | ★ Фубини на списках прямоугольников |
| `example_rect_integral/fubini_concrete/two_rects/fubini_two` | Lemma | конкретные примеры |
| `integral_2d_nil/app/rect_integral_zero_val/width/trace_commute_scalar/fubini_and_trace` | Lemma/Theorem | аддитивность, вырожденные случаи, синтез |

**Key lemmas (deep):**

- **`fubini_step`** - Фубини для 2D ступенчатых функций над Q: итерированный интеграл xy = yx = двойной, точно. Element-сторона: для конечных списков прямоугольников перестановка порядка интегрирования — вычислимое тождество, без условий измеримости. _(fubini, step-functions, 2D)_

**Uniqueness - score 2 (methods).** Фубини для 2D ступенчатых функций над Q (итерированный = двойной интеграл, оба порядка) точно.
> _Caveat:_ Фубини классична; вклад — конструктивная ступенчатая версия над Q, не полный Фубини.

---

## #50 - `src/analysis/HarmonicDiverges.v` - score 2 (methods)

**The harmonic series diverges (Oresme blocks) over Q**

- **Topic.** Partial sums of 1/n, the 2^k-block lower bound (each block >= 1/2), and divergence as the partial sums exceeding every bound.
- **Role.** Series analysis over Q (a canonical divergence). Self-contained.
- **Counts.** Qed 21 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ частичные суммы 1/n; 2^k-блоки. _Roles:_ расходимость как role-limit (нет конечной границы). _Rules:_ каждый блок [2^k,2^{k+1}) ≥ 1/2 ⟹ суммы неограничены. _P4:_ расходимость = role-limit-правило (превосходит любую границу); каждая частичная сумма актуальна (Element).
- **Classical counterpart.** The divergence of the harmonic series (Oresme's 2^k-block argument) is classical; NEW: nothing -- an exact nat/Q formalization of the block lower bound, divergence as unboundedness.
- **Tags.** harmonic-series, divergence, series, role-limit, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `harmonic partial sums / block bounds` | Definition/Lemma | частичные суммы и блочные оценки (1/2 на блок) |
| `harmonic_diverges` | Theorem | ★ гармонический ряд расходится (превосходит любую границу) |

**Key lemmas (deep):**

- **`harmonic_diverges`** - Расходимость гармонического ряда (аргумент Орема: блок [2^k,2^{k+1}) суммирует ≥1/2, значит частичные суммы превосходят любую границу). Role-limit-узор: расходимость = отсутствие конечной границы, каждая частичная сумма — актуальный Element. _(harmonic-series, divergence, role-limit)_

**Uniqueness - score 2 (methods).** Расходимость гармонического ряда (блоки Орема) точно над Q: каждый 2^k-блок ≥1/2, суммы неограничены.
> _Caveat:_ Аргумент Орема — классика XIV века; вклад — точная Q/nat-формализация, не новый результат.

---

## #51 - `src/analysis/HeineBorelComplete.v` - score 3 (new-framing)

**Heine-Borel over Q via a Lebesgue number (honest non-compactness)**

- **Topic.** Epsilon-nets, open covers and intervals over Q; extracting a finite subcover from a grid given a Lebesgue-number hypothesis, with the genuine non-compactness of [0,1] cap Q acknowledged as the reason the hypothesis is needed.
- **Role.** Analysis (Heine-Borel, honest Q version). Self-contained.
- **Counts.** Qed 28 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ эпсилон-сети; открытые покрытия интервалами над Q; число Лебега. _Roles:_ компактность как role-limit ([0,1]∩Q НЕ компактно); число Лебега как честная гипотеза. _Rules:_ при заданном числе Лебега из сетки извлекается конечное подпокрытие. _P4:_ [0,1]∩Q ГЕНУИННО не компактно (role-limit); конечное подпокрытие — Element ТОЛЬКО при числе Лебега (честная гипотеза, не хак).
- **Classical counterpart.** Heine-Borel (every open cover of a compact set has a finite subcover) is classical and FAILS for [0,1] over Q (not complete); NEW is only the honest formalization: finite subcover EXTRACTED given a Lebesgue number, with the Q-non-compactness acknowledged.
- **Tags.** heine-borel, compactness, lebesgue-number, honest-limitation, new-framing

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `epsilon-nets / open covers / Lebesgue number` | Definition | сети, покрытия, число Лебега над Q |
| `finite subcover extraction (grid-based)` | Lemma | ★ извлечение конечного подпокрытия по сетке |
| `heine_borel (with Lebesgue number)` | Theorem | ★ Гейне-Борель при гипотезе числа Лебега |

**Key lemmas (deep):**

- **`heine_borel (with Lebesgue number)`** - Гейне-Борель над Q ЧЕСТНО: конечное подпокрытие извлекается из сетки при гипотезе числа Лебега — потому что [0,1]∩Q genuinely НЕ компактно (нет R-полноты). Гипотеза не хак, а точная локализация недостающей полноты (role-limit). Образец честности проекта (CLAUDE.md invariant). _(heine-borel, lebesgue-number, honest-non-compactness)_

**Uniqueness - score 3 (new-framing).** Гейне-Борель над Q с честной гипотезой числа Лебега: [0,1]∩Q НЕ компактно (role-limit), конечное подпокрытие извлекается лишь при явной локализации недостающей R-полноты.
> _Caveat:_ Гейне-Борель классичен; вклад — честное признание Q-некомпактности + локализация цены (число Лебега), не доказательство полного Гейне-Бореля.

---

## #52 - `src/analysis/ImplicitFunction.v` - score 2 (methods)

**Implicit function theorem via damped contraction over Q**

- **Topic.** A function f, damping lambda, the contraction iterates solving f=0 implicitly, and the convergence of the implicit solution as a process.
- **Role.** Analysis (implicit function via fixed point). Self-contained.
- **Counts.** Qed 20 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ функция f; демпфирование lambda; итераты. _Roles:_ неявное решение как роль-неподвижная точка; демпфирование как роль сходимости. _Rules:_ демпфированная итерация — сжатие ⟹ сходится к неявному решению. _P4:_ неявное решение = ПРОЦЕСС итераций (Element-стадии), предел — role-limit.
- **Classical counterpart.** The implicit function theorem is classical; NEW is only a constructive contraction-mapping (damped iteration) version over Q producing the implicit solution as a process.
- **Tags.** implicit-function, contraction, fixed-point, process, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `f / damping lambda / iterates` | Definition | функция, демпфирование, итераты |
| `contraction / convergence of implicit solution` | Lemma/Theorem | ★ демпфированная итерация сжимает и сходится |

**Key lemmas (deep):**

- **`convergence of implicit solution`** - Неявная функция через демпфированное сжатие: итерация f(x)=0 с демпфированием lambda — сжимающее отображение, сходящееся к неявному решению. Element-сторона: решение строится КАК ПРОЦЕСС итераций (Banach), не как готовый объект. _(implicit-function, contraction, process)_

**Uniqueness - score 2 (methods).** Теорема о неявной функции через демпфированное сжатие над Q: неявное решение как сходящийся процесс итераций.
> _Caveat:_ ТНФ и метод сжатий классичны; вклад — конструктивная Q-версия как процесс.

---

## #53 - `src/analysis/L1Space.v` - score 2 (methods)

**The L1 space of step functions over Q**

- **Topic.** Step functions, the L1 norm, the triangle inequality, L1 Cauchy/convergence, and basic L1 structure over Q.
- **Role.** Functional analysis over Q (L1). Self-contained.
- **Counts.** Qed 16 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith List
- **E/R/R.** _Elements:_ ступенчатые функции; L1-норма. _Roles:_ L1-пространство как роль; норма/сходимость как роли. _Rules:_ L1-норма, треугольное неравенство, L1-Коши. _P4:_ L1 на ступенчатых функциях конструктивен над Q (Element); полнота — процесс Коши.
- **Classical counterpart.** The L1 space (integrable step functions, L1 norm, triangle inequality, completeness-as-Cauchy) is classical functional analysis; NEW: nothing -- a constructive step-function L1 over Q.
- **Tags.** L1, functional-analysis, step-functions, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `step functions / L1 norm` | Definition | ступенчатые функции и L1-норма |
| `L1 triangle inequality / L1 Cauchy / convergence` | Lemma | ★ норма-аксиомы, Коши/сходимость |

**Key lemmas (deep):**

- **`L1 triangle inequality`** - Треугольное неравенство L1-нормы на ступенчатых функциях над Q — делает L1 настоящим нормированным пространством. Element-сторона: конструктивная функциональная аналитика без вещественной меры. _(L1, norm, triangle-inequality)_

**Uniqueness - score 2 (methods).** L1-пространство ступенчатых функций над Q: норма, треугольное неравенство, L1-Коши.
> _Caveat:_ L1 классичен; вклад — конструктивная ступенчатая версия над Q.

---

## #54 - `src/analysis/L2Space.v` - score 2 (methods)

**The L2 space of step functions over Q**

- **Topic.** Step functions with an L2 inner product, the L2 norm, Cauchy-Schwarz, the triangle inequality, and L2 Cauchy structure over Q.
- **Role.** Functional analysis over Q (L2/Hilbert). Self-contained.
- **Counts.** Qed 19 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith List
- **E/R/R.** _Elements:_ ступенчатые функции; L2-скалярное произведение/норма. _Roles:_ L2-гильбертово пространство как роль; скалярное произведение. _Rules:_ L2-норма, Коши-Шварц, треугольное неравенство. _P4:_ L2 на ступенчатых функциях конструктивен над Q (Element); полнота — процесс.
- **Classical counterpart.** The L2 Hilbert space (inner product, L2 norm, Cauchy-Schwarz, completeness-as-Cauchy) is classical; NEW: nothing -- a constructive step-function L2 over Q.
- **Tags.** L2, hilbert, functional-analysis, step-functions, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `step functions / L2 inner product / norm` | Definition | ступенчатые функции, скалярное произведение, норма |
| `L2 Cauchy-Schwarz / triangle inequality / Cauchy` | Lemma | ★ CS, треугольное неравенство, Коши |

**Key lemmas (deep):**

- **`L2 Cauchy-Schwarz`** - Коши-Шварц в L2 на ступенчатых функциях над Q — даёт треугольное неравенство и делает L2 пред-гильбертовым пространством. Element-сторона: конструктивная гильбертова структура без вещественной меры. _(L2, cauchy-schwarz, hilbert)_

**Uniqueness - score 2 (methods).** L2-пространство ступенчатых функций над Q: скалярное произведение, Коши-Шварц, треугольное неравенство.
> _Caveat:_ L2/гильбертово пространство классично; вклад — конструктивная ступенчатая версия над Q.

---

## #55 - `src/analysis/LebesgueMeasure.v` - score 3 (new-framing)

**Measure FROM the integral: Lebesgue measure as integral of indicators over Q**

- **Topic.** Step-function integrals, indicators of intervals, the measure of a set defined as the integral of its indicator, additivity, monotonicity, and the measure of concrete sets -- measure derived from integral, not prior to it.
- **Role.** Vein C-flavour: measure-from-integral (uniqueness-map cites LebesgueMeasure). Self-contained.
- **Counts.** Qed 22 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith List
- **E/R/R.** _Elements:_ ступенчатые интегралы; индикаторы интервалов; множества. _Roles:_ мера как роль, ПРОИЗВОДНАЯ от интеграла (мера = интеграл индикатора). _Rules:_ measure(S)=integral(indicator S); аддитивность, монотонность. _P4:_ мера ВЫВЕДЕНА из интеграла (Element), а не построена до него; конструктивно над Q — переворачивает классический порядок.
- **Classical counterpart.** Lebesgue measure is classically built first (sigma-algebra, outer measure) then integration on top; NEW is the inversion: measure is DERIVED from the step-function integral (measure of a set = integral of its indicator), a constructive measure-from-integral over Q.
- **Tags.** measure, measure-from-integral, lebesgue, vein-C, new-framing

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `step integrals / indicators / measure` | Definition | интеграл, индикаторы, мера=интеграл индикатора |
| `measure additivity / monotonicity` | Lemma | ★ аддитивность и монотонность меры |
| `measure of concrete sets` | Lemma | мера конкретных интервалов/объединений |

**Key lemmas (deep):**

- **`measure additivity`** - Мера множества ОПРЕДЕЛЕНА как интеграл его индикатора (а не наоборот); аддитивность меры следует из аддитивности интеграла. Переворачивает классический порядок (сначала мера, потом интеграл) — конструктивный measure-from-integral над Q. Вена C-аромат: мера как производное правило, не первичный объект. _(measure-from-integral, additivity, vein-C)_

**Uniqueness - score 3 (new-framing).** Мера ВЫВЕДЕНА из интеграла (мера множества = интеграл индикатора), переворачивая классический порядок «сначала мера» — конструктивно над Q.
> _Caveat:_ Конструктивная мера ≈ Бишоп; ново — явный measure-from-integral порядок + Q-исполнение, не новая теория меры.

---

## #56 - `src/analysis/LHopital.v` - score 2 (methods)

**L'Hopital's rule over Q via ratio bounds**

- **Topic.** The 0/0 ratio f/g near a point bounded by f'/g' via linear approximation, with explicit epsilon control over Q.
- **Role.** Calculus over Q (L'Hopital). Self-contained.
- **Counts.** Qed 24 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ функции f,g и производные; отношение f/g у точки. _Roles:_ правило Лопиталя как роль связи отношений. _Rules:_ f/g ≈ f'/g' через линейное приближение + epsilon-контроль. _P4:_ Лопиталь в эпсилон-форме над Q (Element): отношение оценено с явной ошибкой.
- **Classical counterpart.** L'Hopital's rule for 0/0 limits is classical; NEW is only a constructive Q form via Lipschitz/linear-approximation ratio bounds with explicit epsilon control.
- **Tags.** lhopital, calculus, epsilon-control, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `ratio f/g / linear approximation` | Definition | отношение и линейное приближение |
| `lhopital ratio bound (epsilon)` | Lemma/Theorem | ★ f/g оценено через f'/g' с epsilon |

**Key lemmas (deep):**

- **`lhopital ratio bound (epsilon)`** - Правило Лопиталя над Q: отношение f/g (0/0) оценено отношением производных f'/g' через линейное приближение с явным epsilon-контролем. Element-сторона: вместо точного предела (R) — приближение с вычислимой ошибкой. _(lhopital, ratio-bound, epsilon-control)_

**Uniqueness - score 2 (methods).** Правило Лопиталя над Q через оценки отношения производных с epsilon-контролем (без вещественного предела).
> _Caveat:_ Лопиталь классичен; вклад — конструктивная эпсилон-Q-версия.

---

## #57 - `src/analysis/MeasureSynthesis.v` - score 2 (synthesis+observation)

**Measure theory synthesis over Q**

- **Topic.** A synthesis tying together the step integral, measure-from-integral, Fubini and dominated convergence into one constructive measure-theory chain over Q.
- **Role.** Analysis synthesis (measure thread). Cites StepIntegral/LebesgueMeasure/Fubini/DCT.
- **Counts.** Qed 18 / Admitted 0 / axioms 0
- **Imports.** ToS analysis measure files
- **E/R/R.** _Elements:_ результаты конструктивной теории меры над Q. _Roles:_ синтез-цепочка теории меры. _Rules:_ интеграл → мера → Фубини → DCT собраны. _P4:_ сборка конструктивных конечных результатов (Element).
- **Classical counterpart.** Assembling step-integral, measure-from-integral, Fubini, DCT into one measure-theory chain is exposition; NEW: nothing -- a synthesis over the constructive measure files.
- **Tags.** measure-theory, synthesis, Q

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `measure theory chain synthesis` | Theorem | ★ синтез цепочки теории меры над Q |

**Key lemmas (deep):**

- **`measure theory chain synthesis`** - Сборка конструктивной теории меры над Q: ступенчатый интеграл → мера-из-интеграла → Фубини → DCT в одну цепочку. Синтез уже доказанных результатов, демонстрирующий когерентность Q-подхода к мере. _(synthesis, measure-theory)_

**Uniqueness - score 2 (synthesis+observation).** Синтез конструктивной теории меры над Q (интеграл→мера→Фубини→DCT) в одну когерентную цепочку.
> _Caveat:_ Сборка уже доказанного; ценность — демонстрация когерентности measure-from-integral подхода, не новый результат.

---

## #58 - `src/analysis/PeanoExistence.v` - score 3 (new-framing)

**Peano existence for ODEs via Euler polygons over Q**

- **Topic.** Euler-polygon approximate solutions of y'=f(y), their equicontinuity/boundedness, and the existence of a solution as the limit process -- existence without uniqueness (no Lipschitz).
- **Role.** ODE analysis over Q (Peano existence). Self-contained.
- **Counts.** Qed 22 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ Эйлеровы ломаные приближения решения ОДУ. _Roles:_ существование решения как role-limit ломаных; без единственности (нет Липшица). _Rules:_ Эйлеровы ломаные равностепенно непрерывны/ограничены ⟹ предел-решение. _P4:_ решение существует как ПРОЦЕСС ломаных (Element-стадии); предел — role-limit; без Липшица — без единственности.
- **Classical counterpart.** Peano's existence theorem (a continuous ODE has a solution, no uniqueness without Lipschitz) is classical and uses compactness/Arzela-Ascoli; NEW is only a constructive Euler-polygon existence over Q.
- **Tags.** peano, ODE, euler-polygons, existence, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `Euler polygons / equicontinuity / boundedness` | Definition/Lemma | Эйлеровы ломаные и их компактность |
| `peano_existence` | Theorem | ★ существование решения ОДУ (без единственности) |

**Key lemmas (deep):**

- **`peano_existence`** - Существование решения ОДУ y'=f(y) для НЕПРЕРЫВНОГО f через Эйлеровы ломаные над Q — без Липшица, потому без единственности (контраст с PicardLindelof). Element-сторона: решение строится как процесс ломаных приближений; предел — role-limit. _(peano, ODE, euler-polygons, existence-no-uniqueness)_

**Uniqueness - score 3 (new-framing).** Существование Пеано для ОДУ через Эйлеровы ломаные над Q — существование БЕЗ единственности (нет Липшица), решение как процесс приближений.
> _Caveat:_ Теорема Пеано классична (Арцела-Асколи); вклад — конструктивная Q-версия через ломаные + явный контраст с Пикаром (единственность).

---

## #59 - `src/analysis/PicardLindelof.v` - score 3 (new-framing)

**Picard-Lindelof for Lipschitz ODEs via contraction over Q**

- **Topic.** Picard iterates of a Lipschitz ODE, the contraction property, convergence to the unique solution, and the solution as a fixed-point process.
- **Role.** ODE analysis over Q (Picard, unique solution). Self-contained.
- **Counts.** Qed 23 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ Пикаровы итераты Lipschitz-ОДУ. _Roles:_ единственное решение как роль-неподвижная точка; Липшиц даёт сжатие. _Rules:_ Пикарова итерация — сжатие ⟹ единственное решение (Банах). _P4:_ решение = ПРОЦЕСС Пикаровых итераций (Element-стадии), предел — role-limit; Липшиц ⟹ единственность.
- **Classical counterpart.** The Picard-Lindelof theorem (Lipschitz ODE has a unique solution) via Banach fixed point is classical; NEW is only the constructive Q form: Picard iteration as an explicit contraction process.
- **Tags.** picard-lindelof, ODE, contraction, uniqueness, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `Picard iterates / contraction` | Definition/Lemma | Пикаровы итераты и сжатие |
| `picard_lindelof (existence + uniqueness)` | Theorem | ★ единственное решение Lipschitz-ОДУ |

**Key lemmas (deep):**

- **`picard_lindelof (existence + uniqueness)`** - Пикар-Линделёф для Lipschitz-ОДУ через сжатие (Банах) над Q: итерация Пикара сжимает ⟹ ЕДИНСТВЕННОЕ решение. Element-сторона: решение строится как процесс итераций; контраст с Пеано (без Липшица — без единственности). _(picard-lindelof, ODE, contraction, uniqueness)_

**Uniqueness - score 3 (new-framing).** Пикар-Линделёф для Lipschitz-ОДУ через явное сжатие над Q: единственное решение как процесс Пикаровых итераций; контраст с Пеано (существование без единственности).
> _Caveat:_ Пикар-Линделёф и Банах классичны; вклад — конструктивная Q-версия как процесс + Lipschitz/no-Lipschitz дихотомия с Пеано.

---

## #60 - `src/analysis/SpectralTheoremCompact.v` - score 3 (new-framing)

**Spectral theorem for compact self-adjoint operators (finite-dim over Q)**

- **Topic.** Self-adjoint finite-dim operators over Q, real eigenvalues, an orthogonal eigenbasis, and diagonalization -- the finite-dimensional core of the spectral theorem.
- **Role.** Functional analysis over Q (spectral theorem, finite-dim). Builds on CompactOperator. Self-contained.
- **Counts.** Qed 18 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; ToS analysis.CompactOperator
- **E/R/R.** _Elements:_ конечномерные самосопряжённые операторы над Q; собственные пары. _Roles:_ спектральная теорема как роль-диагонализация; ортонормальный собственный базис. _Rules:_ самосопряжённый ⟹ вещественные с.з. + ортогональный собственный базис. _P4:_ конечномерная спектральная теорема точна над Q (Element); бесконечномерный компактный случай — role-limit.
- **Classical counterpart.** The spectral theorem for compact self-adjoint operators (orthonormal eigenbasis, real eigenvalues) is classical and infinite-dimensional; NEW is only the finite-dimensional Q instance (symmetric matrices diagonalized with rational/real eigenvalues).
- **Tags.** spectral-theorem, self-adjoint, finite-dim, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `self-adjoint / eigenpairs / orthogonal eigenbasis` | Definition/Lemma | самосопряжённость, собственные пары, ортогональный базис |
| `spectral_theorem (finite-dim)` | Theorem | ★ диагонализация самосопряжённого оператора |

**Key lemmas (deep):**

- **`spectral_theorem (finite-dim)`** - Спектральная теорема в конечной размерности над Q: самосопряжённый оператор диагонализуется ортогональным собственным базисом с вещественными собственными значениями. Element-сторона: для конечной размерности — точное вычисление; бесконечномерный компактный случай (предельный) — role-limit. _(spectral-theorem, self-adjoint, finite-dim)_

**Uniqueness - score 3 (new-framing).** Спектральная теорема для самосопряжённых операторов в конечной размерности над Q (диагонализация, ортогональный собственный базис) — Element-ядро; бесконечномерный случай — role-limit.
> _Caveat:_ Спектральная теорема классична; вклад — конечномерный Q-инстанс + честная граница с бесконечномерным.

---

## #61 - `src/analysis/Sqrt2Irrational.v` - score 3 (new-framing)

**sqrt2 is irrational (infinite descent over Q)**

- **Topic.** no rational r with r^2=2, by infinite descent; the reusable sqrt2 role-limit witness for the q-kinematics surd thread (Pell process, T-gate, 45-degree).
- **Role.** Irrationality core (reused by q-kinematics: MetallicRatios, MusicTemperament, BellTsirelson, etc.). Self-contained.
- **Counts.** Qed 14 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith ZArith
- **E/R/R.** _Elements:_ рациональные кандидаты r с r²=2. _Roles:_ √2 как role-limit (нетерминирующий процесс), не Element. _Rules:_ бесконечный спуск: r²=2 невозможно над Q. _P4:_ √2 — role-limit (иррационален), его конечные приближения (Пелля) — Element-стадии; «√2 рационально?» — не-вопрос (P4).
- **Classical counterpart.** The irrationality of sqrt2 is classical (Pythagoreans); NEW: nothing -- a clean infinite-descent Q proof, REUSED across the q-kinematics surd thread (T-gate/45-degree role-limit).
- **Tags.** sqrt2, irrationality, role-limit, q-kinematics, new-framing

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `even/parity helpers` | Lemma | чётность для спуска |
| `no_rational_sqrt2 / sqrt2_irrational` | Theorem | ★ нет r∈Q с r²=2 (бесконечный спуск) |
| `sqrt2_not_in_Q (Z form)` | Lemma | целочисленная форма для downstream |

**Key lemmas (deep):**

- **`no_rational_sqrt2`** - √2 иррационален бесконечным спуском над Q — фундаментальный role-limit, ПЕРЕИСПОЛЬЗУЕМЫЙ по всей нити q-kinematics (T-gate, 45°-точка, серебряное сечение, музыкальный темперамент, Цирельсон). √2 = канонический квадратичный role-limit с процессом Пелля. _(sqrt2, irrationality, infinite-descent, role-limit)_

**Uniqueness - score 3 (new-framing).** √2 иррационален (бесконечный спуск над Q) — переиспользуемый role-limit-свидетель, заземляющий нить запрещённых симметрий q-kinematics (T-gate/45°).
> _Caveat:_ Иррациональность √2 — древнейшая классика; уникальность — в роли переиспользуемого role-limit-якоря (H2), не в доказательстве.

---

## #62 - `src/analysis/Sqrt3Irrational.v` - score 3 (new-framing)

**sqrt3 is irrational**

- **Topic.** no rational r with r^2=3, by descent; the sqrt3 role-limit witness for the 60-degree point, Eisenstein/hexagonal thread and IndependenceQ23.
- **Role.** Irrationality core (reused by IndependenceQ23, q-kinematics 60-degree/Eisenstein, RationalLorentz). Self-contained.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith ZArith
- **E/R/R.** _Elements:_ рациональные кандидаты r с r²=3. _Roles:_ √3 как role-limit (60°-точка запрещена для рациональных). _Rules:_ спуск: r²=3 невозможно над Q. _P4:_ √3 — role-limit; запрещает рациональную 60°-точку (④), Пелля-процесс x²−3y²=1 — Element-стадии.
- **Classical counterpart.** The irrationality of sqrt3 is classical; NEW: nothing -- a descent Q proof, REUSED for the 60-degree / crystallographic-restriction role-limit in q-kinematics.
- **Tags.** sqrt3, irrationality, role-limit, q-kinematics, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `mod-3 / parity helpers` | Lemma | вспомогательные для спуска |
| `no_rational_sqrt3 / sqrt3_irrational / sqrt3_irrational_Z` | Theorem | ★ нет r∈Q с r²=3 |

**Key lemmas (deep):**

- **`no_rational_sqrt3`** - √3 иррационален спуском над Q — role-limit, запрещающий рациональную 60°-точку (кристаллографическое ограничение ④) и используемый в IndependenceQ23 (√3∉Q[√2]), Эйзенштейновых тройках, RationalLorentz. Канонический квадратичный role-limit с Пелля-процессом x²−3y²=1. _(sqrt3, irrationality, role-limit, 60-degree)_

**Uniqueness - score 3 (new-framing).** √3 иррационален — переиспользуемый role-limit, запрещающий рациональную 60°-точку (④) и несущий IndependenceQ23/Эйзенштейн/Лоренц.
> _Caveat:_ Иррациональность √3 классична; уникальность — в роли переиспользуемого role-limit-якоря, не в доказательстве.

---

## #63 - `src/analysis/Sqrt5Irrational.v` - score 3 (new-framing)

**sqrt5 is irrational**

- **Topic.** no rational r with r^2=5, by descent; the sqrt5 role-limit witness for phi/Fibonacci, the icosahedron (forbidden order-5), and the pentagon thread.
- **Role.** Irrationality core (reused by GoldenFibonacci, CrystallographicRestriction order-5, ConstructiblePolygons pentagon, MarkovTree). Self-contained.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith ZArith
- **E/R/R.** _Elements:_ рациональные кандидаты r с r²=5. _Roles:_ √5 как role-limit (порядок-5/икосаэдр запрещён для рациональных). _Rules:_ спуск: r²=5 невозможно над Q. _P4:_ √5 — role-limit; запрещает рациональный порядок 5/икосаэдр (④), φ/Фибоначчи-процесс — Element-стадии.
- **Classical counterpart.** The irrationality of sqrt5 is classical; NEW: nothing -- a descent Q proof, REUSED for the golden ratio / icosahedron / pentagon role-limit in q-kinematics.
- **Tags.** sqrt5, irrationality, role-limit, q-kinematics, golden-ratio, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `mod-5 / parity helpers` | Lemma | вспомогательные для спуска |
| `no_rational_sqrt5 / sqrt5_irrational` | Theorem | ★ нет r∈Q с r²=5 |

**Key lemmas (deep):**

- **`no_rational_sqrt5`** - √5 иррационален спуском над Q — role-limit, запрещающий рациональный порядок-5/икосаэдр (④) и несущий золотое сечение φ (GoldenFibonacci), пентагон (ConstructiblePolygons), дерево Маркова. Канонический квадратичный role-limit с процессом Фибоначчи. _(sqrt5, irrationality, role-limit, golden-ratio)_

**Uniqueness - score 3 (new-framing).** √5 иррационален — переиспользуемый role-limit, запрещающий рациональный порядок-5/икосаэдр (④) и несущий φ/Фибоначчи/пентагон/Марков.
> _Caveat:_ Иррациональность √5 классична; уникальность — в роли переиспользуемого role-limit-якоря, не в доказательстве.

---

## #64 - `src/analysis/StepIntegral.v` - score 2 (methods)

**The step-function integral over Q**

- **Topic.** Step functions, their integral, additivity over concatenation, monotonicity, linearity and basic bounds -- the foundation of the constructive measure thread.
- **Role.** Foundation of the constructive integration/measure thread over Q (feeds Lebesgue/Fubini/DCT). Self-contained.
- **Counts.** Qed 17 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith List
- **E/R/R.** _Elements:_ ступенчатые функции; их интеграл. _Roles:_ интеграл ступенчатых как первичная роль (мера выводится из него). _Rules:_ аддитивность, монотонность, линейность интеграла. _P4:_ ступенчатый интеграл конечен и точен над Q (Element); фундамент measure-from-integral.
- **Classical counterpart.** The integral of step (simple) functions, additivity, monotonicity and linearity are the classical starting point of integration theory; NEW: nothing -- the constructive Q step integral the measure thread builds on.
- **Tags.** step-integral, integration, foundation, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `step functions / step integral` | Definition | ступенчатые функции и интеграл |
| `integral additivity / monotonicity / linearity / bounds` | Lemma | ★ аддитивность, монотонность, линейность |

**Key lemmas (deep):**

- **`integral additivity / monotonicity / linearity`** - Интеграл ступенчатых функций над Q с аддитивностью/монотонностью/линейностью — ПЕРВИЧНЫЙ объект, из которого LebesgueMeasure выводит меру (мера = интеграл индикатора). Element-сторона: точный конечный интеграл, фундамент всей конструктивной теории меры. _(step-integral, additivity, foundation)_

**Uniqueness - score 2 (methods).** Ступенчатый интеграл над Q (аддитивность/монотонность/линейность) — первичный фундамент measure-from-integral подхода.
> _Caveat:_ Интеграл простых функций — классическое начало теории интеграла; вклад — конструктивная Q-база, не новый результат.

---

## #65 - `src/analysis/StoneWeierstrass.v` - score 3 (new-framing)

**Stone-Weierstrass: polynomial approximation over Q**

- **Topic.** Polynomial approximation of continuous functions on a rational grid with explicit epsilon error bounds, the algebra of approximants, and density.
- **Role.** Approximation theory over Q (Stone-Weierstrass). Self-contained.
- **Counts.** Qed 24 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ непрерывные функции; полиномиальные приближения на Q-сетке. _Roles:_ полиномы как плотная подалгебра (роль приближения). _Rules:_ приближение с epsilon-границей; алгебра приближений. _P4:_ приближение — ПРОЦЕСС с явной epsilon-ошибкой (Element-стадии), плотность — role-limit.
- **Classical counterpart.** The Stone-Weierstrass theorem (polynomials/subalgebras dense in continuous functions) is classical; NEW is only a constructive Q form: explicit polynomial approximation with epsilon bounds on a rational grid.
- **Tags.** stone-weierstrass, approximation, polynomial, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `polynomial approximation / epsilon bounds` | Definition/Lemma | полиномиальное приближение с epsilon |
| `stone_weierstrass (density)` | Theorem | ★ полиномы плотны (приближают с любой epsilon) |

**Key lemmas (deep):**

- **`stone_weierstrass (density)`** - Стоун-Вейерштрасс над Q: непрерывная функция приближается полиномом с любой заданной epsilon на Q-сетке. Element-сторона: приближение — конструктивный процесс с явной ошибкой; плотность (предел) — role-limit. _(stone-weierstrass, polynomial-approximation, density)_

**Uniqueness - score 3 (new-framing).** Стоун-Вейерштрасс над Q: явное полиномиальное приближение непрерывных функций с epsilon-границами на рациональной сетке — приближение как конструктивный процесс.
> _Caveat:_ Стоун-Вейерштрасс классичен; вклад — конструктивная эпсилон-Q-версия, не новый результат.

