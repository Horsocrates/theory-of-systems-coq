# Database - cluster `foundation`

_Generated from `foundation.json` by `generate.ps1` - do not edit by hand; edit the JSON._

**150 files / 658 Qed.** Score distribution: s5=0 / s4=1 / s3=35 / s2=96 / s1=18 / s0=0

---

## #161 - `src/foundation/AcousticChainThreeFormulas.v` - score 2 (methods)

**Acoustic chain in E/R/R three-formula form over Q**

- **Topic.** A coupled chain (step/impulse/zero), squared frequencies for a 4-chain, ground proxy, mode spectrum (fundamental, max, degenerate modes), the level ladder, causal wavefront propagation, and faster coupling.
- **Role.** E/R/R single-system re-derivation (acoustic). Part of the three-formula physics layer. Self-contained (QArith).
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ моды цепочки; импульс; основная частота. _Roles:_ акустическая система = роль (фонон); причинный фронт как роль. _Rules:_ omega_sq_chain4; mode ladder; wavefront_causal. _P4:_ конечная цепочка мод над Q (Element); акустика в E/R/R-форме трёх формул.
- **Classical counterpart.** The 1D harmonic chain / phonon spectrum and causal wavefront propagation are standard; NEW only as an E/R/R three-formula re-derivation over Q (modes, ladder, causal wavefront from one chain).
- **Tags.** foundation, acoustic, three-formula, err, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `chain_step/chain_impulse/chain_zero/omega_sq_chain4/chain4_ground_proxy/_value/_positive` | Definition/Theorem | цепочка, частоты, основное состояние |
| `mode0_has_no_zero_point/mode_spectrum_chain4/fundamental_is_mode1/max_freq_is_mode2/modes_1_3_degenerate/mode_level/mode1_level0/_level1/mode1_spacing/mode2_spacing/degenerate_modes_same_ladder` | Theorem | ★ спектр мод, лестница уровней |
| `impulse_propagates/wavefront_causal/source_after_step/faster_coupling/acoustic_chain_three_formulas` | Theorem | причинный фронт |

**Key lemmas (deep):**

- **`wavefront_causal`** - Фронт акустической волны причинен (конечная скорость) на цепочке над Q — E/R/R-переобрамление фононной цепочки. Стандартная физика, переписанная в трёх-формульной форме. _(acoustic, phonon, causal, err)_

**Uniqueness - score 2 (methods).** Акустическая цепочка в E/R/R-форме над Q: моды, лестница уровней, причинный фронт из одной цепочки.
> _Caveat:_ Фононная цепочка и причинное распространение классичны; вклад — E/R/R-переобрамление, не новый результат.

---

## #162 - `src/foundation/AnharmonicSHO.v` - score 2 (methods)

**Anharmonic SHO over Q: Morse correction, H2/CO vibrational predictions**

- **Topic.** Morse levels as SHO plus a negative anharmonic correction, H2 omega/x_e and gaps (0-1, 1-2, overtone, ratio below 2), and CO omega/x_e gaps — concrete rational predictions.
- **Role.** E/R/R single-system re-derivation (anharmonic oscillator) with numerical molecular predictions. Self-contained (QArith).
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ уровни Морса; ангармоническая поправка; H2/CO константы. _Roles:_ ангармонизм = роль-поправка к SHO; молекула как система. _Rules:_ morse_is_sho_plus_correction; correction_negative; H2_gap_decreases. _P4:_ конечные рациональные предсказания над Q (Element); ангармонизм в E/R/R-форме.
- **Classical counterpart.** The Morse oscillator, anharmonic correction and H2/CO vibrational gaps are standard molecular spectroscopy; NEW only as exact rational predictions in E/R/R form.
- **Tags.** foundation, morse, anharmonic, prediction, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `morse_level/anharm_correction/morse_is_sho_plus_correction/correction_negative/morse_below_harmonic` | Definition/Theorem | ★ Морс = SHO + отрицательная поправка |
| `H2_omega/H2_xe/H2_morse_0/H2_harmonic_gap/H2_morse_gap_01/_value/_12/H2_gap_decreases/_01_numeric/H2_overtone_gap/_value/_numeric/_ratio_below_2` | Theorem | ★ предсказания H2 (gaps, обертон) |
| `CO_omega/CO_xe/CO_gap_01_numeric/anharmonic_predictions` | Theorem | предсказания CO |

**Key lemmas (deep):**

- **`H2_gap_decreases`** - Ангармонический зазор H2 убывает с номером уровня (overtone_ratio_below_2) — конкретное рациональное молекулярное предсказание над Q в E/R/R-форме. Стандартная спектроскопия Морса, точно формализованная. _(morse, h2, anharmonic, prediction)_

**Uniqueness - score 2 (methods).** Ангармонический SHO над Q: Морс=SHO+поправка, рациональные предсказания H2/CO (зазоры, обертоны).
> _Caveat:_ Осциллятор Морса и молекулярные зазоры — стандартная спектроскопия; вклад — точные Q-предсказания в E/R/R-форме, не новая физика.

---

## #163 - `src/foundation/AnomalyChargeQuantization.v` - score 2 (methods)

**Anomaly charge quantization over Q: hypercharges forced by anomaly cancellation**

- **Topic.** SM hypercharges Y, color/weak/grav/cubic anomalies, the Witten anomaly, all anomalies cancel, hypercharges forced, the SM Vieta relation, electric charges quantized, and proton/neutron charges.
- **Role.** SM-physics leaf (anomaly cancellation). SM-from-distinction is OVER-BRANDED. Self-contained (QArith).
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ гиперзаряды Y; аномалии (color/weak/grav/cubic). _Roles:_ сокращение аномалий = роль, фиксирующая гиперзаряды. _Rules:_ all_anomalies_cancel; hypercharges_forced; charges_quantized. _P4:_ конечная проверка над Q (Element); SM-из-различения OVER-BRANDED — доказано лишь сокращение аномалий, не вывод СМ из онтологии.
- **Classical counterpart.** Gauge/gravitational anomaly cancellation forcing SM hypercharge quantization (Witten, charge quantization) is well-known particle theory; NEW only as an exact rational Coq check — and the 'from distinction' framing is OVER-BRANDED.
- **Tags.** foundation, anomaly, charge-quantization, over-branded, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `YQ/Yu/Yd/YL/Ye/anomaly_color/_weak/_grav/_cubic/n_doublets/anomaly_witten` | Definition/Theorem | гиперзаряды, аномалии |
| `all_anomalies_cancel/hypercharges_forced/split_forced/sm_vieta` | Theorem | ★ аномалии сокращаются, гиперзаряды фиксированы |
| `Qem_up/_down/_elec/_nu/charges_quantized/proton_neutron/anomaly_charge_quantization` | Theorem | ★ электрозаряды квантованы |

**Key lemmas (deep):**

- **`all_anomalies_cancel`** - Сокращение color/weak/grav/cubic + Виттен-аномалии фиксирует гиперзаряды СМ и квантует электрозаряды — реальный алгебраический факт физики частиц, точно над Q. Но «из различения» OVER-BRANDED: доказана алгебра аномалий, а не вывод СМ из онтологии ToS. _(anomaly, charge-quantization, over-branded)_

**Uniqueness - score 2 (methods).** Аномалии СМ сокращаются над Q → гиперзаряды фиксированы, электрозаряды квантованы (Виттен + кубическая).
> _Caveat:_ Сокращение аномалий и квантование зарядов — известная физика частиц; вклад — точная Q-проверка; «из различения» OVER-BRANDED.

---

## #164 - `src/foundation/AnomalyExhaustive.v` - score 2 (methods)

**Anomaly exhaustive over Q: SM unique among tested assignments**

- **Topic.** Linear and cubic anomaly conditions, the SM Y5 value satisfying both, the all-equal trivial case, and several named alternatives failing the cubic condition; SM unique among tested.
- **Role.** SM-physics leaf (anomaly uniqueness check). SM-from-distinction OVER-BRANDED. Self-contained (QArith).
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ линейное/кубическое условия аномалий; альтернативные присвоения. _Roles:_ условие аномалии = роль-фильтр присвоений. _Rules:_ sm_satisfies_linear/_cubic; alternatives fail cubic; sm_unique_among_tested. _P4:_ конечный перебор присвоений над Q (Element); СМ-уникальность среди ПРОВЕРЕННЫХ (не доказана глобальная единственность).
- **Classical counterpart.** That the SM hypercharge assignment is essentially the unique anomaly-free chiral solution is known; NEW only as an exhaustive rational check that named alternatives fail the cubic condition.
- **Tags.** foundation, anomaly, uniqueness, over-branded, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `linear_cond/cubic_cond/check_anomaly/sm_Y5_value/sm_satisfies_linear/_cubic/sm_is_solution` | Definition/Theorem | условия аномалий, СМ их удовлетворяет |
| `all_equal_trivial/alt_000_fails_cubic/alt_m1_1_0_Y5/_fails_cubic/alt_third_mthird_0_fails_cubic/sm_unique_among_tested` | Theorem | ★ альтернативы проваливают кубическое; СМ уникальна среди тестов |

**Key lemmas (deep):**

- **`sm_unique_among_tested`** - СМ-присвоение уникально среди ПРОВЕРЕННЫХ альтернатив (они проваливают кубическое условие) — честная формулировка: «среди протестированных», не глобальная единственность. Точный перебор над Q. _(anomaly, uniqueness, exhaustive, honest)_

**Uniqueness - score 2 (methods).** Перебор присвоений аномалий над Q: СМ удовлетворяет линейное+кубическое, перечисленные альтернативы проваливают кубическое — СМ уникальна среди протестированных.
> _Caveat:_ Анти-аномальная единственность СМ известна; вклад — точный конечный перебор (честно «среди тестов»), не новый результат.

---

## #165 - `src/foundation/AnomalySystematic.v` - score 1 (exposition)

**Anomaly systematic over Q: scan of hypercharge candidates**

- **Topic.** Cubic-after-linear, the SM cubic zero, an SM permutation works, and a systematic scan of Y2 and Y4 candidate values all failing.
- **Role.** SM-physics leaf (anomaly scan). SM-from-distinction OVER-BRANDED. Self-contained (QArith).
- **Counts.** Qed 1 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ кандидаты Y2/Y4; кубическое условие. _Roles:_ систематический скан = роль-перебор. _Rules:_ sm_cubic_zero; test_Y2_*_fails; test_sm_Y4_*_fails. _P4:_ конечный скан кандидатов над Q (Element); большинство проваливаются.
- **Classical counterpart.** Systematic scanning of hypercharge candidates against anomaly conditions is standard; NEW only as a rational enumeration where many Y2/Y4 values fail.
- **Tags.** foundation, anomaly, scan, over-branded, exposition

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `cubic_after_linear/sm_cubic_zero/sm_permuted_works` | Theorem | СМ-кубическое = 0, перестановка работает |
| `test_Y2_0_fails/_1_6_fails/_1_3_fails/_neg1_3_fails/_1_2_fails/_neg1_2_fails/_2_3_fails/_neg2_3_fails/_1_fails/_neg1_fails/test_sm_Y4_0_fails/_1_3_fails/_neg1_3_fails/_1_6_fails/anomaly_systematic_summary` | Theorem | ★ скан Y2/Y4: все проваливаются |

**Key lemmas (deep):**

- **`anomaly_systematic_summary`** - Систематический скан Y2/Y4-кандидатов: все перечисленные значения проваливают кубическое условие — точный конечный перебор над Q, подкрепляющий уникальность СМ. Стандартное содержание, честно перечислено. _(anomaly, scan, exhaustive)_

**Uniqueness - score 1 (exposition).** Систематический скан гиперзарядов над Q: перечисленные Y2/Y4 проваливают кубическое условие.
> _Caveat:_ Скан кандидатов аномалий стандартен; конечный Q-перебор без нового содержания.

---

## #166 - `src/foundation/AntigravityCondition.v` - score 1 (exposition)

**Antigravity condition over Q: repulsion needs tension**

- **Topic.** Source attracts, antigravity iff conditions, three spatial dimensions, the equation of state, a zero threshold, dust/radiation/positive-pressure attract, lambda antigravity, antigravity needs tension, realizable.
- **Role.** Gravity/cosmology leaf. Self-contained (QArith).
- **Counts.** Qed 1 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ источник; уравнение состояния; давление/натяжение. _Roles:_ антигравитация = роль (нарушение SEC); натяжение как роль-источник отталкивания. _Rules:_ antigravity_needs_tension; dust/radiation attracts; lambda_antigravity. _P4:_ конечные оценки над Q (Element); антигравитация требует натяжения.
- **Classical counterpart.** The strong-energy-condition violation (negative pressure / tension drives repulsive gravity; dust and radiation attract) is standard GR; here a small Q instance.
- **Tags.** foundation, antigravity, gravity, exposition

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `source/attracts/antigravity/attracts_iff/antigravity_iff/three_is_spatial_dims/source_eos/threshold_zero` | Definition/Theorem | источник, уравнение состояния |
| `dust_attracts/radiation_attracts/positive_pressure_attracts/lambda_antigravity/antigravity_needs_tension/antigravity_realizable/antigravity_structure` | Theorem | ★ антигравитация требует натяжения |

**Key lemmas (deep):**

- **`antigravity_needs_tension`** - Отталкивающая гравитация требует натяжения (отрицательного давления) — нарушение сильного энергетического условия над Q. Стандартная ОТО, дуют/радиация притягивают. Иллюстративно. _(antigravity, tension, SEC)_

**Uniqueness - score 1 (exposition).** Условие антигравитации над Q: отталкивание требует натяжения, пыль/радиация притягивают, Lambda даёт антигравитацию.
> _Caveat:_ Нарушение сильного энергетического условия — стандартная ОТО; Q-инстанс без нового содержания.

---

## #167 - `src/foundation/AperyConstantERR.v` - score 2 (methods)

**Apery constant in E/R/R form over Q: zeta(3) bracketed**

- **Topic.** Inverse cubes, partial sums of zeta(3) (s1..s5), bounds (s5 above 1.185 / below 1.186), Apery convergents, the bracket a3 in (1.202, 1.203), and that zeta(3) brackets the observed value.
- **Role.** Numerical-constant leaf (E/R/R, machine-verified bracket). Self-contained (QArith).
- **Counts.** Qed 2 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ частичные суммы zeta(3); обратные кубы. _Roles:_ константа Апери = role-limit процесса частичных сумм. _Rules:_ apery_3_above_1202; apery_3_below_1203; apery_3_brackets_observed. _P4:_ частичные суммы конечны над Q (Element); zeta(3) — role-limit с машинно-проверенной рациональной скобкой [1.202,1.203].
- **Classical counterpart.** zeta(3) = Apery's constant ~1.202 and its rational convergents are classical; NEW only as a machine-verified rational bracket placing zeta(3) in [1.202, 1.203] over Q.
- **Tags.** foundation, apery, zeta3, numerical, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `inv_cube/zeta3_partial/zeta3_s1/_s2/_s3/_s4/_s5/_s5_above_1185/_s5_below_1186/_s5_below_6_5/_s3_below_s4` | Definition/Theorem | частичные суммы и оценки |
| `apery_1/_2/_3/_2_value/_3_value/_2_above_1197/_2_below_1198/_3_above_1202/_3_below_1203` | Theorem | ★ скобка a3 ∈ (1.202,1.203) |
| `standard_s3_below_apery_3/_below_12/apery_3_brackets_observed/apery_constant_err` | Theorem | ★ zeta(3) скобит наблюдаемое |

**Key lemmas (deep):**

- **`apery_3_brackets_observed`** - zeta(3) машинно зажата в рациональную скобку (1.202,1.203) над Q — частичные суммы как Element-процесс, константа Апери как role-limit. Один из честно-верифицируемых численных результатов проекта (см. CLAUDE.md), но zeta(3) — классическая константа. _(apery, zeta3, bracket, machine-verified)_

**Uniqueness - score 2 (methods).** Константа Апери zeta(3) над Q: машинно-проверенная рациональная скобка (1.202,1.203) из частичных сумм (E/R/R role-limit).
> _Caveat:_ zeta(3)=константа Апери классична; вклад — точная машинно-проверенная Q-скобка, не новый результат об иррациональности.

---

## #168 - `src/foundation/ApplicationsAudit.v` - score 2 (methods)

**Applications audit over Q: which derivations are genuine (honesty meta + 2n^2 shells)**

- **Topic.** Shell capacities 2,8,18,32 and the 2n^2 capacity law, actual atomic periods carrying Aufbau doubling, an application-kind classifier, and the honest finding that not all applications are genuine.
- **Role.** Honesty/meta leaf auditing the application claims. Periodic-table 2n^2 is OVER-BRANDED. Self-contained (QArith).
- **Counts.** Qed 1 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ ёмкости оболочек (2,8,18,32); виды приложений. _Roles:_ аудит = роль-классификатор подлинности приложений. _Rules:_ capacities_are_2n2; is_genuine; not_all_genuine. _P4:_ конечный аудит над Q (Element); ЧЕСТНО: не все приложения подлинны; 2n² OVER-BRANDED.
- **Classical counterpart.** No classical counterpart — an internal HONESTY audit classifying which applications are genuine derivations vs not, plus the 2,8,18,32 shell capacities (2n^2, which is OVER-BRANDED).
- **Tags.** foundation, honesty, audit, over-branded, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `shell_capacity/capacities_2_8_18_32/capacity_law/capacities_are_2n2/actual_periods/periods_carry_aufbau_doubling` | Definition/Theorem | ёмкости 2,8,18,32 = 2n² |
| `AppKind/App/app_kind/all_apps/is_genuine/n_genuine/kinds_classified/not_all_genuine/applications_audit` | Definition/Theorem | ★ ЧЕСТНО: не все приложения подлинны |

**Key lemmas (deep):**

- **`not_all_genuine`** - Внутренний ЧЕСТНЫЙ аудит: классифицирует приложения и доказывает, что НЕ ВСЕ подлинны (n_genuine < all). Образец встроенной калибровки против over-claim. Ёмкости 2n² корректны, но как «предсказание» OVER-BRANDED. _(honesty, audit, 2n2, over-branded)_

**Uniqueness - score 2 (methods).** Аудит приложений над Q: ёмкости оболочек = 2n², но ЧЕСТНО доказано, что не все приложения — подлинные выводы (встроенная калибровка).
> _Caveat:_ 2n²-ёмкости — учебная химия (OVER-BRANDED как предсказание); ценность файла — честная самооценка подлинности, не новый результат.

---

## #169 - `src/foundation/ArrowFromDistinction.v` - score 2 (new-framing)

**Arrow of time from distinction over Q: irreversibility from succ/pred asymmetry**

- **Topic.** A time step, the initial moment with nothing before it, time going forward, no cycles, entropy increasing (second law, monotone), a time process with an arrow, pred cannot undo succ, no negative time, and thermodynamic = cosmological arrow.
- **Role.** Distinction-spine leaf (arrow of time). Self-contained.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ временной шаг; начальный момент; энтропия. _Roles:_ стрела времени = роль из асимметрии различения; succ необратим pred. _Rules:_ distinction_creates_arrow; second_law; arrows_agree. _P4:_ конечные временные шаги (Element); стрела времени = асимметрия succ/pred, не дополнительный постулат.
- **Classical counterpart.** The thermodynamic/cosmological arrow of time from monotone entropy and irreversibility is standard; NEW is the framing that the arrow arises from the asymmetry of distinction itself (pred cannot undo succ), with thermo and cosmo arrows agreeing.
- **Tags.** foundation, arrow-of-time, distinction, new-framing

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `time_step/initial_moment/no_before_initial/time_goes_forward/no_time_cycles` | Definition/Theorem | временной шаг, нет начала до начала |
| `entropy/_initial/entropy_increases/second_law/entropy_monotone/time_process/has_arrow/vacuum_has_arrow/constant_no_arrow` | Theorem | ★ энтропия растёт, второй закон |
| `distinction_creates_arrow/pred_cannot_undo_succ_at_zero/no_negative_time/thermodynamic_arrow/cosmological_arrow/arrows_agree/arrow_from_distinction_summary/arrow_theorem_count` | Theorem | ★ различение создаёт стрелу; стрелы согласованы |

**Key lemmas (deep):**

- **`distinction_creates_arrow`** - Стрела времени выводится из асимметрии различения (pred не отменяет succ в нуле, no_negative_time) — переобрамление «стрелы» как структурного следствия succ/pred, а не отдельного постулата. Термо- и космологическая стрелы согласованы. Содержательное наблюдение, не новая физика. _(arrow-of-time, distinction, irreversible, succ-pred)_

**Uniqueness - score 2 (new-framing).** Стрела времени из различения над Q: необратимость из асимметрии succ/pred, второй закон, термо=космо стрелы.
> _Caveat:_ Стрела времени из монотонной энтропии стандартна; вклад — переобрамление через асимметрию различения, не новый результат.

---

## #170 - `src/foundation/ArrowGroundingDescent.v` - score 1 (exposition)

**Arrow grounding descent over Q: what is grounded vs posited in the arrow**

- **Topic.** A generation count with monotone arrow, a trajectory where direction is not the sign, generations up but entropy down, a peak start giving no increase, an arrow-aspect/grounding split, and the honest split of what is grounded.
- **Role.** Honesty/descent leaf for the arrow of time (separates grounded from posited). Uses local section hypothesis (discharged), axioms=0. Self-contained.
- **Counts.** Qed 1 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ счётчик поколений; траектория; пик. _Roles:_ обоснование = роль; аспект стрелы vs обоснование = разделение. _Rules:_ direction_not_sign; peak_start_no_increase; aspect_grounding/the_split. _P4:_ конечный счётчик (Element); ЧЕСТНО разделяет обоснованное (направление энтропии) и постулированное (знак).
- **Classical counterpart.** No direct counterpart — an internal 'descent' file separating what is grounded (entropy direction) from what is not (the sign convention), honest about the gap.
- **Tags.** foundation, honesty, arrow, descent, exposition

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `gen_count/gen_arrow_monotone/W_traj/direction_not_sign/gen_up_but_entropy_down/peak/low_start_has_room/peak_start_no_increase` | Definition/Theorem | траектория, направление≠знак |
| `ArrowAspect/Grounding/aspect_grounding/the_split/arrow_grounding_descent` | Definition/Theorem | ★ разделение обоснованного и постулированного |

**Key lemmas (deep):**

- **`the_split`** - ЧЕСТНОЕ разделение: что в стреле времени обосновано (направление энтропии) vs постулировано (знаковая конвенция). gen_up_but_entropy_down показывает, что направление ≠ знак. Образец калибровки. Использует локальную секционную гипотезу (разряжается), не глобальную аксиому. _(honesty, grounding, descent, arrow)_

**Uniqueness - score 1 (exposition).** Спуск-обоснование стрелы над Q: разделяет обоснованное направление энтропии и постулированный знак (честная калибровка).
> _Caveat:_ Внутренний honesty-файл; собственного результата нет, ценность — в разделении обоснованного/постулированного.

---

## #171 - `src/foundation/AsymmetricDistinction.v` - score 3 (new-framing)

**Asymmetric distinction over Q: negation presupposes affirmation (the L2 root)**

- **Topic.** The negative depends on the positive, the positive is given, negation presupposes affirmation, swap (involution) changes positive/reverses direction, the marked > unmarked order, one precedes zero, positive has content / negative vacuous, before/after exclusive and exhaustive, and asymmetry inherent.
- **Role.** Distinction-spine root (the asymmetry of L2). Foundational framing. Self-contained.
- **Counts.** Qed 2 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ положительная/отрицательная стороны различения; метка. _Roles:_ асимметрия = роль (positive дан, negative зависим); swap как инволюция-разворот. _Rules:_ negation_presupposes_affirmation; marked_greater_than_unmarked; asymmetry_inherent. _P4:_ конечное различение (Element); асимметрия ВСТРОЕНА — отрицание presupposes утверждение, не симметричная пара.
- **Classical counterpart.** Spencer-Brown's 'Laws of Form' (a distinction has a marked/unmarked asymmetry) and that negation presupposes affirmation are philosophical; NEW is the formal Q/Coq statement that the distinction is inherently asymmetric (swap is an involution that reverses direction).
- **Tags.** foundation, distinction, asymmetry, L2-root, new-framing

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `negative_depends_on_positive/positive_is_given/negation_presupposes_affirmation/swap_distinction/swap_changes_positive/swap_involution_positive/_negative/distinction_asymmetric` | Theorem | ★ отрицание presupposes утверждение; swap инволютивен |
| `mark/unmark/marked_greater_than_unmarked/distinction_order/one_precedes_zero_in_distinction/positive_has_content/negative_vacuous_when_positive` | Definition/Theorem | ★ метка > не-метка; порядок различения |
| `distinction_direction/direction_stable/direction_reversed_by_swap/before/after/before_after_exclusive/_exhaustive/asymmetry_inherent/asymmetric_distinction_summary/_theorem_count` | Theorem | направление, before/after исчерпывают |

**Key lemmas (deep):**

- **`negation_presupposes_affirmation`** - Формализует асимметрию различения (Laws of Form): отрицательная сторона ЗАВИСИТ от положительной (positive_is_given), отрицание presupposes утверждение, swap — инволюция, разворачивающая направление. Корень L2 в ToS: различение не симметричная пара, а направленный акт. Философская идея, формализованная над Q. _(distinction, asymmetry, spencer-brown, L2-root)_

**Uniqueness - score 3 (new-framing).** Асимметрия различения над Q: отрицание presupposes утверждение, метка>не-метка, swap-инволюция разворачивает направление — формальный корень L2 (различение направлено, не симметрично).
> _Caveat:_ Идея асимметрии различения восходит к Spencer-Brown «Laws of Form»; вклад — её формализация над Q как корня L2, не новая логика.

---

## #172 - `src/foundation/AsymptoticFreedomBound.v` - score 2 (methods)

**Asymptotic freedom bound over Q: max generations, N_strong=3**

- **Topic.** A pi approximation, beta_0 (and SU(3)), the AF condition for SU(3)/SU(2)/SU(N) with 3 generations, monotonicity in N_c, the SU(3)/SU(2) bounds (fail at 9/6 generations), max generations, three is the minimum non-binary, and N_strong=3.
- **Role.** SM-physics leaf (asymptotic freedom). SM-from-distinction OVER-BRANDED. Self-contained (QArith).
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ beta_0; число цветов N_c; число поколений. _Roles:_ асимптотическая свобода = роль (знак beta); граница поколений. _Rules:_ af_su3_3gen; af_su3_fails_9; N_strong_is_3. _P4:_ конечные оценки beta над Q (Element); граница max-поколений из знака beta; SM-framing OVER-BRANDED.
- **Classical counterpart.** The one-loop beta-function sign (asymptotic freedom for SU(N) with few generations, the 11N/3 - 2nf/3 bound) is standard QCD; NEW only as a rational instance bounding the max generations and identifying N_strong=3.
- **Tags.** foundation, asymptotic-freedom, qcd, over-branded, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `pi_approx/beta_0/beta_0_su3/af_condition/af_su3_3gen/af_su2_3gen/af_any_N_3gen/af_monotone_Nc` | Definition/Theorem | условие АС, монотонность по N_c |
| `af_su3_bound/af_su3_fails_9/af_su2_bound/af_su2_fails_6/max_gen_su3/max_gen_su2/three_is_min_nonbinary/N_strong_is_3` | Theorem | ★ граница поколений, N_strong=3 |
| `af_su4_3gen/af_su5_3gen/af_all_above_3/af_summary/af_theorem_count` | Theorem | АС для SU(4/5) |

**Key lemmas (deep):**

- **`N_strong_is_3`** - Знак одно-петлевой beta-функции ограничивает максимум поколений (SU(3) проваливает АС при 9, SU(2) при 6) и выделяет N_strong=3 — стандартный КХД-факт над Q. SM-from-distinction OVER-BRANDED: алгебра beta-функции, не вывод из онтологии. _(asymptotic-freedom, beta-function, N-strong, over-branded)_

**Uniqueness - score 2 (methods).** Граница асимптотической свободы над Q: max-поколения из знака beta (SU(3) fails@9, SU(2)@6), N_strong=3.
> _Caveat:_ Знак beta-функции и асимптотическая свобода — стандартная КХД; вклад — Q-инстанс; SM-framing OVER-BRANDED.

---

## #173 - `src/foundation/BackgroundIndependence.v` - score 2 (new-framing)

**Background independence over Q: geometry from order, metric from roles**

- **Topic.** Interval cardinality, geometry from order, geometry tracks order, a metric (symmetric, depending on roles), and relational not fixed-background.
- **Role.** Foundational leaf (relational geometry, vein-C-flavoured). Self-contained.
- **Counts.** Qed 2 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ интервалы; порядок; метрика. _Roles:_ геометрия = роль из порядка/отношений, не из фиксированного фона. _Rules:_ geometry_from_order; metric_depends_on_roles; relational_not_fixed_background. _P4:_ конечные интервалы (Element); геометрия реляционна (из ролей), фон не постулируется.
- **Classical counterpart.** Background independence (geometry from relations/order, not a fixed background) is a GR/quantum-gravity principle; NEW only as a small Q instance where the metric depends on roles and geometry tracks order.
- **Tags.** foundation, background-independence, relational, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `interval_card/geometry_from_order/geometry_tracks_order` | Definition/Theorem | геометрия из порядка |
| `metric/metric_symmetric/metric_depends_on_roles/relational_not_fixed_background/background_independence` | Theorem | ★ метрика из ролей, фон-независимость |

**Key lemmas (deep):**

- **`background_independence`** - Геометрия возникает из порядка/ролей (metric_depends_on_roles), а не из фиксированного фона — формализация принципа фон-независимости над Q (вена-C-смежно: геометрия реляционна). Принцип КГ, переписанный в ToS-онтологии. _(background-independence, relational, geometry, vein-C)_

**Uniqueness - score 2 (new-framing).** Фон-независимость над Q: геометрия из порядка, метрика из ролей, реляционно (без фиксированного фона).
> _Caveat:_ Фон-независимость — принцип ОТО/квантовой гравитации; вклад — малый Q-инстанс в ToS-онтологии, не новый результат.

---

## #174 - `src/foundation/BaryogenesisBoundary.v` - score 2 (new-framing)

**Baryogenesis boundary over Q: element-derived vs role-limit (two walls)**

- **Topic.** An open box and boundary-kind classifier, the Jarlskog value and sphaleron as role-limits, departure as a different arena, counting role-limits, two finitization walls, a box-status with all-element-derived vs Jarlskog/sphaleron element-derived.
- **Role.** Baryogenesis-boundary leaf (honest element/role-limit audit, vein-A-flavoured). Self-contained.
- **Counts.** Qed 1 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ величины бариогенезиса (Jarlskog, сфалерон); статусы. _Roles:_ граница = роль-классификатор (element-derived vs role-limit). _Rules:_ jvalue_role_limit; two_finitization_walls; all_element_derived. _P4:_ конечная классификация (Element); ДВЕ стены финитизации — что выводимо как Element vs остаётся role-limit (честный аудит).
- **Classical counterpart.** Baryogenesis quantities (Jarlskog, sphaleron rate) are standard; NEW is the ToS framing that classifies which are element-derived vs role-limit ('two finitization walls'), an honest boundary audit.
- **Tags.** foundation, baryogenesis, finitization-boundary, vein-A, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `OpenBox/BoundaryKind/boundary_kind/jvalue_role_limit/sphaleron_role_limit/departure_different_arena/is_role_limit/n_role_limits/two_finitization_walls` | Definition/Theorem | ★ две стены финитизации |
| `BoxStatus/box_status/all_element_derived/jvalue_element_derived/sphaleron_element_derived/baryogenesis_boundary` | Definition/Theorem | статусы element-derived |

**Key lemmas (deep):**

- **`two_finitization_walls`** - Честный аудит границы бариогенезиса: классифицирует величины на element-derived (вычислимы) vs role-limit (предельны) — «две стены финитизации». Та же вена-A логика (разрешимая граница Element/role-limit), применённая к физике, с честной фиксацией пределов. _(baryogenesis, finitization-boundary, element-role-limit, vein-A)_

**Uniqueness - score 2 (new-framing).** Граница бариогенезиса над Q: классификация величин element-derived vs role-limit (две стены финитизации) — честный аудит, что выводимо.
> _Caveat:_ Величины бариогенезиса (Jarlskog/сфалерон) стандартны; вклад — ToS-классификация границы Element/role-limit, не новая физика.

---

## #175 - `src/foundation/BaryogenesisBoundaryConvergence.v` - score 2 (new-framing)

**Baryogenesis boundary convergence over Q: bottoms converge, square criterion**

- **Topic.** A bottom type and convergence relation, bottoms/angle/exp/finite converge, all bottoms converge, a perfect-square criterion, non-termination derived, and bottom-3 is a framework law.
- **Role.** Baryogenesis-boundary leaf (convergence + square criterion, vein-A). Self-contained.
- **Counts.** Qed 1 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ дны (bottoms) бариогенезиса; критерий квадрата. _Roles:_ сходимость дна = роль; квадратный критерий как роль-решатель. _Rules:_ all_bottoms_converge; bottom1_square_criterion; bottom2_nontermination_derived. _P4:_ конечные дны (Element); сходимость + перфект-квадрат критерий (вена A).
- **Classical counterpart.** No direct counterpart — a ToS audit showing baryogenesis 'bottoms' converge, with a perfect-square criterion and non-termination derived (vein-A-flavoured boundary).
- **Tags.** foundation, baryogenesis, square-criterion, vein-A, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `Bottom/ConvergesTo/bottom_converges/angle_converges/exp_converges/finite_converges/all_bottoms_converge` | Definition/Theorem | ★ все дны сходятся |
| `is_square/bottom1_square_criterion/bottom2_nontermination_derived/bottom3_is_framework_law/boundary_convergence` | Definition/Theorem | ★ квадратный критерий, нетерминация выведена |

**Key lemmas (deep):**

- **`bottom1_square_criterion`** - Перфект-квадрат критерий решает сходимость «дна» бариогенезиса (bottom2_nontermination_derived) — та же вена-A механика (is_square решает Element vs role-limit), применённая к границе бариогенезиса. Нетерминация выводится, не постулируется. _(baryogenesis, square-criterion, convergence, vein-A)_

**Uniqueness - score 2 (new-framing).** Сходимость границы бариогенезиса над Q: дны сходятся, перфект-квадрат критерий решает терминацию, нетерминация выведена (вена A).
> _Caveat:_ Внутренний ToS-аудит; вклад — применение перфект-квадрат критерия к границе, не новый физический результат.

---

## #176 - `src/foundation/BaryogenesisTransport.v` - score 2 (methods)

**Baryogenesis transport over Q: eta from CP x B-violation x non-equilibrium**

- **Topic.** CP/B-violation/non-equilibrium factors (all positive), eta transport positive, refining the Jarlskog estimate, eta at 0/1, decreasing, and needing non-equilibrium.
- **Role.** Baryogenesis leaf (transport/Sakharov product). Self-contained (QArith).
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ факторы CP/B-наруш/неравновесия; eta. _Roles:_ перенос = роль-произведение трёх факторов Сахарова. _Rules:_ eta_transport_pos; eta_transport_refines_jarlskog; eta_transport_needs_noneq. _P4:_ конечные факторы над Q (Element); eta как произведение трёх условий Сахарова.
- **Classical counterpart.** Baryogenesis as a product of CP, B-violation and out-of-equilibrium factors (Sakharov), refining the Jarlskog estimate, is standard; here a rational instance.
- **Tags.** foundation, baryogenesis, sakharov, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `cp_factor/bviol_factor/noneq_factor/eta_transport/cp_factor_pos/bviol_factor_pos/noneq_factor_pos/bviol_face_active` | Definition/Theorem | три фактора Сахарова, положительны |
| `eta_transport_pos/_refines_jarlskog/_at_0/_at_1/_decreasing/_needs_noneq/baryogenesis_transport` | Theorem | ★ eta>0, нужно неравновесие |

**Key lemmas (deep):**

- **`eta_transport_needs_noneq`** - eta-перенос = произведение CP × B-нарушения × неравновесия (eta→0 без неравновесия) — формализация трёх условий Сахарова над Q, уточняющая Jarlskog-оценку. Стандартная физика бариогенезиса. _(baryogenesis, sakharov, eta, non-equilibrium)_

**Uniqueness - score 2 (methods).** Перенос бариогенезиса над Q: eta = CP×B-наруш×неравновесие (Сахаров), уточняет Jarlskog, требует неравновесия.
> _Caveat:_ Три условия Сахарова и Jarlskog-оценка стандартны; вклад — Q-инстанс, не новый результат.

---

## #177 - `src/foundation/BaryonFromFoundation.v` - score 2 (methods)

**Baryon asymmetry from foundation over Q: Sakharov chain to positive eta**

- **Topic.** A Jarlskog estimate (3-gen positive, 2-gen vanishing, dilution), a coupling kappa, an eta estimate (positive, small), and a five-step chain: distinction asymmetric -> balance impossible -> CP needs 3 gen -> Jarlskog nonzero -> eta positive (Sakharov from distinction).
- **Role.** Baryogenesis leaf (the foundation->baryon chain). SM-from-distinction OVER-BRANDED. Self-contained (QArith).
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ Jarlskog; eta; шаги цепочки. _Roles:_ цепочка = роль (различение → асимметрия барионов); 3 поколения нужны для CP. _Rules:_ step3_cp_requires_3gen; step4_jarlskog_nonzero; sakharov_from_distinction. _P4:_ конечные оценки над Q (Element); цепочка различение→барион OVER-BRANDED (Jarlskog≠0 для 3 поколений — реальный факт, вывод из онтологии — нет).
- **Classical counterpart.** The Jarlskog invariant, its vanishing for <3 generations, and the Sakharov chain to a baryon asymmetry are standard; NEW only as a rational chain from 'distinction asymmetry' to a positive eta (the 'from distinction' framing is OVER-BRANDED).
- **Tags.** foundation, baryogenesis, jarlskog, over-branded, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `jarlskog_estimate/_3gen/_positive/_2gen/_dilution/kappa_coupling/eta_estimate/_value/_positive/_small` | Definition/Theorem | Jarlskog (3gen>0, 2gen=0), eta |
| `step1_distinction_asymmetric/step2_balance_impossible/step3_cp_requires_3gen/step4_jarlskog_nonzero/step5_eta_positive/sakharov_from_distinction/baryon_asymmetry_summary/baryon_theorem_count` | Theorem | ★ пятишаговая цепочка различение→барион |

**Key lemmas (deep):**

- **`step3_cp_requires_3gen`** - CP-нарушение требует ≥3 поколений (Jarlskog зануляется при 2) — реальный факт физики частиц над Q. Цепочка «различение→асимметрия барионов» (sakharov_from_distinction) OVER-BRANDED: алгебра Jarlskog корректна, но связь с онтологией различения — интерпретация, не вывод. _(baryogenesis, jarlskog, 3-generations, over-branded)_

**Uniqueness - score 2 (methods).** Барионная асимметрия над Q: цепочка различение→3 поколения→Jarlskog≠0→eta>0 (Сахаров).
> _Caveat:_ Jarlskog≠0 для 3 поколений и условия Сахарова стандартны; вклад — Q-цепочка; «из различения» OVER-BRANDED.

---

## #178 - `src/foundation/BianchiFromBoundary.v` - score 2 (methods)

**Bianchi from boundary over Q: dd=0 gives the Bianchi identity**

- **Topic.** Curvature components (can be nonzero), a second boundary, boundary-of-boundary = 0, and the Bianchi identity as a theorem.
- **Role.** Gravity/geometry leaf (Bianchi from dd=0). Self-contained.
- **Counts.** Qed 1 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ компоненты кривизны; граница. _Roles:_ тождество Бианки = роль-следствие ∂∂=0. _Rules:_ boundary_of_boundary=0; bianchi_identity; bianchi_is_a_theorem. _P4:_ конечные компоненты (Element); Бианки как ТЕОРЕМА из ∂∂=0, не постулат.
- **Classical counterpart.** The Bianchi identity as a consequence of 'boundary of a boundary is zero' (dd=0) is standard differential geometry (Misner-Thorne-Wheeler); NEW only as a small Q instance making it a theorem.
- **Tags.** foundation, bianchi, geometry, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `curv_F0/F1/F2/F3/curvature_can_be_nonzero/boundary2/boundary_of_boundary` | Definition/Theorem | кривизна, ∂∂ |
| `bianchi/bianchi_identity/bianchi_is_a_theorem` | Theorem | ★ Бианки как теорема из ∂∂=0 |

**Key lemmas (deep):**

- **`bianchi_is_a_theorem`** - Тождество Бианки выводится из «граница границы = 0» (∂∂=0) над Q — стандартная дифгеометрия (MTW), сделанная теоремой, а не постулатом. Иллюстративно. _(bianchi, boundary, dd-zero)_

**Uniqueness - score 2 (methods).** Тождество Бианки над Q как теорема из ∂∂=0 (граница границы = 0).
> _Caveat:_ Бианки из ∂∂=0 — стандартная дифгеометрия; вклад — малый Q-инстанс-теорема, не новый результат.

---

## #179 - `src/foundation/Binarity.v` - score 2 (new-framing)

**Binarity over Q: each distinction doubles the microstates (2^n)**

- **Topic.** A two-sided distinction (L2 exclusive, L3 exhaustive), exactly two sides, powers of two (monotone, positive, strict), microstates, more distinctions = more states, and a new distinction doubles the count.
- **Role.** Distinction-spine leaf (binarity -> 2^n). Self-contained.
- **Counts.** Qed 1 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ две стороны различения; микросостояния. _Roles:_ бинарность = роль (L2 исключающая, L3 исчерпывающая); удвоение состояний. _Rules:_ exactly_two_sides; new_dist_doubles; microstates=2^n. _P4:_ конечное число различений (Element); каждое новое различение УДВАИВАЕТ микросостояния (2^n).
- **Classical counterpart.** That a binary distinction yields 2^n microstates (information/entropy = bit count) is elementary; NEW only as the ToS statement that each new distinction doubles the state count (L2 exclusive, L3 exhaustive).
- **Tags.** foundation, binarity, distinction, new-framing

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `Side/L2_exclusive/L3_exhaustive/exactly_two_sides` | Definition/Theorem | ★ ровно две стороны (L2/L3) |
| `two_pow/pow_0/_1/_2/_3/_4/_5/_6/_10/pow_monotone/_positive/_double/_strict_monotone` | Definition/Theorem | степени двойки |
| `microstates/more_dist_more_states/new_dist_doubles` | Theorem | ★ новое различение удваивает состояния |

**Key lemmas (deep):**

- **`new_dist_doubles`** - Каждое новое бинарное различение удваивает число микросостояний (2^n) — формальный мост от L2/L3 (исключающее/исчерпывающее) к экспоненциальному росту пространства состояний над Q. Корень энтропии-как-счёта в ToS. _(binarity, doubling, microstates, L2-L3)_

**Uniqueness - score 2 (new-framing).** Бинарность над Q: ровно две стороны (L2 исключающая, L3 исчерпывающая), каждое различение удваивает микросостояния (2^n).
> _Caveat:_ 2^n микросостояний — элементарная комбинаторика/информация; вклад — привязка к L2/L3-онтологии, не новый результат.

---

## #180 - `src/foundation/BinarityRelativitySynthesis.v` - score 1 (exposition)

**Binarity-relativity synthesis over Q: entropy=count, simultaneity relative, interval invariant**

- **Topic.** Powers of two, the binarity-relativity synthesis, exact binarity, each bit doubles, entropy is count, the cone is causal, simultaneity relative, and the interval invariant.
- **Role.** Synthesis leaf joining binarity and causal structure. Self-contained (QArith).
- **Counts.** Qed 1 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ степени двойки; причинный конус; интервал. _Roles:_ узел-синтез: бинарность ↔ относительность. _Rules:_ entropy_is_count; simultaneity_relative; interval_invariant. _P4:_ конечные состояния (Element); связывает бинарность и причинную структуру.
- **Classical counterpart.** Entropy = bit count, relative simultaneity and interval invariance are standard; here a small synthesis tying binarity to a causal/relativistic cone over Q.
- **Tags.** foundation, binarity, synthesis, exposition

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `tpow/binarity_relativity_synthesis/binarity_exact/each_bit_doubles/entropy_is_count` | Definition/Theorem | энтропия=счёт, удвоение |
| `cone_is_causal/simultaneity_relative/interval_invariant/tpow_monotone/_positive` | Theorem | ★ конус причинен, интервал инвариантен |

**Key lemmas (deep):**

- **`interval_invariant`** - Связывает бинарность (энтропия=счёт) с причинной структурой (относительная одновременность, инвариантный интервал) над Q — узел-синтез. Стандартное содержание, объединённое. _(synthesis, binarity, interval-invariant)_

**Uniqueness - score 1 (exposition).** Синтез бинарности и относительности над Q: энтропия=счёт, одновременность относительна, интервал инвариантен.
> _Caveat:_ Узел-синтез стандартных фактов; собственного результата нет.

---

## #181 - `src/foundation/BitString.v` - score 1 (infrastructure)

**Bit string over Q: sides are binary, length by adding bits**

- **Topic.** Side binarity (a side is binary), all sides complete with length, a Bit and BitString type, length, adding a bit increments length, a one-bit string, positive bit count, and nonempty bit-string induction.
- **Role.** Distinction-spine infrastructure (bit strings). Self-contained.
- **Counts.** Qed 2 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ биты; битовые строки; стороны. _Roles:_ сторона = бинарная роль; строка как последовательность различений. _Rules:_ side_is_binary; add_bit_increments_length; nonempty_bitstring_ind. _P4:_ конечные битовые строки (Element); сторона различения бинарна.
- **Classical counterpart.** Bit strings and their lengths are elementary; here only the ToS framing that a side is binary and bit strings build up by adding bits.
- **Tags.** foundation, bit-string, infrastructure

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `side_binarity/side_is_binary/all_sides/_complete/_length` | Definition/Theorem | сторона бинарна |
| `Bit/BitString/bit_length/add_bit/add_bit_increments_length/one_bit/_length/positive_bit_count/nonempty_positive_count/nonempty_bitstring_ind` | Definition/Theorem | битовые строки, индукция |

**Key lemmas (deep):**

- **`add_bit_increments_length`** - Битовые строки строятся добавлением бита (длина растёт) с индукцией по непустым строкам — инфраструктура различения-как-последовательности над Q. Элементарно. _(bit-string, length, infrastructure)_

**Uniqueness - score 1 (infrastructure).** Битовые строки над Q: сторона бинарна, длина растёт добавлением бита, индукция по непустым.
> _Caveat:_ Битовые строки элементарны; чистая инфраструктура различения.

---

## #182 - `src/foundation/BlockCayleyUnistochastic.v` - score 3 (new-framing)

**Block-Cayley unistochastic over Q: antisymmetric block -> unitary -> doubly-stochastic**

- **Topic.** An antisymmetric i-block (squared, determinant), a 2-block M, the Cayley unitary U_block (column norms, orthogonality), the Gamma block (row/col sums, doubly-stochastic), concrete theta-angle instances, a 3-block, and 'connection makes quantum' / real-vs-block Cayley.
- **Role.** Vein-D-flavoured foundation leaf (Cayley -> unistochastic, the L1 doubly-stochastic root). One of the larger foundation files (Q20). Self-contained (QArith).
- **Counts.** Qed 20 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ антисимметричный блок; Cayley-унитарий U; Gamma=\|U\|² (бистохастика). _Roles:_ преобразование Кэли = роль (блок→унитарий); унистохастика как роль-вероятности. _Rules:_ U_block_2_orth; Gamma_block_DS; connection_makes_quantum. _P4:_ конечные блоки над Q (Element); Кэли превращает антисимметричный блок в бистохастическую (квантовую) матрицу — вена D.
- **Classical counterpart.** The Cayley transform from a skew/antisymmetric block to a unitary, and unistochastic (doubly-stochastic from \|U_ij\|^2) matrices, are classical; NEW is the explicit Q-arithmetic block instance tying an antisymmetric block via Cayley to a doubly-stochastic matrix ('connection makes quantum').
- **Tags.** foundation, cayley, unistochastic, vein-D, new-framing

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `i_block/_antisym/_sq/_det/M_block_2/_antisym/U_block_2/sq_nonneg/denom_pos/_neq_0` | Definition/Theorem | антисимметричный блок, Cayley |
| `U_block_2_row0_norm/_orth_01/block_mod_sq/Gamma_block_row_sum/_col_sum/_DS` | Theorem | ★ U унитарен, Gamma бистохастична |
| `U_block_theta2_00/_03/Gamma_block_theta2/_theta2_DS/_theta1/_theta1_DS/M_block_3/_antisym` | Theorem | конкретные theta-инстансы, 3-блок |
| `block_cayley_unistochastic/real_vs_block_cayley/connection_makes_quantum` | Theorem | ★ связь делает квантовым (унистохастика) |

**Key lemmas (deep):**

- **`Gamma_block_DS`** - Преобразование Кэли из антисимметричного блока даёт унитарий U, чей \|U_ij\|² — БИСТОХАСТИЧЕСКАЯ (унистохастическая) матрица, точно над Q. Вена D: рациональная связь между антисимметрией (связностью) и квантовыми вероятностями. Корень L1 doubly-stochastic в физической ветви. _(cayley, unistochastic, doubly-stochastic, vein-D)_
- **`connection_makes_quantum`** - «Связь делает квантовым»: связность (антисимметричный блок) через Кэли порождает квантовые (унистохастические) вероятности — содержательное переобрамление над Q, связывающее геометрию связности с born-правилом. Перекликается с ConnectionClosesGap/UnistochasticFromGraph. _(connection, quantum, unistochastic)_

**Uniqueness - score 3 (new-framing).** Блок-Кэли над Q: антисимметричный блок → унитарий → бистохастическая матрица (унистохастика), «связь делает квантовым» — вена D, рациональный мост связность↔квантовые вероятности.
> _Caveat:_ Преобразование Кэли и унистохастические матрицы классичны; вклад — явный Q-блок-инстанс и переобрамление «связь→квант», не новая теория.

---

## #183 - `src/foundation/BMinusLNeutrino.v` - score 2 (methods)

**B-L neutrino over Q: right-handed neutrino forced by anomaly cancellation**

- **Topic.** The right-neutrino hypercharge (SM-neutral), B-L charges for all fermions, B-L color/weak/grav/cubic anomalies, the grav and cubic deficits, nu_R cancels both, and nu_R forced.
- **Role.** SM-physics leaf (B-L / right neutrino). SM-from-distinction OVER-BRANDED. Self-contained (QArith).
- **Counts.** Qed 2 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ B-L заряды; правый нейтрино nu_R. _Roles:_ сокращение B-L аномалий = роль, требующая nu_R. _Rules:_ bl_grav_deficit; bl_cubic_deficit; nuR_cancels_both; nuR_forced. _P4:_ конечная проверка над Q (Element); nu_R вынужден сокращением grav+cubic дефицитов; SM-framing OVER-BRANDED.
- **Classical counterpart.** That a right-handed neutrino with the right B-L charge cancels the residual gravitational and cubic anomalies (B-L gauge anomaly cancellation) is standard; NEW only as a rational check that nu_R is forced.
- **Tags.** foundation, b-minus-l, anomaly, over-branded, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `YnuR/nuR_sm_neutral/BLq/BLu/BLd/BLl/BLe/BLnu/bl_color/_weak/_grav/_cubic` | Definition/Theorem | B-L заряды, аномалии |
| `bl_grav_deficit/bl_cubic_deficit/nuR_cancels_both/nuR_forced/b_minus_l_forces_neutrino` | Theorem | ★ nu_R вынужден (сокращает grav+cubic) |

**Key lemmas (deep):**

- **`nuR_forced`** - Правый нейтрино nu_R вынужден: без него остаются gravitational+cubic B-L дефициты, nu_R сокращает оба — реальный факт сокращения B-L аномалий над Q. SM-from-distinction OVER-BRANDED, но сама алгебра корректна. _(b-minus-l, right-neutrino, anomaly, over-branded)_

**Uniqueness - score 2 (methods).** B-L нейтрино над Q: правый nu_R вынужден сокращением gravitational+cubic B-L аномалий.
> _Caveat:_ Сокращение B-L аномалий правым нейтрино известно; вклад — Q-проверка; SM-framing OVER-BRANDED.

---

## #184 - `src/foundation/BornRuleDescent.v` - score 2 (methods)

**Born rule descent over Q: only the square is conserved**

- **Topic.** The square preserved on the unit circle, the 1-norm growing/shrinking, only the square conserved, a Born-aspect/grounding split, and the honest split.
- **Role.** Honesty/descent leaf for the Born rule (exponent 2). Self-contained (QArith).
- **Counts.** Qed 1 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ норма (квадрат vs 1-норма); единичная окружность. _Roles:_ правило Борна = роль; обоснованное (квадрат сохраняется) vs постулированное. _Rules:_ only_square_conserved; one_norm_grows/shrinks; the_split. _P4:_ конечные значения над Q (Element); ЧЕСТНО: квадрат — единственная сохраняемая норма (показатель 2 обоснован).
- **Classical counterpart.** That the squared modulus (not \|.\|^1 or \|.\|^4) is the unique norm conserved under unitary evolution (Born exponent 2) is standard; here an internal 'descent' separating the grounded part (square conserved) from the posited part.
- **Tags.** foundation, born-rule, descent, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `square_preserved/on_unit_circle/one_norm_grows/one_norm_shrinks/only_square_conserved` | Theorem | ★ только квадрат сохраняется |
| `BornAspect/Grounding/aspect_grounding/the_split/born_rule_descent` | Definition/Theorem | разделение обоснованного/постулированного |

**Key lemmas (deep):**

- **`only_square_conserved`** - Только квадрат модуля сохраняется на единичной окружности (1-норма растёт/убывает) — обосновывает показатель 2 правила Борна над Q. Descent-файл честно отделяет обоснованное (квадрат) от постулированного. Ср. physics/BornRuleFromUnitarity. _(born-rule, exponent-2, descent, honest)_

**Uniqueness - score 2 (methods).** Спуск правила Борна над Q: только квадрат модуля сохраняется (показатель 2 обоснован), 1-норма не сохраняется.
> _Caveat:_ Единственность показателя 2 (квадрат) стандартна; вклад — честное descent-разделение обоснованного/постулированного, не новый результат.

---

## #185 - `src/foundation/BornRuleFromProcess.v` - score 2 (methods)

**Born rule from process over Q: probabilities sum to one**

- **Topic.** An inner product, squared norm, Born probability at level K, basis states, a superposition, overlaps, Born certain/impossible/half, and that Born probabilities sum to one.
- **Role.** E/R/R leaf (Born rule from a finite process). Self-contained (QArith).
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ скалярное произведение; базисные состояния; суперпозиция. _Roles:_ правило Борна = роль (квадраты перекрытий); вероятности как роли. _Rules:_ born_certain; born_impossible; born_sum_to_one. _P4:_ конечный процесс над Q (Element); вероятности Борна суммируются в 1.
- **Classical counterpart.** The Born rule (probabilities = squared overlaps, summing to one, certain/impossible on basis states) is standard QM; NEW only as a derivation over a finite Q process.
- **Tags.** foundation, born-rule, process, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `inner_K/norm_sq_K/born_prob_K/basis_0/basis_1/superpos/inner_00/_11/_01/_ss/_s0/_s1` | Definition/Theorem | скалярное произведение, базис, перекрытия |
| `born_certain/born_impossible/born_half/born_half_other/born_sum_to_one/born_rule_derived` | Theorem | ★ Борн: уверенно/невозможно/половина, сумма=1 |

**Key lemmas (deep):**

- **`born_sum_to_one`** - Вероятности Борна (квадраты перекрытий) суммируются в 1 на конечном процессе над Q, с уверенностью/невозможностью на базисных состояниях — E/R/R-вывод правила Борна. Стандартная КМ, переписанная процессно. _(born-rule, process, normalization)_

**Uniqueness - score 2 (methods).** Правило Борна из процесса над Q: вероятности=квадраты перекрытий, сумма=1, уверенность/невозможность на базисе.
> _Caveat:_ Правило Борна стандартно; вклад — вывод над конечным Q-процессом (E/R/R), не новый результат.

---

## #186 - `src/foundation/CarbonStructure.v` - score 2 (methods)

**Carbon structure over Q: shells, Hund triplet, Slater screening, tetravalence**

- **Topic.** Carbon Z=6, 1s/2s/2p counts (total 6), subshell capacities, full/partial subshells, p orientations and the 2n^2 capacity formula, Hund's rule (triplet over singlet ground), the 6th ionization (beats Li/He), Slater screening, Z_eff for 2p, valence count, and tetravalence.
- **Role.** E/R/R atomic-structure leaf (carbon). 2n^2 shells OVER-BRANDED. Self-contained (QArith).
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ оболочки 1s/2s/2p; ёмкости; экранирование Слейтера. _Roles:_ правило Хунда = роль (триплет); валентность как роль. _Rules:_ hund_triplet_over_singlet; c_tetravalent; capacity_formula=2n². _P4:_ конечные оценки над Q (Element); углерод в E/R/R-форме; 2n²-ёмкости OVER-BRANDED как «предсказание».
- **Classical counterpart.** Carbon's electron configuration, shell capacities (2n^2), Hund's rule (triplet ground), Slater screening, tetravalence and the steep 6th ionization are textbook chemistry; NEW only as an exact rational instance (2n^2 shells are OVER-BRANDED).
- **Tags.** foundation, carbon, atomic, over-branded, methods

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `Z_C/c_1s_count/c_2s_count/c_2p_count/c_total/c_total_is_6/s_subshell_capacity/p_subshell_capacity/d_subshell_capacity/c_*_within_capacity/c_*_is_full/c_2p_is_partial` | Definition/Theorem | конфигурация, ёмкости |
| `p_m_orientations/p_capacity_formula/c_2p_free/c_has_4_free_p_slots/spin_state/singlet/triplet/hund_prefers/hund_triplet_over_singlet/hund_triplet_at_max/c_ground_spin/c_ground_is_triplet/c_hund_ground` | Definition/Theorem | ★ правило Хунда (триплет) |
| `c_5plus_E/_ground/_n2/_n3/_scales_36x/c_sixth_ionization/_value/_beats_li_third/_beats_he_second` | Theorem | 6-я ионизация (масштаб 36×) |
| `slater_same_shell/c_slater_sigma/_value/c_Z_eff_2p/_value/c_2p_binding_slater/_value/c_first_ionization_slater/_value/slater_overestimates/c_valence_count/c_has_4_valence/c_bond_capacity/c_tetravalent/h_valence/li_valence/c_valence/c_has_most_valence_so_far/carbon_structure_complete` | Theorem | ★ Слейтер, тетравалентность |

**Key lemmas (deep):**

- **`c_tetravalent`** - Углерод тетравалентен (4 валентных слота из правила Хунда + ёмкостей) над Q — корректная E/R/R-формализация структуры углерода. Хунд-триплет основное состояние, Слейтер-экранирование. Учебная химия; 2n²-ёмкости как «предсказание» OVER-BRANDED. _(carbon, hund, tetravalent, over-branded)_

**Uniqueness - score 2 (methods).** Структура углерода над Q: конфигурация 1s²2s²2p², правило Хунда (триплет), Слейтер-экранирование, тетравалентность, 6-я ионизация.
> _Caveat:_ Конфигурация/Хунд/Слейтер/тетравалентность — учебная химия; 2n²-ёмкости OVER-BRANDED; вклад — точный Q-инстанс, не новый результат.

---

## #187 - `src/foundation/CascadeBoundary.v` - score 2 (new-framing)

**Cascade boundary over Q: truncation side vs closure side (finitization boundary)**

- **Topic.** Dyadic/enstrophy nonnegativity, shell and total NS enstrophy, enstrophy monotone (with witness), a cascade-side type, the truncation side vs closure side, disjoint, and a cascade finitization boundary.
- **Role.** NS/cascade leaf with a finitization boundary (vein-A). Links to navier_stokes. Self-contained (QArith).
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ энстрофия оболочек; стороны каскада. _Roles:_ граница финитизации = роль (truncation vs closure). _Rules:_ enstrophy_monotone; h1_cascade_disjoint; cascade_finitization_boundary. _P4:_ конечные оболочки энстрофии над Q (Element); граница каскада разделяет усечение и замыкание (вена A).
- **Classical counterpart.** The turbulent energy cascade and enstrophy monotonicity are standard fluid dynamics; NEW is the ToS framing of a 'finitization boundary' splitting the truncation side from the closure side (vein-A-flavoured).
- **Tags.** foundation, cascade, finitization-boundary, vein-A, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `kdyad_nonneg/wdyad_nonneg/q_sq_nonneg/shell_enstrophy_nonneg/total_ns_enstrophy_nonneg/enstrophy_monotone/_witness` | Lemma/Theorem | энстрофия неотрицательна, монотонна |
| `CascadeSide/truncation_side/closure_side/h1_cascade_disjoint/cascade_finitization_boundary` | Definition/Theorem | ★ граница каскада (усечение vs замыкание) |

**Key lemmas (deep):**

- **`cascade_finitization_boundary`** - Граница финитизации каскада разделяет сторону усечения (truncation) и сторону замыкания (closure), доказуемо непересекающиеся — та же вена-A логика (разрешимая граница), применённая к турбулентному каскаду. Связь с navier_stokes/ оболочечными моделями. _(cascade, finitization-boundary, enstrophy, vein-A)_

**Uniqueness - score 2 (new-framing).** Граница каскада над Q: сторона усечения vs замыкания (граница финитизации, непересекающиеся), энстрофия монотонна.
> _Caveat:_ Энергетический каскад и энстрофия стандартны; вклад — ToS-граница финитизации усечение/замыкание (вена A), не новая гидродинамика.

---

## #188 - `src/foundation/CasimirBernoulli.v` - score 1 (exposition)

**Casimir-Bernoulli over Q: zeta(-1)=-1/12, zeta(-3) via Bernoulli**

- **Topic.** Bernoulli numbers B0/B1/B2/B4 with recursions, zeta(-1) and zeta(-3), and the partial sums diverging.
- **Role.** Numerical leaf (Bernoulli/Casimir, parallels experimental/BernoulliNumbers). Self-contained (QArith).
- **Counts.** Qed 1 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ числа Бернулли; zeta(-1),(-3). _Roles:_ регуляризация = роль; Бернулли как источник конечного значения. _Rules:_ zeta_minus_one=−1/12; zeta_minus_three; partial_sums_diverge. _P4:_ Бернулли — точные Q-числа (Element); наивные суммы расходятся (role-limit).
- **Classical counterpart.** zeta(-1)=-1/12, zeta(-3)=1/120 via Bernoulli numbers and the divergence of the naive sums are classical; here a tiny Q instance.
- **Tags.** foundation, bernoulli, zeta-negative, exposition

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `B0/B1/B2/B4/bernoulli_B2_recursion/_B4_recursion` | Definition/Theorem | числа Бернулли, рекурсии |
| `zeta_m1/zeta_minus_one/zeta_m3/zeta_minus_three/partial_sums_diverge/casimir_bernoulli` | Theorem | ★ zeta(-1)=−1/12, суммы расходятся |

**Key lemmas (deep):**

- **`zeta_minus_one`** - zeta(-1)=-1/12 через B2 над Q, при том что partial_sums_diverge — точное конечное значение vs расходящаяся наивная сумма. Дубликат-в-малом experimental/BernoulliNumbers; питает Casimir-ветвь. _(bernoulli, zeta-negative, -1/12)_

**Uniqueness - score 1 (exposition).** Casimir-Бернулли над Q: zeta(-1)=−1/12, zeta(-3) через Бернулли, наивные суммы расходятся.
> _Caveat:_ zeta(-n) через Бернулли классично; малый Q-инстанс, перекликается с experimental/BernoulliNumbers.

---

## #189 - `src/foundation/CausalCone.v` - score 1 (exposition)

**Causal cone over Q: future cone, transitivity, spacelike separation**

- **Topic.** An event, the future cone (self in cone, nearby future, far not in cone, on boundary), past not future, transitivity, a symmetric site, the cone widening, and spacelike separation.
- **Role.** Causal-structure leaf (the light cone). Self-contained.
- **Counts.** Qed 2 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ события; будущий конус. _Roles:_ причинный конус = роль-структура порядка; пространственноподобность как роль. _Rules:_ self_in_cone; cone_transitive; spacelike_separation. _P4:_ конечные события (Element); причинный конус как порядок, расширяется со стадией.
- **Classical counterpart.** The causal (future/past light) cone, its transitivity and spacelike separation are standard relativity; here a small Q/graph instance.
- **Tags.** foundation, causal-cone, relativity, exposition

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `Event/in_future_cone/self_in_cone/nearby_future/far_not_in_cone/on_boundary/past_not_future` | Definition/Theorem | будущий конус |
| `cone_transitive_ex/symmetric_site/cone_widens/spacelike_separation` | Theorem | ★ транзитивность, пространственноподобность |

**Key lemmas (deep):**

- **`cone_widens`** - Причинный конус расширяется со стадией, транзитивен, даёт пространственноподобную разделённость над Q — дискретная картина светового конуса. Стандартная релятивистская структура. _(causal-cone, lightcone, spacelike)_

**Uniqueness - score 1 (exposition).** Причинный конус над Q: будущий конус, транзитивность, пространственноподобная разделённость.
> _Caveat:_ Световой конус и пространственноподобность — стандартная релятивистика; дискретный Q-инстанс без нового содержания.

---

## #190 - `src/foundation/CausalOrderGeometry.v` - score 2 (new-framing)

**Causal-order geometry over Q: order + number = frame-free geometry**

- **Topic.** A causal-before relation (irreflexive, transitive, antisymmetric), an interval with cardinality, order says connected, number adds scale, relabeling preserves order, translation preserves count, and order+number = frame-free geometry.
- **Role.** Causal-structure leaf (causal-set geometry, vein-C-flavoured). Self-contained.
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ причинный порядок; интервал; кардинальность. _Roles:_ геометрия = роль из порядка+числа; перемаркировка/трансляция как симметрии. _Rules:_ relabel_preserves_order; translate_preserves_count; order_plus_number_is_frame_free_geometry. _P4:_ конечные интервалы (Element); геометрия из порядка+счёта, без фоновых координат (вена-C-смежно).
- **Classical counterpart.** Causal-set theory (geometry from a partial order + counting) and the slogan 'order + number = geometry' are known (Sorkin et al.); NEW only as a small Q instance where relabeling preserves order and translation preserves count (frame-free geometry).
- **Tags.** foundation, causal-set, frame-free, vein-C, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `cprec/causally_before/chain_irrefl/_trans/_antisym/interval/interval_card/_0_4/_0_2` | Definition/Theorem | причинный порядок, интервал |
| `order_says_connected/number_adds_scale/relabel_preserves_order/translate_preserves_count/order_plus_number_is_frame_free_geometry` | Theorem | ★ порядок+число = фон-свободная геометрия |

**Key lemmas (deep):**

- **`order_plus_number_is_frame_free_geometry`** - «Порядок + число = геометрия» (причинный частичный порядок даёт связность, кардинальность даёт масштаб; перемаркировка сохраняет порядок, трансляция — счёт) над Q — формализация causal-set идеи (Sorkin) в ToS-онтологии. Вена-C-смежно: геометрия эмерджентна, не фоновая. _(causal-set, frame-free, order-number, vein-C)_

**Uniqueness - score 2 (new-framing).** Причинно-порядковая геометрия над Q: порядок (связность) + число (масштаб) = фон-свободная геометрия; перемаркировка сохраняет порядок, трансляция — счёт.
> _Caveat:_ «Order + number = geometry» — идея causal-set теории (Sorkin); вклад — малый Q-инстанс в ToS-онтологии, не новый результат.

---

## #191 - `src/foundation/CausalSignature.v` - score 2 (new-framing)

**Causal signature over Q: Lorentzian 3+1 from causal edge signs**

- **Topic.** A causal edge type and sign, a squared interval, space same-stage/reversible/symmetric/positive, time forward/irreversible/negative, the Lorentzian signature in d dimensions, signature 3+1, counting negatives, and one time dimension.
- **Role.** Causal-structure leaf (Lorentzian signature). Self-contained (QArith).
- **Counts.** Qed 4 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ причинные рёбра (знак); интервал. _Roles:_ сигнатура = роль из знаков рёбер; время необратимо, пространство симметрично. _Rules:_ space_positive; time_negative; one_time_dimension; signature_3plus1. _P4:_ конечные рёбра над Q (Element); лоренцева сигнатура 3+1 из знаков (одно время).
- **Classical counterpart.** The Lorentzian (3+1) signature with one time dimension (time irreversible, space reversible) is standard; NEW is deriving the signature from a causal edge-sign (space symmetric/positive, time forward/negative) over Q.
- **Tags.** foundation, lorentzian, signature, causal, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `CEdgeType/cedge_sign/interval_sq/space_same_stage/space_reversible_by_definition/space_symmetric/time_forward/time_irreversible` | Definition/Theorem | знаки рёбер, пространство/время |
| `space_positive/time_negative/space_interval_positive/time_interval_negative/lorentzian_signature_d/signature_3plus1/is_neg/count_negative/one_time_dimension/causal_signature_synthesis` | Theorem | ★ сигнатура 3+1, одно время |

**Key lemmas (deep):**

- **`one_time_dimension`** - Лоренцева сигнатура (3+1, одно время) выводится из знаков причинных рёбер: пространство симметрично/положительно, время направлено/отрицательно над Q. Переобрамление сигнатуры как следствия причинной структуры (одно отрицательное направление = одно время). Содержательно, но физика известна. _(lorentzian, signature, one-time, causal)_

**Uniqueness - score 2 (new-framing).** Причинная сигнатура над Q: лоренцева 3+1 (одно время) из знаков причинных рёбер — пространство симметрично/положительно, время направлено/отрицательно.
> _Caveat:_ Лоренцева сигнатура 3+1 — стандартная физика; вклад — её вывод из знаков причинных рёбер, не новый результат.

---

## #192 - `src/foundation/CausalStructureSynthesis.v` - score 2 (new-framing)

**Causal-structure synthesis over Q: L5 -> causal -> Lorentzian**

- **Topic.** Step 1 L5 to partial order, step 2 not a total order, step 3 causal to signature, step 4 one time dimension / signature 3+1, L5 to causal to Lorentzian, no backward causation, not Euclidean.
- **Role.** Synthesis leaf joining L5 to the Lorentzian signature. Self-contained.
- **Counts.** Qed 4 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ L5-порядок; причинная структура; сигнатура. _Roles:_ узел-синтез: L5 → причинность → лоренцева структура. _Rules:_ L5_to_causal_to_lorentzian; no_backward_causation; not_euclidean. _P4:_ конечная цепочка (Element); L5 → лоренцева 3+1 (не евклидова).
- **Classical counterpart.** The chain from a partial causal order to a Lorentzian (3+1, no backward causation, not Euclidean) structure is standard; here a synthesis tying L5 to the signature.
- **Tags.** foundation, L5, lorentzian, synthesis, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `step1_L5_to_partial_order/step2_not_total_order/step3_causal_to_signature/step4_one_time_dimension/step4_signature_3plus1` | Theorem | шаги L5→сигнатура |
| `L5_to_causal_to_lorentzian/no_backward_causation/not_euclidean` | Theorem | ★ L5 → лоренцева, нет обратной причинности |

**Key lemmas (deep):**

- **`L5_to_causal_to_lorentzian`** - Синтез: L5 (конститутивный порядок) → частичный (не полный) порядок → причинная сигнатура → лоренцева 3+1, без обратной причинности, не евклидова. Связывает ToS-закон L5 с физической сигнатурой. Узел-агрегатор CausalSignature/CausalOrderGeometry. _(synthesis, L5, lorentzian, causal)_

**Uniqueness - score 2 (new-framing).** Синтез причинной структуры над Q: L5 → частичный порядок → причинная сигнатура → лоренцева 3+1 (нет обратной причинности, не евклидова).
> _Caveat:_ Цепочка частичный-порядок→лоренцева структура стандартна; вклад — привязка к закону L5, не новый результат.

---

## #193 - `src/foundation/ChargeLatticeTheory.v` - score 2 (methods)

**Charge lattice theory over Q: charges grounded on two honest posits**

- **Topic.** Color/weak/grav/cubic anomalies, Y_L/ud-sum/Y_e forced, family anomalies, a ud-discriminant-square condition, family ud sum/product, unique ud roots, the SM anomaly-free, a framework posit and a normalization posit, charges just/grounded on two posits.
- **Role.** SM-physics leaf (charge lattice) with explicit honest posits. SM-from-distinction OVER-BRANDED. Self-contained (QArith).
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ гиперзаряды; аномалии; дискриминант ud. _Roles:_ сокращение аномалий = роль-фиксатор; ДВА явных постулата (framework+normalization). _Rules:_ ud_discriminant_square; sm_anomaly_free; charges_two_posits. _P4:_ конечная решётка зарядов над Q (Element); ЧЕСТНО: заряды опираются на 2 постулата, не чистый вывод; перфект-квадрат дискриминант (вена A).
- **Classical counterpart.** The hypercharge lattice fixed by anomaly cancellation (with a discriminant-square condition for rational roots) is standard; NEW is the HONEST framing that the charges rest on two explicit posits (framework + normalization), not a pure derivation.
- **Tags.** foundation, charge-lattice, anomaly, honest-posits, vein-A, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `anom_su3/_su2/_grav/_cubic/yl_forced/ud_sum_forced/ye_forced/family_anom_su3/_su2/_grav/_cubic` | Definition/Theorem | аномалии, вынужденные заряды |
| `ud_discriminant_square/family_ud_sum/_product/ud_unique_roots/sm_anomaly_free` | Theorem | ★ дискриминант-квадрат → рациональные корни ud |
| `framework_posit/normalization_posit/charges_just/charges_grounded/charges_two_posits/charge_lattice` | Theorem | ★ ЧЕСТНО: заряды на 2 постулатах |

**Key lemmas (deep):**

- **`charges_two_posits`** - ЧЕСТНО: решётка зарядов СМ опирается на ДВА явных постулата (framework_posit + normalization_posit), а не выводится с нуля. ud_discriminant_square (перфект-квадрат → рациональные корни) = вена A. Образец калибровки: что постулировано, что выведено. _(charge-lattice, honest-posits, discriminant, vein-A)_

**Uniqueness - score 2 (methods).** Решётка зарядов над Q: аномалии фиксируют заряды (ud-дискриминант-квадрат → рациональные корни), но ЧЕСТНО опираются на 2 явных постулата (framework+normalization).
> _Caveat:_ Анти-аномальная решётка гиперзарядов известна; вклад — честная фиксация двух постулатов + перфект-квадрат (вена A); SM-framing OVER-BRANDED.

---

## #194 - `src/foundation/CharPolyEigenvalue3.v` - score 2 (methods)

**Characteristic-polynomial eigenvalue 3x3 over Q: rational eigenvalue is integer**

- **Topic.** Trace, second invariant, determinant, characteristic coefficients, the characteristic homogeneous form equals the matrix's, a rational 3x3 eigenvalue is an integer, and a diag(2,3,5) example with integer eigenvalue 2.
- **Role.** Vein-A-flavoured leaf (rational-root theorem for 3x3). Self-contained (QArith/ZArith).
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith ZArith
- **E/R/R.** _Elements:_ характеристический многочлен 3x3; собственные значения. _Roles:_ рациональный корень монического целого многочлена = роль (обязан быть целым). _Rules:_ rational_eigenvalue_3x3_is_integer; charhom_eq_mhom. _P4:_ конечные 3x3 над Z/Q (Element); рациональное собственное значение целочисленно (рациональный корень = вена A).
- **Classical counterpart.** That a rational eigenvalue of a 3x3 integer matrix (monic integer characteristic polynomial) must be an integer is the rational-root theorem; NEW only as an explicit Q/Z 3x3 instance (vein-A-flavoured).
- **Tags.** foundation, rational-root, eigenvalue, vein-A, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `tr3/m2_3/det3A/charcoeffs/charhom/charhom_eq_mhom` | Definition/Theorem | характеристические коэффициенты |
| `rational_eigenvalue_3x3_is_integer/diag235_eig2/diag235_rational_eig_integer/determinant/charpoly_eigenvalue_3x3` | Theorem | ★ рациональное с.з. = целое |

**Key lemmas (deep):**

- **`rational_eigenvalue_3x3_is_integer`** - Рациональное собственное значение целочисленной 3x3-матрицы обязано быть целым (теорема о рациональном корне для монического характеристического многочлена) над Z/Q — та же вена-A механика (рациональный-корень/перфект-квадрат), что решает Element vs role-limit в физической ветви. _(rational-root, eigenvalue, integer, vein-A)_

**Uniqueness - score 2 (methods).** Собственные значения 3x3 над Q: рациональное собственное значение целочисленной матрицы обязано быть целым (рациональный корень монического char-многочлена).
> _Caveat:_ Теорема о рациональном корне классична; вклад — явный 3x3 Q/Z-инстанс (вена A), не новый результат.

---

## #195 - `src/foundation/ChiralAnomalyUniqueness.v` - score 2 (methods)

**Chiral anomaly uniqueness over Q: SM is the unique chiral 321 solution**

- **Topic.** General 321 content, linear/cubic conditions, the SM satisfies both and is a general 321, charge quantization gives/has the SM, the trivial vectorlike solution, scaling preserves anomaly-freedom, SM unique chiral, charge quantization determines SM, SM cubic nontrivial.
- **Role.** SM-physics leaf (chiral anomaly uniqueness). SM-from-distinction OVER-BRANDED. Self-contained (QArith).
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ 321-содержание; линейное/кубическое условия; вектороподобные решения. _Roles:_ хиральность = роль (нетривиальное анти-аномальное решение); квантование зарядов фиксирует СМ. _Rules:_ sm_unique_chiral; charge_quantization_determines_sm; scaled_sm_anomaly_free. _P4:_ конечная проверка над Q (Element); СМ-уникальность хирального решения; SM-framing OVER-BRANDED.
- **Classical counterpart.** That the SM hypercharge content is essentially the unique chiral anomaly-free 321 solution (up to scaling), with charge quantization determining it, is known; NEW only as a rational Coq check (the 'from distinction' framing is OVER-BRANDED).
- **Tags.** foundation, chiral, anomaly, uniqueness, over-branded, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `general_321_content/linear_condition/cubic_condition/sm_satisfies_linear/_cubic/sm_is_general_321/charge_quantization/cq_gives_sm/sm_has_cq` | Definition/Theorem | 321-содержание, квантование→СМ |
| `trivial_satisfies_linear/_cubic/trivial_solution_anomaly_free/trivial_is_vectorlike/scaling_preserves_linear/_cubic/scaled_sm_anomaly_free` | Theorem | тривиальное вектороподобное, масштаб |
| `sm_unique_chiral/charge_quantization_determines_sm/sm_cubic_nontrivial/chiral_anomaly_summary/_theorem_count` | Theorem | ★ СМ — уникальное хиральное решение |

**Key lemmas (deep):**

- **`sm_unique_chiral`** - СМ — уникальное НЕТРИВИАЛЬНОЕ (хиральное, не вектороподобное) анти-аномальное 321-решение, квантование зарядов его определяет — реальный факт физики частиц над Q (с точностью до масштаба). SM-from-distinction OVER-BRANDED, но алгебра единственности корректна. _(chiral, anomaly, uniqueness, over-branded)_

**Uniqueness - score 2 (methods).** Хиральная единственность над Q: СМ — уникальное нетривиальное анти-аномальное 321-решение, квантование зарядов его определяет.
> _Caveat:_ Анти-аномальная единственность СМ известна; вклад — Q-проверка; SM-from-distinction OVER-BRANDED.

---

## #196 - `src/foundation/ChiralityFromL2.v` - score 2 (new-framing)

**Chirality from L2 over Q: chirality is the L2 (unpaired-charge) property**

- **Topic.** Having an unpaired charge, the SM is strongly chiral, vectorlike is not chiral, L2 implies chirality, chirality is L2 and respects L2, vectorlike rejected, SM passes chirality, and several unpaired/paired charge checks.
- **Role.** Distinction->SM bridge leaf (chirality as L2). SM-from-distinction OVER-BRANDED. Self-contained (QArith).
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ непарные/парные заряды; вектороподобное содержание. _Roles:_ хиральность = L2-роль (непарный заряд); вектороподобное отвергается. _Rules:_ chirality_is_L2; vectorlike_rejected; sm_passes_chirality. _P4:_ конечная проверка зарядов над Q (Element); хиральность = L2-свойство; SM-framing OVER-BRANDED.
- **Classical counterpart.** That the SM is chiral (fermions have unpaired gauge charges; vectorlike content is non-chiral) is standard; NEW is the ToS framing that chirality IS the L2 (exclusive-distinction) property — vectorlike content is rejected.
- **Tags.** foundation, chirality, L2, over-branded, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `has_unpaired_charge/sm_is_chiral_strong/vectorlike_not_chiral/L2_implies_chirality/chirality_is_L2/chirality_respects_L2/vectorlike_rejected/sm_passes_chirality` | Theorem | ★ хиральность = L2, вектороподобное отвергнуто |
| `empty_not_chiral/nonzero_single_chiral/different_mult_chiral/charge_1_6_unpaired/charge_1_unpaired/charge_neg23_unpaired/sm_all_unpaired/vectorlike_1_3_not_chiral/_1_not_chiral/_0_not_chiral/chirality_summary/_theorem_count` | Theorem | проверки непарности зарядов |

**Key lemmas (deep):**

- **`chirality_is_L2`** - Хиральность отождествлена с L2-свойством (наличие непарного заряда = исключающее различение): вектороподобное (парное) содержание отвергается, СМ-фермионы все непарны над Q. Мост различение→хиральность. SM-from-distinction OVER-BRANDED, но привязка хиральности к L2 — содержательное наблюдение. _(chirality, L2, unpaired, over-branded)_

**Uniqueness - score 2 (new-framing).** Хиральность из L2 над Q: хиральность = L2-свойство (непарный заряд), вектороподобное отвергается, СМ полностью непарна.
> _Caveat:_ Хиральность СМ vs вектороподобность известна; вклад — привязка к L2-онтологии; SM-from-distinction OVER-BRANDED.

---

## #197 - `src/foundation/CombinatorialGrowth.v` - score 1 (exposition)

**Combinatorial growth over Q: super-linear gap, inexhaustible**

- **Topic.** An attention width, a potential, a gap (at 3/5/10/20, growing), ratios growing, and inexhaustibility at 6/10/20.
- **Role.** Foundational leaf (combinatorial growth / inexhaustibility). Self-contained (QArith).
- **Counts.** Qed 0 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ ширина внимания; потенциал; зазор. _Roles:_ комбинаторный рост = роль (зазор растёт сверхлинейно). _Rules:_ gap_grows; ratio_grows; inexhaustible. _P4:_ конечные значения над Q (Element); потенциал растёт сверхлинейно (неисчерпаем).
- **Classical counterpart.** That a combinatorial potential grows super-linearly (the gap widens, ratio grows, 'inexhaustible') is elementary; here a small Q instance about attention width.
- **Tags.** foundation, combinatorial-growth, exposition

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `attention_width/pot/gap/gap_3/_5/_10/_20/gap_grows_3_5/_5_10/_10_20` | Definition/Theorem | зазор растёт |
| `ratio_5/_10/ratio_grows/inexhaustible_6/_10/_20` | Theorem | ★ отношение растёт, неисчерпаемость |

**Key lemmas (deep):**

- **`inexhaustible_20`** - Комбинаторный потенциал растёт сверхлинейно (зазор и отношение растут) → «неисчерпаем» над Q. Элементарная иллюстрация роста, 0 Qed (всё через определения/примеры). Уникальности нет. _(combinatorial-growth, inexhaustible)_

**Uniqueness - score 1 (exposition).** Комбинаторный рост над Q: зазор/отношение растут сверхлинейно, потенциал неисчерпаем.
> _Caveat:_ Сверхлинейный рост элементарен; иллюстративный файл (0 Qed).

---

## #198 - `src/foundation/ConnectionClosesGap.v` - score 2 (new-framing)

**Connection closes gap over Q: doubly-stochastic chains from a connection**

- **Topic.** A doubly-stochastic 2x2/3x3 test, uniform DS matrices, U2/U3 column norms and orthogonality, Gamma2/Gamma3 rows/cols doubly-stochastic, a history with different/intermediate paths, indivisibility, complete N=2/N=3 chains, and a grand synthesis.
- **Role.** Vein-D-flavoured leaf (DS from connection, with BlockCayleyUnistochastic). Self-contained (QArith).
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ бистохастические матрицы; история путей. _Roles:_ связь = роль, замыкающая бистохастическую цепь; неделимость как роль. _Rules:_ Gamma2_is_DS; Gamma3_is_DS; paths_indivisible. _P4:_ конечные DS-матрицы над Q (Element); связь замыкает полную цепь (вена D).
- **Classical counterpart.** Doubly-stochastic matrices from a unitary (\|U_ij\|^2) and indivisibility of a chain are standard; NEW is the Q instance tying a 'connection' to a complete DS chain ('grand synthesis') with intermediate-via paths.
- **Tags.** foundation, doubly-stochastic, connection, vein-D, new-framing

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `is_DS_2x2/uniform_2_sum/DS_uniform_2x2/U2_col0_norm/_col1_norm/U2_orthogonality/Gamma2_row0/_row1/_col0/_col1/Gamma2_is_DS` | Definition/Theorem | ★ Gamma2 бистохастична |
| `U3_col0_norm/_col1_norm/_col2_norm/U3_ortho_01/Gamma3_row0/_row1/_row2/_col0/_col1/_col2/Gamma3_is_DS` | Theorem | ★ Gamma3 бистохастична |
| `History/diff_histories/has_intermediate/indivisible/history_12/intermediate_via_2/_via_4/paths_indivisible/complete_chain_N2/_N3/grand_synthesis` | Definition/Theorem | неделимые пути, полная цепь |

**Key lemmas (deep):**

- **`Gamma3_is_DS`** - «Связь» (унитарий через Кэли) порождает БИСТОХАСТИЧЕСКИЕ Gamma2/Gamma3 (строки и столбцы суммируются в 1), замыкая полную N=2/N=3 цепь над Q — вена D, продолжение BlockCayleyUnistochastic. Неделимость путей связывает с indivisible-distinction. _(doubly-stochastic, connection, vein-D)_

**Uniqueness - score 2 (new-framing).** Связь замыкает бистохастическую цепь над Q: Gamma2/Gamma3 бистохастичны, полная N=2/N=3 цепь, неделимые пути — вена D.
> _Caveat:_ Бистохастика из унитария классична; вклад — Q-инстанс полной цепи (вена D), не новая теория.

---

## #199 - `src/foundation/ContinuumLimitIsReal.v` - score 2 (new-framing)

**Continuum limit is real over Q: bracketing a root (vein C)**

- **Topic.** A Pell determinant equality and sign, sign from product, a consecutive gap, r above/below, brackets root, and a gap example; the continuum limit is real.
- **Role.** Vein-C leaf (continuum as bracketing process). Self-contained (QArith).
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ Pell-детерминант; рациональные приближения; скобка корня. _Roles:_ континуум-предел = role-limit процесса скобок. _Rules:_ brackets_root; sign_from_product; continuum_limit_is_real. _P4:_ рациональные приближения конечны (Element); континуум-предел РЕАЛЕН как процесс скобок (role-limit, вена C).
- **Classical counterpart.** Bracketing an irrational (Pell/sqrt) root by rational approximants with a sign-change criterion is classical; NEW is the vein-C framing that the continuum limit is REAL as a bracketing process.
- **Tags.** foundation, continuum, bracket, vein-C, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `pell_det_eq/pell_det_pm/sign_from_product/consecutive_gap/r_above/r_below` | Definition/Theorem | Pell-детерминант, скобки |
| `brackets_root/ex_gap/continuum_limit_is_real` | Theorem | ★ скобки зажимают корень; континуум реален |

**Key lemmas (deep):**

- **`brackets_root`** - Рациональные приближения (Pell) зажимают иррациональный корень в скобку со сменой знака над Q — континуум-предел РЕАЛЕН как процесс скобок (вена C), а не завершённый объект. Перекликается с ContinuumLimitRoleLimit/ContinuumLimitProcess. _(continuum, bracket, pell, vein-C)_

**Uniqueness - score 2 (new-framing).** Континуум-предел реален над Q как процесс скобок: Pell-приближения зажимают корень сменой знака (вена C).
> _Caveat:_ Скобки иррационального корня рациональными приближениями классичны; вклад — вена-C переобрамление «предел=процесс», не новый результат.

---

## #200 - `src/foundation/ContinuumLimitProcess.v` - score 2 (new-framing)

**Continuum limit process over Q: constructive volume with error bound**

- **Topic.** An unbounded positive kq, a volume estimate (upper/lower), a continuum-limit error, an example (low/exact/error), and the continuum limit constructive.
- **Role.** Vein-C leaf (continuum as constructive process). Self-contained (QArith).
- **Counts.** Qed 5 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ оценка объёма; граница ошибки. _Roles:_ континуум-предел = role-limit конструктивного процесса. _Rules:_ vol_estimate_upper/lower; continuum_limit_error; continuum_limit_constructive. _P4:_ конечные оценки над Q (Element); континуум-предел конструктивен с явной границей ошибки (вена C).
- **Classical counterpart.** Constructive approximation of a continuum quantity (a volume) with an explicit error bound is classical; NEW is the vein-C framing of the continuum limit as a constructive process.
- **Tags.** foundation, continuum, constructive, vein-C, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `kq/kq_pos/kq_unbounded/vol_estimate/_upper/_lower/continuum_limit_error` | Definition/Theorem | оценка объёма, ошибка |
| `ex_low/ex_exact/ex_error/continuum_limit_constructive` | Theorem | ★ континуум-предел конструктивен |

**Key lemmas (deep):**

- **`continuum_limit_constructive`** - Континуум-предел (объём) конструктивен с явной границей ошибки над Q — вена C: предел как процесс приближения, не завершённый объект. Пара к ContinuumLimitIsReal/RoleLimit. _(continuum, constructive, error-bound, vein-C)_

**Uniqueness - score 2 (new-framing).** Континуум-предел над Q конструктивен: оценка объёма с явной границей ошибки (вена C).
> _Caveat:_ Конструктивная аппроксимация с границей ошибки классична; вклад — вена-C переобрамление, не новый результат.

---

## #201 - `src/foundation/ContinuumLimitRoleLimit.v` - score 3 (new-framing)

**Continuum limit as role-limit over Q: sqrt(2) is never reached (vein C)**

- **Topic.** Pell sequences (px, py with successors), Pell values, sqrt2 never reached, a positivity, an injectivity, r^2 close to but not equal to 2, and the continuum limit as a role-limit.
- **Role.** Vein-C flagship leaf (sqrt2 as role-limit, the sharp 'never reached'). Self-contained (QArith).
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ последовательности Пелля (px,py); приближения r к √2. _Roles:_ √2 = role-limit (приближается, никогда не достигается). _Rules:_ sqrt2_never_reached; r_sq_close; r_sq_ne_2. _P4:_ каждое приближение r рационально и конечно (Element); √2 — role-limit (r²≠2 всегда, sqrt2_never_reached) — РЕЗКАЯ вена C.
- **Classical counterpart.** That sqrt(2) is irrational and is only approached (never equalled) by rational Pell convergents is classical; NEW is the SHARP vein-C statement 'sqrt2_never_reached' — the continuum value is a role-limit, never an actual rational element.
- **Tags.** foundation, sqrt2, role-limit, vein-C, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `pell/px/py/pell_S/px_succ/py_succ/pell_1/_3/pell_val/_0/_neg/_pm/_nonzero/_sq` | Definition/Theorem | последовательности Пелля, значения |
| `sqrt2_never_reached/pxy_pos/py_ge/r/py_inject_ne/r_sq_close/r_sq_ne_2/continuum_limit_role_limit` | Theorem | ★ √2 НИКОГДА не достигается (r²≠2) |

**Key lemmas (deep):**

- **`sqrt2_never_reached`** - РЕЗКАЯ формулировка вены C: рациональные приближения Пелля r подходят к √2 сколь угодно близко (r_sq_close), но r²≠2 ВСЕГДА (sqrt2_never_reached) — континуум-значение есть role-limit, никогда не актуальный рациональный Element. Тот же механизм, что 0.999…→1 не равенством, и ShrinkingIntervals/IVT над Q. _(sqrt2, role-limit, never-reached, vein-C)_
- **`r_sq_ne_2`** - r²≠2 для каждого рационального приближения — точное свидетельство, что √2 вне Q (приближается процессом, не достигается). Делает «role-limit» строгим, а не риторическим. _(irrational, exact, role-limit)_

**Uniqueness - score 3 (new-framing).** Континуум как role-limit над Q: √2 приближается приближениями Пелля сколь угодно близко, но r²≠2 ВСЕГДА (sqrt2_never_reached) — резкая вена C, континуум-значение никогда не актуальный Element.
> _Caveat:_ Иррациональность √2 и приближения Пелля классичны; уникальность — в резкой P4-формулировке role-limit (никогда не достигается), не в новом результате о √2.

---

## #202 - `src/foundation/CountingSideSynthesis.v` - score 1 (exposition)

**Counting-side synthesis over Q: exact derivation mechanisms vs H1 wall**

- **Topic.** A count-kind and derivation type, mechanisms cover, distinct count mechanisms, all derivations exact, charge derivations, an H1-side wall type, and the counting side disjoint from the H1 side.
- **Role.** Synthesis/meta leaf (counting-side vs H1-wall classification). Self-contained.
- **Counts.** Qed 1 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ механизмы счёта; стороны (counting vs H1-wall). _Roles:_ узел-синтез: счётная сторона (точная) vs H1-стена. _Rules:_ all_derivations_exact; h1_disjoint; counting_side_synthesis. _P4:_ конечная классификация (Element); счётная сторона точна, дизъюнктна со стеной H1.
- **Classical counterpart.** No direct counterpart — an internal synthesis classifying the 'counting side' derivation mechanisms (all exact) vs the H1 wall side (disjoint).
- **Tags.** foundation, counting-side, synthesis, exposition

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `CountKind/Derivation/mechanism/mechanisms_cover/count_mechanisms_distinct/is_exact/all_derivations_exact/all_derivations/is_charge/two_charge_derivations` | Definition/Theorem | ★ механизмы счёта точны |
| `H1Side/count_side/WallType/wall_side/h1_disjoint/counting_side_synthesis` | Definition/Theorem | ★ счётная сторона дизъюнктна H1 |

**Key lemmas (deep):**

- **`h1_disjoint`** - Счётная сторона (точные механизмы вывода) дизъюнктна со стороной H1-стены над Q — узел-синтез, разделяющий, что выводится точно vs упирается в стену. Меньший отголосок вены A (граница). _(counting-side, h1-wall, disjoint, synthesis)_

**Uniqueness - score 1 (exposition).** Синтез счётной стороны над Q: механизмы вывода точны, дизъюнктны со стороной H1-стены.
> _Caveat:_ Внутренний классифицирующий узел; собственного результата нет.

---

## #203 - `src/foundation/CouplingElementForcing.v` - score 2 (new-framing)

**Coupling element forcing over Q: equal-diagonal forces an element (vein A)**

- **Topic.** An equal-diagonal discriminant, a symmetric-equal-diagonal square/element, Yang-Mills is symmetric-equal-diagonal, the discriminant excess is a gap square, a lever equal-diagonal element, and a broken-diagonal role-limit.
- **Role.** Vein-A leaf (discriminant forces element). Self-contained (QArith).
- **Counts.** Qed 2 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ симметричная матрица с равной диагональю; дискриминант. _Roles:_ равная диагональ = роль, форсирующая Element (перфект-квадрат); сломанная диагональ = role-limit. _Rules:_ symmetric_equal_diag_square; disc_excess_is_gap_square; lever_broken_diag_role_limit. _P4:_ конечные матрицы над Q (Element); равная диагональ → перфект-квадрат дискриминант → Element; сломанная → role-limit (вена A).
- **Classical counterpart.** That a symmetric matrix with equal diagonal has a perfect-square discriminant (a real/rational element) is elementary; NEW is the vein-A framing that 'equal-diagonal forces an element' while a broken diagonal is a role-limit.
- **Tags.** foundation, discriminant, element-role-limit, vein-A, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `equal_diag_disc/symmetric_equal_diag_square/symmetric_equal_diag_element/ym_is_symmetric_equal_diag/disc_excess_is_gap_square` | Theorem | ★ равная диагональ → квадрат-дискриминант → Element |
| `lever_equal_diag_element/lever_broken_diag_role_limit/coupling_element_forcing` | Theorem | ★ сломанная диагональ → role-limit |

**Key lemmas (deep):**

- **`lever_broken_diag_role_limit`** - Симметричная матрица с РАВНОЙ диагональю имеет перфект-квадрат дискриминант → собственные значения суть Element; СЛОМАННАЯ диагональ → role-limit над Q. Та же вена-A механика (перфект-квадрат решает Element/role-limit), привязанная к Янг-Миллсу (ym_is_symmetric_equal_diag). _(discriminant, equal-diagonal, element-role-limit, vein-A)_

**Uniqueness - score 2 (new-framing).** Форсирование элемента связью над Q: равная диагональ → перфект-квадрат дискриминант → Element; сломанная диагональ → role-limit (вена A, привязка к YM).
> _Caveat:_ Перфект-квадрат дискриминант симметричной матрицы элементарен; вклад — вена-A переобрамление Element/role-limit, не новый результат.

---

## #204 - `src/foundation/CouplingFromERR.v` - score 2 (methods)

**Coupling from E/R/R over Q: sin^2(theta_W) as a DOF ratio (over-branded)**

- **Topic.** Squared couplings, sin^2 from couplings, a cancellation constant C, sin^2 is a DOF ratio, wrong-if-g-not-g2 / wrong-if-g4 checks, alpha_EM tree, alpha_inv tree, and a general C cancellation.
- **Role.** SM-physics leaf (Weinberg angle as DOF ratio). sin^2(theta_W)=3/13 OVER-BRANDED. Self-contained (QArith).
- **Counts.** Qed 5 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ константы связи (квадраты); sin²θ_W. _Roles:_ угол Вайнберга = роль (отношение степеней свободы). _Rules:_ sin2_is_DOF_ratio; C_cancels; alpha_inv_tree. _P4:_ конечные константы над Q (Element); sin²θ_W как DOF-отношение; sin²θ_W=3/13 OVER-BRANDED.
- **Classical counterpart.** That the Weinberg angle sin^2(theta_W) can be written as a degree-of-freedom ratio (and the tree-level value) is a known relation; NEW only as a rational E/R/R instance — and sin^2(theta_W)=3/13 is OVER-BRANDED.
- **Tags.** foundation, weinberg-angle, dof-ratio, over-branded, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `coupling_sq/sin2_from_couplings/C_cancels/sin2_is_DOF_ratio/wrong_if_g_not_g2/wrong_if_g4` | Definition/Theorem | ★ sin² = DOF-отношение |
| `alpha_EM_tree/alpha_inv_tree/inject_Z_nat_pos/C_cancels_general/coupling_from_ERR_synthesis` | Theorem | alpha tree, общее сокращение C |

**Key lemmas (deep):**

- **`sin2_is_DOF_ratio`** - sin²θ_W записан как отношение степеней свободы (константа C сокращается) над Q в E/R/R-форме. Связь корректна как алгебраическое тождество, но значение sin²θ_W=3/13 (фигурирующее в проекте) OVER-BRANDED — это древесная оценка, не подтверждённое предсказание; caveat честно это фиксирует. _(weinberg-angle, dof-ratio, over-branded)_

**Uniqueness - score 2 (methods).** Связь из E/R/R над Q: sin²θ_W как отношение степеней свободы (C сокращается), alpha tree.
> _Caveat:_ Запись sin²θ_W через DOF — известное соотношение; sin²θ_W=3/13 OVER-BRANDED (древесная оценка, не предсказание).

---

## #205 - `src/foundation/CPMagnitudeDescent.v` - score 1 (exposition)

**CP magnitude descent over Q: concrete Jarlskog values**

- **Topic.** An n-mixing, three-generation mixing and CP, a Jarlskog product, concrete Jarlskog values (3-4-5 and 5-12-13, rational and positive), and a J-value descent.
- **Role.** Baryogenesis/CP leaf (Jarlskog magnitudes). Self-contained (QArith).
- **Counts.** Qed 1 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ смешивание (n-gen); Jarlskog-произведение. _Roles:_ CP-магнитуда = роль (Jarlskog для 3 поколений). _Rules:_ three_gen_cp; jarlskog_345_positive; jvalue_descent. _P4:_ конечные Jarlskog-значения над Q (Element); CP-магнитуда из 3 поколений (Пифагоровы тройки).
- **Classical counterpart.** The Jarlskog invariant as a product of mixing factors (nonzero for 3 generations) is standard; here a small rational 'descent' computing concrete Jarlskog values.
- **Tags.** foundation, jarlskog, cp, exposition

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `n_mixing/three_gen_mixing/three_gen_cp/jarlskog_prod/jarlskog_345/_345_rational/_345_positive` | Definition/Theorem | Jarlskog для 3-4-5 |
| `jarlskog_5_12_13/_5_12_13_rational/jvalue_descent` | Theorem | ★ Jarlskog 5-12-13, descent |

**Key lemmas (deep):**

- **`jarlskog_345_positive`** - Конкретные Jarlskog-значения для троек 3-4-5 и 5-12-13 (рациональны, положительны) над Q — CP-магнитуда из 3 поколений, на пифагоровых тройках. Стандартная физика, конкретно вычисленная. _(jarlskog, cp, pythagorean)_

**Uniqueness - score 1 (exposition).** CP-магнитуда над Q: конкретные Jarlskog-значения (3-4-5, 5-12-13), положительные для 3 поколений.
> _Caveat:_ Jarlskog для 3 поколений стандартен; конкретные Q-значения без нового содержания.

---

## #206 - `src/foundation/CreationSynthesis.v` - score 1 (exposition)

**Creation synthesis over Q: two mechanisms, void constructive**

- **Topic.** A creation synthesis, two distinct mechanisms, a super-linear potential, surplus at steps 5-6/9-10/19-20, step grows, matter exceeds consciousness, and void constructive.
- **Role.** Synthesis/meta leaf (creation mechanisms). Self-contained (QArith).
- **Counts.** Qed 1 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ механизмы творения; излишек. _Roles:_ узел-синтез: два механизма творения; пустота конструктивна. _Rules:_ two_mechanisms_distinct; potential_superlinear; void_constructive. _P4:_ конечные шаги над Q (Element); пустота конструктивна (рождает излишек).
- **Classical counterpart.** No direct counterpart — an internal synthesis on two creation mechanisms (super-linear potential, surplus growth) and 'void constructive'.
- **Tags.** foundation, creation, synthesis, exposition

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `creation_synthesis/two_mechanisms_distinct/potential_superlinear/surplus_step_5_6/_9_10/_19_20/step_grows` | Theorem | ★ два механизма, сверхлинейный излишек |
| `matter_exceeds_consciousness/void_constructive` | Theorem | пустота конструктивна |

**Key lemmas (deep):**

- **`void_constructive`** - «Пустота конструктивна»: два механизма творения дают сверхлинейный излишек над Q. Философско-метафизический узел-синтез, иллюстративный. Уникальности нет. _(creation, void, synthesis)_

**Uniqueness - score 1 (exposition).** Синтез творения над Q: два механизма, сверхлинейный излишек, пустота конструктивна.
> _Caveat:_ Метафизический узел-синтез; собственного формального результата нет.

---

## #207 - `src/foundation/CubicCouplingSpectrum.v` - score 3 (new-framing)

**Cubic coupling spectrum over Q: degree-stratified spectral boundary (vein A)**

- **Topic.** Being mode-3, elements at modes 1/2/3, a cube gives a rational mode, cubic-two reduces, a square gives element-2, a degree-2 golden role-limit, a boundary-degree type, degree stratified, and a cubic spectral boundary.
- **Role.** Vein-A leaf (degree-stratified element/role-limit boundary). Self-contained (QArith).
- **Counts.** Qed 2 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ моды (кубические/квадратичные); степень. _Roles:_ степень = роль-стратификатор границы (куб → Element, deg-2 золотое → role-limit). _Rules:_ cube_gives_rational_mode; deg2_role_limit_golden; cubic_spectral_boundary. _P4:_ конечные моды над Q (Element); куб даёт рациональную моду (Element), deg-2 золотое сечение — role-limit (вена A по степени).
- **Classical counterpart.** That a cubic gives a rational mode while degree-2 (golden-ratio) is irrational is elementary algebra; NEW is the vein-A framing of a degree-stratified 'spectral boundary' (cubic element vs deg-2 role-limit).
- **Tags.** foundation, cubic, degree-stratified, vein-A, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `is_mode3/elt3_mode_1/_2/_3/cube_gives_rational_mode/cubic_two_reduces/square_gives_element2/deg2_role_limit_golden` | Definition/Theorem | ★ куб → рациональная мода; deg-2 → золотое role-limit |
| `BoundaryDegree/boundary_degree_stratified/cubic_spectral_boundary` | Definition/Theorem | ★ граница, стратифицированная по степени |

**Key lemmas (deep):**

- **`cubic_spectral_boundary`** - Спектральная граница стратифицирована по СТЕПЕНИ: кубическое уравнение даёт рациональную моду (Element), степень-2 (золотое сечение) — role-limit над Q. Расширяет вену A с перфект-квадрата на степенную стратификацию — какие степени дают Element vs role-limit. _(cubic, degree-stratified, spectral-boundary, vein-A)_

**Uniqueness - score 3 (new-framing).** Кубический спектр над Q: граница, стратифицированная по степени — куб даёт рациональную моду (Element), deg-2 (золотое) даёт role-limit (вена A).
> _Caveat:_ Рациональность кубических vs иррациональность золотого сечения элементарна; вклад — вена-A стратификация границы по степени, не новый результат.

---

## #208 - `src/foundation/DecidableBoundary.v` - score 3 (new-framing)

**Decidable boundary over Z: is_square decides element vs role-limit (vein A flagship)**

- **Topic.** is_square over Z (boolean, reflection), a discriminant over Z, a coupling element (boolean, decidable), deciding the diagonal element, deciding the golden role-limit, and a decidable finitization boundary.
- **Role.** Vein-A flagship (the decidable finitization boundary over Z). Self-contained (ZArith).
- **Counts.** Qed 2 / Admitted 0 / axioms 0
- **Imports.** Stdlib: ZArith
- **E/R/R.** _Elements:_ дискриминант над Z; перфект-квадрат тест. _Roles:_ is_square = РАЗРЕШИМАЯ роль-решатель (Element vs role-limit). _Rules:_ coupling_element_decidable; decide_diagonal_element; decide_golden_role_limit. _P4:_ конечный разрешимый тест над Z (Element); is_square РЕШАЕТ границу финитизации (диагональ=Element, золотое=role-limit) — ФЛАГМАН вены A.
- **Classical counterpart.** Deciding whether an integer is a perfect square (hence whether a discriminant gives a rational root) is classical; NEW is the vein-A flagship framing: a DECIDABLE finitization boundary where is_square decides element vs role-limit (the golden case).
- **Tags.** foundation, decidable, is-square, finitization-boundary, vein-A, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `is_square_Z/is_square_Z_b/is_square_Z_reflect/disc_Z/coupling_element/coupling_element_b/coupling_element_decidable` | Definition/Theorem | ★ is_square разрешим (булев + рефлексия) |
| `decide_diagonal_element/decide_golden_role_limit/decidable_finitization_boundary` | Theorem | ★ РЕШАЕТ Element (диагональ) vs role-limit (золотое) |

**Key lemmas (deep):**

- **`decidable_finitization_boundary`** - ФЛАГМАН вены A: разрешимый тест is_square (с булевой рефлексией) РЕШАЕТ границу финитизации — диагональный случай даёт Element (перфект-квадрат дискриминант), золотое сечение — role-limit. Граница между «вычислимым/конечным» и «предельным» сделана АЛГОРИТМИЧЕСКОЙ. Корень одной из главных уникальностей проекта (decidable finitization boundary). _(decidable, is-square, finitization-boundary, vein-A, flagship)_

**Uniqueness - score 3 (new-framing).** Разрешимая граница над Z (ФЛАГМАН вены A): is_square (булев+рефлексия) РЕШАЕТ финитизацию — диагональ=Element (перфект-квадрат), золотое=role-limit. Граница вычислима, алгоритмична.
> _Caveat:_ Разрешимость перфект-квадрата классична; уникальность — в том, что эта разрешимость СТАНОВИТСЯ границей Element/role-limit (финитизации), а не в новом тесте квадрата.

---

## #209 - `src/foundation/DecidableBoundaryQ.v` - score 3 (new-framing)

**Decidable boundary over Q: is_square_Q decides element vs role-limit (vein A flagship)**

- **Topic.** A relatively-prime square, a square quotient, is_square_Q (boolean), Z<->Q square bridges, reflection, deciding the quarter element (a square), the half role-limit, and a decidable finitization boundary over Q.
- **Role.** Vein-A flagship (the decidable finitization boundary over Q, lifting DecidableBoundary to rationals). Self-contained (QArith).
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ рациональный перфект-квадрат тест (числитель/знаменатель). _Roles:_ is_square_Q = РАЗРЕШИМАЯ роль-решатель над Q. _Rules:_ is_square_Q_reflect; quarter_is_square; half_is_role_limit. _P4:_ конечный разрешимый тест над Q (Element); is_square_Q РЕШАЕТ границу (1/4=Element, 1/2=role-limit) — ФЛАГМАН вены A над Q.
- **Classical counterpart.** Deciding whether a rational is a perfect square (reduced numerator and denominator both squares) is classical; NEW is the vein-A flagship over Q: is_square_Q decides element (quarter) vs role-limit (half).
- **Tags.** foundation, decidable, is-square-Q, finitization-boundary, vein-A, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `rel_prime_sqr/square_quotient/is_square_Q/is_square_Q_b/is_square_Z_to_Q/is_square_Q_to_Z/is_square_Q_reflect` | Definition/Theorem | ★ is_square_Q разрешим (Z↔Q мосты) |
| `decide_quarter_element/quarter_is_square/half_is_role_limit/decidable_finitization_boundary_Q` | Theorem | ★ РЕШАЕТ: 1/4=Element, 1/2=role-limit |

**Key lemmas (deep):**

- **`decidable_finitization_boundary_Q`** - ФЛАГМАН вены A над Q: is_square_Q (числитель И знаменатель — квадраты, с Z↔Q мостами) РЕШАЕТ границу финитизации — 1/4 даёт Element (перфект-квадрат), 1/2 — role-limit. Поднимает DecidableBoundary с Z на рациональные: разрешимая граница Element/role-limit над полем Q. Ядро уникальности проекта. _(decidable, is-square-Q, finitization-boundary, vein-A, flagship)_

**Uniqueness - score 3 (new-framing).** Разрешимая граница над Q (ФЛАГМАН вены A): is_square_Q (числитель+знаменатель квадраты) РЕШАЕТ финитизацию — 1/4=Element, 1/2=role-limit. Поднимает Z-границу на рациональные.
> _Caveat:_ Разрешимость рационального квадрата классична; уникальность — в роли этой разрешимости как границы Element/role-limit над Q, не в новом тесте.

---

## #210 - `src/foundation/DegreeTwoSpecial.v` - score 2 (methods)

**Degree-two special over Q: only degree 2 is preserved**

- **Topic.** A degree-2 quantity preserved (at a point), degrees 1/3/4 broken, a degree type, preserved, and only degree-2 preserved.
- **Role.** Foundational leaf (degree-2 specialness, vein-A-adjacent). Self-contained (QArith).
- **Counts.** Qed 1 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ величины степени 1/2/3/4. _Roles:_ степень 2 = особая роль (сохраняется); другие степени ломаются. _Rules:_ deg2_preserved; only_deg2_preserved; degree_two_special. _P4:_ конечные величины над Q (Element); только степень 2 сохраняется.
- **Classical counterpart.** That a degree-2 (quadratic) map has special preservation properties not shared by degrees 1/3/4 is elementary; NEW only as a small Q instance ('only deg-2 preserved').
- **Tags.** foundation, degree-two, vein-A-adjacent, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `deg2_preserved/deg2_at_point/deg1_broken/deg3_broken/deg4_broken/Degree/preserved` | Definition/Theorem | степень 2 сохраняется, другие ломаются |
| `only_deg2_preserved/degree_two_special` | Theorem | ★ только степень 2 сохраняется |

**Key lemmas (deep):**

- **`only_deg2_preserved`** - Только степень 2 (квадратичная) сохраняется, степени 1/3/4 ломаются над Q — выделяет особость степени-2 (отголосок показателя-2 Борна и квадратичных форм). Малый файл, вена-A-смежно (степень как граница). _(degree-two, special, vein-A-adjacent)_

**Uniqueness - score 2 (methods).** Особость степени 2 над Q: только степень 2 сохраняется, степени 1/3/4 ломаются.
> _Caveat:_ Особые свойства квадратичных отображений элементарны; малый Q-инстанс, вена-A-смежно.

---

## #211 - `src/foundation/DemarcationClosure.v` - score 2 (methods)

**Demarcation closure over Q: ToS reaches rung 2, never fully forced (honest)**

- **Topic.** A warrant strength and classifier, counts of rung-2/rung-3/numerology/falsified/non-empirical, genuine-confirmed, a warrant total, ToS never fully forced, ToS reaches rung 2, and the summit is rung 2.
- **Role.** Honesty/demarcation meta leaf. Self-contained.
- **Counts.** Qed 1 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ уровни обоснования (warrant rungs); счётчики. _Roles:_ демаркация = роль-классификатор; ToS достигает rung-2, не форсирована полностью. _Rules:_ tos_never_fully_forced; tos_summit_is_rung_2; count_numerology. _P4:_ конечная классификация (Element); ЧЕСТНО: ToS на rung-2, не полностью вынуждена (калибровка против over-claim).
- **Classical counterpart.** No direct counterpart — an internal demarcation audit (Popper-flavoured warrant rungs) honestly classifying ToS claims and concluding 'ToS reaches rung 2, is never fully forced'.
- **Tags.** foundation, honesty, demarcation, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `Warrant/strength/warrant_of/warrant_eqb/count_warrant/count_rung2/_rung3/_numerology/_falsified/_nonempirical/genuine_confirmed/_eq/warrant_total` | Definition/Theorem | уровни обоснования, счётчики |
| `tos_never_fully_forced/tos_reaches_rung2/tos_summit_is_rung_2/demarcation_closure` | Theorem | ★ ToS на rung-2, не полностью вынуждена |

**Key lemmas (deep):**

- **`tos_summit_is_rung_2`** - ЧЕСТНАЯ демаркация: классифицирует обоснования и заключает, что ToS достигает «rung 2», но НИКОГДА не вынуждена полностью (tos_never_fully_forced) — встроенная калибровка против over-claim, отделяющая подтверждённое от нумерологии. _(honesty, demarcation, warrant, calibration)_

**Uniqueness - score 2 (methods).** Демаркационное закрытие над Q: ToS достигает rung-2, никогда не вынуждена полностью; счётчики rung-2/rung-3/нумерологии (честная калибровка).
> _Caveat:_ Внутренний honesty-аудит (демаркация Поппера); собственного физического результата нет, ценность — калибровка.

---

## #212 - `src/foundation/DepartureDescent.v` - score 2 (methods)

**Departure descent over Q: departure terminates to a finite element**

- **Topic.** A q-sum, a departure partial (at 0, stabilizes, terminates, finite value), a boundary-kind, departure-kind, and departure not a role-limit.
- **Role.** Wall-taxonomy leaf (departure terminates = element). Self-contained (QArith).
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ departure-сумма; частичные суммы. _Roles:_ departure = роль, терминирующая к конечному значению (Element). _Rules:_ departure_stabilizes; departure_terminates; departure_not_role_limit. _P4:_ конечные суммы (Element); departure терминирует → Element, НЕ role-limit.
- **Classical counterpart.** No direct counterpart — a ToS audit showing a 'departure' quantity terminates to a finite value (an element, not a role-limit).
- **Tags.** foundation, departure, wall-taxonomy, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `qsum/departure_partial/_0/departure_stabilizes/departure_terminates/departure_finite_value` | Definition/Theorem | ★ departure терминирует к конечному значению |
| `BoundaryKind3/departure_kind/departure_not_role_limit/departure_descent` | Definition/Theorem | departure = Element, не role-limit |

**Key lemmas (deep):**

- **`departure_not_role_limit`** - Величина «departure» терминирует к конечному значению (Element), а не остаётся role-limit над Q — классификация по границе финитизации (вена-A-смежно). Отделяет терминирующие величины от предельных. _(departure, terminates, element, vein-A-adjacent)_

**Uniqueness - score 2 (methods).** Спуск departure над Q: величина терминирует к конечному значению (Element), не role-limit.
> _Caveat:_ Внутренняя классификация терминации; вклад — отнесение departure к Element-стороне границы, не новый результат.

---

## #213 - `src/foundation/DepartureWallDescent.v` - score 2 (methods)

**Departure wall descent over Q: departure is a fourth, non-fundamental wall**

- **Topic.** A departure process (terminates, value determined), an exp process (never stabilizes), a wall type, is-fundamental-wall, departure not fundamental, departure is the fourth type, and genuine walls are fundamental.
- **Role.** Wall-taxonomy leaf (departure = 4th non-fundamental wall). Self-contained (QArith).
- **Counts.** Qed 1 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ departure/exp процессы; типы стен. _Roles:_ стена = роль-тип; departure — 4-й НЕ фундаментальный тип. _Rules:_ departure_terminates; exp_never_stabilizes; departure_not_fundamental. _P4:_ конечные процессы (Element); departure терминирует (не фундаментальная стена), exp не стабилизируется (фундаментальная).
- **Classical counterpart.** No direct counterpart — a ToS wall-taxonomy audit classifying 'departure' as a fourth, non-fundamental wall type (genuine walls are fundamental).
- **Tags.** foundation, wall-taxonomy, departure, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `K_dep/dep_process/dep_terminates/dep_value_determined/exp_process/exp_never_stabilizes` | Definition/Theorem | departure терминирует, exp не стабилизируется |
| `Wall/WallType/wall_type/is_fundamental_wall/departure_not_fundamental/departure_is_fourth_type/genuine_walls_are_fundamental/departure_descent` | Definition/Theorem | ★ departure = 4-й не фундаментальный тип стены |

**Key lemmas (deep):**

- **`departure_not_fundamental`** - Departure классифицирован как ЧЕТВЁРТЫЙ, НЕ фундаментальный тип стены (он терминирует, тогда как exp_never_stabilizes — фундаментальная) над Q. Уточняет таксономию финитизационных стен. Вена-A-смежно. _(wall-taxonomy, departure, non-fundamental)_

**Uniqueness - score 2 (methods).** Departure как 4-й не фундаментальный тип стены над Q (терминирует), exp — фундаментальный (не стабилизируется).
> _Caveat:_ Внутренняя таксономия стен; вклад — классификация departure, не новый результат.

---

## #214 - `src/foundation/DepthFixpoint.v` - score 2 (methods)

**Depth fixpoint over Q: SM gauge group at depth 3, nothing new beyond 2**

- **Topic.** Regions, gauge/endo dimensions, depths 0-3 (depth-3/4 fixpoints), the gauge groups SU2/SU3/U1 at depth 3, total gauge, an endo fixpoint, no new beyond 2, SM predicted, binary at depth 0, ternary at depth 1, and fixpoint stability.
- **Role.** Distinction->SM leaf (depth fixpoint -> gauge group). SM-from-distinction OVER-BRANDED. Self-contained.
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ глубины вложенности; калибровочные размерности. _Roles:_ фиксточка глубины = роль (SM на глубине 3); нет нового за глубиной 2. _Rules:_ depth3_fixpoint; no_new_beyond_2; SM_predicted. _P4:_ конечные глубины (Element); SM-калибровка на глубине-3 фиксточке; SM-from-distinction OVER-BRANDED.
- **Classical counterpart.** No classical counterpart — a ToS nesting-depth fixpoint argument concluding the SM gauge group (SU3xSU2xU1) at depth 3 with no new structure beyond depth 2 (SM-from-distinction OVER-BRANDED).
- **Tags.** foundation, depth-fixpoint, gauge-group, over-branded, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `regions/gauge_dim/endo_dim/depth0/_1/_2/depth3_fixpoint/depth4_fixpoint` | Definition/Theorem | глубины, фиксточки |
| `gauge_SU2/_SU3/_U1/gauge_depth3/total_gauge/endo_fixpoint/no_new_beyond_2/SM_predicted/binary_at_depth0/ternary_at_depth1/fixpoint_stability` | Theorem | ★ SM-калибровка на глубине 3, нет нового за 2 |

**Key lemmas (deep):**

- **`no_new_beyond_2`** - Вложенность различений достигает фиксточки на глубине 3 (SU3×SU2×U1), без новой структуры за глубиной 2 над Q — аргумент за SM-калибровку из глубины. SM-from-distinction OVER-BRANDED: фиксточка построена так, чтобы дать SM, а не вынуждает его. _(depth-fixpoint, gauge-group, over-branded)_

**Uniqueness - score 2 (methods).** Фиксточка глубины над Q: SM-калибровка SU3×SU2×U1 на глубине 3, нет новой структуры за глубиной 2.
> _Caveat:_ Конструкция настроена давать SM-калибровку; SM-from-distinction OVER-BRANDED, не вывод.

---

## #215 - `src/foundation/DepthThreeNecessity.v` - score 2 (methods)

**Depth-three necessity over Q: depth exactly 3 for matter, CP, 3 generations**

- **Topic.** Depth sufficient for matter (depths 1/2 insufficient, 3 sufficient), CP requires depth 3, depth bounded by terminal, SM depth is 3, depth exactly three (minimum sufficient), the gauge group unique from minimality, repetition kills uniqueness, three generations from depth 3, and depth 3 enables CP.
- **Role.** Distinction->SM leaf (depth-3 necessity). SM-from-distinction OVER-BRANDED. Self-contained.
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ глубина вложенности; материя/CP/поколения. _Roles:_ глубина-3 = роль-необходимость (материя, CP, 3 поколения). _Rules:_ depth_exactly_three; cp_requires_depth3; three_gen_from_depth3. _P4:_ конечная глубина (Element); глубина=3 как минимум для материи/CP; SM-from-distinction OVER-BRANDED.
- **Classical counterpart.** No classical counterpart — a ToS argument that nesting depth must be exactly 3 (for matter/CP/3 generations), with the gauge group from minimality (SM-from-distinction OVER-BRANDED).
- **Tags.** foundation, depth-three, over-branded, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `depth_sufficient_for_matter/depth_1_insufficient/depth_2_insufficient/depth_3_sufficient/cp_requires_depth3/depth_bounded_by_terminal/sm_depth_bounded/sm_depth_is_3/terminal_stops_nesting` | Theorem | глубина-3 достаточна, 1/2 нет |
| `depth_exactly_three/depth_3_is_minimum_sufficient/gauge_group_unique/_from_minimality/repetition_kills_uniqueness/three_gen_from_depth3/depth3_enables_cp/depth_three_necessity_summary/_count` | Theorem | ★ глубина ровно 3, 3 поколения, CP |

**Key lemmas (deep):**

- **`depth_exactly_three`** - Аргумент, что глубина вложенности должна быть РОВНО 3 (1/2 недостаточны для материи, 3 даёт CP и 3 поколения) над Q. SM-from-distinction OVER-BRANDED: «необходимость» опирается на встроенные пороги достаточности, а не выводит их независимо. _(depth-three, necessity, 3-generations, over-branded)_

**Uniqueness - score 2 (methods).** Необходимость глубины-3 над Q: глубина ровно 3 для материи/CP/3 поколений, калибровка из минимальности.
> _Caveat:_ Пороги достаточности встроены; SM-from-distinction OVER-BRANDED, не независимый вывод.

---

## #216 - `src/foundation/DerivedVsNumerological.v` - score 2 (methods)

**Derived vs numerological over Q: honest count of which constants are derived**

- **Topic.** A match always available, the neutrino value with a non-unique match, sin^2 selected, an evidence/confirmed-prediction classifier, counts of evidence, n derived vs n numerological.
- **Role.** Honesty/meta leaf (derived vs numerological audit). Self-contained.
- **Counts.** Qed 4 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ константы; совпадения (derived vs numerological). _Roles:_ аудит = роль-классификатор подлинности вывода. _Rules:_ neutrino_match_nonunique; n_derived; n_numerological. _P4:_ конечная классификация (Element); ЧЕСТНО: часть «совпадений» нумерологичны (neutrino_match_nonunique), не выводы.
- **Classical counterpart.** No direct counterpart — an internal HONESTY audit distinguishing genuinely derived constants from numerological matches (e.g. the neutrino value match is non-unique).
- **Tags.** foundation, honesty, numerological, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `match_always_available/neutrino_value/neutrino_match_nonunique/sin2_selected` | Definition/Theorem | совпадение всегда доступно, нейтрино неуникально |
| `Evidence/ConfPred/evidence/all_confpred/evidence_eqb/count_evidence/n_derived/n_numerological/derived_vs_numerological` | Definition/Theorem | ★ счёт derived vs numerological |

**Key lemmas (deep):**

- **`neutrino_match_nonunique`** - ЧЕСТНО: «совпадение всегда доступно» (match_always_available), нейтринное значение имеет НЕУНИКАЛЬНОЕ совпадение → нумерология, не вывод. Классифицирует n_derived vs n_numerological. Сильная встроенная калибровка против over-claim численных предсказаний. _(honesty, numerological, derived, calibration)_

**Uniqueness - score 2 (methods).** Derived vs numerological над Q: честный счёт выведенных констант против нумерологических совпадений (neutrino_match_nonunique).
> _Caveat:_ Внутренний honesty-аудит; ценность — калибровка (что вывод, что нумерология), не новый результат.

---

## #217 - `src/foundation/DeterminantModB.v` - score 2 (methods)

**Determinant mod B over Q: rational eigenvalue of an integer n x n matrix is integer**

- **Topic.** Scalars, minors, cofactors, a fold determinant, a determinant congruence mod b, the characteristic matrix, a general-n rational-eigenvalue-is-integer theorem, a diag(2,3) eigenvalue-2 example, and 'determinant closes general n'.
- **Role.** Vein-A leaf (rational-root theorem, general n). Generalizes CharPolyEigenvalue3. Self-contained.
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: ZArith
- **E/R/R.** _Elements:_ n×n целые матрицы; характеристический многочлен; миноры. _Roles:_ рациональный корень монического char-многочлена = роль (обязан быть целым). _Rules:_ rational_eigenvalue_nxn_is_integer; det_congr_mod_b; determinant_closes_general_n. _P4:_ конечные n×n матрицы над Z (Element); рациональное собственное значение целочисленно для ЛЮБОГО n (вена A).
- **Classical counterpart.** The rational-root theorem generalized to n x n integer matrices (a rational eigenvalue of an integer matrix is an integer, via the monic characteristic polynomial) is classical; NEW only as a general-n Coq instance (vein-A-flavoured).
- **Tags.** foundation, rational-root, general-n, vein-A, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `scalar/minor/cof/detf/fold_all_zero/div_fold_add/fold_map_sub/detf_ext/minor_scalar0/det_scalar/det_congr_mod_b/charmat` | Definition/Theorem | детерминант, миноры, конгруэнция |
| `rational_eigenvalue_nxn_is_integer/det2_diag23_eig2/determinant_closes_general_n` | Theorem | ★ рациональное с.з. целочисленно для общего n |

**Key lemmas (deep):**

- **`rational_eigenvalue_nxn_is_integer`** - Обобщает теорему о рациональном корне на ЛЮБОЕ n: рациональное собственное значение целочисленной n×n-матрицы обязано быть целым (через det-конгруэнцию mod b) над Z. Вена A в общей размерности — расширяет CharPolyEigenvalue3 (3x3) до determinant_closes_general_n. _(rational-root, general-n, eigenvalue, vein-A)_

**Uniqueness - score 2 (methods).** Детерминант mod B над Z: рациональное собственное значение целочисленной n×n-матрицы целочисленно для общего n (вена A, обобщение 3x3).
> _Caveat:_ Теорема о рациональном корне классична; вклад — общий-n Coq-инстанс (вена A), не новый результат.

---

## #218 - `src/foundation/DiffeoIsRelabeling.v` - score 2 (new-framing)

**Diffeomorphism is relabeling over Q: order/number invariant, labels not**

- **Topic.** A relation, an order isomorphism, number/order relabel invariance, an antichain, three points, a swap (an order iso, involutive), concrete number invariance, the head label not invariant, and diffeo = relabel invariance.
- **Role.** Relational-geometry leaf (diffeo = relabeling, vein-C-flavoured). Self-contained.
- **Counts.** Qed 2 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ отношения порядка; точки; перестановки (swap). _Roles:_ диффеоморфизм = роль-перемаркировка (сохраняет порядок/число). _Rules:_ order_relabel_invariant; number_invariant_concrete; diffeo_is_relabel_invariance. _P4:_ конечные точки (Element); диффео = перемаркировка — порядок/число инвариантны, метки нет (вена C).
- **Classical counterpart.** That a diffeomorphism is a relabeling (gauge) preserving order/number but not labels — the relational/background-independent view — is standard; NEW only as a small Q instance (an order isomorphism via swaps).
- **Tags.** foundation, diffeomorphism, relabeling, vein-C, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `Relation/order_iso/number_relabel_invariant/order_relabel_invariant/antichain/pts3/swap02/_iso/_involutive` | Definition/Theorem | порядок-изоморфизм, swap |
| `number_invariant_concrete/head_label_not_invariant/diffeo_is_relabel_invariance` | Theorem | ★ диффео = перемаркировка (число инвариантно, метка нет) |

**Key lemmas (deep):**

- **`diffeo_is_relabel_invariance`** - Диффеоморфизм = перемаркировка: порядок и число инвариантны, метки (head_label) нет над Q — формализация фон-независимости/калибровки координат (ср. BackgroundIndependence). Вена-C-смежно: физическое содержание в порядке/числе, не в метках. _(diffeomorphism, relabeling, background-independence, vein-C)_

**Uniqueness - score 2 (new-framing).** Диффео = перемаркировка над Q: порядок/число инвариантны при swap-изоморфизме, метки нет — фон-независимость.
> _Caveat:_ Диффео как калибровка/перемаркировка — стандартный реляционный взгляд; вклад — малый Q-инстанс, не новый результат.

---

## #219 - `src/foundation/DimensionFromSpin.v` - score 2 (methods)

**Dimension from spin over Q: d=3, D=4 from spin-1 and orbital stability**

- **Topic.** Spin-1 dimension bounds, max d for stability, spatial/spacetime dimension, a derived metric DOF, force exponent, stable orbits, n_metric at d, sin^2 at d, spin-1 needs 3, stability needs <=3, d=3, D=4, n_metric=10, and constraints agree.
- **Role.** Dimension-derivation leaf (d=3 from spin/stability). 'Uniquely determined' OVER-BRANDED. Self-contained (QArith).
- **Counts.** Qed 4 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ размерности (пространственная/пространство-время); спин-1; стабильность. _Roles:_ размерность = роль (d=3 из спина-1 + стабильности орбит). _Rules:_ spin1_needs_3; stability_needs_le3; d_is_3/D_is_4. _P4:_ конечные размерности (Element); d=3 из совпадения ограничений; «uniquely determined» OVER-BRANDED.
- **Classical counterpart.** Arguments that 3 spatial dimensions are special (spin-1 needs 3, stable orbits need <=3, inverse-square in d=3) are classic anthropic/dimensional-analysis results; NEW only as a Q instance concluding d=3, D=4 (the 'uniquely determined' framing is OVER-BRANDED).
- **Tags.** foundation, dimension, spin, over-branded, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `spin1_dim/min_d_for_spin1/max_d_for_stability/spatial_dim/spacetime_dim/n_metric_derived/force_exponent/stable_orbits/n_metric_at_d/sin2_at_d` | Definition/Theorem | размерности, метрика, сила |
| `spin1_needs_3/stability_needs_le3/d_is_3/D_is_4/n_metric_is_10/force_exp_d3/_d4/stable_d3/_d4/wrong_d2/_d4/correct_d3/dimension_uniquely_determined/stability_excludes_d4_and_above/constraints_agree` | Theorem | ★ d=3, D=4 из спина+стабильности |

**Key lemmas (deep):**

- **`constraints_agree`** - d=3 (D=4) выводится из совпадения двух ограничений: спин-1 требует ≥3, стабильность орбит требует ≤3 над Q. Классические анти­пные/размерные аргументы. «dimension_uniquely_determined» OVER-BRANDED: ограничения встроены, а совпадение — не независимый вывод. _(dimension, spin-1, stability, over-branded)_

**Uniqueness - score 2 (methods).** Размерность из спина над Q: d=3, D=4 из спин-1≥3 и стабильности орбит≤3 (ограничения совпадают), n_metric=10.
> _Caveat:_ Особость d=3 (спин/орбиты/обратный квадрат) — классические аргументы; «uniquely determined» OVER-BRANDED.

---

## #220 - `src/foundation/DimensionPositReduction.v` - score 2 (methods)

**Dimension posit reduction over Q: D=4 rests on one honest posit**

- **Topic.** Triangular numbers, the metric DOF as triangular, D=4 derived/clamped, a stability posit, D=4 just/grounded, D=4 one new posit, an ERR-level for dimension/DOF-model, and the DOF model bundling both.
- **Role.** Honesty/posit-reduction leaf for dimension. Self-contained.
- **Counts.** Qed 4 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ треугольные числа; метрические DOF; D=4. _Roles:_ редукция постулатов = роль; D=4 на ОДНОМ новом постулате (стабильность). _Rules:_ metric_dof_triangular; D4_one_new_posit; stability_posit. _P4:_ конечные DOF (Element); ЧЕСТНО: D=4 опирается на 1 явный постулат стабильности, не чистый вывод.
- **Classical counterpart.** No direct counterpart — an HONEST posit-reduction showing D=4 rests on one new posit (a stability posit), the metric DOF being triangular.
- **Tags.** foundation, honesty, posit-reduction, dimension, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `triangular/triangular_4/triangular_double/metric_dof_triangular/D4_is_derived/D4_clamped/stability_posit` | Definition/Theorem | треугольные DOF, D=4 выведено/закреплено |
| `D4_just/D4_just_grounded/D4_one_new_posit/ERRLevel/dim_level/dofmodel_level/residual_levels_distinct/dof_model_bundles_both/dimension_posit_reduction` | Theorem | ★ D=4 на одном явном постулате |

**Key lemmas (deep):**

- **`D4_one_new_posit`** - ЧЕСТНО: D=4 сводится к ОДНОМУ новому постулату (стабильность), метрические DOF треугольны над Q. Редукция постулатов — образец калибровки: явно фиксирует единственный остаточный постулат, а не выдаёт D=4 за чистый вывод. _(honesty, posit-reduction, dimension)_

**Uniqueness - score 2 (methods).** Редукция постулатов размерности над Q: D=4 опирается на ОДИН явный постулат стабильности, метрические DOF треугольны.
> _Caveat:_ Внутренняя редукция постулатов; ценность — честная фиксация единственного остаточного постулата, не новый результат.

---

## #221 - `src/foundation/DimensionRoleLimit.v` - score 2 (new-framing)

**Dimension role-limit over Q: integer dimension is an element, between-powers is a role-limit**

- **Topic.** Dimension is an element (16, 8), a between-powers role-limit (5, 7), and dimension is a finitization boundary.
- **Role.** Vein-A/C leaf (dimension as finitization boundary). Self-contained (QArith).
- **Counts.** Qed 2 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ размерности (степени vs между-степенные). _Roles:_ целая размерность = Element (степень); между-степенная = role-limit. _Rules:_ dim_is_element; between_powers_role_limit; dimension_is_finitization_boundary. _P4:_ конечные размерности (Element); целая размерность=Element, дробная между степенями=role-limit — размерность как граница финитизации (вена A/C).
- **Classical counterpart.** No classical counterpart — the vein-A/C statement that an integer dimension is an element (a perfect power) while a value between powers is a role-limit (dimension is a finitization boundary).
- **Tags.** foundation, dimension, role-limit, vein-A, vein-C, new-framing

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `dim_is_element/dim_element_16/dim_element_8/between_powers_role_limit/dim_role_limit_5/dim_role_limit_7/dimension_is_finitization_boundary` | Definition/Theorem | ★ целая размерность=Element, между=role-limit |

**Key lemmas (deep):**

- **`dimension_is_finitization_boundary`** - Размерность сама есть граница финитизации: целые/степенные значения (16, 8) суть Element, значения между степенями (5, 7) — role-limit над Q. Применяет вену-A/C дихотомию Element/role-limit к понятию размерности (ср. fractal dimension). Сжатый, но содержательный. _(dimension, role-limit, finitization-boundary, vein-A, vein-C)_

**Uniqueness - score 2 (new-framing).** Размерность как граница финитизации над Q: целая/степенная размерность=Element, между-степенная=role-limit.
> _Caveat:_ Дихотомия Element/role-limit — ядро проекта; здесь применена к размерности (малый файл), не новый результат.

---

## #222 - `src/foundation/DimensionThreeAxes.v` - score 2 (methods)

**Dimension three axes over Q: compact/noncompact/null with a finite-element test**

- **Topic.** A Fin (finite) flag, a discriminant-is-square test, a boost-345 finite element vs a boost-P finite role-limit, a compact disc not square, type doesn't fix Fin, a dimension locus with rank-preserving up-iteration, and three axes.
- **Role.** Dimension-classification leaf (with a vein-A discriminant test). Self-contained (QArith).
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ типы преобразований (compact/noncompact/null); дискриминант. _Roles:_ тип = роль (rotation/boost/shear); finite-test через перфект-квадрат. _Rules:_ boost345_fin_element; boostP_fin_rolelimit; disc_is_square. _P4:_ конечные преобразования над Q (Element); finite-статус через перфект-квадрат дискриминант (вена A): boost345=Element, boostP=role-limit.
- **Classical counterpart.** Classifying transformations as compact/noncompact/null (rotation/boost/shear) preserving definite/indefinite forms is standard Lie-group geometry; NEW only as a Q instance with a discriminant-square 'finite element' test.
- **Tags.** foundation, dimension, compact-noncompact, vein-A, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `Fin/disc_is_square/q_sqr_nonneg/boost345_fin_element/boostP_fin_rolelimit/compact_disc_not_square/type_does_not_fix_fin` | Definition/Theorem | ★ finite через перфект-квадрат (boost345 vs boostP) |
| `DimLocus/dl_up/_rank/dl_up_preserves_type/_preserves_fin/dl_iter/dl_reach/dimension_three_axes` | Definition/Theorem | локус размерностей, ранг-сохранение |

**Key lemmas (deep):**

- **`boost345_fin_element`** - Finite-статус преобразования решается перфект-квадратом дискриминанта: boost-345 (пифагорова тройка) даёт finite Element, boost-P — role-limit над Q. Совмещает классификацию compact/noncompact/null с веной A (is_square). type_does_not_fix_fin: тип не определяет finiteness. _(dimension, compact-noncompact, discriminant, vein-A)_

**Uniqueness - score 2 (methods).** Три оси размерности над Q: compact/noncompact/null + finite-тест через перфект-квадрат дискриминанта (boost345=Element, boostP=role-limit).
> _Caveat:_ Классификация compact/noncompact/null — стандартная геометрия групп Ли; вклад — Q-инстанс с веной-A finite-тестом.

---

## #223 - `src/foundation/DimensionTwoAxes.v` - score 2 (methods)

**Dimension two axes over Q: type vs rank classification**

- **Topic.** A DimType (compact/noncompact/null), rotation compact / boost noncompact / shear null, compact preserves definite / noncompact indefinite, a locus with step up/down/flip-type, nesting changes rank but preserves type, type preserves rank, axes commute, and flip-type involutive.
- **Role.** Dimension-classification leaf (type vs rank, two axes). Self-contained.
- **Counts.** Qed 2 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ типы преобразований; ранг; локус. _Roles:_ тип (compact/noncompact/null) и ранг = две независимые оси. _Rules:_ nesting_changes_rank; nesting_preserves_type; axes_commute. _P4:_ конечные локусы (Element); тип и ранг — две коммутирующие оси классификации.
- **Classical counterpart.** Classifying transformation types (compact/noncompact/null) preserving definite/indefinite/degenerate forms, with a nesting that preserves type but changes rank, is standard; here a Q instance.
- **Tags.** foundation, dimension, type-rank, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `DimType/is_compact/is_noncompact/is_null/rotation_is_compact/boost_is_noncompact/shear_is_null/compact_preserves_definite/noncompact_preserves_indefinite` | Definition/Theorem | типы (compact/noncompact/null) |
| `Locus/step_up/_down/flip_type/locus_of/ascend_is_step_up/nesting_changes_rank/_preserves_type/type_preserves_rank/type_flip_changes/axes_commute/flip_type_involutive/iter_up/reach_grid/dimension_two_axes` | Definition/Theorem | ★ тип и ранг — две коммутирующие оси |

**Key lemmas (deep):**

- **`axes_commute`** - Тип (compact/noncompact/null) и ранг — две НЕЗАВИСИМЫЕ коммутирующие оси: вложенность меняет ранг, сохраняя тип; flip-type инволютивен над Q. Классификация преобразований по двум осям. Стандартная геометрия групп Ли. _(dimension, type-rank, compact-noncompact)_

**Uniqueness - score 2 (methods).** Две оси размерности над Q: тип (compact/noncompact/null) и ранг независимы и коммутируют (вложенность меняет ранг, сохраняет тип).
> _Caveat:_ Классификация типов преобразований стандартна; вклад — Q-инстанс двух-осевой классификации, не новый результат.

---

## #224 - `src/foundation/DiracFromSpin.v` - score 2 (methods)

**Dirac from spin over Q: minimal Clifford dimension is 4, Pauli anticommute**

- **Topic.** Minimal Clifford dimension at d=1/2/3, the Dirac dimension, dirac_d3 is 4, a 2x2 matrix algebra, sigma1/sigma3, anticommutator, sigma13 anticommutator components, and Pauli anticommute.
- **Role.** Spin/Dirac leaf (Clifford dimension). Self-contained.
- **Counts.** Qed 2 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ алгебра Клиффорда; матрицы Паули sigma1/sigma3. _Roles:_ размерность Дирака = роль (минимальный спинор); антикоммутатор как роль. _Rules:_ dirac_d3_is_4; pauli_anticommute; clifford_min_dim. _P4:_ конечные 2×2 матрицы (Element); минимальная размерность Дирака = 4 в d=3+1.
- **Classical counterpart.** The minimal Clifford-algebra / Dirac spinor dimension in d dimensions (4 in d=3+1) and Pauli-matrix anticommutation are standard; here a Q instance.
- **Tags.** foundation, dirac, clifford, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `clifford_min_dim/clifford_d1/_d2/_d3/dirac_dim/dirac_d3_is_4` | Definition/Theorem | ★ минимальная размерность Дирака = 4 |
| `M2/mat_mul/mat_add/mat_zero/mat_id/sigma1/sigma3/anticomm/sigma13_ac_00/_01/_10/_11/pauli_anticommute/dirac_from_spin_synthesis` | Definition/Theorem | ★ Паули антикоммутируют |

**Key lemmas (deep):**

- **`pauli_anticommute`** - Минимальная размерность спинора Дирака = 4 в d=3+1 (из алгебры Клиффорда), матрицы Паули антикоммутируют над Q — стандартная спинорная алгебра. Иллюстративно. _(dirac, clifford, pauli, anticommute)_

**Uniqueness - score 2 (methods).** Дирак из спина над Q: минимальная размерность Клиффорда=4 (d=3+1), матрицы Паули антикоммутируют.
> _Caveat:_ Размерность спинора Дирака и антикоммутация Паули — учебная физика; Q-инстанс без нового содержания.

---

## #225 - `src/foundation/DiracOnLattice.v` - score 2 (methods)

**Dirac on lattice over Q: zero mode at m=0, doubler at m=-2**

- **Topic.** A 2x2 matrix and determinant, a hopping term, the Wilson-Dirac 2-determinant (factored), a zero mode at m=0, a doubler at m=-2, only two zeros, and a nonzero kernel vector.
- **Role.** Lattice-fermion leaf (Wilson-Dirac doubling). Self-contained.
- **Counts.** Qed 4 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ решёточный оператор Вильсона-Дирака; детерминант. _Roles:_ нулевая мода = роль (m=0); дублёр = роль (m=-2). _Rules:_ zero_mode_at_m0; doubler_at_m_neg2; only_two_zeros. _P4:_ конечная 2×2 решётка (Element); нулевая мода m=0 и дублёр m=-2 (удвоение фермионов).
- **Classical counterpart.** The Wilson-Dirac operator on a lattice with a massless zero mode and a doubler at m=-2 (fermion doubling) is standard lattice gauge theory; here a 2x2 Q instance.
- **Tags.** foundation, dirac, lattice, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `M2/mat2_det/hop_2/wd_2/wd_2_det/wd_2_det_factored` | Definition/Theorem | Вильсон-Дирак детерминант |
| `zero_mode_at_m0/doubler_at_m_neg2/only_two_zeros/kernel_vec_m0/kernel_check_0/_1/kernel_nonzero/dirac_on_lattice_synthesis` | Theorem | ★ нулевая мода m=0, дублёр m=-2 |

**Key lemmas (deep):**

- **`doubler_at_m_neg2`** - Решёточный оператор Вильсона-Дирака имеет нулевую моду при m=0 и дублёр при m=-2 (only_two_zeros) над Q — стандартная картина фермионного удвоения. Дубликат-в-малом fermions/DiracOnGraph. _(dirac, lattice, doubler, zero-mode)_

**Uniqueness - score 2 (methods).** Дирак на решётке над Q: нулевая мода m=0, дублёр m=-2 (удвоение фермионов, ровно два нуля).
> _Caveat:_ Удвоение Вильсона-Дирака — стандартная решёточная теория; Q-инстанс без нового содержания.

---

## #226 - `src/foundation/DiscreteGeometrySynthesis.v` - score 2 (methods)

**Discrete-geometry synthesis over Q: three pieces proven, Hauptvermutung open (honest)**

- **Topic.** Metric/conformal/volume DOF (all 4), order+number DOF = 4, a discrete-geometry/chain-geometry, a claim-status type, the Hauptvermutung is open, and three pieces proven.
- **Role.** Synthesis/meta leaf (discrete geometry) with an honest open-problem flag. Self-contained.
- **Counts.** Qed 1 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ DOF (метрика/конформ/объём); порядок+число. _Roles:_ узел-синтез: геометрия из порядка+числа; Hauptvermutung ОТКРЫТА. _Rules:_ order_plus_number_dof_4; hauptvermutung_is_open; three_pieces_proven. _P4:_ конечные DOF (Element); ЧЕСТНО: 3 части доказаны, Hauptvermutung открыта (не over-claim).
- **Classical counterpart.** Reconstructing geometry from order + number (metric/conformal/volume DOF) is the causal-set program; NEW only as a synthesis that HONESTLY flags the Hauptvermutung as open (three pieces proven).
- **Tags.** foundation, discrete-geometry, honest, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `metric_dof/conformal_dof/volume_dof/metric_dof_4/conformal_dof_4/order_plus_number_dof_4/order_plus_number_dof/DiscreteGeometry/chain_geometry` | Definition/Theorem | DOF = 4 из порядка+числа |
| `ClaimStatus/Claim/status/hauptvermutung_is_open/three_pieces_proven/discrete_geometry_synthesis` | Definition/Theorem | ★ ЧЕСТНО: Hauptvermutung открыта |

**Key lemmas (deep):**

- **`hauptvermutung_is_open`** - Геометрия из порядка+числа (DOF=4), но файл ЧЕСТНО помечает Hauptvermutung как ОТКРЫТУЮ проблему (доказаны только 3 части) над Q — образец калибровки: явно фиксирует, что НЕ доказано, рядом с доказанным. _(discrete-geometry, hauptvermutung, honest, open-problem)_

**Uniqueness - score 2 (methods).** Синтез дискретной геометрии над Q: DOF=4 из порядка+числа, 3 части доказаны, Hauptvermutung ЧЕСТНО помечена открытой.
> _Caveat:_ Геометрия из порядка+числа — causal-set программа; ценность файла — честная фиксация открытой Hauptvermutung.

---

## #227 - `src/foundation/DiscriminantCompleteEigenvalue.v` - score 3 (new-framing)

**Discriminant complete eigenvalue over Q: rational eigenvalue iff discriminant is a square (vein A)**

- **Topic.** A characteristic value, has-rational-eigenvalue, a Q-discriminant, the discriminant-is-square, the eig<->square bridge both ways, rational-eigenvalue-iff-disc-square, a decision procedure over Z, boost-345 has an eigenvalue, and Fibonacci has none.
- **Role.** Vein-A leaf (discriminant decides rational eigenvalue, the 'iff'). Self-contained (QArith).
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ дискриминант 2×2; собственные значения. _Roles:_ перфект-квадрат дискриминант = роль-решатель (рациональное с.з. ⟺ квадрат). _Rules:_ rational_eigenvalue_iff_disc_square; decide_rational_eigenvalue_Z; fibonacci_no_eig. _P4:_ конечные дискриминанты над Q (Element); рациональное с.з. ⟺ дискриминант-квадрат (РЕШАЕМО): boost345 имеет, Фибоначчи (золотое) — нет (вена A, ⟺).
- **Classical counterpart.** That a 2x2 matrix has a rational eigenvalue iff its discriminant is a perfect square is elementary; NEW is the vein-A 'complete' framing with a decision procedure and a sharp contrast (boost-345 has an eigenvalue, Fibonacci/golden does not).
- **Tags.** foundation, discriminant, eigenvalue, vein-A, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `charval/has_rat_eig/discQ/disc_is_square_Q/eig_to_square/square_to_eig/rational_eigenvalue_iff_disc_square/disc_bridge` | Definition/Theorem | ★ рациональное с.з. ⟺ дискриминант-квадрат |
| `decide_rational_eigenvalue_Z/boost345_has_eig/fibonacci_no_eig/discriminant_complete_eigenvalue` | Theorem | ★ решатель; boost345 имеет, Фибоначчи нет |

**Key lemmas (deep):**

- **`rational_eigenvalue_iff_disc_square`** - ПОЛНЫЙ критерий (⟺): 2×2-матрица имеет рациональное собственное значение ТОГДА И ТОЛЬКО ТОГДА, когда дискриминант — перфект-квадрат, с разрешающей процедурой над Z. Резкий контраст: boost-345 (пифагор) имеет с.з., Фибоначчи (золотое сечение) — НЕТ. Чистая вена A: перфект-квадрат как полная граница Element/role-limit для спектра. _(discriminant, iff, eigenvalue, vein-A, fibonacci)_

**Uniqueness - score 3 (new-framing).** Полный критерий над Q (вена A): рациональное собственное значение ⟺ дискриминант-перфект-квадрат, с решателем; boost-345 имеет с.з., Фибоначчи/золотое — нет.
> _Caveat:_ Критерий «рациональный корень ⟺ квадратный дискриминант» элементарен; вклад — полная (⟺) вена-A формулировка с решателем и резким контрастом, не новый результат.

---

## #228 - `src/foundation/Distinction.v` - score 4 (synthesis+observation)

**Distinction: the primitive of the whole foundation (carries the L3 'classic' axiom)**

- **Topic.** The Distinction type and distinction_of, every prop distinguishes, L1 stability (negative stable), L2 exclusivity, L3 totality, L4 self-grounding (contrapositive), a distinction count (zero/one/two, successor), co-constitution, true/false distinctions, decidability, and the five properties of a distinction.
- **Role.** ROOT of the entire foundation chain (Distinction -> ERR -> SM -> L5). Sole-source of the L3 axiom 'classic' (CLAUDE.md). 53+ files depend on this lineage. Self-contained.
- **Counts.** Qed 3 / Admitted 0 / axioms 1
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ примитив Distinction; положительная/отрицательная стороны. _Roles:_ различение = корневая роль; L1-L4 как роли-свойства различения. _Rules:_ L1_stability; L2_exclusivity; L3_totality; L4_self_grounding. _P4:_ конечный счётчик различений (Element); НЕСЁТ аксиому classic (L3=исключённое третье) — единственный источник; корень всей foundation.
- **Classical counterpart.** Spencer-Brown's 'Laws of Form' (the primitive act of distinction) and the law of excluded middle are the conceptual ancestors; NEW is the formalization of a Distinction primitive carrying the five ToS laws (L1 stability, L2 exclusivity, L3 totality, L4 self-grounding) AND being the sole source of the project's L3 axiom 'classic'.
- **Tags.** foundation, distinction, L1-L4, classic-axiom, root, synthesis+observation

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `Distinction/distinction_of/every_prop_distinguishes` | Definition/Theorem | примитив различения |
| `L1_stability/L1_negative_stable/L2_exclusivity/L3_totality/L4_self_grounding/L4_contrapositive` | Theorem | ★ пять законов L1-L4 как свойства различения |
| `distinction_count/zero_distinctions/one_distinction_exists/two_distinctions_exist/distinction_count_succ/_any/co_constitution` | Definition/Theorem | счётчик различений, со-конституция |
| `true_distinction_positive/_negative/false_distinction_positive/distinction_decidable/distinction_and/distinction_or/five_properties_of_distinction/distinction_theorem_count` | Theorem | ★ разрешимость, пять свойств различения |

**Key lemmas (deep):**

- **`five_properties_of_distinction`** - Корень всей foundation: примитив Distinction несёт пять законов ToS (L1 стабильность, L2 исключительность, L3 тотальность, L4 само-обоснование) как ДОКАЗАННЫЕ свойства. Каждое prop порождает различение (every_prop_distinguishes). Это аналог Core_ERR для физической ветви — отсюда выводятся ERR, SM, L5. Формализация Spencer-Brown в ToS-онтологии. _(distinction, L1-L4, root, spencer-brown)_
- **`L3_totality`** - L3 (тотальность=исключённое третье) — здесь же ИСТОЧНИК аксиомы classic (единственный по CLAUDE.md). Различение исчерпывает (positive ∨ negative), что и есть LEM. Связывает примитив различения с единственной логической аксиомой проекта. _(L3, classic-axiom, excluded-middle)_

**Uniqueness - score 4 (synthesis+observation).** Примитив Distinction — КОРЕНЬ всей foundation: несёт пять законов ToS (L1-L4) как доказанные свойства и является единственным источником аксиомы classic (L3=исключённое третье). 53+ файлов наследуют эту линию.
> _Caveat:_ Идея примитива различения восходит к Spencer-Brown «Laws of Form», LEM классичен; уникальность — в роли корня всей foundation-онтологии и единственного источника L3, не в новом логическом результате.

---

## #229 - `src/foundation/DistinctionProcess.v` - score 3 (new-framing)

**Distinction as process over Q: sharpness, coherence, Born rule as distinction weight (vein C)**

- **Topic.** Distinction sharpness (at 0/1/2, bounded), coherence (positive, plus sharpness), measurement completing (at 9, 99, eventually, concrete), valid/complementary weights, and the Born rule as the distinction weight.
- **Role.** Core process file (in CLAUDE.md key defs: distinction_sharpness, coherence). Vein-C bridge distinction->QM. Self-contained (QArith).
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ острота различения (sharpness); когерентность. _Roles:_ различение = процесс (sharpness+coherence); измерение = роль-завершение. _Rules:_ measurement_eventually_completes; coherence_plus_sharpness; born_rule_is_distinction_weight. _P4:_ каждая стадия остроты конечна (Element); измерение ЗАВЕРШАЕТСЯ как процесс (role-limit); правило Борна = вес различения (вена C).
- **Classical counterpart.** Modelling measurement as a sharpening process and the Born weights as complementary is standard QM intuition; NEW is the vein-C framing that a distinction is a PROCESS (sharpness + coherence) whose measurement eventually completes, with the Born rule as the distinction weight.
- **Tags.** foundation, distinction-process, born-rule, vein-C, new-framing

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `distinction_sharpness/sharpness_0/_1/_2/sharpness_bounded_0/_1/_2/coherence/coherence_at_0/_1/_2/coherence_positive/coherence_plus_sharpness` | Definition/Theorem | ★ острота + когерентность |
| `measurement_complete/measurement_at_9/_99/measurement_eventually_completes/_concrete` | Theorem | ★ измерение завершается (процесс) |
| `valid_weight/complementary_weights/born_rule_is_distinction_weight/distinction_process_summary/_theorem_count` | Theorem | ★ правило Борна = вес различения |

**Key lemmas (deep):**

- **`born_rule_is_distinction_weight`** - Правило Борна отождествлено с ВЕСОМ различения (комплементарные веса): различение есть процесс sharpness+coherence, чьё измерение завершается (measurement_eventually_completes) над Q. Вена C — мост различение→КМ: квантовая вероятность эмерджентна из заострения различения, а не постулат. _(distinction-process, born-rule, measurement, vein-C)_
- **`measurement_eventually_completes`** - Измерение ЗАВЕРШАЕТСЯ как процесс заострения (sharpness→полнота на стадии 9, 99) — вена C: измерение есть приближение-процесс, а не мгновенный коллапс. Конкретно над Q. _(measurement, process, completion, vein-C)_

**Uniqueness - score 3 (new-framing).** Различение как процесс над Q (вена C): sharpness+coherence, измерение завершается, правило Борна = вес различения — квантовая вероятность эмерджентна из заострения различения.
> _Caveat:_ Измерение-как-заострение и комплементарные веса Борна — известная интуиция КМ; вклад — вена-C формализация различение→КМ, не новый результат.

---

## #230 - `src/foundation/DistinctionRepetition.v` - score 2 (methods)

**Distinction repetition over Q: minimal non-repeating depth gives 321, uniquely**

- **Topic.** Repeats-at / no-repetition, SM no repetition, minimal ND, SM is minimal, nontrivial depth, depth-2/3 nontrivial/terminal, the minimal depth-2 is 3, uniqueness 321 (strong), SM total is 6, SM unique minimal, all different, and uniqueness gives generators.
- **Role.** Distinction->SM leaf (321 from minimal distinction). SM-from-distinction OVER-BRANDED. Self-contained.
- **Counts.** Qed 17 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ вложенные различения; глубина; повторение. _Roles:_ минимальное не-повторяющееся различение = роль (321); генераторы из уникальности. _Rules:_ sm_unique_minimal; uniqueness_321; three_gen_from... _P4:_ конечная глубина (Element); 321 из минимального не-повторяющегося различения; SM-from-distinction OVER-BRANDED.
- **Classical counterpart.** No classical counterpart — a ToS argument that the minimal non-repeating nested distinction has depth-2 structure 3-2-1 giving the SM '321', uniquely (SM-from-distinction OVER-BRANDED).
- **Tags.** foundation, distinction, 321, over-branded, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `repeats_at/no_repetition/sm_no_repetition/constant_repeats/primary_no_repetition/is_minimal_nd/sm_is_minimal/nontrivial_at/depth2_nontrivial/depth1_nontrivial/depth3_terminal` | Definition/Theorem | минимальное не-повторяющееся различение |
| `depth2_not_2/depth3_not_2/depth3_ne_depth2/minimal_depth2_is_3/depth2_minimum_is_3/uniqueness_321/_strong/sm_total_is_6/sm_unique_minimal/sm_all_different/sm_depth_order/uniqueness_gives_generators/distinction_repetition_summary/_count` | Theorem | ★ 321 из уникального минимального различения |

**Key lemmas (deep):**

- **`uniqueness_321`** - Минимальное НЕ-повторяющееся вложенное различение глубины-2 даёт структуру 3-2-1 (= SM-калибровка), уникально (uniqueness_321_strong, sm_total_is_6) над Q. SM-from-distinction OVER-BRANDED: конструкция минимальности настроена давать 321, а не выводит SU(3)×SU(2)×U(1) независимо. _(distinction, 321, minimal, over-branded)_

**Uniqueness - score 2 (methods).** Повторение различения над Q: минимальное не-повторяющееся различение глубины-2 даёт 321 уникально, генераторы из уникальности.
> _Caveat:_ Конструкция минимальности настроена на 321; SM-from-distinction OVER-BRANDED, не независимый вывод калибровочной группы.

---

## #231 - `src/foundation/DOFCounting.v` - score 2 (methods)

**DOF counting over Q: sin^2(theta_W)=3/13 etc. as DOF ratios (over-branded)**

- **Topic.** Dimension D, metric/gauge/total DOF (10/3/13), sin^2/kappa/alpha from DOF, sin^2 = 3/13, kappa = 1/10, alpha_EM = 3/130, alpha_inv > 43, sin^2 matches experiment, error < 1 per-mille.
- **Role.** SM-physics leaf (DOF-ratio constants). sin^2(theta_W)=3/13 OVER-BRANDED. Self-contained (QArith).
- **Counts.** Qed 1 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ степени свободы (метрика 10 / калибровка 3 / всего 13). _Roles:_ константы = роли-отношения DOF (sin²θ_W, kappa, alpha). _Rules:_ sin2_is_3_over_13; kappa_is_1_over_10; alpha_EM_is_3_over_130. _P4:_ конечный подсчёт DOF (Element); sin²θ_W=3/13 OVER-BRANDED (древесная оценка ~0.19% от PDG, не предсказание).
- **Classical counterpart.** Writing sin^2(theta_W) and alpha as degree-of-freedom ratios at tree level is a known relation; NEW only as a rational instance — and sin^2(theta_W)=3/13, kappa=1/10, alpha=3/130 are OVER-BRANDED tree estimates.
- **Tags.** foundation, weinberg-angle, 3/13, over-branded, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `D/n_metric/n_gauge/n_total/sin2_from_DOF/kappa_from_DOF/alpha_EM_from_DOF/n_metric_is_10/n_gauge_is_3/n_total_is_13` | Definition/Theorem | DOF 10/3/13 |
| `sin2_is_3_over_13/kappa_is_1_over_10/alpha_EM_is_3_over_130/alpha_EM_inv_gt_43/sin2_match_experiment/error_less_than_one_permille/DOF_counting_synthesis` | Theorem | ★ sin²θ_W=3/13 (OVER-BRANDED) |

**Key lemmas (deep):**

- **`sin2_is_3_over_13`** - sin²θ_W = 3/13 как отношение степеней свободы (метрика-3 / всего-13) над Q, error<1‰ от эксперимента. OVER-BRANDED (явно по аудиту проекта): это древесная оценка ~0.19% от PDG, а не подтверждённое предсказание; caveat это фиксирует. kappa=1/10, alpha=3/130 — там же. _(weinberg-angle, 3/13, dof-counting, over-branded)_

**Uniqueness - score 2 (methods).** Подсчёт DOF над Q: sin²θ_W=3/13, kappa=1/10, alpha=3/130 как отношения степеней свободы (10/3/13).
> _Caveat:_ Запись констант через DOF — известное соотношение; sin²θ_W=3/13 OVER-BRANDED (древесная оценка, не предсказание).

---

## #232 - `src/foundation/DynamicBoundaryDecidable.v` - score 3 (new-framing)

**Dynamic boundary decidable over Q: structured flows decidable, general flows undecidable (vein A)**

- **Topic.** A scale-flow (nondecreasing, bounded-above/unbounded), a flow element vs role-limit, a linear flow (element/role-limit sides, correct), a boundary representation, static/structured-flow decidable, and general-flow undecidable.
- **Role.** Vein-A leaf (the DYNAMIC decidable boundary, with an honest undecidable case). Self-contained (QArith).
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ потоки (scale-flow); ограниченные/неограниченные. _Roles:_ динамическая граница = роль-решатель (поток→Element vs role-limit). _Rules:_ structured_flow_decidable; general_flow_undecidable; flow_element/flow_role_limit. _P4:_ конечные потоки над Q (Element); СТРУКТУРИРОВАННЫЕ потоки решаемы (Element vs role-limit), ОБЩИЕ — честно неразрешимы (вена A, динамическая граница).
- **Classical counterpart.** Deciding whether a bounded monotone sequence converges is constructively non-trivial; NEW is the vein-A framing of a DYNAMIC finitization boundary: structured flows are decidable (element vs role-limit), but general flows are honestly undecidable.
- **Tags.** foundation, dynamic-boundary, decidable, vein-A, new-framing

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `ScaleFlow/nondecreasing/bounded_above/unbounded/flow_element/flow_role_limit/arch_nat/Qle_of_nat_le` | Definition/Theorem | потоки, Element vs role-limit |
| `lin/lin_nondecreasing/lin_element/lin_role_limit/lin_side_element_b/lin_side_correct_element/_role_limit/BoundaryRep` | Definition/Theorem | линейный поток решаем |
| `boundary_decidable/static_value_decidable/structured_flow_decidable/general_flow_undecidable/dynamic_boundary_frontier` | Theorem | ★ структурир. решаемы, ОБЩИЕ неразрешимы |

**Key lemmas (deep):**

- **`general_flow_undecidable`** - ДИНАМИЧЕСКАЯ граница финитизации: структурированные потоки (линейные) РЕШАЕМЫ (Element=ограничен, role-limit=неограничен), но ОБЩИЕ потоки честно НЕРАЗРЕШИМЫ над Q. Расширяет вену A со статических чисел (is_square) на динамические последовательности, с честной фиксацией предела разрешимости. Ср. DynamicBoundaryLPO. _(dynamic-boundary, decidable, undecidable, vein-A)_

**Uniqueness - score 3 (new-framing).** Динамическая граница над Q (вена A): структурированные потоки решаемы (Element vs role-limit), общие — честно неразрешимы. Расширяет статическую границу is_square на последовательности.
> _Caveat:_ Разрешимость сходимости последовательностей конструктивно нетривиальна; вклад — динамическая вена-A граница с честной фиксацией неразрешимости общего случая, не новый результат теории вычислимости.

---

## #233 - `src/foundation/DynamicBoundaryFrontier.v` - score 3 (new-framing)

**Dynamic boundary frontier over Q: the decidable frontier of monotone flows (vein A)**

- **Topic.** A nat-flow (nondecreasing, bounded, eventually-const, monotone), eventually-const bounded, ge-id unbounded, const/id flows, a flow-kind, a decidable side, eventually-const/dominates-id decidable, and general r.e. undecidable.
- **Role.** Vein-A leaf (decidability frontier of flows, the honest boundary). Self-contained.
- **Counts.** Qed 4 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ nat-потоки (eventually-const / dominates-id). _Roles:_ фронтир разрешимости = роль; решаемая сторона vs общий r.e. случай. _Rules:_ ev_const_decidable; dominates_id_decidable; general_re_undecidable. _P4:_ конечные потоки (Element); фронтир: eventually-const/dominates-id РЕШАЕМЫ, общий r.e. — неразрешим (вена A).
- **Classical counterpart.** Constructive frontier of decidability for monotone sequences; NEW is the vein-A framing where eventually-constant / dominates-id flows are decidable but the general r.e. case is undecidable.
- **Tags.** foundation, dynamic-boundary, frontier, vein-A, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `NatFlow/nf_nondecreasing/nf_bounded/nf_eventually_const/nf_mono/ev_const_bounded/ge_id_unbounded/const_flow/const_nondecreasing/const_element/id_flow/id_nondecreasing/id_role_limit` | Definition/Theorem | потоки, const=Element, id=role-limit |
| `FlowKind/decidable_side/ev_const_decidable/dominates_id_decidable/general_re_undecidable/dynamic_boundary_frontier_nat` | Definition/Theorem | ★ фронтир: решаемая сторона vs общий r.e. |

**Key lemmas (deep):**

- **`general_re_undecidable`** - Фронтир разрешимости: eventually-constant и dominates-id потоки РЕШАЕМЫ (Element/role-limit), но общий рекурсивно-перечислимый случай НЕРАЗРЕШИМ над nat. Очерчивает точную границу вены A для динамических потоков — где разрешимость кончается. Пара к DynamicBoundaryDecidable/LPO. _(dynamic-boundary, frontier, undecidable, vein-A)_

**Uniqueness - score 3 (new-framing).** Фронтир динамической границы над nat (вена A): eventually-const/dominates-id потоки решаемы, общий r.e. неразрешим — точная граница разрешимости.
> _Caveat:_ Граница разрешимости r.e. предикатов — классическая вычислимость; вклад — её привязка к вене-A финитизационной границе потоков, не новый результат.

---

## #234 - `src/foundation/DynamicBoundaryLPO.v` - score 3 (new-framing)

**Dynamic boundary is LPO over Q: the finitization frontier equals LPO**

- **Topic.** A nat-flow (nondecreasing, bounded, eventually-const, monotone), LPO, MCT_nat, any-true (monotone, last, spec), an LPO flow, MCT implies LPO and LPO implies MCT, and the boundary frontier is LPO.
- **Role.** Vein-A flagship (the dynamic boundary = LPO, the sharp constructive characterization). Self-contained.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ nat-потоки; LPO; MCT. _Roles:_ динамическая граница = роль, ЭКВИВАЛЕНТНАЯ LPO. _Rules:_ mct_implies_lpo; lpo_implies_mct; boundary_frontier_is_lpo. _P4:_ конечные потоки (Element); ДИНАМИЧЕСКАЯ граница финитизации ⟺ LPO — резкая конструктивная характеризация (вена A).
- **Classical counterpart.** The Limited Principle of Omniscience (LPO) and the Monotone Convergence Theorem are constructive-analysis staples; NEW is the SHARP identification that the dynamic finitization boundary (deciding if a bounded monotone flow is element vs role-limit) IS equivalent to LPO.
- **Tags.** foundation, LPO, dynamic-boundary, MCT, vein-A, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `NatFlow/nf_nondecreasing/nf_bounded/nf_eventually_const/nf_mono/LPO/MCT_nat/any_true/_mono/_last/_spec` | Definition/Theorem | потоки, LPO, MCT, any_true |
| `f_lpo/f_lpo_nondecreasing/_bounded/mct_implies_lpo/lpo_implies_mct/boundary_frontier_is_lpo` | Theorem | ★ граница ⟺ LPO (MCT⟺LPO) |

**Key lemmas (deep):**

- **`boundary_frontier_is_lpo`** - РЕЗКАЯ характеризация: решить, ограниченный монотонный поток есть Element (стабилизируется) или role-limit, ЭКВИВАЛЕНТНО Принципу Ограниченного Всеведения (LPO) — mct_implies_lpo И lpo_implies_mct. Помещает вену A (динамическую границу финитизации) ТОЧНО на конструктивную карту: граница = LPO = (не)разрешимость монотонной сходимости. Самый острый результат вены A в foundation. _(LPO, dynamic-boundary, MCT, vein-A, flagship)_

**Uniqueness - score 3 (new-framing).** Динамическая граница ⟺ LPO над nat (вена A флагман): решить Element-vs-role-limit для ограниченного монотонного потока ЭКВИВАЛЕНТНО LPO (MCT⟺LPO). Точная конструктивная локализация границы финитизации.
> _Caveat:_ LPO и MCT — классика конструктивного анализа; уникальность — в отождествлении динамической финитизационной границы проекта с LPO, не в новом конструктивном принципе.

---

## #235 - `src/foundation/DynamizedGaugeHierarchy.v` - score 2 (methods)

**Dynamized gauge hierarchy over Q: gauge is an element-finite flow**

- **Topic.** Gauge roles/generators, gauge terminates, is-element-finite, gauge bounded, gauge not monotone, total roles/generators, a gauge flux that telescopes, and the flux total.
- **Role.** Distinction->SM leaf (gauge hierarchy as element-finite flow). SM-from-distinction OVER-BRANDED. Self-contained (QArith).
- **Counts.** Qed 1 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ калибровочная иерархия (роли/генераторы); поток flux. _Roles:_ калибровка = роль-поток (терминирующий, ограниченный = Element). _Rules:_ gauge_is_element_finite; gauge_flux_telescopes; gauge_terminates. _P4:_ конечная калибровочная иерархия (Element); калибровка = element-finite поток (терминирует); SM-framing OVER-BRANDED.
- **Classical counterpart.** No classical counterpart — a ToS argument that the gauge hierarchy is an element-finite (terminating, bounded) flow whose flux telescopes (SM-from-distinction OVER-BRANDED).
- **Tags.** foundation, gauge-hierarchy, over-branded, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `gauge_roles/gauge_gens/gauge_terminates/is_element_finite/gauge_is_element_finite/gauge_bounded/gauge_not_monotone` | Definition/Theorem | ★ калибровка = element-finite поток |
| `gauge_total_roles/gauge_total_gens/gauge_flux/gauge_flux_telescopes/gauge_flux_total/dynamized_gauge_hierarchy` | Theorem | поток flux телескопирует |

**Key lemmas (deep):**

- **`gauge_is_element_finite`** - Калибровочная иерархия — element-finite поток (терминирует, ограничен), её flux телескопирует над Q. Применяет вену-A классификацию потоков (Element-finite) к калибровке. SM-from-distinction OVER-BRANDED. _(gauge-hierarchy, element-finite, telescopes, over-branded)_

**Uniqueness - score 2 (methods).** Динамизированная калибровочная иерархия над Q: калибровка = element-finite поток (терминирует, ограничен), flux телескопирует.
> _Caveat:_ Внутренняя ToS-конструкция; SM-from-distinction OVER-BRANDED, не вывод калибровки.

---

## #236 - `src/foundation/EinsteinRuleElementCoupling.v` - score 2 (methods)

**Einstein rule-element coupling over Q: conservation from Bianchi**

- **Topic.** A symmetric 2-tensor, Einstein preserves symmetry, a field with divergence and scaling, divergence scales, conservation from Bianchi, and Einstein is a rule-element coupling.
- **Role.** Gravity leaf (Einstein equation as ERR coupling). Self-contained.
- **Counts.** Qed 2 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ симметричный 2-тензор; поле; дивергенция. _Roles:_ уравнение Эйнштейна = роль-связь правило↔элемент; сохранение из Бианки. _Rules:_ einstein_preserves_symmetry; conservation_from_bianchi; einstein_is_rule_element_coupling. _P4:_ конечные тензоры (Element); сохранение из тождества Бианки (∂∂=0); Эйнштейн как ERR-связь.
- **Classical counterpart.** That the Einstein tensor is symmetric and divergence-free (conservation from the Bianchi identity) is standard GR; NEW only as the ToS framing of Einstein's equation as a rule-element coupling.
- **Tags.** foundation, einstein, gravity, ERR, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `Tensor2/symmetric/einstein_preserves_symmetry/Field/ddiv/scale/ddiv_scale` | Definition/Theorem | тензор, дивергенция |
| `conservation_from_bianchi/einstein_is_rule_element_coupling` | Theorem | ★ сохранение из Бианки; Эйнштейн = ERR-связь |

**Key lemmas (deep):**

- **`conservation_from_bianchi`** - Сохранение (дивергенция-ноль тензора Эйнштейна) следует из тождества Бианки (∂∂=0), Эйнштейн переобрамлён как связь правило↔элемент над Q. Стандартная ОТО (ср. BianchiFromBoundary), привязанная к ERR. _(einstein, bianchi, conservation, ERR)_

**Uniqueness - score 2 (methods).** Эйнштейн как связь правило-элемент над Q: симметрия сохраняется, сохранение из Бианки.
> _Caveat:_ Симметрия и дивергенция-ноль тензора Эйнштейна — стандартная ОТО; вклад — ERR-переобрамление, не новый результат.

---

## #237 - `src/foundation/EnergyFromContent.v` - score 1 (exposition)

**Energy from content over Q: trace = eigenvalue sum, content determines energy**

- **Topic.** A 2x2 matrix (trace, determinant), hydrogen/helium kinetic matrices and energies (diagonal, negative), distinct energies, helium lower, trace = eigenvalue sum, determinant = eigenvalue product, content determines trace, and various trace identities.
- **Role.** E/R/R atomic-energy leaf (energy from matrix content). Self-contained (QArith).
- **Counts.** Qed 2 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ 2×2 матрицы (H/He); след/детерминант. _Roles:_ энергия = роль из содержания матрицы (след=сумма с.з.). _Rules:_ trace_is_eigenvalue_sum; content_determines_trace; helium_lower. _P4:_ конечные 2×2 матрицы над Q (Element); энергия из следа (содержания матрицы).
- **Classical counterpart.** That a diagonal Hamiltonian's trace is the eigenvalue sum and the determinant the product (energy from the matrix content) is elementary linear algebra; here a Q instance for H/He.
- **Tags.** foundation, energy, trace, err, exposition

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `Mat2/trace_M/det_M/T_hydrogen/_trace/_det/E_hydrogen/_is_diagonal/_negative/T_helium/E_helium/_trace/_det/_is_diagonal/_negative/energies_distinct/helium_lower` | Definition/Theorem | H/He энергии из следа |
| `trace_is_eigenvalue_sum/det_is_eigenvalue_product/content_determines_trace/T_zero/zero_trace/zero_det/T_identity/identity_trace/_det/T_traceless/traceless_trace/trace_additive_diag/distinct_diagonal_distinct_trace` | Theorem | ★ след=сумма с.з., содержание определяет след |

**Key lemmas (deep):**

- **`content_determines_trace`** - Энергия определяется СОДЕРЖАНИЕМ матрицы: след = сумма собственных значений, детерминант = произведение, He ниже H над Q — элементарная линалгебра в E/R/R-форме (энергия из содержания, а не из внешнего фона). _(energy, trace, content, err)_

**Uniqueness - score 1 (exposition).** Энергия из содержания над Q: след=сумма с.з., детерминант=произведение, He ниже H.
> _Caveat:_ След=сумма собственных значений — элементарная линалгебра; Q-инстанс H/He в E/R/R-форме без нового содержания.

---

## #238 - `src/foundation/EnergySynthesis.v` - score 1 (exposition)

**Energy synthesis over Q: energy from trace, He below H**

- **Topic.** A 2x2 energy matrix, e-trace, energy from content, energy from trace, distinct energies, zero content = zero energy, trace additive, energy scales, H/He energies, He lower than H, a unique ground state, and trace invariant.
- **Role.** Synthesis leaf (energy from trace). Self-contained (QArith).
- **Counts.** Qed 1 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ энергетическая матрица; след. _Roles:_ узел-синтез: энергия = след содержания. _Rules:_ synth_energy_from_trace; synth_He_lower_than_H; synth_trace_invariant_diag. _P4:_ конечные матрицы над Q (Element); энергия из следа, инвариантного к диагонали.
- **Classical counterpart.** Energy as the trace of a content matrix (additive, scaling, He below H, trace invariant) is elementary; here a synthesis over Q.
- **Tags.** foundation, synthesis, energy, exposition

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `EMat2/e_trace/E_from_content/synth_energy_from_trace/synth_distinct_energies/synth_zero_content_zero_energy/e_add/synth_trace_additive/e_scale/synth_energy_scales` | Definition/Theorem | энергия из следа, аддитивность |
| `synth_H/synth_He/synth_H_energy/synth_He_energy/synth_He_lower_than_H/synth_ground_state_unique/synth_grand_energy/synth_trace_invariant_diag` | Theorem | ★ He ниже H, след инвариантен |

**Key lemmas (deep):**

- **`synth_He_lower_than_H`** - Узел-синтез энергии-из-следа: He ниже H, след аддитивен/масштабируется/инвариантен над Q. Агрегатор EnergyFromContent. Уникальности нет. _(synthesis, energy, trace)_

**Uniqueness - score 1 (exposition).** Синтез энергии над Q: энергия=след содержания (аддитивна, масштабируется), He ниже H.
> _Caveat:_ Узел-синтез энергии-из-следа; элементарная линалгебра, собственного результата нет.

---

## #239 - `src/foundation/EntropyExact.v` - score 1 (exposition)

**Entropy exact over Q: Ising microstates double (2^n)**

- **Topic.** Powers of two over Q, Ising counts 1-5, Ising doubles, step counts, and positivity.
- **Role.** Thermodynamic leaf (exact entropy = bit count). Self-contained (QArith).
- **Counts.** Qed 0 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ Изинг-микросостояния; степени двойки. _Roles:_ энтропия = роль-счёт (удваивается на спин). _Rules:_ ising_doubles; pow_Q_positive. _P4:_ конечные степени двойки над Q (Element); энтропия = точный счёт (2^n).
- **Classical counterpart.** That an Ising/binary system's microstate count doubles per spin (entropy = bit count, 2^n) is elementary statistical mechanics; here a tiny Q instance.
- **Tags.** foundation, entropy, ising, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `two_pow_Q/ising_1/_2/_3/_4/_5/ising_doubles/step_1/_2/_3/_4/_5/pow_Q_positive_1/_5/_3` | Definition/Theorem | ★ Изинг удваивается (2^n) |

**Key lemmas (deep):**

- **`ising_doubles`** - Число микросостояний Изинга удваивается на спин (2^n) над Q — энтропия как точный счёт (ср. Binarity). Элементарно, 0 Qed (через определения/примеры). Уникальности нет. _(entropy, ising, 2^n)_

**Uniqueness - score 1 (exposition).** Точная энтропия над Q: Изинг-микросостояния удваиваются на спин (2^n).
> _Caveat:_ Энтропия=счёт битов (2^n) элементарна; иллюстративный файл (0 Qed).

---

## #240 - `src/foundation/EquipartitionBedrock.v` - score 2 (methods)

**Equipartition bedrock over Q: equipartition rests on honest posits shadowing the laws**

- **Topic.** An equal-pair uniform, sectors partition, an indistinguishability posit, an equivariance posit, indifference opened/grounded (two parts), sectors/locality posits, reference opened/grounded, an ERR-law atom, equivariance shadows L2, locality shadows P1, and atoms are framework-affine.
- **Role.** Honesty/bedrock leaf for equipartition (explicit posits). Self-contained.
- **Counts.** Qed 1 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ секторы; постулаты (неразличимость, эквивариантность). _Roles:_ равнораспределение = роль на ЯВНЫХ постулатах, «тенящих» L1/L2/P1. _Rules:_ indistinguishability_posit; equivariance_shadows_L2; locality_shadows_P1. _P4:_ конечные секторы (Element); ЧЕСТНО: равнораспределение опирается на явные постулаты (тени законов), не чистый вывод.
- **Classical counterpart.** The principle of indifference / equipartition (uniform over indistinguishable sectors) is classical; NEW is the HONEST framing that it rests on explicit posits (indistinguishability, equivariance) that 'shadow' L1/L2/P1.
- **Tags.** foundation, honesty, equipartition, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `equal_pair_uniform/sectors_partition/indistinguishability_posit/equivariance_posit/indifference_opened/_grounded/_two_parts/sectors_posit/locality_posit/reference_opened/_grounded/_two_parts` | Definition/Theorem | постулаты равнораспределения |
| `ERRLaw/Atom/atom_shadows/equivariance_shadows_L2/locality_shadows_P1/atoms_are_framework_affine/equipartition_bedrock` | Definition/Theorem | ★ постулаты «тенят» L2/P1 (честно) |

**Key lemmas (deep):**

- **`equivariance_shadows_L2`** - ЧЕСТНО: равнораспределение/принцип безразличия опирается на ЯВНЫЕ постулаты (неразличимость, эквивариантность), которые «тенят» (shadow) законы L2/P1 — не выводятся, а постулируются как framework-affine атомы над Q. Образец калибровки: вскрывает, на чём держится равнораспределение. _(honesty, equipartition, posits, shadows-laws)_

**Uniqueness - score 2 (methods).** Основание равнораспределения над Q: равнораспределение опирается на явные постулаты (неразличимость/эквивариантность), «тенящие» L2/P1 — честная фиксация оснований.
> _Caveat:_ Принцип безразличия классичен; ценность — честное вскрытие постулатов (тени законов), не новый результат.

---

## #241 - `src/foundation/EquipartitionRule.v` - score 2 (methods)

**Equipartition rule over Q: kappa forced by indifference (two honest posits)**

- **Topic.** Equipartition quantum, weight forced, equipartition normalizes, kappa is quantum, sin^2 is a multiple, metric-4 nonzero, kappa forced by indifference, an indifference posit and a reference posit, and the DOF rule just/grounded (two parts).
- **Role.** Honesty leaf for the equipartition/DOF rule (two posits). sin^2 context OVER-BRANDED. Self-contained.
- **Counts.** Qed 2 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ квант равнораспределения; вес; kappa. _Roles:_ правило DOF = роль на ДВУХ постулатах (безразличие, опорная точка). _Rules:_ kappa_forced_by_indifference; dof_rule_two_parts; weight_forced. _P4:_ конечные веса (Element); ЧЕСТНО: правило DOF опирается на 2 постулата; sin² контекст OVER-BRANDED.
- **Classical counterpart.** Equipartition fixing a uniform quantum weight (and kappa, sin^2 multiples) is the principle of indifference applied; NEW is the HONEST framing that the DOF rule rests on two posits (indifference, reference).
- **Tags.** foundation, honesty, equipartition, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `from/equipart_quantum/weight_forced/equipart_quantum_normalizes/kappa_is_quantum/sin2w_is_multiple/metric4_nonzero/kappa_forced_by_indifference` | Definition/Theorem | ★ kappa вынужден безразличием |
| `indifference_posit/reference_posit/dof_rule_just/dof_rule_grounded/dof_rule_two_parts/equipartition_rule_structure` | Theorem | ★ правило DOF на 2 постулатах (честно) |

**Key lemmas (deep):**

- **`kappa_forced_by_indifference`** - kappa вынужден принципом безразличия, но правило DOF ЧЕСТНО опирается на ДВА явных постулата (indifference + reference) над Q. Калибровка: вскрывает основания DOF-правила (продолжение EquipartitionBedrock). sin²-контекст связан с OVER-BRANDED 3/13. _(honesty, equipartition, kappa, posits)_

**Uniqueness - score 2 (methods).** Правило равнораспределения над Q: kappa вынужден безразличием, но опирается на 2 явных постулата (безразличие+опора) — честная фиксация.
> _Caveat:_ Принцип безразличия классичен; ценность — честные 2 постулата DOF-правила; sin²-контекст OVER-BRANDED.

---

## #242 - `src/foundation/ERRAutomorphism.v` - score 2 (methods)

**ERR automorphism over Q: ERR automorphisms = gauge generators**

- **Topic.** An ERR automorphism, identity (is id), composition (map, id-left/right, associative), inverse (inv-left), automorphism generator counts (1/2/3 gen, U1/SM total), and an automorphism synthesis.
- **Role.** ERR-machinery leaf (automorphisms = gauge). SM-from-distinction OVER-BRANDED. Self-contained.
- **Counts.** Qed 2 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ ERR-автоморфизмы; генераторы. _Roles:_ автоморфизм ERR = роль-калибровка (генераторы SM). _Rules:_ err_aut_compose; aut_compose_assoc; sm_aut_total. _P4:_ конечная группа автоморфизмов (Element); ERR-автоморфизмы = калибровочные генераторы; SM-framing OVER-BRANDED.
- **Classical counterpart.** That automorphisms of a structure form a group (identity, composition, associativity, inverse) and gauge symmetries are automorphisms is standard; NEW is the ToS framing that the ERR automorphisms generate the SM gauge generators (SM-from-distinction OVER-BRANDED).
- **Tags.** foundation, ERR, automorphism, over-branded, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `ERRAutomorphism/err_aut_id/_is_id/err_aut_compose/aut_compose_map/aut_id_left/_right/aut_compose_assoc/err_aut_inv/aut_inv_left` | Definition/Theorem | ★ автоморфизмы образуют группу |
| `aut_generator_count/aut_1_gen/u1_aut_generators/aut_2_gen/aut_3_gen/sm_aut_total/err_automorphism_synthesis` | Theorem | генераторы = SM |

**Key lemmas (deep):**

- **`sm_aut_total`** - ERR-автоморфизмы образуют группу (id/композиция/ассоциативность/обратный) и их генераторы дают SM-калибровку над Q. Содержательная привязка «калибровка=автоморфизм ERR», но SM-from-distinction OVER-BRANDED (число генераторов настроено на SM). _(ERR, automorphism, gauge, over-branded)_

**Uniqueness - score 2 (methods).** ERR-автоморфизмы над Q: образуют группу, генераторы = SM-калибровка (калибровка=автоморфизм ERR).
> _Caveat:_ Автоморфизмы как группа и калибровка-автоморфизм стандартны; SM-from-distinction OVER-BRANDED.

---

## #243 - `src/foundation/ERRBijections.v` - score 2 (new-framing)

**ERR bijections over Q: physics/compression/observer all well-formed ERR**

- **Topic.** Physics-to-ERR (well-formed, has all three), sound/QM well-formed ERR, compression as physics (well-formed), DFT is DFT, a gamma process (zero preserves, one kills, half partial), decoherence = damping, observer/compressor keep, observer = compressor (discarded modes), and four bijections.
- **Role.** ERR-machinery leaf (cross-domain ERR bijections). Self-contained.
- **Counts.** Qed 2 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ системы (физика/звук/сжатие/DFT); ERR-структура. _Roles:_ узел-биекция: разные системы = одна well-formed ERR. _Rules:_ physics_to_err_well_formed; decoherence_eq_damping; observer_eq_compressor. _P4:_ конечные системы (Element); физика/сжатие/наблюдатель — все well-formed ERR (четыре биекции).
- **Classical counterpart.** No classical counterpart — a ToS file showing several systems (physics, sound, compression, DFT, decoherence/damping, observer/compressor) are all well-formed ERR, via four bijections.
- **Tags.** foundation, ERR, bijections, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `physics_to_err/_well_formed/physics_has_all_three/sound_is_well_formed_err/qm_is_well_formed_err/compression_as_physics/compression_is_physical_process/_is_well_formed/dft_is_dft` | Theorem | системы как well-formed ERR |
| `gamma_process/gamma_zero_preserves/_one_kills/_half_partial/decoherence_eq_damping/observer_keeps/compressor_keeps/observer_eq_compressor/discarded_modes/observer_discards_eq_compressor_discards/four_bijections` | Theorem | ★ декогеренция=затухание, наблюдатель=компрессор |

**Key lemmas (deep):**

- **`four_bijections`** - Четыре биекции, показывающие, что физика/сжатие/наблюдатель/декогеренция суть одна well-formed ERR-структура над Q (decoherence=damping, observer=compressor). Объединяет разнодоменные явления под ERR. Связь с crown/CompressionIsPhysics, decoherence/. _(ERR, bijections, cross-domain)_

**Uniqueness - score 2 (new-framing).** Биекции ERR над Q: физика/звук/сжатие/DFT/наблюдатель — все well-formed ERR; декогеренция=затухание, наблюдатель=компрессор (четыре биекции).
> _Caveat:_ Кросс-доменные аналогии (наблюдатель=компрессор и т.п.) — переобрамления; вклад — их объединение под ERR, не новый результат.

---

## #244 - `src/foundation/ERRCategory.v` - score 2 (methods)

**ERR category over Q: ERR objects and morphisms form a category**

- **Topic.** ERR objects (primary/ternary/reflexive), morphisms (identity, map, composition, self-compose), block morphisms (bid is id, bcompose, associative, id-left/right), and object sizes/role-counts.
- **Role.** ERR-machinery leaf (the ERR category). Parallels category/ cluster. Self-contained.
- **Counts.** Qed 1 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ ERR-объекты (primary/ternary/reflexive); морфизмы. _Roles:_ категория = роль-каркас ERR-объектов. _Rules:_ err_bcompose_assoc; err_bid_left/right; err_category_synthesis. _P4:_ конечные ERR-объекты (Element); образуют категорию (id/композиция/ассоциативность).
- **Classical counterpart.** That objects with identity/composition/associativity form a category is standard; NEW only as the ToS instance where ERR objects (primary/ternary/reflexive) with their morphisms form a category.
- **Tags.** foundation, ERR, category, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `ERRObject/err_primary/_ternary/_reflexive/ERRMorphism/err_id/_id_map/err_compose/err_self_compose` | Definition/Theorem | ERR-объекты и морфизмы |
| `ERRBMorphism/err_bid/_is_id/err_bcompose/_map/_assoc/err_bid_left/_right/err_primary_size/_nroles/err_ternary_size/_nroles/err_reflexive_size/_nroles/err_category_synthesis` | Definition/Theorem | ★ блок-морфизмы: категориальные законы |

**Key lemmas (deep):**

- **`err_bcompose_assoc`** - ERR-объекты (primary/ternary/reflexive) с морфизмами образуют категорию (id/композиция/ассоциативность) над Q — категориальная структура ERR-триады. Стандартная категория, ERR-инстанс (ср. category/ кластер). _(ERR, category, morphism)_

**Uniqueness - score 2 (methods).** Категория ERR над Q: ERR-объекты (primary/ternary/reflexive) с морфизмами образуют категорию (id/композиция/ассоциативность).
> _Caveat:_ Категориальные законы стандартны; вклад — ERR-инстанс категории, не новый результат.

---

## #245 - `src/foundation/ERRComputationBridge.v` - score 2 (methods)

**ERR computation bridge over Q: ERR = Wilson, positive gap**

- **Topic.** ERR is Wilson (matches at 1/2), an observable count, a chain length starting at ERR, a gap from ERR (positive, sub-1), and sin^2 from ERR (positive, sub-half).
- **Role.** ERR-machinery leaf (ERR<->Wilson computation, with ERRWilsonBridge). Self-contained.
- **Counts.** Qed 2 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ ERR-наблюдаемая; Wilson-действие; зазор. _Roles:_ ERR = роль-вычисление (= Wilson); зазор из ERR. _Rules:_ err_is_wilson; gap_from_err; gap_positive. _P4:_ конечная ERR-цепь над Q (Element); ERR=Wilson, зазор положителен (<1).
- **Classical counterpart.** No classical counterpart — a ToS bridge equating the ERR observable to the Wilson action, yielding a positive sub-1 gap and a sub-half sin^2.
- **Tags.** foundation, ERR, wilson, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `err_is_wilson/err_matches_wilson_1/_2/observable_count/chain_length/chain_starts_at_err` | Theorem | ERR=Wilson, цепь |
| `gap_from_err/gap_positive/gap_less_than_1/sin2_from_err/sin2_positive/sin2_less_than_half/err_computation_summary/_count` | Theorem | ★ зазор из ERR положителен (<1) |

**Key lemmas (deep):**

- **`gap_from_err`** - ERR-наблюдаемая отождествлена с Wilson-действием, давая положительный зазор (<1) над Q — мост ERR↔решёточная калибровка (ср. ERRWilsonBridge, gauge/). Связь онтологии ERR с вычислимым масс-зазором. _(ERR, wilson, gap)_

**Uniqueness - score 2 (methods).** Вычислительный мост ERR над Q: ERR=Wilson, положительный зазор (<1), sin² из ERR (<½).
> _Caveat:_ Внутренний ERR↔Wilson мост; вклад — привязка ERR к решёточному зазору, не новый результат.

---

## #246 - `src/foundation/ERRFromDistinction.v` - score 3 (new-framing)

**ERR from distinction over Q: the triad from a distinction (SM roles over-branded)**

- **Topic.** ERR element/role/rule counts, a distinction has two elements/two roles, minimum two roles, L1 for elements / L2 for roles / L3 for completeness / L4 rules ground roles / L5 ERR hierarchy, extended/SM roles, SU2/SU3 generators from distinction, a complete foundation, and ERR well-formed/balanced.
- **Role.** ERR-machinery core (ERR derived from distinction). SM-roles OVER-BRANDED. Self-contained.
- **Counts.** Qed 2 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ ERR-счётчики; два элемента/две роли различения. _Roles:_ ERR-триада = роль из различения; L1-L5 размечают компоненты ERR. _Rules:_ L1_for_elements; L4_rules_ground_roles; su2_from_distinction. _P4:_ конечная ERR-триада (Element); ERR выведена из различения, L1-L5 размечают; SM-роли OVER-BRANDED.
- **Classical counterpart.** No classical counterpart — a ToS file deriving the ERR (Elements/Roles/Rules) triad from a distinction, with the SM roles/SU2/SU3 generators (SM-from-distinction OVER-BRANDED).
- **Tags.** foundation, ERR, distinction, over-branded, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `err_element_count/err_role_count/err_rule_count/err_elements/distinction_has_two_elements/_two_roles/minimum_two_roles/L1_for_elements/L2_for_roles/L3_for_completeness/L4_rules_ground_roles/L5_err_hierarchy` | Definition/Theorem | ★ ERR из различения, L1-L5 разметка |
| `extended_roles/sm_roles/su2_from_distinction/su2_generators/su3_generators/complete_foundation/err_well_formed/_balanced/err_complete_spec/foundation_summary/err_distinction_theorem_count` | Theorem | SM-роли, SU2/SU3 генераторы |

**Key lemmas (deep):**

- **`L5_err_hierarchy`** - ERR-триада (Elements/Roles/Rules) выводится из различения, с законами L1-L5, размечающими её компоненты (L1→элементы, L2→роли, L3→полнота, L4→правила обосновывают роли, L5→иерархия) над Q. Содержательное ядро «ERR из различения» (ср. Distinction #228). SM-роли (SU2/SU3 генераторы) OVER-BRANDED. _(ERR, distinction, L1-L5, over-branded)_

**Uniqueness - score 3 (new-framing).** ERR из различения над Q: триада Elements/Roles/Rules выведена из различения, законы L1-L5 размечают её компоненты — ядро ERR-онтологии.
> _Caveat:_ Разметка ERR законами L1-L5 — содержательное ядро; SM-роли (SU2/SU3 из различения) OVER-BRANDED, не вывод.

---

## #247 - `src/foundation/ERRGaugeFunctorSynthesis.v` - score 2 (methods)

**ERR gauge-functor synthesis over Q: distinction -> ERR, automorphism = gauge**

- **Topic.** Nested-distinction-to-ERR (primary/ternary/reflexive), automorphism = gauge, SM generators via automorphism, distinction is a category, gauge is automorphism, and generators match the SM.
- **Role.** ERR-machinery synthesis (distinction->ERR->gauge). SM-from-distinction OVER-BRANDED. Self-contained.
- **Counts.** Qed 5 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ вложенное различение; ERR; автоморфизмы. _Roles:_ узел-синтез: различение→ERR, автоморфизм=калибровка. _Rules:_ aut_eq_gauge; gauge_is_automorphism; generators_match_sm. _P4:_ конечная конструкция (Element); различение→ERR→калибровка; SM-from-distinction OVER-BRANDED.
- **Classical counterpart.** That gauge symmetry is the automorphism group of a structure is standard; NEW only as a synthesis mapping nested distinction -> ERR and automorphism -> gauge generators (SM-from-distinction OVER-BRANDED).
- **Tags.** foundation, ERR, gauge, over-branded, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `nd_to_err/nd_to_err_primary/_ternary/_reflexive/aut_eq_gauge/sm_generators_via_aut` | Definition/Theorem | различение→ERR, автоморфизм=калибровка |
| `distinction_is_category/gauge_is_automorphism/generators_match_sm/err_gauge_synthesis` | Theorem | ★ калибровка=автоморфизм, генераторы=SM |

**Key lemmas (deep):**

- **`gauge_is_automorphism`** - Синтез: вложенное различение→ERR-триада, калибровка=группа автоморфизмов, генераторы соответствуют SM над Q. Объединяет ERRFromDistinction+ERRAutomorphism. SM-from-distinction OVER-BRANDED. _(ERR, gauge, automorphism, over-branded)_

**Uniqueness - score 2 (methods).** Синтез ERR-калибровки над Q: различение→ERR, калибровка=автоморфизм, генераторы=SM.
> _Caveat:_ Калибровка=автоморфизм стандартно; SM-from-distinction OVER-BRANDED, не вывод.

---

## #248 - `src/foundation/ERRKnowledgeBase.v` - score 3 (new-framing)

**ERR knowledge base over Q: status logic, well-formedness, logic-math-physics chain**

- **Topic.** No-rules-no-roles, invalid has no weight, generative order, role-type/unique-status, deterministic candidate/invalid, weight-update rules, status preservation, system levels (logic/generation/concrete), constitution from previous, L2/L3 well-formedness, ERR aspects (roundtrip), number contains predecessors, proper-system vs mere-collection, and the logic-math-physics chain.
- **Role.** ERR-machinery hub (the largest ERR file, Q11). Self-contained.
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ ERR-статусы; уровни системы (logic/math/physics). _Roles:_ база знаний = роль (логика статусов ERR, иерархия конституций). _Rules:_ constitution_from_previous; logic_math_physics_chain; L2_L3_ground_well_formedness. _P4:_ конечная база статусов (Element); трёхуровневая цепь логика→математика→физика конституций.
- **Classical counterpart.** No classical counterpart — a ToS knowledge-base file laying out the ERR status logic, the L2/L3 well-formedness, and a three-level (logic/math/physics) constitution chain.
- **Tags.** foundation, ERR, logic-math-physics, new-framing

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `no_rules_no_roles/invalid_has_no_weight/generative_order/RoleType/role_type_of/is_unique_status/primary_is_unique/candidate_is_deterministic/has_sufficient_reason_to_update/higher_weight_updates/status_preservation` | Definition/Theorem | логика статусов, обновление весов |
| `SystemLevel/level_0_logic/_1_generation/_2_concrete/constitution_from_previous/L2_exclusive/L3_exhaustive/L2_L3_ground_well_formedness/three_level_hierarchy` | Definition/Theorem | ★ уровни системы, L2/L3 обосновывают well-formedness |
| `ERRAspect/category_to_aspect/aspect_roundtrip/proper_system/collection_no_function/system_has_function/Mathematics_Level/Physics_Level/math_constitution_is_logic/physics_constitution_is_math/logic_math_physics_chain/err_knowledge_base_full_synthesis` | Definition/Theorem | ★ цепь логика→математика→физика |

**Key lemmas (deep):**

- **`logic_math_physics_chain`** - Трёхуровневая цепь конституций: физика конституируется математикой, математика — логикой (constitution_from_previous), плюс логика статусов ERR (primary уникален, обновление весов) над Q. Самый крупный ERR-файл; систематизирует, как уровни системы обосновывают друг друга. proper_system vs mere_collection — система требует функции. _(ERR, logic-math-physics, constitution, knowledge-base)_

**Uniqueness - score 3 (new-framing).** База знаний ERR над Q: логика статусов (primary уникален, обновление весов), L2/L3 обосновывают well-formedness, цепь конституций логика→математика→физика.
> _Caveat:_ Иерархия конституций — внутренняя ToS-онтология; систематизация, не новый формальный результат.

---

## #249 - `src/foundation/ERRLawsCorrespondence.v` - score 3 (new-framing)

**ERR-laws correspondence over Q: a bijection ERR <-> laws (L4/L5 complementarity)**

- **Topic.** An ERR-law type, category<->law roundtrips, an ERR-law bijection, L1 provides identity/reflexivity, L4 provides justification, L5 provides structure, fully-determinate, roles-no-rules indeterminate, rules-no-roles pointless, and L4/L5 complementarity.
- **Role.** ERR-machinery leaf (ERR<->laws bijection). Self-contained.
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ ERR-компоненты; законы L1/L4/L5. _Roles:_ соответствие = роль-биекция ERR↔законы; L4/L5 комплементарны. _Rules:_ err_law_bijection; L4_L5_complementarity; roles_no_rules_indeterminate. _P4:_ конечная биекция (Element); ERR↔законы взаимно-однозначно; роли без правил неопределённы, правила без ролей бессмысленны.
- **Classical counterpart.** No classical counterpart — a ToS bijection between ERR components/aspects and the laws (L1 identity, L4 justification, L5 structure), with roles-without-rules indeterminate and rules-without-roles pointless.
- **Tags.** foundation, ERR, laws, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `ERRLaw/category_law/law_category/category_law_roundtrip/law_category_roundtrip/err_law_bijection` | Definition/Theorem | ★ биекция ERR↔законы |
| `L1_provides_identity/L1_reflexivity/L4_provides_justification/L4_justification/L5_provides_structure/L5_structure/is_fully_determinate/roles_no_rules/_indeterminate/rules_no_roles/_pointless/L4_L5_complementarity/err_laws_correspondence_synthesis` | Theorem | ★ L1/L4/L5 ↔ ERR; L4/L5 комплементарны |

**Key lemmas (deep):**

- **`err_law_bijection`** - Взаимно-однозначное соответствие между компонентами ERR и законами: L1→тождество, L4→обоснование, L5→структура над Q. Роли без правил НЕОПРЕДЕЛЁННЫ, правила без ролей БЕССМЫСЛЕННЫ (L4/L5 комплементарны) — содержательно связывает триаду ERR с законами как единую структуру. _(ERR, laws, bijection, L4-L5)_

**Uniqueness - score 3 (new-framing).** Соответствие ERR↔законы над Q: биекция (L1→тождество, L4→обоснование, L5→структура), роли-без-правил неопределённы, правила-без-ролей бессмысленны (L4/L5 комплементарны).
> _Caveat:_ Внутренняя ToS-онтология; систематизация связи ERR↔законы, не новый формальный результат.

---

## #250 - `src/foundation/ERRProcess.v` - score 2 (methods)

**ERR process over Q: integrity gate assigns weight, blocks self-reference**

- **Topic.** Gate signals, raw scores, a status, an integrity gate (compute, valid), a weight, an ERR entity, valid signals/scores/gate (passes, positive weight), invalid (fails, zero weight), a zero-gate law, self-ref fails (zero weight), order-violation fails, and valid entity is a candidate.
- **Role.** ERR-machinery leaf (the integrity-gate process, vein-E-adjacent: self-ref blocked). Self-contained.
- **Counts.** Qed 2 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ ERR-сущность; сигналы/оценки; вес. _Roles:_ интегрити-гейт = роль-вентиль (валидное→вес>0, само-ссылка→0). _Rules:_ valid_gate_passes; self_ref_zero_weight; order_violation_fails. _P4:_ конечный вентиль (Element); валидная ERR→положительный вес, само-ссылка/нарушение порядка→0 (вена-E-смежно).
- **Classical counterpart.** No classical counterpart — a ToS integrity-gate process that assigns a weight to an ERR entity (valid passes/positive weight, invalid/self-ref/order-violation fail with zero weight).
- **Tags.** foundation, ERR, self-reference, vein-E, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `GateSignals/RawScores/Status/IntegrityGate/compute_gate/gate_valid/compute_weight/ERREntity/valid_signals/_scores/_gate/_gate_passes/valid_weight/_positive/_value` | Definition/Theorem | ★ валидное проходит (вес>0) |
| `invalid_signals/_gate/_gate_fails/_weight/_weight_zero/zero_gate_law/self_ref_signals/_fails/_zero_weight/order_violation_signals/_fails/process_entity/valid_entity_is_candidate/invalid_entity_is_invalid/err_process_synthesis` | Theorem | ★ само-ссылка/нарушение → вес 0 |

**Key lemmas (deep):**

- **`self_ref_zero_weight`** - Интегрити-гейт присваивает вес ERR-сущности: валидное проходит с положительным весом, но САМО-ССЫЛКА и нарушение порядка проваливаются с НУЛЕВЫМ весом над Q. Вена-E-смежно: само-ссылочные конструкции структурно блокируются (ср. ERRWellFormedness, Soundness.russell_untypable). _(ERR, integrity-gate, self-reference, vein-E)_

**Uniqueness - score 2 (methods).** Процесс ERR над Q: интегрити-гейт даёт вес (валидное→>0), само-ссылка и нарушение порядка→вес 0 (блок само-ссылки).
> _Caveat:_ Вентиль валидности — внутренняя конструкция; вклад — блокировка само-ссылки весом 0 (вена-E-смежно), не новый результат.

---

## #251 - `src/foundation/ERRWellFormedness.v` - score 3 (new-framing)

**ERR well-formedness over Q: Russell/Liar/Grelling ill-formed, decidably (vein E)**

- **Topic.** An ERR category with equality, an ERR system, no-self-reference, rules-above-elements, is-well-formed, nat/Russell/Liar/Grelling systems, nat/chess well-formed, Russell/Liar/Grelling ill-formed, well-formed implies no self-ref, and decidable well-formedness.
- **Role.** Vein-E leaf (paradoxes ill-formed, decidably; the ERR analogue of Soundness.russell_untypable). Self-contained.
- **Counts.** Qed 4 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ ERR-системы (nat/chess vs Russell/Liar/Grelling). _Roles:_ well-formedness = роль (нет само-ссылки, правила над элементами); РАЗРЕШИМА. _Rules:_ no_self_reference; russell_ill_formed; well_formedness_decidable. _P4:_ конечные ERR-системы (Element); парадоксальные (Russell/Liar/Grelling) ill-formed, разрешимо (вена E).
- **Classical counterpart.** Russell's paradox, the Liar and Grelling-Nelson are resolved by type/level stratification (no self-reference); NEW is the DECIDABLE ERR well-formedness check that classifies nat/chess as well-formed and Russell/Liar/Grelling as ill-formed.
- **Tags.** foundation, well-formedness, russell, decidable, vein-E, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `ERRCategory/err_cat_eqb/ERRSystem/no_self_reference/rules_above_elements/is_well_formed/nat_system/russell_system/liar_system/grelling_system` | Definition | ERR-системы, well-formedness |
| `nat_well_formed/russell_ill_formed/liar_ill_formed/grelling_ill_formed/well_formed_no_self_ref/nat_has_all_three/chess_system/chess_well_formed/well_formedness_decidable/err_well_formedness_synthesis` | Theorem | ★ Russell/Liar/Grelling ill-formed, РАЗРЕШИМО |

**Key lemmas (deep):**

- **`well_formedness_decidable`** - РАЗРЕШИМАЯ проверка well-formedness ERR: nat/chess проходят, Russell/Liar/Grelling-Nelson ОТВЕРГАЮТСЯ как ill-formed (само-референтны, правила не над элементами) над Q. Вена E: парадоксы блокируются СТРУКТУРНО и РАЗРЕШИМО — ERR-аналог Soundness.russell_untypable и Architecture_of_Reasoning/ParadoxDissolution. Один механизм (запрет само-ссылки) растворяет три классических парадокса. _(well-formedness, russell, liar, decidable, vein-E)_

**Uniqueness - score 3 (new-framing).** Разрешимая well-formedness ERR над Q (вена E): Russell/Liar/Grelling ill-formed (само-ссылка), nat/chess well-formed — парадоксы блокируются структурно и разрешимо.
> _Caveat:_ Разрешение Russell/Liar через типы/уровни классично (Russell/Tarski); вклад — единый разрешимый ERR-критерий well-formedness, не новый результат.

---

## #252 - `src/foundation/ERRWilsonBridge.v` - score 2 (methods)

**ERR-Wilson bridge over Q: ERR path-sum = scaled Wilson action**

- **Topic.** A gauge config, a 2cos approximation, an ERR path-sum-2 and scaled ERR/Wilson actions, agreement at N=0/1/2 (vacuum both zero, ERR equals Wilson), 2cos even/zero/bounded, and 2-2cos.
- **Role.** ERR-machinery leaf (ERR<->Wilson action, with ERRComputationBridge). Links to gauge/. Self-contained.
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ калибровочная конфигурация; ERR path-sum; Wilson-действие. _Roles:_ ERR path-sum = роль (= масштаб. Wilson-действие). _Rules:_ err_equals_wilson_N1; err_equals_wilson_N2; two_minus_two_cos. _P4:_ конечные конфигурации над Q (Element); ERR path-sum = масштабированное Wilson-действие на N=0/1/2.
- **Classical counterpart.** The Wilson lattice gauge action (2-2cos plaquette) is standard; NEW is the ToS bridge equating an ERR path-sum to the (scaled) Wilson action at concrete lattice sizes.
- **Tags.** foundation, ERR, wilson, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `GConfig/zero_gconfig/two_cos_approx/err_path_sum_2/err_action_scaled/wilson_action_scaled/two_cos_at_0/err_path_sum_2_N0/wilson_scaled_N0/err_scaled_N0/vacuum_both_zero` | Definition/Theorem | ERR/Wilson действия, вакуум=0 |
| `err_path_sum_2_N1/err_scaled_N1/wilson_scaled_N1/err_equals_wilson_N1/err_path_sum_2_N2/err_scaled_N2/wilson_scaled_N2/err_equals_wilson_N2/two_cos_even/_zero/two_minus_two_cos/two_cos_bounded/err_wilson_bridge_summary/_count` | Theorem | ★ ERR = Wilson на N=1,2 |

**Key lemmas (deep):**

- **`err_equals_wilson_N2`** - ERR path-sum РАВЕН масштабированному Wilson-действию (2−2cos плакета) на конкретных размерах N=0/1/2 над Q — мост ERR-онтологии к решёточной калибровке (gauge/). Делает ERR вычислимо эквивалентной стандартному действию. Ср. ERRComputationBridge. _(ERR, wilson, action, lattice)_

**Uniqueness - score 2 (methods).** Мост ERR-Wilson над Q: ERR path-sum = масштабированное Wilson-действие (2−2cos) на N=0/1/2.
> _Caveat:_ Wilson-действие стандартно; вклад — отождествление с ERR path-sum, не новый результат калибровки.

---

## #253 - `src/foundation/EtaFromLattice.v` - score 2 (methods)

**Eta from lattice over Q: baryon eta from the Jarlskog transport asymmetry**

- **Topic.** Local CP phases, CP phase exists/derived, two-gen no CP, three-gen one CP, a Jarlskog estimate (positive, decreasing), eta from Jarlskog (positive derived), and eta as a transport asymmetry.
- **Role.** Baryogenesis leaf (eta from Jarlskog). Self-contained (QArith).
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ CP-фазы; Jarlskog; eta. _Roles:_ eta = роль из Jarlskog (асимметрия переноса); 3 поколения для CP. _Rules:_ three_gen_one_cp; eta_from_jarlskog; eta_positive_derived. _P4:_ конечные Jarlskog-оценки над Q (Element); eta из Jarlskog (3 поколения).
- **Classical counterpart.** That CP requires 3 generations (Jarlskog nonzero) and the baryon asymmetry eta follows from it as a transport asymmetry is standard; here a rational instance.
- **Tags.** foundation, baryogenesis, jarlskog, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `n_cp_phases_local/cp_phase_exists/_derived/two_gen_no_cp/three_gen_one_cp/pos_cube/jarlskog_estimate/jarlskog_at_0/_1/_2/jarlskog_pos_0/_1/_2/jarlskog_positive/jarlskog_decreasing` | Definition/Theorem | CP из 3 поколений, Jarlskog |
| `eta_from_jarlskog/eta_positive_derived/eta_as_transport_asymmetry` | Theorem | ★ eta из Jarlskog (асимметрия переноса) |

**Key lemmas (deep):**

- **`eta_as_transport_asymmetry`** - eta (барионная асимметрия) выводится из Jarlskog как асимметрия переноса: CP требует 3 поколений (two_gen_no_cp), Jarlskog положителен над Q. Стандартная физика бариогенезиса (ср. BaryonFromFoundation/BaryogenesisTransport). _(baryogenesis, jarlskog, eta, cp)_

**Uniqueness - score 2 (methods).** Eta из решётки над Q: барионная eta из Jarlskog-асимметрии переноса, CP из 3 поколений.
> _Caveat:_ CP из 3 поколений и eta из Jarlskog стандартны; Q-инстанс без нового содержания.

---

## #254 - `src/foundation/EulerCharacteristic.v` - score 2 (methods)

**Euler characteristic over Q: chi determines genus (sphere vs torus)**

- **Topic.** chi, chi of a cube, all Platonic solids are spheres, chi invariant under edge split / diagonal add, chi genus, chi determines genus, and sphere/torus distinct.
- **Role.** Topology leaf (Euler characteristic). Self-contained.
- **Counts.** Qed 1 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ эйлерова характеристика chi; род. _Roles:_ chi = роль-инвариант (определяет род). _Rules:_ chi_determines_genus; sphere_torus_distinct; chi_split_edge. _P4:_ конечные комплексы (Element); chi инвариантна, определяет род (сфера≠тор).
- **Classical counterpart.** The Euler characteristic chi, its invariance under edge splits / diagonal adds, and chi determining genus (sphere vs torus) are classical topology; here a Q instance.
- **Tags.** foundation, euler-characteristic, topology, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `chi/chi_cube/platonic_all_sphere/chi_split_edge/chi_add_diagonal/chi_genus` | Definition/Theorem | chi инвариантна |
| `chi_determines_genus/sphere_torus_distinct/euler_topology` | Theorem | ★ chi определяет род (сфера≠тор) |

**Key lemmas (deep):**

- **`chi_determines_genus`** - Эйлерова характеристика chi инвариантна (под расщеплением рёбер/добавлением диагоналей) и определяет род — сфера и тор различны над Q. Стандартная топология (ср. geometry/DiscreteGaussBonnet). Иллюстративно. _(euler-characteristic, genus, topology)_

**Uniqueness - score 2 (methods).** Эйлерова характеристика над Q: chi инвариантна, определяет род (сфера≠тор), платоновы тела — сферы.
> _Caveat:_ chi и её связь с родом — классическая топология; Q-инстанс без нового содержания.

---

## #255 - `src/foundation/EulerProcessRoleLimit.v` - score 3 (new-framing)

**Euler's e as a role-limit over Q: e excludes the rationals (vein C)**

- **Topic.** A rational factorial, an e-partial, scaling, a scaled bridge, e excludes a rational, 3/2 excluded, the e-process is a role-limit, and e is a role-limit.
- **Role.** Vein-C leaf (e as role-limit, sibling of ContinuumLimitRoleLimit/sqrt2). Self-contained (QArith).
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ частичные факториальные суммы e; приближения. _Roles:_ e = role-limit (приближается, не достигает рационального). _Rules:_ e_excludes_rational; three_halves_excluded; e_is_role_limit. _P4:_ каждая частичная сумма рациональна и конечна (Element); e — role-limit (исключает рациональные, three_halves_excluded) — вена C.
- **Classical counterpart.** That e (Euler's number) is irrational — its partial factorial-sum approximations never equal a rational like 3/2 — is classical; NEW is the vein-C statement 'e is a role-limit' (the process approaches but never reaches a rational).
- **Tags.** foundation, euler-e, role-limit, vein-C, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `qfact/epart/inject_pos/scale_lt/qfact_pos/qfact_nat/inject_Z_lt_inv/escaled/escaled_bridge` | Definition/Theorem | факториальные частичные суммы e |
| `e_excludes_rational/three_halves_excluded/e_process_is_role_limit/e_is_role_limit/euler_process_role_limit` | Theorem | ★ e исключает рациональные (role-limit) |

**Key lemmas (deep):**

- **`e_is_role_limit`** - Число e — role-limit: частичные факториальные суммы приближаются, но ИСКЛЮЧАЮТ рациональные значения (three_halves_excluded) над Q. Тот же механизм, что sqrt2_never_reached (ContinuumLimitRoleLimit) — иррациональная константа как процесс-предел, не актуальный Element. Вена C. _(euler-e, role-limit, irrational, vein-C)_

**Uniqueness - score 3 (new-framing).** Число e как role-limit над Q (вена C): частичные факториальные суммы приближаются, но исключают рациональные (three_halves_excluded) — e никогда не актуальный Element.
> _Caveat:_ Иррациональность e классична; уникальность — в P4-формулировке role-limit (процесс исключает рациональные), пара к sqrt2_never_reached, не новый результат об e.

---

## #256 - `src/foundation/FeigenbaumERR.v` - score 2 (methods)

**Feigenbaum in E/R/R over Q: period-2 via discriminant, delta bracketed in (4,5)**

- **Topic.** A logistic step/iteration, fixed points at r=2/3/7.2, a period-72 cycle (period-2 at 7.2), period-4 consistency, the first bifurcation exact, a period-2 discriminant (a rational square at 7.2), no period-2 below 3 / exists above 3, and delta loose/tight brackets (delta in (4,5)).
- **Role.** Numerical/chaos leaf (Feigenbaum, with a vein-A discriminant). Self-contained (QArith).
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ логистическое отображение; неподвижные точки; дискриминант period-2. _Roles:_ бифуркация = роль (period-2 при r>3); delta как role-limit с рациональной скобкой. _Rules:_ first_bifurcation_exact; period_2_exists_above_3; disc_at_72_is_rational_square. _P4:_ конечные итерации над Q (Element); первая бифуркация точна (r=3), delta зажата в (4,5); period-2 решается дискриминантом (вена A).
- **Classical counterpart.** The logistic-map period-doubling, the first bifurcation at r=3 and the Feigenbaum constant delta~4.669 are classical chaos theory; NEW is the vein-A touch (the period-2 discriminant is a rational square above r=3) plus a machine-verified rational bracket delta in (4,5).
- **Tags.** foundation, feigenbaum, discriminant, vein-A, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `logistic_step/logistic_iter/iter_0/_1/fixed_pt_r2/_r3/_r72/_zero/cycle_72_step1/_step2/period_2_at_72_from_three_sevenths/_six_sevenths/period_4_consistency/cycle_elements_distinct/cycle_distinct_from_fixed` | Definition/Theorem | логистическое отображение, цикл period-2 |
| `r_bif_1/first_bifurcation_exact/period2_discriminant/disc_at_3/_at_72/disc_at_72_is_rational_square/no_period_2_below_3/period_2_exists_above_3` | Theorem | ★ первая бифуркация r=3, дискриминант period-2 |
| `delta_loose_lower/_upper/delta_tight_lower/_upper/tight_inside_loose_lower/_upper/tight_bracket_valid/delta_in_4_5/feigenbaum_facts/at` | Theorem | ★ delta зажата в (4,5) |

**Key lemmas (deep):**

- **`disc_at_72_is_rational_square`** - Период-2 логистического отображения возникает при r>3, решаемо через ДИСКРИМИНАНТ (рациональный квадрат при r=7.2) над Q — вена-A касание (перфект-квадрат решает существование цикла). Первая бифуркация точна (r=3). delta зажата в (4,5) машинно. Классическая теория хаоса с веной-A инструментом. _(feigenbaum, logistic, discriminant, vein-A)_
- **`delta_in_4_5`** - Константа Фейгенбаума delta зажата в рациональную скобку (4,5) над Q (tight внутри loose) — delta как role-limit с машинной скобкой (ср. AperyConstantERR). Честная численная оценка. _(feigenbaum, delta, bracket, role-limit)_

**Uniqueness - score 2 (methods).** Фейгенбаум в E/R/R над Q: первая бифуркация r=3 точна, period-2 через дискриминант (рациональный квадрат, вена A), delta зажата в (4,5).
> _Caveat:_ Удвоение периода, r=3 и delta~4.669 — классическая теория хаоса; вклад — вена-A дискриминант period-2 + машинная скобка delta, не новый результат.

---

## #257 - `src/foundation/FoundationNamedFloor.v` - score 2 (methods)

**Foundation named floor over Q: which choices are posited (honest audit)**

- **Topic.** A source/audit, is-posited, n-posited, rides-on-model, gauge-group/generation-count audits, gauge-group/generation ride, audit upgraded (implies old), upgraded gauge/generation, and a posited-flag resolves.
- **Role.** Honesty/posit-audit leaf (the named framework floor). Self-contained.
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ источники; постулаты (калибровка, число поколений). _Roles:_ аудит = роль-классификатор постулатов (что постулировано до upgrade). _Rules:_ gauge_group_rides; generation_rides; posited_flag_resolves. _P4:_ конечный аудит (Element); ЧЕСТНО: калибровка и число поколений постулированы (ride on model), пока не upgraded.
- **Classical counterpart.** No classical counterpart — an internal posit audit naming the framework 'floor': the gauge group and generation count are posited (ride on a model) until upgraded.
- **Tags.** foundation, honesty, posit-audit, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `Source/Audit/is_posited/n_posited/rides_on_model/gauge_group_audit/generation_count_audit/gauge_group_rides/generation_rides` | Definition/Theorem | ★ калибровка/поколения постулированы |
| `audit_upgraded/upgraded_implies_old/gauge_group_upgraded/generation_upgraded/posited_flag_resolves/foundation_audit_named_floor` | Theorem | upgrade разрешает флаг постулата |

**Key lemmas (deep):**

- **`gauge_group_rides`** - ЧЕСТНЫЙ аудит «пола» фреймворка: калибровочная группа и число поколений ПОСТУЛИРОВАНЫ (rides_on_model), пока не upgraded над Q. Образец калибровки против SM-from-distinction over-claim — явно помечает, что НЕ выведено, а постулировано. _(honesty, posit-audit, gauge-group, calibration)_

**Uniqueness - score 2 (methods).** Названный пол foundation над Q: калибровка и число поколений ЧЕСТНО помечены постулированными (ride on model), пока не upgraded.
> _Caveat:_ Внутренний posit-аудит; ценность — честная фиксация постулатов против SM-over-claim, не новый результат.

---

## #258 - `src/foundation/FrameFreeFinitization.v` - score 3 (new-framing)

**Frame-free finitization over Q: crystallographic restriction, order-5 forbidden, count is frame-free**

- **Topic.** A lattice trace, lattice compatibility, lattice traces are integers, order-5 has no integer trace / is not a lattice, the crystallographic orders, lattice invariant under / count invariant under, frame-free, count is frame-free, lattice not frame-free, lattice symmetry partial vs count symmetry total, and 'the refutation shows the path'.
- **Role.** Vein-A/D leaf (crystallographic restriction; HIGHLIGHTS H2 'sqrt5/order-5 forbidden symmetry'). Self-contained.
- **Counts.** Qed 2 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ решёточные следы; кристаллографические порядки. _Roles:_ счёт = роль-полная симметрия (frame-free); решётка — частичная. _Rules:_ lattice_traces_are_integers; order5_not_lattice; count_is_frame_free. _P4:_ конечные следы (Element); порядок-5 НЕ имеет целого следа (запрещён кристаллографией), счёт frame-free, решётка частична (вена A/D).
- **Classical counterpart.** The crystallographic restriction (only orders 1,2,3,4,6 have integer lattice traces; order-5 is forbidden) is classical; NEW is the vein-A/D framing that counting is frame-free (total symmetry) while the lattice is only partial — 'the refutation shows the path'.
- **Tags.** foundation, crystallographic, order-5-forbidden, sqrt5, vein-A, vein-D, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `lattice_trace/lattice_compatible/lattice_traces_are_integers/order5_no_integer_trace/order5_not_lattice/crystallographic_orders` | Definition/Theorem | ★ кристалл. порядки, order-5 запрещён |
| `lattice_invariant_under/count_invariant_under/frame_free/count_is_frame_free/lattice_not_frame_free/lattice_symmetry_is_partial/count_symmetry_is_total/refutation_shows_the_path` | Definition/Theorem | ★ счёт frame-free (полная симметрия), решётка частична |

**Key lemmas (deep):**

- **`order5_not_lattice`** - Кристаллографическое ограничение: только порядки 1,2,3,4,6 имеют ЦЕЛЫЙ решёточный след; порядок-5 (пятикратная симметрия, √5/золотое) НЕ имеет → не решётка над Q. Та же нить, что forbidden-symmetry √5 (HIGHLIGHTS H2) и crystallographic-restriction в q-kinematics/geometry. Вена A (целочисленность=граница) ∩ вена D (симметрии). _(crystallographic, order-5-forbidden, sqrt5, vein-A, vein-D)_
- **`count_is_frame_free`** - Счёт (число) frame-free (полная симметрия, инвариантен ко всему), тогда как РЕШЁТКА только частична (lattice_symmetry_is_partial) над Q. «refutation_shows_the_path»: невозможность order-5 на решётке указывает на frame-free счёт. Связь с фон-независимостью (вена C). _(frame-free, count, lattice-partial, vein-C-adjacent)_

**Uniqueness - score 3 (new-framing).** Frame-free финитизация над Q: кристаллографическое ограничение (порядок-5/√5 запрещён, нет целого следа), счёт frame-free (полная симметрия), решётка частична. Нить forbidden-symmetry √5 (HIGHLIGHTS H2), вена A∩D.
> _Caveat:_ Кристаллографическое ограничение (нет 5-кратной симметрии решётки) классично; вклад — вена-A/D переобрамление (целочисленность следа = граница; счёт frame-free vs решётка частична), не новый результат.

---

## #259 - `src/foundation/FrameworkConvergence.v` - score 2 (methods)

**Framework convergence over Q: every descent terminates in the floor**

- **Topic.** A framework element, the framework floor (size, nonempty), a descent, descent bottoms, kappa/eta terminate, every descent terminates in the framework, P4 in both, irreducible axioms, and framework convergence.
- **Role.** Synthesis/meta leaf (descents converge to the floor). Self-contained.
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ элементы фреймворка; спуски (kappa, eta). _Roles:_ сходимость = роль (всякий спуск терминирует в полу фреймворка). _Rules:_ every_descent_terminates_in_framework; kappa_terminates; irreducible_axioms. _P4:_ конечный пол фреймворка (Element); всякий спуск терминирует в неприводимых аксиомах (P4 в обоих).
- **Classical counterpart.** No classical counterpart — a ToS audit that every descent (kappa, eta) terminates in the framework floor, with P4 in both and irreducible axioms.
- **Tags.** foundation, framework, convergence, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `FrameworkElement/framework_floor/_size/_nonempty/Descent/descent_bottoms/kappa_terminates/eta_terminates` | Definition/Theorem | пол фреймворка, спуски терминируют |
| `every_descent_terminates_in_framework/P4_in_both/irreducible_axioms/framework_convergence` | Theorem | ★ всякий спуск терминирует в полу |

**Key lemmas (deep):**

- **`every_descent_terminates_in_framework`** - Всякий спуск (kappa, eta) терминирует в «полу» фреймворка (неприводимые аксиомы, P4 в обоих) над Q — узел-синтез, фиксирующий, что обоснования сходятся к конечному неприводимому ядру. Связь с FoundationNamedFloor/FrameworkConvergence. _(framework, convergence, floor, irreducible)_

**Uniqueness - score 2 (methods).** Сходимость фреймворка над Q: всякий спуск (kappa/eta) терминирует в неприводимом полу (P4 в обоих).
> _Caveat:_ Внутренний узел сходимости обоснований; систематизация, не новый результат.

---

## #260 - `src/foundation/GammaUnification.v` - score 2 (new-framing)

**Gamma unification over Q: decoherence = damping = compression**

- **Topic.** A decay step, decay after, gamma-zero (eternal), gamma-one (instant), gamma-half (monotone), decoherence/damping/compression steps, three are one, and a quantum-classical spectrum.
- **Role.** Synthesis leaf (decoherence=damping=compression). Self-contained.
- **Counts.** Qed 2 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ затухание (gamma); декогеренция/демпфирование/сжатие. _Roles:_ узел-синтез: три процесса = один gamma-распад. _Rules:_ three_are_one; decoherence_step=damping_step=compression_step. _P4:_ конечные шаги затухания (Element); декогеренция=затухание=сжатие (один gamma).
- **Classical counterpart.** That decoherence, damping and lossy compression are the same exponential-decay process (gamma) is a known analogy; NEW only as a Q instance ('three are one').
- **Tags.** foundation, gamma, decoherence, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `decay_step/decay_after/gamma_zero_step/_eternal/gamma_one_step/_instant/gamma_half_step1/_step2/_step3/_monotone` | Definition/Theorem | gamma-распад (0 вечен, 1 мгновенен) |
| `decoherence_step/damping_step/compression_step/three_are_one/quantum_classical_spectrum` | Theorem | ★ три процесса = один gamma |

**Key lemmas (deep):**

- **`three_are_one`** - Декогеренция, демпфирование и сжатие — один и тот же gamma-распад (three_are_one) над Q, дающий квантово-классический спектр. Узел-синтез аналогии (ср. ERRBijections, decoherence/, crown/). Переобрамление, не вывод. _(gamma, decoherence, damping, compression)_

**Uniqueness - score 2 (new-framing).** Унификация gamma над Q: декогеренция=затухание=сжатие (один gamma-распад), квантово-классический спектр.
> _Caveat:_ Аналогия декогеренция/затухание/сжатие известна; вклад — её Q-объединение (three_are_one), не новый результат.

---

## #261 - `src/foundation/GaugeFromDistinctionSynthesis.v` - score 2 (methods)

**Gauge from distinction synthesis over Q: SM gauge group, zero free parameters (over-branded)**

- **Topic.** SM gauge from distinction, valid ND, SM is valid / minimal depth-2, the decomposition is SM, roles match ERR, SU2 from primary / SU3 from nested / U1 from reflexive, and zero free parameters in gauge.
- **Role.** Distinction->SM synthesis. SM-from-distinction OVER-BRANDED. Self-contained.
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ вложенное различение; SM-калибровка. _Roles:_ узел-синтез: SU2/SU3/U1 из primary/nested/reflexive различения. _Rules:_ sm_gauge_from_distinction; zero_free_parameters_in_gauge. _P4:_ конечная конструкция (Element); SM-калибровка из различения; SM-from-distinction OVER-BRANDED.
- **Classical counterpart.** No classical counterpart — a ToS synthesis claiming the SM gauge group SU3xSU2xU1 from nested distinction (SU2 from primary, SU3 from nested, U1 from reflexive) with zero free parameters (SM-from-distinction OVER-BRANDED).
- **Tags.** foundation, gauge, distinction, over-branded, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `sm_gauge_from_distinction/valid_nd/sm_is_valid/sm_minimal_depth2/decomposition_is_sm/roles_match_err` | Theorem | SM из вложенного различения |
| `su2_from_primary/su3_from_nested/u1_from_reflexive/zero_free_parameters_in_gauge/gauge_from_distinction_summary/_theorem_count` | Theorem | ★ SU2/SU3/U1 из primary/nested/reflexive |

**Key lemmas (deep):**

- **`zero_free_parameters_in_gauge`** - Синтез SM-калибровки из вложенного различения (SU2←primary, SU3←nested, U1←reflexive), «ноль свободных параметров» над Q. SM-from-distinction OVER-BRANDED: соответствие настроено давать 321, не выводит калибровку независимо. _(gauge, distinction, over-branded)_

**Uniqueness - score 2 (methods).** Калибровка из различения над Q: SU3×SU2×U1 из primary/nested/reflexive, ноль свободных параметров.
> _Caveat:_ Соответствие настроено на 321; SM-from-distinction OVER-BRANDED, не вывод.

---

## #262 - `src/foundation/GaugeGroupMinimality.v` - score 2 (methods)

**Gauge group minimality over Q: the i-block as minimal generator**

- **Topic.** An i-block (order not 2, i^4, i != -i, det 1, unitary columns/cross), a swap block, and gauge group minimality.
- **Role.** Distinction->SM leaf (minimal gauge generator). Self-contained (QArith).
- **Counts.** Qed 1 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ i-блок; swap-блок. _Roles:_ минимальный калибровочный генератор = роль (i-блок, порядок 4). _Rules:_ i_order_not_2; i_det_one; i_unitary. _P4:_ конечные блоки над Q (Element); i-блок = минимальный неабелев генератор (порядок 4, унитарен).
- **Classical counterpart.** That the imaginary-unit block i (order 4, det 1, unitary) is the minimal nonabelian gauge generator is standard SU(2) algebra; here a Q instance.
- **Tags.** foundation, gauge, su2, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `i_00/i_10/i_sq_00/_11/_01/_10/i_order_not_2/i4_00/_11/sw_00/_10/swap_sq_00/_11` | Definition/Theorem | i-блок, порядок |
| `i_neq_minus_i/i_det_one/i_unitary_col0/_col1/_cross/gauge_group_minimality` | Theorem | ★ i-блок: det=1, унитарен (минимален) |

**Key lemmas (deep):**

- **`gauge_group_minimality`** - i-блок (мнимая единица как матрица, порядок 4, det=1, унитарен) — минимальный неабелев калибровочный генератор над Q. Стандартная SU(2)-алгебра. Связь с BlockCayleyUnistochastic. _(gauge, minimal, su2)_

**Uniqueness - score 2 (methods).** Минимальность калибровочной группы над Q: i-блок (порядок 4, det=1, унитарен) = минимальный неабелев генератор.
> _Caveat:_ SU(2)-алгебра i-блока стандартна; Q-инстанс без нового содержания.

---

## #263 - `src/foundation/GaugeLevelSeparation.v` - score 2 (methods)

**Gauge level separation over Q: exactly two factors mix, SU3 structurally separated**

- **Topic.** A distinction-level, is-endpoint / participates-in-mixing, SU2/U1 endpoints, SU3 not endpoint, SU2/U1 mix, SU3 separated, exactly two mix, separation not confinement, and separation is structural.
- **Role.** Distinction->SM leaf (gauge level separation). SM-from-distinction OVER-BRANDED. Self-contained.
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ уровни различения; калибровочные факторы. _Roles:_ разделение = роль (SU3 структурно отделена, SU2/U1 смешиваются). _Rules:_ exactly_two_mix; SU3_separated; separation_is_structural. _P4:_ конечные уровни (Element); ровно два фактора смешиваются (SU2/U1), SU3 отделена структурно; SM-framing OVER-BRANDED.
- **Classical counterpart.** No classical counterpart — a ToS argument that exactly two of the three gauge factors mix (SU2/U1 endpoints) and SU3 is separated structurally (not by confinement).
- **Tags.** foundation, gauge, separation, over-branded, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `DistinctionLevel/is_endpoint/participates_in_mixing/all_levels/SU2_endpoint/SU3_not_endpoint/U1_endpoint/SU2_mixes/SU3_separated/U1_mixes` | Definition/Theorem | уровни, конечные точки |
| `exactly_two_mix/separation_not_confinement/separation_is_structural/gauge_level_separation_synthesis` | Theorem | ★ ровно два смешиваются, SU3 структурно отделена |

**Key lemmas (deep):**

- **`separation_is_structural`** - SU3 отделена СТРУКТУРНО (она не конечная точка уровня), SU2/U1 смешиваются — ровно два фактора смешиваются над Q. SM-from-distinction OVER-BRANDED: соответствие уровней настроено под SM. _(gauge, separation, over-branded)_

**Uniqueness - score 2 (methods).** Разделение калибровочных уровней над Q: ровно два фактора (SU2/U1) смешиваются, SU3 отделена структурно (не конфайнментом).
> _Caveat:_ Соответствие уровней настроено под SM; SM-from-distinction OVER-BRANDED.

---

## #264 - `src/foundation/GaugePositReduction.v` - score 2 (methods)

**Gauge posit reduction over Q: gauge group rests on three honest posits**

- **Topic.** A depth-3 decomposition, genuine distinction, no-repeat-binary, primary binary, is-minimal, L4 minimal level-1, reflexive terminal, the minimal level-1 is 3, gauge unique, SM f/primary/reflexive/L4, generators, three posits (L1/L4/reflexive), and gauge just/grounded.
- **Role.** Honesty/posit-reduction leaf for the gauge group. Self-contained.
- **Counts.** Qed 4 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ декомпозиция глубины-3; постулаты (L1/L4/reflexive). _Roles:_ редукция постулатов = роль; калибровка на ТРЁХ постулатах. _Rules:_ gauge_three_posits; gauge_unique; min_level1_is_3. _P4:_ конечная декомпозиция (Element); ЧЕСТНО: калибровка опирается на 3 постулата (L1/L4/reflexive).
- **Classical counterpart.** No classical counterpart — an HONEST posit-reduction showing the gauge group rests on three posits (L1, L4, reflexive) after the minimal depth-2 derivation.
- **Tags.** foundation, honesty, posit-reduction, gauge, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `decomp3/genuine_distinction/no_repeat_binary/primary_binary/is_minimal/L4_minimal_level1/reflexive_terminal/min_level1_is_3/gauge_unique/sm_f/sm_primary/sm_reflexive/sm_L4/sm_decomp_forced/gens/sm_total_generators` | Definition/Theorem | декомпозиция, калибровка |
| `Just/grounded/n_posits/L1_posit/L4_posit/refl_posit/gauge_just/gauge_grounded/gauge_three_posits/gauge_posit_reduction` | Theorem | ★ калибровка на 3 постулатах (честно) |

**Key lemmas (deep):**

- **`gauge_three_posits`** - ЧЕСТНО: калибровочная группа опирается на ТРИ явных постулата (L1, L4, reflexive) над Q — редукция постулатов фиксирует основания SM-калибровки. Калибровка против gauge-from-distinction over-claim: явно перечисляет, на чём держится. _(honesty, posit-reduction, gauge)_

**Uniqueness - score 2 (methods).** Редукция постулатов калибровки над Q: калибровочная группа опирается на 3 явных постулата (L1/L4/reflexive) — честная фиксация.
> _Caveat:_ Внутренняя редукция; ценность — честные 3 постулата калибровки, не вывод.

---

## #265 - `src/foundation/GeneralEigenvalueIntegral.v` - score 2 (methods)

**General eigenvalue integral over Q: rational eigenvalue is integer (general n)**

- **Topic.** A general eigenvalue-integral, the monic-mod-b characteristic homogeneous form, a monic root via the general argument, n=4/n=7 examples, and general eigenvalue integrality.
- **Role.** Vein-A leaf (rational-root, general n; with DeterminantModB). Self-contained.
- **Counts.** Qed 4 / Admitted 0 / axioms 0
- **Imports.** Stdlib: ZArith
- **E/R/R.** _Elements:_ char-многочлен общего n; собственные значения. _Roles:_ рациональный корень монического char-многочлена = роль (целочислен). _Rules:_ monic_root_via_general; general_eigenvalue_integrality. _P4:_ конечные char-многочлены (Element); рациональное с.з. целочисленно для общего n (вена A).
- **Classical counterpart.** The rational-root theorem for the monic characteristic polynomial (a rational eigenvalue of an integer matrix is an integer) at general n is classical; here a Q instance via mod-b.
- **Tags.** foundation, rational-root, general-n, vein-A, methods

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `eigenvalue_integral_general/mhom_monic_mod_b/monic_root_via_general/eig_n4/eig_n7/general_eigenvalue_integrality` | Theorem | ★ рациональное с.з. целочисленно (общий n) |

**Key lemmas (deep):**

- **`general_eigenvalue_integrality`** - Рациональное собственное значение целочисленной матрицы общего n целочисленно (через монический char-многочлен mod b) — вена A, дубликат-родственник DeterminantModB. Подтверждает границу Element/role-limit для спектра в любой размерности. _(rational-root, general-n, vein-A)_

**Uniqueness - score 2 (methods).** Общая интегральность собственных значений над Z: рациональное с.з. целочисленно для общего n (вена A).
> _Caveat:_ Теорема о рациональном корне классична; вклад — общий-n инстанс (родствен DeterminantModB), не новый результат.

---

## #266 - `src/foundation/GeneralHermitianCayley.v` - score 3 (new-framing)

**General Hermitian Cayley over Q: dense in U(N), all unistochastic (vein D)**

- **Topic.** A general Hermitian H (symmetric, extends the block, diagonal freedom), iH (antisymmetric, reduces to block), parameter counts (N=2/N=3/general, N(N-1)/2), concrete entries, different from block Cayley, Cayley levels, general covers block, Cayley dense in U(N), and P4 all-unistochastic.
- **Role.** Vein-D leaf (general Hermitian Cayley, dense in U(N); generalizes BlockCayleyUnistochastic). One of the larger foundation files (Q12). Self-contained (QArith).
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ общая эрмитова H; iH (антисимметрична); Cayley-параметры. _Roles:_ общий Cayley = роль (плотен в U(N)); унистохастика как роль. _Rules:_ cayley_dense_in_UN; p4_all_unistochastic; general_covers_block. _P4:_ конечные параметры над Q (Element); общий Cayley плотен в U(N), ВСЕ унистохастичны — вена D (обобщение блочного).
- **Classical counterpart.** The Cayley transform of a general Hermitian (here antisymmetric/imaginary) matrix to a unitary, and unistochastic matrices being dense in the doubly-stochastic ones, are classical; NEW is the explicit Q parametrization with a parameter count and 'P4: all unistochastic / Cayley dense in U(N)'.
- **Tags.** foundation, cayley, unistochastic, vein-D, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `i_block/H_general/_symmetric/_extends_block/_diagonal_freedom/iH_general/_antisym/iH_reduces_to_block/param_count_N2/_N3/div2_even/param_count_general` | Definition/Theorem | общая эрмитова H, счёт параметров |
| `H_concrete_entry_02/_03/_symmetric/iH_concrete_antisym/different_from_block_cayley/CayleyLevel/levels_of_cayley/general_covers_block/general_has_N2_params/cayley_dense_in_UN/p4_all_unistochastic/general_hermitian_synthesis` | Definition/Theorem | ★ Cayley плотен в U(N), все унистохастичны |

**Key lemmas (deep):**

- **`cayley_dense_in_UN`** - Общее преобразование Кэли (эрмитова H с N(N-1)/2 параметрами) плотно в U(N), и ВСЕ результирующие матрицы унистохастичны над Q — обобщает BlockCayleyUnistochastic с блока на полную унитарную группу. Вена D: рациональный Cayley покрывает всю калибровочную группу, p4_all_unistochastic связывает с born-вероятностями. _(cayley, dense-U(N), unistochastic, vein-D)_

**Uniqueness - score 3 (new-framing).** Общий эрмитов Cayley над Q: плотен в U(N), все матрицы унистохастичны (N(N-1)/2 параметров) — вена D, обобщение блочного Cayley на полную U(N).
> _Caveat:_ Преобразование Кэли и плотность унистохастики классичны; вклад — явная Q-параметризация всей U(N), не новая теория.

---

## #267 - `src/foundation/GenerationsFromL4.v` - score 2 (methods)

**Generations from L4 over Q: 3 is the minimum for CP (CLAUDE.md key def)**

- **Topic.** n_cp_phases, has_cp_violation, no CP for 1/2 generations, yes CP for 3/4, min generations for CP, three is minimum, L4 stops at 3, no CP below 3, CP from 3, phase counts grow, and three generations match experiment.
- **Role.** Distinction->SM leaf (generations from L4; CLAUDE.md key defs n_cp_phases/min_generations_for_cp). CP-needs-3 real, count-cap OVER-BRANDED. Self-contained.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ число CP-фаз; число поколений. _Roles:_ поколения = роль; L4 ограничивает 3; CP требует ≥3. _Rules:_ min_generations_for_cp; three_is_minimum; L4_stops_at_3. _P4:_ конечный счёт фаз (Element); CP требует ≥3 поколений (РЕАЛЬНО); L4-ограничение сверху OVER-BRANDED.
- **Classical counterpart.** That CP violation requires >=3 fermion generations (the Jarlskog/CKM phase needs 3) is standard particle physics; NEW is the ToS framing that L4 caps the count at 3 (the SM-from-distinction part is OVER-BRANDED, but CP-needs-3 is real).
- **Tags.** foundation, generations, cp, over-branded, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `n_cp_phases/has_cp_violation/no_cp_1gen/no_cp_2gen/yes_cp_3gen/yes_cp_4gen/min_generations_for_cp` | Definition/Theorem | ★ CP требует ≥3 поколений |
| `three_is_minimum/L4_stops_at_3/no_cp_below_3/cp_from_3/phase_counts/phases_grow/three_generations_match_experiment/generations_summary/_theorem_count` | Theorem | ★ 3 — минимум; L4 ограничивает сверху |

**Key lemmas (deep):**

- **`min_generations_for_cp`** - CP-нарушение требует ≥3 поколений (число CP-фаз зануляется при 1/2, появляется при 3) над Q — реальный факт физики частиц (CLAUDE.md key def). НИЖНЯЯ граница (3 для CP) обоснована; ВЕРХНЯЯ граница (L4_stops_at_3 = ровно 3) — SM-from-distinction OVER-BRANDED. _(generations, cp, 3-minimum, over-branded)_

**Uniqueness - score 2 (methods).** Поколения из L4 над Q: CP требует ≥3 поколений (минимум обоснован), L4 ограничивает ровно 3.
> _Caveat:_ CP-нужно-3-поколения — реальная физика; верхняя граница «ровно 3» (L4) SM-from-distinction OVER-BRANDED.

---

## #268 - `src/foundation/GenerationsPositReduction.v` - score 2 (methods)

**Generations posit reduction over Q: 'exactly 3' rests on two honest posits**

- **Topic.** n_cp_phases, CP false at 2 / true at 3, no CP below 3, a generations lower bound, L4 minimal generations, generations unique, three is L4-minimal, a framework posit and an L4-min posit, count just, exactly-3 just (two posits), and exactly costs one more posit.
- **Role.** Honesty/posit-reduction leaf for generations. Self-contained.
- **Counts.** Qed 4 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ CP-фазы; число поколений; постулаты. _Roles:_ редукция = роль; «ровно 3» на ДВУХ постулатах (framework + L4-min). _Rules:_ exactly3_two_posits; generations_lower_bound; exactly_costs_one_more_posit. _P4:_ конечный счёт (Element); ЧЕСТНО: нижняя граница 3 обоснована, «ровно 3» стоит +1 постулат.
- **Classical counterpart.** No classical counterpart — an HONEST posit-reduction showing 'exactly 3 generations' rests on two posits (framework + L4-minimality) beyond the CP lower bound.
- **Tags.** foundation, honesty, generations, posit-reduction, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `n_cp_phases/has_cp_violation/cp_2_false/cp_3_true/no_cp_below_3/generations_lower_bound/L4_minimal_generations/generations_unique/three_is_L4_minimal` | Definition/Theorem | нижняя граница 3 (CP) |
| `framework_posit/L4min_posit/count_just/exactly3_just/count_one_posit/exactly3_two_posits/exactly_costs_one_more_posit/generations_posit_reduction` | Theorem | ★ «ровно 3» = +1 постулат (честно) |

**Key lemmas (deep):**

- **`exactly_costs_one_more_posit`** - ЧЕСТНО: нижняя граница (≥3 для CP) обоснована, но «РОВНО 3 поколения» стоит ОДНОГО дополнительного постулата (L4-минимальность) над Q. Калибровка: явно разделяет обоснованную нижнюю границу от постулированной точной. _(honesty, generations, posit-reduction)_

**Uniqueness - score 2 (methods).** Редукция постулатов поколений над Q: ≥3 обосновано (CP), «ровно 3» стоит +1 постулата (L4-минимальность) — честное разделение.
> _Caveat:_ Внутренняя редукция; ценность — честное разделение нижней границы и точного числа, не вывод.

---

## #269 - `src/foundation/GenerationsSynthesis.v` - score 2 (methods)

**Generations synthesis over Q: three generations derived (over-branded)**

- **Topic.** Three generations derived, the derivation chain, three-gen physics, two-gen insufficient, four-gen unnecessary, and experimental match.
- **Role.** Distinction->SM synthesis (three generations). SM-from-distinction OVER-BRANDED. Self-contained.
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ поколения; цепочка вывода. _Roles:_ узел-синтез: три поколения «выведены». _Rules:_ three_generations_derived; two_gen_insufficient; four_gen_unnecessary. _P4:_ конечная цепочка (Element); три поколения; SM-from-distinction OVER-BRANDED.
- **Classical counterpart.** No classical counterpart — a synthesis claiming three generations derived (two insufficient, four unnecessary) matching experiment (SM-from-distinction OVER-BRANDED).
- **Tags.** foundation, generations, synthesis, over-branded, methods

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `three_generations_derived/generation_derivation_chain/three_gen_physics/two_gen_insufficient/four_gen_unnecessary/experimental_match/generations_complete/generations_synthesis_theorem_count` | Theorem | ★ три поколения (2 мало, 4 лишне) |

**Key lemmas (deep):**

- **`three_generations_derived`** - Синтез: три поколения «выведены» (2 недостаточно, 4 излишне), совпадает с экспериментом над Q. SM-from-distinction OVER-BRANDED: «вывод» опирается на постулированные пороги (ср. GenerationsPositReduction). _(generations, synthesis, over-branded)_

**Uniqueness - score 2 (methods).** Синтез поколений над Q: три поколения (2 мало для CP, 4 лишне), совпадает с экспериментом.
> _Caveat:_ Опирается на постулированные пороги; SM-from-distinction OVER-BRANDED.

---

## #270 - `src/foundation/GraphUnitary.v` - score 2 (new-framing)

**Graph unitary over Q: Cayley of an antisymmetric graph gives a unitary (vein D)**

- **Topic.** An antisymmetric M_2, Cayley_2 (orthogonal rows/cols), a Gamma_2, concrete entries, an antisymmetric M_3, U_3 Cayley (orthogonal rows), and Gamma_3 rows/cols.
- **Role.** Vein-D leaf (graph -> unitary via Cayley; with BlockCayleyUnistochastic/GeneralHermitianCayley). Self-contained (QArith).
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ антисимметричная M (граф); Cayley-унитарий; Gamma=\|U\|². _Roles:_ граф = роль (связность); Cayley превращает в унитарий. _Rules:_ cayley_2_orth; U_3_orth_row; Gamma бистохастична. _P4:_ конечные графы над Q (Element); Cayley антисимметричного графа → унитарий → бистохастика (вена D).
- **Classical counterpart.** The Cayley transform of an antisymmetric graph adjacency to a unitary, with the resulting \|U\|^2 doubly-stochastic, is classical; NEW only as an explicit Q 2x2/3x3 instance (vein D).
- **Tags.** foundation, graph, cayley, vein-D, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `M_2/M_2_antisym/cayley_2/sq_nonneg/inv4_pos/denom_pos/_neq_0/cayley_2_orth_00/_11/_01/_col_orth_00/gamma_2_row_0/_row_1/cayley_2_at_1_00/_01/_10/_11` | Definition/Theorem | ★ Cayley_2 ортогонален |
| `M_3/M_3_antisym/U_3_cayley/Gamma_3/U_3_orth_row0/_row1/_row2/_01/Gamma_3_row0/_row1/_col0/_col1` | Theorem | ★ U_3 ортогонален, Gamma_3 бистохастична |

**Key lemmas (deep):**

- **`U_3_orth_row0`** - Преобразование Кэли антисимметричной графовой матрицы (2×2, 3×3) даёт ортогональный/унитарный U, \|U\|² бистохастична над Q — вена D, конкретный граф→квант мост (ср. BlockCayleyUnistochastic, GeneralHermitianCayley). Связность графа → квантовые вероятности. _(graph, cayley, unitary, vein-D)_

**Uniqueness - score 2 (new-framing).** Граф-унитарий над Q: Cayley антисимметричного графа (2×2,3×3) → ортогональный U, Gamma=|U|² бистохастична (вена D).
> _Caveat:_ Cayley антисимметричной матрицы → унитарий классично; вклад — явный графовый Q-инстанс (вена D), не новая теория.

---

## #271 - `src/foundation/GravityFinitization.v` - score 3 (new-framing)

**Gravity finitization over Q: pathologies are continuum role-limits that dissolve (vein C)**

- **Topic.** A gravity object/side, gravity richly formalized, the continuum is a role-limit, a pathology side, all pathologies are continuum, graviton self-energy/UV dissolves, singularity dissolves, vacuum density / lambda dissolves.
- **Role.** Gravity leaf (pathologies as role-limits, vein-C). Honest reframing. Self-contained.
- **Counts.** Qed 2 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ гравитационные объекты; патологии (UV/сингулярность/Lambda). _Roles:_ континуум = role-limit; патологии живут на стороне континуума. _Rules:_ continuum_is_role_limit; uv_dissolves; singularity_dissolves; lambda_dissolves. _P4:_ конечная (element) сторона гравитации (Element); патологии (UV/сингулярность/Lambda) суть континуум-role-limit, РАСТВОРЯЮТСЯ в финитном (вена C) — переобрамление, не решение.
- **Classical counterpart.** The UV divergence of perturbative quantum gravity, the singularity and the cosmological-constant problem are real open problems; NEW is the P4/vein-C framing that these pathologies are continuum role-limits that 'dissolve' in the finite (element) picture — honest reframing, not a solution.
- **Tags.** foundation, gravity, continuum-role-limit, vein-C, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `GravObject/Side/grav_side/all_grav/is_element/n_element/gravity_richly_formalized/continuum_is_role_limit` | Definition/Theorem | ★ континуум = role-limit |
| `Pathology/pathology_side/pathologies_all_continuum/graviton_self_energy/uv_dissolves/shell_radius/inject_succ_pos/singularity_dissolves/vacuum_density/lambda_dissolves/gravity_finitization` | Definition/Theorem | ★ UV/сингулярность/Lambda растворяются |

**Key lemmas (deep):**

- **`pathologies_all_continuum`** - ВСЕ патологии квантовой гравитации (UV-расходимость, сингулярность, проблема Lambda) лежат на стороне КОНТИНУУМА (role-limit) и «растворяются» в финитной (element) картине над Q — вена C. ЧЕСТНОЕ переобрамление: показывает, что патологии — артефакты континуум-предела, а не решает физическую гравитацию. _(gravity, uv-dissolves, continuum-role-limit, vein-C)_

**Uniqueness - score 3 (new-framing).** Финитизация гравитации над Q: патологии (UV/сингулярность/Lambda) — континуум-role-limit, растворяются в финитной картине (вена C).
> _Caveat:_ UV-расходимость, сингулярность и проблема Lambda — реальные открытые проблемы; вклад — честное P4/вена-C переобрамление (патологии=континуум-артефакты), НЕ решение квантовой гравитации.

---

## #272 - `src/foundation/GravityH1Decision.v` - score 2 (new-framing)

**Gravity H1 decision over Q: sort gravity pathologies by boundedness (vein A)**

- **Topic.** An observable, a cutoff, bounded/unbounded, cutoff unbounded, dominates-cutoff unbounded, bounded/unbounded exclusive, Newton/vac-density/UV/lambda/singularity observables, UV/lambda/singularity unbounded, an H1 pathology UV, a sort (disjoint), and gravity sort.
- **Role.** Vein-A leaf (gravity pathology sort by boundedness; with GravityFinitization). Self-contained.
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ гравитационные наблюдаемые; cutoff. _Roles:_ сортировка = роль (bounded=Element vs unbounded=патология). _Rules:_ uv_unbounded; lambda_unbounded; sing_unbounded; sort_disjoint. _P4:_ конечные наблюдаемые (Element); UV/Lambda/сингулярность НЕОГРАНИЧЕНЫ (role-limit), Newton ограничен (Element) — вена A сортировка.
- **Classical counterpart.** No classical counterpart — a vein-A sort of gravity observables into bounded (element) vs unbounded (role-limit/pathology), classifying UV/lambda/singularity as unbounded.
- **Tags.** foundation, gravity, bounded-unbounded, vein-A, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `Obs/cutoff/Bounded/Unbounded/arch_nat/cutoff_unbounded/dominates_cutoff_unbounded/bounded_unbounded_exclusive/const_bounded/cutoff_prefix_bounded` | Definition/Theorem | bounded vs unbounded |
| `newton_obs/vac_density_obs/uv_obs/lambda_obs/sing_obs/uv_unbounded/lambda_unbounded/sing_unbounded/h1_pathology_uv/Side/classified/sort_disjoint/gravity_sort` | Definition/Theorem | ★ UV/Lambda/сингулярность неограничены |

**Key lemmas (deep):**

- **`gravity_sort`** - Сортирует гравитационные наблюдаемые на ОГРАНИЧЕННЫЕ (Element: Newton) vs НЕОГРАНИЧЕННЫЕ (role-limit/патология: UV, Lambda, сингулярность) над Q, дизъюнктно — вена A применённая к гравитации (граница bounded/unbounded). Дополняет GravityFinitization вычислимой классификацией. _(gravity, bounded-unbounded, pathology-sort, vein-A)_

**Uniqueness - score 2 (new-framing).** H1-решение для гравитации над Q: сортировка наблюдаемых bounded (Element: Newton) vs unbounded (role-limit: UV/Lambda/сингулярность), дизъюнктно (вена A).
> _Caveat:_ Классификация по ограниченности проста; вклад — вена-A применение к гравитационным патологиям, не новый результат.

---

## #273 - `src/foundation/GravityRuleUniversality.v` - score 2 (new-framing)

**Gravity rule universality over Q: gravity is a rule (universal), gauge is selective**

- **Topic.** A physical system with gravitational/inertial charge and gauge coupling, several systems, the equivalence principle, universal free fall, gravity universal / no screening, gauge selective / signed / ratio not universal, neutral still gravitates, and gravity is a rule not a role.
- **Role.** Gravity leaf (equivalence principle as rule-universality). Self-contained.
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ физические системы; гравитационный/калибровочный заряды. _Roles:_ гравитация = ПРАВИЛО (универсальна), калибровка = роль (селективна). _Rules:_ universal_free_fall; gravity_no_screening; gravity_is_rule_not_role. _P4:_ конечные системы (Element); гравитация универсальна (правило), калибровка селективна/знаковая (роль).
- **Classical counterpart.** The equivalence principle (universal free fall, gravity couples to everything, no screening) vs selective/signed gauge coupling is standard GR; NEW is the ToS framing 'gravity is a rule, not a role'.
- **Tags.** foundation, gravity, equivalence-principle, ERR, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `PhysSystem/grav_charge/inertial/gauge_coupling/sysA/sysB/sysNeutral/sysNeg/equivalence_principle/universal_free_fall` | Definition/Theorem | принцип эквивалентности |
| `gravity_universal/gravity_no_screening/gauge_selective/neutral_still_gravitates/gauge_ratio_not_universal/gauge_signed/gravity_is_rule_not_role` | Theorem | ★ гравитация = правило, калибровка = роль |

**Key lemmas (deep):**

- **`gravity_is_rule_not_role`** - Гравитация — ПРАВИЛО (универсальна, нет экранирования, нейтральное тоже гравитирует), тогда как калибровка — РОЛЬ (селективна, знаковая, отношение не универсально) над Q. Принцип эквивалентности в ERR-онтологии: гравитация на уровне Rules, калибровка на уровне Roles. _(gravity, equivalence-principle, rule-not-role, ERR)_

**Uniqueness - score 2 (new-framing).** Универсальность правила гравитации над Q: гравитация = правило (универсальна, нет экранирования), калибровка = роль (селективна/знаковая) — принцип эквивалентности в ERR.
> _Caveat:_ Принцип эквивалентности классичен; вклад — ERR-переобрамление (гравитация=Rule vs калибровка=Role), не новый результат.

---

## #274 - `src/foundation/GravitySymSquareGauge.v` - score 2 (methods)

**Gravity sym-square gauge over Q: graviton + dilaton from the symmetric square**

- **Topic.** A triangular number, symmetric/antisymmetric square dimensions, spin-2/1/0 dimensions, the tensor splits, sym^2(3) is graviton + dilaton, antisym^2(3) is so(3), and kappa.
- **Role.** Gravity leaf (graviton as sym-square gauge; the 'double copy' hypothesis H3). Uses a local section hypothesis (discharged), axioms=0. Self-contained.
- **Counts.** Qed 2 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ тензорное произведение спин-1; симм/антисимм квадрат. _Roles:_ симметричный квадрат = роль (гравитон+дилатон); double-copy гипотеза H3. _Rules:_ sym2_3_is_graviton_plus_dilaton; antisym2_3_is_so3; gravity_is_sym_square_gauge. _P4:_ конечные размерности (Element); гравитон = симм. квадрат калибровки (H3 — локальная гипотеза, разряжена, axioms=0).
- **Classical counterpart.** That the symmetric square of a spin-1 (vector) gives spin-2 (graviton) + spin-0 (dilaton) — the 'double copy' / tensor decomposition — is standard; NEW only as a small Q instance (uses a local section hypothesis H3, discharged; axioms=0).
- **Tags.** foundation, gravity, double-copy, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `tri/dim_sym2/dim_antisym2/spin2_dim/spin1_dim/spin0_dim/tri_double/sym2_dof/tensor_splits/dim_sym2_4/dim_antisym2_4/split_4` | Definition/Theorem | размерности симм/антисимм квадрата |
| `sym2_3_is_graviton_plus_dilaton/antisym2_3_is_so3/vector_tensor_3/kappa/kappa_4/gravity_is_sym_square_gauge` | Theorem | ★ симм²(3) = гравитон+дилатон |

**Key lemmas (deep):**

- **`sym2_3_is_graviton_plus_dilaton`** - Симметричный квадрат спин-1 (вектора) = спин-2 (гравитон) + спин-0 (дилатон), антисимметричный = so(3) над Q — стандартное тензорное разложение / «double copy» (гипотеза H3). Использует локальную секционную гипотезу (разряжается в лемму), не глобальную аксиому. _(gravity, double-copy, graviton, sym-square)_

**Uniqueness - score 2 (methods).** Гравитон как симм-квадрат калибровки над Q: симм²(спин-1) = гравитон + дилатон, антисимм² = so(3).
> _Caveat:_ Тензорное разложение / double-copy стандартно; Q-инстанс (гипотеза H3, локальная) без нового результата.

---

## #275 - `src/foundation/GRQFTDiscriminantBridge.v` - score 3 (new-framing)

**GR-QFT discriminant bridge over Q: one discriminant classifies rotation/boost (vein A)**

- **Topic.** Trace/det/discriminant (tr^2-4det), several SL(2) elements (rot-345/90, boost-345/P, parabolic), elliptic/hyperbolic/parabolic types, rotations preserve Euclid / boosts preserve Minkowski, on-circle/on-hyperbola, isometries, boost-345 discriminant a square, 32 not a square, timelike/null/spacelike-345, and GR-QFT one discriminant.
- **Role.** Vein-A leaf (one discriminant unifies GR/QFT transformation types). Comment 'HYPOTHESIS' false-positive (axioms=0). Self-contained (QArith).
- **Counts.** Qed 5 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ SL(2)-элементы; дискриминант tr²−4det. _Roles:_ дискриминант = роль-классификатор (elliptic/hyperbolic/parabolic = rotation/boost/null). _Rules:_ boost345_disc_square; rot345_elliptic; boost345_hyperbolic; gr_qft_one_discriminant. _P4:_ конечные SL(2)-элементы над Q (Element); ОДИН дискриминант классифицирует и поворот (QFT/евклид) и буст (GR/Минковский) — вена A.
- **Classical counterpart.** The classification of SL(2) elements as elliptic/hyperbolic/parabolic by the trace discriminant (tr^2-4det), with rotations elliptic (Euclidean isometries) and boosts hyperbolic (Minkowski isometries), is classical; NEW is the vein-A bridge that one discriminant unifies GR (boost/Minkowski) and QFT (rotation/Euclidean), e.g. boost-345 has a square discriminant.
- **Tags.** foundation, discriminant, sl2, vein-A, gr-qft, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `mtr/mdet/mdisc/disc_is_tr2_minus_4det/r_a/r_c/q_a/.../rot345_sl2/rot90_sl2/boost345_sl2/boostP_sl2/par_sl2/rot345_elliptic/rot90_elliptic/boost345_hyperbolic/boostP_hyperbolic/par_parabolic` | Definition/Theorem | ★ дискриминант классифицирует elliptic/hyperbolic/parabolic |
| `rotation_preserves_euclid/boost_preserves_mink/rot345_on_circle/boost345_on_hyperbola/rot345_euclid_isometry/boost345_mink_isometry/boost345_disc/_disc_square/boost345_eigs/boostP_disc/thirtytwo_not_square/mink/euclid/timelike_345/null_on_cone/spacelike_345/euclid_no_null_offorigin/gr_qft_one_discriminant` | Theorem | ★ один дискриминант объединяет GR (буст) и QFT (поворот) |

**Key lemmas (deep):**

- **`gr_qft_one_discriminant`** - ОДИН дискриминант tr²−4det классифицирует SL(2)-элементы: поворот elliptic (евклидова изометрия, QFT/компактная сторона), буст hyperbolic (изометрия Минковского, GR-сторона), параболик null. boost-345 (пифагор) имеет КВАДРАТНЫЙ дискриминант → рациональные собственные значения (вена A). Объединяет GR и QFT через одну дискриминантную границу. _(discriminant, sl2, elliptic-hyperbolic, vein-A, gr-qft)_

**Uniqueness - score 3 (new-framing).** GR-QFT дискриминантный мост над Q: один дискриминант tr²−4det классифицирует поворот (elliptic/евклид/QFT) и буст (hyperbolic/Минковский/GR); boost-345 имеет квадратный дискриминант (вена A).
> _Caveat:_ Классификация SL(2) по дискриминанту (elliptic/hyperbolic/parabolic) классична; вклад — вена-A объединение GR/QFT через одну дискриминантную границу, не новый результат.

---

## #276 - `src/foundation/GRQFTSynthesis.v` - score 2 (new-framing)

**GR-QFT synthesis over Q: Lorentz 6 generators = 3 boosts (GR) + 3 rotations (QFT)**

- **Topic.** A sector/plane, involves-time, plane sectors, is-boost/is-rot, n-boosts/n-rots, Lorentz 6 generators, three boosts + three rotations, boost iff time, boost sector hyperbolic/Minkowski, rotation sector elliptic/Euclid, rotations are SU(2) generators, SU(2) compact and gauge, and the lightcone boundary.
- **Role.** Synthesis leaf (Lorentz = GR boosts + QFT rotations; with GRQFTDiscriminantBridge). Self-contained.
- **Counts.** Qed 1 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ секторы Лоренца; бусты/повороты. _Roles:_ узел-синтез: 6 генераторов = 3 буста (GR) + 3 поворота (QFT/SU2). _Rules:_ lorentz_6_generators; boost_iff_time; rotations_are_su2_generators. _P4:_ конечные секторы (Element); Лоренц = 3 буста (гиперболич./Минковский) + 3 поворота (эллиптич./евклид/SU2).
- **Classical counterpart.** That the Lorentz group has 6 generators (3 boosts, 3 rotations), boosts involve time (hyperbolic/Minkowski), rotations are SU(2) (elliptic/Euclidean/compact gauge) is standard; here a synthesis over Q.
- **Tags.** foundation, lorentz, gr-qft, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `Sector/Plane/involves_time/plane_sector/all_planes/is_boost/is_rot/n_boosts/n_rots/lorentz_6_generators/three_boosts_three_rotations` | Definition/Theorem | ★ 6 генераторов = 3 буста + 3 поворота |
| `boost_iff_time/boost_sector_hyperbolic/_mink/rotation_sector_elliptic/_euclid/rotations_are_su2_generators/su2_is_compact_and_gauge/su2_rotates_space/lightcone_boundary/gr_qft_synthesis` | Theorem | ★ бусты=GR/Минковский, повороты=QFT/SU2 |

**Key lemmas (deep):**

- **`gr_qft_synthesis`** - Группа Лоренца (6 генераторов) расщепляется на 3 буста (гиперболические, Минковский, GR-сторона) и 3 поворота (эллиптические, евклид, SU(2)/компактная калибровка, QFT-сторона) над Q. Синтез GRQFTDiscriminantBridge: boost⟺time, rotations=SU(2). Стандартная теория групп, объединённая через дискриминант. _(lorentz, boost-rotation, su2, gr-qft)_

**Uniqueness - score 2 (new-framing).** Синтез GR-QFT над Q: Лоренц = 3 буста (GR/Минковский) + 3 поворота (QFT/SU2/евклид), boost⟺время.
> _Caveat:_ Структура группы Лоренца (бусты+повороты) стандартна; вклад — объединение GR/QFT-сторон через дискриминант, не новый результат.

---

## #277 - `src/foundation/H1AlgebraicDecider.v` - score 3 (new-framing)

**H1 algebraic decider over Q: sound+complete decider for algebraic element vs role-limit (vein A, HIGHLIGHTS H1)**

- **Topic.** A z-sequence and membership, divide-abs-le, gcd-1/relatively-prime bridges, root candidates, a boolean decider (sound, complete), decide-algebraic-element, and concrete cases (quad true, sqrt(1/2) false, cubic true).
- **Role.** Vein-A H1 flagship (the constructivity-boundary decider; HIGHLIGHTS H1 'finitization boundary = constructivity boundary'). Self-contained.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: ZArith
- **E/R/R.** _Elements:_ кандидаты корней; целочисленные последовательности. _Roles:_ decider = РАЗРЕШИМАЯ роль (алгебраический Element vs role-limit). _Rules:_ decideb_sound; decideb_complete; decide_alg_element. _P4:_ конечные кандидаты (Element); ПОЛНЫЙ+КОРРЕКТНЫЙ решатель: квадрат=Element, sqrt(1/2)=role-limit, куб=Element — вена A H1 (граница конструктивности).
- **Classical counterpart.** The rational-root test (a decidable procedure for whether a polynomial has a rational/algebraic root via bounded candidate denominators) is classical; NEW is the H1 vein-A flagship framing: a sound+complete DECIDER for 'is this an algebraic element vs a role-limit' (quad yes, sqrt(1/2) no, cubic yes).
- **Tags.** foundation, H1, decider, constructivity-boundary, vein-A, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `zseq/in_zseq_lower/in_zseq/divide_abs_le/gcd1_rp/rp_gcd1/root_candidates/decideb/decideb_sound/decideb_complete` | Definition/Theorem | ★ решатель корректен И полон |
| `decide_alg_element/decideb_quad_true/decideb_sqrt_half_false/decideb_cubic_true/h1_algebraic_decider` | Theorem | ★ квадрат=Element, sqrt(1/2)=role-limit, куб=Element |

**Key lemmas (deep):**

- **`decideb_complete`** - КОРРЕКТНЫЙ+ПОЛНЫЙ разрешитель «алгебраический Element vs role-limit» через рациональный-корневой тест (ограниченные кандидаты-знаменатели) над Z: квадратное уравнение даёт Element, sqrt(1/2) — role-limit, кубическое — Element. Это H1-флагман: финитизационная граница СДЕЛАНА разрешимой = граница конструктивности (HIGHLIGHTS H1). Ядро вены A в полной общности. _(H1, decider, rational-root, constructivity-boundary, vein-A, flagship)_

**Uniqueness - score 3 (new-framing).** H1 алгебраический решатель над Z (вена A флагман, HIGHLIGHTS H1): КОРРЕКТНЫЙ+ПОЛНЫЙ decider «алгебраический Element vs role-limit» (квадрат да, sqrt(1/2) нет, куб да) — финитизационная граница = граница конструктивности.
> _Caveat:_ Рациональный-корневой тест классичен; уникальность — в его роли как РАЗРЕШИМОЙ границы Element/role-limit (= конструктивности), синтез-наблюдение, не новый алгоритм.

---

## #278 - `src/foundation/H1AlgebraicElement.v` - score 3 (new-framing)

**H1 algebraic element over Q: rational-root criterion defines the element boundary (vein A)**

- **Topic.** A polynomial-homomorphism, length-snoc, p divides trail, lead/q-div-lead, a rational root, the rational-root criterion, a bounded denominator, an AlgElement, relatively-prime 1/2, quad is element, and sqrt(1/2) is a role-limit.
- **Role.** Vein-A H1 leaf (the algebraic element boundary; with H1AlgebraicDecider). Self-contained.
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: ZArith
- **E/R/R.** _Elements:_ алгебраические значения; кандидаты корней. _Roles:_ алгебраический Element = роль (проходит рациональный-корневой критерий). _Rules:_ rational_root_criterion; denominator_bounded; sqrt_half_role_limit. _P4:_ конечные кандидаты (Element); алгебраическое значение = Element ⟺ проходит критерий: квадрат=Element, sqrt(1/2)=role-limit (вена A H1).
- **Classical counterpart.** The rational-root criterion (numerator divides the constant, denominator divides the lead) bounding algebraic roots is classical; NEW is the H1 vein-A framing that an algebraic value is an 'element' iff it passes (quad is element, sqrt(1/2) is a role-limit).
- **Tags.** foundation, H1, algebraic-element, vein-A, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `phom/len_snoc/p_div_trail/phom_lead_mod/q_div_lead/rat_root/rational_root_criterion/denominator_bounded` | Definition/Theorem | ★ рациональный-корневой критерий, ограниченный знаменатель |
| `AlgElement/rel_prime_1_2/quad_is_element/sqrt_half_role_limit/h1_algebraic_boundary` | Theorem | ★ квадрат=Element, sqrt(1/2)=role-limit |

**Key lemmas (deep):**

- **`h1_algebraic_boundary`** - Определяет H1-границу через рациональный-корневой критерий (числитель\|константа, знаменатель\|старший): алгебраическое значение есть Element ⟺ проходит, с ограниченным знаменателем. Квадрат=Element, sqrt(1/2)=role-limit над Q. Конструктивная сторона H1AlgebraicDecider — вена A. _(H1, rational-root, algebraic-element, vein-A)_

**Uniqueness - score 3 (new-framing).** H1 алгебраический элемент над Q (вена A): рациональный-корневой критерий определяет границу Element/role-limit (квадрат=Element, sqrt(1/2)=role-limit), знаменатель ограничен.
> _Caveat:_ Рациональный-корневой критерий классичен; вклад — его роль как H1-границы конструктивности (Element/role-limit), не новый критерий.

---

## #279 - `src/foundation/H1ConstructivityComputable.v` - score 3 (new-framing)

**H1 constructivity computable over Q: a computable element-test sorts matrices (vein A)**

- **Topic.** A boolean is-element-b (correct, reflected), a boolean is-role-limit-b (correct), the Z-discriminant, a sort-matrix, sorts of boost-345/Fibonacci/Pell/order-6, runs at 36/5, and H1 sort is computable.
- **Role.** Vein-A H1 leaf (computable element-sort with reflection). Self-contained.
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** Stdlib: ZArith
- **E/R/R.** _Elements:_ матрицы (boost345/Fibonacci/Pell/order6); дискриминанты. _Roles:_ computable-тест = роль (Element vs role-limit, булева рефлексия). _Rules:_ is_element_b_correct; is_element_reflect; H1_sort_is_computable. _P4:_ конечные матрицы (Element); ВЫЧИСЛИМЫЙ тест с рефлексией сортирует boost345/Fibonacci/Pell/order6 на Element vs role-limit (вена A H1).
- **Classical counterpart.** Boolean-reflected decidability of perfect-square / integer-trace tests is standard; NEW is the H1 vein-A framing of a COMPUTABLE element-test with reflection that sorts boost-345/Fibonacci/Pell/order-6 matrices into element vs role-limit.
- **Tags.** foundation, H1, computable, vein-A, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `is_element_b/is_element_b_correct/is_element_reflect/is_role_limit_b/_correct/mdiscZ/sort_matrix` | Definition/Theorem | ★ вычислимый тест (булева рефлексия) |
| `sort_boost345/sort_fibonacci/sort_pell/sort_order6/run_36/run_5/H1_sort_is_computable` | Theorem | ★ сортировка матриц вычислима |

**Key lemmas (deep):**

- **`H1_sort_is_computable`** - ВЫЧИСЛИМЫЙ тест Element-vs-role-limit (с булевой рефлексией is_element_reflect) сортирует конкретные матрицы — boost-345/Pell (Element), Fibonacci/golden (role-limit), order-6 — над Z. Делает H1-границу не только разрешимой, но и исполнимо вычислимой (vm_compute-готовой). Вена A. _(H1, computable, reflection, vein-A)_

**Uniqueness - score 3 (new-framing).** H1 вычислимость над Z (вена A): вычислимый тест с булевой рефлексией сортирует матрицы (boost345/Pell=Element, Fibonacci=role-limit) — H1-граница исполнима.
> _Caveat:_ Булева рефлексия разрешимости стандартна; вклад — её применение к H1-границе Element/role-limit (исполнимая сортировка), не новый метод.

---

## #280 - `src/foundation/H1ConstructivityDecidable.v` - score 3 (new-framing)

**H1 constructivity decidable over Z: element-or-role-limit is a theorem (vein A flagship)**

- **Topic.** An ElementZ and role-limit, a decide-elementZ, element-or-role-limit, not-both, element-36, role-limit-5/32/-3, and the H1 constructive half is a theorem.
- **Role.** Vein-A H1 flagship (the constructive dichotomy as a theorem). Self-contained.
- **Counts.** Qed 5 / Admitted 0 / axioms 0
- **Imports.** Stdlib: ZArith
- **E/R/R.** _Elements:_ целые (Element=квадрат vs role-limit). _Roles:_ разрешимость = роль (Element ∨ role-limit, не оба). _Rules:_ decide_elementZ; element_or_rolelimit; not_both. _P4:_ конечные целые (Element); «Element ИЛИ role-limit (и не оба)» — ТЕОРЕМА (36=Element, 5/32/-3=role-limit); конструктивная половина H1 доказана.
- **Classical counterpart.** Deciding whether an integer is a perfect square is classical; NEW is the H1 vein-A flagship statement that the 'constructive half' (element OR role-limit, not both) is a THEOREM (36 element, 5/32/-3 role-limit).
- **Tags.** foundation, H1, decidable, dichotomy, vein-A, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `ElementZ/role_limit/decide_elementZ/element_or_rolelimit/not_both` | Definition/Theorem | ★ Element ∨ role-limit (не оба) — теорема |
| `element_36/rolelimit_5/rolelimit_32/rolelimit_neg3/H1_constructive_half_is_theorem` | Theorem | ★ 36=Element, 5/32/-3=role-limit |

**Key lemmas (deep):**

- **`H1_constructive_half_is_theorem`** - Конструктивная ПОЛОВИНА H1 — «всякое целое есть Element (перфект-квадрат) ИЛИ role-limit, и не оба» — доказана как ТЕОРЕМА над Z (decide_elementZ разрешает; 36=Element, 5/32/-3=role-limit). Это чистейшая формулировка вены A: дихотомия финитизации конструктивна и разрешима. Корень H1 (HIGHLIGHTS). _(H1, decidable, dichotomy, vein-A, flagship)_

**Uniqueness - score 3 (new-framing).** H1 разрешимость над Z (вена A флагман): «Element ∨ role-limit, не оба» — ТЕОРЕМА (decide_elementZ; 36=Element, 5/32/-3=role-limit). Конструктивная дихотомия финитизации.
> _Caveat:_ Разрешимость перфект-квадрата классична; уникальность — в формулировке дихотомии Element/role-limit как доказанной конструктивной теоремы (H1), не в новом тесте.

---

## #281 - `src/foundation/H1CubicConstructivity.v` - score 3 (new-framing)

**H1 cubic constructivity over Z: perfect-cube element boundary (vein A)**

- **Topic.** A CubeElement vs cube-role-limit, cubeelement-iff-int-cube, a boolean is-cube-nat (correct), Z-to-nat cube, int-cube-iff-abs, decide-cubeelement, cube-element-or-role-limit, cube-not-both, cube-element-8, and cube-role-limits 2/3/5/9.
- **Role.** Vein-A H1 leaf (cube version of the boundary). Self-contained.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: ZArith
- **E/R/R.** _Elements:_ целые (Element=куб vs role-limit). _Roles:_ куб-разрешимость = роль (cube-Element ∨ role-limit). _Rules:_ decide_cubeelement; cube_element_or_rolelimit; cube_not_both. _P4:_ конечные целые (Element); перфект-куб граница: 8=Element, 2/3/5/9=role-limit (вена A H1, степень 3).
- **Classical counterpart.** Deciding whether an integer is a perfect cube is classical; NEW is the H1 vein-A extension to cubes (cube-element vs role-limit, 8 element, 2/3/5/9 role-limit).
- **Tags.** foundation, H1, cube, vein-A, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `CubeElement/cube_role_limit/cubeelement_iff_intcube/is_cube_nat/_correct/Z2Nat_cube/intcube_iff_abs/decide_cubeelement` | Definition/Theorem | ★ перфект-куб разрешим |
| `cube_element_or_rolelimit/cube_not_both/cube_element_8/cube_rolelimit_2/_3/_5/_9/H1_cubic_constructive_half` | Theorem | ★ 8=Element, 2/3/5/9=role-limit |

**Key lemmas (deep):**

- **`H1_cubic_constructive_half`** - H1-граница для КУБОВ: перфект-куб = Element, иначе role-limit, разрешимо (8=Element, 2/3/5/9=role-limit) над Z. Расширяет вену A с квадратов на кубы — граница финитизации стратифицирована по степени (ср. CubicCouplingSpectrum, H1GeneralDegreeConstructivity). _(H1, cube, decidable, vein-A)_

**Uniqueness - score 3 (new-framing).** H1 кубическая конструктивность над Z (вена A): перфект-куб граница (8=Element, 2/3/5/9=role-limit), разрешима — степень-3 стратификация финитизации.
> _Caveat:_ Разрешимость перфект-куба классична; вклад — кубическая H1-граница Element/role-limit, не новый тест.

---

## #282 - `src/foundation/H1GeneralDegreeConstructivity.v` - score 3 (new-framing)

**H1 general-degree constructivity over Z: uniform perfect-power decider (vein A)**

- **Topic.** A z-power-abs, z-power-ge-base, a root-abs bound, root candidates (membership), is-kth-power (correct), decide-perfect-power, perfect-power-or-not, and concrete cases (sq-36 yes / sq-5 no, cube-8 yes / cube-2 no / cube-(-8) yes, quart-16 yes / quart-5 no).
- **Role.** Vein-A H1 leaf (uniform-degree perfect-power decider). Self-contained.
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib: ZArith
- **E/R/R.** _Elements:_ целые (Element=перфект-k-степень vs role-limit); все степени. _Roles:_ uniform-решатель = роль (одна процедура для всех степеней). _Rules:_ is_kth_power_correct; decide_perfect_power; perfect_power_or_not. _P4:_ конечные кандидаты (Element); ОДИН решатель перфект-k-степени для ВСЕХ степеней (sq/cube/quart): 36/8/16=Element, 5/2/5=role-limit (вена A H1).
- **Classical counterpart.** Deciding whether an integer is a perfect k-th power is classical; NEW is the H1 vein-A UNIFORM result: one decision procedure handles all degrees (square/cube/quartic), bounding roots.
- **Tags.** foundation, H1, general-degree, vein-A, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `zpow_abs/zpow_ge_base/root_abs_bound/root_cands/In_root_cands/is_kth_power/_correct/decide_perfect_power/perfect_power_or_not` | Definition/Theorem | ★ uniform решатель перфект-k-степени |
| `pp_sq_36/pp_sq_5/pp_cube_8/pp_cube_2/pp_cube_neg8/pp_quart_16/pp_quart_5/H1_degree_uniform_decidable` | Theorem | ★ все степени: 36/8/16=Element, 5/2/5=role-limit |

**Key lemmas (deep):**

- **`H1_degree_uniform_decidable`** - ОДНА равномерная процедура решает перфект-k-степень для ВСЕХ степеней k (квадрат/куб/кварта), с границей на корни — 36/8/16=Element, 5/2/5=role-limit над Z. Унифицирует H1-границу по степеням: финитизация разрешима в любой степени. Вершина вены A в общей степени. _(H1, general-degree, uniform, vein-A)_

**Uniqueness - score 3 (new-framing).** H1 общая степень над Z (вена A): ОДИН uniform-решатель перфект-k-степени для всех степеней (sq/cube/quart), 36/8/16=Element vs 5/2/5=role-limit.
> _Caveat:_ Разрешимость перфект-степени классична; вклад — равномерная по степени H1-граница, не новый алгоритм.

---

## #283 - `src/foundation/H1RationalDegreeUniform.v` - score 3 (new-framing)

**H1 rational-degree uniform over Q: perfect-power element boundary on the rationals (vein A)**

- **Topic.** A q-power (numerator/denominator/morphism/inject), rational-kth-power-is-perfect, a QkthElement (iff int power), decide-QkthElement, Qkth-element-or-not, and cases (sqrt-36 yes, cbrt-8 yes, cbrt-2 no, sqrt-5 no, quart-5 no).
- **Role.** Vein-A H1 leaf (the boundary lifted to Q, uniform degree; caps the H1 cluster). Self-contained (QArith).
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ рациональные (Element=перфект-k-степень над Q vs role-limit). _Roles:_ uniform-решатель над Q = роль (числитель И знаменатель — k-степени). _Rules:_ rational_kth_power_is_perfect; decide_QkthElement; Qkth_element_or_not. _P4:_ конечные рациональные (Element); H1-граница ПОДНЯТА на Q, равномерно по степени: sqrt(36)/cbrt(8)=Element, cbrt(2)/sqrt(5)/quart(5)=role-limit (вена A).
- **Classical counterpart.** That a rational is a perfect k-th power iff its reduced numerator and denominator both are is classical; NEW is the H1 vein-A LIFT to Q with a uniform decider (sqrt-36 yes, cbrt-8 yes, cbrt-2 no, sqrt-5 no, quart-5 no).
- **Tags.** foundation, H1, rational, vein-A, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `qpow/qpow_num/_den/_morphism/_inject/rational_kth_power_is_perfect/QkthElement/_iff_intpower/decide_QkthElement` | Definition/Theorem | ★ перфект-k-степень над Q разрешима |
| `Qkth_element_or_not/qkth_sqrt36/qkth_cbrt8/qkth_cbrt2_no/qkth_sqrt5_no/qkth_quart5_no/H1_rational_degree_uniform` | Theorem | ★ sqrt36/cbrt8=Element, cbrt2/sqrt5/quart5=role-limit |

**Key lemmas (deep):**

- **`H1_rational_degree_uniform`** - Поднимает H1-границу на РАЦИОНАЛЬНЫЕ числа, равномерно по степени: q — перфект-k-степень ⟺ числитель И знаменатель суть k-степени, разрешимо (sqrt36/cbrt8=Element, cbrt2/sqrt5/quart5=role-limit) над Q. Завершает H1-кластер: финитизационная граница конструктивна на Q в любой степени. Вена A в полной общности (HIGHLIGHTS H1). _(H1, rational, uniform-degree, vein-A, flagship)_

**Uniqueness - score 3 (new-framing).** H1 рациональная равномерность над Q (вена A, завершает H1-кластер): перфект-k-степень над Q разрешима равномерно по степени (sqrt36/cbrt8=Element, cbrt2/sqrt5/quart5=role-limit).
> _Caveat:_ Критерий рациональной k-степени классичен; вклад — равномерная H1-граница Element/role-limit над Q (= граница конструктивности), синтез-наблюдение.

---

## #284 - `src/foundation/HeavyWallAudit.v` - score 3 (synthesis+observation)

**Heavy-wall audit over Q: domain axioms classified eliminable vs load-bearing (honesty anchor)**

- **Topic.** A domain-axiom and axiom-kind, a wall, axiom-wall/kind/eliminable, all axioms, heavy walls carry axioms, walls correct, axioms classified, is-eliminable / is-load-bearing, counts of eliminable / load-bearing.
- **Role.** Honesty anchor (the axiom audit; mirrors CLAUDE.md's HeavyWallAudit). Self-contained.
- **Counts.** Qed 1 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ доменные аксиомы (NS, zeta); тяжёлые стены. _Roles:_ аудит = роль-классификатор (eliminable vs load-bearing). _Rules:_ heavy_walls_carry_axioms; is_eliminable; is_load_bearing. _P4:_ конечная классификация (Element); ЧЕСТНО: тяжёлые стены (NS/zeta) несут аксиомы (eliminable vs load-bearing), foundation = 0-аксиом.
- **Classical counterpart.** No classical counterpart — an internal HONEST audit (matching CLAUDE.md) classifying the heavy-wall domain axioms (Navier-Stokes, zeta) as eliminable vs load-bearing, and confirming the foundation is 0-axiom.
- **Tags.** foundation, honesty, axiom-audit, synthesis+observation

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `of/DomainAxiom/AxKind/Wall/ax_wall/ax_kind/ax_eliminable/all_axioms` | Definition/Theorem | доменные аксиомы, классификация |
| `heavy_walls_carry_axioms/walls_correct/axioms_classified/is_eliminable/is_load_bearing/n_eliminable/n_load_bearing/n_eliminable_eq/n_load_bearing_eq/heavy_wall_audit` | Theorem | ★ eliminable vs load-bearing (честный счёт) |

**Key lemmas (deep):**

- **`heavy_wall_audit`** - ЧЕСТНЫЙ аудит (зеркало CLAUDE.md): тяжёлые стены (Navier-Stokes, zeta) НЕСУТ доменные аксиомы, классифицированные на eliminable (provable structures) vs load-bearing (B_coeff_bounded) над Q. Подтверждает: foundation = 0-аксиом, аксиомы только на стенах. Ключевой якорь честности проекта против «0 axioms» over-claim. _(honesty, axiom-audit, load-bearing, calibration)_

**Uniqueness - score 3 (synthesis+observation).** Аудит тяжёлых стен над Q (якорь честности): доменные аксиомы (NS/zeta) классифицированы eliminable vs load-bearing, foundation подтверждена 0-аксиомной.
> _Caveat:_ Внутренний honesty-аудит; ценность — точная калибровка где аксиомы (стены) vs где их нет (foundation), не новый математический результат.

---

## #285 - `src/foundation/HeliumBoundary.v` - score 2 (new-framing)

**Helium boundary over Q: He eigenvalue rational iff discriminant is a square (vein A)**

- **Topic.** A diagonal-spectrum element, hydrogen-like (element), a He CI matrix and discriminant, the He CI eigenvalue is rational iff a square, the He square iff 117, helium role-limit, and the helium-vs-hydrogen boundary.
- **Role.** Vein-A atomic leaf (He spectral boundary via discriminant). Self-contained (QArith).
- **Counts.** Qed 5 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ спектр гелия (CI); дискриминант. _Roles:_ перфект-квадрат дискриминант = роль (He с.з. рационально ⟺ квадрат). _Rules:_ heCI_eigenvalue_iff_square; helium_role_limit; helium_vs_hydrogen_boundary. _P4:_ конечная CI-матрица He над Q (Element); He с.з. рационально ⟺ дискриминант-квадрат (He=role-limit, H=Element) — вена A.
- **Classical counterpart.** That a CI helium eigenvalue is rational iff its discriminant is a perfect square (else a role-limit) is an instance of the rational-eigenvalue criterion; NEW is the vein-A application to the He vs H spectral boundary.
- **Tags.** foundation, helium, discriminant, vein-A, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `diagonal_spectrum_element/hydrogenlike/hydrogenlike_element/heCI/heCI_disc/heCI_eigenvalue_iff_square/he_square_iff_117` | Definition/Theorem | ★ He с.з. рационально ⟺ квадрат дискриминанта |
| `helium_role_limit/helium_vs_hydrogen_boundary` | Theorem | ★ He=role-limit, H=Element |

**Key lemmas (deep):**

- **`helium_vs_hydrogen_boundary`** - Граница H/He через дискриминант: водородоподобный спектр — Element (рационален), гелиевый CI — role-limit (дискриминант не квадрат, he_square_iff_117) над Q. Вена A применённая к атомной спектроскопии: точная граница вычислимости спектра между H и He. _(helium, discriminant, spectral-boundary, vein-A)_

**Uniqueness - score 2 (new-framing).** Граница гелия над Q (вена A): He с.з. рационально ⟺ дискриминант-квадрат; водород=Element, гелий=role-limit.
> _Caveat:_ Критерий рационального с.з. через дискриминант элементарен; вклад — вена-A применение к границе H/He, не новый результат.

---

## #286 - `src/foundation/HeliumStructure.v` - score 2 (methods)

**Helium structure over Q: variational ground state, Pauli, ionization ratio**

- **Topic.** Z=2, He+ energies (ground/excited/scaled), screening sigma and Z_eff, a variational energy (below -2, above -3, above the naive sum), a positive correlation correction, second/first ionization, first < second, ionization ratio > 2, Pauli-allowed states, He 1s^2 same-spin forbidden, ortho/para He, and Pauli symmetric.
- **Role.** E/R/R atomic-structure leaf (helium). Self-contained (QArith).
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ He (Z=2); вариационная энергия; экранирование. _Roles:_ правило Паули = роль (1s² антисимметрия); ионизация как роль. _Rules:_ he_1s2_same_spin_forbidden; ionization_ratio_above_2; correlation_is_positive. _P4:_ конечные оценки над Q (Element); гелий в E/R/R-форме (вариация, Паули, ионизация).
- **Classical counterpart.** Helium structure — variational ground state, screening/Z_eff, correlation correction, the two ionization energies, Pauli (para/ortho), the ionization ratio > 2 — is textbook; NEW only as an exact rational instance.
- **Tags.** foundation, helium, atomic, pauli, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `Z_He/he_plus_E/_ground/_excited/_n3/_scaled_n1/_n2/_n3/screening_sigma/Z_eff/_value/he_variational/_value/_below_minus_2/_above_minus_3/variational_above_naive_sum/he_correlation_correction/correlation_is_positive` | Definition/Theorem | вариационная энергия, экранирование |
| `second_ionization/_value/first_ionization/_value/_positive/first_less_than_second/ionization_ratio_above_2/same_quantum_state/pauli_allowed/he_1s2_allowed/he_1s2_same_spin_forbidden/ortho_he_allowed/para_he_allowed/pauli_symmetric/helium_structure_complete` | Theorem | ★ Паули, ионизация (ratio>2) |

**Key lemmas (deep):**

- **`he_1s2_same_spin_forbidden`** - Гелий 1s² с одинаковым спином ЗАПРЕЩЁН (Паули-антисимметрия), ortho/para He различены, ионизационное отношение >2 над Q — корректная E/R/R-формализация структуры гелия. Учебная атомная физика. _(helium, pauli, ionization, err)_

**Uniqueness - score 2 (methods).** Структура гелия над Q: вариационное основное состояние (между −2 и −3), экранирование/Z_eff, Паули (1s² same-spin запрещён, ortho/para), ионизационное отношение >2.
> _Caveat:_ Структура гелия (вариация/Паули/ионизация) — учебная физика; Q-инстанс без нового результата.

---

## #287 - `src/foundation/HierarchyLaplacian.v` - score 2 (new-framing)

**Hierarchy Laplacian over Q: spectrum rational iff discriminant is a square (vein A)**

- **Topic.** A Laplacian trace/determinant/discriminant, an eigenvalue, is-square-Q, the spectrum is rational iff the discriminant is a square, a Laplacian diagonal element, a Laplacian golden discriminant, a spectrum side, and the spectrum H1 disjoint.
- **Role.** Vein-A leaf (Laplacian spectral boundary). Self-contained (QArith).
- **Counts.** Qed 2 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ граф-лапласиан; дискриминант спектра. _Roles:_ перфект-квадрат дискриминант = роль (спектр рационален ⟺ квадрат). _Rules:_ spectrum_rational_iff_disc_square; laplacian_golden_disc; spectrum_h1_disjoint. _P4:_ конечный лапласиан над Q (Element); спектр рационален ⟺ дискриминант-квадрат (диагональ=Element, золотой=role-limit) — вена A.
- **Classical counterpart.** That a graph-Laplacian's spectrum is rational iff its discriminant is a perfect square (else a golden/irrational role-limit) is an instance of the rational-eigenvalue criterion; NEW is the vein-A framing of the Laplacian spectral boundary disjoint from the H1 wall.
- **Tags.** foundation, laplacian, discriminant, vein-A, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `cl_tr/cl_det/cl_disc/cl_disc_eq/is_eigenvalue/is_square_Q/spectrum_rational_iff_disc_square` | Definition/Theorem | ★ спектр рационален ⟺ дискриминант-квадрат |
| `laplacian_diagonal_element/laplacian_golden_disc/SpectrumSide/spectrum_h1_disjoint/hierarchy_laplacian_spectrum` | Definition/Theorem | ★ диагональ=Element, золотой=role-limit |

**Key lemmas (deep):**

- **`spectrum_rational_iff_disc_square`** - Спектр граф-лапласиана рационален ⟺ дискриминант — перфект-квадрат (диагональный лапласиан=Element, золотой дискриминант=role-limit) над Q. Вена A применённая к лапласовскому спектру; spectrum_h1_disjoint связывает с H1-границей. Ср. DiscriminantCompleteEigenvalue. _(laplacian, discriminant, spectral-boundary, vein-A)_

**Uniqueness - score 2 (new-framing).** Иерархический лапласиан над Q (вена A): спектр рационален ⟺ дискриминант-квадрат (диагональ=Element, золотой=role-limit), дизъюнктно с H1.
> _Caveat:_ Критерий рационального спектра через дискриминант элементарен; вклад — вена-A применение к лапласиану, не новый результат.

---

## #288 - `src/foundation/HydrogenStructure.v` - score 2 (methods)

**Hydrogen structure over Q: n^2 degeneracy, selection rules, atom is emergent**

- **Topic.** Free/bound/binding energies, bound below free, positive binding, atom is emergent (emergent info = binding), angular states, degeneracy at n=1..4/10, degeneracy is n^2, total states with spin, the periodic row, and selection rules (s->p/p->s/p->d/d->p allowed, s->s/s->d/p->p/s->f forbidden).
- **Role.** E/R/R atomic-structure leaf (hydrogen). Self-contained.
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ уровни водорода; угловые состояния. _Roles:_ вырождение = роль (n²); правила отбора как роли. _Rules:_ degeneracy_is_n_squared; s_to_p_allowed; s_to_s_forbidden. _P4:_ конечные уровни (Element); n²-вырождение, правила отбора; атом эмерджентен (binding=emergent info).
- **Classical counterpart.** Hydrogen structure — binding energy, n^2 degeneracy, selection rules (s->p allowed, s->s forbidden), the periodic row — is textbook; NEW only as an exact rational instance with 'atom is emergent'.
- **Tags.** foundation, hydrogen, atomic, err, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `E_free/E_bound/E_binding/bound_below_free/binding_value/binding_positive/atom_is_emergent/emergent_info/emergent_equals_binding` | Definition/Theorem | связь, эмерджентность атома |
| `angular_states/degen_n1/_n2/_n3/_n4/degeneracy_is_n_squared/degen_n10/total_states_with_spin/_n2/_n3/periodic_row_4` | Theorem | ★ вырождение = n² |
| `allowed_transition/s_to_p_allowed/p_to_s_allowed/p_to_d_allowed/d_to_p_allowed/s_to_s_forbidden/s_to_d_forbidden/p_to_p_forbidden/s_to_f_forbidden/allowed_symmetric/hydrogen_structure_complete` | Theorem | ★ правила отбора (Δl=±1) |

**Key lemmas (deep):**

- **`degeneracy_is_n_squared`** - Вырождение водорода = n² и правила отбора (Δl=±1: s→p разрешён, s→s запрещён) над Q — корректная E/R/R-формализация структуры водорода. atom_is_emergent: атом эмерджентен, binding=emergent info. Учебная физика. _(hydrogen, degeneracy, selection-rules, err)_

**Uniqueness - score 2 (methods).** Структура водорода над Q: n²-вырождение, правила отбора (Δl=±1), атом эмерджентен (binding=emergent info).
> _Caveat:_ Структура водорода (n²/правила отбора) — учебная физика; Q-инстанс без нового результата.

---

## #289 - `src/foundation/HydrogenThreeFormulas.v` - score 2 (methods)

**Hydrogen three formulas over Q: Lyman/Balmer ratios (verifiable)**

- **Topic.** Hydrogen energy levels, the ground minimum, ionization, transitions (Lyman alpha/beta/gamma, Balmer alpha/beta), the 2-1 level ratio, Lyman alpha is 75% of ionization, and the Balmer/Lyman wavelength ratio.
- **Role.** E/R/R single-system leaf (hydrogen spectrum, verifiable ratios per CLAUDE.md). Self-contained.
- **Counts.** Qed 1 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ уровни водорода; переходы (Lyman/Balmer). _Roles:_ спектральная серия = роль; отношения длин волн как роли. _Rules:_ lyman_alpha_is_75pct_ionization; balmer_lyman_wavelength_ratio; level_ratio_2_1. _P4:_ конечные уровни (Element); Lyman/Balmer отношения точны над Q (верифицируемо: CLAUDE.md Lyman/Balmer=27/5).
- **Classical counterpart.** The hydrogen spectrum, Lyman/Balmer series and their wavelength ratios are textbook; NEW only as exact rational ratios (e.g. Lyman/Balmer) in E/R/R form (a verifiable prediction per CLAUDE.md).
- **Tags.** foundation, hydrogen, lyman-balmer, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `hydrogen_E/H_ground/H_E2/_E3/_E4/ground_is_minimum/ionization_energy/_value/transition/lyman_alpha/_beta/_gamma/balmer_alpha/_beta` | Definition/Theorem | уровни, переходы Lyman/Balmer |
| `level_ratio_2_1/lyman_alpha_is_75pct_ionization/balmer_lyman_wavelength_ratio/hydrogen_three_formulas` | Theorem | ★ отношения длин волн (Lyman/Balmer) |

**Key lemmas (deep):**

- **`balmer_lyman_wavelength_ratio`** - Точные рациональные отношения водородных серий (Lyman α = 75% ионизации, Balmer/Lyman отношение) над Q в E/R/R-форме — машинно-верифицируемое предсказание (CLAUDE.md: Lyman/Balmer=27/5 exact). Стандартная спектроскопия, точно формализованная. _(hydrogen, lyman-balmer, ratio, verifiable)_

**Uniqueness - score 2 (methods).** Водородные три формулы над Q: спектр, Lyman/Balmer переходы, точные отношения длин волн (верифицируемо).
> _Caveat:_ Серии Lyman/Balmer — учебная спектроскопия; вклад — точные Q-отношения в E/R/R-форме, не новая физика.

---

## #290 - `src/foundation/IndivisibleDistinction.v` - score 3 (new-framing)

**Indivisible distinction over Q: quantization from indivisibility (vein C)**

- **Topic.** Pseudo-distinctions lacking exclusivity/exhaustivity, all four necessary, exclusive/exhaustive essential, positive determines negative, exactly one side, a pair without rules contradictory, distinction indivisible, the count is natural / always nonneg, no fractional distinctions, an increment, quantization from distinction, and the process domain forced.
- **Role.** Distinction-spine leaf (indivisibility -> quantization, vein-C). Self-contained.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ различения (неделимые); счётчик различений (натуральный). _Roles:_ неделимость = роль (квантование); все 4 свойства необходимы. _Rules:_ distinction_indivisible; no_fractional_distinctions; quantization_from_distinction. _P4:_ счётчик различений натурален (Element); НЕТ дробных различений → квантование; процессный домен ВЫНУЖДЕН (вена C).
- **Classical counterpart.** That a count is a natural number (no fractional distinctions) and quantization follows from indivisibility is a foundational intuition; NEW is the formal statement that all four distinction properties are necessary and the count being natural forces the process domain (quantization from distinction).
- **Tags.** foundation, distinction, quantization, vein-C, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `pseudo_distinction_no_excl/_no_exh/all_four_necessary/exclusive_essential/exhaustive_essential/positive_determines_negative/exactly_one_side/pair_without_rules_contradictory/distinction_indivisible/without_exclusive_anything/without_exhaustive_gap` | Theorem | ★ все 4 свойства необходимы, различение неделимо |
| `distinction_count_nat/count_is_natural/count_always_nonneg/no_fractional_distinctions/distinction_increment/zero_distinctions/one_distinction/quantization_from_distinction/process_domain_forced/indivisible_distinction_summary` | Theorem | ★ квантование из неделимости; процессный домен вынужден |

**Key lemmas (deep):**

- **`quantization_from_distinction`** - Квантование выводится из НЕДЕЛИМОСТИ различения: счётчик различений натурален, НЕТ дробных различений (no_fractional_distinctions), все 4 свойства необходимы → процессный домен ВЫНУЖДЕН (process_domain_forced) над Q. Вена C: дискретность/квантование не постулат, а следствие неделимости различения. Связь с Binarity, P4-онтологией. _(distinction, quantization, indivisible, vein-C)_

**Uniqueness - score 3 (new-framing).** Неделимое различение над Q (вена C): все 4 свойства необходимы, счётчик натурален (нет дробных различений) → квантование и процессный домен ВЫНУЖДЕНЫ из неделимости.
> _Caveat:_ Квантование из неделимости — основательная интуиция; вклад — формальный вывод «процессный домен вынужден» из свойств различения, не новый физический результат.

---

## #291 - `src/foundation/InterLevelCalculus.v` - score 2 (new-framing)

**Inter-level calculus over Q: every interaction has a boundary (vein A)**

- **Topic.** A scale-flow (nondecreasing, bounded/unbounded), flow element vs role-limit, element excludes role-limit, a constant-element flow, an interaction (foundational), a finite side vs closure side, every interaction has a boundary, and directions distinct.
- **Role.** Vein-A leaf (inter-level boundary calculus). Self-contained (QArith).
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ межуровневые взаимодействия; потоки. _Roles:_ граница = роль (всякое взаимодействие имеет границу: finite vs closure). _Rules:_ every_interaction_has_boundary; flow_element; flow_role_limit. _P4:_ конечные потоки над Q (Element); ВСЯКОЕ межуровневое взаимодействие имеет границу (finite=Element vs closure=role-limit) — вена A.
- **Classical counterpart.** No classical counterpart — a vein-A 'inter-level calculus' where every interaction between levels has a boundary (finite side vs closure side; element vs role-limit flow).
- **Tags.** foundation, inter-level, boundary, vein-A, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `ScaleFlow/nondecreasing/bounded_above/unbounded/flow_element/flow_role_limit/element_excludes_role_limit/flow_element_const` | Definition/Theorem | потоки Element/role-limit |
| `Interaction/Foundational/Side/finite_side/closure_side/every_interaction_has_boundary/Direction/directions_distinct/inter_level_calculus` | Definition/Theorem | ★ всякое взаимодействие имеет границу |

**Key lemmas (deep):**

- **`every_interaction_has_boundary`** - Всякое межуровневое взаимодействие имеет ГРАНИЦУ — конечную (Element) сторону vs замыкающую (role-limit) сторону над Q. Обобщает вену A с конкретных тестов на универсальный «инкремент-уровневое исчисление»: граница финитизации присутствует в каждом взаимодействии уровней. _(inter-level, boundary, finite-closure, vein-A)_

**Uniqueness - score 2 (new-framing).** Межуровневое исчисление над Q (вена A): всякое взаимодействие имеет границу (finite=Element vs closure=role-limit), Element исключает role-limit.
> _Caveat:_ Обобщение вены A на межуровневые взаимодействия; универсализация, не новый результат.

---

## #292 - `src/foundation/JFactorDescent.v` - score 1 (exposition)

**J-factor descent over Q: the Jarlskog factor as a bare-hierarchy wall**

- **Topic.** n-angles/n-phases, CP count derived, CKM params for 3 gen, a wall type, J is a bare hierarchy, J same as lambda, and the taxonomy closed under J.
- **Role.** Wall-taxonomy leaf (J-factor). Self-contained.
- **Counts.** Qed 1 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ J-фактор (Jarlskog); CKM-параметры. _Roles:_ J = роль-стена (bare hierarchy, как lambda). _Rules:_ j_is_bare_hierarchy; j_same_as_lambda; taxonomy_closed_under_j. _P4:_ конечные параметры (Element); J-фактор = bare-hierarchy стена, таксономия замкнута под J.
- **Classical counterpart.** No classical counterpart — a ToS wall-taxonomy audit placing the Jarlskog J-factor as a 'bare hierarchy' wall (same as lambda), closing the taxonomy under J.
- **Tags.** foundation, wall-taxonomy, jarlskog, exposition

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `n_angles/n_phases/cp_count_derived/ckm_params_3gen/Wall/WallType/wall_type` | Definition/Theorem | CKM-параметры, тип стены |
| `j_is_bare_hierarchy/j_same_as_lambda/taxonomy_closed_under_j/j_factor_descent` | Theorem | ★ J = bare-hierarchy стена |

**Key lemmas (deep):**

- **`taxonomy_closed_under_j`** - Помещает J-фактор Jarlskog в таксономию стен как «голую иерархию» (то же, что lambda), замыкая таксономию под J над Q. Внутренняя классификация стен (ср. BaryogenesisBoundary, WallTaxonomy). Уникальности нет. _(wall-taxonomy, jarlskog, bare-hierarchy)_

**Uniqueness - score 1 (exposition).** Спуск J-фактора над Q: J = bare-hierarchy стена (как lambda), таксономия замкнута под J.
> _Caveat:_ Внутренняя таксономия стен; собственного результата нет.

---

## #293 - `src/foundation/KappaFrameworkChain.v` - score 2 (methods)

**Kappa framework chain over Q: kappa is one extra posit (honest)**

- **Topic.** A K-leaf, a kappa chain, a D4 chain, is-extra, named-in-floor, kappa one extra, D4 zero extra, stability carried by P4, kappa laws in the floor, and the chain never zero.
- **Role.** Honesty/posit-chain leaf (kappa). Self-contained.
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ kappa-цепь; D4-цепь; постулаты. _Roles:_ цепь = роль (kappa = +1 постулат, D4 = 0 лишних). _Rules:_ kappa_one_extra; d4_zero_extra; stability_carried_by_P4. _P4:_ конечная цепь (Element); ЧЕСТНО: kappa — один лишний постулат, стабильность несёт P4.
- **Classical counterpart.** No classical counterpart — a ToS posit-chain audit showing kappa is one extra posit while D4 is zero-extra, with stability carried by P4 and kappa's laws in the floor.
- **Tags.** foundation, honesty, kappa, methods

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `KLeaf/kappa_chain/d4_chain/is_extra/named_in_floor/kappa_one_extra/d4_zero_extra/stability_carried_by_P4/kappa_laws_in_floor/chain_never_zero/kappa_framework_chain` | Definition/Theorem | ★ kappa = +1 постулат (честно) |

**Key lemmas (deep):**

- **`kappa_one_extra`** - ЧЕСТНАЯ цепь постулатов: kappa — ОДИН дополнительный постулат, D4 — ноль лишних, стабильность несёт P4 над Q. Калибровка против over-claim: явно фиксирует, что kappa постулирована (ср. KappaPositReduction, FoundationNamedFloor). _(honesty, kappa, posit-chain)_

**Uniqueness - score 2 (methods).** Цепь фреймворка kappa над Q: kappa = +1 постулат, D4 = 0 лишних, стабильность несёт P4 — честная фиксация.
> _Caveat:_ Внутренний posit-аудит; ценность — честная фиксация постулата kappa, не вывод.

---

## #294 - `src/foundation/KappaPositReduction.v` - score 2 (methods)

**Kappa posit reduction over Q: kappa rests on two honest posits**

- **Topic.** Metric/gauge DOF (4/3), DOF sum, kappa, kappa-4, sin^2w, a D4 posit and a DOF-model posit, kappa just/grounded, and kappa two posits.
- **Role.** Honesty/posit-reduction leaf (kappa). sin^2w context OVER-BRANDED. Self-contained.
- **Counts.** Qed 1 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ метрические/калибровочные DOF; kappa. _Roles:_ редукция = роль; kappa на ДВУХ постулатах (D4 + DOF-модель). _Rules:_ kappa_two_posits; D4_posit; dof_model_posit. _P4:_ конечные DOF (Element); ЧЕСТНО: kappa опирается на 2 постулата; sin²w-контекст OVER-BRANDED.
- **Classical counterpart.** No classical counterpart — an HONEST posit-reduction showing kappa=1/10 rests on two posits (D4 + DOF model) beyond the metric/gauge DOF.
- **Tags.** foundation, honesty, kappa, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `metric_dof/gauge_dof/metric_dof_4/gauge_dof_3/dof_sum_4/kappa/kappa_4/sin2w/sin2w_4` | Definition/Theorem | DOF, kappa |
| `D4_posit/dof_model_posit/kappa_just/kappa_grounded/kappa_two_posits/kappa_posit_reduction` | Theorem | ★ kappa на 2 постулатах (честно) |

**Key lemmas (deep):**

- **`kappa_two_posits`** - ЧЕСТНО: kappa=1/10 опирается на ДВА явных постулата (D4 + DOF-модель) над Q — редукция постулатов фиксирует основания. Калибровка против sin²θ_W=3/13 over-claim (sin²w-контекст здесь). Ср. EquipartitionRule, KappaFrameworkChain. _(honesty, kappa, posit-reduction)_

**Uniqueness - score 2 (methods).** Редукция постулатов kappa над Q: kappa опирается на 2 явных постулата (D4 + DOF-модель) — честная фиксация.
> _Caveat:_ Внутренняя редукция; sin²w-контекст OVER-BRANDED; ценность — честные 2 постулата kappa.

---

## #295 - `src/foundation/L1_DoublyStochastic.v` - score 3 (new-framing)

**L1 doubly-stochastic over Q: L1 (stability) implies doubly-stochastic (vein D root)**

- **Topic.** A matrix, row/col sums, row/col-stochastic, doubly-stochastic, uniform, is-stationary, L1 doubly-stochastic, L1 implies DS (2x2/3x3), concrete T_2x2/T_3x3/T_sym (all DS) and T_asym (not col-stochastic).
- **Role.** Vein-D root (L1 -> doubly-stochastic; feeds the Cayley/unistochastic thread). One of the larger foundation files (Q22). Self-contained (QArith).
- **Counts.** Qed 22 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ переходные матрицы; строчные/столбцовые суммы. _Roles:_ L1 (стабильность) = роль, влекущая бистохастичность; равномерное стационарно. _Rules:_ L1_implies_DS; uniform_stationary; doubly_stochastic. _P4:_ конечные матрицы над Q (Element); L1 (стабильность) ⟹ бистохастика (равномерное стационарно) — корень вены D.
- **Classical counterpart.** That a transition matrix with uniform stationary distribution is doubly-stochastic (Birkhoff) is classical; NEW is the ToS framing that L1 (stability) IMPLIES doubly-stochasticity, with concrete 2x2/3x3/symmetric instances (vein D root).
- **Tags.** foundation, L1, doubly-stochastic, vein-D, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `Mat/row_sum/col_sum/row_stochastic/col_stochastic/doubly_stochastic/uniform/is_stationary/fold_left_scalar/Qmult_cancel_l/L1_doubly_stochastic/L1_implies_DS/L1_doubly_stochastic_2/_3` | Definition/Theorem | ★ L1 ⟹ бистохастика |
| `T_2x2/_row_stochastic/_uniform_stationary/_col_stochastic/_doubly_stochastic/L1_implies_DS_2x2/T_3x3/.../L1_implies_DS_3x3/T_sym/.../T_asym/T_asym_row_stochastic/T_asym_not_col_stochastic` | Theorem | ★ конкретные 2x2/3x3/sym бистохастичны |

**Key lemmas (deep):**

- **`L1_implies_DS`** - L1 (стабильность распределения = равномерное стационарно) ВЛЕЧЁТ бистохастичность матрицы (строки И столбцы суммируются в 1) над Q. Корень вены D в физической ветви: стабильность → бистохастика → (через Cayley) унистохастика → born-вероятности. Конкретно для 2x2/3x3/симметричных; T_asym показывает, что асимметрия ломает столбцовую стохастичность. _(L1, doubly-stochastic, stability, vein-D)_

**Uniqueness - score 3 (new-framing).** L1 бистохастика над Q (корень вены D): L1 (стабильность=равномерное стационарно) ⟹ бистохастичность (2x2/3x3/sym), асимметрия ломает столбцовую стохастичность.
> _Caveat:_ Связь стационарность↔бистохастика (Биркгоф) классична; вклад — привязка к закону L1 как корню вены D, не новый результат.

---

## #296 - `src/foundation/L2DiracSynthesis.v` - score 2 (methods)

**L2-Dirac synthesis over Q: L2 -> chirality -> spin -> Dirac chain**

- **Topic.** Chain steps L2-to-chirality, chirality-to-spin, spin-to-Dirac, lattice-zero-mode; no-chirality-no-Dirac, wrong dimension, integer vs half, the L2-to-Dirac chain, and each step necessary.
- **Role.** Distinction->SM synthesis (L2->Dirac). SM-from-distinction OVER-BRANDED. Self-contained.
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ цепочка L2→хиральность→спин→Дирак. _Roles:_ узел-синтез: L2 порождает структуру Дирака. _Rules:_ L2_to_dirac_chain; no_chirality_no_dirac; chain_each_step_necessary. _P4:_ конечная цепочка (Element); L2→Дирак; SM-from-distinction OVER-BRANDED.
- **Classical counterpart.** The chain L2(chirality)->spin->Dirac->lattice-zero-mode is a re-telling of how chirality forces the Dirac structure; NEW only as a ToS synthesis (SM-from-distinction OVER-BRANDED).
- **Tags.** foundation, L2, dirac, over-branded, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `chain_step1_L2_to_chirality/chain_step2_chirality_to_spin/chain_step3_spin_to_dirac/chain_step4_lattice_zero_mode/no_chirality_no_dirac/wrong_dimension/integer_vs_half` | Theorem | ★ цепочка L2→Дирак |
| `L2_to_dirac_chain/chain_each_step_necessary` | Theorem | каждый шаг необходим |

**Key lemmas (deep):**

- **`L2_to_dirac_chain`** - Цепочка L2(хиральность)→спин→Дирак→решёточная нулевая мода, каждый шаг необходим над Q. Синтез ChiralityFromL2/DiracFromSpin/DiracOnLattice. SM-from-distinction OVER-BRANDED. _(L2, dirac, chirality, over-branded)_

**Uniqueness - score 2 (methods).** Синтез L2-Дирак над Q: L2→хиральность→спин→Дирак→нулевая мода, каждый шаг необходим.
> _Caveat:_ Цепочка хиральность→Дирак — известная физика; SM-from-distinction OVER-BRANDED.

---

## #297 - `src/foundation/L5_Arrow.v` - score 3 (new-framing)

**L5 arrow over Q: the arrow of time from the constitutive order L5**

- **Topic.** A stage (undifferentiated, first distinction), a distinction set with membership/subset, L5 preservation, arrow forward, nothing before undifferentiated, cannot unmake a distinction, arrow strictly forward, no backward from start, minimal start entropy, arrow composes / never returns, no universal backward, arrow preserves info, stage well-founded, and arrow iteration strictly increasing.
- **Role.** L5-law leaf (L5 -> arrow of time; with ArrowFromDistinction). Self-contained.
- **Counts.** Qed 4 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ стадии; множества различений. _Roles:_ L5 = конститутивный порядок; стрела = роль (различения нельзя отменить). _Rules:_ cannot_unmake_distinction; arrow_strictly_forward; stage_well_founded. _P4:_ конечные стадии (Element); стрела времени из L5 (различения необратимы, well-founded), строго возрастает.
- **Classical counterpart.** The thermodynamic arrow as monotone, well-founded, irreversible accumulation is standard; NEW is deriving it from L5 (the constitutive order): distinctions cannot be unmade, so the arrow is strictly forward.
- **Tags.** foundation, L5, arrow, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `stage/undifferentiated/first_distinction/DistSet'/has_dist'/dist_subset'/L5_pres/arrow_forward/nothing_before_undifferentiated` | Definition/Theorem | стадии, L5-сохранение |
| `cannot_unmake_distinction/arrow_strictly_forward/no_arrow_backward_from_start/D_start/entropy_start/start_minimal/entropy_start_minimal/arrow_compose/arrow_never_returns/no_universal_backward/arrow_preserves_info/stage_well_founded/arrow_iter/_adds/_strictly_increasing` | Theorem | ★ стрела строго вперёд (L5), well-founded |

**Key lemmas (deep):**

- **`cannot_unmake_distinction`** - Стрела времени выводится из L5 (конститутивного порядка): различение НЕЛЬЗЯ отменить (cannot_unmake_distinction), стадии well-founded, стрела строго вперёд и никогда не возвращается над Q. L5→необратимость как структурное следствие, а не постулат термодинамики. Ср. ArrowFromDistinction, L5_Preservation. _(L5, arrow, irreversible, well-founded)_

**Uniqueness - score 3 (new-framing).** L5-стрела над Q: стрела времени из конститутивного порядка L5 (различения необратимы, well-founded, строго вперёд, никогда не возвращается).
> _Caveat:_ Необратимая монотонная стрела стандартна; вклад — её вывод из закона L5 (различения нельзя отменить), не новый результат.

---

## #298 - `src/foundation/L5_as_Theorem.v` - score 3 (new-framing)

**L5 as a theorem over Q: P4 implies L5 (L5 is derived, not postulated)**

- **Topic.** A distinction history, has-monotone-subsequence, L5 from consecutive/chains/forks, P4 implies L5 chain/tree/full, L5 constant, monotone gives a pair, and L5 resolution exists.
- **Role.** L5-law flagship (L5 derived from P4, not an axiom). Self-contained.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ истории различений; монотонные подпоследовательности. _Roles:_ L5 = ТЕОРЕМА (не аксиома); P4 влечёт L5. _Rules:_ P4_implies_L5_chain; P4_implies_L5_full; L5_resolution_exists. _P4:_ конечные истории (Element); P4 (конечная актуальность) ВЛЕЧЁТ L5 на цепях/деревьях/полной истории — L5 выведена, не постулирована.
- **Classical counterpart.** No classical counterpart — the ToS result that L5 (the constitutive resolution order) is not an axiom but a THEOREM: P4 (finite actuality) implies L5 on chains, trees and the full history (a monotone subsequence always exists).
- **Tags.** foundation, L5, P4-implies-L5, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `DistinctionHistory/has_monotone_subsequence/L5_from_consecutive/L5_from_chains/L5_from_forks` | Definition/Theorem | L5 из последовательных/цепей/развилок |
| `P4_implies_L5_chain/P4_implies_L5_tree/P4_implies_L5_full/L5_constant/monotone_gives_pair/L5_resolution_exists/l5_as_theorem_synthesis` | Theorem | ★ P4 ⟹ L5 (L5 — теорема) |

**Key lemmas (deep):**

- **`P4_implies_L5_full`** - L5 (конститутивный порядок разрешения) — НЕ аксиома, а ТЕОРЕМА: P4 (конечная актуальность) влечёт L5 на полной истории различений (всегда есть монотонная подпоследовательность) над Q. Снижает число постулатов ToS: L5 выводится из P4. Сильное foundational наблюдение. _(L5, theorem, P4-implies-L5, derived)_

**Uniqueness - score 3 (new-framing).** L5 как теорема над Q: P4 (конечная актуальность) ВЛЕЧЁТ L5 на цепях/деревьях/полной истории — L5 выведена из P4, не постулирована (снижает число аксиом).
> _Caveat:_ Существование монотонной подпоследовательности — стандартный комбинаторный факт; вклад — его использование для вывода закона L5 из P4, foundational наблюдение.

---

## #299 - `src/foundation/L5_Conservation.v` - score 3 (new-framing)

**L5 conservation over Q: energy/charge/momentum conserved from L5**

- **Topic.** A distinction set with membership/subset, L5 preservation, conserved, L5 conservation, an energy distinction (10 at 0/1/2, 20 at 1, preserved, grows), info never lost, a charge distinction (conserved), a momentum distinction (conserved), and conservation monotone.
- **Role.** L5-law leaf (L5 -> conservation laws). Self-contained.
- **Counts.** Qed 14 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ множества различений (энергия/заряд/импульс). _Roles:_ L5-сохранение = роль; сохраняемые величины = L5-сохранённые. _Rules:_ L5_conservation; info_never_lost; charge_conserved. _P4:_ конечные множества (Element); законы сохранения (энергия/заряд/импульс, информация) из L5 (сохранение различений).
- **Classical counterpart.** Conservation laws (energy/charge/momentum, information never lost) as monotone invariants are standard; NEW is deriving them from L5 (preservation of distinctions): conserved quantities are exactly the L5-preserved ones.
- **Tags.** foundation, L5, conservation, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `CDistSet/chas/c_subset/L5_pres/conserved/L5_conservation/D_energy/energy_has_10_at_0/_1/_2/_20_at_1/energy_pres_0_1/_1_2/D_energy_grows/info_never_lost` | Definition/Theorem | ★ L5-сохранение, информация не теряется |
| `D_charge/charge_pres/charge_conserved/D_momentum/momentum_pres/momentum_conserved_5/_3/conservation_monotone/c_subset_refl/_trans/chas_cons/chas_head/chas_nil/L5_pres_multi/energy_has_10_at_3/conserved_weaken/energy_pres_2_3` | Theorem | ★ заряд/импульс сохраняются |

**Key lemmas (deep):**

- **`L5_conservation`** - Законы сохранения (энергия, заряд, импульс, информация не теряется) выводятся из L5 (сохранение различений): сохраняемая величина = L5-сохранённое множество различений над Q. L5→Нётер-подобная связь: конститутивный порядок порождает инварианты. info_never_lost = информационная версия. _(L5, conservation, noether-like, information)_

**Uniqueness - score 3 (new-framing).** L5-сохранение над Q: законы сохранения (энергия/заряд/импульс, информация не теряется) из L5 (сохранение различений) — конститутивный порядок порождает инварианты.
> _Caveat:_ Законы сохранения как монотонные инварианты стандартны; вклад — их вывод из закона L5, не новый физический результат.

---

## #300 - `src/foundation/L5_CoreSynthesis.v` - score 1 (exposition)

**L5 core synthesis over Q: the L5 monotone-preservation grand statement**

- **Topic.** A distinction set with membership/subset, L5 preservation, permutations, sub-chains 01/12/23/34, membership at various stages, lengths, and the L5 grand synthesis.
- **Role.** L5-law synthesis node. Self-contained.
- **Counts.** Qed 5 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ множества различений; цепи подмножеств. _Roles:_ узел-синтез: L5-монотонное сохранение. _Rules:_ L5_pres'; L5_grand_synthesis. _P4:_ конечные множества (Element); агрегат L5-сохранения.
- **Classical counterpart.** No classical counterpart — a synthesis node tying the L5 monotone-preservation results (membership, subset chains, permutations) into one grand statement.
- **Tags.** foundation, L5, synthesis, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `DS/has_d/ds_subset/L5_pres'/Ds/perm'/sub_01/_12/_23/_34/has_d_1_in_1/_1_in_2/_3_in_2/_5_in_3/_7_in_4/len_01/_12/_23/_34/L5_grand_synthesis` | Definition/Theorem | ★ L5-монотонное сохранение (синтез) |

**Key lemmas (deep):**

- **`L5_grand_synthesis`** - Узел-синтез L5-сохранения (членство, цепи подмножеств, перестановки) над Q. Агрегатор L5_Preservation/L5_Conservation. Собственной уникальности нет. _(L5, synthesis)_

**Uniqueness - score 1 (exposition).** Ядро-синтез L5 над Q: L5-монотонное сохранение (членство, цепи, перестановки).
> _Caveat:_ Узел-агрегатор L5-результатов; собственного результата нет.

---

## #301 - `src/foundation/L5_Indivisible.v` - score 3 (new-framing)

**L5 indivisible over Q: L5 implies indivisibility, path-dependence**

- **Topic.** A distinction set (included), a history with L5-monotone, included refl/trans, history in current, a state (same config different D), two monotone histories H1/H2, same initial/final but different intermediate, a distinction-sensitive transition, a path value (path-dependent example), indivisible, L5 implies indivisible, initial persists, and intermediate states.
- **Role.** L5-law leaf (L5 -> indivisibility/path-dependence; with IndivisibleDistinction). Self-contained.
- **Counts.** Qed 16 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ множества различений; истории (H1/H2). _Roles:_ L5 = роль (неделимость); пути зависят от истории. _Rules:_ L5_implies_indivisible; path_dependent_example; initial_persists. _P4:_ конечные истории (Element); L5 ⟹ неделимость (разрешение не расщепить); пути зависят от истории (одинаковые концы, разные середины).
- **Classical counterpart.** Path-dependence and that the initial state persists under a monotone history are standard order-theory facts; NEW is the ToS statement that L5 implies indivisibility (the resolution cannot be split; histories are path-dependent).
- **Tags.** foundation, L5, indivisible, path-dependent, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `DSet/dset_included/History/L5_monotone/dset_included_refl/_trans/history_in_current/State/same_config_diff_D/H1/H2/H1_monotone/H2_monotone/same_initial/same_final/diff_intermediate` | Definition/Theorem | истории, одинаковые концы/разные середины |
| `Transition/distinction_sensitive/path_value/path_dependent_example/indivisible/L5_implies_indivisible/initial_persists/monotone_compose/states_at_intermediate/H1_has_2_at_1/H2_lacks_2_at_1/H2_has_3_at_1/H1_lacks_3_at_1/empty_history_monotone/const_history_monotone/L5_indivisible_synthesis` | Theorem | ★ L5 ⟹ неделимость, путь-зависимость |

**Key lemmas (deep):**

- **`L5_implies_indivisible`** - L5 ВЛЕЧЁТ неделимость: разрешение различений нельзя расщепить, а истории ПУТЬ-ЗАВИСИМЫ (две истории H1/H2 с одинаковыми началом/концом, но разными промежуточными состояниями) над Q. L5→память пути (как геометрическая фаза/гистерезис). Ср. IndivisibleDistinction. _(L5, indivisible, path-dependent)_

**Uniqueness - score 3 (new-framing).** L5-неделимость над Q: L5 ⟹ неделимость разрешения + путь-зависимость (одинаковые концы, разные середины) — конститутивный порядок помнит путь.
> _Caveat:_ Путь-зависимость — стандартный факт теории порядка; вклад — её вывод из L5 (неделимость), не новый результат.

---

## #302 - `src/foundation/L5_NatFromHierarchy.v` - score 2 (new-framing)

**L5 nat from hierarchy over Q: the naturals from the L5 level hierarchy**

- **Topic.** A Level type, level-to-nat / nat-to-level (roundtrips), levels 0/1/2, Peano zero, successor injective, base not successor, level order/size, hierarchy irreflexive/transitive, decidable equality, and the order 0<1<2.
- **Role.** L5-law leaf (nat from the level hierarchy; with L5/Core). Self-contained.
- **Counts.** Qed 2 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ уровни (Level); натуральные числа. _Roles:_ иерархия уровней = роль (изоморфна nat: Пеано). _Rules:_ level_nat_level; lsucc_injective; level_lt_trans. _P4:_ конечные уровни (Element); nat ВЫВОДИТСЯ из иерархии уровней L5 (Пеано: 0, инъективный succ, строгий порядок).
- **Classical counterpart.** That a well-founded level hierarchy is isomorphic to the naturals (Peano: zero, injective successor, strict order) is standard; NEW is deriving nat FROM the L5 distinction hierarchy.
- **Tags.** foundation, L5, nat, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `Level/level_to_nat/nat_to_level/level_nat_level/nat_level_nat/level_0/_1/_2/level_0_nat/_1_nat/_2_nat` | Definition/Theorem | Level ↔ nat (изоморфизм) |
| `peano_zero/lsucc_injective/base_not_succ/level_lt/level_size/level_lt_size/hierarchy_irrefl/level_lt_trans/level_eq_dec/lt_0_1/lt_1_2/lt_0_2` | Theorem | ★ Пеано из иерархии уровней |

**Key lemmas (deep):**

- **`lsucc_injective`** - Натуральные числа ВЫВОДЯТСЯ из иерархии уровней L5: Level изоморфен nat (Пеано — 0, инъективный succ, строгий транзитивный порядок) над Q. Связывает конститутивную иерархию с арифметикой числа (ср. ERRKnowledgeBase number_contains_predecessors). _(L5, nat, peano, hierarchy)_

**Uniqueness - score 2 (new-framing).** Nat из иерархии над Q: натуральные числа изоморфны иерархии уровней L5 (Пеано: 0, инъективный succ, строгий порядок).
> _Caveat:_ Изоморфизм well-founded иерархии и nat стандартен; вклад — вывод nat из L5-иерархии, не новый результат.

---

## #303 - `src/foundation/L5_PhasesSynthesis.v` - score 1 (exposition)

**L5 phases synthesis over Q: the L5 phases consistent**

- **Topic.** A synthesis aspect, phase-3 duality, conserved, phase-4 conservation (concrete), phase-5 energy (commutative, distinct), resolve, phase-6 resolution (total, deterministic), the L5 phases grand synthesis, and phases consistent.
- **Role.** L5-law synthesis node. Self-contained.
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ фазы L5 (дуальность/сохранение/энергия/разрешение). _Roles:_ узел-синтез: фазы L5 согласованы. _Rules:_ L5_phases_grand_synthesis; phases_consistent. _P4:_ конечные фазы (Element); агрегат фаз L5.
- **Classical counterpart.** No classical counterpart — a synthesis node tying the L5 'phases' (duality, conservation, energy, resolution) into one consistent statement.
- **Tags.** foundation, L5, synthesis, exposition

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `SynthAspect/synth_ph3_duality/synth_conserved/synth_ph4_conservation_concrete/synth_ph5_energy_commutative/_distinct/synth_resolve/synth_ph6_resolution_total/_deterministic/L5_phases_grand_synthesis/phases_consistent` | Definition/Theorem | ★ фазы L5 согласованы |

**Key lemmas (deep):**

- **`phases_consistent`** - Узел-синтез фаз L5 (дуальность, сохранение, энергия, разрешение total+детерминистично) над Q. Агрегатор L5-кластера. Собственной уникальности нет. _(L5, phases, synthesis)_

**Uniqueness - score 1 (exposition).** Синтез фаз L5 над Q: фазы (дуальность/сохранение/энергия/разрешение) согласованы.
> _Caveat:_ Узел-агрегатор фаз L5; собственного результата нет.

---

## #304 - `src/foundation/L5_Preservation.v` - score 3 (new-framing)

**L5 preservation over Q: the second law from L5 (distinctions are permanent)**

- **Topic.** A distinction set, count, membership/subset, L5 preservation, distinctions permanent, concrete D0..D4 with L5 at each step, count non-decreasing, entropy non-decreasing, the second law from L5, L5 implies reliable (forever), info conservation, and all conserved.
- **Role.** L5-law leaf (L5 -> second law; with L5_Conservation). Self-contained.
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ множества различений; энтропия=счёт различений. _Roles:_ L5-сохранение = роль (различения постоянны); второй закон. _Rules:_ distinction_permanent; second_law_from_L5; info_conservation. _P4:_ конечные множества (Element); второй закон (энтропия не убывает) из L5 (различения постоянны).
- **Classical counterpart.** The second law (monotone non-decreasing entropy) and information conservation are standard; NEW is deriving the second law FROM L5 (distinctions are permanent), with entropy = distinction count.
- **Tags.** foundation, L5, second-law, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `DistSet/dist_count/has_dist/dist_subset/L5_preservation/distinction_permanent/D0/D1/D2/D3/D4/L5_concrete_01/_12/_23/_34/count_nondecr_01/_12/_23/_34` | Definition/Theorem | L5-сохранение, различения постоянны |
| `entropy/entropy_nondecr_01/_12/_23/_34/second_law_from_L5/L5_implies_reliable/_forever/info_conservation/L5_all_conserved/dist_subset_refl/_trans/L5_multi_step/empty_subset/count_chain` | Theorem | ★ второй закон из L5 |

**Key lemmas (deep):**

- **`second_law_from_L5`** - Второй закон термодинамики (энтропия не убывает) выводится из L5: различения ПОСТОЯННЫ (distinction_permanent), энтропия = счёт различений, потому не убывает над Q. L5→второй закон + сохранение информации (info_conservation, L5_implies_reliable_forever). Структурный вывод стрелы энтропии. Ср. L5_Arrow. _(L5, second-law, entropy, information)_

**Uniqueness - score 3 (new-framing).** L5-сохранение над Q: второй закон (энтропия не убывает) из L5 (различения постоянны), сохранение информации (надёжно навсегда).
> _Caveat:_ Второй закон как монотонная энтропия стандартен; вклад — его вывод из закона L5 (постоянство различений), не новый результат.

---

## #305 - `src/foundation/L5_ResolutionGeneral.v` - score 2 (new-framing)

**L5 resolution general over Q: total deterministic selection without AC (vein B)**

- **Topic.** L5 resolve, L5 total, L5 deterministic (eq), L5 constructive, L5 empty, examples 1/2/3, no Banach-Tarski, L5 prepend, L5 singleton idempotent, and L5 resolve cons.
- **Role.** L5-law leaf (the general L5 resolution; vein-B deterministic selection without AC). All Definitions (Q0). Self-contained.
- **Counts.** Qed 0 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ разрешение L5 (выбор); конечные множества. _Roles:_ L5-разрешение = роль (тотальный детерминированный выбор БЕЗ AC). _Rules:_ L5_total; L5_deterministic; no_banach_tarski. _P4:_ конечные множества (Element); L5-разрешение тотально/детерминированно/конструктивно БЕЗ аксиомы выбора (вена B); no_banach_tarski.
- **Classical counterpart.** A deterministic, total selection (resolution) over a finite set without invoking the axiom of choice is the constructive selection; NEW is the L5 general resolution: total, deterministic, constructive, with no Banach-Tarski (vein B).
- **Tags.** foundation, L5, no-AC, vein-B, new-framing

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `L5_resolve/L5_total/L5_deterministic/L5_deterministic_eq/L5_constructive/L5_empty/L5_example_1/_2/_3/no_banach_tarski/L5_prepend/L5_singleton_idem/L5_resolve_cons` | Definition | ★ тотальный детерминированный выбор без AC |

**Key lemmas (deep):**

- **`L5_deterministic`** - L5-разрешение — ТОТАЛЬНЫЙ, ДЕТЕРМИНИРОВАННЫЙ, КОНСТРУКТИВНЫЙ выбор над конечным множеством БЕЗ аксиомы выбора (вена B), с no_banach_tarski над Q. Та же нить, что argmax-by-index/Bolzano-Weierstrass-no-DC (вена B: детерминированный выбор без AC). Все определения (Q0), но содержательно — конструктивная альтернатива AC. _(L5, selection, no-AC, vein-B)_

**Uniqueness - score 2 (new-framing).** L5 общее разрешение над Q (вена B): тотальный детерминированный конструктивный выбор БЕЗ аксиомы выбора, no_banach_tarski.
> _Caveat:_ Конструктивный выбор над конечным множеством элементарен; вклад — привязка к L5 как детерминированной альтернативе AC (вена B), не новый результат (Q0, всё определения).

---

## #306 - `src/foundation/L5_RGConnection.v` - score 2 (methods)

**L5 RG connection over Q: effective hbar runs to a classical limit**

- **Topic.** An effective hbar (at 0/1/2/3), RG monotone (01/12/23), hbar positive, a classical-limit bound (small), an RG fixed point, RG preserves positivity, RG ratios, and hbar bounded below.
- **Role.** L5-law leaf (L5 <-> RG flow). Self-contained (QArith).
- **Counts.** Qed 5 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ эффективный hbar; RG-поток. _Roles:_ RG-поток = роль (hbar к классическому пределу); фиксточка. _Rules:_ rg_monotone; classical_limit_small; rg_fixed_point. _P4:_ конечные значения hbar над Q (Element); hbar монотонно бежит к классическому пределу (RG-фиксточка, положителен).
- **Classical counterpart.** An effective hbar running monotonically toward a classical limit (RG fixed point, positivity) is a standard semiclassical picture; here a small Q instance connecting L5 to RG flow.
- **Tags.** foundation, L5, rg-flow, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `hbar_eff/hbar_0/_1/_2/_3/rg_monotone_01/_12/_23/hbar_positive/classical_limit_bound/classical_limit_small` | Definition/Theorem | hbar монотонен к пределу |
| `rg_fixed_point/rg_preserves_positive/rg_ratio_01/_12/hbar_bounded_below/L5_RGConnection` | Theorem | ★ RG-фиксточка, классический предел |

**Key lemmas (deep):**

- **`rg_fixed_point`** - Эффективный hbar монотонно бежит к классическому пределу (RG-фиксточка, положителен, ограничен снизу) над Q — связь L5 с RG-потоком/полуклассикой. Стандартная картина бега констант, малый Q-инстанс. _(L5, rg-flow, classical-limit, hbar)_

**Uniqueness - score 2 (methods).** L5-RG связь над Q: эффективный hbar монотонно бежит к классическому пределу (RG-фиксточка, положителен).
> _Caveat:_ Бег hbar к классическому пределу — стандартная полуклассика; Q-инстанс без нового результата.

---

## #307 - `src/foundation/L5_StructurePreservation.v` - score 2 (methods)

**L5 structure preservation over Q: refinement order preserved by maps**

- **Topic.** A structured distinction (level/index/finer/coarse/fine/finest), finer-than relations, finer transitive/irreflexive/asymmetric, structure preserved, identity/shift/compose preserve, an object-map preserving monotone, decidable equality, const not preserving, and shift-zero identity.
- **Role.** L5-law leaf (structure preservation under refinement). Self-contained.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ структурированные различения (finer/coarser); порядок измельчения. _Roles:_ сохранение структуры = роль (порядок измельчения сохраняется отображениями). _Rules:_ struct_preserved; sd_finer_trans; shift_preserves. _P4:_ конечные различения (Element); порядок измельчения (строгий частичный) сохраняется структурными отображениями (id/shift/compose).
- **Classical counterpart.** That a refinement (finer-than) order is a strict partial order preserved by structure-maps (identity, shift, compose) is standard order theory; NEW only as the L5 structure-preservation instance.
- **Tags.** foundation, L5, refinement-order, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `SDistinction/sd_level/sd_index/sd_finer/sd_coarse/sd_fine/sd_finest/fine_finer_than_coarse/finest_finer_than_fine/_coarse/sd_finer_trans/_irrefl` | Definition/Theorem | порядок измельчения (строгий частичный) |
| `struct_preserved/id_preserves/level_shift/shift_preserves/compose_preserves/sd_map_obj/sd_map_preserves_monotone/double_preserves/sd_eq_dec/const_not_preserves/sd_finer_asymm/shift_zero_id/shift_compose` | Theorem | ★ структура сохраняется отображениями |

**Key lemmas (deep):**

- **`struct_preserved`** - Порядок измельчения (finer-than, строгий частичный: транзитивен, иррефлексивен, асимметричен) СОХРАНЯЕТСЯ структурными отображениями (id/shift/compose) над Q; const НЕ сохраняет. L5-сохранение структуры как функториальность отображений измельчения. Стандартная теория порядка. _(L5, structure-preservation, refinement-order)_

**Uniqueness - score 2 (methods).** L5-сохранение структуры над Q: порядок измельчения (строгий частичный) сохраняется отображениями (id/shift/compose), const не сохраняет.
> _Caveat:_ Сохранение частичного порядка отображениями — стандартная теория порядка; L5-инстанс без нового результата.

---

## #308 - `src/foundation/L5CausalOrder.v` - score 2 (new-framing)

**L5 causal order over Q: causal precedence is a partial order (from L5)**

- **Topic.** A causal event, causally-precedes, reflexive/antisymmetric/transitive, causal is a partial order, no backward, origin/far event, spacelike not causal / incomparable, a next event, timelike causal, and the L5 causal synthesis.
- **Role.** L5-law leaf (L5 -> causal partial order; with CausalStructureSynthesis). Self-contained.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ причинные события; причинное предшествование. _Roles:_ L5 = роль (причинный частичный порядок); пространственноподобные несравнимы. _Rules:_ causal_is_partial_order; no_backward; spacelike_incomparable. _P4:_ конечные события (Element); причинное предшествование — частичный порядок (рефлексивен/антисимметричен/транзитивен) из L5; нет обратной причинности.
- **Classical counterpart.** That causal precedence is a partial order (reflexive, antisymmetric, transitive) with spacelike events incomparable and no backward causation is standard causal-set theory; NEW is deriving it from L5.
- **Tags.** foundation, L5, causal-order, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `CausalEvent/causally_precedes/causal_reflexive/causal_antisymmetric/causal_transitive/causal_is_partial_order/no_backward` | Definition/Theorem | ★ причинный частичный порядок |
| `origin/far_event/spacelike_not_causal/_rev/spacelike_incomparable/next_event/timelike_causal/l5_causal_synthesis` | Theorem | ★ пространственноподобные несравнимы, нет обратной причинности |

**Key lemmas (deep):**

- **`causal_is_partial_order`** - Причинное предшествование — ЧАСТИЧНЫЙ порядок (рефлексивен, антисимметричен, транзитивен), пространственноподобные события НЕСРАВНИМЫ, нет обратной причинности над Q — выводится из L5. L5→causal-set структура (ср. CausalOrderGeometry, CausalStructureSynthesis). Связь конститутивного порядка с причинностью. _(L5, causal-order, partial-order, spacelike)_

**Uniqueness - score 2 (new-framing).** L5-причинный порядок над Q: причинное предшествование = частичный порядок (рефлексивен/антисимметричен/транзитивен) из L5, пространственноподобные несравнимы, нет обратной причинности.
> _Caveat:_ Причинность как частичный порядок — causal-set теория; вклад — её вывод из L5, не новый результат.

---

## #309 - `src/foundation/LambdaAntigravityComputation.v` - score 1 (exposition)

**Lambda antigravity computation over Q: lambda gives positive acceleration**

- **Topic.** Equation-of-state parameters (matter/radiation/lambda/threshold), matter positive / lambda negative, antigravity iff w, a Newton G, accelerations (matter/lambda), lambda acceleration positive, the acceleration ratio, and lambda antigravity computed.
- **Role.** Gravity/cosmology leaf (lambda antigravity). Self-contained (QArith).
- **Counts.** Qed 1 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ параметры уравнения состояния; ускорение. _Roles:_ Lambda = роль (антигравитация при w<−1/3). _Rules:_ antigravity_iff_w; accel_lambda_positive; lambda_antigravity_computed. _P4:_ конечные параметры над Q (Element); Lambda даёт положительное (отталкивающее) ускорение.
- **Classical counterpart.** That a negative-pressure (w<-1/3) component gives positive (repulsive) acceleration while matter/radiation give negative is standard FRW dynamics; here a small Q instance for lambda.
- **Tags.** foundation, lambda, antigravity, exposition

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `q_param/q_matter/q_radiation/q_lambda/q_threshold/q_matter_positive/q_lambda_negative/antigravity_iff_w` | Definition/Theorem | уравнение состояния, порог |
| `G_newton/accel/accel_matter/accel_lambda/accel_lambda_positive/accel_ratio/lambda_antigravity_computed` | Theorem | ★ Lambda даёт положительное ускорение |

**Key lemmas (deep):**

- **`accel_lambda_positive`** - Lambda (w<−1/3) даёт ПОЛОЖИТЕЛЬНОЕ (отталкивающее) ускорение, материя/радиация — отрицательное над Q — стандартная FRW-динамика (ср. AntigravityCondition). Иллюстративно. _(lambda, antigravity, acceleration)_

**Uniqueness - score 1 (exposition).** Вычисление антигравитации Lambda над Q: Lambda (w<−1/3) даёт положительное ускорение, материя/радиация отрицательное.
> _Caveat:_ Отталкивание при отрицательном давлении — стандартная FRW-динамика; Q-инстанс без нового содержания.

---

## #310 - `src/foundation/LambdaPrediction.v` - score 2 (methods)

**Lambda prediction over Q: a small positive lambda running with scale**

- **Topic.** kappa, lambda at scale K, kappa^2, lambda at K0/K1, lambda always positive / never zero / decreasing, a lambda hierarchy, lambda from scale, different lambda, and the lambda structure.
- **Role.** Cosmology leaf (lambda prediction). Self-contained (QArith).
- **Counts.** Qed 2 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ kappa; Lambda на масштабе K. _Roles:_ Lambda = роль (всегда положительна, бежит с масштабом). _Rules:_ lambda_always_positive; lambda_never_zero; lambda_hierarchy. _P4:_ конечные значения Lambda над Q (Element); Lambda всегда положительна, убывает, бежит с масштабом.
- **Classical counterpart.** Predicting a small positive cosmological constant that runs with scale is standard cosmology; NEW only as a kappa^2-based Q instance (lambda always positive, never zero, decreasing, hierarchy).
- **Tags.** foundation, lambda, cosmology, methods

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `kappa/lambda_at_K/kappa_sq/lambda_K0/_K1/lambda_always_positive/lambda_never_zero/lambda_decreasing_01` | Definition/Theorem | ★ Lambda положительна, убывает |
| `lambda_hierarchy/lambda_from_scale/different_lambda/lambda_structure/lambda_prediction_summary/_theorem_count` | Theorem | Lambda-иерархия, бег с масштабом |

**Key lemmas (deep):**

- **`lambda_always_positive`** - Lambda (через kappa²) всегда положительна, никогда не ноль, убывает с масштабом над Q — предсказание малой положительной космологической постоянной. Связь kappa↔Lambda; малый Q-инстанс (kappa OVER-BRANDED по аудиту). _(lambda, cosmological-constant, prediction)_

**Uniqueness - score 2 (methods).** Предсказание Lambda над Q: малая положительная Lambda (через kappa²), всегда положительна, убывает, бежит с масштабом.
> _Caveat:_ Малая положительная бегущая Lambda — стандартная космология; kappa-основа OVER-BRANDED, не подтверждённое предсказание.

