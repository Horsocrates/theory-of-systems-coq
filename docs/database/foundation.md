# Database - cluster `foundation`

_Generated from `foundation.json` by `generate.ps1` - do not edit by hand; edit the JSON._

**306 files / 2377 Qed.** Score distribution: s5=0 / s4=22 / s3=102 / s2=151 / s1=31 / s0=0

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
- **Role.** SM-physics leaf (anomaly SAMPLE check). June 2026 honesty rollback: 'exhaustive search' RETIRED — ~5 tested alternatives, Y1 fixed; SUPERSEDED by AnomalyLatticeDial.v (#1861): true box-exhaustion 1317 -> 11 -> exactly {SM, u<->d swap}. Self-contained (QArith).
- **Counts.** Qed 10 / Admitted 0 / axioms 0
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
- **Role.** SM-physics leaf (1-D SAMPLE scan: Y2 over ~10 points, Y3=Y4=0). June 2026 honesty rollback: 'systematic'/'unique among Z/6' RETIRED; SUPERSEDED by AnomalyLatticeDial.v (#1861) box-exhaustion. Self-contained (QArith).
- **Counts.** Qed 17 / Admitted 0 / axioms 0
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
- **Counts.** Qed 6 / Admitted 0 / axioms 0
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
- **Counts.** Qed 6 / Admitted 0 / axioms 0
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
- **Role.** Dimension-derivation leaf (d=3 from spin/stability). June 2026 honesty rollback: 'uniquely determined' RETIRED (renamed dimension_consistency_record); d=3 = INTERSECTION of two posited bounds (stable_iff_le3 derives d<=3 given the orbit model; spin-1 lower bound is a bare posit); unique_given_bounds + uniqueness_lives_in_the_posits added. Self-contained (QArith).
- **Counts.** Qed 18 / Admitted 0 / axioms 0
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
- **Role.** ROOT of the entire foundation chain (Distinction -> ERR -> SM -> L5). Sole-source of the L3 axiom 'classic' (CLAUDE.md). 53+ files depend on this lineage. Self-contained. June 2026 wave-4 tail: co_constitution was vacuous ((P -> exists Q, Q = ~P) with hypotheses unused) -> one-act simultaneity: positive (distinction_of P) = P and negative = ~P, both by reflexivity from the SINGLE act (statement-only change; .vo not rebuilt in place, text verified via temp copy).
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
- **Counts.** Qed 6 / Admitted 0 / axioms 0
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
- **Role.** ERR-machinery hub (the largest ERR file, Q11). Self-contained. June 2026 wave-4 vacuity rollback: L2_exclusive was cat1 <> cat2 -> True (vacuous Definition) -> real uniqueness (no entity equals two different categories) + L2_exclusive_holds.
- **Counts.** Qed 36 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ ERR-статусы; уровни системы (logic/math/physics). _Roles:_ база знаний = роль (логика статусов ERR, иерархия конституций). _Rules:_ constitution_from_previous; logic_math_physics_chain; L2_L3_ground_well_formedness. _P4:_ конечная база статусов (Element); трёхуровневая цепь логика→математика→физика конституций.
- **Classical counterpart.** No classical counterpart — a ToS knowledge-base file laying out the ERR status logic, the L2/L3 well-formedness, and a three-level (logic/math/physics) constitution chain.
- **Tags.** foundation, ERR, logic-math-physics, new-framing

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `no_rules_no_roles/invalid_has_no_weight/generative_order/RoleType/role_type_of/is_unique_status/primary_is_unique/candidate_is_deterministic/has_sufficient_reason_to_update/higher_weight_updates/status_preservation` | Definition/Theorem | логика статусов, обновление весов June 2026 wave-4 vacuity rollback: L2_exclusive was cat1 <> cat2 -> True (vacuous Definition) -> real uniqueness (no entity equals two different categories) + L2_exclusive_holds. |
| `SystemLevel/level_0_logic/_1_generation/_2_concrete/constitution_from_previous/L2_exclusive/L3_exhaustive/L2_L3_ground_well_formedness/three_level_hierarchy` | Definition/Theorem | ★ уровни системы, L2/L3 обосновывают well-formedness June 2026 wave-4 vacuity rollback: L2_exclusive was cat1 <> cat2 -> True (vacuous Definition) -> real uniqueness (no entity equals two different categories) + L2_exclusive_holds. |
| `ERRAspect/category_to_aspect/aspect_roundtrip/proper_system/collection_no_function/system_has_function/Mathematics_Level/Physics_Level/math_constitution_is_logic/physics_constitution_is_math/logic_math_physics_chain/err_knowledge_base_full_synthesis` | Definition/Theorem | ★ цепь логика→математика→физика June 2026 wave-4 vacuity rollback: L2_exclusive was cat1 <> cat2 -> True (vacuous Definition) -> real uniqueness (no entity equals two different categories) + L2_exclusive_holds. |

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
- **Counts.** Qed 6 / Admitted 0 / axioms 0
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
- **Counts.** Qed 6 / Admitted 0 / axioms 0
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
- **Role.** Honesty anchor (the axiom audit; mirrors CLAUDE.md's HeavyWallAudit). Self-contained. June 2026 update: the 2 eliminable axioms WERE eliminated (B_antisym -> antisymmetrization Lemma in GalerkinSystem; functional_equation_structure -> 2-line Lemma in FunctionalEquation); post-elimination section added with machine-checked closure: eliminated_iff_eliminable (the eliminated set = the predicted eliminable set), n_remaining = 2 (C_B_positive input + B_coeff_bounded load-bearing), load_bearing_not_eliminated.
- **Counts.** Qed 9 / Admitted 0 / axioms 0
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
- **Counts.** Qed 6 / Admitted 0 / axioms 0
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
- **Role.** Distinction-spine leaf (indivisibility -> quantization, vein-C). Self-contained. June 2026 wave-4 vacuity rollback: count_is_natural -> count ADDITIVITY over ++; quantization conjunct -> finite-ratio by type; process_domain_forced -> domain discreteness (0 or successor).
- **Counts.** Qed 18 / Admitted 0 / axioms 0
- **Imports.** Stdlib: basic
- **E/R/R.** _Elements:_ различения (неделимые); счётчик различений (натуральный). _Roles:_ неделимость = роль (квантование); все 4 свойства необходимы. _Rules:_ distinction_indivisible; no_fractional_distinctions; quantization_from_distinction. _P4:_ счётчик различений натурален (Element); НЕТ дробных различений → квантование; процессный домен ВЫНУЖДЕН (вена C).
- **Classical counterpart.** That a count is a natural number (no fractional distinctions) and quantization follows from indivisibility is a foundational intuition; NEW is the formal statement that all four distinction properties are necessary and the count being natural forces the process domain (quantization from distinction).
- **Tags.** foundation, distinction, quantization, vein-C, new-framing

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `pseudo_distinction_no_excl/_no_exh/all_four_necessary/exclusive_essential/exhaustive_essential/positive_determines_negative/exactly_one_side/pair_without_rules_contradictory/distinction_indivisible/without_exclusive_anything/without_exhaustive_gap` | Theorem | ★ все 4 свойства необходимы, различение неделимо June 2026 wave-4 vacuity rollback: count_is_natural -> count ADDITIVITY over ++; quantization conjunct -> finite-ratio by type; process_domain_forced -> domain discreteness (0 or successor). |
| `distinction_count_nat/count_is_natural/count_always_nonneg/no_fractional_distinctions/distinction_increment/zero_distinctions/one_distinction/quantization_from_distinction/process_domain_forced/indivisible_distinction_summary` | Theorem | ★ квантование из неделимости; процессный домен вынужден June 2026 wave-4 vacuity rollback: count_is_natural -> count ADDITIVITY over ++; quantization conjunct -> finite-ratio by type; process_domain_forced -> domain discreteness (0 or successor). |

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
- **Counts.** Qed 6 / Admitted 0 / axioms 0
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
- **Counts.** Qed 6 / Admitted 0 / axioms 0
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

---

## #311 - `src/foundation/LambdaSmallnessDescent.v` - score 3 (new-framing)

**Lambda-smallness descent: finiteness derived, value not — a second wall-type (BareHierarchy)**

- **Topic.** A third 'descent' testing whether the derived-invariant/posited-symmetry shape of two earlier descents generalizes; it does not — finitization fixes finiteness (vac_bound <= 1) but no symmetry forces the magnitude, so Lambda is a BareHierarchy wall, distinct from the SymmetryChoice walls.
- **Role.** Self-contained (QArith/Lqa). Third of a small family of 'descent' meta-files; produces a 2-element WallType taxonomy. No downstream dependents.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; Stdlib: Lqa
- **E/R/R.** _Elements:_ vac_bound=1/2; значения 1/1000 и 1/10^6 — оба ниже границы; типы стен Wall/WallType. _Roles:_ конечность = выведенная структура; малость = свободное масштабное отношение (нет инварианта). _Rules:_ финитизация фиксирует КОНЕЧНОСТЬ, не ЗНАЧЕНИЕ; нет симметрии для магнитуды (голая иерархия). _P4:_ третий спуск РАСЩЕПИЛ паттерн-из-двух: role-limit-сторона гетерогенна (>=2 типа стен); анти-уплощение.
- **Classical counterpart.** The cosmological-constant smallness/hierarchy problem and renormalized vacuum energy are standard open physics; NEW only as an internal taxonomic observation that the 'arrow' and 'Born-rule' descent shape does NOT generalize to Lambda.
- **Tags.** foundation, cosmological-constant, taxonomy, honesty, new-framing

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `vac_bound/divergence_solved` | Definition/Lemma | O(1) граница вакуума; расходимость решена (<=1) |
| `smallness_not_from_finiteness/finiteness_picks_no_value` | Lemma | конечность != малость; не выбирает значение (1/1000 и 1/10^6 оба ниже) |
| `Wall/WallType/wall_type/has_derived_invariant` | Definition | таксономия стен: SymmetryChoice vs BareHierarchy |
| `lambda_is_bare_hierarchy/two_wall_types/lambda_smallness_descent` | Lemma/Theorem | Lambda = BareHierarchy; паттерн-из-двух сломан; капстоун |

**Key lemmas (deep):**

- **`two_wall_types`** - Машинно фиксирует, что 'стрела' и 'Борн' имеют выведенный инвариант (SymmetryChoice), а Lambda — нет (BareHierarchy). Это честное АНТИ-обобщение: вместо синтеза-одной-формы автор доказывает гетерогенность role-limit-стороны. Содержательно это наблюдение/мнение о структуре ToS, а не теорема о физике; сами 'инварианты' — рефлексивные (reflexivity). _(lambda, taxonomy, anti-generalization, honesty)_

**Uniqueness - score 3 (new-framing).** Внутренняя таксономия 'стен' финитизации: третий спуск ломает паттерн-из-двух и вводит тип BareHierarchy (конечность выведена, инвариант — нет).
> _Caveat:_ Сама проблема малости Lambda (иерархия масштабов, вакуумная энергия) — классическая нерешённая физика; здесь НЕ выводится ни значение, ни структура Lambda. Доказательства — рациональные неравенства + reflexivity над крошечным конечным перечислением; 'инвариант'/'симметрия' трактуются неформально. Вклад = честное обрамление, не результат.

---

## #312 - `src/foundation/LatticeDecimationRG.v` - score 3 (new-framing)

**Genuine 1D Ising real-space decimation u->u^2: RG semigroup + honesty contrast with 1/N fake**

- **Topic.** Exact rational real-space RG: decimating by 2 squares the bond activity; the N-step flow is double-exponential u^(2^N), forms a semigroup (steps add), and the 3-step value 1/256 is machine-shown to differ from the 1/3 a faked analytic 1/N scaling would give.
- **Role.** Self-contained (QArith/Lqa/Lia). Exposes the honesty gap of gauge/ExactRGProcess.v; abstracts RGCascadeReal.v's t->t^2 with the lattice identification. No downstream dependents.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; Stdlib: Lia; Stdlib: Lqa
- **E/R/R.** _Elements:_ активность u in Q на каждом масштабе; конечное N; u^(2^N) (двойная экспонента). _Roles:_ u = масштаб/связь; шаг decimation = огрубление; неподвижные точки u=0(устойч.)/u=1(неустойч.) = фазы. _Rules:_ decimate u = u^2 (per-step пересчёт); шаги складываются (полугруппа); u<1 течёт к 0. _P4:_ genuine многошаговый поток (per-step u^2) vs аналитич. фейк gap/N; различаются (1/256 != 1/3) => 1/N не настоящий RG.
- **Classical counterpart.** The exact 1D Ising real-space decimation u=tanh(K) -> u^2 is textbook real-space RG (Kadanoff/Wilson); NEW only as an exact-rational Coq exemplar machine-contrasting a genuine per-step flow against a faked 1/N scaling used elsewhere in the repo (gauge/ExactRGProcess.v).
- **Tags.** foundation, rg, ising, honesty-contrast, new-framing

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `decimate/decimate_fixed_disorder/decimate_fixed_critical` | Definition/Lemma | правило u->u^2; неподвижные точки 0 и 1 |
| `decimate_iter/decimate_iter_S` | Definition/Lemma | N-шаговая итерация; per-step пересчёт |
| `decimate_compose` | Lemma | ★ RG-полугруппа: шаги складываются 2^a+2^b=2^(a+b) |
| `decimate_flow_1/decimate_flow_3/real_flow_differs_from_1overN/lattice_decimation_rg` | Lemma/Theorem | двойно-экспонент. поток; ★ контраст 1/256 != 1/3; капстоун |

**Key lemmas (deep):**

- **`real_flow_differs_from_1overN`** - Машинная разница 1/256 (настоящий 3-шаговый поток) vs 1/3 (фейк gap/N) — это конкретный, проверяемый аргумент честности против другого файла репозитория. Полугруппа decimate_compose — структурный закон, которого фейк не удовлетворяет. Сама RG-децимация 1D Изинга классична; ценность = аккуратная Q-формализация + внутренний аудит фейкового скейлинга. _(rg, ising, semigroup, honesty-contrast)_

**Uniqueness - score 3 (new-framing).** Первая genuine многошаговая вещественно-пространственная децимация в репо (per-step u^2, RG-полугруппа, двойная экспонента) с машинным разоблачением фейкового 1/N-скейлинга.
> _Caveat:_ 1D Ising decimation u->u^2 — стандартный учебный RG; новизны в физике нет. Это 1D эксемпляр: gauge SU(N)-децимация (то, о чём ExactRGProcess.v) НЕ переделана; xi=-1/ln(u) не вычислена. Header заявляет 9 Qed — фактически 8 (дрейф).

---

## #313 - `src/foundation/LawsFromDistinction.v` - score 1 (exposition)

**Five Laws (L1-L5) as theorems about the Distinction record**

- **Topic.** Each of the five ToS laws is stated as a lemma over the Distinction structure: identity (reflexivity), non-contradiction, excluded middle (= classic), sufficient reason (self-grounding), and hierarchy (level order irreflexive/transitive), unified in five_laws_from_distinction.
- **Role.** Foundation file 2/4 of the Distinction chain. Imports Distinction.v + Core_ERR; reused by NestedDistinction.v and the SM-from-distinction chain. Defines laws_theorem_count := 22. June 2026 wave-4 vacuity rollback: L5_no_infinite_descent was exists n, depth l = n (vacuous) -> STRICT depth decrease along << (Core_ERR level_lt_depth) = genuine well-foundedness.
- **Counts.** Qed 22 / Admitted 0 / axioms 0
- **Imports.** ToS: foundation.Distinction; ToS: TheoryOfSystems_Core_ERR
- **E/R/R.** _Elements:_ Distinction (positive/negative); Level (L1,L2,L3...). _Roles:_ каждый закон = аспект ОДНОЙ структуры различения, не отдельная аксиома. _Rules:_ L1=A=A; L2 исключительность; L3=classic; L4 самообоснование; L5 иерархия (irrefl/trans). _P4:_ L1-L5 как СЛЕДСТВИЯ структуры Distinction; конструктивные части — над конечным Level; L3 честно = classic (1 аксиома).
- **Classical counterpart.** Laws of identity, non-contradiction, excluded middle, sufficient reason, and a well-founded order are classical logic; NEW only as a framing that presents L1-L5 as theorems 'about the Distinction record' rather than independent axioms (L3 = the classic axiom; the rest are essentially reflexivity / standard logic).
- **Tags.** foundation, distinction, five-laws, logic, exposition

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `Law_of_Identity/L1_through_distinction/L1_distinction_preserves` | Theorem | L1: тождество (reflexivity) June 2026 wave-4 vacuity rollback: L5_no_infinite_descent was exists n, depth l = n (vacuous) -> STRICT depth decrease along << (Core_ERR level_lt_depth) = genuine well-foundedness. |
| `Law_of_NonContradiction/L2_from_distinction/L2_canonical` | Theorem | L2: непротиворечивость June 2026 wave-4 vacuity rollback: L5_no_infinite_descent was exists n, depth l = n (vacuous) -> STRICT depth decrease along << (Core_ERR level_lt_depth) = genuine well-foundedness. |
| `Law_of_ExcludedMiddle/L3_from_distinction/L3_independence` | Theorem | L3: исключённое третье = classic June 2026 wave-4 vacuity rollback: L5_no_infinite_descent was exists n, depth l = n (vacuous) -> STRICT depth decrease along << (Core_ERR level_lt_depth) = genuine well-foundedness. |
| `Law_of_SufficientReason/L4_contra/L4_canonical/L4_double_negation` | Theorem | L4: достаточное основание + двойное отрицание June 2026 wave-4 vacuity rollback: L5_no_infinite_descent was exists n, depth l = n (vacuous) -> STRICT depth decrease along << (Core_ERR level_lt_depth) = genuine well-foundedness. |
| `L5_hierarchy/L5_transitivity/L5_concrete/L5_chain/L5_no_infinite_descent` | Theorem | L5: иерархия уровней (irrefl, trans, цепь) June 2026 wave-4 vacuity rollback: L5_no_infinite_descent was exists n, depth l = n (vacuous) -> STRICT depth decrease along << (Core_ERR level_lt_depth) = genuine well-foundedness. |
| `five_laws_from_distinction/laws_consistent/L1_L2_combined/L3_L4_combined/laws_theorem_count` | Theorem/Definition | ★ объединение всех пяти законов; совместность June 2026 wave-4 vacuity rollback: L5_no_infinite_descent was exists n, depth l = n (vacuous) -> STRICT depth decrease along << (Core_ERR level_lt_depth) = genuine well-foundedness. |

**Key lemmas (deep):**

- **`five_laws_from_distinction`** - Объединяет L1-L5 для произвольного Distinction. Содержательно это РЕФРЕЙМ: каждый закон сводится к reflexivity, к полю Record (exclusive/exhaustive) или к classic. L3 честно объявлен равным classic (L3_independence — это просто переадресация к classic). Никакой новой логики; ценность чисто экспозиционно-структурная (превращение комментарных имён L1-L5 в проверяемые утверждения). _(five-laws, distinction, reflexivity, classic)_

**Uniqueness - score 1 (exposition).** Превращает L1-L5 из имён-в-комментариях в машинно-проверяемые теоремы над структурой Distinction.
> _Caveat:_ Все пять — классическая логика; L1/L5 по сути reflexivity и стандартный порядок, L3 буквально = аксиома classic (не выводится). Это экспозиция/обрамление, не новый результат. Header пишет 'Qed' без числа; laws_theorem_count=22 совпадает с фактическим (22).

---

## #314 - `src/foundation/LevelComparison.v` - score 2 (methods)

**Comparability of concrete ordinals (nat, omega) over the ToS Ord type**

- **Topic.** Defines ord_le and proves nat order lifts to ord_lt, nat trichotomy/comparability, embedding preserves and reflects order, all finite ordinals below omega, ord_lt irreflexivity (via well-foundedness), and monotonicity under ord_add — plus concrete ToS-domain (D1..D6) comparisons.
- **Role.** Imports foundation.Ordinal + foundation.TransfiniteInduction. Provides comparability lemmas for the ordinal/Level layer; reused by transfinite/domain-level files.
- **Counts.** Qed 18 / Admitted 0 / axioms 0
- **Imports.** ToS: foundation.Ordinal; ToS: foundation.TransfiniteInduction; Stdlib: Lia/ZArith/List/Bool
- **E/R/R.** _Elements:_ nat_to_ord, omega; конкретные ординалы (D1..D6). _Roles:_ ord_le/сравнение/вложение/трихотомия как роли порядка. _Rules:_ структурная индукция по nat; конструкторы ord_lt; well_founded_ind для irrefl. _P4:_ сравнимы только КОНКРЕТНЫЕ ординалы (Element); общий ord_lt a (OSucc a) для предельных не выводим — честная граница.
- **Classical counterpart.** Comparability/trichotomy of ordinals and the nat embedding into ordinals are classical ordinal theory; NEW only as a constructive Coq development restricted to CONCRETE ordinals (nat, omega) over the project's own Ord type, honestly noting general ord_lt a (OSucc a) is not provable from the chosen constructors.
- **Tags.** foundation, ordinal, comparability, constructive, methods

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `ord_le/ord_le_refl/ord_lt_implies_le` | Definition/Lemma | <= через < или = |
| `nat_to_ord_lt/nat_le_compare/nat_trichotomy/two_finite_comparable` | Lemma | nat-порядок -> ord_lt; трихотомия; сравнимость |
| `nat_embed_preserves_lt/nat_embed_reflects_lt` | Lemma | вложение сохраняет и отражает порядок |
| `nat_lt_omega_all/ord_lt_irrefl/nat_ord_lt_trans_succ` | Lemma | конечные < omega; иррефлексивность; шаг succ |
| `ord_lt_add_r/d1_lt_d5/d_levels_ordered/finite_hierarchy_embeds/zero_lt_succ` | Lemma | монотонность по ord_add; конкретные сравнения |
| `tos_domains_comparable/tos_domains_below_omega` | Lemma | ToS-домены D1..D6 сравнимы и < omega |

**Key lemmas (deep):**

- **`ord_lt_irrefl`** - Иррефлексивность ord_lt через well_founded_ind по wf_ord_lt — единственное место с реальной индукцией по фундированности (остальное — nat-индукция, перенесённая через nat_to_ord). Это стандартная конструктивная ординальная техника; новизны нет, но реализация над собственным Ord-типом репозитория аккуратна и честна о пределах (общий succ-факт не доказуем). _(ordinal, well-founded, comparability, constructive)_

**Uniqueness - score 2 (methods).** Конструктивная сравнимость/трихотомия конкретных ординалов (nat, omega) над Ord-типом ToS с честным ограничением на предельные.
> _Caveat:_ Сравнимость и трихотомия ординалов — классика; здесь — лишь конкретный (нат+omega) фрагмент, общий случай (ord_lt a (OSucc a) для пределов) явно не доказуем из выбранных конструкторов. Это методы/инфраструктура, не новый результат.

---

## #315 - `src/foundation/LevelStructure.v` - score 2 (methods)

**Geometric levels: why n_metric = D(D+1)/2 = 10 (Level 0), not 20**

- **Topic.** Defines three GeometricLevels (pointwise/first-deriv/second-deriv) with DOF formulas, and proves the 4D values 10 (symmetric metric, Level 0) and 20 (Riemann, Level 2), asserting U(1)_Y acts at Level 0 so n_ambient=10.
- **Role.** Self-contained (Lia/PeanoNat). Companion to MetricDOFJustification.v; both feed the sin^2(theta_W)=3/13 narrative. No downstream dependents.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Lia; Stdlib: PeanoNat
- **E/R/R.** _Elements:_ GeometricLevel; DOF_at_level; U1_level; n_ambient. _Roles:_ U(1)_Y = поточечно = Level 0; Риман = Level 2. _Rules:_ локальная симметрия действует на Level 0; n_metric=10 'выведено'. _P4:_ конечные натуральные DOF-счёты (Element); 'почему 10' = выбор уровня действия симметрии (интерпретативно).
- **Classical counterpart.** Symmetric-tensor (10), Riemann (20) and Lorentz (6) DOF counts in 4D are elementary differential geometry; NEW only as a labelling that names U(1)_Y as acting at 'geometric Level 0' to justify picking the 10-count — a justification driving the over-branded sin^2(theta_W)=3/13 claim.
- **Tags.** foundation, dof, weinberg-angle, overbranded, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `GeometricLevel/DOF_at_level/U1_level/n_ambient` | Definition | уровни и формулы DOF; n_ambient=DOF(4,Level0) |
| `level0_D4/level2_D4/U1_is_level0/n_ambient_is_10` | Lemma | DOF(4,L0)=10; DOF(4,L2)=20; U1=L0; n_ambient=10 |
| `level_structure_synthesis` | Theorem | синтез: 10/20/n_ambient=10 |

**Key lemmas (deep):**

- **`n_ambient_is_10`** - Вся 'выводимость' держится на постулате, что U(1)_Y действует на компоненты метрики (симметричный тензор, Level 0), а не на Риман (Level 2) или изометрии (Lorentz, 6). Это ИНТЕРПРЕТАТИВНЫЙ выбор, подогнанный под нужное число 10, дающее sin^2=3/13. Доказательства — reflexivity на D(D+1)/2. По сути нумерология DOF, обёрнутая в 'геометрические уровни'. _(dof, metric, weinberg-angle, interpretive)_

**Uniqueness - score 2 (methods).** Маркирует U(1)_Y как симметрию 'геометрического Level 0', чтобы зафиксировать счёт DOF метрики = 10.
> _Caveat:_ Счёты 10/20/6 — школьная диф.геометрия (reflexivity). 'Почему 10' — НЕ вывод, а подгонка уровня действия под желаемый sin^2(theta_W)=3/13; это над-брендированное звено (см. MetricDOFJustification). Уровень: методы/обрамление, не результат.

---

## #316 - `src/foundation/LiouvilleBeyondAlgebraic.v` - score 3 (new-framing)

**Liouville process L=Sum 1/2^(k!): constructive transcendence signature beyond the algebraic decider**

- **Topic.** Builds the rational partial sums S_n=Sum 1/2^(k!) with denominator q_n=2^(n!), proves the super-exponential law q_{n+1}=q_n^(n+1), the Liouville gap S_{n+1}-S_n < 1/q_n^n at every n, and that S_n=p_n/q_n with p_n integer — the finitary part of 'L is transcendental'.
- **Role.** Self-contained (ZArith/QArith/Lqa/Lia/Factorial). Extends the project's finitization-boundary layer past H1AlgebraicDecider (algebraic=decidable) into the transcendental layer. No downstream dependents.
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: ZArith/QArith/Lqa/Lia/Arith/Factorial
- **E/R/R.** _Elements:_ стадии S_n=Sum 1/2^(k!) (рациональные); q_n=2^(n!); p_n=q_n*S_n in Z (конвергента). _Roles:_ L = роль-предел; 'алгебраично ли L' — следующий слой границы за разрешимым алгебраическим. _Rules:_ суперэкспонента q_{n+1}=q_n^(n+1) => зазор 1/q_n^(n+1) < 1/q_n^n на КАЖДОМ n => (Лиувилль) не алгебраично. _P4:_ L аппроксимируется рациональными p_n/q_n ДО ВСЕХ порядков (подпись); только процесс/стадии, без готового L.
- **Classical counterpart.** Liouville's construction L = Sum 1/2^(k!) and Liouville's approximation theorem (algebraic numbers are not approximable to all orders) are classical (1844); NEW only as a constructive, 0-axiom Coq formalization of the Liouville SIGNATURE (super-exponential gap + integer convergent) over the rational stages, citing (not re-proving) the transcendence conclusion.
- **Tags.** foundation, liouville, transcendence, finitization-boundary, new-framing

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `qden/lterm/lsum` | Definition | знаменатель 2^(n!); член; частичная сумма |
| `qden_pos/qden_ne/qden_superexp/qden_ge2/qden_pow_n_lt` | Lemma | ★ суперэкспонента q_{n+1}=q_n^(n+1); q_n^n < q_{n+1} |
| `Qinv_lt_pos/liouville_gap` | Lemma/Theorem | ★★ зазор S_{n+1}-S_n < 1/q_n^n (подпись Лиувилля) |
| `lsum_integer` | Lemma | ★ целая конвергента: q_n*S_n in Z |
| `qden_values/lsum2_value/liouville_beyond_algebraic` | Example/Theorem | конкретные стадии; капстоун |

**Key lemmas (deep):**

- **`liouville_gap`** - Главный технический результат: для каждого n зазор до следующей стадии < 1/q_n^n — это и есть аппроксимируемость 'до всех порядков', подпись трансцендентности по Лиувиллю. Доказано конструктивно над Z/Q (super-exp + reciprocal-monotonicity), 0 аксиом. Сам вывод 'L трансцендентно' — классическая теорема Лиувилля, честно процитирована, а не передоказана. _(liouville, transcendence, super-exponential, constructive)_

**Uniqueness - score 3 (new-framing).** Конструктивная 0-аксиомная формализация подписи Лиувилля (суперэкспонент. зазор + целая конвергента) — число за пределом алгебраического решателя репо, как процесс (P4).
> _Caveat:_ Конструкция L=Sum 1/2^(k!) и теорема о приближении — классика Лиувилля (1844); трансцендентность здесь НЕ доказана, а процитирована. Новизна = аккуратная финитарная подпись над стадиями + размещение на границе финитизации. Header заявляет 10 Qed — фактически 11 (две Example добавляют по одному; дрейф).

---

## #317 - `src/foundation/LithiumStructure.v` - score 2 (methods)

**Lithium (Z=3): Pauli-forced shell filling, core/valence, Slater screening — exact rational predictions**

- **Topic.** Hydrogen-like energy E_n(Z)=-Z^2/(2n^2) recovering H/He+, Li2+ third ionization exactly -9/2 Hartree, shell capacity 2n^2 (proved via SO(4) degeneracy), Pauli forcing a second shell, core/valence separation, and Slater sigma=17/10, Z_eff=13/10 giving first ionization 169/800 Hartree.
- **Role.** Imports foundation.HydrogenThreeFormulas/HydrogenStructure/HeliumStructure. Part of the atomic E/R/R composition chain (H->He->Li->C); reuses degeneracy_is_n_squared.
- **Counts.** Qed 27 / Admitted 0 / axioms 0
- **Imports.** ToS: foundation.HydrogenThreeFormulas/HydrogenStructure/HeliumStructure; Stdlib: QArith/Qabs/ZArith/List/PeanoNat/Lia/Lqa
- **E/R/R.** _Elements:_ уровни E_n(Z); ёмкости оболочек 2n^2; Slater sigma=17/10; Z_eff=13/10. _Roles:_ ядро (1s^2) vs валентность (2s^1) = разные роли; экранирование = роль-зависимая связь. _Rules:_ Z^2-скейлинг; Pauli форсирует 2-ю оболочку; Slater: sigma=2*(17/20); Z_eff=Z-sigma. _P4:_ конечные точные Q-предсказания; внутренняя связь (полностью ободранный ион) ТОЧНА, внешняя (Slater) ~6.6% — честная граница точности.
- **Classical counterpart.** Hydrogen-like Z^2 scaling, Pauli shell filling 2n^2, Slater screening, and lithium ionization energies are textbook atomic physics; NEW only as exact rational predictions in E/R/R form, with the third ionization exact and valence/Slater values honestly flagged as ~6.6% approximate.
- **Tags.** foundation, atomic, lithium, prediction, overbranded, methods

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `hydrogenic_E/hydrogenic_Z1_matches_H/hydrogenic_Z2_matches_Heplus/Z_Li/li_2plus_E` | Definition/Theorem | Z^2-скейлинг; согласование с H, He+ |
| `li_2plus_ground/_n2/_n3/li_scales_9x_hydrogen_n1/_n2` | Theorem | ★ Li2+ основное = -9/2; = 9*H (точно) |
| `shell_capacity/shell1_2/shell2_8/shell3_18/shell_capacity_is_2n_sq` | Definition/Theorem | ёмкость 2n^2 через SO(4)-вырождение |
| `li_requires_shell_2/li_ground_*/li_has_3_electrons/li_1s_full` | Theorem | Pauli форсирует 2-ю оболочку |
| `li_core_count/li_valence_count/core_plus_valence/core_is_full_shell/valence_is_partial` | Definition/Theorem | разделение ядро/валентность |
| `slater_per_inner_electron/li_slater_sigma/_value/li_Z_eff_valence/_value/li_2s_binding_slater/_value` | Definition/Theorem | ★ Slater sigma=17/10; Z_eff=13/10; связь 2s |
| `li_first_ionization/_value/_positive/li_third_ionization/_value/third_*/third_over_first_ratio/lithium_structure_complete` | Definition/Theorem | иерархия ионизаций; капстоун |

**Key lemmas (deep):**

- **`li_third_ionization_value`** - Третья ионизация (отрыв последнего e от водородоподобного Z=3) ТОЧНА = 9/2 Hartree = 122.45 эВ (<0.01% от опыта), потому что это чистая Z^2-задача. Это законное точное Q-предсказание. Контраст: первая ионизация через Slater даёт 169/800 (~6.6% ошибки) — честно помечено. Вся физика (Z^2, 2n^2, Slater) учебная; вклад = точная рациональная формализация в E/R/R. _(lithium, ionization, exact, slater)_

**Uniqueness - score 2 (methods).** Точные рациональные предсказания лития (Li2+ ионизация -9/2 точно, ёмкости 2n^2, Slater sigma=17/10) в E/R/R-форме над Q.
> _Caveat:_ Z^2-скейлинг, заполнение Паули 2n^2, экранирование Слейтера — классическая атомная физика; новой физики нет. 'Ёмкость 2n^2 = периодическая таблица' и 'core/valence из L3' — над-брендированные обороты (это просто Паули+вырождение). Header заявляет 25 Qed — фактически 27 (дрейф).

---

## #318 - `src/foundation/LogicalAtom.v` - score 1 (exposition)

**Logical atom: distinction as indivisible unit (integer gauge dims, spin quantization)**

- **Topic.** Posits 1 distinction = the atom of existence, proves trivial nat facts (atom is minimum, unsplittable, void unique), then frames integer gauge dimension SU(N)=N^2-1 and half-integer spin as consequences of distinctions being indivisible whole counts.
- **Role.** Imports foundation.Distinction/IndivisibleDistinction/ERRFromDistinction. Philosophical/foundation framing file; no downstream dependents. June 2026 wave-4 vacuity rollback: vacuous exists replaced: gauge_dimension_integer = INJECTIVITY of N->N^2-1 on positives (no two ladders share a dimension); spin_quantization = exclusive Even/Odd dichotomy; boson/fermion = real parity facts.
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** ToS: foundation.Distinction/IndivisibleDistinction/ERRFromDistinction; Stdlib: Lia/PeanoNat
- **E/R/R.** _Elements:_ logical_atom=1; logical_void=0; число различений = натуральное. _Roles:_ различение = неделимый атом существования; стороны различения = ориентации (спин). _Rules:_ нельзя ниже 1; SU(N)=N^2-1 (N=натуральное); спин 1/2 = одна сторона одного различения. _P4:_ существование атомарно (Element=натуральный счёт различений); нет SU(2.5), т.к. 2.5 различения невозможно.
- **Classical counterpart.** The integrality of SU(N) generator counts (N^2-1) and that natural quantities are >= 1 are trivial; the 'logical atom = distinction' is a philosophical analogy (Democritus/Leibniz). NEW only as a framing tying integer gauge dimension and spin half-integrality to 'distinction = indivisible unit'.
- **Tags.** foundation, distinction, gauge-dimension, philosophical, exposition

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `logical_atom/logical_void/atom_is_minimum/atom_unsplittable/existence_is_atomic/void_unique/compound_from_atoms` | Definition/Theorem/Lemma | атом=1, неделим, минимален; пустота=0 June 2026 wave-4 vacuity rollback: vacuous exists replaced: gauge_dimension_integer = INJECTIVITY of N->N^2-1 on positives (no two ladders share a dimension); spin_quantization = exclusive Even/Odd dichotomy; boson/fermion = real parity facts. |
| `gauge_dimension_integer/su2_dim/su3_dim/su5_dim` | Theorem/Lemma | целая размерность SU(N)=N^2-1 June 2026 wave-4 vacuity rollback: vacuous exists replaced: gauge_dimension_integer = INJECTIVITY of N->N^2-1 on positives (no two ladders share a dimension); spin_quantization = exclusive Even/Odd dichotomy; boson/fermion = real parity facts. |
| `spin_quantization/boson_even_sides/fermion_odd_sides` | Theorem/Lemma | спин = стороны/2; бозон/фермион по чётности June 2026 wave-4 vacuity rollback: vacuous exists replaced: gauge_dimension_integer = INJECTIVITY of N->N^2-1 on positives (no two ladders share a dimension); spin_quantization = exclusive Even/Odd dichotomy; boson/fermion = real parity facts. |
| `logical_atom_summary` | Theorem | сводка: минимум, неделимость, целые размерности June 2026 wave-4 vacuity rollback: vacuous exists replaced: gauge_dimension_integer = INJECTIVITY of N->N^2-1 on positives (no two ladders share a dimension); spin_quantization = exclusive Even/Odd dichotomy; boson/fermion = real parity facts. |

**Key lemmas (deep):**

- **`gauge_dimension_integer`** - Утверждает существование целого d=N^2-1 для каждого N (тривиальная nat-арифметика, lia). 'Объяснение' почему нет SU(2.5) — чисто словесное (2.5 различения невозможно); сама теорема не несёт этого содержания. Спин-half через 'две стороны одного различения' — тоже метафора поверх exists n, n=sides. Это философское обрамление с тривиальными nat-леммами как подпорками. _(distinction, gauge-dimension, spin, philosophical)_

**Uniqueness - score 1 (exposition).** Обрамляет неделимость различения как 'логический атом', связывая целочисленность размерностей SU(N) и полуцелость спина с дискретностью различений.
> _Caveat:_ Целочисленность N^2-1 и '>=1' — тривиальная nat-арифметика (lia/reflexivity); связь со спином/калибровкой — словесная аналогия, не доказывается леммами. Это экспозиция/философия, не результат. Header заявляет 15 Qed — фактически 13 (дрейф).

---

## #319 - `src/foundation/MandelbrotERR.v` - score 3 (new-framing)

**Mandelbrot set in Q^2: orbit classifier as R-process, membership as P4 obstruction**

- **Topic.** Implements complex arithmetic in Q*Q and the Mandelbrot iteration from z_0=0; verifies exact orbits at c=0 (period-1), -1 (period-2), -2 (pre-period-1), i (pre-period-2), 1 (escapes step 4), and the escape-radius theorem |c|^2>4 => escape at step 1.
- **Role.** Self-contained (QArith/Qabs/ZArith/List/PeanoNat/Lia/Lqa). E/R/R 'classifier' exemplar alongside Apery/Feigenbaum P4 cases. No downstream dependents.
- **Counts.** Qed 35 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith/Qabs/ZArith/List/PeanoNat/Lia/Lqa
- **E/R/R.** _Elements:_ c in Q*Q; итерации z_n точно вычислимы; mod_sq in Q. _Roles:_ M = КЛАССИФИКАТОР (период-k / escape), не множество-Element; поведение = роль c. _Rules:_ z_{n+1}=z_n^2+c, z_0=0; escape если \|z\|^2>4; одно правило, параметризованное c. _P4:_ per-step факты (escape на шаге n, периодичность) разрешимы; 'c in M' требует ВСЕ n => канонная P4-преграда (нет Element-формы).
- **Classical counterpart.** The Mandelbrot iteration z->z^2+c, its periodic/escape orbits and the escape radius \|c\|>2 are classical complex dynamics; NEW only as an exact Q[i]=Q^2 treatment framing M as an R-process classifier (not a set Element) with per-step decidable orbit facts, the canonical P4 obstruction.
- **Tags.** foundation, mandelbrot, complex-dynamics, p4-obstruction, new-framing

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `C/c_eq/c_zero/c_one/c_i/c_add/c_mul/c_sq/mod_sq` | Definition | комплексная арифметика в Q*Q |
| `mod_sq_zero/mod_sq_i/mandelbrot_step/mandelbrot_iter/escaped` | Definition/Theorem | итерация и предикат escape |
| `step_preserves_zero/orbit_at_zero_forever/c_zero_never_escapes` | Theorem | c=0 период-1 навсегда |
| `orbit_neg1_at_1..4/c_neg1_period_2_evidence` | Theorem | c=-1 период-2 цикл 0<->-1 |
| `orbit_neg2_*/c_neg2_mod_at_3/orbit_i_*/c_i_pre_period_2/orbit_pos1_*/mod_sq_pos1_at_4/c_pos1_escapes_at_4` | Theorem | пред-периоды; escape c=1 на шаге 4 |
| `iter_at_1/escape_radius_step1/c_3_escapes_at_1/c_3i_escapes_at_1/c_neg2_marginal_at_3/_not_escaped/mandelbrot_facts` | Lemma/Theorem | ★ радиус escape \|c\|^2>4; граничные точки; капстоун |

**Key lemmas (deep):**

- **`escape_radius_step1`** - Для любого c с \|c\|^2>4 орбита убегает уже на шаге 1 (т.к. iter 1 = c) — это разрешимая Q-граница: M содержится в диске \|c\|^2<=4. Сильнейшая часть файла, т.к. это утверждение про ВСЕ c, а не отдельные орбиты. Концептуально ценно обрамление: M — не множество-Element, а R-процесс-классификатор, и 'c in M' — каноничная P4-преграда (требует всех n). Сама динамика классическая. _(mandelbrot, escape-radius, p4-obstruction, classifier)_

**Uniqueness - score 3 (new-framing).** Точная Q^2-формализация орбит Мандельброта как R-процесса-классификатора: per-step разрешимость + членство 'c in M' как каноничная P4-преграда (нет Element-формы).
> _Caveat:_ Итерация z->z^2+c, периоды и радиус escape |c|>2 — классическая комплексная динамика; новой математики нет. Вклад = P4-обрамление (множество как процесс) + аккуратная рациональная реализация. Header заявляет 28 Qed — фактически 35 (дрейф: много Theorem-орбит).

---

## #320 - `src/foundation/MatterAsymmetry.v` - score 2 (methods)

**Matter>antimatter from distinction asymmetry (eta placeholder model)**

- **Topic.** Defines an asymmetry parameter eta(K)=1/(1+K^2), proves eta>0 always and perfect balance impossible, ties matter/antimatter weight to the marked/unmarked side of a Distinction, and frames the Sakharov conditions as aspects of distinction — header admits eta's form is a placeholder, not derived.
- **Role.** Imports foundation.Distinction/AsymmetricDistinction. Foundation 'physics from distinction' framing file; no downstream dependents.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** ToS: foundation.Distinction/AsymmetricDistinction; Stdlib: QArith/Qabs/Lia/Lqa
- **E/R/R.** _Elements:_ параметр асимметрии eta(K)=1/(1+K^2); вес материи/антиматерии. _Roles:_ материя = маркированная (positive) сторона; антиматерия = unmark; асимметрия различения -> асимметрия материи. _Rules:_ eta>0 всегда; баланс невозможен; материя > антиматерии (marked > unmarked). _P4:_ eta — процесс (nat-индексирован, не статичен); конкретная форма 1/(1+K^2) — ЗАГЛУШКА, не выведена (честно помечено).
- **Classical counterpart.** Baryogenesis and the Sakharov conditions are real open physics; NEW only as a philosophical claim that matter>antimatter follows from distinction asymmetry, with eta(K)=1/(1+K^2) an ADMITTEDLY placeholder model (positive, decreasing, never zero) — honestly flagged as not derived.
- **Tags.** foundation, baryogenesis, distinction, placeholder, methods

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `eta/eta_at_K0/eta_at_K1` | Definition/Lemma | eta(0)=1, eta(1)=1/2 |
| `eta_always_positive/balance_impossible` | Theorem | ★ eta>0; идеальный баланс невозможен |
| `matter_weight/antimatter_weight/matter_exceeds_antimatter/asymmetry_from_distinction` | Definition/Theorem | материя > антиматерии из marked>unmarked |
| `eta_not_constant/eta_decreasing_concrete/C_violation_from_asymmetry/matter_asymmetry_summary` | Theorem | eta убывает; C-нарушение; сводка |

**Key lemmas (deep):**

- **`balance_impossible`** - eta(K)>0 для всех K => идеальный баланс (eta=0) невозможен. Доказано честно над Q, но это полностью предопределено выбором eta=1/(1+K^2)>0 — заглушки, которую сам header признаёт не выведенной из решёточного действия. То есть 'материя побеждает антиматерию' здесь не выводится из физики, а закодировано в выборе положительной функции. Самый честный файл признаёт это прямо в комментарии. _(baryogenesis, asymmetry, placeholder, honesty)_

**Uniqueness - score 2 (methods).** Формализует 'материя>антиматерии' как следствие асимметрии различения (marked>unmarked) с положительным убывающим eta.
> _Caveat:_ Бариогенезис и условия Сахарова — реальная нерешённая физика; здесь eta=1/(1+K^2) — ЗАГЛУШКА (header признаёт: форма не выведена), так что положительность 'асимметрии' просто закодирована. Это методы/обрамление, не вывод. Header и matter_asymmetry_theorem_count=15 расходятся с фактическими 10 Qed (дрейф).

---

## #321 - `src/foundation/MeasurementSynthesis.v` - score 2 (methods)

**Measurement problem 'dissolved': measurement = distinction sharpening process**

- **Topic.** Defines measurement_at_K = distinction_sharpness K, proves it starts at 0 and increases, defines quantum (coherent) vs classical (decoherent) by coherence>1/2 vs <=1/2 with a smooth transition (K=0 quantum, K=1 boundary, K=2 classical), and asserts there is no sharp quantum/classical boundary.
- **Role.** Imports foundation.Distinction/DistinctionProcess (all values come from DistinctionProcess sharpness/coherence). Foundation 'physics dissolution' file; no downstream dependents.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** ToS: foundation.Distinction/DistinctionProcess; Stdlib: QArith/Lia/Lqa
- **E/R/R.** _Elements:_ measurement_at_K = distinction_sharpness K; coherence K. _Roles:_ измерение = процесс различения; суперпозиция = нерешённое различение; квант=низкий K, классика=высокий K. _Rules:_ нет постулата коллапса/ветвления; коллапс = различение завершено (L3 A v ~A решено); Борн = вес различения. _P4:_ граница квант/классика = просто разрешение K (не резкая); измерение = ТО ЖЕ различение, что основывает логику (процесс, не состояние).
- **Classical counterpart.** The quantum measurement problem and decoherence are real foundational physics; NEW only as a philosophical 'dissolution' reframing measurement as a distinction-sharpening process (coherence->0), with concrete values borrowed from DistinctionProcess.v — no collapse postulate, but no new physics either.
- **Tags.** foundation, measurement, decoherence, dissolution, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `measurement_at_K/measurement_starts_undecided/measurement_progresses/measurement_approaches_1` | Definition/Theorem | измерение стартует с 0 и растёт |
| `is_quantum/is_classical/K0_is_quantum/K1_is_boundary/K2_is_classical` | Definition/Theorem | квант/классика по coherence vs 1/2 |
| `no_sharp_boundary/measurement_unified` | Theorem | ★ нет резкой границы; сводка |

**Key lemmas (deep):**

- **`no_sharp_boundary`** - Утверждает is_quantum 0 /\ is_classical 2 — т.е. переход квант->классика плавный по K. Все числа (sharpness 0,1/2,2/3; coherence 1,1/2,1/3) импортированы из DistinctionProcess.v; этот файл лишь переименовывает их в 'измерение' и навешивает философский нарратив (нет коллапса, нет ветвления). Содержательной новой физики или математики нет — это пересборка чужих лемм под тезис 'проблема измерения растворена'. _(measurement, decoherence, dissolution, reframing)_

**Uniqueness - score 2 (methods).** Переобрамляет проблему измерения как процесс заострения различения (coherence->0), с плавной (не резкой) границей квант/классика.
> _Caveat:_ Проблема измерения и декогеренция — реальная физика; здесь нет нового механизма, только философское 'растворение' и переименование импортированных из DistinctionProcess значений. Это обрамление, не результат. Header и measurement_synthesis_theorem_count=15 расходятся с фактическими 8 Qed (дрейф).

---

## #322 - `src/foundation/MetricDOFJustification.v` - score 2 (methods)

**Why n_metric=10 not 20/6 — and the over-branded sin^2(theta_W)=3/13 claim**

- **Topic.** Proves the 4D DOF counts (sym=10, Riemann=20, Lorentz=6), computes sin2_with_ambient(3,ambient) for each, and argues only ambient=10 gives 3/13 ~ 0.2308 within 1% of the observed 0.2312, plus a kappa-chain alpha_EM/kappa = sin^2(theta_W).
- **Role.** Self-contained (QArith/Qabs/Lia/ZArith/Lqa). Companion to LevelStructure.v; the numerical core of the project's most over-branded physics claim. No downstream dependents.
- **Counts.** Qed 16 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith/Qabs/Lia/ZArith/Lqa
- **E/R/R.** _Elements:_ sym_tensor_dim/riemann_dim/lorentz_dim; sin2_with_ambient; kappa, alpha_EM. _Roles:_ U(1)_Y действует на КОМПОНЕНТЫ метрики (симм. тензор), не на производные/изометрии. _Rules:_ локальная симметрия поточечна => Level 0 => ambient=10; только 10 даёт 3/13. _P4:_ конечные Q-вычисления (Element); 'только метрика совпадает с опытом' — подгонка ambient под желаемое число.
- **Classical counterpart.** Symmetric-tensor (10), Riemann (20), Lorentz (6) DOF counts and a Weinberg-angle ratio are standard; this file's sin^2(theta_W)=3/13 'matching experiment' is an OVER-BRANDED numerical coincidence — the ambient count 10 is hand-picked precisely because only it yields 3/13.
- **Tags.** foundation, weinberg-angle, 3/13, overbranded, methods

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `sym_tensor_dim/sym_dim_2/3/4` | Definition/Lemma | симм.тензор D(D+1)/2; D=4 -> 10 |
| `riemann_dim/riemann_dim_4/lorentz_dim/lorentz_dim_4` | Definition/Lemma | Риман=20; Лоренц=6 (альтернативы) |
| `sin2_with_ambient/sin2_metric/sin2_riemann/sin2_lorentz` | Definition/Lemma | sin^2 для каждого выбора ambient (3/13, 3/23, 1/3) |
| `sin2_observed/metric_error_small/metric_error_lt_1pct/riemann_too_small/lorentz_too_large/SU2_inside_Lorentz` | Definition/Lemma | ★ только метрика в пределах 1%; альтернативы мимо |
| `kappa/alpha_EM/alpha_EM_value/alpha_over_kappa/metric_DOF_justification` | Definition/Lemma/Theorem | ★ kappa-цепь; alpha/kappa=sin^2; капстоун |

**Key lemmas (deep):**

- **`metric_error_lt_1pct`** - \|3/13 - 0.2312\| < 1% — машинно верно, но это и есть над-брендирование: ambient=10 выбран ИМЕННО потому, что только он даёт 3/13 (Риман 3/23 и Лоренц 1/3 мимо). 'Вывод' sin^2(theta_W)=3/13 — численное совпадение, обоснованное интерпретативным выбором уровня действия U(1)_Y, а не первопринципным расчётом. alpha_EM/kappa=3/13 — тавтология (alpha_EM определён как (3/13)*kappa). Этот файл — образцовый пример, который надо помечать в caveat по заданию. _(weinberg-angle, 3/13, overbranded, numerology)_

**Uniqueness - score 2 (methods).** Показывает, что среди счётов DOF (10/20/6) только метрический 10 даёт sin^2(theta_W) в пределах 1% от опыта.
> _Caveat:_ ОВЕР-БРЕНД: sin^2(theta_W)=3/13 — численное совпадение; ambient=10 подобран под результат (альтернативы отброшены post hoc), 'почему U(1)_Y на Level 0' — интерпретация, не вывод. alpha_EM/kappa=3/13 тавтологично (по определению alpha_EM). Счёты DOF — школьная геометрия. Header заявляет 15 Qed — фактически 16 (дрейф). Не вывод физики.

---

## #323 - `src/foundation/MillenniumHonesty.v` - score 3 (new-framing)

**Honest Millennium ledger: YM/NS capstones overclaim, RH is the gold standard**

- **Topic.** A machine-checked ledger tagging each Millennium problem with {Reading-2 (process/Element) proved, Reading-1 (continuum Millennium) open, header honesty}; locates ProofClosure (YM) and MillenniumComplete (NS) as overclaimers, credits RH_FinalAssessment as honest, flags NS 'Unconditional' as false (it lists axioms).
- **Role.** Self-contained (no imports). Meta-honesty audit over gauge/zeta/navier_stokes capstones; the gap Reading-2->Reading-1 is identified as the finitization boundary H1. No downstream dependents.
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** 
- **E/R/R.** _Elements:_ три задачи Millennium; для каждой {R2 доказано, R1 открыто, честность шапки}. _Roles:_ Reading 2 = Element-сторона (доказано); Reading 1 = role-limit (континуум, открыто); зазор = H1. _Rules:_ ни одно классич. Millennium-утверждение не доказано; процесс-утверждение — да; оверклеймеры локализованы. _P4:_ оверклейм = риторика пересекает границу финитизации (H1), где математика не пересекает; реестр, не переписывание.
- **Classical counterpart.** No classical analogue — this is an internal meta-audit. It records that the repo's Yang-Mills (ProofClosure.v) and Navier-Stokes (MillenniumComplete.v) capstones OVERCLAIM (name promises more than the lattice/process proof delivers), while the Riemann capstone is honest.
- **Tags.** foundation, honesty, millennium, self-audit, new-framing

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `MProblem/Honesty/MStatus/status` | Definition | три задачи; статус каждой (R2/R1/честность) |
| `no_reading1_proved/all_reading2_proved` | Lemma | ★ R1 открыто для всех; R2 доказано для всех |
| `overclaimers_located/riemann_is_honest/ns_not_unconditional` | Lemma | ★ YM/NS оверклеймят; RH честен; NS 'unconditional' ложно |
| `Reading/Side/reading_side/millennium_gap_is_finitization/millennium_honesty` | Definition/Lemma/Theorem | зазор R2->R1 = граница финитизации; капстоун |

**Key lemmas (deep):**

- **`ns_not_unconditional`** - Машинно фиксирует, что Navier-Stokes-капстоун MillenniumComplete.v называет себя 'Unconditional', хотя его собственный header перечисляет 5 аксиом (classic, L4_witness, B_antisym, C_B_positive, B_coeff_bounded) — значит 'безусловно' ложно. Это ценный внутренний аудит честности (само-критика репо), но формально файл лишь кодирует булевы теги в enum и доказывает reflexivity. Содержание = суждение автора о других файлах, а не математика. _(honesty, overclaim, millennium, self-audit)_

**Uniqueness - score 3 (new-framing).** Машинно-проверяемый честный реестр: ни одно классическое Millennium-утверждение в репо не доказано (R1 открыто), доказана только процесс-сторона (R2); YM/NS-капстоуны оверклеймят, RH — эталон.
> _Caveat:_ Это мета-аудит, а не математический результат: доказательства — reflexivity над крошечным enum булевых тегов. Сама ценность (само-критика над-брендированных капстоунов и привязка зазора R2->R1 к границе финитизации) реальна, но это обрамление/честность, не теорема. 0 аксиом, header совпадает (7 Qed).

---

## #324 - `src/foundation/MinimalLengthDerivation.v` - score 2 (methods)

**Minimal-length derivation audit: value posited, energy scaling derived (parameter-free)**

- **Topic.** Models the deviation factor effect(l,k)=(l*k)^2, proves the energy scaling is l-independent (effect ratio = (k2/k1)^2, one anchor fixes the whole curve), the dimensionful scale is not derived (different l differ), and the leading coefficient is realization-dependent — tagged Derived/Posited/RealizationDependent.
- **Role.** Self-contained (QArith/Lqa). Part of a MinimalLength* honesty cluster (with Dispersion/IsUnit/NoPosit); same derived/posited spirit as WeinbergAudit. No downstream dependents.
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; Stdlib: Lqa
- **E/R/R.** _Elements:_ effect l k=(l*k)^2; масштабирование effect(k1)*k2^2=effect(k2)*k1^2; lattice_coeff=1/24. _Roles:_ масштабирование = Derived (параметр-свободно); масштаб l = Posited (один якорь); коэфф. = RealizationDependent. _Rules:_ l входит только через l*k; ratio = (k2/k1)^2 (l сокращается); один якорь фиксирует кривую. _P4:_ ЧЕСТНО: значение НЕ выводимо (размерный якорь + выбор реализации), но СТРУКТУРА/масштабирование выводимы и параметр-свободны (тестируемо).
- **Classical counterpart.** Lorentz-invariance-violating dispersion corrections from a minimal length and their energy scaling are standard quantum-gravity phenomenology (and Fermi-LAT tests them); NEW only as an honest derivation-audit: the dimensionful value is NOT derived, but the parameter-free energy scaling IS.
- **Tags.** foundation, minimal-length, quantum-gravity, honesty, methods

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `effect/scaling_param_free/one_anchor_determines/ex_scaling` | Definition/Lemma | ★ масштабирование l-независимо; один якорь => вся кривая |
| `scale_not_derived` | Lemma | ★ размерный масштаб не выводим (разные l различны) |
| `lattice_coeff/causal_set_leading_coeff/coeff_realization_dependent` | Definition/Lemma | коэффициент зависит от реализации (1/24 vs 0) |
| `Aspect/Tag/audit/audit_verdict/minimal_length_derivation` | Definition/Lemma/Theorem | теги Derived/Posited/RealizationDependent; капстоун |

**Key lemmas (deep):**

- **`scaling_param_free`** - Энергетическое масштабирование effect(k2)/effect(k1)=(k2/k1)^2 не зависит от l (l сокращается, доказано ring) — это и есть параметр-свободная, Fermi-LAT-тестируемая часть. Файл честно разделяет: структура/скейлинг выводимы, размерное ЗНАЧЕНИЕ l — нет (нужен якорь), коэффициент зависит от реализации (решётка 1/24 vs causal-set 0). Физика (LV-дисперсия) известна; вклад = аккуратный аудит выводимого/постулируемого без переклейма 'вывели l_Planck'. _(minimal-length, dispersion, derived-vs-posited, honesty)_

**Uniqueness - score 2 (methods).** Честный аудит минимальной длины: размерное значение НЕ выводимо (нужен якорь), но параметр-свободное энергетическое масштабирование выводимо и тестируемо.
> _Caveat:_ LV-дисперсия от минимальной длины и её энергетическое масштабирование — стандартная феноменология квантовой гравитации (Fermi-LAT). Здесь не выводится размерное число; всё — рациональные ring-тождества + теги. Это методы/честное обрамление, не новая физика. 0 аксиом, header совпадает (7 Qed).

---

## #325 - `src/foundation/MinimalLengthDispersion.v` - score 3 (new-framing)

**Minimal-length dispersion: the falsifiable edge (energy-dependent signal => length bound)**

- **Topic.** Models the leading fractional dispersion signal corr(ell,k)=(ell k)^2/24, proves it is positive (discreteness detectable), strictly increasing in probe momentum (the time-of-flight signature), shrinks as ell->0, and that an observational ceiling eps is equivalent to (ell k)^2 <= 24 eps — a toy falsifiable prediction.
- **Role.** Self-contained (QArith/Lqa). Falsifiability layer of the MinimalLength* cluster; complementary to stdlib/ProcessLatticeDispersion.v. No downstream dependents.
- **Counts.** Qed 15 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; Stdlib: Lqa
- **E/R/R.** _Elements:_ рациональный сигнал frac_signal=(ell k)^2 и corr=(ell k)^2/24; конкретные значения. _Roles:_ ell = минимальная длина (искомое конечное число); k = энергия зонда; eps = наблюдательный потолок. _Rules:_ дискретность => ненулевой энергозависимый сигнал => потолок eps форсирует (ell k)^2 <= 24 eps. _P4:_ ТОЙ/структурная модель (не Fermi-LAT); граница на КВАДРАТ рациональна (Element), сама ell=корень (role-limit) за стеной H1.
- **Classical counterpart.** Lattice dispersion omega=(2/ell)sin(ell k/2)=k(1-(ell k)^2/24+...) and time-of-flight Lorentz-violation tests (Fermi-LAT) are standard; NEW only as a 0-axiom toy/structural Coq model of the FALSIFIABLE SHAPE (nonzero, energy-dependent signal => length bound), explicitly not a Fermi-LAT fit.
- **Tags.** foundation, minimal-length, dispersion, falsifiability, new-framing

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `Q24_pos/Q24_nz/Hid24/Qsqr_lt` | Lemma | факты про 24; монотонность квадрата (рабочая лошадка) |
| `frac_signal/corr/frac_pos` | Definition/Lemma | ★ сигнал положителен (дискретность детектируема) |
| `frac_energy_dependent/frac_shrinks_with_ell` | Lemma | ★ сигнал растёт с энергией (smoking gun); -> 0 при ell->0 |
| `corr_le_iff/signal_exceeds_excluded` | Lemma | ★ потолок eps <=> (ell k)^2 <= 24 eps; превышение исключает ell |
| `corr_1_1/corr_energy_concrete/corr_shrinks_concrete/toy_signal_exceeds/toy_excluded/minimal_length_falsifiable` | Lemma/Theorem | конкретные числа; той-фальсификация; капстоун |

**Key lemmas (deep):**

- **`corr_le_iff`** - Эквивалентность 'наблюдательный потолок corr<=eps' <=> '(ell k)^2 <= 24 eps' переводит null-наблюдение в явную верхнюю границу на минимальную длину — это и есть фальсифицируемое ядро. H1-штрих честен: граница на КВАДРАТ рациональна (Element), сама ell=sqrt(24 eps)/k — корень (role-limit). Физика решёточной дисперсии классическая, sin заменён рациональной головой Тейлора; числа иллюстративны (не Fermi-LAT). Машинно-проверена именно ФОРМА предсказания. _(minimal-length, dispersion, falsifiability, toy-model)_

**Uniqueness - score 3 (new-framing).** 0-аксиомная машинно-проверенная ФОРМА фальсифицируемого предсказания минимальной длины: дискретность => ненулевой энергозависимый сигнал => явная верхняя граница (ell k)^2 <= 24 eps.
> _Caveat:_ Решёточная дисперсия omega=k(1-(ell k)^2/24+...) и time-of-flight тесты (Fermi-LAT) — стандартная феноменология; это ТОЙ-модель (ведущий порядок, sin -> рациональный Тейлор, числа иллюстративны), НЕ воспроизведение анализа Fermi-LAT. Вклад = аккуратное обрамление фальсифицируемости + граница H1, не новая физика.

---

## #326 - `src/foundation/MinimalLengthIsUnit.v` - score 2 (methods)

**Minimal length is a unit: count<->length dictionary, value is gauge**

- **Topic.** Models length_of_count(g,n)=g*n, proves length ratios are g-free (= count ratios), rescaling g leaves every dimensionless ratio invariant, minimal length/time are one posit g with derived conversion (min_length=c*min_time), and different g give different absolute lengths (a convention).
- **Role.** Self-contained (QArith/Lqa). Refines the MinimalLength* cluster's 'Posited' tag from 'a gap' to 'a category necessity'; imported by MinimalLengthNoPosit.v.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; Stdlib: Lqa
- **E/R/R.** _Elements:_ length_of_count g n=g*n; отношения g-свободны; min_length=c*min_time. _Roles:_ счёт = Element-физика; g = единица/словарь (мост счёт<->длина); отношения = выведенные (g-свободны). _Rules:_ длина = счёт*единица; безразмерное = g-инвариантно (выведено); g = конвенция (единица, не дыра). _P4:_ g — конвертер Element-счёта в role-limit-длину; всё безразмерное выведено и g-инвариантно; постулируется одна конвенция.
- **Classical counterpart.** Dimensional analysis and the fact that units (e.g. '1 meter') are conventions, not derived, are elementary; NEW only as a conceptual reframing: the 'posited minimal length' is a count<->length UNIT, so its value is a gauge while all dimensionless content is derived and unit-invariant.
- **Tags.** foundation, minimal-length, units, dimensional-analysis, methods

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `length_of_count/length_ratio_unit_free` | Definition/Lemma | ★ отношение длин = отношение счётов (g сокращается) |
| `ratio_g_invariant/ex_ratio` | Lemma | ★ перешкалирование g не меняет безразмерных отношений |
| `min_time/min_length/length_time_ratio_fixed` | Definition/Lemma | один постулат g; отношение min_length/min_time=c фиксировано |
| `value_is_convention/minimal_length_is_unit` | Lemma/Theorem | ★ разные g => разные длины (конвенция); капстоун |

**Key lemmas (deep):**

- **`ratio_g_invariant`** - Перешкалирование единицы g1->g2 оставляет любое безразмерное отношение инвариантным (ring-тождество) — формальная подпорка тезиса 'g — калибровка длины, конвенция'. Содержательно это переупаковка элементарного факта размерного анализа (единицы не выводятся) в язык H1 (счёт=Element, длина=role-limit, g=словарь). Доказательства тривиальны (ring/lra); ценность чисто концептуальная — почему 'постулируется' не есть слабость теории. _(minimal-length, units, gauge, dimensional-analysis)_

**Uniqueness - score 2 (methods).** Уточняет, почему минимальная длина постулируется: она — единица (словарь счёт<->длина), её значение = калибровка, а всё безразмерное выводимо и единице-инвариантно.
> _Caveat:_ Это элементарный размерный анализ (единицы — конвенции, '1 метр' не выводится), переписанный в язык H1. Все леммы — тривиальные ring/lra-тождества; новой математики/физики нет. Концептуальное обрамление, не результат. 0 аксиом, header совпадает (6 Qed).

---

## #327 - `src/foundation/MinimalLengthNoPosit.v` - score 2 (methods)

**Minimal length adds no new posit: existence=P4, structure=theorem, value=gauge**

- **Topic.** Decomposes the 'posited minimal length' into three components: existence is P4 (framework floor, not new), structure is a theorem (length_of_count determined by the unit L(1), forced by additivity), and value is a vacuous gauge — so none is a new physical postulate.
- **Role.** Imports foundation.MinimalLengthIsUnit. The 'true floor' of the MinimalLength* honesty cluster; refines the earlier 'Posited' tags. No downstream dependents.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** ToS: foundation.MinimalLengthIsUnit; Stdlib: QArith; Stdlib: Lqa
- **E/R/R.** _Elements:_ length g n=(length g 1)*n; значение калибровочно; нет нового поста. _Roles:_ существование = P4 (пол); структура = теорема; значение = калибровка; ни одно = новый физ. постулат. _Rules:_ минимальная длина не добавляет поста: P4 (существование) + теорема (структура) + калибровка (значение). _P4:_ 'постулат' расщепляется: Существование=P4 (рамочный пол, не новое), Структура=теорема (линейность из аддитивности), Значение=пустая калибровка.
- **Classical counterpart.** That a linear measure is determined by its value at 1 (additivity => linearity) and that units are conventions are elementary; NEW only as a conceptual decomposition arguing the minimal length adds NO new physical posit (existence=P4, structure=theorem, value=gauge).
- **Tags.** foundation, minimal-length, posit-reduction, honesty, methods

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `unit_is_length_of_one/structure_determined_by_unit` | Lemma | ★ карта длины определена единицей L(1) (форма вынуждена) |
| `value_is_gauge` | Lemma | значение калибровочно (из ratio_g_invariant) |
| `Component/Source/source/is_new_physical_posit/no_new_posit` | Definition/Lemma | ★ ни один компонент не новый физ. постулат |
| `minimal_length_no_new_posit` | Theorem | капстоун: нет нового поста сверх P4 |

**Key lemmas (deep):**

- **`structure_determined_by_unit`** - length_of_count g n = (length_of_count g 1)*n — карта длины определяется значением в счёте 1 (ring-тождество), что подаётся как 'структура = теорема, а не постулат'. Вместе с value_is_gauge и enum source это даёт тезис: минимальная длина не вводит ничего сверх P4. Содержательно — переформулировка элементарной линейности+конвенции единиц; доказательства тривиальны. Уровень — концептуальная гигиена постулатов, не математика. _(minimal-length, posit-reduction, additivity, gauge)_

**Uniqueness - score 2 (methods).** Декомпозиция: минимальная длина не добавляет нового физ. постулата — существование=P4, структура=теорема (линейность), значение=пустая калибровка.
> _Caveat:_ Линейность из аддитивности (мера определена значением в 1) и конвенциональность единиц — элементарны; все леммы тривиальные ring/lra. Это концептуальное обрамление редукции постулатов, не результат. 0 аксиом, header совпадает (5 Qed).

---

## #328 - `src/foundation/MonicRationalRoot.v` - score 3 (new-framing)

**General rational root theorem (monic): rational root => integer, via divisibility**

- **Topic.** Represents a monic polynomial by its lower coefficients cs, defines the cleared value mhom=a^n+g where g is the lower homogenized sum, proves b|g, and concludes a rational root a/b (lowest terms) of any monic integer polynomial has b=1 (integer), subsuming x^2-2 and x^3-2 (Delian cube root).
- **Role.** Builds on algebra.RationalRootTest (coprime_div_pow_unit / Gauss). Supersedes the pure-root form of RationalRootEigenvalue.v with the arbitrary-monic case; framed for the eigenvalue-rationality criterion.
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** ToS: algebra.RationalRootTest; Stdlib: ZArith/Lia/Znumtheory/List
- **E/R/R.** _Elements:_ монический полином = младшие коэфф. cs (ведущий x^n неявно), n=length cs; mhom=a^n+g. _Roles:_ рациональный корень a/b <=> mhom=0; критерий = делимость на b. _Rules:_ g (младшая сумма) делится на b (каждый член b^{>=1}) => a^n=-g делится на b => (Гаусс) b=+-1 => b=1. _P4:_ рациональный корень ПРОИЗВОЛЬНОГО монического => ЦЕЛЫЙ = общий n*n критерий рациональности собств. значения; решается конечным перебором кандидатов.
- **Classical counterpart.** The rational root theorem (a rational root of a monic integer polynomial is an integer) and Gauss's lemma are classical; NEW only as a fresh, list-coefficient Coq formulation avoiding List.last/length-1 pitfalls, framed as the n*n eigenvalue-rationality criterion building on algebra.RationalRootTest.
- **Tags.** foundation, rational-root, gauss, divisibility, new-framing

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `zpow_S/g/g_cons/g_div_b` | Lemma/Definition | ★ младшая сумма g делится на b (каждый член несёт b^{>=1}) |
| `mhom/rational_root_monic_is_integer` | Definition/Theorem | ★★ рациональный корень монического => целый (b=1) |
| `mhom_x2_minus_2/sqrt2_root_is_integer` | Lemma/Corollary | x^2-2 (Delta=8) подчинён общему |
| `mhom_x3_minus_2/cbrt2_root_is_integer/monic_rational_root_criterion` | Lemma/Corollary/Theorem | x^3-2 (делийский корень); капстоун |

**Key lemmas (deep):**

- **`rational_root_monic_is_integer`** - Полный рациональный корневой тест для ПРОИЗВОЛЬНОГО монического целого полинома: из mhom=0 следует a^n=-g, b\|g (g_div_b), значит b\|a^n, и по Гауссу (coprime_div_pow_unit) b=1. Доказательство — чистая делимость (Z.divide), без ring на абстрактных списках, без List.last — это и есть 'свежая формулировка', обходящая ловушки первой попытки. Сама RRT классическая; вклад = аккуратная сборка общего случая, на которую опирается n*n критерий рациональности собств. значений. _(rational-root, gauss, divisibility, eigenvalue)_

**Uniqueness - score 3 (new-framing).** Общий рациональный корневой тест (произвольный монический целый полином => рациональный корень целый) свежей делимостной формулировкой; = n*n критерий рациональности собственного значения.
> _Caveat:_ Сама теорема о рациональном корне и лемма Гаусса — классика (опирается на algebra.RationalRootTest). Новизна — переформулировка через младшие коэффициенты (обход List.last/length-1) + обрамление как eigenvalue-критерий; полный матричный n*n тест ещё требует вычисления char-полинома (не строится). 0 аксиом, header совпадает (9 Qed).

---

## #329 - `src/foundation/NatureBoundaryLedger.v` - score 3 (new-framing)

**Nature vs finitization ledger: data disciplines (refutes naive lattice), does not crown**

- **Topic.** Five observational windows with verdicts: quantization SupportsFinite, Lorentz dispersion RefutesNaiveLattice (Fermi-LAT 6/5 > naive 1), spatial finiteness Undecided, Lambda NotDerived (~10^-122 vs O(1) bound), holographic info SupportsFinite — a mixed 2-support/1-refute ledger selecting a Lorentz-invariant (causal-set) substrate.
- **Role.** Self-contained (QArith/Lqa/List). Confronts the finitization boundary (from MinimalLengthDispersion) with published numbers; references GravityFinitization's O(1) bound. No downstream dependents.
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; Stdlib: Lqa; Stdlib: List
- **E/R/R.** _Elements:_ реальные числа: Fermi-LAT 6/5 vs наивное 1; водород 1/4; O(1) vs ~10^-122; Бекенштейн A/4. _Roles:_ каждое окно даёт вердикт; конечность НАБЛЮДАЕМЫХ (подтверждено) vs дискретность СУБСТРАТА (решётка опровергнута). _Rules:_ конфронтация предсказания с наблюдением; проверка ДИСЦИПЛИНИРУЕТ (вплоть до опровержения), не коронует. _P4:_ природа подтверждает конечную актуальность на уровне наблюдаемых/голографии, но опровергает наивную регулярную решётку (Fermi-LAT) на уровне субстрата.
- **Classical counterpart.** Atomic spectra discreteness, the Fermi-LAT GRB 090510 bound M_QG,1/M_Planck>1.2, near-flat curvature, the ~10^-122 cosmological constant, and the Bekenstein bound are real observational/theoretical facts; NEW only as a machine-checked ledger letting the data REFUTE the naive regular-lattice realization of P4.
- **Tags.** foundation, finitization, fermi-lat, honesty, new-framing

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `Window/Verdict/verdict/verdicts_assigned` | Definition/Lemma | пять окон и их вердикты |
| `naive_lattice_ratio/fermi_lower_bound/naive_lattice_excluded/naive_lattice_ruled_out` | Definition/Lemma | ★ Fermi-LAT 6/5 > наивное 1 => решётка исключена |
| `hydrogen_ratio_2_1/hydrogen_ratio_rational/sho_gap/sho_gap_0/sho_gap_1` | Definition/Lemma | квантование: водород 1/4; SHO лестница 2n+1 (Element) |
| `lambda_not_explained/bekenstein/bekenstein_finite` | Lemma/Definition | Lambda не объяснена; голографическая конечность |
| `all_windows/is_supports/is_refutes/n_supports/n_refutes/_eq/nature_disciplines_boundary` | Definition/Lemma/Theorem | ★ баланс 2 support/1 refute; капстоун |

**Key lemmas (deep):**

- **`naive_lattice_ruled_out`** - Самый острый зуб файла: наивная регулярная пространственная решётка предсказывает линейное LV на планковском масштабе (ratio=1), а Fermi-LAT даёт M_QG/M_Planck > 6/5; 1 < 6/5 => регулярно-решёточная реализация P4 ИСКЛЮЧЕНА. Это редкий случай, где проверка режет ПРОТИВ собственной наивной теории — честная дисциплина. Важно различение (в комментариях): конечность НАБЛЮДАЕМЫХ подтверждена, но дискретность СУБСТРАТА (решётка) опровергнута; жизнеспособна Lorentz-инвариантная (causal-set) финитизация. Все числа — реальные опубликованные. _(fermi-lat, lattice-refuted, finitization, honesty)_

**Uniqueness - score 3 (new-framing).** Машинно-проверяемый реестр конфронтации финитизации с природой, где данные (Fermi-LAT 6/5 > 1) ОПРОВЕРГАЮТ наивную регулярно-решёточную реализацию P4; смешанный баланс, проверка дисциплинирует.
> _Caveat:_ Все числа (квантование, Fermi-LAT 6/5, ~10^-122, Бекенштейн) — известные опубликованные факты; доказательства — рациональные неравенства + reflexivity над enum вердиктов. 'Наивная решётка => ratio=1' — упрощение (не строгий вывод). Это честное обрамление/аудит, не новый результат; различение наблюдаемой конечности vs дискретности субстрата — ценное наблюдение. 0 аксиом, header совпадает (11 Qed).

---

## #330 - `src/foundation/NestedDimensionsOpenTower.v` - score 3 (new-framing)

**Nesting tower as open process of dimensions: finite depth (Element), no maximum (role-limit)**

- **Topic.** Reads the Level tower as dimensions: dimension=nesting depth, ascend=embed (up one), descend=forget (down one) with descend.ascend=id; containment strictly monotone in depth; you can always ascend (open up), L1 is the floor, no maximal level exists, yet every level has finite depth reached from L1.
- **Role.** Self-contained (Arith/Lia; Level replicated from Core_ERR to stay leaf-clean). Metaphysics-hint file; relates to DimensionRoleLimit/LevelStructure/LevelFunctors but formalizes the tower-as-process itself. No downstream dependents.
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith; Stdlib: Lia
- **E/R/R.** _Elements:_ уровни L1, LS L1, LS(LS L1)... — ступени; база L1 = дно; каждый достижим из базы за КОНЕЧНО шагов. _Roles:_ 'измерение' = глубина вложенности (depth=ранг); 'переход' = шаг ascend(embed)/descend(forget). _Rules:_ P1 — высший строго содержит низший (level_lt => depth<depth); всегда есть преемник (открыто вверх); L1 — дно; descend.ascend=id. _P4:_ каждый уровень КОНЕЧНОЙ глубины (Element), НО башня без максимума (role-limit) => 'все измерения' = ОТКРЫТЫЙ ПРОЦЕСС, не завершённый объект.
- **Classical counterpart.** A well-founded successor tower (like the natural numbers / unbounded ordinals) with finite-depth elements but no maximum is standard; NEW only as a reframing reading the Level nesting tower as 'dimensions with transitions', an instance of the project flagship 'X = open process, not a completed object'.
- **Tags.** foundation, nesting, dimension, open-process, new-framing

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `Level/level_lt/depth/dimension` | Definition | башня; порядок; глубина = измерение |
| `ascend/descend/ascend_dim/descend_ascend/descend_LS` | Definition/Lemma | ★ embed/forget; descend.ascend=id (единица адъюнкции) |
| `level_lt_depth` | Lemma | ★ содержание строго монотонно по глубине (P1) |
| `can_always_ascend/floor_L1/no_maximal_level` | Lemma | ★★ всегда вверх; L1 — дно; НЕТ максимума (role-limit) |
| `iterLS/iterLS_dim/reached_from_base/dimension_L1/dimension_three/nested_dimensions_open_tower` | Definition/Lemma/Theorem | ★★ конечная достижимость из базы (Element); капстоун |

**Key lemmas (deep):**

- **`no_maximal_level`** - Башня уровней не имеет максимума (любой кандидат Lmax превзойдён LS Lmax), при этом reached_from_base показывает: каждый уровень достижим из L1 за depth(l) шагов (конечно). Комбинация 'конечно-каждый + нет-максимума-в-целом' — подпись Element/role-limit, применённая к измерению: 'бесконечномерие' = открытый процесс, не завершённый стек. Математически это просто свойства nat-подобной фундированной башни (lia); новизна — обрамление 'измерение=процесс' (флагман репо) и явная адъюнкция descend.ascend=id. _(nesting, dimension, open-process, well-founded)_

**Uniqueness - score 3 (new-framing).** Читает башню вложенности Level как 'измерения с переходами': конечная глубина каждого (Element) + отсутствие максимума (role-limit) => измерения суть ОТКРЫТЫЙ ПРОЦЕСС (флагман 'X = процесс').
> _Caveat:_ Свойства фундированной башни с преемником, конечной глубиной и без максимума — стандартны (как nat/неограниченные ординалы); все доказательства тривиальны (lia/reflexivity). Формализуется СТРУКТУРА башни, не физический механизм перехода между пространственными измерениями. Уровень — обрамление, не результат. 0 аксиом, header совпадает (12 Qed).

---

## #331 - `src/foundation/NestedDistinction.v` - score 2 (methods)

**SM gauge group [3,2,1] from nested distinctions (interpretive constraints)**

- **Topic.** Defines a NestedDistinction (depth + roles-at-level), the SM distinction sm_distinction with decomposition [2,3,1], total 6 roles and 12 gauge generators, and three constraints (depth1 binary, depth2>=3 no-repeat, depth3 reflexive) it claims [2,3,1] uniquely satisfies — header admits the constraints are 'reasonable but partially interpretive'.
- **Role.** Foundation file 10/14 of the SM-from-distinction chain. Imports Distinction/ERRFromDistinction/LawsFromDistinction; defines nested_distinction_theorem_count := 25. Bottleneck per CLAUDE.md (sm_distinction, gauge_generators).
- **Counts.** Qed 17 / Admitted 0 / axioms 0
- **Imports.** ToS: foundation.Distinction/ERRFromDistinction/LawsFromDistinction; Stdlib: QArith/Lia/List/PeanoNat
- **E/R/R.** _Elements:_ NestedDistinction (depth, roles_at); декомпозиция [2,3,1]; всего 6 ролей. _Roles:_ depth1=бинарно(SU(2)); depth2=тернарно(SU(3)); depth3=рефлексивно(U(1)). _Rules:_ sm_distinction; gauge_generators=N^2-1; sm_total=6; генераторы 8+3+1=12. _P4:_ [2,3,1] — 'единственное' решение под ограничениями (no-repeat/минимальность/терминал-3), но ограничения ЧАСТИЧНО ИНТЕРПРЕТАТИВНЫ (header честно).
- **Classical counterpart.** The SM gauge group SU(3)xSU(2)xU(1) with 8+3+1=12 generators is empirical fact; this file's 'derivation' of [3,2,1] from nested distinctions rests on partially-interpretive constraints (no-repetition, minimality, terminal-at-3) the header itself flags as not forced — an over-branded 'SM from distinction' claim.
- **Tags.** foundation, standard-model, nested-distinction, overbranded, methods

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `NestedDistinction/primary_nd/primary_roles/nd_decomposition/nd_total_roles/primary_decomp/primary_total` | Record/Definition/Lemma | вложенное различение; декомпозиция и сумма ролей |
| `depth1_is_binary/depth2_no_repeat/depth3_is_reflexive/sm_distinction` | Definition | ★ три ограничения; SM-различение [2,3,1] |
| `sm_depth/sm_depth1/2/3/sm_decomp_is_231/sm_total/sm_satisfies_constraints` | Lemma/Theorem | ★ [2,3,1], всего 6; удовлетворяет ограничениям |
| `depth_terminal/sm_terminal_at_depth3/sm_beyond_depth3` | Definition/Theorem | терминал на глубине 3 (рефлексивно) |
| `gauge_generators/su3_gen/su2_gen/u1_generators/sm_generators/sm_generators_from_decomp/nested_distinction_summary/nested_distinction_theorem_count` | Definition/Lemma/Theorem | ★ генераторы 8+3+1=12; сводка |

**Key lemmas (deep):**

- **`sm_satisfies_constraints`** - Показывает, что sm_distinction=[2,3,1] удовлетворяет трём ограничениям (depth1=2, depth2>=3, depth3=1) — все reflexivity/lia. Но это НЕ вывод [3,2,1] из различения: ограничения (нет повторения, минимальность, терминал на 3) сами выбраны так, чтобы дать ответ, и header прямо признаёт их 'partially interpretive'. 'Почему SU(3)', 'почему depth=3' аргументируются словесно (L1/L4), а не теоремами. Это над-брендированное 'SM из различения': числа 6 и 12 закодированы в sm_distinction, а не выведены. _(standard-model, nested-distinction, [3,2,1], interpretive)_

**Uniqueness - score 2 (methods).** Формализует нарратив 'калибровочная группа SM [3,2,1] из вложенных различений' с тремя ограничениями, которым [2,3,1] удовлетворяет (всего 6 ролей, 12 генераторов).
> _Caveat:_ ОВЕР-БРЕНД 'SM из различения': SU(3)xSU(2)xU(1) и 12 генераторов — эмпирический факт; здесь [2,3,1] не ВЫВОДИТСЯ, а закодирован в sm_distinction, а 'ограничения' (no-repeat/минимальность/терминал-3) частично интерпретативны (header признаёт). Доказательства — reflexivity/lia. Header и nested_distinction_theorem_count=25 расходятся с фактическими 17 Qed (дрейф).

---

## #332 - `src/foundation/NestedHierarchyConservation.v` - score 2 (methods)

**Nesting tree of systems: content = leaf sum, conserved under regrouping (chain->tree)**

- **Topic.** Defines a binary nesting tree WTree with content wval (leaf sum), proves parent content = sum of children, content = leaf sum (independent of nesting), same leaves => same content, regrouping conserves, nonneg subtree <= parent — generalizing the cascade chain's telescoping to a tree.
- **Role.** Self-contained (QArith/List/Lia/Lqa). Tree generalization of ScaleHierarchyTransfer (the cascade chain is the path-tree case); part of the Иерархии-и-Каскады far-horizon. No downstream dependents.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; Stdlib: List; Stdlib: Lia; Stdlib: Lqa
- **E/R/R.** _Elements:_ дерево WTree; листья in Q; содержание wval. _Roles:_ узлы=системы на уровнях; родитель<-дети=вертикаль; брат+брат=латераль; листья/корень. _Rules:_ wval(родитель)=wval(l)+wval(r) (межуровень); содержание=Σ листья (независимо от вложенности); перегруппировка сохраняет. _P4:_ конечное дерево=Element (точное содержание, сохранено при перегруппировке); бесконечная глубина=role-limit (не строится).
- **Classical counterpart.** That a sum over the leaves of a binary tree is invariant under re-bracketing (associativity/monoid fold) is elementary; NEW only as a 'nesting hierarchy of systems' framing with vertical (parent<-children) and lateral (sibling+sibling) coupling and a conservation law, generalizing a cascade chain to a tree.
- **Tags.** foundation, nesting, conservation, hierarchy, methods

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `WTree/wval/wval_node` | Definition/Lemma | ★ дерево; содержание; родитель=сумма детей |
| `leaves/qsum/qsum_app/wval_is_leafsum` | Definition/Lemma/Theorem | ★ содержание = сумма листьев (независимо от вложенности) |
| `content_nesting_independent/wval_rebracket` | Corollary/Lemma | ★ одинаковые листья => одинаковое содержание; перегруппировка сохраняет |
| `tree_nonneg/wval_nonneg/subtree_le_parent_left` | Definition/Lemma | монотонность: подсистема <= объемлющая (для >=0) |
| `tree_witness/NestSide/nest_h1_disjoint/nested_hierarchy_conservation` | Example/Definition/Lemma/Theorem | конкретный свидетель 7/4; H1-стороны; капстоун |

**Key lemmas (deep):**

- **`wval_is_leafsum`** - Содержание дерева = сумма его листьев (индукция + qsum_app) => не зависит от вложенности/скобок (content_nesting_independent, wval_rebracket). Математически это просто ассоциативность/коммутативность сложения над листьями монада (моноидный fold) — элементарно. Ценность чисто в ОБРАМЛЕНИИ: вертикальная (родитель<-дети) + латеральная (брат+брат) связь систем на разных уровнях с законом сохранения, обобщающим каскадную цепь до дерева. Новой математики нет. _(nesting, conservation, tree, monoid-fold)_

**Uniqueness - score 2 (methods).** Обобщает каскадную цепь до дерева вложенных систем: содержание = сумма листьев, сохраняется при произвольной перегруппировке (вертикаль + латераль).
> _Caveat:_ Инвариантность суммы листьев под перескобочиванием — элементарная ассоциативность сложения (моноидный fold); новой математики нет, только обрамление 'иерархия систем'. Бесконечная глубина (role-limit) не строится. Уровень — методы/обрамление. Header заявляет 11 Qed — фактически 10 (дрейф).

---

## #333 - `src/foundation/NontrivialDepth.v` - score 2 (methods)

**SU(1) trivial => nontrivial gauge needs N>=2 (a [3,2,1] depth constraint)**

- **Topic.** Defines su_generators(N)=N^2-1, proves SU(1)=0 (trivial), SU(2)=3/SU(3)=8 nontrivial, nontriviality forces N>=2, and uses this for the depth constraints of the [3,2,1] argument (depth2 forced to 3, depth3 terminal at 1, depth4 wasteful).
- **Role.** Self-contained (QArith/Lia/ZArith/Lqa). Supplies the nontriviality step for the NestedDistinction/NontrivialDepth SM narrative (formalizes a previously 'argued' constraint). No downstream dependents.
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; Stdlib: Lia; Stdlib: ZArith; Stdlib: Lqa
- **E/R/R.** _Elements:_ su_generators(N)=N^2-1; депт-константы N0=2,N1=3,N2=1. _Roles:_ формализовать, почему [3,2,1] требует N1>=2 (SU(1)=тривиальна). _Rules:_ SU(N) имеет N^2-1 генераторов; N=1 даёт 0 = тривиально; нетривиальность => N>=2. _P4:_ различение с 0 генераторами не добавляет структуры (L4: без достаточного основания = нет различения); глубина терминальна на 3.
- **Classical counterpart.** That SU(1) is trivial (N^2-1=0 generators) and SU(N) for N>=2 is nontrivial is elementary group theory; NEW only as a step formalizing one constraint in the [3,2,1]-from-distinction narrative (replacing an 'argued' step with 'SU(1) is trivial => N1>=2').
- **Tags.** foundation, su(n), standard-model, elementary, methods

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `su_generators/su1_trivial/su2_nontrivial/su3_nontrivial/su4_generators/su5_generators` | Definition/Lemma | N^2-1; SU(1)=0, SU(2)=3, SU(3)=8, SU(4)=15, SU(5)=24 |
| `nontrivial_group/su1_not_nontrivial/su2_is_nontrivial/su3_is_nontrivial/nontrivial_at_least_2` | Definition/Theorem | ★ нетривиальность => N>=2 |
| `depth1_N0/depth2_min_N1/depth3_min_N2/depth4_minimum_N3/depth2_forced/depth3_terminal/depth4_wasteful` | Definition/Theorem | депт-ограничения [3,2,1] |
| `nontrivial_forces_321` | Theorem | ★ синтез: SU(1)=0, SU(2)/SU(3) нетривиальны, депт-аргумент |

**Key lemmas (deep):**

- **`nontrivial_at_least_2`** - Нетривиальная калибровочная группа (>=1 генератор) требует N>=2, т.к. SU(1) даёт N^2-1=0 (доказано разбором случаев + lia). Это и есть 'формализация ранее аргументированного шага' в нарративе [3,2,1]. Но содержательно — тривиальная nat-арифметика (N^2-1); 'различение без генераторов = нет различения' (L4) — словесная подпорка. Файл закрывает один интерпретативный пробел NestedDistinction, но сам по себе это школьная теория групп, не вывод SM. _(su(n), nontrivial, [3,2,1], elementary)_

**Uniqueness - score 2 (methods).** Формализует, что SU(1) тривиальна (0 генераторов), поэтому нетривиальная калибровочная группа требует N>=2 — закрывая один 'аргументированный' шаг в выводе [3,2,1].
> _Caveat:_ SU(1)=тривиальна и SU(N>=2) нетривиальна — элементарная теория групп (N^2-1, доказано lia). Это лишь подпорка к над-брендированному нарративу 'SM из различения' (см. NestedDistinction); 'различение без генераторов = нет различения' — интерпретация, не теорема. Уровень — методы. 0 аксиом, header совпадает (13 Qed).

---

## #334 - `src/foundation/NSBoundDescent.v` - score 3 (new-framing)

**NS nonlinearity bound as a third wall-type (HardStructure): realizable but cascade-summation hard**

- **Topic.** Toy nat-model showing the advection bound B~k <= max is realizable structure (not a free magnitude, not a symmetry choice), while the difficulty lives in the unbounded cascade sum; concludes a third 'HardStructure' wall-type.
- **Role.** Part of the wall-taxonomy/finitization-boundary audit series (HeavyWallAudit, OpenFrontierLedger). Self-contained (Arith/Lia). Reuses the load-bearing axiom B_coeff_bounded conceptually but declares none.
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith, Lia
- **E/R/R.** _Elements:_ B_model k l m = k; cascade n = 1+..+n; типы Wall/WallType (3 рода). _Roles:_ оценка = реализуемая структура; каскадная сумма = где живёт открытая трудность. _Rules:_ поштриадная оценка структурна (B~k<=max); регулярность держится на СУММЕ каскада (суперкритично 3D). _P4:_ ТРЕТИЙ тип -- HardStructure: доказуемо-в-принципе поштриадно, но несущая каскадная сумма = открытая Millennium-проблема (blow-up не исключён).
- **Classical counterpart.** The Navier-Stokes nonlinearity bound \|B(k,l,m)\| <= C*max(k,l,m) and the supercritical 3D energy cascade are standard turbulence/Millennium-problem facts; NEW only as a toy taxonomic 'descent' classifying the NS bound as a THIRD wall-type vs symmetry-choice and bare-hierarchy walls.
- **Tags.** foundation, navier-stokes, wall-taxonomy, finitization-boundary, new-framing, honest-limit

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `B_model/bound_is_structural` | Definition/Lemma | модельная связь B~k <= max(k,l,m) реализуема |
| `cascade/cascade_grows/cascade_unbounded` | Fixpoint/Lemma | каскадная сумма растёт неограниченно |
| `Wall/WallType/wall_type/ns_is_hard_structure` | Inductive/Definition/Lemma | классификация стен; NS = HardStructure |
| `ns_is_third_type/three_types_distinct` | Lemma | NS отличается от обоих других типов; три типа различны |
| `ns_bound_descent` | Theorem | капстоун: четвёртый спуск, NS = третий тип стены |

**Key lemmas (deep):**

- **`ns_bound_descent`** - Не теорема о физике, а ТАКСОНОМИЧЕСКОЕ наблюдение: NS-оценка реализуема (B~k<=max), значит не свободная магнитуда и не выбор-симметрии, но регулярность опирается на каскадную сумму (cascade_unbounded), которая суперкритична в 3D. Машинная часть тривиальна (le_max_l, индукция, discriminate); ценность -- честная локализация, что несущая оценка ЕСТЬ открытая проблема. Это не приближение к решению NS. _(navier-stokes, wall-taxonomy, finitization-boundary, cascade, honest-limit)_

**Uniqueness - score 3 (new-framing).** Классификация NS-нелинейной оценки как ТРЕТЬЕГО типа стены (HardStructure): реализуемая структура с открытой несущей оценкой.
> _Caveat:_ Сама оценка |B|<=C*max и суперкритичность 3D-каскада -- стандартная турбулентность/Millennium; здесь лишь toy-nat-модель и таксономический ярлык, никакого продвижения к регулярности NS. Header заявляет 6 Qed -- фактически 7 (drift).

---

## #335 - `src/foundation/NumberIsVolume.v` - score 3 (new-framing)

**Number = volume as a finite additive monotone measure tiling the causal chain**

- **Topic.** Counting measure vol A = length A on finite causal-set regions: finite additivity (length_app), monotonicity (NoDup_incl_length), empty=0; on the chain half-open segments [x,y)=y-x tile exactly.
- **Role.** Deepens the NUMBER half of CausalOrderGeometry.v; Element-side replacement of the continuum volume integral. Self-contained (List/Arith/Lia).
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: List, Arith, Lia
- **E/R/R.** _Elements:_ vol A := length A; seg x y := y-x; seg 0 4 = 4. _Roles:_ счёт = мера; непересекающееся объединение = аддитивность; вложение = монотонность; сегмент = тайл. _Rules:_ vol(A++B)=vol A+vol B; A⊆B⟹vol A<=vol B; vol[]=0; seg x z = seg x y + seg y z. _P4:_ объём = nat (Element, конечен по построению), не вещественный интеграл ∫√(-g) (role-limit, мог бы расходиться); континуумный предел = гипотеза Соркина, НЕ доказывается.
- **Classical counterpart.** Sorkin's causal-set 'number = volume', the finite counting measure, and half-open interval tiling are standard causal-set kinematics; NEW only as a machine-checked statement that the counting volume is a genuine finitely-additive monotone measure that tiles on the 1D chain.
- **Tags.** foundation, causal-set, measure, sorkin, new-framing

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `vol/disjoint/vol_empty` | Definition/Lemma | счётная мера и пустой объём |
| `vol_additive/disjoint_union_nodup/vol_monotone` | Lemma | конечная аддитивность и монотонность |
| `seg/seg_self/seg_additive/seg_concrete/seg_is_count` | Definition/Lemma | сегменты цепи тайлируют, счёт = объём |
| `number_is_volume` | Theorem | капстоун: число=объём = конечная мера, замощающая цепь |

**Key lemmas (deep):**

- **`seg_additive / number_is_volume`** - Делает метафору Соркина 'число=объём' буквальной МЕРОЙ: конечная аддитивность + монотонность + точное замощение полуоткрытыми сегментами на цепи. Доказательства -- прямые обёртки стандартных List-лемм (length_app, NoDup_incl_length, length_seq, lia). Содержательный P4-поворот: объём интринсически конечен (nat), Element-замена расходящегося континуумного интеграла. Честно ограничено 1D-цепью; континуумная близость (Hauptvermutung) не трогается. _(causal-set, measure, number-is-volume, sorkin, finite)_

**Uniqueness - score 3 (new-framing).** Машинно-проверенное переосмысление 'число=объём' как подлинной конечно-аддитивной монотонной меры, точно замощающей причинную цепь.
> _Caveat:_ Причинно-множественная кинематика и 'число=объём' -- известны (Соркин). Это лишь 1D-инстанс + общая конечная мера; континуумный предел счёт→объём (гипотеза близости) НЕ доказан, природа-как-причинное-множество НЕ утверждается.

---

## #336 - `src/foundation/NumericalPredictions.v` - score 2 (methods)

**Concrete rational predictions from three-formula physics: SHO ratios, Born probs, Weinberg 3/13**

- **Topic.** Extracts numerical predictions from SHO/Qubit three-formula files: E_n/E_0=2n+1, uniform spacing omega, Born probs on (3,4,5)/(5,12,13)/(8,15,17), sin^2(theta_W)=3/13, zero-point=half-gap.
- **Role.** Numerical-prediction layer over SHOThreeFormulas.v + QubitThreeFormulas.v. Imports those two foundation files.
- **Counts.** Qed 25 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, Qabs, ZArith, List, PeanoNat, Lia, Lqa; ToS: foundation.SHOThreeFormulas, foundation.QubitThreeFormulas
- **E/R/R.** _Elements:_ sho_level omega n; born_qubit; weinberg_prediction = 3/13. _Roles:_ уровни SHO = роли-ступени; борновские квадраты амплитуд = вероятности. _Rules:_ E_n/E_0=2n+1; равный зазор omega; P=\|amp\|^2; zero-point=половина зазора. _P4:_ все предсказания -- точные рациональные значения над Q (Element), сравниваемые с экспериментом.
- **Classical counterpart.** SHO odd-integer level ratios (2n+1), uniform IR spacing, Born probabilities on Pythagorean superpositions, the Weinberg angle, and SHO zero-point are all standard QM/spectroscopy; NEW only as exact rational predictions over Q. The sin^2(theta_W)=3/13 claim is OVER-BRANDED.
- **Tags.** foundation, prediction, born, weinberg, over-branding, methods

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `sho_ratio_1_to_0/2_to_0/3_to_0/4_to_0` | Theorem | нечётно-целые отношения уровней 3,5,7,9 |
| `sho_transition_0_1/1_2/2_3/sho_overtone_ratio` | Theorem | равный зазор omega; обертон/фундамент = 2 |
| `born_3_4_5_prob0/prob1/total` | Theorem | борновские вероятности на (3,4,5) |
| `born_5_12_13_*/born_8_15_17_*` | Theorem | борновские вероятности на (5,12,13),(8,15,17) |
| `weinberg_prediction/weinberg_lower_bound/upper_bound/tight_lower/tight_upper/within_001_of_observed` | Definition/Theorem | 3/13 в [0.230,0.231], \|3/13 - 0.23121\|<0.001 |
| `zero_point_half_of_gap/ground_to_first_ratio` | Theorem | zero-point=половина зазора; E_0/E_1=1/3 |
| `concrete_predictions` | Theorem | капстоун: все числа в одной теореме |

**Key lemmas (deep):**

- **`weinberg_within_001_of_observed`** - ФЛАГМАН ПЕРЕБРЕНДА: sin^2(theta_W)=3/13≈0.23077 совпадает с PDG MS-bar 0.23121 на 0.19%, но 3/13 -- ПОДОГНАННАЯ дробь (см. PhysicsDemarcation.v: r=3/10 даёт то же 3/13; постдикция-тень). Лемма машинно проверяет \|3/13-0.23121\|<1/1000 -- это арифметика над Q, НЕ предсказание из первых принципов. Остальные предсказания (2n+1, борновские квадраты) -- тождественная переформулировка стандартной QM/спектроскопии. Ценность файла -- точные Q-числа, не новая физика. _(weinberg, over-branding, born, sho, prediction)_

**Uniqueness - score 2 (methods).** Точные рациональные предсказания над Q: отношения уровней SHO 2n+1, борновские вероятности на пифагоровых тройках, zero-point=половина зазора.
> _Caveat:_ Всё -- стандартная QM/спектроскопия, точно формализованная над Q. sin^2(theta_W)=3/13 СИЛЬНО ПЕРЕБРЕНДЕНО: дробь подгоняема (r=3/10⟹3/13), это постдикция, не безпараметрическое предсказание (сам репо это признаёт в PhysicsDemarcation.v). Header заявляет 21 Qed -- фактически 25 (drift).

---

## #337 - `src/foundation/ObserverCompressor.v` - score 3 (new-framing)

**Observer = Compressor: QM as DFT information processing (Born=Parseval, collapse=compression)**

- **Topic.** Maps QM concepts to DFT/information theory: Born=energy fraction, measurement=truncation to one mode, collapse=max compression (M=1), uncertainty=1/(2N), complementarity=position/momentum basis swap.
- **Role.** Builds on PhysicalProcess.v (pp_energy, impulse_pp). Information-theoretic reframing of QM.
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, Qabs, Lia, ZArith, List, PeanoNat, Bool, Lqa; ToS: foundation.PhysicalProcess
- **E/R/R.** _Elements:_ time_energy/freq_energy; born_prob; min_uncertainty N; BasisChoice. _Roles:_ Born=Парсеваль; измерение=усечение мод; коллапс=сжатие с потерями. _Rules:_ неопределённость = DFT-предел время-частота; комплементарность = выбор базиса. _P4:_ всё на конечных N-точечных DFT (Element); неопределённость 1/(2N) уменьшается с измельчением графа.
- **Classical counterpart.** The Born rule <-> Parseval, measurement <-> mode truncation, collapse <-> lossy compression, uncertainty <-> DFT time-frequency limit, complementarity <-> basis choice are standard QM/signal-processing analogies; presented here as an E/R/R 'identity' but proven only on tiny concrete instances.
- **Tags.** foundation, born-parseval, dft, information-theory, new-framing, over-claim

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `time_energy/freq_energy/impulse_time_energy` | Definition/Lemma | энергия во времени/частоте (Парсеваль) |
| `born_prob/born_normalized_example/born_sum_is_parseval` | Definition/Lemma | Born = доля спектральной энергии, сумма=1 |
| `measure/truncate_to_one/post_measurement_one_mode/measurement_eq_coefficient` | Definition/Lemma | измерение = усечение до одной моды |
| `collapse_to_mode/compress_to_M/collapse_is_max_compression/info_lost_*/collapse_loses_most/no_collapse_lossless` | Definition/Lemma | коллапс = максимальное сжатие M=1 |
| `min_uncertainty/uncertainty_N4/uncertainty_N8/finer_less_uncertain` | Definition/Lemma | неопределённость 1/(2N) убывает с N |
| `BasisChoice/basis_localized_in/basis_delocalized_in/complementarity` | Inductive/Definition/Lemma | комплементарность = своп базиса |
| `observer_compressor_synthesis` | Theorem | капстоун: все 5 соответствий |

**Key lemmas (deep):**

- **`born_sum_is_parseval / observer_compressor_synthesis`** - Заголовок называет это 'crown jewel' и 'IDENTITY through E/R/R', но фактические леммы -- vm_compute на конкретных N=4/8 примерах и тривиальные dec-вычисления (truncate, info_lost). Аналогия QM<->DFT (Born=Парсеваль, коллапс=сжатие, неопределённость=время-частота) стандартна в обработке сигналов; здесь она НЕ доказана как общее тождество, лишь проиллюстрирована числами. Уровень -- переформулировка/иллюстрация, не теорема. _(born-parseval, dft, compression, over-claim, illustration)_

**Uniqueness - score 3 (new-framing).** E/R/R-переформулировка QM как обработки информации на DFT: Born=Парсеваль, измерение=усечение, коллапс=сжатие.
> _Caveat:_ Соответствия QM<->обработка-сигналов (Born=Парсеваль, время-частотная неопределённость, комплементарность=базис) -- ХОРОШО ИЗВЕСТНЫ. Файл доказывает лишь конкретные N=4/8 инстансы, не общее 'тождество'; 'crown jewel'/'IDENTITY' -- перебренд. Header заявляет 15 Qed -- фактически 13 (drift).

---

## #338 - `src/foundation/ObserverFoundation.v` - score 2 (methods)

**Observer as append-only witness: observation grows state, distinctions are preserved (L5)**

- **Topic.** Observer = list of distinction indices; observe prepends a new index; lemmas: state grows, self-witnessing is permanent, prior distinctions preserved, length monotone, observers can differ.
- **Role.** Foundation file for the observer/time/L5 cluster; reused conceptually by ObserverSynthesis.v. Self-contained (QArith/List/Bool).
- **Counts.** Qed 14 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, Lia, ZArith, Lqa, List, Bool
- **E/R/R.** _Elements:_ ObsState = list nat; Observer; observe; has. _Roles:_ быть различённым = быть свидетелем своего существования. _Rules:_ L1 = само-свидетельствование; L5 = состояние только растёт. _P4:_ наблюдение = добавление элемента в конечный список (Element); потенциальное, не завершённое.
- **Classical counterpart.** An append-only list of observed indices with membership-preservation is elementary list algebra; the 'observer = self-witnessing, L5 = state only grows' framing is philosophical labeling, not a new result.
- **Tags.** foundation, observer, list-algebra, L5, methods

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `ObsState/has/Observer/initial_obs/initial_empty` | Definition/Record/Lemma | состояние-список, начальный наблюдатель пуст |
| `observe/observe_grows/observe_adds/self_witness` | Definition/Lemma | наблюдение растит состояние и добавляет различие (L1) |
| `self_witness_permanent/obs_preserves/state_monotone` | Lemma | различия сохраняются, длина монотонна (L5) |
| `obs_A/obs_B/observers_differ/shared_distinction/private_distinction` | Definition/Lemma | разные наблюдатели, общие/частные различия |
| `first_obs_nonempty/two_obs_both/cumulative_3` | Lemma | первое наблюдение создаёт время; кумулятивность |
| `observer_foundation_synthesis` | Theorem | капстоун-синтез наблюдателя |

**Key lemmas (deep):**

- **`self_witness_permanent / state_monotone`** - Все леммы -- элементарная алгебра списков: existsb после cons (Nat.eqb_refl, orb_true_r), монотонность длины (lia). Содержательного математического ядра нет; ценность -- ФИЛОСОФСКАЯ привязка 'наблюдатель = само-свидетельствующий процесс, L5 = состояние растёт' к E/R/R. L1/L5 здесь -- ярлыки уровня reflexivity, не выводимые законы. _(observer, list-algebra, L5, philosophical, infrastructure)_

**Uniqueness - score 2 (methods).** Формализация наблюдателя как append-only процесса: наблюдение растит состояние, различия неуничтожимы.
> _Caveat:_ Чистая алгебра списков (existsb/length/orb); 'L1=само-свидетельствование, L5=рост состояния' -- философские ярлыки reflexivity-уровня, не математические теоремы. Header заявляет 20 Qed -- фактически 14 (drift).

---

## #339 - `src/foundation/ObserverSynthesis.v` - score 1 (exposition)

**Grand 13-conjunct synthesis of observer + time + L5 (standalone re-inline)**

- **Topic.** One big theorem asserting 13 trivial facts about the inlined observer model: empty start, observation grows state, membership preserved, S m != 0, potential infinity n<m, distinct observer lists.
- **Role.** Capstone aggregator for the observer cluster; inlines its own definitions (S-prefixed) to compile standalone. No imports beyond Stdlib.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, Lia, ZArith, Lqa, List, Bool
- **E/R/R.** _Elements:_ SObsState/SObs/sinit/sobs/shas (инлайн). _Roles:_ объединить наблюдателя, время и L5 в одной теореме. _Rules:_ 13-конъюнктный синтез тривиальных list/nat фактов. _P4:_ конечный список наблюдений; нет завершённой бесконечности (S m != 0), есть потенциальная (n<m).
- **Classical counterpart.** A single 13-conjunct theorem bundling trivial list/nat facts (membership, length, S m != 0, n < S n); standalone re-inlining of ObserverFoundation with an 'S' prefix. No new content.
- **Tags.** foundation, observer, synthesis, exposition

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `SObsState/shas/SObs/sinit/sobs` | Definition/Record | инлайн-копия модели наблюдателя |
| `sobs_adds/sobs_preserves` | Lemma | вспомогательные: добавление и сохранение |
| `observer_grand_synthesis` | Theorem | 13-конъюнктный гранд-синтез |
| `void_unchanged/logic_unchanged/witness_indestructible/three_acts_three_moments/observation_is_creation` | Lemma | дополнительные тривиальные факты |

**Key lemmas (deep):**

- **`observer_grand_synthesis`** - 13-конъюнктная теорема, каждый конъюнкт -- reflexivity/vm_compute/lia/discriminate на инлайн-списках. Полностью дублирует ObserverFoundation.v через S-префикс ради standalone-компиляции. Математической новизны ноль; это агрегатор-витрина. Конъюнкты вроде 'forall n, exists m, n<m' (потенциальная бесконечность) и '~exists m, S m = 0' -- стандартные факты nat. _(observer, synthesis, trivial, duplicate, infrastructure)_

**Uniqueness - score 1 (exposition).** Гранд-синтез: 13 фактов о наблюдателе/времени/L5 в одной теореме.
> _Caveat:_ Все 13 конъюнктов тривиальны (reflexivity/lia/discriminate); файл -- инлайн-дубликат ObserverFoundation.v ради standalone-сборки, без новой математики. Header заявляет 10 Qed -- фактически 8 (drift).

---

## #340 - `src/foundation/OpenFrontierLedger.v` - score 3 (new-framing)

**Open-frontier ledger: Lambda, eta, Hauptvermutung as one wall (structure-derivable, value-not)**

- **Topic.** Classifies three open walls by kind (GenuineGap/InheritedFailure/ResearchMath), all on the role-limit side of H1: structure derivable, value not. The Lambda gem: finitization solves divergence (vac<=1) but not smallness (not <=1e-6).
- **Role.** Audit-methodology series (HeavyWallAudit, NSBoundDescent). Self-contained (QArith/Lqa/List). A classification, not a solution.
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, Lqa, List
- **E/R/R.** _Elements:_ Wall/Kind/H1Side; structure_derivable=true, value_derivable=false; vac_bound=1/2. _Roles:_ Lambda=GenuineGap; eta=InheritedFailure; Hauptvermutung=ResearchMath; все=role-limit магнитуда. _Rules:_ классифицировать каждую открытую стену; все три = одна стена (свободная магнитуда). _P4:_ деривационный край ToS останавливается единообразно: структура выводима (Element), значение нет (role-limit); ни одно значение не выведено.
- **Classical counterpart.** The cosmological-constant smallness problem, the baryon-asymmetry magnitude, and the causal-set Hauptvermutung are all genuine open problems; NEW only as a machine-checked CLASSIFICATION tagging all three as the same 'free-magnitude / role-limit' side of the finitization boundary.
- **Tags.** foundation, finitization-boundary, cosmological-constant, hauptvermutung, new-framing, honest-limit

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `Wall/Kind/H1Side/wall_kind/wall_side/structure_derivable/value_derivable` | Inductive/Definition | три стены, их роды и H1-сторона |
| `all_role_limit/kinds_distinct/structure_yes_value_no` | Lemma | все на role-limit; структура да, значение нет |
| `vac_bound/lambda_divergence_solved/lambda_smallness_unsolved` | Definition/Lemma | Lambda-гем: расходимость решена, малость нет |
| `all_walls/is_role_limit/n_role_limit/n_role_limit_eq` | Definition/Lemma | баланс реестра: 3 role-limit стены |
| `open_frontier_ledger` | Theorem | капстоун: открытый фронтир, классифицированный |

**Key lemmas (deep):**

- **`lambda_smallness_unsolved / open_frontier_ledger`** - Содержательная 'жемчужина': финитизация СНИМАЕТ расходимость вакуумной энергии (vac_bound=1/2<=1), но НЕ малость (1/2 не <= 1e-6, lra) -- честное различение того, что решено и что нет. Остальное -- inductive-классификация (reflexivity). Главная ценность -- БРУТАЛЬНО ЧЕСТНАЯ локализация: три открытые проблемы = одна стена (свободная магнитуда), деривационный край ToS = 'структура да, значение нет'. Не решение ни одной из трёх. _(cosmological-constant, baryon-asymmetry, hauptvermutung, finitization-boundary, honest-limit)_

**Uniqueness - score 3 (new-framing).** Машинный реестр, классифицирующий три открытые стены (Lambda, eta, Hauptvermutung) как одну: свободная магнитуда на role-limit-стороне H1.
> _Caveat:_ Все три -- настоящие открытые проблемы; файл их КЛАССИФИЦИРУЕТ, не решает (ни одно значение не выведено, Hauptvermutung не доказана). Lambda-гем (расходимость!=малость) содержателен, но это известное различение. Честный по построению.

---

## #341 - `src/foundation/Ordinal.v` - score 2 (methods)

**Constructive ordinal arithmetic + epsilon_0: ordinals as limit processes (P4)**

- **Topic.** Inductive Ord with OLim:(nat->Ord), nat embedding, omega, ord_add/mul/exp by recursion on b, the omega-tower, epsilon_0 = OLim omega_tower, an ord_lt relation, plus arithmetic identities and concrete computations.
- **Role.** Foundational ordinal type; replicated (partially) into P4_Eliminates_ATR.v. Self-contained (Lia/FunctionalExtensionality).
- **Counts.** Qed 20 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Lia, ZArith, List, FunctionalExtensionality
- **E/R/R.** _Elements:_ Ord (OZero/OSucc/OLim); nat_to_ord; omega; epsilon_0. _Roles:_ OLim f = предел процесса f: nat->Ord; ord_lt = порядок. _Rules:_ структурная рекурсия по второму аргументу; ord_add/mul/exp; omega_tower. _P4:_ ординалы = ПРОЦЕССЫ; epsilon_0 = предел башни omega,omega^omega,... -- потенциальный, не завершённый объект.
- **Classical counterpart.** Constructive ordinal notations (OZero/OSucc/OLim), ordinal +/*/exp by recursion on the second argument, omega, the omega-tower, and epsilon_0 are textbook ordinal arithmetic (Cantor normal form notations); NEW only as the P4 'ordinals = processes, OLim = limit of nat->Ord' reading.
- **Tags.** foundation, ordinals, epsilon_0, constructive, methods

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `Ord/nat_to_ord/omega/ord_add/ord_mul/ord_exp/omega_tower/epsilon_0/ord_lt` | Inductive/Fixpoint/Definition | тип ординалов и арифметика |
| `ord_add_zero_r/succ_r/zero_l/mul_zero_r/mul_one_r/exp_zero` | Lemma | арифметические тождества |
| `ord_succ_injective/succ_ne_zero/nat_to_ord_injective` | Lemma | свойства конструкторов и вложения |
| `nat_to_ord_lt_succ/nat_lt_omega/ord_lt_zero_one` | Lemma | факты порядка; n<omega |
| `omega_is_limit/epsilon_0_is_limit/ord_zero_ne_omega` | Lemma | omega,epsilon_0 -- предельные |
| `nat_to_ord_3/ord_add_concrete/ord_mul_concrete/omega_tower_0/omega_tower_1` | Lemma | конкретные вычисления |

**Key lemmas (deep):**

- **`epsilon_0 / nat_lt_omega`** - Стандартные конструктивные нотации ординалов (как в системах нотаций до epsilon_0); рекурсия по второму аргументу, OLim берёт фундаментальную последовательность nat->Ord. Доказательства -- индукция + functional_extensionality (ord_add_zero_l) и reflexivity. Новизна нулевая математически; ценность -- P4-чтение 'ординал = процесс, epsilon_0 = предел башни', т.е. потенциальная, а не актуальная бесконечность. ord_lt не доказан транзитивным/well-founded здесь. _(ordinals, epsilon_0, constructive, process-reading, exposition)_

**Uniqueness - score 2 (methods).** Конструктивная арифметика ординалов с epsilon_0, прочитанная как процессы (OLim = предел nat->Ord).
> _Caveat:_ Нотации ординалов, ord_add/mul/exp и epsilon_0 -- учебная конструктивная теория ординалов (системы нотаций). Новое -- лишь P4-ярлык 'ординал=процесс'; well-foundedness/транзитивность ord_lt здесь НЕ доказаны. Header '~20 Qed' совпадает с фактическими 20.

---

## #342 - `src/foundation/P4_Eliminates_AC.v` - score 2 (methods)

**AC = L5 head-of-list choice on finite families (+ finite Zorn = list max)**

- **Topic.** Under P4 'sets are finite lists', L5 choice = first element; proves finite choice, a concrete example, finite Zorn (list maximum), and a stage-wise bounded-front choice theorem. Notes the unbounded version reduces to P4ProhibitsAC.
- **Role.** P4 'eliminates classical axioms' series; the prohibition counterpart is P4ProhibitsAC.v. Self-contained (List/Lia/PeanoNat/Bool).
- **Counts.** Qed 15 / Admitted 0 / axioms 0
- **Imports.** Stdlib: List, Lia, PeanoNat, Bool
- **E/R/R.** _Elements:_ L5_choose (голова списка); finite_choice_fn; list_max. _Roles:_ L5-статус = канонический выбор первого элемента; максимум списка = финитный Цорн. _Rules:_ голова списка = конструктивный выбор; никакой аксиомы не нужно. _P4:_ при P4 'множество' на стадии N = конечный список; выбор -- правило (голова), не завершённый граф; финитный фронт N.
- **Classical counterpart.** On finite/list-indexed families, 'choice = head of list' and 'finite Zorn = list maximum' are trivial constructive facts; the Axiom of Choice as a genuine axiom concerns infinite families. The unguarded P4_eliminates_AC over ALL nat is the questionable claim (the file itself flags it).
- **Tags.** foundation, axiom-of-choice, L5, finite-choice, methods

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `L5_choose/finite_choice_fn/L5_choose_in_nonempty/finite_choice` | Definition/Lemma | выбор=голова непустого списка |
| `example_family/finite_choice_concrete/L5_choice_deterministic` | Definition/Lemma | конкретный пример, детерминизм |
| `process_choice/process_choice_valid` | Definition/Lemma | постадийный выбор из N-приближения |
| `list_max/list_max_in/list_max_is_max/finite_zorn` | Fixpoint/Lemma | финитный Цорн = максимум списка |
| `AC_is_L5/finite_decomposition_preserves_length/decidable_subset_finite` | Lemma | AC=L5; конечные разбиения, разрешимые подмножества |
| `choice_singleton/choice_cons` | Lemma | выбор на синглтоне/cons |
| `P4_eliminates_AC/P4_eliminates_AC_finite` | Theorem | AC как теорема финитной комбинаторики; явная финитная версия |

**Key lemmas (deep):**

- **`P4_eliminates_AC / P4_eliminates_AC_finite`** - Ключевая честность В САМОМ ФАЙЛЕ: комментарий перед P4_eliminates_AC признаёт, что он квантифицирует по ВСЕМ nat и как завершённый граф {(i,f i)} подпадает под P4ProhibitsAC (т.е. сам по себе не P4-совместим); P4_eliminates_AC_finite -- честная финитно-фронтовая версия (выбор на {0..N-1}). На непустых списках 'выбор=голова' и 'Цорн=максимум списка' тривиальны (left;reflexivity, индукция+lia). Содержательного избегания AC нет -- AC нетривиален лишь для бесконечных семейств. Banach-Tarski-блокировка -- лишь app_length+filter. _(axiom-of-choice, L5, finite-choice, self-flagged-caveat, methods)_

**Uniqueness - score 2 (methods).** AC как L5-выбор головы списка на конечных/финитно-фронтовых семействах; финитный Цорн = максимум списка.
> _Caveat:_ Это ТРИВИАЛЬНО: AC нетривиален только для бесконечных семейств; на списках выбор=голова. Сам файл признаёт, что безграничный P4_eliminates_AC подпадает под P4ProhibitsAC. Honest finite version отдельна. Header заявляет 16 Qed -- фактически 15 (drift).

---

## #343 - `src/foundation/P4_Eliminates_ATR.v` - score 2 (methods)

**Transfinite predicate iteration along Ord notations as a Coq Fixpoint (claimed ATR0 elimination)**

- **Topic.** Cantor-Bendixson-style CB_step and a generic iterate_pred over Ord (OLim = forall-k over fundamental sequence); proves zero/succ/limit equations, CB=iterate equivalence, finite-stage unfolding.
- **Role.** P4 'eliminates classical axioms' series; uses an inline copy of Ord. Self-contained (List/Lia/PeanoNat).
- **Counts.** Qed 17 / Admitted 0 / axioms 0
- **Imports.** Stdlib: List, Lia, PeanoNat
- **E/R/R.** _Elements:_ Ord (инлайн); CB_step; CB_transfinite; iterate_pred. _Roles:_ структурная рекурсия по alpha устраняет аксиому ATR0; предельная стадия = пересечение по фундам. последовательности. _Rules:_ проверяльщик завершимости Coq -- единственный нужный принцип; OLim => forall k. _P4:_ трансфинитная рекурсия = Fixpoint на индуктивном Ord (Element-конструкция стадия-за-стадией), не завершённая иерархия.
- **Classical counterpart.** ATR0 (arithmetical transfinite recursion) is a genuine subsystem of reverse mathematics; here transfinite iteration of a predicate operator along an ordinal NOTATION is a Coq Fixpoint on the inductive Ord. This is NOT ATR0 (which concerns recursion along arbitrary well-orderings / hyperarithmetic sets), only iteration along built-in ordinal notations.
- **Tags.** foundation, ATR0, transfinite-recursion, reverse-math, over-claim, methods

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `Ord/nat_to_ord/omega/CB_step/CB_transfinite/iterate_pred` | Inductive/Fixpoint/Definition | тип ординалов и трансфинитная итерация |
| `CB_trans_zero/succ/lim_forward/lim_backward/decreasing` | Lemma | базовые уравнения CB-итерации |
| `iterate_zero/iterate_succ/concrete_iter_1/concrete_iter_2` | Lemma | уравнения и конкретные итерации iterate_pred |
| `ATR_pattern/ATR_limit_stage` | Lemma | паттерн ATR: нулевая/предельная стадии |
| `CB_is_iterate_pointwise/finite_iterate/iterate_identity` | Lemma | CB=iterate поточечно; финитное развёртывание |
| `succ_stage_monotone/lim_below_all` | Lemma | монотонность преемника; предел ниже всех |
| `P4_eliminates_ATR0` | Theorem | капстоун: ATR0 = определение (zero/succ уравнения) |

**Key lemmas (deep):**

- **`P4_eliminates_ATR0 / CB_is_iterate_pointwise`** - Капстоун P4_eliminates_ATR0 доказывает лишь zero/succ уравнения iterate_pred (split;reflexivity) -- это НЕ устранение ATR0. ATR0 в обратной математике касается рекурсии вдоль ПРОИЗВОЛЬНЫХ счётных вполне-упорядочений и существования гиперарифметических множеств; здесь -- итерация оператора предикатов вдоль ВСТРОЕННЫХ нотаций Ord, что Coq принимает структурно. Содержательная лемма -- CB_is_iterate_pointwise (индукция, аккуратная). Заявление 'ATR0 становится определением' СИЛЬНО переоценивает: предельная стадия определена как forall-k, а сила ATR0 (выбор/итерация по непредставленным ординалам) не воспроизводится. _(ATR0, transfinite-recursion, reverse-math, over-claim, ordinal-notation)_

**Uniqueness - score 2 (methods).** Трансфинитная итерация предикат-оператора вдоль нотаций Ord как Fixpoint Coq; CB-производная = iterate_pred.
> _Caveat:_ ПЕРЕОЦЕНКА: это НЕ устранение ATR0. ATR0 -- рекурсия вдоль произвольных вполне-упорядочений + гиперарифметика; здесь лишь итерация вдоль встроенных нотаций Ord (предел = forall-k). Капстоун доказывает только zero/succ уравнения. Header заявляет 15 Qed -- фактически 17 (drift).

---

## #344 - `src/foundation/P4_Eliminates_Infinity.v` - score 2 (methods)

**nat as inductive RULE not completed SET: induction, recursion, finite boundedness**

- **Topic.** Shows nat-induction, strong induction, factorial, partial sums, constant-sequence convergence, and finite-list boundedness all work via nat_rect without a completed infinite set; P4 reads nat as a generating rule.
- **Role.** P4 'eliminates classical axioms' series. Self-contained (Lia/PeanoNat/List).
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Lia, PeanoNat, List
- **E/R/R.** _Elements:_ partial_sum; factorial; converges; finite list. _Roles:_ индукция = встроенное правило, не аксиома; nat = правило-генератор. _Rules:_ всё (суммы, пределы, сходимость) работает через nat_rect, не через 'множество всех nat'. _P4:_ nat = ПРАВИЛО (индукция), не ОБЪЕКТ (завершённое множество); каждый n конечен (n<S n).
- **Classical counterpart.** That nat is an inductive type with induction/recursion built in (not the set-theoretic Axiom of Infinity) is standard type theory; strong induction, factorial, partial sums, and finite-list boundedness are elementary. The 'P4 eliminates Infinity' framing is philosophical.
- **Tags.** foundation, axiom-of-infinity, nat-inductive, type-theory, methods

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `nat_induction_works/each_n_finite` | Lemma | индукция как правило; каждый n конечен |
| `partial_sum/partial_sum_zero/partial_sum_3` | Fixpoint/Lemma | частичная сумма без бесконечного множества |
| `converges/const_converges` | Definition/Lemma | сходимость = forall-exists над nat (Prop) |
| `strong_ind_aux/strong_induction` | Lemma | сильная индукция через вспом. предикат |
| `factorial/factorial_5/finite_list_bounded` | Fixpoint/Lemma | рекурсия=Fixpoint; конечный список ограничен |
| `P4_eliminates_Infinity` | Theorem | капстоун: индукция/факториал/сумма без аксиомы бесконечности |

**Key lemmas (deep):**

- **`P4_eliminates_Infinity`** - Корректное, но тривиальное наблюдение: в теории типов nat -- индуктивный тип (правило nat_rect), а не теоретико-множественная аксиома бесконечности; индукция/рекурсия 'бесплатны'. Все леммы -- nat_ind, lia, reflexivity. Это стандартный факт о конструктивных основаниях, переупакованный под P4 'конечная актуальность'. Ничего не 'устраняется' сверх того, что Coq и так не имеет аксиомы бесконечности. _(axiom-of-infinity, nat-inductive, type-theory, philosophical, methods)_

**Uniqueness - score 2 (methods).** nat как индуктивное ПРАВИЛО, а не завершённое множество: индукция/рекурсия/сходимость без аксиомы бесконечности.
> _Caveat:_ Стандартный факт теории типов (Coq и так не имеет set-theoretic AoI); все леммы -- nat_ind/lia/reflexivity. 'P4 устраняет бесконечность' -- философская переупаковка. Header заявляет 12 Qed -- фактически 10 (drift).

---

## #345 - `src/foundation/P4_Eliminates_Pi11.v` - score 2 (methods)

**Pi-1-1 'collapse' to arithmetic via an abstract program-evaluator Parameter (caveat: questionable)**

- **Topic.** Defines forall/exists over functions as forall/exists over program codes via Parameter eval_program; proves closure (conjunction/disjunction), negation (uses classic), and a 'hierarchy collapse' that holds only on eval_program's range.
- **Role.** P4 'eliminates classical axioms' series. The ONLY file in this batch with a Parameter (eval_program). Uses Classical_Prop. June 2026 wave-4 vacuity rollback: program_exists was exists c, c = c (vacuous) -> inhabited Program.
- **Counts.** Qed 15 / Admitted 0 / axioms 1
- **Imports.** Stdlib: Lia, PeanoNat, List, Classical_Prop
- **E/R/R.** _Elements:_ Program=nat; eval_program (Parameter); P4_forall/exists_function. _Roles:_ второй порядок над функциями сведён к первому над кодами программ. _Rules:_ каждая функция = код программы, так forall f = forall c:nat. _P4:_ при P4 функция = ПРОЦЕСС = программа; квантификация над функциями = над nat-кодами (арифметика).
- **Classical counterpart.** The claim 'every function nat->nat is a program code, so Pi-1-1 collapses to arithmetic' is FALSE classically (Pi-1-1 / hyperarithmetic hierarchy is a genuine proper hierarchy; not every function is computable). This file uses an abstract Parameter eval_program and only restricts quantification to its range — it does NOT collapse the real hierarchy.
- **Tags.** foundation, pi-1-1, hyperarithmetic, reverse-math, parameter, over-claim, methods

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `Program/eval_program/P4_forall_functions/P4_exists_function` | Definition/Parameter | функции как коды программ |
| `P4_functions_are_nat/pi11_to_arithmetic/sigma11_to_arithmetic` | Lemma | Pi/Sigma-1-1 как forall/exists над nat |
| `program_exists/function_space_indexed_by_nat` | Lemma | коды существуют; пространство функций индексировано nat |
| `pi11_negation/pi11_set/pi11_set_is_arithmetic` | Lemma | отрицание (classic); множество Pi-1-1 арифметично |
| `compose_programs/compose_is_nat_function/pi11_conjunction/sigma11_disjunction` | Definition/Lemma | композиция; замкнутость по конъюнкции/дизъюнкции |
| `decidable_lift/pi11_witness/pi11_hierarchy_collapse` | Lemma | подъём разрешимости; свидетель; 'коллапс' иерархии |
| `const_zero/const_zero_property/P4_eliminates_Pi11` | Definition/Lemma/Theorem | капстоун: Pi-1-1 = forall-nat над range eval_program |

**Key lemmas (deep):**

- **`pi11_hierarchy_collapse / P4_eliminates_Pi11`** - Самое СОМНИТЕЛЬНОЕ заявление в батче. Классически Pi-1-1/гиперарифметическая иерархия -- СОБСТВЕННАЯ (не всякая функция nat->nat вычислима; квантификация по всем функциям существенно сильнее, чем по вычислимым кодам). Здесь eval_program -- абстрактный Parameter, а 'коллапс' лишь ПЕРЕОПРЕДЕЛЯЕТ forall f как forall c в range(eval_program); pi11_hierarchy_collapse даже берёт равенство range-ограничения В ГИПОТЕЗУ. Так реальная иерархия НЕ коллапсируется -- меняется область квантификации. pi11_negation честно использует classic. Это методологически интересно как P4-онтология, но математически НЕ устраняет Pi-1-1. _(pi-1-1, hyperarithmetic, parameter, over-claim, range-restriction)_

**Uniqueness - score 2 (methods).** При P4-онтологии 'функция=код программы' квантификация по функциям переписывается как арифметическая (forall c:nat) на области eval_program.
> _Caveat:_ КЛАССИЧЕСКИ ЛОЖНО как коллапс: Pi-1-1/гиперарифметика -- собственная иерархия, не всякая функция вычислима. Файл лишь СУЖАЕТ область квантификации к range абстрактного Parameter eval_program (pi11_hierarchy_collapse берёт это в гипотезу). Содержит 1 Parameter (eval_program) -- учтён в Print Assumptions (см. CLAUDE.md). Qed 15 совпадает.

---

## #346 - `src/foundation/P4CompletedInfinity.v` - score 2 (methods)

**P4 prohibits (not just replaces) completed infinity: a stage-bound vs all-at-once contradiction**

- **Topic.** Defines CompletedInfSet, P4_stage_bounded, a bridge to stage-0 actuality; derives False from their conjunction; shows potential infinity is compatible, and prohibition is stronger than reinterpretation.
- **Role.** Hub of the P4Prohibits* cluster (imported by P4ProhibitsAC, P4ProhibitsImpredicative, P4ProhibitionSynthesis). Self-contained (PeanoNat/Lia).
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: PeanoNat, Lia
- **E/R/R.** _Elements:_ CompletedInfSet; P4_stage_bounded; potential_infinity; bridge. _Roles:_ P4 (конечная актуальность) → ограничение на каждой стадии → противоречие с завершённой ∞. _Rules:_ completed_inf + P4_bounded + bridge → False. _P4:_ завершённая бесконечность НЕсовместима с P4 (мост делает все элементы актуальными на стадии 0, но стадия 0 ограничена); потенциальная -- совместима.
- **Classical counterpart.** The 'contradiction' is engineered: a CompletedInfSet (every n holds) plus a bridge forcing all members 'actual at stage 0' plus a stage-0 bound trivially clashes. This is not a deep result about infinity — it is a definitional inconsistency between three chosen predicates. Potential vs actual infinity is a classical philosophical distinction.
- **Tags.** foundation, completed-infinity, potential-infinity, P4, methods

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `CompletedInfSet/P4_stage_bounded/potential_infinity/bridge` | Definition | завершённая/потенциальная ∞ и мост к актуальности |
| `completed_inf_unbounded` | Lemma | завершённая ∞ неограничена |
| `completed_inf_contradicts_P4/P4_prohibition_infinity` | Theorem | P4+completed+bridge → False |
| `potential_inf_exists/potential_compatible_with_P4` | Lemma | потенциальная ∞ совместима с P4 |
| `prohibition_stronger/nat_as_completed/nat_would_be_completed/nat_not_completed_under_P4` | Theorem/Definition/Lemma | запрет сильнее переинтерпретации; nat не завершён под P4 |
| `p4_completed_infinity_synthesis` | Theorem | капстоун-синтез запрета |

**Key lemmas (deep):**

- **`completed_inf_contradicts_P4`** - Противоречие ИСКУССТВЕННОЕ/определительное: CompletedInfSet S := forall n, S n; bridge := forall n, S n -> actual 0 n (т.е. ВСЁ актуально на стадии 0); P4_stage_bounded даёт границу для стадии 0. Берём n=bound+1: получаем actual 0 (bound+1) <= bound, lia, False. Это просто несовместимость трёх выбранных предикатов, а не глубокий результат о бесконечности. Различие потенциальной/актуальной бесконечности -- классическое (Аристотель). Ценность -- формальная привязка к P4, но 'prohibition' держится на том, что МОСТ навязывает all-at-once на стадии 0. _(completed-infinity, potential-infinity, engineered-contradiction, P4, new-framing)_

**Uniqueness - score 2 (methods).** Формальный запрет завершённой бесконечности под P4: stage-bound + all-at-once мост → False; потенциальная ∞ совместима.
> _Caveat:_ Противоречие ОПРЕДЕЛИТЕЛЬНОЕ: мост навязывает 'всё актуально на стадии 0', что тривиально бьётся с границей стадии 0 (lia). Потенциальная/актуальная бесконечность -- классическое различие (Аристотель/Кантор). Header заявляет 12 Qed -- фактически 9 (drift).

---

## #347 - `src/foundation/P4ProhibitionSynthesis.v` - score 1 (exposition)

**P4 is a PROHIBITION not just reinterpretation: three prohibitions + three preservations bundled**

- **Topic.** Re-exports: P4 prohibits completed infinity, full AC-on-nat (produces completed infinity), Russell; preserves potential infinity, finite L5 choice, inductive nat. States prohibition implies but is not implied by reinterpretation.
- **Role.** Top-level synthesis of the P4Prohibits cluster; imports P4CompletedInfinity, P4ProhibitsAC, P4ProhibitsImpredicative.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: PeanoNat, Lia, List; ToS: foundation.P4CompletedInfinity, foundation.P4ProhibitsAC, foundation.P4ProhibitsImpredicative
- **E/R/R.** _Elements:_ запрет vs переинтерпретация; три запрета, три сохранения. _Roles:_ запрет = несовместимость; переинтерпретация = альтернатива. _Rules:_ запрет ⇒ переинтерпретация (строго сильнее); обратное неверно. _P4:_ P4 -- структурный ЗАПРЕТ (завершённая ∞, полный AC-на-nat, Russell несовместимы), а не просто замена; сохраняет потенц. ∞, финитный выбор, индуктивные типы.
- **Classical counterpart.** An aggregator theorem bundling the three P4ProhibitsX results (completed infinity, AC-on-nat, Russell/impredicativity) and three preservations; no new mathematics, only re-export. Prohibition=>reinterpretation is a trivial implication.
- **Tags.** foundation, P4, synthesis, exposition

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `P4_prohibits_three` | Theorem | три запрета: completed ∞, AC-на-nat, Russell |
| `P4_preserves_three` | Theorem | три сохранения: потенц. ∞, финитный выбор, индуктивный nat |
| `prohibition_implies_reinterpretation/reinterpretation_weaker` | Theorem/Lemma | запрет ⇒ переинтерпретация; обратное нет |
| `P4_is_prohibition` | Theorem | P4 = запрет (конкретное противоречие + совместимые альтернативы) |
| `p4_prohibition_grand_synthesis` | Theorem | капстоун: три запрета + три сохранения |

**Key lemmas (deep):**

- **`p4_prohibition_grand_synthesis`** - Чистый агрегатор: каждый конъюнкт -- exact на лемме из импортированных файлов (completed_inf_contradicts_P4, ac_implies_completed, russell_contradiction_without_P1, finite_choice_works, nat_staged_bounded). Никакой новой математики. Концептуальная рамка (prohibition строго сильнее reinterpretation) проиллюстрирована тривиально (prohibition_implies_reinterpretation игнорирует посылку и выдаёт potential_inf_exists). _(synthesis, P4, aggregator, infrastructure)_

**Uniqueness - score 1 (exposition).** Синтез: P4 -- запрет (3 несовместимости), а не переинтерпретация (3 сохранения).
> _Caveat:_ Чистый re-export лемм из P4CompletedInfinity/P4ProhibitsAC/P4ProhibitsImpredicative; новой математики нет. Прохождение 'запрет⇒переинтерпретация' тривиально (игнорирует посылку). Header заявляет 8 Qed -- фактически 6 (drift).

---

## #348 - `src/foundation/P4ProhibitsAC.v` - score 2 (methods)

**P4 prohibits full AC-on-nat (via completed-infinity bridge), preserves finite L5 choice**

- **Topic.** AC_on_nat yields a choice function whose graph is a CompletedInfSet (trivially: graph := fun _ => True), which P4 prohibits; finite_choice on {0..N-1} via head-of-list survives and is deterministic.
- **Role.** Part of P4Prohibits cluster; imports P4CompletedInfinity. The 'eliminate' counterpart is P4_Eliminates_AC.v.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: PeanoNat, Lia, List; ToS: foundation.P4CompletedInfinity
- **E/R/R.** _Elements:_ AC_on_nat; choice_graph; finite_choice; L5_choose. _Roles:_ полный AC требует завершённого индекс-множества, P4 это запрещает; финитный выбор = голова списка. _Rules:_ AC_on_nat + P4 → completed_inf → противоречие. _P4:_ полный AC даёт завершённый бесконечный объект (граф выбора), запрещённый P4; финитный выбор (L5) сохраняется.
- **Classical counterpart.** AC-on-nat is consistent with ZF (and follows from countable choice / is weak); the 'choice graph is a completed infinite set, hence prohibited' argument is an engineered clash with P4CompletedInfinity, not a real inconsistency of AC. Finite L5 choice being constructive is trivial.
- **Tags.** foundation, axiom-of-choice, completed-infinity, P4, methods

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `AC_on_nat/choice_graph/choice_graph_completed` | Definition/Lemma | AC-на-nat и его граф как завершённое множество |
| `ac_implies_completed` | Theorem | AC-на-nat ⟹ завершённый бесконечный объект |
| `L5_choose/L5_choose_in/finite_choice/finite_choice_works` | Definition/Lemma | финитный выбор через голову списка работает |
| `P4_prohibits_AC/L5_choose_deterministic/L5_choose_is_head` | Theorem/Lemma | P4 запрещает AC, сохраняет финитный детерминир. выбор |
| `p4_ac_synthesis` | Theorem | капстоун-синтез |

**Key lemmas (deep):**

- **`ac_implies_completed`** - АРГУМЕНТ ШАТКИЙ: choice_graph f := fun _ => True, поэтому 'граф полон' ТРИВИАЛЬНО (любая тотальная функция). Затем completed_inf_contradicts_P4 бьёт это мостом all-at-once. Но AC-на-nat КОНСИСТЕНТЕН с ZF (слабая форма, следствие счётного выбора); 'запрет' возникает только из P4-определения completed-infinity + искусственного моста, не из самого AC. Финитная часть (finite_choice_works, голова списка) тривиальна. Это онтологическая позиция P4, не математическая невозможность AC. _(axiom-of-choice, completed-infinity, engineered, P4, new-framing)_

**Uniqueness - score 2 (methods).** P4 запрещает полный AC-на-nat (его граф = завершённый объект), сохраняя финитный детерминированный L5-выбор.
> _Caveat:_ AC-на-nat КОНСИСТЕНТЕН с ZF (слабая форма); 'запрет' держится на choice_graph:=fun _=>True (тривиально полон) + искусственном all-at-once мосте, не на самом AC. Это P4-онтология, не невозможность AC. Header заявляет 10 Qed -- фактически 8 (drift).

---

## #349 - `src/foundation/P4ProhibitsImpredicative.v` - score 2 (methods)

**P4 + P1 dissolve Russell: irreflexive membership blocks self-reference, inductive types compatible**

- **Topic.** russell_contradiction_without_P1 (standard Russell False), P1_blocks_russell (irreflexivity makes Russell's criterion trivially all), and nat as stage-bounded inductive type compatible with P4.
- **Role.** Part of P4Prohibits cluster; imports P4CompletedInfinity. Self-contained otherwise (PeanoNat/Lia). June 2026 wave-4 vacuity rollback: nat_is_inductive was exists m, n = m (vacuous) -> every n is 0 or a successor (real inductive structure).
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib: PeanoNat, Lia; ToS: foundation.P4CompletedInfinity
- **E/R/R.** _Elements:_ impredicative_prop; russell_criterion; member; nat_staged_actual. _Roles:_ импредикативность требует завершённой тотальности, P4 это запрещает; P1 (иерархия) блокирует самочленство. _Rules:_ P1 (иерархия) + P4 (конечность) растворяют Russell. _P4:_ 'все множества' = завершённая тотальность (запрещена P4); индуктивные типы строятся стадия-за-стадией (совместимы).
- **Classical counterpart.** Russell's paradox and its resolution by a cumulative hierarchy / type stratification (irreflexive membership) is the textbook foundations result; the 'P4 prohibits impredicativity because all-sets is a completed totality' framing is philosophical, and the actual proofs are the standard Russell derivation.
- **Tags.** foundation, russell, impredicativity, hierarchy, P4, methods

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `NatTotality/impredicative_prop/russell_criterion` | Definition | тотальность, импредикативность, критерий Russell |
| `P1_blocks_russell/russell_contradiction_without_P1` | Theorem | P1 блокирует Russell; без P1 -- противоречие |
| `nat_is_inductive/nat_staged_actual/nat_staged_bounded/nat_eventually_actual` | Lemma/Definition | nat индуктивен, постадийно ограничен и совместим с P4 |
| `P4_dissolves_russell/p4_impredicative_synthesis` | Theorem | капстоуны: P4 растворяет Russell, индуктивные типы совместимы |

**Key lemmas (deep):**

- **`russell_contradiction_without_P1 / P1_blocks_russell`** - russell_contradiction_without_P1 -- СТАНДАРТНЫЙ вывод парадокса Russell (из member r r <-> ~member r r получаем False; ~5 строк). P1_blocks_russell -- тривиально: если членство иррефлексивно (forall x, ~member x x), то критерий Russell ~member x x выполнен для всех x. Связь с 'импредикативностью' и 'завершённой тотальностью' -- чисто словесная (NatTotality определена как тривиально истинная с комментарием, что 'настоящее содержание' в квантификации). Классическое решение (кумулятивная иерархия/типизация) переупаковано под P1/P4. _(russell, impredicativity, hierarchy, standard-result, new-framing)_

**Uniqueness - score 2 (methods).** P1 (иррефлексивное членство) + P4 растворяют Russell; индуктивные типы (nat) P4-совместимы.
> _Caveat:_ russell_contradiction_without_P1 -- учебный вывод парадокса Russell; P1_blocks_russell тривиально (иррефлексивность). Решение через иерархию/типизацию -- классика; связь с 'импредикативностью/завершённой тотальностью' словесная (NatTotality тривиально истинна). Header заявляет 10 Qed -- фактически 7 (drift).

---

## #350 - `src/foundation/ParadoxDiagnosis.v` - score 3 (new-framing)

**Unified paradox diagnosis: all five classical paradoxes are E/R/R ill-formed (by a decidable check)**

- **Topic.** Encodes 5 paradoxes as ERRSystem instances; all evaluate is_well_formed=false (vm_compute); well-formed implies cannot match any paradox; each paradox maps to a specific violation/solution type.
- **Role.** Formalizes the ERR_Framework/Law-of-Order paradox table; depends on foundation.ERRWellFormedness (ERRSystem, is_well_formed, russell/liar/grelling_system).
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, Lia, ZArith, List, PeanoNat, Bool, Lqa; ToS: foundation.ERRWellFormedness
- **E/R/R.** _Elements:_ ParadoxType/ViolationType/SolutionType; paradox_system. _Roles:_ каждый парадокс = конкретное E/R/R-нарушение = конкретное нарушение уровня. _Rules:_ из Law of Order §9.2-9.3 / ERR Framework §6: единая таблица. _P4:_ парадокс = ill-formed E/R/R система (смешение Element/Rule/System); проверка is_well_formed разрешима (vm_compute).
- **Classical counterpart.** The table mapping Russell/Liar/Grelling/Cantor/Burali-Forti to type-theory/Tarski/stratification/no-universal-set/proper-classes is standard foundations exposition; here it is encoded as a decidable is_well_formed check on a small ERRSystem record, so 'all paradoxes ill-formed' is by construction.
- **Tags.** foundation, paradoxes, ERR, new-framing

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `ParadoxType/ViolationType/SolutionType/paradox_violation/paradox_solution/paradox_system` | Inductive/Definition | классификация 5 парадоксов и их разрешений |
| `russell_is_ill_formed/liar_is_ill_formed/grelling_is_ill_formed/cantor_is_ill_formed/buraliforti_is_ill_formed` | Lemma | каждый парадокс ill-formed |
| `all_paradoxes_ill_formed` | Theorem | универсально: ВСЕ парадоксы E/R/R ill-formed |
| `well_formed_paradox_free` | Theorem | well-formed ⟹ не совпадает ни с одним парадоксом |
| `russell_violation/liar_violation/grelling_violation` | Lemma | тип нарушения определён типом парадокса |
| `paradox_diagnosis_synthesis` | Theorem | капстоун-синтез диагностики |

**Key lemmas (deep):**

- **`all_paradoxes_ill_formed`** - Универсальная теорема 'forall p, is_well_formed (paradox_system p) = false' доказывается destruct p; vm_compute -- т.е. ВСЁ закодировано в is_well_formed на маленьком ERRSystem-record так, что парадоксы заведомо ill-formed. Это формализованная ЭКСПОЗИЦИЯ известной таблицы парадоксов (Russell→типы, Liar→Тарский, и т.д.), а не новый результат: 'ill-formedness' -- решение по построению. well_formed_paradox_free -- контрапозитива (subst+discriminate). Cantor/Burali-Forti переиспользуют структуру Russell/Grelling. _(paradoxes, ERR, decidable-check, exposition, by-construction)_

**Uniqueness - score 3 (new-framing).** Единая машинная диагностика: все 5 классических парадоксов = E/R/R ill-formed системы по разрешимой проверке.
> _Caveat:_ Таблица парадоксов (Russell/Liar/Grelling/Cantor/Burali-Forti → типизация/Тарский/...) -- стандартная экспозиция оснований; 'ill-formed' здесь -- по построению (vm_compute на маленьком record). Не новый результат, а формализация известного. Header заявляет 12 Qed -- фактически 11 (drift).

---

## #351 - `src/foundation/PhotonThreeFormulas.v` - score 2 (methods)

**Photon as edge field at causal limit (c^2=1): massless, E_n=n*omega, sharp light cone over Q**

- **Topic.** Edge wave step; photon rest energy 0, photon_level=n*omega (no 1/2 offset), level spacing omega; at c^2=1 the self-coupling vanishes giving full amplitude transfer / sharp cone; photon vs sound transfer ratio 4.
- **Role.** Completes the SHO(matter)/AcousticChain(sound)/Photon(light) triad. Imports foundation.SHOThreeFormulas + foundation.AcousticChainThreeFormulas.
- **Counts.** Qed 15 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, Qabs, ZArith, List, PeanoNat, Lia, Lqa; ToS: foundation.SHOThreeFormulas, foundation.AcousticChainThreeFormulas
- **E/R/R.** _Elements:_ edge_step; photon_level omega n = n*omega; photon_rest_energy=0. _Roles:_ E-формула тривиальна (rest=0); R-спектр = лестница без 1/2; R-правила = реберное волновое ур-ние при c^2=1. _Rules:_ при c^2=1 коэффициент (2-2c^2)=0 ⟹ полный перенос, резкий световой конус. _P4:_ конечные рациональные вычисления над Q (Element); фотон = реберное поле на причинном пределе.
- **Classical counterpart.** The massless photon (zero rest energy, E_n=n*omega, no zero-point), the massless wave equation on a lattice, and a sharp light cone at c=1 are standard physics; NEW only as exact Q computations completing a vertex/edge/mode E/R/R triad. 'Same wave equation, different carrier' is the framing.
- **Tags.** foundation, photon, wave-equation, light-cone, methods

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `edge_step/photon_impulse/photon_zero/photon_rest_energy/photon_massless` | Definition/Theorem | реберный шаг; нулевая масса покоя |
| `photon_level/photon_level_0/photon_level_1/photon_spacing/photon_no_zero_point` | Definition/Theorem | E_n=n*omega, зазор omega, нет zero-point (vs SHO) |
| `photon_ratio_2_to_1/photon_ratio_3_to_1` | Theorem | E_n/E_1 = n (целые отношения) |
| `causal_coefficient_vanishes/photon_full_transfer/sound_partial_transfer/photon_vs_sound_ratio` | Theorem | при c^2=1 полный перенос; фотон/звук = 4 |
| `photon_causal/photon_leaves_source/sound_stays_at_source` | Theorem | резкий конус; источник опустошается (vs звук) |
| `photon_three_formulas` | Theorem | капстоун: три формулы фотона |

**Key lemmas (deep):**

- **`causal_coefficient_vanishes / photon_full_transfer`** - Аккуратные Q-вычисления (vm_compute/ring) для безмассового реберного поля: при c^2=1 самосопряжение (2-2c^2)=0, импульс полностью уходит к соседу (резкий конус), отношение переноса фотон/звук = 4 = c^2_light/c^2_sound. Физика стандартна (безмассовое волновое ур-ние, световой конус); вклад -- точная Q-формализация и завершение vertex/edge/mode E/R/R-триады. photon_no_zero_point подаёт E_0=0<omega/2 как структурное отличие материи от излучения. Не новая физика. _(photon, massless, wave-equation, light-cone, triad)_

**Uniqueness - score 2 (methods).** Фотон как реберное поле на причинном пределе c^2=1 над Q: безмассовость, E_n=n*omega, резкий конус, отношение переноса 4 к звуку.
> _Caveat:_ Безмассовый фотон, лестница без zero-point и резкий световой конус -- стандартная физика; вклад -- точные Q-вычисления и завершение E/R/R-триады vertex/edge/mode, не новая физика. Header заявляет 22 Qed -- фактически 15 (drift).

---

## #352 - `src/foundation/PhysicalProcess.v` - score 3 (new-framing)

**Every physical process = three E/R/R formulas: one record, seven toy instantiations**

- **Topic.** PhysicalProcess record (pp_evolve=Rules, pp_spectrum=Roles, pp_ground=Elements) instantiated for Sound/Light/QM/Thermal/Casimir/Gravity/SM on tiny graphs; lemmas verify ground states, Born=1/4, Casimir ZPE=4, SU(3)=8 generators.
- **Role.** Generic schema reused by ObserverCompressor.v (pp_energy, impulse_pp). Self-contained (QArith). June 2026 wave-4 sweep: vacuous finiteness-shams (exists q, _ = q) replaced by the by-type finite-ratio form (num#den); see UNIQUENESS.md. (pp_well_formed Definition was always-true; now by-type form.)
- **Counts.** Qed 14 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, Qabs, Lia, ZArith, List, PeanoNat, Bool, Lqa
- **E/R/R.** _Elements:_ PhysicalProcess record; 7 инстансов (Sound..SM); pp_energy. _Roles:_ R(Rules)=ур-ние движения; R(Roles)=спектральное разложение; E=поле на графе. _Rules:_ порождающий порядок Rules→Roles→Elements; одна запись, разные параметры. _P4:_ каждый физпроцесс = три E/R/R формулы на конечном графе (Element); 7 доменов = одна структура.
- **Classical counterpart.** Bundling equation-of-motion / spectral decomposition / ground state into one record and instantiating it for 7 domains (sound, light, QM, thermal, Casimir, gravity, SM) is an organizational schema; each instance is a toy 4-vertex Q computation. The 'physics = same three formulas, different parameters' claim is a framing, and the SM/gauge generator counts are over-branded.
- **Tags.** foundation, err-schema, seven-domains, over-branding, new-framing

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `PhysicalProcess/pp_energy/pp_well_formed/zero_field_pp/impulse_pp/inner_pp/const_basis/alt_basis` | Record/Definition | общая запись и хелперы June 2026 wave-4 sweep: vacuous finiteness-shams (exists q, _ = q) replaced by the by-type finite-ratio form (num#den); see UNIQUENESS.md. (pp_well_formed Definition was always-true; now by-type form.) |
| `sound_process/sound_ground_zero/sound_well_formed` | Definition/Lemma | звук: волновое ур-ние c^2=1/4 June 2026 wave-4 sweep: vacuous finiteness-shams (exists q, _ = q) replaced by the by-type finite-ratio form (num#den); see UNIQUENESS.md. (pp_well_formed Definition was always-true; now by-type form.) |
| `light_process/light_ground_zero` | Definition/Lemma | свет: реберное ур-ние c^2=1 June 2026 wave-4 sweep: vacuous finiteness-shams (exists q, _ = q) replaced by the by-type finite-ratio form (num#den); see UNIQUENESS.md. (pp_well_formed Definition was always-true; now by-type form.) |
| `qm_process/qm_born_rule` | Definition/Lemma | QM: Born \|A\|^2=1/4 June 2026 wave-4 sweep: vacuous finiteness-shams (exists q, _ = q) replaced by the by-type finite-ratio form (num#den); see UNIQUENESS.md. (pp_well_formed Definition was always-true; now by-type form.) |
| `thermal_process/thermal_equal_amplitudes/casimir_process/casimir_vacuum_*/casimir_zpe` | Definition/Lemma | термал; Казимир ZPE=4 June 2026 wave-4 sweep: vacuous finiteness-shams (exists q, _ = q) replaced by the by-type finite-ratio form (num#den); see UNIQUENESS.md. (pp_well_formed Definition was always-true; now by-type form.) |
| `gravity_process/gravity_flat/sm_process/sm_su2_generators/sm_su3_generators/sm_total_12` | Definition/Lemma | гравитация плоская; SM генераторы 3,8,12 June 2026 wave-4 sweep: vacuous finiteness-shams (exists q, _ = q) replaced by the by-type finite-ratio form (num#den); see UNIQUENESS.md. (pp_well_formed Definition was always-true; now by-type form.) |
| `seven_instances_exist/physical_process_synthesis` | Theorem | капстоуны: 7 инстансов, гранд-синтез June 2026 wave-4 sweep: vacuous finiteness-shams (exists q, _ = q) replaced by the by-type finite-ratio form (num#den); see UNIQUENESS.md. (pp_well_formed Definition was always-true; now by-type form.) |

**Key lemmas (deep):**

- **`sm_su3_generators / physical_process_synthesis`** - Организационная СХЕМА: один record с тремя полями, заполненный для 7 доменов на графах из 4 вершин; леммы -- vm_compute на конкретных числах. 'physics = same three formulas' -- рамка, не теорема. SM-инстанс особенно ПЕРЕБРЕНДЕН: pp_evolve sm := curr*curr-1, ground=[2,3,1]; '8 генераторов SU(3)' = вычисление 3*3-1, '12' = 3+8+1 -- это подгонка под N^2-1, а не вывод калибровочной группы. Гравитация 'curvature=degree-average' -- словесная аналогия. Полезно как каталог E/R/R-разложений, не как физика. _(err-schema, seven-domains, sm-generators, over-branding, toy-model)_

**Uniqueness - score 3 (new-framing).** Единая E/R/R-запись (evolve/spectrum/ground), инстанцированная для 7 физдоменов: одна структура, разные параметры.
> _Caveat:_ Организационная схема на игрушечных 4-вершинных графах (vm_compute); 'физика = три формулы' -- рамка, не теорема. SM-инстанс ПЕРЕБРЕНДЕН (8=3*3-1 подгонка под N^2-1, не вывод SU(3)); гравитация -- словесная аналогия. Header заявляет 18 Qed -- фактически 14 (drift).

---

## #353 - `src/foundation/PhysicsDemarcation.v` - score 4 (synthesis+observation)

**Popperian demarcation of ToS physics claims: 2 confirmed predictions, not many (with teeth)**

- **Topic.** Classifies 10 headline claims into Prediction/Postdiction/Reframing; proves the ratio model fits any target (postdiction has no content), SHO 2n+1 is analytic (v==v), 3/13 is sharp/synthetic/matches but has a postdiction shadow (r=3/10 gives 3/13); honest count: 4/3/3, only 2 confirmed.
- **Role.** Epistemic-content audit axis complementing PredictionHonesty.v and ProcessDerivedVsConsistent.v. Self-contained (QArith/Lqa/Lia/List). The brutal-honesty showcase of the batch.
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, Lqa, Lia, List
- **E/R/R.** _Elements:_ EpiStatus {Prediction/Postdiction/Reframing}; Claim (10 заявлений); 3/13; параметр r; тождество v==v. _Roles:_ Prediction=безпараметрично+фальсифицируемо+синтетично; Postdiction=подогнанный r; Reframing=аналитично. _Rules:_ постдикция r/(1+r) ловит ЛЮБОЕ s≠1 (нефальсифицируема); переформулировка v==v (не может быть ложной); предсказание sharp+синтетично (3/13≠0.23121 символьно, но \|Δ\|<1/2000). _P4:_ синтетическое предсказание пересекает границу к данным (могло не совпасть = 'Element-подобно'); переформулировка аналитична (истинна по построению, границу не пересекает). Честный счёт: 2 подтверждённых.
- **Classical counterpart.** Popper's falsifiability and the analytic/synthetic distinction applied to a theory's own claims; NEW as a self-audit with machine-checked DISCRIMINATORS (postdiction fits anything; reframing is v==v; prediction is sharp+synthetic+matches), brutally deflating the repo's own physics 'successes' to 2 confirmed.
- **Tags.** foundation, popper, falsifiability, brutal-honesty, weinberg-deflation, synthesis+observation

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `EpiStatus/Claim/status/matched/all_claims` | Inductive/Definition | эпистемические статусы и реестр 10 заявлений |
| `prediction_sharp/prediction_synthetic/prediction_matches` | Lemma | 3/13 sharp (≠1/4,1/5), синтетично (≠0.23121), совпадает (<1/2000) |
| `postdiction_fits_anything/postdiction_shadow` | Lemma | r/(1+r) ловит любое s≠1; r=3/10 даёт то же 3/13 |
| `sho_gap/reframing_analytic/reframing_concrete` | Definition/Lemma | SHO 2n+1 аналитично (v==v), не может быть ложным |
| `status_eqb/count_status/n_prediction/n_postdiction/n_reframing` | Definition/Lemma | счёт: 4 предсказания / 3 постдикции / 3 переформулировки |
| `confirmed_predictions/n_confirmed` | Definition/Lemma | ровно 2 подтверждённых безпараметрических предсказания |
| `physics_demarcation` | Theorem | капстоун: демаркация с машинными зубами |

**Key lemmas (deep):**

- **`postdiction_fits_anything / postdiction_shadow / n_confirmed`** - ВИТРИНА БРУТАЛЬНОЙ ЧЕСТНОСТИ. postdiction_fits_anything: для любого s≠1 есть r с r(1-s)=s (r:=s/(1-s), Qmult_inv_r) -- значит модель отношения r/(1+r) предсказывает НИЧЕГО до независимой фиксации r. postdiction_shadow машинно: (3/10)/(1+3/10)=3/13 -- флагманское значение имеет постдикционную тень, т.е. 3/13 -- предсказание ТОЛЬКО через принудительный DOF-маршрут. reframing_analytic: 2n+1 -- тождество (не фальсифицируемо). n_confirmed=2: после снятия переформулировок (не могут быть ложны) и постдикций (ловят что угодно) остаётся 2 подтверждённых предсказания, а не 'дюжина успехов'. Это прямо ДЕЗАВУИРУЕТ перебренд из NumericalPredictions.v. Уровень -- синтез+наблюдение с зубами. _(popper, falsifiability, brutal-honesty, postdiction-shadow, weinberg-deflation)_

**Uniqueness - score 4 (synthesis+observation).** Попперовская демаркация заявлений ToS с машинными дискриминаторами: постдикция ловит что угодно, переформулировка = v==v, предсказание sharp+синтетично; честный итог -- 2 подтверждённых безпараметрических предсказания.
> _Caveat:_ Сам критерий Поппера и аналитич/синтетич -- классическая философия науки; новое -- применение к claim'ам репозитория с машинными зубами. Доказывает НЕ новую физику, а ДЕЗАВУИРУЕТ перебренд (3/13 имеет постдикционную тень r=3/10; 'успехов' не дюжина, а 2). Header 12 Qed совпадает.

---

## #354 - `src/foundation/PhysicsERR.v` - score 2 (methods)

**Three E/R/R formulas (field/spectrum/evolution) on a graph: the A=exists -> physics chain (toy)**

- **Topic.** FieldOnGraph + DFT spectral_coeff + evolve_single/evolve_chain; lemmas: impulse energy 1, const/alt modes 1/4, period-4 oscillation, causal propagation, Born example; narrates the full A=exists->physics chain in comments.
- **Role.** Earlier/sibling version of PhysicalProcess.v's schema; the comment chain references Distinction/Laws/Principles files. Self-contained code (QArith).
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, Qabs, Lia, ZArith, List, PeanoNat, Lqa
- **E/R/R.** _Elements:_ FieldOnGraph; spectral_coeff; evolve_single/evolve_chain. _Roles:_ E=что существует (L1); R=что значит (L4, спектр); R=как меняется (L5, эволюция). _Rules:_ три формулы + граф = вся физика; порядок A=exists→Distinction→L1-L5→P1-P4→E/R/R→3 формулы. _P4:_ конечные N-точечные поля над Q (Element); физика = {граф × тип поля × связи}.
- **Classical counterpart.** The deductive-chain narrative (A=exists -> Distinction -> L1-L5 -> P1-P4 -> E/R/R -> three formulas -> physics) plus a field/spectrum/evolution decomposition on a graph; each lemma is a toy N=4 Q computation. The 'three formulas = entire physics' claim is a framing, and the 'A=exists' chain is asserted in comments, not proven here.
- **Tags.** foundation, err-chain, three-formulas, dft, methods

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `FieldOnGraph/zero_field/impulse_field/field_energy/zero_field_zero_energy/impulse_has_energy` | Definition/Lemma | E-формула: поле и энергия на графе |
| `inner_product_N/spectral_coeff/mode_energy/basis_const/basis_alt/const_mode_of_impulse/alt_mode_of_impulse` | Definition/Lemma | R-формула: спектральное разложение (DFT) |
| `evolve_single/evolve_chain/oscillation_period4/propagation_causal` | Definition/Lemma | R-формула: эволюция, осцилляция период 4, причинное распространение |
| `E_from_L1/sound_step/born_probability/born_normalized_example/thermal_energy` | Lemma/Definition | E↔L1; инстансы звук/QM/термал |
| `physics_err_chain` | Theorem | капстоун: цепь A=exists→E/R/R→физика (на примерах N=4) |

**Key lemmas (deep):**

- **`physics_err_chain`** - Сиблинг/более ранняя версия схемы PhysicalProcess.v: те же три формулы (поле/спектр/эволюция) на N=4 графе, леммы -- vm_compute/ring. Главное -- НАРРАТИВ в комментариях, разворачивающий полную цепь A=exists→Distinction→L1-L5→P1-P4→E/R/R→3 формулы→физика со ссылками на другие файлы. Но сам файл доказывает лишь конкретные числовые факты (энергия импульса=1, моды=1/4, осцилляция период 4); 'A=exists' и 'три формулы = вся физика' -- утверждения комментариев, не теоремы здесь. E_from_L1 = reflexivity. Перекрывается с PhysicalProcess.v. _(err-chain, three-formulas, dft, toy-model, narrative)_

**Uniqueness - score 2 (methods).** Три E/R/R формулы (поле/спектр/эволюция) на графе с нарративом цепи A=exists→физика; конкретные N=4 вычисления.
> _Caveat:_ Сиблинг PhysicalProcess.v (дублирует схему); доказывает лишь игрушечные N=4 факты (vm_compute), а 'A=exists→...→вся физика' -- нарратив комментариев со ссылками на другие файлы, не теорема здесь. E↔L1 = reflexivity. Header заявляет 15 Qed -- фактически 9 (drift).

---

## #355 - `src/foundation/PiAngleAllTriples.v` - score 4 (synthesis+observation)

**pi-incommensurability for ALL coprime Pythagorean triples via mod-p eigenvector (generalizes 2a==1)**

- **Topic.** Mod p (p|c) the rotation sends (a,b) to 2a*(a,b) (eigenvector), so X_n == (2a)^(n-1)*a; if p coprime to a and 2a then X_n != c^n: infinite order. Taking p=c covers EVERY primitive triple, incl. 5-12-13, 8-15-17, 20-21-29 missed by 2a==1.
- **Role.** Generalizes foundation.PiAngleRoleLimit (the fixed-point case); reuses its Rot/Xr/Yr/cpow and algebra.RationalRootTest (zpow, rel_prime_zpow).
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: ZArith, Znumtheory, Lia; ToS: algebra.RationalRootTest, foundation.PiAngleRoleLimit
- **E/R/R.** _Elements:_ целочисленный поворот (Xn,Yn)×c^n; собственный вектор (a,b) с множителем 2a mod p. _Roles:_ конечный порядок = π-соизмеримость (Element); бесконечный = π-несоизмеримость (role-limit). _Rules:_ mod p (p\|c): (a,b)↦2a·(a,b) (т.к. a²−b²≡2a²) ⟹ Xn≡(2a)^(n−1)·a; coprime(p,2a),(p,a) ⟹ Xn≢0 ⟹ Xn≠c^n. _P4:_ модуль = c (для примитивной тройки coprime к a,2a) ⟹ ВСЕ примитивные тройки дают углы ∉ πℚ (role-limit); 2a≡1 был лишь неподвижной точкой.
- **Classical counterpart.** Niven's theorem (the only rational values of (1/pi)*arccos(r) for rational r are 0,1/2,...) is classical; this is its CONSTRUCTIVE shadow for ALL coprime Pythagorean triples via an eigenvector-mod-p argument, generalizing PiAngleRoleLimit's fixed-point criterion. It proves angles are irrational multiples of pi, NOT pi's own irrationality (Niven's integral).
- **Tags.** foundation, niven, pythagorean-triples, number-theory, role-limit, synthesis+observation

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `rot_mod_eigen` | Lemma | ★ орбита = (a,b)-собственная линия ×(2a)^(n−1) mod p |
| `rp_compute/rel_prime_not_div` | Lemma | хелперы взаимной простоты |
| `rotation_inf_order_coprime` | Theorem | ★★ p\|c coprime к a,2a ⟹ Xn≠c^n (бесконечный порядок) |
| `angle_role_limit_general` | Corollary | угол = role-limit (общая версия) |
| `role_limit_5_12_13/role_limit_8_15_17/role_limit_20_21_29` | Corollary | тройки, пропущенные критерием 2a≡1 |
| `pi_angle_all_triples` | Theorem | капстоун: ВСЕ coprime-тройки + семейство |

**Key lemmas (deep):**

- **`rot_mod_eigen / rotation_inf_order_coprime`** - НАСТОЯЩАЯ математика (не reflexivity): mod p при p\|c имеем b²≡−a², поэтому шаг поворота (a²−b², 2ab)≡(2a², 2ab)=2a·(a,b) -- (a,b) собственный вектор с собственным значением 2a. Индукцией Xn≡(2a)^(n−1)·a; при coprime(p,a),(p,2a) это ≢0, тогда как c^n≡0, значит Xn≠c^n -- бесконечный порядок, угол ∉ πℚ. Беря p=c (для примитивной тройки c нечётно, gcd(a,c)=1, gcd(2a,c)=1) покрываем ВСЕ примитивные тройки, включая 5-12-13/8-15-17/20-21-29, которые fixed-point-критерий 2a≡1 ПРОПУСКАЛ. Обобщает PiAngleRoleLimit с одного семейства до всех coprime-троек. Честно: это углы, не сам π (интеграл Нивена не трогается). _(niven, pythagorean-triples, eigenvector-mod-p, infinite-order, role-limit)_

**Uniqueness - score 4 (synthesis+observation).** Конструктивный π-несоизмеримый результат для ВСЕХ взаимно простых пифагоровых троек через собственный вектор mod p (множитель 2a); обобщает критерий неподвижной точки 2a≡1, ловя 5-12-13/8-15-17/20-21-29.
> _Caveat:_ Теорема Нивена (рациональные значения arccos(r)/π) -- КЛАССИЧЕСКАЯ; это её конструктивная тень для троек, доказывает несоизмеримость УГЛОВ, НЕ иррациональность самого π (интеграл Нивена -- стена, не трогается). Header 9 Qed совпадает.

---

## #356 - `src/foundation/PiAngleRoleLimit.v` - score 4 (synthesis+observation)

**pi-incommensurability criterion 2a==1 mod p: Pythagorean rotation has infinite order (a family)**

- **Topic.** Integer rotation Rot/Xr/Yr scaled by c^n; under 2a==1 (mod p), p|c, the orbit is fixed at (a,b) mod p (n>=1), so X_n != c^n: infinite order, arccos(a/c)/pi irrational. pi_commensurable = orbit returns to identity (role-limit on its negation).
- **Role.** Generalizes NivenRationalCosine.v's 3-4-5 case; base for PiAngleAllTriples.v (which uses its Rot/Xr/Yr/cpow). Self-contained (ZArith/Znumtheory/Lia).
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: ZArith, Znumtheory, Lia
- **E/R/R.** _Elements:_ целочисленные (Xn,Yn) поворота (×c^n); рациональные точки орбиты. _Roles:_ конечный порядок = π-СОИЗМЕРИМОСТЬ (угол ∈ πℚ, Element — процесс замыкается); бесконечный = π-НЕсоизмеримость (role-limit). _Rules:_ 2a≡1 (mod p), p\|c ⟹ (Xn,Yn)≡(a,b) mod p (неподвижная точка) ⟹ Xn≢0 ⟹ Xn≠c^n ⟹ бесконечный порядок. _P4:_ 'возврат поворота в тождество' = role-limit (требует π-соизмеримости, над ℚ не актуализуется); рациональный cos=a/c с углом ∉ πℚ — апериодический процесс; НЕ иррациональность самого π.
- **Classical counterpart.** Niven's rational-cosine theorem; this isolates a sufficient criterion (2a==1 mod p, p\|c) for a Pythagorean rotation to have infinite order, generalizing NivenRationalCosine's single 3-4-5 mod-5 case to a family (3-4-5, 33-56-65 via p=5). Proves angles are irrational multiples of pi, not pi itself.
- **Tags.** foundation, niven, rational-cosine, number-theory, role-limit, synthesis+observation

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `Rot/Xr/Yr/Xr_S/Yr_S/Xr_1/Yr_1` | Fixpoint/Definition/Lemma | целочисленный поворот и рекуррентности |
| `cpow/cpow_div` | Fixpoint/Lemma | c^n и делимость p\|c^n |
| `rot_mod_fixed` | Lemma | ★ (Xn,Yn)≡(a,b) mod p для n≥1 (неподвижная точка) |
| `not_div_a/rotation_infinite_order` | Lemma/Theorem | ★★ p∤a; Xn≠c^n -- бесконечный порядок |
| `pi_commensurable/angle_is_role_limit` | Definition/Corollary | π-соизмеримость; угол = role-limit |
| `role_limit_345/role_limit_33_56_65` | Corollary | 3-4-5 и 33-56-65 через p=5 |
| `pi_angle_role_limit` | Theorem | капстоун: критерий + семейство |

**Key lemmas (deep):**

- **`rot_mod_fixed / rotation_infinite_order`** - НАСТОЯЩАЯ теоретико-числовая работа (nia/индукция, не reflexivity): при 2a≡1 (mod p) и p\|c шаг поворота фиксирует (a,b) mod p, т.к. a²−b²−a=a(2a−1)−c²≡0 и 2ab−b=b(2a−1)≡0. Тогда Xn≡a≢0 (p∤a, иначе p\|1 из 2a−1), а c^n≡0, значит Xn≠c^n -- поворот никогда не возвращается в тождество, бесконечный порядок, arccos(a/c)/π ∉ ℚ. Изолирует ПОЧЕМУ работал mod-5 инвариант 3-4-5 и обобщает на семейство (33-56-65 via p=5). Честная рамка: π-соизмеримость = Element (процесс замыкается), несоизмеримость = role-limit; доказывает иррациональность УГЛА, явно НЕ самого π (интеграл Нивена -- стена). PiAngleAllTriples затем заменяет фикс-точку на собственный вектор для ВСЕХ троек. _(niven, rational-cosine, mod-p-fixed-point, infinite-order, role-limit)_

**Uniqueness - score 4 (synthesis+observation).** Общий критерий 2a≡1 (mod p), p|c ⟹ пифагоров поворот имеет бесконечный порядок (угол ∉ πℚ), покрывающий семейство (3-4-5, 33-56-65 via p=5); в репо ранее был лишь случай 3-4-5.
> _Caveat:_ Теорема Нивена о рациональных косинусах -- КЛАССИЧЕСКАЯ; это её конструктивная тень + изоляция достаточного критерия. Доказывает несоизмеримость УГЛА, НЕ иррациональность самого π (интеграл Нивена ∫xⁿ(π−x)ⁿsin x -- стена, не трогается). Header заявляет 10 Qed -- фактически 12 (drift).

---

## #357 - `src/foundation/PiAngleScaleInvariant.v` - score 4 (synthesis+observation)

**Scale-invariance of pi-commensurability: every Pythagorean triple reduces to its primitive core**

- **Topic.** The rotation by g*(a,b) over scale g*c equals g^n times the rotation by (a,b)/c, so finite order (pi-commensurability) is invariant under scaling; hence 6-8-10 and 15-20-25 (missed by the coprime criterion) reduce to 3-4-5.
- **Role.** Builds on foundation.PiAngleRoleLimit (Rot/Xr/Yr/cpow, role_limit_345) and algebra.RationalRootTest. Closes the non-primitive triples that PiAngleAllTriples could not reach; consumed by PrimitiveTripleNT and the RoleLimitTaxonomy orbit-closure stratum.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: ZArith Lia; ToS: algebra.RationalRootTest, foundation.PiAngleRoleLimit
- **E/R/R.** _Elements:_ масштаб g; поворот g*(a,b) над g*c; примитивное ядро (a,b,c). _Roles:_ pi-соизмеримость = конечный порядок (Element); масштаб не меняет угол => инвариант. _Rules:_ Rot (g*a)(g*b) n = g^n*Rot a b n; cpow (g*c) n = g^n*cpow c n => соизмеримость(g*abc) <=> соизмеримость(abc). _P4:_ любая тройка = g*(примитивная), угол тот же => беск. порядок ВСЕХ непримитивных сводится к примитивному ядру. Граница: вырожденные (ось, cos=1) соизмеримы, невырожденные = role-limit.
- **Classical counterpart.** Niven's theorem (rational multiples of pi with rational cosine) — here only the CONSTRUCTIVE shadow over Z: scale-invariance of finite-order rotation extends infinite order from primitive to ALL Pythagorean triples. NOT pi-irrationality itself (Niven's integral is the uncrossed wall).
- **Tags.** foundation, pythagorean, pi, scale-invariance, role-limit, niven, synthesis

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `zpow_nonzero/cpow_scale/rot_scale` | Lemma | законы масштабирования g^n для cpow и поворота Xr/Yr |
| `pi_commensurable_scale` | Theorem | ★★ pi-соизмеримость инвариантна относительно масштаба g<>0 |
| `role_limit_6_8_10/role_limit_15_20_25` | Corollary | ★ непримитивные тройки сводятся к 3-4-5 (role-limit) |
| `degenerate_commensurable` | Corollary | ★ вырожденный случай (c,0)/c (cos=1) соизмерим (порядок 1) |
| `pi_angle_scale_invariant` | Theorem | capstone: инвариантность + обе непримитивные + вырожденная сторона |

**Key lemmas (deep):**

- **`pi_commensurable_scale`** - Структурный фикс: rel_prime-аргумент (модуль c) НЕ достаёт 15-20-25 (5\|a=15); масштаб-инвариантность сводит ЛЮБУЮ тройку к примитивному ядру через g^n-сокращение (Z.mul_cancel_l при g^n<>0). Машинно проверено, 0 аксиом. Завершает конструктивную тень Нивена для ВСЕХ невырожденных пифагоровых углов. _(scale-invariance, pythagorean, niven-shadow, new-theorem)_

**Uniqueness - score 4 (synthesis+observation).** Масштаб-инвариантность pi-соизмеримости => беск. порядок ВСЕХ пифагоровых троек (а не только взаимно-простых) + полная картина границы конечный/беск. порядок.
> _Caveat:_ Это КОНСТРУКТИВНАЯ ТЕНЬ теоремы Нивена над Z (угол arccos(a/c), не сама pi). Иррациональность pi (интеграл Нивена) — стена, НЕ пересечена. Сама масштабная лемма g^n элементарна; новизна — полнота охвата троек.

---

## #358 - `src/foundation/PiRational.v` - score 1 (exposition)

**Better pi over Q: 355/113 within Archimedes' bounds; beta_0(SU3) robustness**

- **Topic.** 355/113 (Zu Chongzhi) lies inside the Archimedes interval and below 22/7; the one-loop QCD beta_0 with n_f=3 changes by < 1/100 between the two pi approximations, so the qualitative (asymptotic-freedom) result is unchanged.
- **Role.** Self-contained (QArith/Lqa). Supplies a sharper rational pi and a beta_0 sensitivity bound; pedagogical companion to the lattice/RG layer.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lia ZArith Qabs Lqa
- **E/R/R.** _Elements:_ pi_7=22/7; pi_113=355/113; границы Архимеда; beta_0. _Roles:_ 355/113 = улучшенное приближение (Element); beta_0 = производная роль от pi. _Rules:_ pi_lower<pi_113<pi_upper; beta_0_pi113 - beta_0_pi7 < 1/100. _P4:_ конечные рациональные границы pi над Q (Element); никакого завершённого пи.
- **Classical counterpart.** Zu Chongzhi's 355/113 and Archimedes' bounds (223/71 < pi < 22/7) are classical (5th c. / antiquity); NEW only as machine-checked Q bounds and the QCD beta_0 sensitivity check.
- **Tags.** foundation, pi, rational, qcd, beta-function, exposition

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `pi_7/pi_113/pi_lower/pi_upper/beta_0_pi7/beta_0_pi113` | Definition | приближения pi и beta_0 на двух значениях |
| `pi_bounds/pi_113_in_lower_bound/_in_upper_bound/_in_bounds/pi_113_lt_pi_7` | Lemma | 355/113 внутри границ Архимеда, ниже 22/7 |
| `beta_0_pi7_positive/beta_0_pi113_positive/beta_0_both_positive/beta_0_close` | Lemma | beta_0 > 0 и расхождение < 1/100 |
| `pi_summary` | Theorem | синтез: границы + положительность + малость расхождения |

**Key lemmas (deep):**

- **`beta_0_close`** - Sensitivity-проверка: качественный результат (асимптотическая свобода, beta_0>0) устойчив к выбору рационального pi — расхождение beta_0 < 1/100, доказано lia на целочисленных числителях. Содержательно тривиально, но честная демонстрация робастности. _(pi, beta_0, qcd, robustness)_

**Uniqueness - score 1 (exposition).** 355/113 внутри границ Архимеда + устойчивость одно-петлевого beta_0(SU3,n_f=3) к выбору рационального pi.
> _Caveat:_ 355/113 (Цзу Чунчжи) и границы Архимеда — древняя классика; beta_0=11N-2n_f/(12pi) — стандартная КХД. Вклад чисто экспозиционный: машинная проверка Q-границ, не новый результат.

---

## #359 - `src/foundation/PlanckBridge.v` - score 2 (methods)

**Planck bridge: E=h*nu as n=1 of photon ladder; exact Balmer/Lyman ratios over Q**

- **Topic.** Dimensional bridge from natural-unit photon ladder to SI E=h*nu; h in [6.626,6.627]e-34; Balmer H-beta/H-alpha = 20/27 and Lyman/Balmer = 27/5 as pure rationals independent of the Rydberg constant.
- **Role.** Builds on foundation.PhotonThreeFormulas (photon_level, photon_spacing, photon_level_1). Numerical-prediction layer; the wavelength ratios are cited in HIGHLIGHTS-style summaries.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs ZArith List PeanoNat Lia Lqa; ToS: foundation.PhotonThreeFormulas
- **E/R/R.** _Elements:_ h_planck_e34; balmer_factor (5/36,3/16,21/100); lyman_alpha_factor 3/4. _Roles:_ E=h*nu = n=1 случай фотонной лестницы (Role-спектр); отношения длин волн = чистые рациональные роли. _Rules:_ photon_level omega 1 == omega; balmer 20/27; lyman/balmer 27/5 — независимы от Ридберга. _P4:_ точные рациональные отношения над Q (Element); h как фиксированная рациональная константа, без завершённой бесконечности.
- **Classical counterpart.** Planck relation E=h*nu and the Balmer/Lyman hydrogen series are textbook spectroscopy; the SI-2019 exact h is metrology. NEW only as the framing E=h*nu = n=1 case of the photon ladder, and exact rational wavelength ratios (R-independent).
- **Tags.** foundation, planck, balmer, hydrogen, prediction, methods, qed-drift

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `h_planck_e34/balmer_factor/lyman_alpha_factor` | Definition | константа Планка и факторы переходов |
| `h_lower/h_upper` | Theorem | h в [6.626,6.627]e-34 (vm_compute) |
| `planck_relation_is_n1/n_photon_energy` | Theorem | E=h*nu = n=1 фотонного спектра; шаг лестницы |
| `balmer_alpha_factor/balmer_beta_factor/balmer_wavelength_ratio/balmer_gamma_alpha_ratio` | Theorem | ★ Бальмер 20/27, 125/189 — точные рациональные отношения |
| `lyman_balmer_wavelength_ratio` | Theorem | ★ Лайман/Бальмер 27/5 (5/27 длин волн) |
| `planck_bridge_predictions` | Theorem | grand: n=1 + h-границы + Бальмер + Лайман |

**Key lemmas (deep):**

- **`balmer_wavelength_ratio`** - Отношение длин волн H-beta/H-alpha = (5/36)/(3/16) = 20/27 = 0.7407 СОВПАДАЕТ с наблюдением (486.1/656.3) до 4 знаков, и оно НЕ ЗАВИСИТ от Ридберга — чистое целочисленное следствие 1/n^2. Машинно (vm_compute). Стандартная спектроскопия, но рациональная инвариантность отношений — приятное наблюдение. _(balmer, hydrogen, rational-ratio, prediction)_

**Uniqueness - score 2 (methods).** E=h*nu как n=1 фотонной лестницы (а не постулат) + точные R-независимые рациональные отношения Бальмера/Лаймана над Q.
> _Caveat:_ Соотношение Планка, серии водорода и SI-значение h — учебник/метрология. ДРЕЙФ: заголовок объявляет 12 Qed, фактически 10. Вклад методический: переобрамление + рациональные отношения, не новая физика.

---

## #360 - `src/foundation/PositFloor.v` - score 1 (exposition)

**Posit floor: the whole SM structure rides on exactly 5 named posits**

- **Topic.** Assembles GaugePositReduction and GenerationsPositReduction into one named floor sm_floor = {Classic, P4, L1NoRep, L4Min, Reflexive}; generations reuse L4-minimality (no new posit); a new honesty tier rides_on_named_floor refines the vague rides_on_model.
- **Role.** Builds on foundation.GaugePositReduction (gauge_unique, Just, n_posits) and foundation.GenerationsPositReduction (generations_unique). Capstone of the 'weakness #1' audit arc; pairs with FoundationAudit and ReductionAtlasSynthesis.
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: List Arith Lia; ToS: foundation.GaugePositReduction, foundation.GenerationsPositReduction
- **E/R/R.** _Elements:_ перечисление NamedPosit; sm_floor; собранные кирпичи (gauge_just, exactly3_just); счёт. _Roles:_ названный пол (framework 2 + структурные 3) = явный честный пол; переиспользование L4Min = экономия постулатов. _Rules:_ вся структура СМ едет на 5 названных постулатах; rides_on_named_floor уточняет rides_on_model. _P4:_ закрытие != обнуление; вся структура -> 5 названных постулатов (не сыпь, не «модель»); дно Мюнхгаузена явно и сосчитано (=5, не ноль).
- **Classical counterpart.** No classical counterpart — this is an internal ToS bookkeeping/audit artifact (a Munchhausen-trilemma posit ledger). Analogous in spirit to a 'minimal axiom set' audit, but the SM-structure derivation it cites is the project's own (over-branded) claim.
- **Tags.** foundation, posit-ledger, audit, munchhausen, standard-model, exposition, over-branded-flag

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `NamedPosit/framework_floor/gauge_floor/gen_floor/sm_floor` | Definition | перечисление постулатов и собранный пол |
| `sm_floor_explicit/sm_floor_size/framework_irreducible/gen_reuses_gauge` | Lemma | ★ пол = 5 названных; поколения переиспользуют L4Min |
| `rides_on_named_floor/named_floor_implies_model/sm_rides_on_named_floor` | Definition/Lemma | новый ярус честности уточняет старый rides_on_model |
| `sm_structure_just/sm_structure_grounded/sm_structure_posit_count` | Definition/Lemma | дерево обоснования заземлено, счёт листьев = 5 |
| `posit_floor` | Theorem | capstone: кирпичи + пол=5 + экономия + апгрейд яруса |

**Key lemmas (deep):**

- **`sm_floor_size`** - Объявляет, что ВСЯ структура СМ держится на ровно 5 названных постулатах ({Classic,P4} + {L1NoRep,L4Min,Reflexive}), доказано reflexivity на length списка. Содержательно это БУХГАЛТЕРИЯ (length [..]=5), а не вывод СМ; настоящая работа в цитируемых GaugePositReduction/GenerationsPositReduction (и сам вывод [2,3,1] из L-принципов — спорное брендирование проекта). _(posit-ledger, munchhausen, audit, infrastructure)_

**Uniqueness - score 1 (exposition).** Явный сосчитанный пол постулатов СМ-структуры = 5 названных; rides_on_named_floor строго честнее расплывчатого rides_on_model.
> _Caveat:_ Сами Qed — reflexivity на списках (length=5, In L4Min ...). Это аудиторская сборка, не теорема; «вся структура СМ из 5 постулатов» опирается на ПЕРЕ-БРЕНДИРОВАННЫЙ вывод gauge-группы [2,3,1] и «ровно 3 поколения» из L-принципов (флаг проекта). Честная самооценка авторов — но контент инфраструктурно-экспозиционный.

---

## #361 - `src/foundation/PredictionHonesty.v` - score 2 (methods)

**Prediction honesty ledger: failures quantified and counted (3:3:1) on a par with successes**

- **Topic.** A verdict map {Success|Failure|Open} over ToS numerical predictions; the failures are quantified (e/mu off by exactly 23x, mu/tau by ~6x) and counted equal to the successes (3 failures, 3 successes, 1 open). Discriminator: ToS gives STRUCTURE, not Yukawa VALUES.
- **Role.** Self-contained (QArith/Lqa). Audit capstone for 'weakness #3'; cross-references NumericalPredictions / ProcessFermionMassAnalysis / ProcessHiggsVEV.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lqa Lia List
- **E/R/R.** _Elements:_ рациональные расхождения (1/9 vs 1/207 = 23x; 17/3 ~ 6x; 125/4096); карта вердиктов. _Roles:_ Success = структурно и близко; Failure = юкава-значение и далеко; Open = финитизационный ящик. _Rules:_ провалы реальны, квантифицированы и сосчитаны вровень с успехами (не похоронены). _P4:_ не прячем провалы — машинный реестр квантифицирует (23x, ~6x) и считает вровень; ToS даёт СТРУКТУРУ, не юкавские ЗНАЧЕНИЯ (граница выведено/подогнано).
- **Classical counterpart.** No classical counterpart — an internal honesty ledger of ToS's own numerical predictions. The underlying numbers (sin^2 theta_W, lepton mass ratios, Higgs tree mass) are project claims, not classical results; this file audits THEM.
- **Tags.** foundation, honesty, predictions, audit, yukawa, failure-ledger, methods, over-branded-flag

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `Verdict/Pred/verdict/all_preds/is_failure/is_success/n_failures/n_success` | Definition | тип вердиктов, карта предсказаний, счётчики |
| `electron_muon_fails/electron_muon_factor_23` | Lemma | ★ e/mu: 1/9 != 1/207, ровно фактор 23 (vm_compute) |
| `muon_tau_fails/muon_tau_factor` | Lemma | ★ mu/tau: 1/3 != 1/17, фактор 17/3 (~6x) |
| `neutrino_success_value` | Lemma | ★ нейтрино (5/16)^3 = 125/4096 — успех |
| `n_failures_eq/n_success_eq` | Lemma | ★ 3 провала, 3 успеха — баланс реестра |
| `prediction_honesty` | Theorem | capstone: провалы + фактор + успех + счёт 3:3 |

**Key lemmas (deep):**

- **`electron_muon_factor_23`** - Машинно доказывает, что предсказание массы (1/3)^2=1/9 промахивается по m_e/m_mu РОВНО в 23 раза от 1/207 (vm_compute (1/9)/(1/207)=23). Редкая ЧЕСТНАЯ формализация: квантифицирует собственный ПРОВАЛ проекта вровень с успехами. Сами Qed тривиальны (Qeq/vm_compute); ценность — методологическая дисциплина не хоронить провалы. _(honesty, failure, lepton-mass, yukawa, audit)_

**Uniqueness - score 2 (methods).** Машинный честный реестр: провалы предсказаний (e/mu 23x, mu/tau ~6x) квантифицированы и сосчитаны вровень с успехами (3:3:1).
> _Caveat:_ ЯВНО флагует пере-брендированность: sin^2 theta_W=3/13 помечен Success лишь как структурный DOF-ratio, а заряж.-лептонные массы — ПРОВАЛЫ (юкава-значения). Сами леммы — арифметика Qeq. Классично: иерархии лептонов — свободные параметры СМ; новизны нет, есть дисциплина.

---

## #362 - `src/foundation/PrimalityOfOne.v` - score 1 (exposition)

**Primality of one: 1 = first distinction, 0 = absence (ToS counting reframing)**

- **Topic.** Counting from distinctions starts at 1 (one distinction), 0 is the conceptually posterior absence; successor = a new distinction; 1 is the Q unit and generates Q. The numerical order 0<1 and the conceptual order are stated as dual.
- **Role.** Builds on foundation.Distinction and foundation.AsymmetricDistinction (distinction_of). Philosophical-foundation file (File 6 of 9); supplies the 1-before-0 framing reused in narrative layers.
- **Counts.** Qed 15 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lia List PeanoNat; ToS: foundation.Distinction, foundation.AsymmetricDistinction
- **E/R/R.** _Elements:_ ToS_nat; счёт различений; 1 = первое различение, 0 = отсутствие. _Roles:_ 1 = первый акт (positive\|negative); 0 = отрицание/отсутствие, логически позднее. _Rules:_ one_is_first; zero_is_absence; succ = новое различение; 1 порождает Q. _P4:_ счёт начинается с конечного 1 различения (Element); 0 требует объяснения ОТСУТСТВИЯ — концептуально позже; каждый nat конечен.
- **Classical counterpart.** Standard arithmetic builds nat from 0 (Peano: 0 first, 1 = S 0) and treats 1 as the multiplicative unit / generator of Q. NEW only as a philosophical reframing ('1 conceptually prior to 0' from distinction); the math content is elementary nat/Q facts.
- **Tags.** foundation, distinction, nat, philosophy, rational, exposition, qed-drift

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `one_from_distinction/zero_from_no_distinction/distinction_count_from_one/add_distinction/tos_first/tos_absence` | Definition | счёт от различений, дуальные обозначения |
| `one_is_first_from_existence/zero_is_absence/first_count_is_one/zero_not_a_count` | Theorem | 1 первое, 0 не есть счёт |
| `add_distinction_increments/succ_is_new_distinction/positive_nat_is_distinction_count` | Theorem | преемник = новое различение; всякое n>=1 есть счёт |
| `one_is_unit/zero_is_additive_identity/one_generates_Q/unit_interval_bound` | Theorem | 1 = единица Q, порождает Q; границы [0,1] |
| `numerical_ordering/tos_ordering/orderings_dual` | Theorem | числовой 0<1 и концептуальный порядок дуальны |
| `primality_summary` | Theorem | синтез пяти пунктов; primality_theorem_count := 20 |

**Key lemmas (deep):**

- **`one_generates_Q`** - Каждое q:Q есть n#d (destruct на конструкторе Q) — стандартный факт, переобрамлённый как «1 порождает Q». Все Qed файла — reflexivity/lia/ring на nat и Q. Контент элементарен; единственное «содержание» — философское прочтение 1-перед-0 из акта различения, не математическое. _(distinction, nat, philosophy, reframing)_

**Uniqueness - score 1 (exposition).** Переобрамление: счёт начинается с 1 (первое различение), 0 = отсутствие (концептуально позже); 1 = единица и образующая Q.
> _Caveat:_ Стандартная арифметика строит nat ОТ 0 (Пеано); '1 порождает Q' и '1 = единица' — учебник. ДРЕЙФ: заголовок и primality_theorem_count объявляют 20 Qed, фактически 15. Вклад чисто философско-экспозиционный, математически тривиален.

---

## #363 - `src/foundation/PrimitiveTripleNT.v` - score 3 (new-framing)

**Primitive-triple number theory: pi role-limit from gcd(a,b)=1 alone**

- **Topic.** Two classical facts machine-proved over Z — (i) primitive => rel_prime a c, (ii) primitive => c odd (squares are 0/1 mod 4) — which together discharge the rel_prime hypotheses, so a primitive triple with c>=2 has a pi-incommensurable angle from gcd(a,b)=1.
- **Role.** Builds on foundation.PiAngleRoleLimit and foundation.PiAngleAllTriples (angle_role_limit_general). With PiAngleScaleInvariant completes the characterization finite-order <=> degenerate; feeds the RoleLimitTaxonomy orbit-closure stratum.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: ZArith Znumtheory Lia; ToS: foundation.PiAngleRoleLimit, foundation.PiAngleAllTriples
- **E/R/R.** _Elements:_ примитивная тройка (gcd(a,b)=1); делители a,c,b^2; чётность mod 4. _Roles:_ примитивность => rel_prime a c И c нечётно => rel_prime c (2a) — гипотезы собств.-вект. теоремы сняты. _Rules:_ (i) d\|a,c => d\|b^2 => (gcd(a,b^2)=1) d\|1; (ii) 2\|c => 4\|a^2+b^2 => (квадрат=0,1 mod4) a,b чётны => contra. _P4:_ role-limit угла теперь из ОДНОЙ примитивности (gcd(a,b)=1); + масштаб => полная характеризация конечный порядок <=> вырожденность. НЕ иррациональность pi.
- **Classical counterpart.** Classical number theory of primitive Pythagorean triples: gcd(a,b)=1 & a^2+b^2=c^2 => gcd(a,c)=1 and c odd (mod-4 parity). NEW only as the in-repo machine-checked version that discharges the coprimality hypothesis of the pi-angle eigenvector theorem from primitivity alone.
- **Tags.** foundation, pythagorean, number-theory, gcd, pi, role-limit, new-framing

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `sq_mod_4` | Lemma | квадрат n^2 = 0 mod4 (n чёт) или 1 mod4 (n нечёт) |
| `prim_c_odd` | Lemma | ★ (ii) примитивность => c нечётно (mod-4 аргумент) |
| `prim_rel_prime_ac` | Lemma | ★ (i) примитивность => gcd(a,c)=1 (общий делитель делит b^2) |
| `prim_role_limit` | Theorem | ★★ примитивная тройка c>=2 => pi-несоизмеримый угол из gcd(a,b)=1 |
| `prim_role_limit_345/prim_role_limit_5_12_13/prim_role_limit_8_15_17` | Corollary | инстансы из одной gcd-проверки (rp_compute) |
| `primitive_triple_nt` | Theorem | capstone: (i) + (ii) + role-limit из примитивности |

**Key lemmas (deep):**

- **`prim_role_limit`** - Снимает per-instance гипотезы rel_prime c a и rel_prime c (2a) теоремы angle_role_limit_general, выводя их из ОДНОЙ примитивности через классические (i)+(ii). Доказательства настоящие (Zis_gcd_intro, делимость b^2, prime_2/prime_rel_prime). Это перенос классической NT примитивных троек в Rocq — машинно новое в репо, но математически классика. _(pythagorean, number-theory, gcd, mod4, new-framing)_

**Uniqueness - score 3 (new-framing).** Снятие коприм-гипотез pi-углового role-limit из ОДНОЙ примитивности gcd(a,b)=1 (классические gcd(a,c)=1 и c нечётно), машинно-проверено.
> _Caveat:_ Оба факта (i),(ii) — стандартная NT примитивных пифагоровых троек (любой учебник теории чисел). Новизна — только их формализация в Rocq и сцепка с угловой теоремой; иррациональность pi (Нивен) НЕ доказывается, остаётся стеной.

---

## #364 - `src/foundation/PrinciplesFromLaws.v` - score 2 (methods)

**Principles from laws: P1-P4 derived from L1-L5 (irreflexivity, precedence, identity, finiteness)**

- **Topic.** P1 (hierarchy, no l<<l), P2 (criterion precedence, witness level < L), P3 (intensional identity, refl/sym/trans), P4 (finite actuality, each process stage is a finite Q) each re-derived from specific laws via Core_ERR and LawsFromDistinction.
- **Role.** Builds on foundation.Distinction, foundation.LawsFromDistinction, TheoryOfSystems_Core_ERR (Level, Criterion, System, P2_always_holds). Imported by PrinciplesToERR; core of the L->P philosophical bridge. June 2026 wave-4 vacuity rollback: P4 conjuncts were VACUOUS (exists q, R n = q); now P4 = finite-ratio BY TYPE (num#den) + discrete domain + DECIDABLE stage-equality (Qeq_dec); honest note: P4 holds by type-construction, constructive content lives in L4_witness.
- **Counts.** Qed 20 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lia; ToS: foundation.Distinction, foundation.LawsFromDistinction, TheoryOfSystems_Core_ERR
- **E/R/R.** _Elements:_ Level; Criterion L; System L; RealProcess = nat->Q. _Roles:_ каждый принцип P = роль, следующая из конкретных законов L. _Rules:_ P1 от L1+L5 (иррефлексивность); P2 от L5 (предшествование); P3 от L1+L4 (тождество); P4 от L5 (конечность). _P4:_ RealProcess: на каждом n значение R n = единичное Q (конечно); процесс ЕСТЬ последовательность, никогда не завершён в бесконечный объект.
- **Classical counterpart.** Mirrors set-theoretic well-foundedness / foundation axiom (no self-membership, Russell-blocking) and Leibniz identity of indiscernibles. NEW only as a ToS-internal derivation chain L1-L5 => P1-P4; the actual lemmas are mostly level-irreflexivity and reflexivity restatements.
- **Tags.** foundation, principles, laws, irreflexivity, identity, methods, qed-drift

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `P1_from_L1_L5/P1_no_self_membership/P1_blocks_russell/P1_concrete_L1_L2/P1_level_step/P1_asymmetry` | Theorem | P1 = иррефлексивность уровней (Рассел заблокирован) June 2026 wave-4 vacuity rollback: P4 conjuncts were VACUOUS (exists q, R n = q); now P4 = finite-ratio BY TYPE (num#den) + discrete domain + DECIDABLE stage-equality (Qeq_dec); honest note: P4 holds by type-construction, constructive content lives in L4_witness. |
| `P2_from_L5/P2_structural/P2_no_circularity` | Theorem | P2 = предшествование критерия (witness level < L) June 2026 wave-4 vacuity rollback: P4 conjuncts were VACUOUS (exists q, R n = q); now P4 = finite-ratio BY TYPE (num#den) + discrete domain + DECIDABLE stage-equality (Qeq_dec); honest note: P4 holds by type-construction, constructive content lives in L4_witness. |
| `P3_reflexivity/P3_symmetry/P3_transitivity/P3_from_L1_L4` | Theorem | P3 = интенсиональное тождество (эквивалентность) June 2026 wave-4 vacuity rollback: P4 conjuncts were VACUOUS (exists q, R n = q); now P4 = finite-ratio BY TYPE (num#den) + discrete domain + DECIDABLE stage-equality (Qeq_dec); honest note: P4 holds by type-construction, constructive content lives in L4_witness. |
| `P4_from_L5/P4_no_completed_infinity/P4_determinate_stages/P4_finite_at_each_stage/P4_nat_finite` | Theorem | P4 = конечная актуальность каждой стадии June 2026 wave-4 vacuity rollback: P4 conjuncts were VACUOUS (exists q, R n = q); now P4 = finite-ratio BY TYPE (num#den) + discrete domain + DECIDABLE stage-equality (Qeq_dec); honest note: P4 holds by type-construction, constructive content lives in L4_witness. |
| `four_principles_from_five_laws/derivation_chain` | Theorem | ★ объединение: все четыре P из конкретных L June 2026 wave-4 vacuity rollback: P4 conjuncts were VACUOUS (exists q, R n = q); now P4 = finite-ratio BY TYPE (num#den) + discrete domain + DECIDABLE stage-equality (Qeq_dec); honest note: P4 holds by type-construction, constructive content lives in L4_witness. |

**Key lemmas (deep):**

- **`four_principles_from_five_laws`** - Связывает все четыре принципа: P1 (level_lt_irrefl), P2 (P2_always_holds), P3 (refl), P4 (exists q, R n = q). Это переупаковка уже-доказанного ядра; P1 = иррефлексивность (= аксиома фундирования / блок Рассела), P3-refl и P4 тривиальны. Содержательная нагрузка лежит в Core_ERR/LawsFromDistinction, не здесь. _(principles, laws, irreflexivity, russell, infrastructure)_

**Uniqueness - score 2 (methods).** Цепь вывода P1-P4 из L1-L5: иерархия/предшествование/тождество/конечность как следствия конкретных законов.
> _Caveat:_ P1 = иррефлексивность уровней (классическая аксиома фундирования, блок Рассела); P3 — рефлексивность/симметрия/транзитивность; P4 — тривиальный destruct Q. ДРЕЙФ: STATUS-заголовок пишет 'Qed' без числа (и principles_theorem_count:=22), фактически 20 Qed. Вклад методический — переупаковка ядра.

---

## #365 - `src/foundation/PrinciplesToERR.v` - score 3 (new-framing)

**Principles <-> E/R/R: self-application is well-formed, self-membership is not**

- **Topic.** Three architectural links (F-2,F-3,F-4): E/R/R's own triad passes its well-formedness criterion (self-application, stratified), unlike Russell's self-membership; principles correspond (not derive) to E/R/R; a Distinction is typed by E/R/R at its OWN level, not embedded as a System L.
- **Role.** Builds on TheoryOfSystems_Core_ERR, foundation.Distinction, foundation.PrinciplesFromLaws, foundation.ERRWellFormedness (ERRSystem, is_well_formed, russell_system). Connecting layer only; the core is untouched (runs Print Assumptions).
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Bool PeanoNat; ToS: TheoryOfSystems_Core_ERR, foundation.Distinction, foundation.PrinciplesFromLaws, foundation.ERRWellFormedness
- **E/R/R.** _Elements:_ err_meta_system (Element/Role/Rule-категории); distinction_meta_system (две стороны, positive/negative, exclusive/exhaustive). _Roles:_ само-ПРИМЕНЕНИЕ (стратифицировано, благое) vs само-ЧЛЕНСТВО (Рассел, ill-formed) — критерий-различитель. _Rules:_ is_well_formed(E/R/R)=true, is_well_formed(russell)=false; принципы <-> E/R/R = соответствие, НЕ вывод. _P4:_ Distinction (генеративный АКТ) первичнее System L (организованный продукт); втиснуть его в System L = ИНВЕРСИЯ уровней (ошибка семейства P4); поэтому типизируем на РОДНОМ уровне.
- **Classical counterpart.** Mirrors the type-theoretic distinction between self-APPLICATION (stratified, fine) and self-MEMBERSHIP (Russell, ill-formed), and Russell's paradox. NEW only as the explicit E/R/R well-formedness discriminator and the honest refusal to fake a principles=>E/R/R entailment.
- **Tags.** foundation, err, russell, self-reference, well-formedness, architecture, new-framing

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `err_meta_system/distinction_meta_system` | Definition | триады E/R/R и Distinction как ERRSystem |
| `err_self_well_formed/self_application_not_self_membership/err_meta_has_all_three` | Theorem | ★ E/R/R само-применима и well-formed, Рассел нет |
| `principles_err_correspondence` | Theorem | ★ P1 (level) <-> no_self_reference (E/R/R) — соответствие |
| `distinction_err_well_formed/every_distinction_err_well_formed/distinction_has_all_three` | Theorem | ★ Distinction типизируется E/R/R на своём уровне |

**Key lemmas (deep):**

- **`self_application_not_self_membership`** - Главный различитель: is_well_formed(err_meta_system)=true И is_well_formed(russell_system)=false (vm_compute). E/R/R, применённая к ОПИСАНИЮ своей триады, благая (стратифицирована, нет ребра i->i), а само-членство Рассела — ill-formed. Честно отмечает (F-2), что это СООТВЕТСТВИЕ, не энтейлмент. Машинно тривиально (vm_compute), но философски аккуратно. _(err, russell, self-reference, well-formedness, new-framing)_

**Uniqueness - score 3 (new-framing).** E/R/R само-применима И P1-совместима (well-formed), в отличие от само-членства Рассела; критерий is_well_formed — точный различитель.
> _Caveat:_ Различие само-применение/само-членство — классика теории типов (стратификация vs Рассел). Qed — vm_compute на конечной булевой решётке. ЧЕСТНО само отказывается выдавать вывод E/R/R из принципов (F-2: только соответствие). Вклад — обрамление, не теорема.

---

## #366 - `src/foundation/ProcessMetricComplete.v` - score 3 (new-framing)

**Process metric + stagewise completeness: the limit is the diagonal process, not an object**

- **Topic.** A P4-compatible metric d_N(R,S)=sum_{k<N}|R(k)-S(k)| on RealProcess; process-Cauchy implies each stage is Cauchy in Q; the diagonal process k|->seq(k)(k) is the stagewise limit. Completeness as a process theorem, not an R-axiom.
- **Role.** Builds on process.ProcessCore (RealProcess). Imported by ProcessP4Synthesis; the metric/completeness substrate for the P4 process-analysis layer.
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: process.ProcessCore
- **E/R/R.** _Elements:_ stage_diff; proc_dist_N; diagonal_process. _Roles:_ RealProcess со стадийной дистанцией = P4-полное пространство; диагональ = предел-процесс. _Rules:_ d_N(R,S) = sum \|R(k)-S(k)\| (конечная сумма); полнота через диагональ. _P4:_ d_N — АКТУАЛЬНАЯ дистанция на стадии N; нет завершённого d(R,S); предел = диагональный ПРОЦЕСС (nat->Q), всегда конечен на каждой стадии.
- **Classical counterpart.** Mirrors the completeness of R (every Cauchy sequence converges) and the metric/diagonal construction; NEW only as a P4-compatible STAGEWISE reformulation: the 'limit' is the diagonal PROCESS (nat->Q), no completed object, and convergence is per-stage not uniform.
- **Tags.** foundation, process, metric, completeness, diagonal, p4, new-framing, qed-drift

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `stage_diff/proc_dist_N/is_process_cauchy/diagonal_process` | Definition | стадийная дистанция, кумулятивная метрика, Коши, диагональ |
| `stage_diff_nonneg/stage_diff_self/proc_dist_N_self/proc_dist_N_nonneg/proc_dist_mono` | Lemma | свойства метрики: неотриц., self=0, монотонность |
| `stagewise_cauchy` | Lemma | ★ процесс-Коши => каждая стадия k Коши в Q |
| `process_completeness` | Theorem | ★★ диагональ приближает каждое стадийное значение |
| `diagonal_is_valid_process/process_metric_synthesis` | Lemma/Theorem | диагональ есть валидный процесс; синтез метрики+полноты |

**Key lemmas (deep):**

- **`process_completeness`** - P4-полнота: процесс-Коши последовательность сходится СТАДИЙНО к диагональному процессу k\|->seq(k)(k); сходимость per-stage (фиксируем k), НЕ равномерно. Это честная замена аксиомы полноты R теоремой над nat->Q. Доказательство опирается на stagewise_cauchy. Математически — диагональный приём (известен), но онтологически переформулирован: предел = процесс, не объект. _(completeness, diagonal, process, p4, new-framing)_

**Uniqueness - score 3 (new-framing).** P4-полнота: предел Коши-последовательности процессов = диагональный ПРОЦЕСС (nat->Q), стадийная сходимость без завершённого объекта.
> _Caveat:_ Полнота R и диагональная конструкция — классика анализа; здесь только онтологическая переформулировка (процесс вместо объекта, per-stage вместо uniform). ДРЕЙФ: заголовок объявляет 12 Qed, фактически 9. Сильная сторона — contrastive: метрика и сходимость, но БЕЗ R и без завершённой бесконечности.

---

## #367 - `src/foundation/ProcessP4Synthesis.v` - score 3 (new-framing)

**Grand synthesis: P4 prohibits completed infinity; process space is complete**

- **Topic.** Three pillars: (1) completed infinity contradicts P4, (2) potential infinity exists via processes, (3) process space is complete (diagonal). Plus process_equiv as the real-number equality, and GenProcess=nat->A as the coinduction-free stream encoding (finite prefixes).
- **Role.** Builds on process.ProcessCore, foundation.P4CompletedInfinity (completed_inf_contradicts_P4, potential_inf_exists), foundation.ProcessMetricComplete. Capstone of the P4->process-mathematics arc. June 2026 wave-4 vacuity rollback: process_finite_at_stage was exists q, R n = q (vacuous) -> finite ratio num#den BY TYPE.
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia List Lqa; ToS: process.ProcessCore, foundation.P4CompletedInfinity, foundation.ProcessMetricComplete
- **E/R/R.** _Elements:_ RealProcess; const_process; diagonal_process; GenProcess A = nat->A. _Roles:_ P4 (конечность) -> процесс-онтология -> метрика -> полнота; бесконечность = процесс (потенциальная), не объект. _Rules:_ completed_inf_contradicts_P4; potential_inf_exists; полнота диагональю; gp_prefix конечен. _P4:_ P4 ЗАПРЕЩАЕТ завершённые бесконечности (не просто избегает); процесс = потенциальная бесконечность; каждый префикс конечен; nat->A кодирует наблюдения без коиндукции.
- **Classical counterpart.** Mirrors the Cauchy-completion construction of R and the potential/actual infinity distinction (Aristotle/Brouwer). NEW only as the explicit synthesis 'P4 prohibits completed infinity & process space is complete' — the math (Cauchy, metric, prefixes) is standard.
- **Tags.** foundation, p4, process, infinity, completeness, ontology, new-framing, qed-drift

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `process_finite_at_stage/const_process_compatible` | Lemma | стадия конечна; константы Коши June 2026 wave-4 vacuity rollback: process_finite_at_stage was exists q, R n = q (vacuous) -> finite ratio num#den BY TYPE. |
| `pillar1_prohibition/pillar2_potential/pillar3_completeness` | Theorem | ★ три столпа: запрет / потенциальная / полнота June 2026 wave-4 vacuity rollback: process_finite_at_stage was exists q, R n = q (vacuous) -> finite ratio num#den BY TYPE. |
| `process_equiv/process_equiv_refl/const_equiv` | Definition/Lemma | эквивалентность процессов = равенство действ. чисел June 2026 wave-4 vacuity rollback: process_finite_at_stage was exists q, R n = q (vacuous) -> finite ratio num#den BY TYPE. |
| `GenProcess/gp_observe/gp_prefix/gp_prefix_length` | Definition/Lemma | nat->A поток без коиндукции; префикс конечен June 2026 wave-4 vacuity rollback: process_finite_at_stage was exists q, R n = q (vacuous) -> finite ratio num#den BY TYPE. |
| `process_p4_grand_synthesis` | Theorem | ★ grand: запрет + потенц. + метрика + полнота + префикс June 2026 wave-4 vacuity rollback: process_finite_at_stage was exists q, R n = q (vacuous) -> finite ratio num#den BY TYPE. |

**Key lemmas (deep):**

- **`process_p4_grand_synthesis`** - Объединяет шесть фактов в один тезис «P4 -> процесс-математика = ПОЛНАЯ рамка»: запрет завершённой бесконечности, потенциальная бесконечность, метрика, полнота, конечные префиксы. Честно перечисляет, что НЕ доказано (весь классический анализ, эквивалентность Дедекинду). Содержательно — агрегатор уже-доказанного из ProcessMetricComplete/P4CompletedInfinity; ценность в формулировке программы. _(p4, process, infinity, completeness, synthesis)_

**Uniqueness - score 3 (new-framing).** Синтез: P4 ЗАПРЕЩАЕТ завершённую бесконечность, процессы дают потенциальную, пространство процессов полно (диагональ) — единая рамка nat->Q.
> _Caveat:_ Конструкция R через Коши-пополнение и различие потенциальной/актуальной бесконечности — классика (Аристотель/Брауэр/анализ). ДРЕЙФ: заголовок 10 Qed, фактически 9. Тезис «то же, другая онтология» честно перечисляет несделанное; вклад — обрамление-программа, не новые теоремы.

---

## #368 - `src/foundation/QuantizationSynthesis.v` - score 2 (methods)

**Quantization synthesis: discreteness from logical indivisibility (NOT hbar)**

- **Topic.** Chain distinction-indivisible -> count=nat -> discrete process domain -> quantization. Packages: atom unsplittable, N^2-1 gauge dimensions integer, minimum nonzero = 1 (mass-gap-as-logical-minimum). Explicitly does NOT derive hbar or Hamiltonian-dependent level values.
- **Role.** Builds on foundation.Distinction, foundation.IndivisibleDistinction, foundation.LogicalAtom (logical_atom, atom_is_minimum, atom_unsplittable). Summary/synthesis file for the indivisibility-quantization arc. June 2026 vacuity rollback: two VACUOUS exists-conjuncts replaced by real content (gauge-dimension ladder strictly increasing; integer/half-integer parity dichotomy); physical_consequences RENAMED arithmetic_consequences; NEW spacing_underdetermined_by_discreteness — discreteness does NOT fix the step/hbar, the old prose gap is now a theorem (two discrete spectra, steps 1 vs 2).
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Lia QArith; ToS: foundation.Distinction, foundation.IndivisibleDistinction, foundation.LogicalAtom
- **E/R/R.** _Elements:_ logical_atom; различение (positive/negative); счёт = nat. _Roles:_ неделимость различения = роль, порождающая дискретность счёта. _Rules:_ неделимо -> nat -> дискретный домен -> квантование (логическое, не физическое). _P4:_ минимум ненулевого = 1 различение (Element); даёт ДИСКРЕТНОСТЬ; физическое квантование (hbar, уровни) требует физики — честно не выводится.
- **Classical counterpart.** No specific classical result — a chain from logical indivisibility to discreteness. The cited consequences (SU(2)=3, SU(3)=8 generators, mass gap, half-integer spin) are standard physics; the file HONESTLY disclaims deriving hbar or specific levels.
- **Tags.** foundation, quantization, indivisibility, gauge, mass-gap, methods, qed-drift, over-branded-flag

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `logical_quantization` | Theorem | различения неделимы; атом; целые gauge-размерности; минимум 1 |
| `quantization_chain` | Theorem | ★ цепь: различение -> неделимо -> nat -> домен процесса |
| `mass_gap_logical` | Theorem | ★ масс-щель как логический минимум (atom_is_minimum) |
| `physical_consequences` | Theorem | SU(2)=3, SU(3)=8, спин=sides/2, щель=1 |
| `indivisibility_grand_synthesis` | Theorem | ★ grand: основание + неделимость + неразбиваемость + целый gauge |

**Key lemmas (deep):**

- **`indivisibility_grand_synthesis`** - Связывает основание различения, неделимость (n>0 => n>=1), неразбиваемость атома и целочисленность gauge (3*3-1=8) в один тезис. Все Qed — lia + цитаты из LogicalAtom. ЧЕСТНО заявляет, что выводит ДИСКРЕТНОСТЬ, а не hbar/уровни — но «SU(2)=3, SU(3)=8, спин полуцелый из неделимости» — пере-брендирование: dim su(N)=N^2-1 и спин — стандартная теория представлений, не следствие распада различения. _(quantization, indivisibility, gauge, mass-gap, over-branded)_

**Uniqueness - score 2 (methods).** Цепь логической квантизации: неделимость различения -> nat-домен -> дискретность; масс-щель как логический минимум 1.
> _Caveat:_ ДРЕЙФ: заголовок объявляет 10 Qed, фактически 5. ПЕРЕ-БРЕНДИРОВАНО: 'почему gauge целочислен / spin полуцелый / SU(2)=3, SU(3)=8 из неделимости' — стандартная теория представлений (dim su(N)=N^2-1), а Qed — просто lia (3*3-1=8). Файл сам честно отрицает вывод hbar. Вклад методический: связь неделимость->дискретность.

---

## #369 - `src/foundation/QuantumGravityCategoryError.v` - score 3 (new-framing)

**Quantum gravity = quantizing the Rule; non-renormalizability = a P1 level-inversion category error**

- **Topic.** Element<Role<Rule with irreflexivity (P1); a gauge field (Role) is quantizable on the spacetime Rule-background, but 'gravity (Rule) as a gauge field' needs Rule<Rule (forbidden). The category error IS P1 irreflexivity; its dimensional shadow is coupling dim (gauge 0 vs gravity -2) from rank-1 vs rank-2 sources.
- **Role.** Self-contained (Stdlib only). Part of the 'gravity = Rule-object' experimental thread; pairs with RicciContraction / RiemannFromConnection (the indexed gravity tensors).
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith Lia ZArith
- **E/R/R.** _Elements:_ источники: скалярный заряд (ранг-0), ток j_m (ранг-1), тензор T_mn (ранг-2). _Roles:_ калибровочное поле = Роль-поле (уровень Role), квантуется на фоне (Rule) — Role<Rule OK. _Rules:_ пространство-время/гравитация = Rule; 'гравитация-как-калибровка' = Rule на уровне Role => Rule<Rule = инверсия, запрет P1. _P4:_ категорная ошибка <=> ~(Rule<Rule) = та же иррефлексивность, что блокирует Рассела/Кантора. Правильно (P4): квантовать Правило = конечный процесс (решётка), без фона/расходимостей.
- **Classical counterpart.** Dyson power-counting (renormalizable iff coupling mass-dimension >= 0; gauge dim 0, Newton's G dim -2) is textbook QFT. NEW only as the framing: non-renormalizability = a Rule-as-Role level inversion blocked by the SAME P1 irreflexivity as Russell/Cantor.
- **Tags.** foundation, quantum-gravity, renormalization, category-error, irreflexivity, new-framing

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `ERRLevel/rank/below/quantizable_on/gauge_field/spacetime/gravity/renormalizable/dim_gauge/dim_gravity/source_rank` | Definition | уровни E/R/R, отношение below, квантуемость, размерности |
| `h_ER/h_RR/h_ERR/below_irrefl` | Lemma | иерархия Element<Role<Rule; P1-иррефлексивность |
| `gauge_quantizable/gravity_as_role_illformed` | Lemma | ★ калибровка well-formed; гравитация-как-калибровка нет |
| `category_error_is_irreflexivity` | Lemma | ★★ кат. ошибка <=> ~(Rule<Rule) (блок Рассела/Кантора) |
| `gauge_renormalizable/gravity_nonrenormalizable/gravity_source_rank2/gauge_source_rank1` | Lemma | размерная тень: dim 0 vs -2; ранг-2 vs ранг-1 источник |
| `quantum_gravity_is_rule_quantization` | Theorem | capstone: иерархия + P1 + калибровка/гравитация + размерности |

**Key lemmas (deep):**

- **`category_error_is_irreflexivity`** - Заявляет: '(~ quantizable_on gravity spacetime) <-> (~ below LRule LRule)' (tauto) — т.е. неперенормируемость гравитации СТРУКТУРНО = та же P1-иррефлексивность, что блокирует Рассела/Кантора. Само доказательство тривиально (определения совпадают), но ОБРАМЛЕНИЕ содержательно: связывает неперенормируемость с путаницей уровней Rule/Role. Точные размерности (gauge 0, G -2) — стандартный power-counting (lia). _(quantum-gravity, renormalization, irreflexivity, category-error, new-framing)_

**Uniqueness - score 3 (new-framing).** Структурная причина неперенормируемости гравитации = инверсия уровней Rule/Role (та же P1-иррефлексивность, что блокирует парадоксы); размерная тень -2 из ранг-2 источника.
> _Caveat:_ Power-counting Дайсона (dim связи >=0 <=> перенормируемо; gauge 0, G -2) — учебник КТП; ранг-2 T_mn vs ранг-1 j_m тоже. Qed — lia/tauto на определениях. Вклад чисто КОНЦЕПТУАЛЬНЫЙ (обрамление через E/R/R-уровни), не новая физика; помечено самим автором как 'новое обрамление известного'.

---

## #370 - `src/foundation/QubitThreeFormulas.v` - score 2 (methods)

**Qubit as three E/R/R formulas over Q: finite spectrum, Pauli rules, Born rule**

- **Topic.** Two-level system in three-formula form: ground/excited (E), binary level spectrum with gap E (R-spectrum), Pauli X/Z involutions that anticommute (R-rules), and the Born rule on a rational (3/5,4/5) superposition. Framed as the structural complement of the SHO (finite vs countable, nonabelian vs abelian).
- **Role.** Self-contained (QArith/Lqa); rational superposition derived in stdlib/PythagoreanTriples. Part of the E/R/R single-system three-formula physics layer; complements SHOThreeFormulas/PhotonThreeFormulas.
- **Counts.** Qed 32 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs ZArith List PeanoNat Lia Lqa
- **E/R/R.** _Elements:_ QubitState (пара амплитуд Q); ground/excited; phi_rational=(3/5,4/5). _Roles:_ бинарный спектр (две роли-уровня) с щелью E; оператор Z = фаза (только при конечном спектре). _Rules:_ Pauli X/Z инволютивны и АНТИкоммутируют; Born = проекция на R-спектр; норма сохраняется. _P4:_ конечный (2-уровневый) спектр над Q (Element); нормировка в Q требует пифагоровой тройки; некоммутативность {X,Z}=0 = прямое следствие конечности спектра.
- **Classical counterpart.** Standard two-level quantum system: Pauli X/Z algebra, anticommutation, Born rule, finite spectrum. NEW only as the E/R/R three-formula re-derivation over Q (with Pythagorean-triple rational superposition) and the SHO-complementarity framing.
- **Tags.** foundation, qubit, pauli, born-rule, three-formula, err, methods, qed-drift

**Lemmas (8):**

| name | kind | role |
|---|---|---|
| `QubitState/qubit_amp0/qubit_amp1/qstate_eq/qubit_norm_sq/qubit_normalized/ground/excited` | Definition | состояние, норма, базис |
| `qstate_eq_refl/ground_norm_one/ground_normalized/excited_norm_one/excited_normalized/ground_ne_excited` | Theorem | E-формула: базисные состояния нормированы и различны |
| `qubit_level/qubit_gap/qubit_level_0_value/qubit_level_1_value/qubit_only_two_levels/qubit_ground_minimum` | Definition/Theorem | ★ R-спектр: ровно два уровня, щель E |
| `pauli_X/pauli_Z/qstate_add/pauli_X_involutive/pauli_Z_involutive/pauli_X_ground/_excited/pauli_Z_ground/_excited` | Definition/Theorem | Pauli-операторы, инволютивность, действие на базис |
| `pauli_XZ_anticommute/pauli_X_preserves_norm/pauli_Z_preserves_norm` | Theorem | ★ X,Z антикоммутируют; сохраняют норму |
| `born_qubit/born_ground_certain/born_ground_never_excited/phi_rational/phi_rational_normalized/born_phi_splits/born_total_one` | Definition/Theorem | ★ правило Борна на рациональной суперпозиции, сумма=1 |
| `qubit_expected_energy/qubit_expected_on_ground/qubit_expected_on_phi` | Definition/Theorem | ожидаемая энергия |
| `qubit_three_formulas/qubit_spectrum_is_finite/qubit_rules_non_abelian/qubit_can_have_zero_ground/qubit_complete` | Theorem | ★ три формулы + комплементарность с SHO |

**Key lemmas (deep):**

- **`pauli_XZ_anticommute`** - Антикоммутатор XZ(s)+ZX(s)=(0,0) для всякого состояния (ring). Файл наблюдает: некоммутативность Pauli — НЕ постулат, а следствие конечного (2-уровневого) спектра. Это аккуратное переобрамление, но сами факты (X^2=Z^2=id, {X,Z}=0, Born, нормировка через пифагорову (3/5,4/5)) — стандартная КМ кубита, доказаны ring/lra/vm_compute. _(qubit, pauli, anticommute, born, err)_

**Uniqueness - score 2 (methods).** Кубит в E/R/R-форме трёх формул над Q: конечный спектр, инволюции Pauli, антикоммутация и Борн на рациональной (3/5,4/5) суперпозиции; комплементарность с SHO.
> _Caveat:_ Алгебра Pauli, антикоммутация, правило Борна, конечный спектр — учебная КМ. ДРЕЙФ: заголовок объявляет 28 Qed, фактически 32. Наблюдение 'нормировка в Q требует пифагоровой тройки' — приятно, но элементарно. Вклад методический: переобрамление, не новая физика.

---

## #371 - `src/foundation/RationalRootEigenvalue.v` - score 3 (new-framing)

**Rational root theorem in the eigenvalue framing: a rational eigenvalue of an integer matrix is integer**

- **Topic.** Generalizes the 2x2 'discriminant a perfect square' eigenvalue criterion to n x n via the rational root theorem: a rational eigenvalue p/q satisfying a pure characteristic equation lambda^(k+1)=m (companion of x^(k+1)-m) is an integer (q=1). The 2x2 (sqrt2) and degree-3 (cbrt2) are the k=1,2 instances.
- **Role.** Builds on algebra.RationalRootTest (nth_root_integer_or_irrational, coprime_div_pow_unit, the general Gauss lemma). The n x n frontier of the eigenvalue-rationality criterion; honestly notes the full arbitrary-monic case needs heavier matrix machinery.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: ZArith Lia Znumtheory; ToS: algebra.RationalRootTest
- **E/R/R.** _Elements:_ целочисл. матрица; char-уравнение lambda^(k+1)=m (companion); рациональное собств. значение p/q. _Roles:_ рациональное собств. значение <=> рациональный корень монического char-полинома (критерий = RRT). _Rules:_ чистый корень lambda^(k+1)=m в низших членах => q=1 (целое), через лемму Гаусса (coprime_div_pow_unit). _P4:_ рациональное собств. значение => ЦЕЛОЕ (делит det) => разрешимо (конечно много кандидатов); 2x2 (sqrt2) и куб (cbrt2) = инстансы k=1,2.
- **Classical counterpart.** The Rational Root Theorem / Gauss's lemma (a rational root of a monic integer polynomial is an integer); irrationality of sqrt2 and cbrt2 (Delian doubling). NEW only as the eigenvalue framing (companion matrix, pure root) and the in-repo assembly.
- **Tags.** foundation, rational-root, gauss-lemma, eigenvalue, irrationality, new-framing, qed-drift

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `pure_root_eigenvalue_integer` | Theorem | ★ рациональное собств. значение pure char-уравнения = целое (q=1) |
| `sqrt2_eigenvalue_integer` | Corollary | ★ 2x2 (x^2-2, Delta=8): рациональный корень = целый => sqrt2 не in Q |
| `cbrt2_eigenvalue_integer` | Corollary | ★ степень-3 (x^3-2, Делийская): рациональный корень = целый => cbrt2 не in Q |
| `no_integer_sqrt2` | Lemma | нет целого m с m^2=2 (корень реально проваливается) |
| `rational_root_eigenvalue_criterion` | Theorem | capstone: критерий + 2x2 + куб + нет sqrt2 |

**Key lemmas (deep):**

- **`pure_root_eigenvalue_integer`** - Применяет общую лемму Гаусса RationalRootTest в собственно-значной рамке: рациональное собств. значение companion-матрицы x^(k+1)-m целое (q=1). Это переупаковка nth_root_integer_or_irrational (exact); содержательная работа в RationalRootTest. Честно отмечает, что полный произвольно-монический n x n требует вычисления char-полинома (не построено). Обобщает 2x2 Delta-критерий до 'целый корень char-полинома'. _(rational-root, gauss-lemma, eigenvalue, companion, new-framing)_

**Uniqueness - score 3 (new-framing).** Критерий рациональности собств. значений n x n = теорема о рациональном корне (движок Гаусса), pure/companion-форма; 2x2 Delta-квадрат и Делийская cbrt2 как инстансы.
> _Caveat:_ Теорема о рациональном корне / лемма Гаусса и иррациональность sqrt2, cbrt2 — классика. ДРЕЙФ: заголовок 6 Qed, фактически 5. Движок (coprime_div_pow_unit) в algebra.RationalRootTest, здесь exact-переупаковка. Полный произвольно-монический n x n НЕ построен (нужна char-полином-машинерия). Вклад — обрамление.

---

## #372 - `src/foundation/RealCouplingSpectrum.v` - score 4 (synthesis+observation)

**Real coupling spectrum: the YM transfer matrix is Element-side; the mass-gap wall is continuum, not spectral**

- **Topic.** Applies the inter-level disc-criterion to the REAL repo Yang-Mills transfer matrix T(beta): disc = (2-beta/4)^2 is a perfect square for all beta, so the spectrum is rational (Element) identically; the two modes 2-beta/8, beta/8 and gap 2-beta/4 are exact. Contrast: golden [[0,1],[1,1]] has disc 5 (surd). The mass-gap wall is thus located at the continuum closure.
- **Role.** Self-contained (QArith/Lqa); disc-criterion replicated from foundation.HierarchyLaplacian; matrix from gauge/TransferMatrix.v. Part of the hierarchy/cascade direction (N1); locates (does not cross) the mass-gap wall.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lia Lqa
- **E/R/R.** _Elements:_ элементы 1, 1-beta/8 in Q настоящей transfer-матрицы; disc; две моды. _Roles:_ собств. векторы (1,1)/(1,-1) = две моды связи; щель = разделение ролей; beta = сила связи; disc = ручка Element/role-limit. _Rules:_ рацион. мода <=> disc полный квадрат; disc(T(beta))=(2-beta/4)^2 (квадрат всегда) => Element-спектр; стена = континуум-замыкание, не спектр. _P4:_ спектр настоящей gauge-матрицы Element при ЛЮБОМ рацион. beta (конечно, точно); role-limit НЕ в спектре, а в континуум-замыкании beta->beta_c. Relocate, not cross.
- **Classical counterpart.** Standard 2x2 eigenvalue theory (rational eigenvalues iff discriminant is a perfect square) and the lattice transfer-matrix spectrum. NEW only as the OBSERVATION that the YM mass-gap wall is the continuum closure, NOT a spectral surd — a classification, not a continuum-limit theorem.
- **Tags.** foundation, yang-mills, transfer-matrix, discriminant, mass-gap, cascade, synthesis

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `cl_tr/cl_det/cl_disc/is_eigenvalue/is_square_Q/tm_a/tm_b/tm_c/tm_d/tm_mass_gap/ym_wall_location` | Definition | disc-критерий, реальная transfer-матрица, локация стены |
| `cl_disc_eq/spectrum_rational_iff_disc_square` | Lemma/Theorem | ★ рациональная мода <=> disc — квадрат |
| `transfer_disc_is_square/transfer_spectrum_element` | Theorem | ★ disc(T(beta)) = квадрат для всех beta => Element-спектр |
| `transfer_mode_ground/transfer_mode_excited/tm_mass_gap_value` | Lemma | две явные рациональные моды и щель 2-beta/4 |
| `golden_coupling_disc` | Example | контраст: disc([[0,1],[1,1]])=5 (сурд, role-limit) |
| `wall_not_spectral` | Lemma | ★ стена щели масс = континуум-замыкание, не спектральный сурд |
| `real_coupling_spectrum` | Theorem | capstone: квадрат + моды + щель + контраст + локация стены |

**Key lemmas (deep):**

- **`transfer_disc_is_square`** - На НАСТОЯЩЕЙ репо-матрице gauge/TransferMatrix.v disc=(2-beta/4)^2 — полный квадрат при любом beta (ring), значит спектр рационален тождественно. Наблюдение (синтез+observation): спектральная стена (сурд собств. значение) ОТСУТСТВУЕТ, а реальная стена щели масс — в континуумном замыкании beta->beta_c. Это РАЗДЕЛЯЕТ две легко смешиваемые стены и ЛОКАЛИЗУЕТ (не пересекает) нужную. Честно: континуум-claim — классификационный ТЕГ, не теорема предела. _(yang-mills, transfer-matrix, discriminant, mass-gap, synthesis)_

**Uniqueness - score 4 (synthesis+observation).** Реальная YM transfer-матрица Element-side (disc квадрат при всех beta); стена щели масс НЕ спектральна (сурд отсутствует), а лежит в континуумном замыкании — две стены разделены, нужная локализована.
> _Caveat:_ Критерий 'рациональные собств. значения <=> disc — квадрат' — стандартная алгебра 2x2; disc=5 для golden — известно (Sqrt5Irrational). Сами Qed — ring/vm_compute. Континуум-стена записана как ТЕГ (ym_wall_location), НЕ доказана теоремой предела (relocate, not cross). Новизна — наблюдение/классификация на реальной матрице, не новый результат.

---

## #373 - `src/foundation/RelativityFoundation.v` - score 1 (exposition)

**Relativity foundation (toy): simultaneity = shared distinction, Minkowski interval over Z**

- **Topic.** Observers as distinction-history lists; simultaneity = sharing a distinction; causal connection dx<=dt; the Minkowski interval interval(dt,dx)=dt^2-dx^2 over Z gives timelike/spacelike/lightlike examples. A small discrete sketch, not a derivation of Lorentz invariance.
- **Role.** Self-contained (QArith/ZArith/List). Early sketch (old header style, no STATUS block); illustrative E/R/R reading of relativity. Not depended upon by the rigorous layers.
- **Counts.** Qed 14 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lia ZArith List Bool Lqa
- **E/R/R.** _Elements:_ ObsSeq (список различений); rhas; interval. _Roles:_ разные наблюдатели = разные истории; одновременность = общее различение (shared distinction). _Rules:_ causally_connected dx<=dt; interval = dt^2-dx^2; сигнатура (+,-) из достижимости. _P4:_ наблюдатель = конечная последовательность различений (Element); одновременность как общий конечный элемент; интервал на конкретных целых.
- **Classical counterpart.** Minkowski spacetime: simultaneity, the (+,-) interval ds^2 = dt^2 - dx^2, light cone / causal structure. NEW only as a toy 'observer = distinction-sequence' discrete model where simultaneity = shared distinction and the signature emerges from reachability.
- **Tags.** foundation, relativity, simultaneity, minkowski, toy, exposition, no-status-header

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `ObsSeq/rhas/O1_K1../O2_K3/simultaneous/graph_distance/causally_connected/interval` | Definition | истории наблюдателей, одновременность, причинность, интервал |
| `different_K1/different_K2/different_K3` | Lemma | истории наблюдателей различны |
| `K1_not_simultaneous/K2_simultaneous/cross_simultaneous` | Lemma | ★ одновременность = общее различение |
| `causal_32/not_causal_13/lightlike_22` | Lemma | причинная связь dx<=dt |
| `timelike_ex/spacelike_ex/lightlike_ex/timelike_51/spacelike_14` | Lemma | интервал: time/space/lightlike примеры (dt^2-dx^2) |

**Key lemmas (deep):**

- **`K2_simultaneous`** - Одновременность определена как СУЩЕСТВОВАНИЕ общего различения (exists d, rhas s1 d /\ rhas s2 d) — операциональное E/R/R-прочтение относительности одновременности. Все Qed — discriminate/simpl/lia на конкретных списках и целых. Это эскиз-иллюстрация, не вывод инвариантности Лоренца; сигнатура (+,-) ПОСТУЛИРОВАНА определением interval, не выведена. _(relativity, simultaneity, minkowski, toy, exposition)_

**Uniqueness - score 1 (exposition).** Игрушечная дискретная модель: наблюдатель = последовательность различений, одновременность = общее различение, интервал Минковского dt^2-dx^2 над Z.
> _Caveat:_ Пространство Минковского, относительность одновременности и сигнатура (+,-) — учебник СТО. НЕТ STATUS-заголовка (старый стиль). Сигнатура (+,-) задана определением interval, не выведена из достижимости; инвариантность Лоренца не затрагивается. Чистая иллюстрация на конкретных целых.

---

## #374 - `src/foundation/RGCascadeReal.v` - score 3 (new-framing)

**RG cascade (real multi-step): t'=t^2 decimation, sub-critical contracts (Element), super-critical runs away (role-limit)**

- **Topic.** A genuine block-spin decimation map rg_step t = t^2, iterated to t^(2^n); fixed points 0 (stable) and 1 (unstable critical); sub-critical [0,1] contracts toward 0 (Element), super-critical t>=1 runs away (role-limit/continuum). The honest fix to ExactRGProcess's 1/N-rescaling fake.
- **Role.** Self-contained (QArith/Lqa). The RG-arena instance of scale-flow, parallel to ShellCascadeNS; consumed by ScaleHierarchySynthesis as one of the two unified arenas.
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lia Lqa
- **E/R/R.** _Elements:_ рациональная связь t; конечные итераты rg_iterate t n; две неподвижные точки. _Roles:_ РГ-ступени n; бегущая связь t_n; критическая точка t=1 (граница). _Rules:_ децимация rg_step t = t^2 (две связи -> одна); докритич. сжимается (Element), надкритич. убегает (role-limit); t=1 неподвижная граница. _P4:_ РГ-поток = процесс; докритический = Element (сжимается к неподв. точке), надкритический = role-limit (убегает, континуум). НАСТОЯЩИЙ многошаг (пересчёт каждый рунг) = honesty-фикс ExactRGProcess.
- **Classical counterpart.** Block-spin / real-space renormalization-group decimation and its fixed-point flow (trivial/critical fixed points, sub/super-critical basins) is standard statistical physics. NEW only as a genuinely multi-step Q model (t'=t^2) contrasting the repo's faked 1/N rescaling (ExactRGProcess), with the Element/role-limit boundary at t=1.
- **Tags.** foundation, renormalization, block-spin, cascade, fixed-point, honesty-fix, new-framing

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `rg_step/rg_iterate` | Definition | карта децимации t^2 и итерация t^(2^n) |
| `rg_iterate_S/rg_fixed_0/rg_fixed_1` | Lemma | ★ многошаг t_{n+1}=t_n^2; неподвижные 0,1 |
| `rg_iterate_in_unit/rg_sub_decreasing` | Lemma/Theorem | ★ докритический поток сжимается в [0,1] (Element) |
| `rg_iterate_ge_1/rg_super_increasing` | Lemma/Theorem | ★ надкритический поток убегает >=1 (role-limit) |
| `rg_subcritical_decays/rg_supercritical_grows/rg_h1_disjoint` | Example/Lemma | 1/2->1/256; 2->256; две стороны границы дизъюнктны |
| `rg_cascade_real` | Theorem | capstone: многошаг + неподв. + сжатие + убегание |

**Key lemmas (deep):**

- **`rg_sub_decreasing`** - Докритический поток (0<=t<=1) НЕ возрастает: rg_iterate t (S n) <= rg_iterate t n (Qmult_le_compat_r на инвариантном [0,1]). Содержательная честность файла — он явно ФИКСИТ обнаруженную подделку: gauge/ExactRGProcess.v делал gap/N (1/N-перешкалирование фиксированного 2x2 gap), без ренормгрупп-контента; здесь связь ПЕРЕСЧИТЫВАЕТСЯ каждый рунг (t^2). Математика элементарна (монотонность t^2 на [0,1] и [1,inf)). _(renormalization, block-spin, fixed-point, honesty-fix, methods)_

**Uniqueness - score 3 (new-framing).** Настоящий многошаговый РГ-поток над Q (t'=t^2, пересчёт каждый рунг) с границей Element/role-limit при t=1 — честный фикс поддельного 1/N-перешкалирования ExactRGProcess.
> _Caveat:_ Блок-спин децимация и её неподвижные точки (тривиальная/критическая, докритич./надкритич. бассейны) — стандартная статфизика; t'=t^2 — безразмерная игрушка, НЕ порт Schur-комплемента BlockDecimation1D, континуум не берётся (= role-limit). Qed элементарны (монотонность t^2). Ценность — методическая честность (фикс подделки).

---

## #375 - `src/foundation/RicciContraction.v` - score 3 (new-framing)

**Ricci contraction: Riemann->Ricci->scalar->Einstein tensor, trace-reversal, vacuum=Ricci-flat over Q**

- **Topic.** Index-contraction chain over Q with a diagonal metric (D=4): Ricci from Riemann (contract indices 1&3), Ricci scalar, Einstein tensor G=R-(1/2)gR; derives g^mn g_mn = 4, trace-reversal tr(G)=-R, G symmetric (Sym^2), and vacuum G=0 implies Ricci-flat. The Einstein tensor as a DERIVED indexed object.
- **Role.** Self-contained (QArith/Lqa); step 4 of the field-level gravity lift. Takes Riemann as given; RiemannFromConnection (step 5) derives it from the metric. Pairs with QuantumGravityCategoryError in the 'gravity = Rule' thread.
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lqa
- **E/R/R.** _Elements:_ компоненты тензора по индексам (числовые носители кривизны: Riem, Ricci, скаляр). _Roles:_ индексы = направления/позиции (L5); свёртка = спаривание Ролей (сумма по повторяющемуся индексу). _Rules:_ свёртки Riemann->Ricci->скаляр; G=R-(1/2)gR (trace-reversal); tr(G)=-R (D=4); вакуум G=0<->Ricci-flat. _P4:_ свёртка = отождествление двух Роль-позиций и суммирование без остатка; G_mn — выводимый индексный объект, не Sym^2-схема. Модель над Q (диагональная метрика D=4); Riemann как данность (символы Кристоффеля не выведены — шаг 5).
- **Classical counterpart.** Standard differential geometry: Riemann->Ricci contraction, Ricci scalar, the Einstein tensor G=R-(1/2)gR, trace-reversal tr(G)=-R (D=4), vacuum G=0 <=> Ricci-flat. NEW only as a self-contained indexed-tensor Q model (diagonal metric, D=4); Riemann is taken as given.
- **Tags.** foundation, ricci, einstein-tensor, general-relativity, differential-geometry, new-framing, qed-drift

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `Tensor/symmetric/ricci_from_riemann/gtr/Rscal/gmet/Gein` | Definition | тензоры, свёртка Riemann->Ricci, метрика, тензор Эйнштейна |
| `ricci_contracts_riemann` | Lemma | ★ свёртка суммирует по повторяющемуся Роль-индексу |
| `gtr_linear/gtr_metric/gtr_ricci` | Lemma | линейность следа; g^mn g_mn=4; tr(Ricci)=скаляр |
| `gtr_einstein` | Lemma | ★★ trace-reversal tr(G)=-R (D=4) |
| `gmet_sym/einstein_symmetric` | Lemma | ★ метрика и тензор Эйнштейна симметричны (Sym^2) |
| `vacuum_ricci_flat` | Lemma | ★ вакуум G=0 => Ricci-flat (R_mn=0) |
| `ricci_to_einstein` | Theorem | capstone: dim + скаляр + reversal + Sym^2 + вакуум |

**Key lemmas (deep):**

- **`gtr_einstein`** - Trace-reversal tr(G)=g^mn G_mn=(1-D/2)R=-R при D=4, доказано через линейность следа + (след метрики=4) + (след Ricci=Rscal). Это СКЕЛЕТ свёртки кривизны над Q (диагональная метрика). Стандартная дифгеометрия, аккуратно формализованная; honest-scope: Riemann берётся как данность (символы Кристоффеля выводятся лишь в шаге 5 RiemannFromConnection). Помечено автором 'новое обрамление известного'. _(ricci, einstein-tensor, trace-reversal, differential-geometry, new-framing)_

**Uniqueness - score 3 (new-framing).** Индексная цепь Riemann->Ricci->скаляр->Эйнштейн над Q (диагональ, D=4): trace-reversal tr(G)=-R, симметрия Sym^2, вакуум=Ricci-flat; G_mn — ВЫВОДИМЫЙ индексный объект.
> _Caveat:_ Свёртка Риччи, тензор Эйнштейна, trace-reversal и вакуум=Ricci-flat — стандартная дифгеометрия любого учебника ОТО. ДРЕЙФ: заголовок объявляет 8 Qed, фактически 9 (леммы внутри Section). Riemann ПОСТУЛИРОВАН (не выведен); метрик-совместимость не доказана. Вклад — обрамление в E/R/R-индексы.

---

## #376 - `src/foundation/RiemannFromConnection.v` - score 3 (new-framing)

**Riemann from connection: Christoffel from metric (torsion-free), Riemann from Gamma, flat=>zero curvature**

- **Topic.** Symbolic 2D-over-Q chain: Levi-Civita Christoffel (first kind) from metric derivatives is torsion-free (symmetric in mu,nu); Riemann from Gamma is antisymmetric in mu,nu; a constant metric gives Gamma=0 gives Riemann=0 (flatness DERIVED). Closes metric->Gamma->Riemann; RicciContraction took Riemann as given.
- **Role.** Self-contained (QArith/Lqa); step 5 (closing) of the field-level gravity lift, feeding RicciContraction (step 4). Metric derivatives carried as free variables (not lattice differences); metric-compatibility not proved.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lqa
- **E/R/R.** _Elements:_ компоненты метрики g_mn и её производных dg (носители геометрии). _Roles:_ индексы/направления; связность Gamma — как Роли переносятся (перенос вдоль направления). _Rules:_ Gamma = 1/2 g^-1 dg (Леви-Чивита, без кручения); Riemann = dG-dG+GG (кривизна из связности); постоянная метрика => Gamma=0 => Riemann=0. _P4:_ метрика->Gamma->Riemann->Ricci->G замкнута; Riemann более не данность. Контраст с d^2=0 (Бианки): GG-член = кривизна (некоммутативность переноса). Символьная 2D-модель над Q; метрик-совместимость nabla g=0 не доказана.
- **Classical counterpart.** Standard differential geometry: Levi-Civita Christoffel symbols from the metric (torsion-free), the Riemann tensor R=dGamma-dGamma+Gamma*Gamma, flat metric => zero curvature. NEW only as a symbolic 2D Q sketch with metric derivatives as free variables; closes the in-repo metric->Riemann chain.
- **Tags.** foundation, christoffel, riemann, general-relativity, differential-geometry, new-framing

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `christoffel1/riemann` | Definition | символы Кристоффеля из метрики; тензор Римана из Gamma |
| `torsion_free` | Lemma | ★ связность симметрична в нижних индексах (без кручения) |
| `flat_metric_zero_christoffel` | Lemma | ★ постоянная метрика => Gamma=0 |
| `riemann_antisymmetric` | Lemma | ★ Riemann антисимметричен в последних двух индексах |
| `flat_zero_riemann` | Lemma | ★ Gamma=0 и dGamma=0 => Riemann=0 |
| `metric_to_riemann` | Theorem | capstone: без кручения + плоск.метрика + антисим. + плоск.кривизна |

**Key lemmas (deep):**

- **`flat_zero_riemann`** - Композиция flat_metric_zero_christoffel + flat_zero_riemann: постоянная метрика => Gamma=0 => Riemann=0, т.е. ПЛОСКОСТНОСТЬ ВЫВЕДЕНА, не постулирована. Замыкает цепь metric->Gamma->Riemann (RicciContraction брал Riemann как данность). Все Qed — ring/rewrite на символьных Q-выражениях (производные = свободные переменные). Стандартная дифгеометрия; honest: 2D, метрик-совместимость не доказана (нужна обратная метрика). _(christoffel, riemann, levi-civita, flatness, new-framing)_

**Uniqueness - score 3 (new-framing).** Замыкание цепи metric->Gamma->Riemann над Q: Кристоффель без кручения, Riemann антисимметричен, постоянная метрика => плоскость ВЫВЕДЕНА (не постулирована).
> _Caveat:_ Символы Леви-Чивита, формула Римана R=dG-dG+GG и flat=>zero curvature — стандартная дифгеометрия. Символьная 2D-модель над Q, производные метрики = СВОБОДНЫЕ переменные (не решёточные разности); метрик-совместимость nabla g=0 НЕ доказана. Qed — ring. Вклад — обрамление/замыкание цепи в репо.

---

## #377 - `src/foundation/RoleLimitTaxonomy.v` - score 4 (synthesis+observation)

**Role-limit taxonomy: decidability stratification (algebraic decidable vs diagonal undecidable)**

- **Topic.** A taxonomy of five mechanisms by which a process fails to be an Element (algebraic, e-integer-trap, Liouville, pi-orbit, diagonal), stratified by whether 'is-it-an-Element?' is itself decidable: 1 class-decidable (algebraic, an algorithm), 1 class-undecidable (diagonal, no algorithm), 3 case-constructive.
- **Role.** Builds on foundation.H1AlgebraicElement/H1AlgebraicDecider (decide_alg_element), foundation.EulerProcessRoleLimit (e_is_role_limit), foundation.UniversalDiagonal (no_universal_decider). The synthesis capstone of the whole finitization/role-limit arc.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: ZArith List Bool; ToS: foundation.H1AlgebraicElement, foundation.H1AlgebraicDecider, foundation.EulerProcessRoleLimit, foundation.UniversalDiagonal
- **E/R/R.** _Elements:_ пять механизмов role-limit (алгебр., e-ловушка, Лиувилль, орбита, диагональ); флаг разрешимости. _Roles:_ каждый механизм = свидетельство «процесс не Element»; ось разрешимости = РАЗРЕШИМ ли сам вопрос «Element?». _Rules:_ алгебр. полюс — решатель ЕСТЬ (decide_alg_element); диагональ. полюс — решателя НЕТ (no_universal_decider); середина — конструктивно по случаю. _P4:_ role-limit'ы не монолитны — стратифицируются по разрешимости «is-Element?»: разрешимо (алгебр.) -> неразрешимо (диагональ). Финитизац. граница пересечена ВТОРОЙ границей — разрешимости.
- **Classical counterpart.** Mirrors the classical hierarchy: decidable algebraic numbers vs the undecidability of the halting problem (Cantor/Russell via Lawvere's diagonal). NEW only as the SYNTHESIS uniting five role-limit mechanisms under one decidability stratification axis.
- **Tags.** foundation, role-limit, decidability, lawvere-diagonal, halting, finitization, synthesis

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `RoleLimitKind/Decidability/decidability/all_kinds/dec_eqb/count_decidability` | Definition | таксономия пяти механизмов и ось разрешимости |
| `algebraic_pole` | Theorem | ★★ алгебр. полюс: РЕШАТЕЛЬ существует (decide_alg_element, Sumbool) |
| `diagonal_pole` | Theorem | ★★ диагональ. полюс: универсального решателя НЕТ (Лоувер) |
| `transcendental_middle` | Theorem | ★ конструктивная середина: e-процесс — role-limit |
| `n_decidable/n_undecidable/n_constructive/taxonomy_total` | Lemma | ★ счёт стратификации: 1 / 1 / 3 |
| `role_limit_taxonomy` | Theorem | capstone: два полюса + середина + счёт 1/1/3 |

**Key lemmas (deep):**

- **`algebraic_pole/diagonal_pole`** - Два настоящих полюса: для алгебраических чисел Element-ность РАЗРЕШИМА (decide_alg_element — вычислимый Sumbool), а на вычислительной границе универсального решателя НЕТ (no_universal_decider — диагональ Лоувера = Кантор=halting=Russell). Объединяющее наблюдение всей арки H1: финитизационная граница (Element/role-limit) сама пересечена ВТОРОЙ границей — разрешимостью «is-Element?». Полюса цитируются (exact); новизна — стратификация и счёт 1/1/3. _(role-limit, decidability, lawvere-diagonal, halting, synthesis)_

**Uniqueness - score 4 (synthesis+observation).** Стратификация role-limit'ов по разрешимости «is-Element?»: разрешимо для алгебраических (есть алгоритм), неразрешимо на диагонали (нет алгоритма), конструктивно для 3 промежуточных — вторая граница, пересекающая финитизационную.
> _Caveat:_ Оба полюса — классика: разрешимость алгебраических чисел и неразрешимость halting (Кантор/Лоувер). Сами полюса доказаны в цитируемых файлах (decide_alg_element, no_universal_decider), здесь exact-сборка + счёт reflexivity. Новизна — ОБЪЕДИНЯЮЩЕЕ наблюдение/таксономия, не новая теорема.

---

## #378 - `src/foundation/SakharovERR.v` - score 3 (new-framing)

**Sakharov conditions = the E/R/R triad of the baryon count (necessity + sufficiency)**

- **Topic.** The three Sakharov conditions map bijectively onto three E/R/R levels {P4,L2,L5}; eta_B is the triadic product cp*bviol*noneq (the volume of the E/R/R box): it collapses to 0 if any factor is 0 (necessity) and is positive if all three are (sufficiency), with the CP factor anchored to the derived Jarlskog invariant.
- **Role.** Builds on foundation.EtaFromLattice (jarlskog_estimate, jarlskog_positive, cp_phase_derived). Baryogenesis Phase 3 (structure); the magnitude (~10^9 gap) is Phase 4. The CP face cites the real derived Jarlskog.
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lqa; ToS: foundation.EtaFromLattice
- **E/R/R.** _Elements:_ три Q-множителя (cp = реальный Ярлског, bviol, noneq); eta = их произведение. _Roles:_ B-нар<->P4, CP<->L2, неравн<->L5 — три условия Сахарова биективны трём уровням E/R/R («почему ровно три»). _Rules:_ eta = триадное произведение; необходимость (любой множитель 0 => eta=0) + достаточность (все >0 => eta>0); eta = объём триадного ящика. _P4:_ три условия Сахарова — не три входа, а три грани ОДНОЙ триады счёта барионов; eta_B = необходимый остаток триады; величина = SM-граница (Фаза 4).
- **Classical counterpart.** Sakharov's three baryogenesis conditions (1967: B-violation, C/CP violation, out-of-equilibrium) are standard cosmology; the eta = product structure is folklore. NEW only as the E/R/R triad reading (3 conditions <-> 3 levels) and the necessity/sufficiency of a triadic product.
- **Tags.** foundation, sakharov, baryogenesis, err-triad, jarlskog, cosmology, new-framing

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `SakharovCondition/ERRLevel/sakharov_err/eta_triad` | Definition | три условия, три уровня, отображение, триадное произведение |
| `sakharov_err_injective/sakharov_err_surjective` | Lemma | ★ биекция условия <-> уровни E/R/R |
| `eta_zero_if_no_cp/eta_zero_if_no_bviol/eta_zero_if_no_noneq` | Lemma | ★ необходимость: убери грань => eta=0 (ящик схлопывается) |
| `eta_pos_needs_cp/_bviol/_noneq/eta_pos_needs_all` | Lemma | положительный eta => все три грани >0 |
| `eta_pos_if_all/eta_realized_pos` | Lemma | ★ достаточность: все >0 => eta>0; CP-грань = реальный Ярлског |
| `sakharov_err_triad` | Theorem | capstone: биекция + необходимость + достаточность + Ярлског-якорь |

**Key lemmas (deep):**

- **`sakharov_err_injective/eta_realized_pos`** - Биекция трёх условий Сахарова на три уровня E/R/R {P4,L2,L5} (inj+surj, congruence) даёт ToS-ответ «почему ровно три условия» = три уровня триады; необходимость/достаточность — это просто свойства произведения трёх Q (ring/Qmult_lt_0_compat). CP-грань заякорена на РЕАЛЬНЫЙ выведенный Ярлског (jarlskog_positive). Честно: величина eta_B (зазор ~10^9) — Фаза 4, не здесь; это СТРУКТУРА. Биекция — содержательное обрамление; необходимость/достаточность тривиальны. _(sakharov, baryogenesis, err-triad, jarlskog, new-framing)_

**Uniqueness - score 3 (new-framing).** Три условия Сахарова = E/R/R-триада счёта барионов (биекция на {P4,L2,L5}); eta_B = триадное произведение с необходимостью (любая грань 0 => 0) и достаточностью (все >0 => >0), CP-грань = реальный Ярлског.
> _Caveat:_ Три условия Сахарова (1967) и eta как произведение факторов — стандартная космология/фольклор. Необходимость/достаточность — тривиальные свойства произведения трёх Q (ring). Величина eta_B (~10^9 зазор) НЕ выводится (Фаза 4). Вклад — обрамление 3<->3 (биекция), не новая физика.

---

## #379 - `src/foundation/ScaleHierarchySynthesis.v` - score 4 (synthesis+observation)

**Scale-hierarchy synthesis: NS energy cascade and RG coupling flow are one monotone scale flow**

- **Topic.** Unifies two arenas as monotone scale flows f:nat->Q: the NS truncated enstrophy is non-decreasing (Element if bounded / role-limit at the alpha=2 wall), the RG sub-critical flow is non-increasing (convergent Element), the RG super-critical flow is non-decreasing (runaway role-limit). The Element/role-limit boundary = the closure of a monotone scale flow.
- **Role.** Builds on foundation.ShellCascadeNS (enstrophy_monotone), foundation.CascadeBoundary, foundation.RGCascadeReal (rg_sub_decreasing, rg_super_increasing). CAPSTONE of the scale-hierarchy/cascade direction; the first 'dynamization of the ToS hierarchy'.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lia Lqa; ToS: foundation.ShellCascadeNS, foundation.CascadeBoundary, foundation.RGCascadeReal
- **E/R/R.** _Elements:_ два scale-процесса (Omega_N, rg_iterate); две FlowSides. _Roles:_ две арены (энергия / связь) как инстансы одного монотонного scale-потока. _Rules:_ scale-flow монотонен в своём режиме; граница = его замыкание (ограничено=Element / убегает=role-limit); обе арены подчиняются. _P4:_ обе арены = монотонные scale-процессы; граница Element/role-limit единообразно = ЗАМЫКАНИЕ монотонного потока. Стена alpha=2 и континуумный предел РГ = ОДИН role-limit. Локализуем, не пересекаем.
- **Classical counterpart.** No single classical result — abstracts two scale-flow phenomena (Navier-Stokes enstrophy cascade, RG coupling flow) under one monotone-flow umbrella. The individual arenas mirror standard turbulence-cascade and RG-flow theory.
- **Tags.** foundation, scale-flow, cascade, navier-stokes, renormalization, synthesis

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `ScaleFlow/flow_nondecreasing/flow_nonincreasing/FlowSide` | Definition | монотонный scale-поток и две стороны замыкания |
| `flow_h1_disjoint` | Lemma | ConvergentElement <> RunawayRoleLimit (стороны дизъюнктны) |
| `cascade_enstrophy_is_flow` | Lemma | ★ NS-энстрофия = неубывающий scale-поток |
| `rg_subcritical_is_flow` | Lemma | ★ РГ докритич. = невозрастающий (Element) |
| `rg_supercritical_is_flow` | Lemma | ★ РГ надкритич. = неубывающий (role-limit) |
| `scale_hierarchy_synthesis` | Theorem | capstone: энергия + связь(-) + связь(+) + дизъюнктность сторон |

**Key lemmas (deep):**

- **`scale_hierarchy_synthesis`** - Объединяет две арены (NS-энстрофия и РГ-поток) под ОДНОЙ абстракцией монотонного scale-потока: в обеих граница Element/role-limit = ЗАМЫКАНИЕ монотонного потока (ограничено=Element, убегает=role-limit), т.е. стена alpha=2 NS и континуумный предел РГ — один тип role-limit. Первая «динамизация иерархии ToS». Честно: НЕ решает ни одно замыкание (ограниченность энстрофии, сходимость убегания) — это и ЕСТЬ role-limit'ы, локализованы не пересечены. Леммы — обёртки уже-доказанной монотонности. _(scale-flow, cascade, navier-stokes, renormalization, synthesis)_

**Uniqueness - score 4 (synthesis+observation).** NS энергетический каскад и РГ поток связи = ОДНА абстракция монотонного scale-потока над Q; граница Element/role-limit = замыкание потока; стена alpha=2 и континуумный предел РГ — один тип role-limit.
> _Caveat:_ Сами арены (турбулентный каскад энстрофии, РГ-поток) — стандартная физика; леммы — лишь ОБЁРТКИ уже-доказанной монотонности (enstrophy_monotone, rg_sub/super из RGCascadeReal). НИ ОДНО замыкание не решается (ограниченность/сходимость = сами role-limit'ы, не пересекаются). Новизна — объединяющее наблюдение (две арены = один абстракт), не новая теорема.

---

## #380 - `src/foundation/ScaleHierarchyTransfer.v` - score 3 (new-framing)

**Inter-level energy flux on a finite scale hierarchy: telescoping conservation over Q**

- **Topic.** Gives the ToS level order its missing payload: an inter-shell current Pi, flux divergence Pi n - Pi(S n), and the telescoping continuity law sum = Pi 0 - Pi N; closed cascade conserves energy exactly.
- **Role.** Self-contained (QArith/Lia). Reused as the base primitive by ShellCascadeNS.v (NS instance) and echoed by SheafLaplacianQ.v (global section = flux-free).
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, Lia, Lqa
- **E/R/R.** _Elements:_ амплитуды оболочек a_n in Q; ток Pi; дивергенция потока; конечные суммы. _Roles:_ оболочки n=0..N-1 = масштабная лестница (k_n=2^n); интерфейсы = сцепления; Pi = межуровневый ток. _Rules:_ сохранение = телескопирующая непрерывность: суммарный вброс = Pi 0 - Pi N; закрытый каскад => 0 вброса. _P4:_ каскад = ПРОЦЕСС: конечен на каждом N (Element), верхний ток Pi N = поток к role-limit N->oo (аномальная диссипация). Перелокализует стену, НЕ пересекает.
- **Classical counterpart.** Discrete continuity/conservation via telescoping (summation-by-parts) and the energy-cascade picture of turbulence. NEW only as the explicit inter-level FLUX primitive the ToS level order lacked, over Q, 0-axiom.
- **Tags.** foundation, cascade, conservation, telescope, navier-stokes, new-framing

**Lemmas (10):**

| name | kind | role |
|---|---|---|
| `shell_scale/shell_sum/shell_sum_S` | Definition/Lemma | дядическая лестница 2^n + сумма по оболочкам |
| `shell_sum_congr` | Lemma | экстенсиональность суммы (реюз для инстансов) |
| `shell_telescope` | Lemma | телескопирующее тождество = генератор всех законов сохранения |
| `shell_energy/total_energy` | Definition | энергия оболочки a_n^2 и суммарная |
| `cascade_injection` | Definition | вброс = дивергенция потока Pi n - Pi(S n) |
| `cascade_total_injection` | Theorem | суммарный вброс телескопирует к Pi 0 - Pi N |
| `closed_cascade/closed_cascade_conserves` | Definition/Theorem | закрытый каскад сохраняет энергию (0 вброса) |
| `cascade_top_flux_is_loss` | Lemma | при Pi0=0 потеря = верхний ток -Pi N (role-limit) |
| `Pi_ex/closed_cascade_witness` | Definition/Example | 3-оболочечный свидетель vm_compute |
| `scale_hierarchy_transfer` | Theorem | капстоун: телескоп + закрытость + role-limit |

**Key lemmas (deep):**

- **`cascade_total_injection / closed_cascade_conserves`** - Дивергенция межоболочечного тока суммируется к граничным токам Pi 0 - Pi N (телескоп); закрытый каскад => точное сохранение. Это и есть НОВЫЙ переиспользуемый межуровневый примитив для level-иерархии ToS (раньше: SystemMorphism 'cross-level = future work'). Сама математика = дискретная непрерывность / summation-by-parts, классика; новизна = постановка примитива над уровнями и локализация стены турбулентности как верхнего тока к role-limit. _(cascade, conservation, telescope, level-flux)_

**Uniqueness - score 3 (new-framing).** Первый межуровневый поток+сохранение на level-иерархии ToS (раньше уровни были без 'нагрузки'); стена турбулентности перелокализована как верхний ток к role-limit N->oo.
> _Caveat:_ Сама телескопирующая непрерывность / summation-by-parts и каскадная картина = классика; стена (замыкание/суперкритическая сумма) НЕ пересекается, лишь локализуется.

---

## #381 - `src/foundation/SheafLaplacianQ.v` - score 3 (new-framing)

**Smallest cellular sheaf over Q: H^0, sheaf Laplacian, Hodge, rational spectrum**

- **Topic.** Builds a 2-vertex/1-edge cellular sheaf over Q: coboundary delta, global sections ker delta, Laplacian [[a^2,-ab],[-ab,b^2]], Hodge, and disc(L)=(a^2+b^2)^2 (perfect square => Element spectrum); a role-limit foil [[1,1],[1,2]] disc 5.
- **Role.** Imports foundation.RealCouplingSpectrum (disc-criterion, is_square_Q, is_eigenvalue). A bridge file connecting ToS to the live field of network sheaves; reuses ScaleHierarchyTransfer's conservation idea conceptually.
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, Lia, Lqa; ToS: foundation.RealCouplingSpectrum
- **E/R/R.** _Elements:_ stalks Q в u,v,e; restriction maps a,b in Q; 2x2 пучок-лапласиан; спектр {0, a^2+b^2}. _Roles:_ вершины/ребро = ячейки; restriction maps = межклеточные отображения; глоб. сечение = согласованное (flux-free) назначение; собств. значения = моды. _Rules:_ delta(xu,xv)=b*xv-a*xu; H^0=ker delta; L=delta*delta; ker L >= H^0 (Ходж); disc(L)=(a^2+b^2)^2 квадрат => Element спектр. _P4:_ пучок-когомология над Q; глоб. сечения = каскад-сохранение (flux-free); спектр на границе Element (disc квадрат); role-limit foil [[1,1],[1,2]] disc 5 (golden). Малый пучок: Element genuine, role-limit foil.
- **Classical counterpart.** Cellular/network sheaf cohomology of Hansen-Ghrist (coboundary, H^0 global sections, sheaf Laplacian L=delta*delta, Hodge ker L >= H^0). Standard over R; NEW only as an over-Q minimal instance with the spectrum classified by the Element/role-limit (square-discriminant) boundary.
- **Tags.** foundation, sheaf, hodge, laplacian, over-Q, bridge, new-framing

**Lemmas (10):**

| name | kind | role |
|---|---|---|
| `delta/global_section_ba` | Definition/Lemma | кограница; (b,a) глобальное сечение |
| `Lap_uu/uv/vu/vv/Lap_u/Lap_v` | Definition | вход пучок-лапласиана |
| `Lap_is_delta_star_delta_u/v` | Lemma | L = delta* delta покомпонентно |
| `global_section_in_kerL` | Lemma | Ходж: глоб. сечение в ker L |
| `kerL_implies_kerDelta` | Lemma | обратное при a/=0: гармоника = сечение |
| `sheaf_disc_square` | Lemma | disc(L)=(a^2+b^2)^2 полный квадрат |
| `sheaf_spectrum_element` | Lemma | рациональная мода существует (Element) |
| `sheaf_eigenvalue_zero/energy` | Lemma | моды 0 (H^0) и a^2+b^2 (несогласованность) |
| `sheaf_role_limit_disc` | Example | foil [[1,1],[1,2]] disc 5 |
| `sheaf_laplacian_Q` | Theorem | капстоун-мост над Q |

**Key lemmas (deep):**

- **`sheaf_disc_square / global_section_in_kerL`** - disc пучок-лапласиана = (a^2+b^2)^2 — полный квадрат, поэтому спектр {0, a^2+b^2} рационален (Element-сторона границы), а каждое глобальное сечение лежит в ker L (Ходж). Genuine содержание = построение клеточной пучок-когомологии НАД Q (а не R) с спектром на той же Element/role-limit границе, что и остальной ToS, плюс мост к Hansen-Ghrist. Сами понятия (delta, H^0, sheaf Laplacian, Hodge) — стандартная теория клеточных пучков; пучок минимален (2 вершины). _(sheaf, hodge, laplacian, over-Q, bridge)_

**Uniqueness - score 3 (new-framing).** Клеточная пучок-когомология построена над Q (не R) с спектром лапласиана на Element/role-limit границе; мост к живому полю network sheaves в отличительном регистре ToS.
> _Caveat:_ Клеточные пучки, H^0, sheaf Laplacian, Ходж — стандарт (Hansen-Ghrist); пучок крошечный (2 верш./1 ребро), role-limit сторона = лишь foil (реализация richer пучком не сделана).

---

## #382 - `src/foundation/ShellCascadeNS.v` - score 2 (methods)

**NS turbulent cascade as a dyadic shell model over Q: conservation + located alpha=2 wall**

- **Topic.** Instantiates ScaleHierarchyTransfer to turbulence: dyadic scales k_n=2^n (k doubles), enstrophy weight w_n=4^n (quadruples), closed cascade conserves energy (inherited), and unbounded scales locate the supercritical wall at N->oo.
- **Role.** Imports foundation.ScaleHierarchyTransfer (the primitive). First concrete instance; ties to NSBoundDescent.v (the alpha=2 wall). Concrete 4-shell witnesses.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, ZArith, Lia, Lqa; ToS: foundation.ScaleHierarchyTransfer
- **E/R/R.** _Elements:_ амплитуды a_n in Q; масштаб k_n=2^n; вес энстрофии w_n=4^n; конкретный 4-оболочечный свидетель. _Roles:_ дядические оболочки k_n=2^n = масштабные роли; w_n=k_n^2 = вес энстрофии/диссипации (опасная роль); каскад-поток = межоболочечный перенос. _Rules:_ каскад сохраняет энергию (закрытый => 0, наследуется); лестница k_{n+1}=2k_n, w_{n+1}=4w_n; масштабы неограничены => замыкание N->oo = суперкритическая стена. _P4:_ каскад = процесс; конечн. N = Element (сохранённая энергия + конечная энстрофия); неограниченные масштабы (2^n->oo, вес 4^n->oo) => замыкание N->oo = стена alpha=2 = role-limit. Локализуем, НЕ пересекаем.
- **Classical counterpart.** Dyadic shell models (GOY/Sabra) of the Navier-Stokes turbulent energy cascade; energy conservation of the inviscid nonlinearity; supercritical enstrophy growth. NEW only as the first 0-axiom Q instance of the inter-level transfer primitive, locating (not crossing) the alpha=2 wall.
- **Tags.** foundation, shell-model, turbulence, enstrophy, navier-stokes, methods

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `kdyad/kdyad_doubles` | Definition/Lemma | масштаб 2^n; удвоение |
| `wdyad/wdyad_quadruples` | Definition/Lemma | вес энстрофии 4^n; учетверение |
| `pow2_ge_succ/cascade_scales_unbounded` | Lemma | масштабы неограничены (достигают каждой шкалы) |
| `shell_enstrophy/total_ns_enstrophy` | Definition | взвешенная энстрофия (опасная величина) |
| `a_ex/Pi_ns` | Definition | свидетель: затухающие амплитуды + закрытый ток |
| `ns_witness_conserves/energy/enstrophy` | Example | свидетели: сохранение, энергия 21/16, энстрофия 3 (плоская) |
| `shell_cascade_ns` | Theorem | капстоун: лестница + сохранение + неограниченность |

**Key lemmas (deep):**

- **`wdyad_quadruples / cascade_scales_unbounded`** - Вес энстрофии учетверяется на каждой оболочке (4^n) и масштабы 2^n неограничены — вместе они ЛОКАЛИЗУЮТ суперкритическую стену alpha=2 как замыкание N->oo, тогда как сохранение энергии наследуется generic-образом от примитива. Честно: сохранение generic (любой закрытый поток сохраняет); NS-специфика = дядическая лестница + 4^n вес + неограниченные шкалы. Стена (ограниченность энстрофии в замыкании) НЕ пересекается. Шелл-модели NS = классика (GOY/Sabra). _(shell-model, turbulence, enstrophy, role-limit)_

**Uniqueness - score 2 (methods).** Первый Q-инстанс межуровневого примитива: NS-каскад как дядическая шелл-модель с точным сохранением и локализованной (не пересечённой) стеной alpha=2.
> _Caveat:_ Дядические шелл-модели турбулентности и суперкритический рост энстрофии = классика; сохранение здесь generic-наследие, стена лишь локализуется.

---

## #383 - `src/foundation/SHOThreeFormulas.v` - score 3 (new-framing)

**Quantum SHO as THREE E/R/R formulas over Q: ground / spectrum / evolution + Born glue**

- **Topic.** Packages the QHO as E-formula (ground omega/2), R-spectrum (E_n=omega(n+1/2)), R-rules (x(t+1)=(2-k)x(t)-x(t-1)), proves the period-4 orbit at k=2, energy conservation, Born rule on rational (3/5,4/5), and mutual consistency.
- **Role.** Self-contained (QArith/Qabs). Template for the three-formula re-derivation method (later reified in ThreeFormulaMethod/Boundary). Sho_ground/sho_level reused.
- **Counts.** Qed 26 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, Qabs, ZArith, List, PeanoNat, Lia, Lqa
- **E/R/R.** _Elements:_ основное состояние omega/2; уровни E_n; пары амплитуд орбиты; born_prob. _Roles:_ E-формула (L1) = основное состояние; R-спектр (L4) = лестница ролей; R-правила (L5) = эволюция; Born = L3-проекция на дискретные роли. _Rules:_ E_n = omega(n+1/2); шаг spacing = omega; x(t+1)=(2-k)x(t)-x(t-1); период-4 при k=2; born_prob нормирован на (3/5,4/5). _P4:_ конечная рациональная формализация над Q/nat (без Гильбертова пространства); три формулы взаимно НЕзависимы (эволюция допускает x=0, но квантовое основание omega/2/=0) но совместны через glue-теорему.
- **Classical counterpart.** Quantum harmonic oscillator (E_0=omega/2 zero-point, E_n=omega(n+1/2) ladder, discrete Newton recurrence), Born rule, Pythagorean rational normalization. NEW only as the E/R/R 'three-formula' decomposition over Q (nat) with no Hilbert space.
- **Tags.** foundation, sho, three-formula, born, quantum, new-framing

**Lemmas (10):**

| name | kind | role |
|---|---|---|
| `sho_ground/ground_positive/ground_is_half_omega/ground_nonzero/ground_classical_limit` | Definition/Theorem | E-формула: нулевая точка omega/2 > 0 |
| `sho_level/level_0_is_ground/level_spacing/level_positive/level_increasing` | Definition/Theorem | R-спектр: лестница с шагом omega |
| `level_0_value/level_1_value/level_2_value` | Lemma | явные первые уровни |
| `sho_evolve/sho_step/sho_period_4_k2_step1..4` | Definition/Theorem | R-правила: эволюция, период-4 орбита |
| `discrete_energy/energy_on_period_4_k2/energy_conserved_period_4_k2` | Definition/Theorem | дискретная энергия инвариантна на орбите |
| `evolution_admits_zero_orbit/classical_ground_is_zero/quantum_ground_nonzero` | Theorem | E-формула НЕ выводима из R-правил |
| `sho_three_formulas_consistent` | Theorem | три формулы взаимно совместны |
| `born_prob/born_norm_3_4_5/born_certain_ground/born_uniform_4` | Definition/Theorem | Born-правило на рациональных амплитудах |
| `expected_energy_01/expected_energy_3_4_superposition` | Definition/Theorem | ожидаемая энергия суперпозиции |
| `sho_complete` | Theorem | капстоун: QHO как E/R/R + Born |

**Key lemmas (deep):**

- **`sho_three_formulas_consistent / evolution_admits_zero_orbit`** - Центральное наблюдение: эволюционное правило допускает тривиальную орбиту x=0 (классическое основание = 0), тогда как квантовое основание omega/2 строго положительно — значит E-формула ДОБАВЛЯЕТ содержание сверх R-правил, и три аспекта лишь совместны (glue), но не выводимы друг из друга. Это переобрамление одной физики (QHO) как трёх E/R/R-формул над Q. Сама физика (нулевая точка, лестница, дискретный Ньютон, Born) = стандарт; новое = разложение и наблюдение независимости. _(sho, three-formula, born, E/R/R)_

**Uniqueness - score 3 (new-framing).** QHO переобрамлён как ТРИ взаимно независимые но совместные E/R/R-формулы над Q/nat (без Гильберта); наблюдение: квантовое основание omega/2 не выводимо из классической эволюции.
> _Caveat:_ Нулевая точка omega/2, лестница E_n, дискретный осциллятор, Born-правило и пифагорейская нормировка (3/5,4/5) — стандартная КМ; новизна в разложении/обрамлении, не в физике.

---

## #384 - `src/foundation/SingleSourcePrinciple.v` - score 2 (methods)

**Single coupling source => C cancels => sin^2 theta_W = 3/13 (vs free in SM)**

- **Topic.** Shows that if g^2=C/3 and g'^2=C/10 come from ONE graph (one budget C), then sin^2=(C/10)/(C/3+C/10)=3/13 independent of C; if from independent C1,C2 the ratio is free.
- **Role.** Self-contained (QArith). One of the sin^2=3/13 cluster (SpectralSectors, StableDimension, ThetaFromL2L3, WeinbergAngleDerivation, SinThetaWDerivationStatus).
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, Lia, ZArith, Lqa
- **E/R/R.** _Elements:_ бюджет связи C; sin^2 из C; размерности 3,10. _Roles:_ единый источник => C1=C2 => sin^2 не зависит от C; разные источники => sin^2 свободен. _Rules:_ sin2_from_C C 3 10 == 3/13 для любого C>0; sin2_independent зависит от отношения C1/C2. _P4:_ конечная рациональная проверка: C сокращается алгебраически. P4-нагрузка минимальна — это арифметика сокращения, а не вывод размерностей 3 и 10.
- **Classical counterpart.** The Weinberg-angle mixing relation sin^2 = g'^2/(g^2+g'^2); in the SM g,g' are independent free parameters. The 'single source' cancellation and sin^2=3/13 are a ToS BRANDING claim, not standard physics.
- **Tags.** foundation, sin2, 3/13, weinberg, over-branded, methods

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `sin2_from_C` | Definition | sin^2 из единого бюджета C |
| `C_cancels_3_10` | Lemma | C сокращается для любого C>0 => 3/13 |
| `C_cancels_at_1/at_42/at_137` | Lemma | конкретные инстансы C-независимости |
| `sin2_independent/independent_gives_different/independent_not_unique` | Definition/Lemma | разные C => разный ответ (3/13 /= 6/16) |
| `single_source_principle` | Theorem | капстоун: единый источник vs независимые |

**Key lemmas (deep):**

- **`C_cancels_3_10`** - Ядро файла: при g^2=C/3, g'^2=C/10 общий множитель C сокращается в отношении, давая 3/13 независимо от C — это всего лишь алгебраическое сокращение, а ЦЕЛЫЕ 3 и 10 (= dim SU(2), метрика 4D) ПРЕДПОЛАГАЮТСЯ, не выводятся здесь. Брендированное 'sin^2=3/13 из одного графа'. Честный статус всей претензии разобран в SinThetaWDerivationStatus.v: 'выведено по модулю одной идентификации', но НЕ полностью вынуждено (какие размерности брать в отношение = идентификация, не теорема). _(sin2, 3/13, cancellation, over-branded)_

**Uniqueness - score 2 (methods).** Если g,g' из ОДНОГО графа (один бюджет C), C сокращается и sin^2=3/13 фиксирован, а не свободен как в SM.
> _Caveat:_ OVER-BRANDED: 3/13 — это сокращение C при ПРЕДПОЛОЖЕННЫХ 3=dim SU(2) и 10=метрика; выбор размерностей = идентификация, не теорема (см. SinThetaWDerivationStatus). Отношение Вайнберга = стандарт.

---

## #385 - `src/foundation/SinThetaWDerivationStatus.v` - score 3 (synthesis+observation)

**Epistemic-status audit of sin^2 theta_W = 3/13: derived modulo ONE discrete identification**

- **Topic.** Quantifies the support behind sin^2=3/13 with 4 pillars (forced theta=1 subtheorem, structurally meaningful integers 3/10, discrete data-selection among {1/11,3/13,8/18}, single bridge choice r=3/10) vs 0 for the (5/16)^3 neutrino numerology.
- **Role.** Audit file. Builds on foundation.ThetaFromL2L3 (theta=1) and foundation.WeinbergAngleDerivation (dim_SU2, n_metric, r, wrong_X). Sibling of PhysicsDemarcation (H39 shadow) and DerivedVsNumerological.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, Lqa, Lia, ZArith, List, Bool; ToS: foundation.ThetaFromL2L3, foundation.WeinbergAngleDerivation
- **E/R/R.** _Elements:_ theta (теорема theta=1); целые 3=dim SU(2), 10=метрика 4D; дискретный набор {1,3,8}/10; мост r=3/10. _Roles:_ опора-1 теорема, опора-2 независимые целые, опора-3 дискретный отбор данными, опора-4 единственный выбор-мост. _Rules:_ тень H39 = непрерывный r ловит всё; НО ToS даёт лишь ДИСКРЕТНЫЕ dim(G)/10, данные выбирают единственный 3/10; при мосте r=3/10 => 3/13 и совпадение 0.19% вынуждены. _P4:_ sin^2 theta_W = 'выведено по модулю ОДНОЙ дискретной, выбранной данными идентификации' — строго сильнее непрерывной постдикции, но НЕ 'полностью вынуждено' (мост = идентификация, не теорема; остаточный честный зазор изолирован).
- **Classical counterpart.** An explicit HONESTY-AUDIT of the flagship sin^2 theta_W = 3/13 claim against the standard EW mixing relation. Self-classifies as 'derived modulo exactly one identification', strictly stronger than continuous postdiction but NOT fully forced.
- **Tags.** foundation, sin2, 3/13, honesty-audit, demarcation, synthesis+observation

**Lemmas (8):**

| name | kind | role |
|---|---|---|
| `has_forced_subtheorem` | Theorem | опора-1: theta=1 — genuine теорема (L2+L3) |
| `integers_are_structural` | Lemma | опора-2: 3=dim SU(2), 10=метрика, независимо осмыслены |
| `sin2_cand/candidate_values` | Definition/Lemma | дискретный набор кандидатов {1/11,3/13,8/18} |
| `obs_lo/obs_hi/in_window/only_su2_selected` | Definition/Lemma | опора-3: только SU(2) попадает в окно (единственность отбора) |
| `derived_modulo_bridge` | Theorem | опора-4: при r=3/10 sin^2=3/13 вынуждено |
| `bridge_from_structural_integers` | Lemma | мост 3/10 = dim SU(2)/метрика (r_weinberg) |
| `Pillar/sin2_pillars/neutrino_pillars/pillar_gap` | Definition/Lemma | счёт опор: 4 vs 0 |
| `sin2thetaW_derived_modulo_one_choice` | Theorem | капстоун аудита |

**Key lemmas (deep):**

- **`only_su2_selected / sin2thetaW_derived_modulo_one_choice`** - Главный апгрейд тени H39: ToS даёт НЕ непрерывный параметр r (который ловит любую цель), а ДИСКРЕТНЫЙ набор размерностных отношений {1/11,3/13,8/18}, и данные выбирают единственный член 3/13 (only_su2_selected — машинно через filter). Это притупляет возражение 'постдикция ловит всё'. ЧЕСТНЫЙ итог: 4 опоры vs 0 у нейтрино, статус = 'выведено по модулю одной идентификации', но мост (какие размерности в отношение) остаётся идентификацией, не теоремой. Ценность файла = сам честный аудит и квантификация зазора. _(sin2, 3/13, honesty-audit, demarcation)_

**Uniqueness - score 3 (synthesis+observation).** Точный эпистемический статус sin^2=3/13: 'выведено по модулю ОДНОЙ дискретной, выбранной данными идентификации' — строго сильнее непрерывной постдикции; апгрейд тени H39 (дискретно vs непрерывно) + единственность отбора + счёт опор 4 vs 0.
> _Caveat:_ НЕ 'полностью вынуждено': мост r=3/10 (какие размерности брать) = идентификация, не теорема — остаточный честный зазор. Реюз theta=1 и wrong_X из готового вывода; новое лишь обрамление/аудит.

---

## #386 - `src/foundation/SMConsistency.v` - score 3 (new-framing)

**SM is CONSISTENT with nested distinction [3,2,1] (crown theorem, honestly scoped)**

- **Topic.** Chains nested distinction -> gauge [3,2,1] (12 generators) -> AF -> anomaly-free + chiral fermion content -> 3 generations from CP -> kappa=1/10, assembling the SM as the minimal chiral anomaly-free theory; includes an honest_assessment of what is proved vs argued.
- **Role.** Crown/synthesis file importing process.ProcessAnomaly(Cancel), foundation.NestedDistinction, ChiralityFromL2, AsymptoticFreedomBound, ChiralAnomalyUniqueness, GenerationsFromL4. Was named SMUniqueness; renamed for honesty.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, Lia, Lqa; ToS: process.ProcessAnomaly, process.ProcessAnomalyCancel, foundation.NestedDistinction, foundation.ChiralityFromL2, foundation.AsymptoticFreedomBound, foundation.ChiralAnomalyUniqueness, foundation.GenerationsFromL4
- **E/R/R.** _Elements:_ distinction; gauge [3,2,1]; зарядовое содержание поколения; kappa. _Roles:_ distinction -> gauge -> хиральность -> аномалия -> 3 поколения -> kappa. _Rules:_ SM = минимальная хиральная анти-аномальная теория, согласованная с [3,2,1]; anomaly-free + chiral + AF + 3 gen + kappa=1/10. _P4:_ crown-теорема: цепь distinction -> SM, но СОГЛАСОВАНОСТЬ, не единственность (другие anti-anomaly возможны, исчерпывающий перебор по Q не сделан). honest_assessment явно разделяет PROVED vs ARGUED.
- **Classical counterpart.** The Standard Model gauge group SU(3)xSU(2)xU(1), anomaly cancellation, asymptotic freedom, 3 generations + CP, are textbook. NEW only as the ToS claim that they are CONSISTENT WITH (not derived/unique from) nested distinction [3,2,1]; explicitly de-branded from 'uniqueness' to 'consistency'.
- **Tags.** foundation, standard-model, consistency, honesty-audit, over-branded, new-framing

**Lemmas (9):**

| name | kind | role |
|---|---|---|
| `n_metric_components/kappa_derived/kappa_equals_1_10` | Definition/Lemma | kappa=1/10 (реплика во избежание stale .vo) |
| `sm_gauge_group_derived` | Theorem | [3,2,1] -> 12 генераторов |
| `sm_is_af` | Theorem | асимптотическая свобода SU(3) |
| `sm_fermion_content_derived` | Theorem | anomaly-free + хиральность (тривиальное не хирально) |
| `sm_3_generations_derived` | Theorem | 3 поколения из CP (n_phases=1) |
| `sm_kappa_derived` | Theorem | kappa=1/10 |
| `standard_model_derived` | Theorem | crown: вся цепь вместе |
| `parameter_reduction/honest_assessment/foundation_complete` | Theorem | счёт параметров + честная оценка + завершение цепи foundation |
| `sm_free_parameters_std/sm_uniqueness_theorem_count` | Definition | 19 свободных параметров SM; счётчик |

**Key lemmas (deep):**

- **`honest_assessment / standard_model_derived`** - Файл сам себя честно деклассирует: переименован SMUniqueness->SMConsistency, потому что доказана СОГЛАСОВАНОСТЬ SM с distinction (anomaly-free, chiral, AF), но НЕ единственность (исчерпывающий перебор всех Q-решений не сделан; тривиальное лишь исключено). honest_assessment явно метит '90% formalized' для 'минимальная хиральная' и 'TOO STRONG' для 'единственно возможная физика'. Каждый шаг цепи (gauge group, 3 поколения, kappa) — реюз готовых лемм; целые 3/10 и sin^2=3/13 — брендированные (см. SinThetaWDerivationStatus). Ценность = честная сборка + явная демаркация. _(standard-model, consistency, honesty-audit, over-branded)_

**Uniqueness - score 3 (new-framing).** SM СОГЛАСОВАН с вложенным различением [3,2,1] (anomaly-free + chiral + AF + 3 поколения + kappa=1/10), собранный в crown-теорему с честной деклассификацией 'consistency, не uniqueness'.
> _Caveat:_ OVER-BRANDED по происхождению: единственность НЕ доказана (нет исчерпывающего перебора по Q), целые 3/10/sin^2=3/13 — идентификации (SinThetaWDerivationStatus), '2n^2'/'SM из distinction' переоценены; шаги = реюз. Ценность в честном аудите, а не новой физике.

---

## #387 - `src/foundation/SortDecidable.v` - score 3 (new-framing)

**The Element/role-limit sort is a total decision procedure on { sqrt n }**

- **Topic.** On the class {sqrt n}, sort_sqrt n = is_square n (Nat.eqb (Nat.sqrt n)^2 n) is total and correct: true iff sqrt n rational (Element), false iff irrational (role-limit); decide_sqrt is a constructive sumbool — no excluded middle.
- **Role.** Self-contained (Arith/Lia). Contrasts GravityH1Decision.v (general sort = halting problem, undecidable) and GeneralSqrt.v (sqrt n rational iff perfect square, there a theorem, here a decision procedure). Answers Q4 of the open agenda.
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith, Lia
- **E/R/R.** _Elements:_ is_square n := Nat.eqb (Nat.sqrt n * Nat.sqrt n) n; decide_sqrt (sumbool); sqrt 4/sqrt 2/sqrt 9. _Roles:_ перфектный квадрат = Element (рациональный корень); не-квадрат = role-limit; decide_sqrt = решающая процедура. _Rules:_ общий сорт неразрешим (halting); на { sqrt n } он тотальная корректная решающая процедура. _P4:_ ДА — сорт делается тотальной решающей процедурой на разрешимом классе. Граница разрешимости = класс, где критерий Element/role-limit ВЫЧИСЛИМ (Nat.sqrt). Один класс; общий сорт остаётся неразрешим.
- **Classical counterpart.** Decidability of 'n is a perfect square' via integer sqrt (Nat.sqrt), and 'sqrt n is rational iff n is a perfect square'. Standard computability; NEW only as the framing that the Element/role-limit SORT becomes a TOTAL decision procedure exactly on a decidable class, contrasting the undecidable general sort.
- **Tags.** foundation, decidability, perfect-square, computability, new-framing

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `is_square/sort_sqrt` | Definition | сорт через целочисленный корень |
| `is_square_iff` | Lemma | корректность: is_square n=true <=> n полный квадрат |
| `sort_element/sort_role_limit` | Lemma | обе стороны границы корректны |
| `decide_sqrt` | Lemma | тотальная решающая процедура (sumbool с доказательством) |
| `sqrt_decidable` | Lemma | конструктивная разрешимость дихотомии (без LEM) |
| `sort_4_element/sort_2_role_limit/sort_9_element` | Lemma | конкретные: sqrt4,sqrt9 Element; sqrt2 role-limit |
| `sort_total_on_decidable_class` | Theorem | капстоун: тотальность+разрешимость на классе |

**Key lemmas (deep):**

- **`decide_sqrt / sort_total_on_decidable_class`** - Genuine содержание = ОБРАМЛЕНИЕ: тот же Element/role-limit сорт, который в общем случае неразрешим (GravityH1Decision = halting), становится ТОТАЛЬНОЙ конструктивной решающей процедурой (sumbool, без LEM) ровно на классе, где критерий вычислим (perfect-square detection через Nat.sqrt). Граница разрешимости = вычислимость критерия на классе. Сама разрешимость perfect-square и связь с рациональностью корня = стандартная computability; новое — постановка как ответ Q4 и контраст с общим сортом. _(decidability, perfect-square, element-role-limit, halting-contrast)_

**Uniqueness - score 3 (new-framing).** Element/role-limit сорт = тотальная конструктивная решающая процедура (без LEM) на разрешимом классе { sqrt n }; граница разрешимости = вычислимость критерия, в контрасте с общим неразрешимым сортом.
> _Caveat:_ Разрешимость perfect-square через Nat.sqrt и 'sqrt n рационален <=> n полный квадрат' — стандартная вычислимость; один класс, общий сорт остаётся неразрешим (halting).

---

## #388 - `src/foundation/SpectralSectors.v` - score 2 (methods)

**Electroweak spectral sectors over Q: sin^2 theta_W = 3/13 = 3 gauge DOF / 13 EW DOF**

- **Topic.** Counts EW = 3 gauge (SU(2)) + 10 metric (D(D+1)/2, D=4) = 13 DOF, with SU(3) (8) level-excluded and U(1) absorbed into metric; computes sin^2 = 3/13, contrasts the wrong inclusion 3/21=1/7.
- **Role.** Self-contained (QArith/List). Part of the sin^2=3/13 cluster; concrete Q DOF arithmetic. Mirrors SingleSourcePrinciple/StableDimension numerically.
- **Counts.** Qed 15 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, Lia, ZArith, List, Lqa
- **E/R/R.** _Elements:_ DOF: gauge 3, metric 10, strong 8, phase 1; EW 13; total gauge 12. _Roles:_ L1 (равный вес на DOF) => смешивание = долевая часть числа DOF. _Rules:_ sin^2 = 3/13; SU(3) исключён из EW (уровень-разделение); U(1) поглощён в метрику. _P4:_ конечный целочисленный счёт DOF над Q; sin^2 = 3/13 = Tr(P_gauge)/Tr(P_EW). P4-нагрузка = арифметика подсчёта; размерности 3,10 ПРЕДПОЛОЖЕНЫ (брендирование).
- **Classical counterpart.** The electroweak mixing sin^2 theta_W and SU(3)xSU(2)xU(1) DOF counts. NEW only as the ToS 'spectral sector' counting sin^2 = Tr(P_gauge)/Tr(P_EW) = 3/13 with SU(3) level-excluded; a BRANDED claim, not standard.
- **Tags.** foundation, sin2, 3/13, weinberg, DOF-counting, over-branded, methods

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `dim_gauge_sector/dim_metric_sector/dim_strong_sector/dim_phase_sector/dim_EW/dim_total_gauge` | Definition | размерности секторов |
| `sin2_spectral/EW_is_13/sin2_is_3_13/total_gauge_12` | Definition/Lemma | EW=13, sin^2=3/13, gauge=12 |
| `strong_excluded/phase_absorbed/sectors_add` | Lemma | SU(3) исключён, U(1) поглощён, сектора складываются |
| `spectral_trace_formula/one_matrix_one_space` | Lemma | трейс-формула; один трансфер-оператор на оба сектора |
| `sin2_wrong/wrong_if_include_SU3` | Definition/Lemma | если включить SU(3): 1/7 /= 3/13 |
| `sin2_ordering/metric_from_spacetime/gauge_from_SU2` | Lemma | упорядочивание; метрика=D(D+1)/2; gauge=2^2-1 |
| `spectral_synthesis/total_DOF/level_separation_concrete` | Lemma | синтез; всего 22 DOF; уровень-разделение |

**Key lemmas (deep):**

- **`sin2_is_3_13 / wrong_if_include_SU3`** - sin^2=3/13 получается как доля 3 gauge DOF из 13 EW DOF (3 gauge + 10 metric), при ПРЕДПОЛОЖЕННОМ исключении SU(3) (level-separation, лишь прокомментировано, не доказано как вынужденное) и поглощении U(1). Контраст 'если включить SU(3) => 1/7' показывает чувствительность к выбору набора секторов. Это та же брендированная претензия 3/13, чей честный статус ('выведено по модулю одной идентификации, не вынуждено') разобран в SinThetaWDerivationStatus.v. Сами DOF-счёты тривиальны. _(sin2, 3/13, DOF-counting, over-branded)_

**Uniqueness - score 2 (methods).** sin^2 theta_W = 3/13 как долевой счёт спектральных секторов (3 gauge / 13 EW DOF) с уровень-исключённым SU(3) и поглощённым U(1).
> _Caveat:_ OVER-BRANDED: 3/13 чувствительно к выбору секторов (включение SU(3) даёт 1/7); исключение SU(3) лишь прокомментировано, размерности 3/10 = идентификации (SinThetaWDerivationStatus). Стандартное смешивание EW, тривиальная арифметика.

---

## #389 - `src/foundation/SpectralSolvability.v` - score 3 (synthesis+observation)

**Coupling spectral role-limit stratified by Galois solvability: surd < radical < radical-inexpressible**

- **Topic.** Stratifies the role-limit side of inter-level coupling spectra into surd (deg 2 golden), radical (deg 3 cbrt2), and radical-INEXPRESSIBLE (deg 5 quintic x^5-x-1, S_5 Galois); machine-checks the 'no rational root' verdicts by candidate evaluation, tags solvability.
- **Role.** Self-contained (QArith/Lia). Direction Delta2; connects the inter-level spectrum thread (H1 / CubicCouplingSpectrum) to the Abel-Ruffini / Galois engine (Part XI GaloisQ23). No-root machine-checked; radical-(in)expressibility cited.
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, Lia, Lqa
- **E/R/R.** _Elements:_ коэффициенты многочленов in Q; рациональные кандидаты-корни; их значения. _Roles:_ характеристический многочлен = спектр связи; группа Галуа = разрешимость; три страта role-limit (surd/radical/radical-inexpressible). _Rules:_ рацион. мода <=> рацион. корень; role-limit стратифицирован по solvability (surd<radical<radical-inexpressible); deg>=5 non-solvable = radical-inexpressible (Abel-Ruffini). _P4:_ role-limit спектра имеет ГЛУБИНУ (solvability-башня); deg-5 квинтика = role-limit, до которого не дотягивается НИ ОДНА конечная radical-башня. No-root машинно; radical-(in)expressibility = цитата. Локализуем, не пересекаем.
- **Classical counterpart.** Galois solvability / Abel-Ruffini: roots expressible by radicals iff the Galois group is solvable; the quintic x^5-x-1 has S_5 Galois group (radical-inexpressible). The rational-root test for monic integer polynomials. NEW only as the OBSERVATION that the inter-level coupling spectral role-limit is stratified by solvability.
- **Tags.** foundation, galois, abel-ruffini, role-limit, spectrum, synthesis+observation

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `p_element/element_has_rational_root` | Definition/Example | Element foil: x^2-3x+2 корень 1 |
| `p_surd2/surd2_at_1/surd2_at_m1` | Definition/Example | golden x^2-x-1: нет рацион. корня (surd) |
| `p_rad3/rad3_at_1/rad3_at_2` | Definition/Example | x^3-2: нет рацион. корня (radical, cbrt2) |
| `p_quintic/quintic_at_1/quintic_at_m1` | Definition/Example | x^5-x-1: нет рацион. корня (radical-inexpressible) |
| `RoleLimitDepth/radical_expressible` | Definition | три страта + предикат radical-выразимости |
| `deg5_not_radical/deg2_is_radical/depths_distinct` | Lemma | deg5 не radical, deg2 radical, страты различны |
| `spectral_solvability_stratification` | Theorem | капстоун: стратификация по разрешимости |

**Key lemmas (deep):**

- **`spectral_solvability_stratification / deg5_not_radical`** - Genuine НОВЫЙ объект = наблюдение, что role-limit спектра связи не единая стена, а БАШНЯ страт по разрешимости Галуа: surd (sqrt5) < radical (cbrt2) < radical-INEXPRESSIBLE (квинтика x^5-x-1 с группой S_5), причём последняя недостижима НИ ОДНОЙ конечной radical-башней (Abel-Ruffini). Машинно проверены лишь 'нет рационального корня' (оценка кандидатов +-1,+-2); разрешимость/Abel-Ruffini = ЦИТАТА из Части XI, не передоказывается. Мост спектр(H1)+Галуа. Сама Abel-Ruffini = классика. _(galois, abel-ruffini, role-limit, solvability, spectrum)_

**Uniqueness - score 3 (synthesis+observation).** НОВЫЙ объект: спектральный role-limit связи стратифицирован по разрешимости Галуа (surd<radical<radical-inexpressible); deg-5 квинтика = role-limit, до которого не дотягивается ни одна radical-башня; мост спектр(H1) <-> Abel-Ruffini.
> _Caveat:_ Машинно лишь 'нет рационального корня' (оценка кандидатов); сама разрешимость и radical-(in)expressibility = цитата Abel-Ruffini/Галуа (Часть XI), классика, не передоказана. Стена локализуется, не пересекается.

---

## #390 - `src/foundation/SphaleronRateDescent.v` - score 3 (new-framing)

**Sphaleron rate's exponential as the canonical non-terminating process (role-limit), over Q**

- **Topic.** Walks BaryogenesisBoundary's SphaleronRate->RoleLimit tag constructively: the exp partial sums Sum x^k/k! are rational (Element), strictly increase for x>0, and NEVER stabilize — the role-limit signature; concrete approximations of e (1,2,5/2).
- **Role.** Self-contained (QArith/Arith/Lia). Branch 2/3 of the baryogenesis boundary (with SphaleronWinding the B-violation face). Parallels surd-Pell convergents and nine_raw (flagship H1).
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, Lqa, Arith, Lia
- **E/R/R.** _Elements:_ factorial, qpow, exp_term, exp_partial (рациональные частичные суммы); приближения e. _Roles:_ частичные суммы = Element-приближения; предел e^x = role-limit (никогда не достигается); показатель E/T = отношение (Element). _Rules:_ частичные суммы строго возрастают и не стабилизируются => процесс не обрывается. _P4:_ ветка сходится в ЯДРО границы финитизации: role-limit = нетерминирующий процесс. Показана НЕТЕРМИНАЦИЯ (не трансцендентность e) — а это и есть критерий role-limit H1. Element-сторона выведена; магнитуда (предел) = стена.
- **Classical counterpart.** The sphaleron rate ~ exp(-E_sph/T); the exponential series Sum x^k/k! and its rational partial sums. NEW only as the framing that exp is the canonical non-terminating process (role-limit), via non-termination (NOT transcendence of e), instancing the finitization boundary H1.
- **Tags.** foundation, exponential, role-limit, non-termination, baryogenesis, new-framing

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `fact/qpow/exp_term/exp_partial` | Definition | факториал, степень, k-й член, частичная сумма |
| `one_over_fact_pos/qpow_pos/exp_term_pos` | Lemma | положительность членов |
| `exp_partial_increasing` | Lemma | частичные суммы строго возрастают (x>0) |
| `exp_partial_never_stabilizes` | Lemma | процесс никогда не стабилизируется (сигнатура role-limit) |
| `exp_partial_e_0/e_1/e_2` | Lemma | приближения e: 1, 2, 5/2 |
| `sphaleron_rate_descent` | Theorem | капстоун: exp = нетерминирующий процесс |

**Key lemmas (deep):**

- **`exp_partial_never_stabilizes`** - Ключевое решение: вместо тяжёлой трансцендентности e файл доказывает НЕТЕРМИНАЦИЮ — ни одна частичная сумма не равна следующей (т.к. строго возрастает положительным членом), что и есть критерий role-limit по финитизационной границе H1. Скорость сфалерона split-ится на {показатель (Element-отношение) + exp (role-limit)}. Element-сторона (суммы, положительность) выведена честно; предел e^x = стена. Сам экспоненциальный ряд и его рациональные частичные суммы = классика; новое = обрамление как канонический нетерминирующий процесс, параллель surd-Pell/nine_raw. _(exponential, role-limit, non-termination, finitization-boundary)_

**Uniqueness - score 3 (new-framing).** Exp скорости сфалерона = канонический нетерминирующий процесс (role-limit): частичные суммы рациональны и строго возрастают, но НИКОГДА не стабилизируются — конструктивный инстанс границы финитизации H1.
> _Caveat:_ Экспоненциальный ряд и его рациональные частичные суммы = классика; доказана лишь нетерминация, НЕ трансцендентность e (честно отмечено); магнитуда (предел) не пересекается.

---

## #391 - `src/foundation/SphaleronWinding.v` - score 2 (methods)

**Sphaleron winding: B-violation (P4 face) as a discrete jump Delta B = 3 Delta N_CS, B-L conserved**

- **Topic.** Realizes the B-violation (Sakharov-1) face as an integer winding jump: one sphaleron gives Delta B = n_gen = 3, B not conserved (P4 face) but B-L conserved (invariant role); the quantum 3 is the L4-derived generation count.
- **Role.** Imports foundation.GenerationsPositReduction (generations_unique, L4_minimal_generations). Fills the P4 (B-violation) face of SakharovERR.v's triad; foreshadows the Phase-4 honest gap (B-L conservation).
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: ZArith, Lia; ToS: foundation.GenerationsPositReduction
- **E/R/R.** _Elements:_ число намотки (Z); скачок Delta N_CS=+-1; Delta B = n_gen * Delta N_CS. _Roles:_ B-нарушение = грань P4 (счёт меняется); B-L = сохраняющаяся инвариантная роль; намотка метит Z-секторы вакуума. _Rules:_ Delta B = 3 Delta N_CS (дискретно, квантовано); B не сохраняется, B-L сохраняется; квант = n_gen (выведено). _P4:_ B-нарушение = грань P4 триады (актуальный счёт меняется), реализованная топологически. Квант Delta B=3 выведен (n_gen из L4). Целочисленность намотки = P4-конечность. B-L сохраняется (Delta B=Delta L) — предвещает SM-разрыв (Фаза 4).
- **Classical counterpart.** The electroweak anomaly / sphaleron: Delta B = n_gen * Delta N_CS, Delta(B-L)=0 (B+L violated, B-L conserved); Chern-Simons winding. Standard baryogenesis. NEW only as the E/R/R reading (B-violation = P4 face) with the quantum 3 = the ToS-derived generation count.
- **Tags.** foundation, sphaleron, baryogenesis, P4-face, methods

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `n_gen/n_gen_is_three/delta_B/delta_L` | Definition/Lemma | n_gen=3; ответ B и L на намотку |
| `sphaleron_delta_B/sphaleron_violates_B/multiple_sphalerons` | Lemma | один сфалерон => Delta B=3/=0; k => 3k |
| `sphaleron_conserves_BminusL` | Lemma | B-L сохраняется (Delta B=Delta L) |
| `adjacent/sphaleron_adjacent/B_change_across_sphaleron` | Definition/Lemma | соседние секторы; Delta B = +-3 через переход |
| `B_quantum_is_generation_count` | Lemma | квант B = выведенный n_gen (L4-минимальность) |
| `sphaleron_winding` | Theorem | капстоун: грань P4 как намоточный скачок |

**Key lemmas (deep):**

- **`B_quantum_is_generation_count / sphaleron_conserves_BminusL`** - Два genuine акцента: (1) квант B-нарушения Delta B=3 НЕ свободен — он равен выведенному числу поколений n_gen (через generations_unique, L4-минимальность), что связывает топологический скачок с distinction-цепью; (2) B-L сохраняется (Delta B=Delta L), и это честно помечено как предвестие Phase-4 разрыва (именно поэтому SM трудно сделать нетто-B). Сама формула Delta B = n_gen Delta N_CS и B-L сохранение = стандартная физика сфалерона; новое = E/R/R-прочтение (B-violation = грань P4) и связь кванта с выведенным n_gen. _(sphaleron, baryogenesis, P4-face, B-violation)_

**Uniqueness - score 2 (methods).** B-нарушение (грань P4 триады Сахарова) реализовано как дискретный намоточный скачок Delta B=3 Delta N_CS, с квантом = ВЫВЕДЕННЫМ числом поколений n_gen и сохранением B-L (предвестие SM-разрыва).
> _Caveat:_ Формула Delta B = n_gen Delta N_CS, B+L-нарушение / B-L-сохранение и Chern-Simons намотка = стандартная физика сфалерона; новое лишь E/R/R-обрамление и связь с выведенным n_gen.

---

## #392 - `src/foundation/SpinFromChirality.v` - score 2 (methods)

**Chirality forces half-integer spin: minimum chiral doublet => spin 1/2**

- **Topic.** Defines spin_quantum(dim)=(dim-1)/2; the minimum faithful chiral rep is 2-component (doublet) giving spin 1/2 (half-integer), while vector-like minimum is a scalar (spin 0); concrete spins for dim 1..4.
- **Role.** Self-contained (QArith/Lia). Sits after ChiralityFromL2.v (left/=right) in the foundation chain; argues spin-1/2 existence from L2.
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, Lia, Lqa
- **E/R/R.** _Elements:_ spin_quantum(dim)=(dim-1)/2; is_half_integer/is_integer; конкретные спины. _Roles:_ L2 (непротиворечие) => хиральность => минимум дублет => спин-1/2. _Rules:_ хиральная материя >=2 компоненты => spin=(dim-1)/2=1/2; вектороподобная => скаляр => spin 0. _P4:_ конечная рациональная связь dim->spin. P4-нагрузка минимальна: 'минимум 2 компоненты' аргументировано (left/=right), но не доказано как вынужденное представление; spin=(dim-1)/2 = определение.
- **Classical counterpart.** Spin quantum number s=(dim-1)/2 from a rep of dimension 2s+1; chiral matter needs >=2 components. Standard rep theory. NEW only as the ToS framing 'L2 (non-contradiction) forces half-integer spin' via the minimum chiral doublet.
- **Tags.** foundation, spin, chirality, methods

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `spin_quantum/is_half_integer/is_integer` | Definition | спин из размерности; полу-/целочисленность |
| `spin_1_is_0/spin_2_is_half/spin_3_is_1/spin_4_is_3_2` | Lemma | конкретные спины 0,1/2,1,3/2 |
| `half_is_half_integer/zero_is_integer/one_is_integer` | Lemma | проверки полу-/целочисленности |
| `min_chiral_dim/chiral_needs_two/min_vectorlike_dim` | Definition/Lemma | мин. хиральная dim=2; вектороподобная=1 |
| `vectorlike_spin_is_zero/chiral_spin_is_half/chiral_spin_half_integer` | Lemma | вектор=>spin0; хираль=>spin1/2 (полуцелый) |
| `spin_from_chirality_synthesis` | Theorem | капстоун: хиральность=>полуцелый спин |

**Key lemmas (deep):**

- **`chiral_spin_half_integer`** - Аргумент: L2 (left/=right) => хиральная материя нуждается в >=2 компонентах => минимальное представление = дублет (dim 2) => spin=(2-1)/2=1/2 (полуцелый), тогда как вектороподобная материя минимизируется до скаляра (spin 0). Genuine = только переобрамление 'L2 порождает полуцелый спин'. Сама связь spin=(dim-1)/2 и spin-статистика = стандартная теория представлений; 'минимум 2 компоненты' лишь аргументировано (counting), не доказано как единственно вынужденное минимальное точное представление. _(spin, chirality, L2, new-framing)_

**Uniqueness - score 2 (methods).** L2 (непротиворечие, left/=right) => хиральность => минимальный дублет => полуцелый спин 1/2, в контрасте с вектороподобным скаляром (spin 0).
> _Caveat:_ spin=(dim-1)/2 и спин-статистика = стандартная теория представлений; 'минимум 2 компоненты' аргументировано counting'ом, не доказано как вынужденное минимальное точное представление.

---

## #393 - `src/foundation/SquareWellThreeFormulas.v` - score 2 (methods)

**Infinite square well as a three-formula instance crossing the finitization boundary**

- **Topic.** First system built on the reified ThreeFormulaMethod + Boundary: E_1=1 (confinement ground), n^2 ladder (Element), and discretizations box2 (disc 4 square => Element {1,3}) vs box3 (disc 8 non-square => role-limit sqrt 2), decided by spectrum_element_iff_square_disc.
- **Role.** Imports foundation.ThreeFormulaMethod + foundation.ThreeFormulaBoundary. Demonstrates the method-as-theorem + boundary criterion on an iconic system. Companion to SHOThreeFormulas.
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, Lqa; ToS: foundation.ThreeFormulaMethod, foundation.ThreeFormulaBoundary
- **E/R/R.** _Elements:_ основание E_1=1; уровни 1,4,9; матрицы дискретизации box2/box3. _Roles:_ n^2-спектральная лестница; Element/role-limit статус каждой дискретизации. _Rules:_ E_n = n^2 E_1 (рациональн., Element); дискретизация Element <=> её disc — полный квадрат. _P4:_ континуум n^2 — Element; дискретизации осциллируют поперёк границы с N; теорема-как-метод работает на каноническом ящике; E_1/=0 = частицу нельзя запереть в покое (различение требует ненулевого основания).
- **Classical counterpart.** Infinite square well (particle in a box): E_n = n^2 E_1, nonzero confinement ground; tridiagonal discrete Laplacian spectra. Standard QM. NEW only as the three-formula-method INSTANCE whose discretizations cross the finitization (square-discriminant) boundary.
- **Tags.** foundation, square-well, three-formula, finitization-boundary, methods

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `box_E/box_ground/box_E2/box_E3` | Definition/Lemma | уровни n^2; основание E_1=1 |
| `box_law_2/box_law_3` | Lemma | закон n^2: E_2=4E_1, E_3=9E_1 |
| `box2/box2_disc/box2_element/box2_eigenvalue/box2_spectrum_element` | Definition/Lemma | N=2 лапласиан: disc 4 квадрат => Element {1,3} |
| `box3/box3_disc/box3_eigenvalue_iff_square8` | Definition/Lemma | N=3: disc 8 => Element <=> is_square 8 (role-limit sqrt2) |
| `square_well_three_formula` | Theorem | капстоун: метод + граница на ящике |

**Key lemmas (deep):**

- **`box3_eigenvalue_iff_square8`** - Демонстрация финитизационной границы в действии: континуумный спектр n^2 рационален (Element), но КОНЕЧНЫЕ дискретизации тридиагонального лапласиана осциллируют поперёк границы — N=2 (disc 4 квадрат) Element {1,3}, а N=3 (disc 8) имеет рациональное собственное значение <=> is_square 8, т.е. role-limit (sqrt 2), по тому же критерию spectrum_element_iff_square_disc из ThreeFormulaBoundary. Genuine = применение переиспользуемого метода+критерия к каноническому ящику. Сама физика ящика (n^2, нулевое основание) = стандарт; критерий импортирован. _(square-well, three-formula, finitization-boundary, discriminant)_

**Uniqueness - score 2 (methods).** Бесконечная яма как инстанс реифицированного метода-как-теоремы: континуум n^2 = Element, а дискретизации (N=2 Element, N=3 role-limit sqrt2) осциллируют поперёк финитизационной границы по импортированному disc-критерию.
> _Caveat:_ Физика ящика (E_n=n^2, ненулевое основание, тридиагональный лапласиан) = стандартная КМ; и метод, и disc-критерий импортированы из ThreeFormulaMethod/Boundary, файл лишь применяет.

---

## #394 - `src/foundation/StabilityDimensionSynthesis.v` - score 2 (methods)

**Synthesis: D=4 + eta>0 + SM anomaly conditions (Tier-3 chain)**

- **Topic.** Assembles StableDimension (D=4, kappa=1/10, sin^2=3/13), EtaFromLattice (CP phase => eta>0), and AnomalyExhaustive (SM anomaly-free) into one derivation chain, with an honest 'what is derived vs modeled' note.
- **Role.** Thin synthesis file importing foundation.StableDimension, EtaFromLattice, AnomalyExhaustive. Pure re-export/conjunction of already-proved results (only 3 Qed).
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, Lia, ZArith, Lqa; ToS: foundation.StableDimension, foundation.EtaFromLattice, foundation.AnomalyExhaustive
- **E/R/R.** _Elements:_ tier3_synthesis; derivation_chain. _Roles:_ объединяет StableDimension + EtaFromLattice + AnomalyExhaustive. _Rules:_ D=4 выведено, eta>0 выведено, SM единственно среди протестированных альтернатив. _P4:_ тонкий синтез: конъюнкция уже доказанных результатов. P4-нагрузка минимальна; 'what_is_derived' честно метит МОДЕЛИРУЕМОЕ (J(K)=1/(1+K)^3 = заглушка, точное eta, форма r).
- **Classical counterpart.** Combines the Ehrenfest/Tangherlini D=4 stability argument, CP/Jarlskog => eta>0, and SM anomaly cancellation. All standard physics; NEW only as a thin synthesis tying three derived foundation results together.
- **Tags.** foundation, synthesis, D=4, eta, over-branded, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `derivation_chain` | Theorem | D=4, kappa=1/10, eta>0 при K=0, SM-аномалия |
| `tier3_synthesis` | Theorem | полный синтез: размерность + асимметрия + единственность SM |
| `what_is_derived` | Theorem | явно: что ВЫВЕДЕНО (D=4, kappa, sin^2, eta>0, SM) |

**Key lemmas (deep):**

- **`what_is_derived`** - Файл — тонкая конъюнкция (3 Qed) трёх готовых результатов с ЧЕСТНЫМ комментарием, отделяющим DERIVED (D=4, kappa=1/10, sin^2=3/13, eta>0, SM-аномалия) от MODELED (Jarlskog J(K)=1/(1+K)^3 — заглушка; точное eta нуждается в CKM; форма r). Ценность инфраструктурная: связывает кластер, но не добавляет математики. Все компоненты (включая брендированные D=4/sin^2=3/13/eta>0) импортированы. _(synthesis, D=4, eta, honesty-note)_

**Uniqueness - score 2 (methods).** Синтез цепи Tier-3: D=4, kappa=1/10, sin^2=3/13, eta>0 и SM-аномалия объединены в одну деривационную цепь с честной пометкой derived vs modeled.
> _Caveat:_ Тонкая конъюнкция (3 Qed) уже доказанных результатов; математики не добавляет. Компоненты брендированы (D=4 из стабильности, sin^2=3/13 = идентификация); J(K) явно помечено как заглушка.

---

## #395 - `src/foundation/StableDimension.v` - score 2 (methods)

**Why D_spatial = 3 (stability vs SU(2)) => D=4, kappa=1/10, sin^2 theta_W = 3/13**

- **Topic.** Pinches D_spatial=3 between orbital stability / hydrogen bound states (D<=3) and SU(2) needing D>=3, so D_spacetime=4; then derives n_metric=D(D+1)/2=10, kappa=1/10, r=3/10, sin^2=3/13.
- **Role.** Self-contained (QArith/Lia). Source of D=4 and the kappa/sin^2 chain reused by StabilityDimensionSynthesis and the broader sin^2=3/13 cluster.
- **Counts.** Qed 17 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, Lia, ZArith, Lqa
- **E/R/R.** _Elements:_ stable_orbits; min_dim_for_SU2; D_spacetime_derived; n_metric; kappa; sin^2. _Roles:_ орбитальная стабильность => D<=3; SU(2) => D>=3; => D_spatial=3 уникально. _Rules:_ D_spatial=3, D_spacetime=4, n_metric=10, kappa=1/10, r=3/10, sin^2=3/13. _P4:_ конечный целочисленный вывод D=3 из зажима двух условий. P4-нагрузка: stable_orbits и SU(2)-нужда заданы как ПРЕДИКАТЫ (D<=3 / >=3), а не доказаны из динамики; следствия kappa/sin^2 = арифметика над предположенными целыми.
- **Classical counterpart.** Ehrenfest (1917) orbital stability and Tangherlini (1963) hydrogen bound states: stable orbits / bound states exist iff D_spatial <= 3; SU(2)/SO(3) needs D >= 3. Standard dimensional-stability arguments. NEW only as the ToS chain D=4 => n_metric=10 => kappa=1/10 => sin^2=3/13.
- **Tags.** foundation, dimension, D=4, sin2, 3/13, over-branded, methods

**Lemmas (8):**

| name | kind | role |
|---|---|---|
| `stable_orbits/D1..D5_stable/unstable` | Definition/Theorem | стабильные орбиты <=> D<=3 (Эренфест) |
| `force_exponent/force_exp_at_3/at_4` | Definition/Lemma | показатель силы D-1 |
| `hydrogen_bound_states/hydrogen_D3/D4_fails` | Definition/Theorem | связанные состояния <=> D<=3 (Tangherlini) |
| `min_dim_for_SU2/SU2_needs_at_least_3` | Definition/Theorem | SU(2)/SO(3) => D>=3 |
| `D_spatial_unique/D_spacetime_derived/D_is_4` | Theorem | D_spatial=3 уникально => D=4 |
| `n_metric_derived/n_metric_is_10/kappa_from_dimension/kappa_is_one_tenth` | Definition/Theorem | n_metric=10, kappa=1/10 |
| `su2_generators/r_from_dimension/r_is_3_over_10/sin2_from_dimension/sin2_is_3_over_13` | Definition/Theorem | r=3/10, sin^2=3/13 |
| `dimension_chain_complete` | Theorem | капстоун: вся цепь D=4 -> sin^2 |

**Key lemmas (deep):**

- **`D_spatial_unique / sin2_is_3_over_13`** - Цепь: орбитальная стабильность + связанные состояния водорода (Эренфест/Tangherlini, D<=3) ЗАЖИМАЮТ с SU(2)-нуждой (D>=3) => D_spatial=3, D=4 => n_metric=D(D+1)/2=10 => kappa=1/10 => r=3/10 => sin^2=3/13. Genuine = переобрамление 'D=4 выведено, не вход'. Честно: stable_orbits и SU(2)-нужда заданы как ПРЕДИКАТЫ (D<=3, D>=3 по комментарию-физике), а не доказаны из динамики орбит/Шрёдингера; sin^2=3/13 = та же брендированная идентификация (SinThetaWDerivationStatus). _(dimension, D=4, sin2, 3/13, over-branded)_

**Uniqueness - score 2 (methods).** D_spatial=3 зажато между стабильностью орбит/водорода (D<=3) и SU(2) (D>=3) => D=4, откуда n_metric=10, kappa=1/10, sin^2=3/13 как следствие.
> _Caveat:_ OVER-BRANDED: stable_orbits и SU(2)-нужда заданы предикатами (D<=3/>=3), не доказаны из динамики; Эренфест/Tangherlini = классика; sin^2=3/13 = идентификация (SinThetaWDerivationStatus), не вынужденная.

---

## #396 - `src/foundation/StatusFromERR.v` - score 2 (methods)

**Status machine: L5-resolution assigns a unique PrimaryMax (argmax by weight, leftmost tiebreak)**

- **Topic.** Given entities with weights+gates, find_primary folds with compare_entities (higher weight, then lower legacy_idx = L5), assign_status labels PrimaryMax/SecondaryMax/Candidate/Invalid; proves uniqueness, stability (Invalid never primary), zero-gate law.
- **Role.** Imports foundation.ERRProcess (ERREntity, Status, process_entity). Coq mirror of regulus/core/status_machine.py; the L5-resolution / status assignment layer over ERRProcess.
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, Lia, ZArith, List, PeanoNat, Bool, Lqa; ToS: foundation.ERRProcess
- **E/R/R.** _Elements:_ compare_entities; find_primary; assign_status; конкретные сущности A/B/C. _Roles:_ PrimaryMax = уникальный победитель по L5 (макс вес, при ничьей — наименьший legacy_idx). _Rules:_ сравнение веса + tie-break legacy_idx = L5-Resolution; gate=0 => Invalid; Invalid не может быть PrimaryMax. _P4:_ E/R/R НЕ статическая тройка, а ПРОЦЕСС: свойства -> gate -> вес -> статус. Конечный детерминированный выбор без AC (argmax-by-index). Три инварианта машинно-проверены.
- **Classical counterpart.** A weight-then-tiebreak argmax (leftmost-among-max) selection with uniqueness/stability invariants; mirrors regulus status_machine.py. Standard deterministic selection without choice. NEW only as the E/R/R 'status machine' (Element->gate->weight->Role) realizing L5-resolution.
- **Tags.** foundation, status-machine, L5, argmax, regulus, methods

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `compare_entities/find_primary/assign_status` | Definition | L5-сравнение; поиск примари; назначение статуса |
| `entity_A/B/C/test_entities/weight_A/B/C` | Definition/Lemma | пример: веса 45,28,0(invalid) |
| `primary_is_A/A_is_primary/B_is_candidate/C_is_invalid` | Lemma | A побеждает; статусы назначены |
| `uniqueness` | Theorem | инвариант 1: не более одного PrimaryMax |
| `stability` | Theorem | инвариант 2: Invalid не может быть PrimaryMax |
| `zero_gate_implies_invalid` | Theorem | инвариант 3: gate=0 => Invalid |
| `status_from_err_synthesis` | Theorem | капстоун: пример + инварианты |

**Key lemmas (deep):**

- **`uniqueness / status_from_err_synthesis`** - Реализует детерминированную argmax-выборку (макс вес, при ничьей leftmost по legacy_idx = L5-resolution) с тремя машинно-проверенными инвариантами: единственность PrimaryMax, стабильность (Invalid никогда не примари), zero-gate. Зеркало regulus status_machine.py. Genuine = E/R/R-обрамление 'E/R/R = процесс свойства->gate->вес->статус, Rules определяют Roles'. Сам leftmost-argmax-с-tie-break = стандартный детерминированный выбор без AC (родня argmax-by-index из EVT_idx); инфраструктура/мост к Regulus. _(status-machine, L5, argmax, regulus-bridge)_

**Uniqueness - score 2 (methods).** Status-машина: L5-resolution назначает уникальный PrimaryMax (argmax по весу, leftmost tie-break) с тремя машинно-проверенными инвариантами; зеркало regulus status_machine.py, E/R/R как процесс.
> _Caveat:_ Leftmost-argmax-с-tie-break = стандартный детерминированный выбор без AC; инварианты тривиальны; ценность — мост к Regulus и E/R/R-обрамление, не новая математика.

---

## #397 - `src/foundation/SU3Minimality.v` - score 2 (methods)

**Depth -> gauge group for all three depths: SU(2), SU(3), U(1), total 12 generators**

- **Topic.** Maps nesting depth to gauge dim via structure_dim (2,3,1) and gauge_dim (n^2-1 or 1): depth 0->3 (SU(2)), 1->8 (SU(3)), 2->1 (U(1)), summing to 12; argues finite groups too small.
- **Role.** Self-contained (Lia/PeanoNat). Recovers the SM gauge dimensions from nesting depth; companion to NestedDistinction/SMConsistency.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Lia, PeanoNat
- **E/R/R.** _Elements:_ structure_dim; gauge_dim; sym_group_order. _Roles:_ минимальная связная группа Ли, точно действующая на C^n. _Rules:_ d=0->SU(2), d=1->SU(3), d=2->U(1); всего 3+8+1=12; конечные группы слишком малы. _P4:_ конечный целочисленный счёт размерностей. P4-нагрузка: 'минимальная связная группа Ли' и 'почему не SO/U/конечные' лишь ПРОКОММЕНТИРОВАНЫ; gauge_dim — заданная функция, минимальность не доказана как теорема.
- **Classical counterpart.** SU(n) (n>=2) / U(1) as minimal connected Lie group acting faithfully unitarily on C^n; dim SU(n)=n^2-1; SM gauge dims 3+8+1=12. Standard Lie theory. NEW only as the ToS depth->gauge-group map (d=0->SU(2), d=1->SU(3), d=2->U(1)).
- **Tags.** foundation, gauge-group, SU3, standard-model, over-branded, methods

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `structure_dim/gauge_dim/sym_group_order` | Definition | глубина->структурная dim->gauge dim; порядок симметрической группы |
| `depth0_gives_SU2/depth1_gives_SU3/depth2_gives_U1` | Lemma | d=0->3, d=1->8, d=2->1 |
| `total_gauge_dim/SM_gauge_group_recovered` | Lemma | сумма = 12 (SM) |
| `finite_groups_too_small` | Lemma | конечные группы меньше gauge dim |
| `structure_dims` | Lemma | структурные размерности 2,3,1 |
| `SU3_minimality_synthesis` | Theorem | капстоун: depth->группа для всех глубин |

**Key lemmas (deep):**

- **`SU3_minimality_synthesis / finite_groups_too_small`** - Сопоставляет глубину вложения с размерностью gauge-группы: d=0->SU(2)(3), d=1->SU(3)(8), d=2->U(1)(1), сумма 12 = SM. 'Минимальность' аргументирована лишь комментарием (конечные группы дискретны/не связны, SO real, U(n) double-counts фазу) + проверкой sym_group_order < gauge_dim для пары случаев; сама gauge_dim — ЗАДАННАЯ кусочная функция, минимальность как теорема НЕ доказана. Это та же брендированная 'SM gauge group из distinction'-линия. dim SU(n)=n^2-1 = стандартная теория Ли. _(gauge-group, SU3, minimality, over-branded)_

**Uniqueness - score 2 (methods).** Карта глубина->gauge-группа: d=0->SU(2), d=1->SU(3), d=2->U(1), сумма 12 = SM gauge group, восстановленная из вложенного различения.
> _Caveat:_ OVER-BRANDED: gauge_dim = заданная кусочная функция; 'минимальная связная группа Ли' и исключение SO/U(n)/конечных лишь прокомментированы, не доказаны; dim SU(n)=n^2-1 = стандартная теория Ли.

---

## #398 - `src/foundation/TeleportationCarrierSwap.v` - score 3 (new-framing)

**Teleportation as a carrier swap over Q: exact recovery for all states/outcomes, move-not-copy**

- **Topic.** Models a qubit as (alpha,beta) over Q, the four Paulis as integer matrices; proves teleportation_recovers (Bob's outcome-selected correction recovers |psi> exactly for ALL inputs/outcomes), state-preserving carrier swap, and bits-essential (wrong correction fails).
- **Role.** Self-contained (QArith/Lqa). Completes the input->output identity SuperdenseCoding only hinted; base for TeleportationResourceNoClone.v. Metaphysics-hint 2 ('system passes into system').
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, Lqa
- **E/R/R.** _Elements:_ носители (кубиты/атомы) A и B — РАЗНЫЕ Элементы; амплитуды (alpha,beta) = содержание. _Roles:_ 'быть \|psi>' = Роль (внешний наблюдаемый класс, P3), не вещество; 2 бита = селектор Роли. _Rules:_ P1 запутанность + L5 измерение + Паули-коррекция (инволюция) + L2 вход разрушается (перенос-НЕ-копия) + классический канал (нет FTL). _P4:_ идентичность телепортируемой системы — по P3 (внешний класс = амплитуды), НЕ по Элементу. 'Переход системы в систему' = переназначение Роли \|psi> с носителя A на B; ничто материальное не летит (летят 2 бита). Формализую СТРУКТУРУ, НЕ реализуемость макротелепортации.
- **Classical counterpart.** Quantum teleportation protocol: Bell measurement + Pauli correction recovers an arbitrary qubit; no-cloning (move not copy); classical channel essential (no FTL). Standard quantum information. NEW only as the complete input->output identity over Q + the E/R/R 'carrier swap' (Role re-assigned to a fresh Element) reading.
- **Tags.** foundation, teleportation, quantum-info, carrier-swap, new-framing

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `qstate/qst_eq/qst_eq_refl` | Definition/Lemma | кубит-состояние; равенство по наблюдаемым (P3) |
| `pI/pX/pZ/pXZ/pZX` | Definition | четыре Паули как целочисленные матрицы |
| `Outcome/bob_pre/bob_correct` | Definition | 2 бита; пред-состояние Боба; коррекция |
| `teleportation_recovers` | Theorem | полная identity: коррекция восстанавливает \|psi> для всех входов/исходов |
| `Located/teleport/teleport_preserves_state/sets_carrier/swaps_element` | Record/Definition/Lemma | носитель; сохранение состояния; смена Элемента |
| `correction_needs_bits` | Lemma | неверная коррекция НЕ восстанавливает (биты существенны, нет FTL) |
| `teleport_example/teleportation_is_carrier_swap` | Example/Theorem | конкретный перенос + капстоун |

**Key lemmas (deep):**

- **`teleportation_recovers / teleportation_is_carrier_swap`** - Genuine = полная identity протокола над Q (которую SuperdenseCoding лишь намекала): для ЛЮБОГО входа (alpha,beta) и КАЖДОГО из 4 исходов Боба коррекция точно восстанавливает \|psi> (Паули = целочисленные биекции, sqrt2 живёт лишь в норме Bell и сокращается). Плюс E/R/R-прочтение: сохраняется СОСТОЯНИЕ (внешний класс P3), а НОСИТЕЛЬ (Element) меняется — 'переход системы в систему'; correction_needs_bits = биты существенны (нет FTL). Честно: формализует СТРУКТУРУ протокола, не реализуемость и не 'перенос сущности'. Сам протокол телепортации = стандарт. _(teleportation, carrier-swap, P3-identity, quantum-info)_

**Uniqueness - score 3 (new-framing).** Полная identity телепортации над Q (точное восстановление для всех входов/4 исходов, перенос-не-копия, биты-существенны), которую SuperdenseCoding лишь намекала, + E/R/R-прочтение 'carrier swap' (та же Роль/состояние P3 на новом Элементе).
> _Caveat:_ Сам протокол телепортации, no-cloning и существенность классического канала = стандартная квантовая информатика; формализуется СТРУКТУРА, НЕ реализуемость макротелепортации и НЕ 'перенос сущности'.

---

## #399 - `src/foundation/TeleportationResourceNoClone.v` - score 3 (new-framing)

**Teleportation: entanglement necessary + no-cloning consistency from one structural fact**

- **Topic.** From psi_blind_fails (a psi-blind output can't equal two distinct states) derives: the quantum half is psi-sighted (bob_pre injective), classical-alone fails (finite channel can't carry continuum => entanglement necessary), and Alice keeps a psi-blind record (move not copy, consistent with no-cloning).
- **Role.** Imports foundation.TeleportationCarrierSwap (qstate, qst_eq, bob_pre, Outcome). Deepens metaphysics-hint 2; lightly fills the 'entanglement necessary' / no-cloning-consistency gap.
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, Lqa; ToS: foundation.TeleportationCarrierSwap
- **E/R/R.** _Elements:_ 2 классических бита (конечный алфавит, 4 значения) vs квантовая половинка (континуум); пост-состояние Алисы vs состояние Боба. _Roles:_ бит = выбор паулиевской рамки (конечная Роль); квантовая половинка = носитель \|psi> (континуум); пост-Алиса = psi-слепая запись; Боб = \|psi>. _Rules:_ psi_blind_fails (psi-слепой выход /= двум разным \|psi>); bob_pre инъективно (psi-зрячий канал); L2 no-cloning — перенос (один носитель), не клон (два). _P4:_ континуум \|psi> нельзя протолкнуть через 4-значный классический канал => запутанность НЕОБХОДИМА; psi-слепая запись Алисы не держит \|psi> для всех => один носитель = перенос, согласуется с L2. Формализую СТРУКТУРНУЮ необходимость, НЕ полную Holevo-теорему.
- **Classical counterpart.** Why entanglement is necessary for teleportation (finite classical channel cannot carry the continuum) and consistency with no-cloning (the protocol moves, not copies). Standard quantum information (related to Holevo/LOCC). NEW only as a light structural proof from one fact (psi-blind output can't track two distinct states).
- **Tags.** foundation, teleportation, entanglement, no-cloning, quantum-info, new-framing

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `qst_eq_sym/qst_eq_trans` | Lemma | qst_eq — эквивалентность |
| `psi_blind_fails` | Lemma | единый фикс. выход не может быть равен двум разным состояниям |
| `bob_pre_injective` | Lemma | квантовая половинка psi-зряча (Паули — биекции) |
| `classical_recover/classical_alone_fails/classical_alone_fails_concrete` | Definition/Theorem/Corollary | классика-в-одиночку не восстанавливает (запутанность необходима) |
| `alice_post/alice_post_psi_blind/teleport_consistent_no_cloning` | Definition/Lemma/Theorem | запись Алисы psi-слепа => перенос, согласуется с no-cloning |
| `teleportation_resource_and_noclone` | Theorem | капстоун: ресурс необходим + no-cloning |

**Key lemmas (deep):**

- **`psi_blind_fails / classical_alone_fails`** - Один структурный факт (psi_blind_fails: psi-слепой выход не может быть qst_eq двум разным состояниям, по транзитивности) порождает ОБА вывода: (a) чисто классическая реконструкция g(outcome) psi-слепа => конечный 4-значный канал не несёт континуум => запутанность НЕОБХОДИМА (контраст: bob_pre инъективно = psi-зрячий квантовый канал); (b) пост-измерительная запись Алисы psi-слепа => \|psi> у одного носителя = перенос, согласуется с no-cloning (L2). Genuine = лёгкое структурное обрамление. Честно: НЕ полная info-теоретическая Holevo-невозможность и НЕ реализуемость. Необходимость запутанности и no-cloning = стандарт. _(teleportation, entanglement-necessity, no-cloning, structural)_

**Uniqueness - score 3 (new-framing).** Из ОДНОГО факта (psi-слепой выход не различает два состояния) следует и необходимость запутанности (конечный классический канал не несёт континуум), и согласованность с no-cloning (перенос-не-копия).
> _Caveat:_ Необходимость запутанности и no-cloning = стандартная квантовая информатика; формализуется СТРУКТУРНАЯ необходимость (конечное vs континуум), НЕ полная Holevo-теорема невозможности и НЕ реализуемость.

---

## #400 - `src/foundation/ThermoArrowAudit.v` - score 3 (synthesis+observation)

**Thermodynamics / arrow-of-time audit: counting structure derived, low-entropy past posited**

- **Topic.** Machine-checks the counting structure (binom profile 1,4,6,4,1; peak 6; total 16; typicality peak beats tails) as Derived, classifies the low-entropy past as a PositedBoundary (the H1 wall), and credits P4 succession with a derived GENERATIVE arrow (direction, not magnitude).
- **Role.** Audit file (Arith/Lia/List). Part G of the physics volume; sibling of the Lambda/eta free-magnitude (H1) audits. ToS localizes, not solves, the arrow problem.
- **Counts.** Qed 14 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith, Lia, List
- **E/R/R.** _Elements:_ binom-кратность, профиль 1,4,6,4,1, пик; классификация Claim/Status. _Roles:_ энтропия = СЧЁТ; равновесие = пик типичности; стрела = генеративная (выведена) vs термодинамическая-магнитуда (посит). _Rules:_ второй закон = огрублённая кратность не убывает при типичной эволюции; стрела = направление генеративного порядка P4 (LS необратимо). _P4:_ counting-СТРУКТУРА ВЫВЕДЕНА (энтропия=счёт, равновесие=пик, типичность); но counting даёт ГДЕ равновесие, не ЧТО система движется к нему — нужен низкоэнтропийный СТАРТ = гипотеза прошлого = ГРАНИЧНОЕ УСЛОВИЕ (не закон) = стена H1. P4 даёт генеративную стрелу (НАПРАВЛЕНИЕ, не магнитуду). ToS не решает стрелу — локализует.
- **Classical counterpart.** Boltzmann statistical mechanics: S=log W (entropy as multiplicity count), equilibrium = max-multiplicity macrostate, typicality; the Boltzmann/Penrose 'past hypothesis' (low-entropy boundary condition). HONESTY-AUDIT of what ToS derives vs posits about the arrow of time.
- **Tags.** foundation, arrow-of-time, entropy, thermodynamics, honesty-audit, synthesis+observation

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `binom/binom_gt` | Definition/Lemma | биномиальная кратность; ноль выше диагонали |
| `profile_0..profile_4` | Lemma | 4-битный профиль 1,4,6,4,1 |
| `equilibrium_is_peak/peak_strict/total_configs/typicality_peak_beats_tail` | Lemma | равновесие = пик; пик строго доминирует; сумма 16; типичность |
| `Claim/Status/claim_status/all_claims/is_derived` | Definition | классификация утверждений derived/posited |
| `n_derived/the_one_posit/structure_all_derived` | Lemma | 3 из 4 выведены; единственный посит = низкоэнтропийное прошлое |
| `thermo_arrow_audit` | Theorem | капстоун аудита |

**Key lemmas (deep):**

- **`thermo_arrow_audit / the_one_posit`** - Честный аудит стрелы времени: counting-структура (энтропия=log кратности, равновесие=пик профиля 1,4,6,4,1, типичность пик>хвосты) ВЫВЕДЕНА машинно — чистая комбинаторика; НО counting даёт лишь ГДЕ равновесие, не движение к нему — для движения нужен низкоэнтропийный старт = гипотеза прошлого = ГРАНИЧНОЕ УСЛОВИЕ, не закон = та же стена H1 (как Lambda, eta). Тонкий честный актив: P4-преемство (LS необратимо) даёт ГЕНЕРАТИВНУЮ стрелу — направление, но не магнитуду термоградиента. Итог: 3 из 4 выведены, 1 посит; ToS ЛОКАЛИЗУЕТ, не решает. Ценность = сам аудит и явная демаркация. _(arrow-of-time, entropy, honesty-audit, past-hypothesis)_

**Uniqueness - score 3 (synthesis+observation).** Аудит стрелы времени: counting-структура (энтропия=счёт, равновесие=пик, типичность) ВЫВЕДЕНА; низкоэнтропийное прошлое = ПОСТУЛИРОВАННОЕ граничное условие (стена H1); P4 даёт генеративную стрелу (направление). ToS локализует, не решает.
> _Caveat:_ S=log W, равновесие=max-кратность, гипотеза прошлого = классическая статфизика (Больцман/Пенроуз); генеративная стрела даёт направление, НЕ магнитуду; проблема стрелы НЕ решена, лишь честно локализована.

---

## #401 - `src/foundation/ThetaFromL2L3.v` - score 3 (new-framing)

**theta=1 is a THEOREM from L2+L3: exact round trip => theta^2=1 => theta=1**

- **Topic.** Models the connection as theta*i (i = 2x2 [[0,-1],[1,0]], i^2=-I); L2+L3 require an EXACT negation round trip (theta i)^2=-I, forcing theta^2=1 and (with theta>0) theta=1; theta<1 leaves a gap (L3), theta>1 overlap (L2). Then sin^2=3/13 is deductive given the chain.
- **Role.** Self-contained (QArith/Qabs). Supplies the forced theta=1 subtheorem reused by SinThetaWDerivationStatus.v (pillar 1) and the broader sin^2=3/13 cluster. The 'missing link' de-postulating theta=1.
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, Qabs, Lia, ZArith, Lqa
- **E/R/R.** _Elements:_ связность theta; круговой обход; i как 2x2 матрица; theta^2. _Roles:_ L2 (исключающее) + L3 (исчерпывающее) => полное бинарное разбиение => точный обход => theta^2=1 => theta=1. _Rules:_ если связь=theta*i, то (theta i)^2=-theta^2 I; L2+L3 требуют (theta i)^2=-I; => theta^2=1; theta>0 => theta=1. _P4:_ theta=1 теперь ТЕОРЕМА, не постулат. theta<1 = обход неполон (зазор, нарушает L3); theta>1 = перелёт (перекрытие, нарушает L2). Конечная рациональная алгебра. Сама i^2=-I и theta^2=1=>theta=1 = элементарны; новое = их подача как следствия L2+L3.
- **Classical counterpart.** The fact that a complex structure squares to -I (i^2=-1) and that a positive scalar theta with theta^2=1 forces theta=1. Elementary algebra. NEW only as the ToS argument that L2+L3 (complete exclusive binary partition) force theta=1, turning the unit-strength postulate into a theorem (feeding sin^2=3/13).
- **Tags.** foundation, theta, L2L3, sin2, 3/13, new-framing

**Lemmas (8):**

| name | kind | role |
|---|---|---|
| `i_00/i_01/i_10/i_11/i_sq_00/01/10/11` | Definition/Lemma | i как [[0,-1],[1,0]]; i^2 покомпонентно |
| `i_squared_is_neg_identity` | Theorem | i^2=-I: обход = точное отрицание |
| `scaled_sq_00/scaled_sq_11` | Lemma | (theta i)^2 диагональ = -theta^2 |
| `theta_squared_is_one` | Theorem | L2+L3 (точный обход) => theta^2=1 |
| `theta_is_one` | Theorem | theta>0, theta^2=1 => theta=1 |
| `L2_L3_force_theta_one` | Theorem | одношагово: L2+L3 => theta=1 (реюзится как опора 1) |
| `theta_less_than_one_gap/theta_greater_than_one_overlap` | Lemma | theta<1 зазор (L3); theta>1 перекрытие (L2) |
| `sin2_is_deductive` | Theorem | капстоун: вся цепь L2+L3 -> sin^2=3/13 дедуктивна |

**Key lemmas (deep):**

- **`L2_L3_force_theta_one / sin2_is_deductive`** - Genuine = переобрамление ранее постулированного 'бинарное различение имеет единичную силу theta=1' в ТЕОРЕМУ: моделируя связь как theta*i и требуя точного отрицательного обхода (theta i)^2=-I (мотивированного полнотой L3 и исключительностью L2), получаем theta^2=1, и при theta>0 — theta=1; theta<1 даёт зазор (нарушает L3), theta>1 перекрытие (нарушает L2). Это и есть 'опора 1' честного аудита sin^2 (SinThetaWDerivationStatus). Сама алгебра (i^2=-I; positive theta с theta^2=1 => 1) элементарна; нагрузка несёт ИНТЕРПРЕТАЦИЯ обхода как L2+L3, а финальный sin^2=3/13 остаётся идентификацией (моста), не вынужден. _(theta, L2L3, sin2, new-framing)_

**Uniqueness - score 3 (new-framing).** theta=1 переведено из постулата в ТЕОРЕМУ: моделируя связь как theta*i и требуя точного обхода (theta i)^2=-I (полнота L3 + исключительность L2), theta^2=1 и theta>0 => theta=1 — 'опора 1' честного вывода sin^2.
> _Caveat:_ Сама алгебра (i^2=-I; positive theta, theta^2=1 => theta=1) элементарна; нагрузка — в ИНТЕРПРЕТАЦИИ обхода как L2+L3, не в математике. Финальный sin^2=3/13 остаётся идентификацией (моста), НЕ вынужден (SinThetaWDerivationStatus).

---

## #402 - `src/foundation/ThreeFormulaBoundary.v` - score 3 (new-framing)

**The three-formula R-formula (spectrum) IS the finitization boundary: Element iff square discriminant**

- **Topic.** Proves complete_square (4 char_poly = (2x-tr)^2 - disc) and the boundary theorem spectrum_element_iff_square_disc; two faces — real/hyperbolic (surd engine: diag23 Element, Fibonacci sqrt5, Pell sqrt2) and elliptic (disc<0 => no real eigenvalue, trace/Niven engine, SHO companion).
- **Role.** Imports foundation.ThreeFormulaMethod (Mat2, char_poly, disc, tr, det, companion, is_square). Companion to ThreeFormulaMethod; reused by SquareWellThreeFormulas.v. Bridge from Part A to H1; mirrors the reduction-atlas discriminant criterion.
- **Counts.** Qed 19 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, Lqa; ToS: foundation.ThreeFormulaMethod
- **E/R/R.** _Elements:_ конкретные спектры (diag, Фибоначчи, Пелля, SHO-компаньон) по обе стороны границы. _Roles:_ слот 'статус спектра' (Element vs role-limit) назначается вердиктом дискриминанта/следа. _Rules:_ спектр Element <=> disc полный квадрат (вещественная грань); эллиптика (disc<0) — нет веществ. собств. значения, конечный порядок по СЛЕДУ (Niven). _P4:_ спектр — место, где метод покидает Q; role-limit = (tr+-sqrt disc)/2 как Коши-процесс, ИМЕНУЕТСЯ не строится; те же движки disc/след, что в атласе (мост Часть A -> H1).
- **Classical counterpart.** For a 2x2 matrix the eigenvalues (tr +- sqrt(disc))/2 are rational iff disc is a perfect square; negative disc => no real eigenvalue. Standard linear algebra / the quadratic discriminant. NEW only as locating the three-formula method's R-formula (spectrum) ON the finitization boundary (Element iff square disc), bridging Part A to Tom II's H1.
- **Tags.** foundation, finitization-boundary, discriminant, spectrum, three-formula, new-framing

**Lemmas (9):**

| name | kind | role |
|---|---|---|
| `complete_square` | Lemma | мост: 4 char_poly = (2x-tr)^2 - disc |
| `eigenvalue_forces_square/square_disc_eigenvalue` | Lemma | рацион. собств. значение <=> disc квадрат (вперёд/назад) |
| `spectrum_element_iff_square_disc/spectrum_role_limit_iff_nonsquare` | Theorem/Corollary | ГРАНИЦА: Element <=> disc квадрат; role-limit сторона |
| `diag23/diag23_disc/element/eigenvalue_2` | Definition/Lemma | полностью рациональный спектр (Element) |
| `fib/fib_disc/fib_eigenvalue_iff_square5` | Definition/Lemma | Фибоначчи: Element <=> is_square 5 (sqrt5) |
| `pell/pell_disc/pell_eigenvalue_iff_square32` | Definition/Lemma | Пелля: Element <=> is_square 32 (sqrt2) |
| `disc_neg_no_eigenvalue` | Lemma | disc<0 => нет рацион. собств. значения (эллиптика) |
| `companion_disc/companion4_disc_zero/element/companion1_disc_neg/role_limit` | Lemma | SHO-компаньон: k=4 параболика Element, k=1 эллиптика role-limit |
| `three_formula_boundary` | Theorem | капстоун: R-формула на финитизационной границе |

**Key lemmas (deep):**

- **`spectrum_element_iff_square_disc / complete_square`** - Ядро: единое тождество complete_square (4 char_poly = (2x-tr)^2 - disc) даёт ТОЧНУЮ границу — спектр 2x2-правила Element (имеет рациональное собственное значение) ТОГДА И ТОЛЬКО ТОГДА, когда disc — полный квадрат; иначе role-limit (sqrt disc, нетерминирующий Коши-процесс). Две грани: вещественная (сурд-движок: diag23 Element, Фибоначчи sqrt5, Пелля sqrt2) и эллиптическая (disc<0 => нет вещественного собств. значения, конечный порядок по следу = Niven). Это локализует, ГДЕ трёхформульный метод покидает Q, и есть тот же disc-критерий атласа редукций (мост Часть A -> H1). Сама связь рациональность<=>квадратный дискриминант = стандартная линейная алгебра; role-limit вердикты (sqrt5,sqrt2) = цитата. _(finitization-boundary, discriminant, spectrum, three-formula)_

**Uniqueness - score 3 (new-framing).** R-формула (спектр) трёхформульного метода ЛОКАЛИЗОВАНА на финитизационной границе: спектр 2x2 Element <=> disc полный квадрат (две грани — сурд и эллиптика/след-Niven); тот же disc-критерий атласа, мост Часть A -> H1.
> _Caveat:_ Связь 'рациональное собств. значение <=> квадратный дискриминант' и 'disc<0 => нет вещественных' = стандартная линейная алгебра; role-limit вердикты для Фибоначчи (sqrt5)/Пелля (sqrt2) опираются на ЦИТИРУЕМЫЕ факты иррациональности, не передоказаны.

---

## #403 - `src/foundation/ThreeFormulaMethod.v` - score 3 (new-framing)

**The three-formula (E/R/R) method reified as a determination theorem for 2x2 systems over Q**

- **Topic.** A 2x2 evolution operator M (L5 rule) determines its roles (tr,det = char poly, L4) and elements (eigenvalues, L1); proves Rules->Roles (Cayley-Hamilton), Roles<->Elements (Vieta), Roles-/->Rules strict (identity vs shear share char poly), and scale-invariance of the perfect-square/Element status.
- **Role.** Reifies the previously example-only three-formula method. Self-contained (QArith/Lqa). Cross-links ReductionAtlasSynthesis/H1 (finitization boundary) and SHOThreeFormulas (independence result).
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; Stdlib: Lqa
- **E/R/R.** _Elements:_ конкретные системы (тождество, сдвиг, SHO-компаньон) с реальными Q-данными; собственные значения. _Roles:_ три формульных слота (rule/roles/elements); статус спектра (Element/role-limit); структура детерминирована, масштаб свободен. _Rules:_ cayley_hamilton (правило обязано своим ролям), vieta_from_roots (роли = симм. функции элементов), generation_strict (детерминация необратима), scale_preserves_square. _P4:_ мета-система конечно-актуальна (оператор над Q, спектр конечен, детерминация = конечное вычисление); role-limit = иррац. собств. значение (метод ИМЕНУЕТ, не строит); терминирует во входе (масштаб) как в постулате.
- **Classical counterpart.** Cayley-Hamilton (2x2), Vieta's formulas, and the fact that the characteristic polynomial does not determine the matrix are standard linear algebra; NEW only as the 'three-formula (E/R/R) method' reified as a one-way determination theorem (rule->roles->elements strict, scale free).
- **Tags.** foundation, three-formula, err, linear-algebra, new-framing

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `Mat2/mk2/I2/mmul/madd/smul/meq/tr/det/disc/roles/char_poly` | Definition | 2x2 матрицы над Q и формульные слоты |
| `cayley_hamilton/roles_respect` | Lemma | ★ Rules->Roles: M^2 = tr*M - det*I; роли = функция правила |
| `vieta_from_roots` | Lemma | ★ Roles<->Elements: сумма/произведение корней = (tr,det) |
| `shear/ident/vfst/generation_strict` | Definition/Lemma | ★ Roles-/->Rules: одни роли, разная динамика |
| `disc_scale/is_square/scale_preserves_square` | Definition/Lemma | масштаб свободен, структура (perfect-square) инвариантна |
| `char_poly_ident/companion/sho_companion_unimodular/sho_companion_trace` | Definition/Lemma | конкретные якоря (SHO-компаньон унимодулярен) |
| `three_formula_method` | Theorem | капстоун: метод как одна теорема |

**Key lemmas (deep):**

- **`generation_strict`** - Тождество и сдвиг имеют ОДИН char poly (x-1)^2 (tr=2,det=1), но разную динамику vfst — спектр НЕ определяет правило. Это локализует 'независимость трёх формул' SHOThreeFormulas как односторонность генерации Rules->Roles->Elements. Содержательно = стандартный факт линейной алгебры (char poly не определяет матрицу), переобрамлённый как E/R/R-детерминация. _(cayley-hamilton, vieta, determination, err)_

**Uniqueness - score 3 (new-framing).** Трёх-формульный метод E/R/R сделан ТЕОРЕМОЙ: структура течёт Rules->Roles->Elements (строго, необратимо), масштаб = свободный вход; статус Element = perfect-square (граница финитизации).
> _Caveat:_ Cayley-Hamilton, Vieta и 'char poly не определяет матрицу' классичны; новизна только в E/R/R-прочтении/локализации, не в самих фактах линейной алгебры.

---

## #404 - `src/foundation/ThreeFormulasBridge.v` - score 1 (exposition)

**Bridge: three-formula E/R/R files agree with the existing QVec/QState library (6 bridges)**

- **Topic.** End-to-end consistency between SHOThreeFormulas/QubitThreeFormulas/NumericalPredictions and the pre-existing library: ho_energy = sho_level at omega=1, sin2_weinberg = weinberg_prediction = 3/13, qubit components, RG chain 3/8 > 12/37 > 3/13, acoustic modes as SHOs, photon = edge field at c^2=1.
- **Role.** Glue/consistency layer. Imports many ToS physics + foundation modules. Reused as the 'pull up / push down' traceability spine between pure-Q and QVec forms.
- **Counts.** Qed 33 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs ZArith List PeanoNat Lia Lqa; ToS: foundation.SHOThreeFormulas/QubitThreeFormulas/NumericalPredictions/WeinbergAngleDerivation/AcousticChainThreeFormulas/PhotonThreeFormulas; ToS: physics.HarmonicOscillator/QState/Qubit; ToS: LinearAlgebra, process.ProcessRGWeinberg, light.EdgeField
- **E/R/R.** _Elements:_ пары значений из двух представлений (ho_energy/sho_level, qubit-компоненты, sin2). _Roles:_ мост = роль согласования; каждое представление = роль одной системы. _Rules:_ ho_energy_is_sho_level_at_one; sin2_weinberg_is_our_prediction; weinberg_rg_chain; chain_mode_is_sho; edge_oscillator_is_sho_evolve. _P4:_ оба представления конечны над Q; мост = конечная проверка согласованности (Element); цепочка A->законы->E/R/R->числа->библиотека->эксперимент прослеживается.
- **Classical counterpart.** Consistency/bridge file: re-proves agreement between the pure-Q three-formula files and the heavier QVec/QState library (HarmonicOscillator, Qubit, Weinberg, RG, acoustics, light). No new physics; pure traceability.
- **Tags.** foundation, bridge, three-formula, consistency, exposition

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `ho_energy_is_sho_level_at_one/ho_ground_is_sho_ground_at_one/ho_level_spacing_from_three_formulas/ho_E1_is_three_E0/ho_E2_is_five_E0/ho_E3_is_seven_E0/ho_zero_point_half_of_gap` | Theorem | мост 1: SHO <-> HarmonicOscillator |
| `sin2_weinberg_is_our_prediction/sin2_weinberg_lower_from_three_formulas/_upper/cos2_weinberg_complements_prediction/cos2_is_10_13_from_three_formulas` | Theorem | мост 2: Weinberg 3/13 |
| `qubit_ground_bridge_comp0/_comp1/qubit_excited_bridge_comp0/_comp1/pauli_z_eigenval_matches_ground/_excited/born_bridge_ground/_never_excited` | Theorem | мост 3: Qubit (QVec) <-> Q*Q |
| `gut_above_prediction/rg_step1_above_prediction/rg_running_toward_prediction/weinberg_rg_chain` | Theorem | мост 4: RG-бег 3/8->12/37->3/13 |
| `oscillation_matches_sho_k2/waveprop_matches_chain/spectrum_matches/chain_mode_is_sho` | Theorem | мост 5: акустика |
| `edge_oscillator_is_sho_evolve/causal_limit_empties_source/subluminal_retains_source/photon_spectrum_starts_at_zero` | Theorem | мост 6: фотон <-> edge field |
| `three_formulas_bridge_complete` | Theorem | большой мост: всё согласовано |

**Key lemmas (deep):**

- **`weinberg_rg_chain`** - Связывает GUT-значение sin2(3/5)=3/8, один RG-шаг до 12/37 и древесное 3/13 как монотонно убывающую цепочку (3/13 = ИК-фикс-точка). Это мост, а не вывод: само 3/13 берётся из WeinbergAngleDerivation (DOF-счёт). Ценность = прослеживаемость pure-Q <-> QVec, не новый результат. _(bridge, weinberg, rg, consistency)_

**Uniqueness - score 1 (exposition).** End-to-end согласованность: новые pure-Q трёх-формульные файлы совпадают с тяжёлой библиотекой QVec/QState (6 мостов).
> _Caveat:_ Чисто связующий/проверочный файл — никаких новых теорем или физики; все числа (включая 3/13) выведены в других файлах.

---

## #405 - `src/foundation/TierThreeUniversality.v` - score 2 (methods)

**Tier-3 posits: the E/R/R bedrock is NOT universal — an honest convergence map**

- **Topic.** Runs the framework-descent on kappa/SU(5)/eta-existence/eta-value: kappa and eta-existence Converge, SU(5) bottoms at a foreign Unification hypothesis (optional, DOF route covers sin2), eta-value is an OpenSlot. Proves convergence is not universal but every confirmed number has a convergent route.
- **Role.** Meta/honesty capstone over the tier-3 cluster. Imports GenerationsPositReduction (generations_unique). Decidable enum bookkeeping.
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith Lia; ToS: foundation.GenerationsPositReduction
- **E/R/R.** _Elements:_ четыре тир-3 пункта (kappa, SU5Route, EtaExistence, EtaValue); карта вердиктов; цена чужеродного постулата. _Roles:_ Converges = дно в законах E/R/R + мосты; ForeignAtom = нерамочная гипотеза (унификация); OpenSlot = не выведено. _Rules:_ descent; not_universal; convergence_partial; dof_route_saves_sin2w; eta_existence_rides_on_generations. _P4:_ скала не универсальна — честная карта 3 статусов; SU(5)=чужеродная унификация (но DOF-маршрут сходится => опционально); eta-существование сходится (3 поколения=L4-мин), eta-значение открыто; спуск РАЗДЕЛЯЕТ, не маскирует.
- **Classical counterpart.** No classical theorem; a meta-bookkeeping file. Honestly maps which tier-3 model posits 'converge into the E/R/R framework' vs bottom at a foreign hypothesis (SU(5) unification) vs stay open (eta value). Notable for explicit anti-overclaim.
- **Tags.** foundation, honesty, tier3, weinberg, methods

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `ForeignHyp/DescentVerdict/TierThree/descent` | Definition | типы вердиктов и карта descent |
| `kappa_converges/eta_existence_converges/su5_foreign/eta_value_open` | Lemma | четыре вердикта |
| `not_universal/convergence_partial` | Lemma | ★ сходимость НЕ универсальна (есть чужеродный атом) |
| `dof_route_saves_sin2w/eta_existence_rides_on_generations` | Lemma | ★ каждое подтверждённое число имеет сходящийся маршрут |
| `extra_foreign_posits/su5_costs_one_foreign/convergent_routes_cost_zero` | Definition/Lemma | цена чужеродных постулатов (0 у сходящихся) |
| `tier_three_universality` | Theorem | капстоун: трёхсторонняя карта |

**Key lemmas (deep):**

- **`not_universal`** - exists t h, descent t = ForeignAtom h — машинно фиксирует, что СКАЛА НЕ универсальна: SU(5) садится на унификацию (Джорджи-Глэшоу), не на закон рамки. Это редкий для проекта анти-оверклейм, но содержательно = перечисление по конечному типу (reflexivity/discriminate), а не теорема. _(honesty, tier3, non-universal, anti-overclaim)_

**Uniqueness - score 2 (methods).** Честная карта: рамочная сходимость тир-3 НЕ универсальна (SU(5)=чужеродная унификация), но каждое подтверждённое число имеет сходящийся маршрут; eta-существование держится на 3 поколениях (L4-минимальность).
> _Caveat:_ Мета-бухгалтерия по конечному перечислению (доказательства = reflexivity/discriminate); единственная импортированная теорема — generations_unique; сами числа не выводятся здесь.

---

## #406 - `src/foundation/TimeFromObservation.v` - score 2 (methods)

**Time as a consequence of observation: state-change sequences over Q/lists**

- **Topic.** Observer states as lists; before first observation there is no change hence no time; concrete state chain grows in length (the arrow) and preserves earlier observations; no highest moment/level.
- **Role.** Foundation/philosophy file. Standalone (inline T-prefixed observer defs). Illustrative, not a dependency hub.
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lia ZArith List Bool Lqa
- **E/R/R.** _Elements:_ moment (nat); состояния-списки наблюдений; конкретная цепочка state_at_0..3. _Roles:_ время = последовательность изменений состояния (не предсуществует наблюдению); стрела = направление роста. _Rules:_ before_time_state; first_moment_nonempty; growth_01/12/23; no_highest_level. _P4:_ вне времени = пустое состояние (Element=0 различий); каждый момент конечен; нет высшего уровня (незавершающийся процесс роста).
- **Classical counterpart.** Relational/process view of time (time = sequence of state changes, no preexisting time) — a philosophical thesis; the Coq content is elementary list-length monotonicity, not a classical theorem.
- **Tags.** foundation, time, arrow, process, methods

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `TObsState/thas/TObs/tinitial/tobserve/moment/before_time/first_obs` | Definition | наблюдатель и моменты |
| `before_time_state/first_moment_nonempty/no_before_first/moments_ordered` | Lemma | до первого акта — нет времени |
| `growth_01/growth_12/growth_23/preserved_1_in_2/preserved_1_in_3` | Lemma | стрела: длина растёт, прошлое сохраняется |
| `outside_time_empty/no_highest_level` | Lemma | вне времени пусто; нет высшего уровня |
| `time_from_observation_synthesis` | Theorem | синтез |

**Key lemmas (deep):**

- **`no_highest_level`** - forall n, exists m, n<m — формальная сторона тезиса 'нет завершённого верхнего момента/уровня'. Содержательно = тривиальная нат-арифметика (exists S n); вся ценность файла в философском обрамлении (время из наблюдения), а не в доказательствах. _(time, arrow, process, philosophy)_

**Uniqueness - score 2 (methods).** Время как следствие наблюдения: до первого акта изменений нет => нет времени; стрела = рост длины списка состояний с сохранением прошлого.
> _Caveat:_ Реляционный/процессный взгляд на время — известный философский тезис; Coq-содержание элементарно (длины списков, нат-арифметика). HEADER DRIFT: заявлено 15 Qed, фактически 12.

---

## #407 - `src/foundation/TransfiniteInduction.v` - score 3 (new-framing)

**Transfinite induction PROVEN (no axiom): well-foundedness of ord_lt by structural induction**

- **Topic.** Proves ord_lt (from Ordinal.v) is well-founded via acc_succ + structural induction on Ord, then derives transfinite induction, transfinite recursion, nat-induction as a special case, and induction at OZero/OSucc/omega/epsilon_0.
- **Role.** Set-theory foundation. Imports Ordinal.v + Stdlib Wellfounded. Provides transfinite_ind/transfinite_rec for downstream ordinal reasoning. 0 new axioms (key claim).
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Wellfounded; ToS: Ordinal
- **E/R/R.** _Elements:_ Ord (OZero/OSucc/OLim), ord_lt, точки доступности Acc. _Roles:_ well_founded ord_lt = порядок-роль; принцип индукции/рекурсии вдоль порядка. _Rules:_ acc_succ; wf_ord_lt (ТЕОРЕМА); transfinite_ind; transfinite_rec. _P4:_ well-foundedness ВЫВЕДЕНА из структурной индукции (конструктивно, без нового аксиома); ординалы = нотации (потенциальная, не завершённая бесконечность); Print Assumptions = classic + L4_witness.
- **Classical counterpart.** Transfinite induction/recursion over ordinal notations and well-foundedness of ord_lt — classical set theory; HERE wf_ord_lt is a THEOREM (structural induction on the inductive Ord), introducing NO new axiom beyond classic+L4_witness.
- **Tags.** foundation, ordinal, transfinite, set-theory, new-framing

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `acc_succ` | Lemma | x доступен => OSucc x доступен |
| `wf_ord_lt` | Theorem | ★★★ ord_lt вполне-обоснован (ТЕОРЕМА, не аксиома) |
| `transfinite_ind/transfinite_rec` | Theorem | трансфинитная индукция и рекурсия |
| `nat_induction_from_transfinite/omega_tower_induction` | Lemma | нат-индукция как частный случай |
| `transfinite_ind_zero/_succ/_omega/_epsilon_0` | Lemma | индукция на конкретных ординалах |
| `wf_restricts_to_nat/axiom_count_documentation` | Lemma | сужение на nat; учёт аксиом |

**Key lemmas (deep):**

- **`wf_ord_lt`** - Доказывает well_founded ord_lt структурной индукцией по Ord (OZero: inversion; OSucc: acc_succ; OLim: Acc_inv по IHf) — так что трансфинитная индукция НЕ требует отдельной аксиомы, только classic+L4_witness. Сам принцип трансфинитной индукции классичен; новизна = конструктивная выводимость well-foundedness из inductive Ord (характерно для ToS: бесконечность как процесс/нотация). _(ordinal, well-founded, transfinite, no-axiom)_

**Uniqueness - score 3 (new-framing).** Трансфинитная индукция/рекурсия как ТЕОРЕМА: well-foundedness ord_lt выведена структурной индукцией по inductive Ord, без нового аксиома (только classic+L4_witness).
> _Caveat:_ Трансфинитная индукция и well-founded recursion — классика теории множеств; новое только в конструктивной выводимости (ординалы как нотации), а не в принципе.

---

## #408 - `src/foundation/TransfiniteInductionLevel.v` - score 3 (new-framing)

**Well-founded induction over the Level hierarchy + Burali-Forti analogue (no top level)**

- **Topic.** level_lt is well-founded because it decreases the nat rank level_depth (proved in Core_ERR); derives strong induction over Level; shows the successor LS always escapes any candidate top, so 'the level of all levels' cannot exist (Burali-Forti dissolved).
- **Role.** Companion to TransfiniteInduction.v but over the membership hierarchy Level (the order blocking P1 self-membership). Imports Core_ERR + Wf_nat. 0 axioms.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Wf_nat Lia; ToS: TheoryOfSystems_Core_ERR
- **E/R/R.** _Elements:_ Level (L1\|LS), level_lt, level_depth (нат-ранг). _Roles:_ level_lt = порядок основания; level_depth = его ранг; LS = всегда-убегающий преемник. _Rules:_ level_lt_wf; level_strong_induction; level_no_top; no_universal_level. _P4:_ иерархия = ПРАВИЛО (порядок основания), не завершённый объект 'уровень всех уровней'; попытку назвать верх опровергает один шаг LS (незавершимость).
- **Classical counterpart.** Well-founded/strong induction over a hierarchy and the Burali-Forti 'no set of all ordinals' — classical; HERE specialized to the ToS membership Level (L1\|LS), with no-top dissolved structurally by the successor LS. 0 axioms.
- **Tags.** foundation, level, burali-forti, set-theory, new-framing

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `level_lt_wf` | Lemma | level_lt вполне-обоснован (через level_depth) |
| `level_strong_induction` | Theorem | сильная индукция по иерархии Level |
| `level_lt_succ/succ_not_le` | Lemma | L < LS L; преемник не ниже/равен |
| `level_no_top` | Theorem | ★ для любого кандидата-верха есть убегающий уровень |
| `no_universal_level` | Theorem | ★ нет универсального уровня (Burali-Forti растворён) |

**Key lemmas (deep):**

- **`no_universal_level`** - ~ exists Top, forall L, L<<Top \/ L=Top — структурное растворение Burali-Forti на иерархии Level: LS Top убегает от Top. Содержательно = классический аргумент (преемник), специализированный к ToS-иерархии; новизна = прочтение иерархии как правила-процесса, а не объекта. _(level, burali-forti, no-top, well-founded)_

**Uniqueness - score 3 (new-framing).** Сильная индукция по иерархии Level + структурное растворение Burali-Forti: преемник LS любого кандидата-верха убегает => нет 'уровня всех уровней'.
> _Caveat:_ Well-founded induction и Burali-Forti классичны; вклад — специализация к ToS-иерархии Level и прочтение её как процесса-правила, не новый результат.

---

## #409 - `src/foundation/TwoMechanisms.v` - score 1 (exposition)

**Two mechanisms of creation: analysis (K) + synthesis (K choose 2) pairs over nat**

- **Topic.** Analysis potential = K; synthesis pairs = K(K-1)/2; total potential = K + C(K,2); concrete pair/total counts (K=1..20), potential > K for K>=3, and an 'interacts' predicate (distinct => new quality).
- **Role.** Foundation/philosophy combinatorics. Standalone (Stdlib only). Sibling of VoidInexhaustible.v (same K(K-1)/2 surplus idea).
- **Counts.** Qed 18 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lia ZArith List Bool Lqa
- **E/R/R.** _Elements:_ энергии различий (nat); пары; полный потенциал. _Roles:_ анализ = роль (вход в существующее различие); синтез = роль (комбинация двух различий). _Rules:_ synthesis_pairs = K(K-1)/2; total_potential = analysis + synthesis; exceeds_K; interacts. _P4:_ K актуализированных различий, но потенциал (пары) > K — потенциал превосходит актуальное (P4: конечная актуальность с растущим потенциальным запасом).
- **Classical counterpart.** Counts K (analysis) + C(K,2) pairs (synthesis) and total = triangular+K — elementary combinatorics; the 'two mechanisms of creation' framing is the only novelty, no classical theorem.
- **Tags.** foundation, combinatorics, potential, exposition

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `analysis_potential/synthesis_pairs/total_potential/interacts` | Definition | два механизма + предикат взаимодействия |
| `pairs_1/_2/_3/_4/_5/_10` | Lemma | конкретные числа пар (0,1,3,6,10,45) |
| `potential_3/_4/_5/_10/_20` | Lemma | конкретные полные потенциалы |
| `exceeds_3/_5/_10/_20` | Lemma | потенциал > K |
| `same_no_new/diff_new/diff_new_2` | Lemma | новое качество только от различных |

**Key lemmas (deep):**

- **`exceeds_10`** - 10 < total_potential 10 (=55): потенциал комбинаций превосходит число актуализированных элементов. Это просто треугольное число + K, проверенное на конкретных K; 'два механизма' — обрамление, а не математика. _(combinatorics, triangular, potential, p4)_

**Uniqueness - score 1 (exposition).** Два механизма создания (анализ K + синтез C(K,2)) и их полный потенциал, превосходящий K, на конкретных nat.
> _Caveat:_ Элементарная комбинаторика (треугольные числа); 'два механизма' — философское обрамление, не теорема.

---

## #410 - `src/foundation/TwoSU2OneQuaternion.v` - score 3 (new-framing)

**One quaternion carries BOTH SU(2)'s: weak-gauge fundamental + rotation adjoint, elliptic side of H**

- **Topic.** Quaternions over Q: norm-multiplicativity (Euler four-square = SU(2) Casimir = det M), conjugation as an R^3 isometry / SO(3) with 2:1 double cover, unit q => SL2 (det 1) AND elliptic (disc = 4w^2-4 <= 0), with concrete q0=(1+i+j+k)/2 cycling e_x->e_y.
- **Role.** Hypothesis H2 (closes the 'weak-SU(2) = rotation-SU(2)' seam). Self-contained (Stdlib only). Cross-links GRQFTDiscriminantBridge.v (H, elliptic/hyperbolic faces).
- **Counts.** Qed 14 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lqa ZArith Lia
- **E/R/R.** _Elements:_ кватернионы над Q (w,x,y,z); произведение Гамильтона; норма; сопряжение; trace/det матрицы 2x2. _Roles:_ фундаментальное представление = дублет/калибровка (det=норма, спин-1/2); присоединённое = вектор/вращение (q v q-bar, спин-1). _Rules:_ qnorm_mult (N(pq)=N(p)N(q) = четыре квадрата = Casimir); unit q => SL2 & elliptic; double_cover; rotate_unit_isometry. _P4:_ вычисления над Q конечны (Element); q0 — конкретное рациональное вращение; компактная (эллиптическая) грань H — реальная Q-проверка disc<=0.
- **Classical counterpart.** Quaternion fundamental (spin-1/2, det=norm) and adjoint (spin-1, conjugation = SO(3), 2:1 cover) reps, Euler four-square = norm multiplicativity, SU(2) elliptic — all classical (Hamilton/Cayley); NEW as a concrete machine-checked over-Q unification of weak-SU(2) and rotation-SU(2) tied to the discriminant (elliptic) bridge.
- **Tags.** foundation, quaternion, su2, gauge, rotation, new-framing

**Lemmas (8):**

| name | kind | role |
|---|---|---|
| `Quat/qmul/qconj/qneg/qnorm/qpure` | Definition | кватернионы и операции |
| `qnorm_mult/qconj_norm` | Lemma | ★ мультипликативность нормы = четыре квадрата |
| `rotate/rotate_pure/rotate_norm/rotate_unit_isometry/double_cover` | Definition/Lemma/Corollary | ★ присоединённое: вращение R^3, изометрия, 2:1 покрытие |
| `M_trace/M_det/M_disc/M_det_is_norm/M_disc_eq` | Definition/Lemma | фундаментальная матрица 2x2 (det=норма) |
| `q_sq_nonneg` | Lemma | квадрат >= 0 над Q |
| `unit_quat_SL2/unit_quat_elliptic` | Lemma | ★★ единичный q => SL2 и эллиптический (disc<=0) |
| `q0/q0_unit/q0_rotates_x_to_y` | Definition/Lemma | ★ конкретное вращение (1+i+j+k)/2 |
| `two_su2_one_quaternion` | Theorem | капстоун: два SU(2), один кватернион |

**Key lemmas (deep):**

- **`unit_quat_elliptic`** - Для единичного кватерниона disc M(q)=4w^2-4<=0 (так как w^2<=N=1) — ВСЯКИЙ элемент SU(2) ЭЛЛИПТИЧЕН, то есть и калибровочный, и вращательный SU(2) лежат на компактной/евклидовой грани дискриминантного моста H (бусты Лоренца = гиперболическая грань). Объединяет H и H2 на оси GR/QFT. Сами факты (det=норма, эллиптичность компактной группы) классичны; новизна = конкретная Q-формализация и связь обоих SU(2) с дискриминантным мостом одним вычислением. _(quaternion, su2, elliptic, four-square, discriminant)_

**Uniqueness - score 3 (new-framing).** ОДИН единичный кватернион несёт ОБА SU(2) (слабый-калибровочный = фундаментальное, пространственное вращение = присоединённое) и лежит на компактной/эллиптической грани дискриминантного моста H — машинно над Q.
> _Caveat:_ Двойное представление кватерниона, четыре-квадратная мультипликативность, 2:1 покрытие SU(2)->SO(3) и эллиптичность компактной группы — классика (Гамильтон/Кэли); новое только конкретное Q-обрамление и сшивка с мостом H, не новая теорема.

---

## #411 - `src/foundation/UnistochasticFromGraph.v` - score 2 (methods)

**Unistochastic => doubly stochastic over Q: |U|^2 of orthogonal U, concrete 2x2/3x3 witnesses**

- **Topic.** Matrices over Q; orthogonality forces gamma row sums = 1 (gamma_of U = entrywise square); transpose-orthogonality forces column sums = 1; concrete U2 (3/5,4/5) and U3 (2/3,1/3) Cayley matrices proved orthogonal with their Gamma unistochastic; main theorem unistochastic => doubly stochastic.
- **Role.** Foundation linear algebra (toward Born-rule / Birkhoff polytope context). Standalone (Stdlib only). is_transpose_orthogonal taken as a hypothesis (general proof needs determinant theory).
- **Counts.** Qed 19 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith List Lqa
- **E/R/R.** _Elements:_ ортогональная матрица U над Q; поэлементный квадрат gamma_of; дважды-стохастическая матрица. _Roles:_ ортогональность -> нормировка строк/столбцов; возведение в квадрат -> неотрицательность. _Rules:_ orth_implies_gamma_row_1; trans_orth_implies_gamma_col_1; unistochastic_implies_DS. _P4:_ конечные NxN матрицы над Q (Element); конкретные 2x2/3x3 свидетели вычисляются точно; унистохастичность как конечная проверка.
- **Classical counterpart.** Unistochastic => doubly stochastic (entrywise \|U\|^2 of an orthogonal/unitary matrix has unit row & column sums) is a standard linear-algebra fact; NEW only as an explicit over-Q proof with concrete 2x2/3x3 Cayley witnesses (Birkhoff context).
- **Tags.** foundation, unistochastic, linear-algebra, born-rule, methods

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `Mat/mat_prod/mat_trans/is_orthogonal/gamma_of/gamma_row_sum/gamma_col_sum` | Definition | матрицы над Q и суммы gamma |
| `orth_diag_is_row_sum/orth_implies_gamma_row_1/orth_trans_diag_is_col_sum/is_transpose_orthogonal/trans_orth_implies_gamma_col_1` | Lemma/Definition | ортогональность => суммы=1 |
| `is_doubly_stochastic/is_unistochastic` | Definition | DS и унистохастичность |
| `U2/Gamma2/gamma_2_DS_at_1/U2_orthogonal/U2_trans_orthogonal/Gamma2_is_gamma_of_U2/Gamma2_unistochastic` | Definition/Lemma | конкретный 2x2 свидетель |
| `U3/Gamma3/gamma_3_DS/U3_orthogonal/U3_trans_orthogonal/Gamma3_is_gamma_of_U3/Gamma3_unistochastic` | Definition/Lemma | конкретный 3x3 свидетель |
| `gamma_row_sum_eq_fold/gamma_col_sum_eq_fold/fold_left_gamma_row/fold_left_gamma_col` | Lemma | fold-хелперы для Qeq |
| `unistochastic_implies_DS` | Theorem | ★ унистохастическая => дважды стохастическая |

**Key lemmas (deep):**

- **`unistochastic_implies_DS`** - Из существования ортогональной (и транспонированно-ортогональной) U с Gamma = \|U\|^2 следует, что Gamma дважды стохастична (суммы строк и столбцов = 1). Это стандартный факт (поэлементный квадрат унитарной/ортогональной матрицы дважды стохастичен), доказанный явно над Q с fold-хелперами для Qeq; конкретные U2/U3 — рациональные свидетели. Содержательно классично; ценность = аккуратная Q-формализация. _(unistochastic, doubly-stochastic, orthogonal, birkhoff)_

**Uniqueness - score 2 (methods).** Унистохастическая => дважды стохастическая над Q (поэлементный квадрат ортогональной U), с конкретными рациональными 2x2/3x3 свидетелями (Cayley).
> _Caveat:_ Стандартный факт линейной алгебры; новизна только в явной Q-формализации и свидетелях, не в результате. is_transpose_orthogonal взята как гипотеза (общий вывод требует теории определителей).

---

## #412 - `src/foundation/UniversalDiagonal.v` - score 4 (synthesis+observation)

**The universal diagonal (Lawvere): Cantor = halting = Russell as ONE machine-checked instance**

- **Topic.** Lawvere's theorem (point-surjection A->(A->B) forces every g:B->B to have a fixed point) and its contrapositive no-go; instantiated with B=bool, g=negb to prove Cantor (no onto A->(A->bool)), no_universal_decider (halting), russell (membership table) by IDENTICAL proofs; Goedel tagged/cited (logical negation, provability model not built).
- **Role.** Direction Delta3 / uniqueness D (paradox-diagonal unification). Self-contained, 0 axioms, fully constructive (pointwise surjectivity, no funext). Cites ShrinkingIntervals (Cantor) and src/cs/HaltingRoleLimit (halting); ties to H1 role-limit boundary.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Bool
- **E/R/R.** _Elements:_ тип объекта A; двузначное B (bool) и его эндокарта; диагональный элемент f a0 a0. _Roles:_ диагональ fun a => g(f a a) = порождатель role-limit; g без неподв. точки (negb/неотрицание) = несовпадение; четыре парадокса = инстансы одной теоремы. _Rules:_ lawvere (point-сюръекция => фикс-точка); lawvere_diagonal (fixed-point-free g блокирует сюръекцию); заблокированная сюръекция = role-limit-объект. _P4:_ диагональ = универсальный порождатель role-limit (граница H1: enumerable A = Element, un-enumerable A->B = role-limit); Cantor=halting=Russell машинно ОДНА теорема; формализует уникальность D.
- **Classical counterpart.** Lawvere's fixed-point theorem (1969) and the observation that Cantor / halting / Russell / Goedel are one diagonal — KNOWN; NEW as a single 0-axiom constructive Coq proof literally instantiating Cantor=halting=Russell with identical proofs (B=bool, g=negb), formalizing the project's uniqueness D.
- **Tags.** foundation, lawvere, diagonal, cantor, halting, russell, uniqueness-D, synthesis

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `lawvere` | Theorem | ★ Lawvere 1969: point-сюръекция => всякий g имеет неподв. точку |
| `lawvere_diagonal` | Corollary | ★ no-go: fixed-point-free g блокирует сюръекцию |
| `negb_fixed_point_free` | Lemma | negb без неподвижной точки |
| `cantor/no_universal_decider/russell` | Corollary | ★ Cantor=halting=Russell идентичными доказательствами (B=bool,g=negb) |
| `DiagonalParadox/endomap_is_negb/three_share_negb/godel_uses_negation` | Definition/Lemma | четыре парадокса; три делят negb, Goedel = логич. отрицание (цитата) |
| `universal_diagonal` | Theorem | капстоун: универсальная диагональ объединяет парадоксы |

**Key lemmas (deep):**

- **`cantor / no_universal_decider / russell`** - Три парадокса доказаны ОДНОЙ строкой apply (lawvere_diagonal A bool negb), negb_fixed_point_free — меняется лишь тип A (множество/программа/множество). Это машинно демонстрирует, что Cantor, проблема остановки и Рассел = один инстанс теоремы Лавера, формализуя уникальность D проекта. Сама теорема Лавера (1969) и её роль в объединении парадоксов ИЗВЕСТНЫ; вклад = единое 0-аксиомное конструктивное доказательство + role-limit-прочтение (связь с H1). Goedel требует модели провабилити (цитируется, не строится). _(lawvere, cantor, halting, russell, diagonal, role-limit)_

**Uniqueness - score 4 (synthesis+observation).** Одна машинно-проверенная диагональ (Лавер) объединяет Cantor = проблема остановки = Рассел (идентичные доказательства, B=bool, g=negb) и читается как универсальный порождатель role-limit (граница H1); формализует уникальность D проекта.
> _Caveat:_ Теорема Лавера (1969) и наблюдение 'Cantor=halting=Russell=Goedel — одна диагональ' хорошо известны; новизна — единая 0-аксиомная конструктивная формализация + role-limit-прочтение, а не новая теорема. Goedel только помечен/цитируется (модель провабилити не построена).

---

## #413 - `src/foundation/UniversalInterLevelCalculus.v` - score 2 (methods)

**Universal inter-level interaction calculus: the level-spine as one monotone-flow structure**

- **Topic.** Scale flows nat->Q with the dichotomy element_excludes_role_limit (bounded vs unbounded); the two directions (generation up = nondecreasing, convergence down = nonincreasing) as the two signs of monotonicity, demonstrated on step u=u^2 (u=2 escapes to 256, u=1/2 descends to 1/256, u=1 fixed); a registry of five directions H1-H4+Cascade with Element/role-limit verdicts.
- **Role.** Final synthesis capstone (direction N5) over the hierarchy/cascade cluster. Standalone (Stdlib only). Replicates dichotomy from InterLevelCalculus.v; registry entries proved in their own files.
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lia Lqa
- **E/R/R.** _Elements:_ потоки nat->Q; step-карта u\|->u^2; пять тегов направлений; вердикты. _Roles:_ две направленности (генерация вверх / сходимость вниз); пять инстансов; граница Element/role-limit. _Rules:_ element_excludes_role_limit (монот.+огранич = Element XOR монот.+неогранич = role-limit); две направленности = два знака монотонности; одна граница. _P4:_ спина уровней сделана динамической, одно исчисление, одна граница; вверх u=2 убегает (role-limit), вниз u=1/2 к полу 0 (Element), u=1 фикс (стена); организующий капстоун (последним).
- **Classical counterpart.** No classical theorem; an organizing synthesis capstone. The one genuine general result is a boundedness dichotomy (a monotone flow can't be both bounded and unbounded) reused from InterLevelCalculus.v; the rest is a witnessed registry of five 'directions' over Q.
- **Tags.** foundation, inter-level, dichotomy, synthesis, methods

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `ScaleFlow/nondecreasing/nonincreasing/bounded_above/unbounded_above/flow_element_up/flow_role_limit_up` | Definition | потоки и режимы Element/role-limit |
| `element_excludes_role_limit` | Theorem | ★ дихотомия (reused): не оба Element и role-limit |
| `Direction/direction_sign/directions_distinct` | Definition/Lemma | ★ две направленности = два знака монотонности |
| `step/step_iter/generation_up_escapes/convergence_down_to_floor/boundary_fixed` | Definition/Lemma | ★ конкретика u=u^2 (256, 1/256, фикс 1) |
| `Direction5/Verdict/direction_verdict/h2_element_only/h1_both_sides` | Definition/Lemma | регистр пяти направлений и вердикты |
| `universal_inter_level_calculus` | Theorem | капстоун |

**Key lemmas (deep):**

- **`element_excludes_role_limit`** - Единственная подлинная общая теорема файла: монотонный межуровневый поток не может быть одновременно Element (ограничен) и role-limit (неограничен) — переиспользована из InterLevelCalculus.v. Две направленности (генерация=nondecreasing, сходимость=nonincreasing) и step=u^2 — демонстрация на свидетелях, не общая теорема сходимости (та требует classic). Честно помечено как организующий капстоун: located, not crossed. _(dichotomy, monotone, inter-level, synthesis, registry)_

**Uniqueness - score 2 (methods).** Спина уровней ToS как одно исчисление монотонных потоков с одной границей Element/role-limit; две направленности (генерация/сходимость) = два знака монотонности; пять направлений H1-H4+каскад как инстансы.
> _Caveat:_ Организующий синтез-капстоун; единственная общая теорема (дихотомия ограниченности) переиспользована из InterLevelCalculus.v; регистр = перечисление, конкретика = свидетели на u=u^2; НЕ новый глубокий результат (так помечено в самом файле).

---

## #414 - `src/foundation/VacuumFromTransfer.v` - score 2 (methods)

**Vacuum energy from transfer-matrix eigenvalue over Q: E_vac = 1 - lambda0 (replaces ad hoc 1/(1+K))**

- **Topic.** Replicates the Bessel/character transfer eigenvalue; defines E_vac(beta,M) = 1 - transfer_eig 0 beta M; computes E_vac(1,0)=1/8, E_vac(2,0)=1/2 (positive, monotone increasing with beta) and Lambda = E_vac*(1/100) giving 1/800, 1/200.
- **Role.** Foundation/lattice cosmological-constant file; upgrades VacuumNecessity.v's placeholder to a derived transfer-matrix value. Standalone (replicates transfer eig to avoid stale .vo). Concrete vm_compute proofs.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lia ZArith Lqa
- **E/R/R.** _Elements:_ E_vac_transfer; собственное значение переноса lambda0; Lambda. _Roles:_ вакуумная энергия = роль основного состояния матрицы переноса; Lambda = роль масштабированной вакуумной энергии. _Rules:_ E_vac_transfer = 1 - transfer_eig 0; E_vac_b1_M0=1/8; E_vac_monotone; lambda_from_transfer. _P4:_ конечная матрица переноса, частичная сумма Бесселя над Q (Element); E_vac = ВЫВЕДЕННОЕ конкретное Q-значение, не плейсхолдер; вычисляется vm_compute.
- **Classical counterpart.** Vacuum energy as 1 - lambda0 of a (character/Bessel) transfer matrix replacing the ad hoc 1/(1+K); the transfer-matrix/eigenvalue method is standard lattice gauge theory, used here for concrete rational E_vac values.
- **Tags.** foundation, transfer-matrix, vacuum, lattice, methods

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `Qpow/fact_Q/fact_prod/bessel_term/bessel_partial/transfer_eig` | Definition | реплика собственного значения переноса (Бессель) |
| `E_vac_transfer/E_vac_b1_M0/E_vac_positive_b1/E_vac_b2_M0/E_vac_monotone` | Definition/Lemma/Theorem | ★ E_vac=1-lambda0; 1/8, 1/2; положительна, растёт |
| `lambda_from_transfer/lambda_b1_M0/lambda_positive/lambda_b2_M0` | Definition/Lemma/Theorem | Lambda = E_vac*(1/100) (1/800, 1/200) |
| `vacuum_from_transfer_synthesis` | Theorem | синтез |

**Key lemmas (deep):**

- **`E_vac_b1_M0`** - E_vac(beta=1,M=0)=1/8 (lambda0=7/8), доказано vm_compute по реплике характерного/Бесселева собственного значения переноса — заменяет ad hoc 1/(1+K) ВЫВЕДЕННЫМ значением. Метод матрицы переноса классичен для решёточной теории; вклад = конкретное рациональное E_vac из неё, не новая физика. Магнитуда зависит от модельного усечения (M). _(transfer-matrix, vacuum, bessel, lattice)_

**Uniqueness - score 2 (methods).** Вакуумная энергия E_vac = 1 - lambda0 из собственного значения матрицы переноса над Q (1/8, 1/2), заменяющая ad hoc 1/(1+K); Lambda = E_vac*kappa^2.
> _Caveat:_ Метод матрицы переноса / собственного значения — стандарт решёточной калибровочной теории; вклад только в конкретных Q-значениях; усечение Бесселя (M) — модельный вход, не предсказание физической Lambda.

---

## #415 - `src/foundation/VacuumIsAntigravity.v` - score 2 (methods)

**The framework vacuum is necessarily antigravity: positive + homogeneous => rho+3p = -2rho < 0**

- **Topic.** Replicates rho_vac(K)=1/(1+K) (>0, necessary); homogeneity + first law force p=-rho (w=-1), hence the gravitational source rho+3p = -2rho < 0 at every scale K (antigravity), with magnitude decreasing with K but sign robust.
- **Role.** Foundation/cosmology file connecting hint (1) to VacuumNecessity's cc_process. Self-contained (Stdlib only; cc_process replicated). Synthesis-level (links vacuum-necessity + antigravity condition).
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lqa ZArith Lia
- **E/R/R.** _Elements:_ rho_vac(K)=1/(1+K) (содержание вакуума, >0 необходимо). _Roles:_ давление p = напряжение содержания по направлениям; источник rho+3p. _Rules:_ vacuum_eos (p=-rho); vacuum_source_value (rho+3p=-2rho); vacuum_is_antigravity (<0). _P4:_ вакуум>0 НЕОБХОДИМ (VacuumNecessity) + p=-rho (гомогенность) => антигравитация структурно неизбежна; магнитуда -2rho(K) убывает с K (CC-резолюция), знак робастен.
- **Classical counterpart.** Dark-energy equation of state p = -rho (w=-1) from homogeneity + first law, giving the Friedmann source rho+3p = -2rho < 0 (repulsion) — standard cosmology; here applied to the framework's own positive vacuum density.
- **Tags.** foundation, vacuum, dark-energy, antigravity, cosmology, methods

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `vacuum_density/vacuum_positive/vacuum_density_0/vacuum_density_1` | Definition/Lemma | rho_vac>0 (реплика из VacuumNecessity) |
| `vacuum_pressure/vacuum_first_law/vacuum_eos` | Definition/Lemma | ★ p=-rho из гомогенности + первого закона |
| `vacuum_source/vacuum_source_value/vacuum_is_antigravity/vacuum_source_0/vacuum_source_1` | Definition/Lemma | ★★ источник rho+3p=-2rho<0 (антигравитация) |
| `vacuum_is_necessarily_antigravity` | Theorem | капстоун |

**Key lemmas (deep):**

- **`vacuum_is_antigravity`** - rho+3p = -2rho < 0 на каждом K, объединяя НЕОБХОДИМУЮ положительность вакуума (VacuumNecessity) с уравнением состояния p=-rho (гомогенность + первый закон). Вывод: антигравитация структурно неизбежна в рамке. Само уравнение состояния тёмной энергии (w=-1, rho+3p<0) — стандартная космология; p=-rho здесь — моделирующий вход (гомогенность), rho>0 доказано, 1/(1+K) — плейсхолдер; это НЕ предсказание значения Lambda. _(dark-energy, equation-of-state, antigravity, cosmology)_

**Uniqueness - score 2 (methods).** Положительный (необходимый) гомогенный вакуум рамки ВЫНУЖДАЕТ антигравитацию: p=-rho => rho+3p=-2rho<0 на каждом масштабе K (знак робастен, магнитуда убывает).
> _Caveat:_ Уравнение состояния тёмной энергии w=-1 и источник rho+3p<0 — стандартная космология; p=-rho — моделирующий вход (гомогенность), 1/(1+K) — плейсхолдер; не предсказание физической Lambda. Уровень: синтез связи (vacuum-necessity + antigravity).

---

## #416 - `src/foundation/VacuumNecessity.v` - score 2 (methods)

**Vacuum energy > 0 is structurally necessary; the CC is a process, not a constant**

- **Topic.** vacuum_energy(K)=1/(1+K) proved >0, never 0, decreasing; distinction requires energy; cc_process is not constant (cc(0)!=cc(1)) and decreases; Lambda determined by scale not fine-tuning; energy is rational (Q not R); no UV divergence (max at K=0).
- **Role.** Foundation file 7/9; defines vacuum_energy/cc_process reused by VacuumIsAntigravity.v and VacuumFromTransfer.v. Imports foundation.Distinction. The CC-problem dissolution narrative.
- **Counts.** Qed 15 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia Lqa List; ToS: foundation.Distinction
- **E/R/R.** _Elements:_ процесс вакуумной энергии vacuum_energy(K); космологическая 'константа' cc_process. _Roles:_ различие требует энергии; плоское пространство (Lambda=0) невозможно; CC = процесс по K. _Rules:_ vacuum_always_positive; vacuum_never_zero; cc_not_constant; lambda_determined_by_scale. _P4:_ все физ. величины = Q (не завершённые R); E_vac>0 следует из минимум-1-различия; CC = процесс (потенциальная, не актуальная константа); нет UV-расходимости (макс при K=0).
- **Classical counterpart.** The 'cosmological constant problem' (why is Lambda not 0 / fine-tuning) reframed: in ToS Lambda=0 is impossible (no distinction = nothing), and Lambda is a process indexed by K, not a constant. The specific 1/(1+K) form is an acknowledged placeholder, not a derivation.
- **Tags.** foundation, vacuum, cosmological-constant, process, methods

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `vacuum_energy/vacuum_at_K0/vacuum_at_K1` | Definition/Lemma | модель 1/(1+K), значения 1 и 1/2 |
| `vacuum_always_positive/vacuum_never_zero/distinction_requires_energy` | Theorem | ★ E_vac>0 необходимо (различие требует энергии) |
| `cc_process/cc_process_positive/cc_not_constant/cc_decreasing_concrete` | Definition/Theorem | ★ CC = процесс, не константа, убывает |
| `lambda_determined_by_scale/different_scales_different_lambda/hierarchy_is_process` | Theorem | Lambda задаётся масштабом, не подгонкой |
| `energy_is_rational/no_uv_divergence_K0/no_uv_divergence_K1` | Theorem | энергия рациональна; нет UV-расходимости |
| `vacuum_necessity_summary/vacuum_necessity_theorem_count` | Theorem/Definition | сводка |

**Key lemmas (deep):**

- **`vacuum_never_zero`** - ~(vacuum_energy K == 0) — формальная сторона 'растворения' CC-проблемы: вопрос не 'почему Lambda>0?', а 'почему ждать Lambda=0?', ведь Lambda=0 = нет различия = ничего. Содержательно опирается на МОДЕЛЬ 1/(1+K), явно помеченную в файле как качественный плейсхолдер (первопринципный вывод требует решёточного эффективного потенциала). Тезис необходимости вакуума философски силён, но формальная положительность тривиальна для 1/(1+K). _(cosmological-constant, vacuum, process, placeholder)_

**Uniqueness - score 2 (methods).** E_vac>0 структурно необходимо (различие требует энергии; Lambda=0 = ничего), а космологическая 'константа' — процесс по масштабу K, не константа; растворение проблемы тонкой настройки.
> _Caveat:_ Форма 1/(1+K) — явно объявленный качественный плейсхолдер (не первопринципный вывод); положительность для неё тривиальна. HEADER DRIFT: заявлено 20 Qed (и vacuum_necessity_theorem_count:=20), фактически 15 Qed.

---

## #417 - `src/foundation/VariationalEinsteinSourced.v` - score 3 (new-framing)

**Sourced discrete Einstein equation as the action minimum over Q (L4 at the field level)**

- **Topic.** A kappa-scaled Regge+matter action S(delta)=delta^2 - 2*kappa*m*delta with stationarity residual delta - kappa*m; vacuum (m=0)=>delta=0, sourced => delta=kappa*m (curvature=matter, the case ProcessReggeVariation deferred), genuine global minimum via (delta-kappa*m)^2 >= 0.
- **Role.** Field-level lift step 2 over the Regge cluster (ProcessRegge/ProcessReggeVariation). Self-contained (Stdlib only). Adds the matter coupling the existing vacuum Regge layer deferred.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lqa
- **E/R/R.** _Elements:_ дефицит delta (значение кривизны), масса m (содержание/источник в вершине). _Roles:_ варьируемая конфигурация геометрии (то, по чему берётся вариация). _Rules:_ field_equation (delta=kappa*m); sourced_einstein; einstein_is_minimum; action_finite_diff. _P4:_ стационарность dS=0 ЕСТЬ L4 (достаточное основание) на поле — актуальная геометрия самообоснована (нет неизрасходованной вариации); вакуум m=0=>delta=0, источник=>delta=kappa*m (НОВОЕ для слоя), подлинный минимум (квадрат>=0).
- **Classical counterpart.** The sourced (curvature = kappa*matter) field equation as the minimum of a Regge+matter action, with completing-the-square showing a global minimum — standard variational gravity; here a model quadratic action over Q read as L4 (sufficient reason).
- **Tags.** foundation, regge, einstein, variational, new-framing

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `action/stationarity/action_finite_diff` | Definition/Lemma | действие + конечноразностная производная = 2*стационарность |
| `field_equation/vacuum_flat/sourced_einstein` | Lemma | ★ стационарность <=> delta=kappa*m; вакуум и источник |
| `q_sq_nonneg/action_above_min/einstein_is_minimum` | Lemma | ★ delta=kappa*m — глобальный минимум (квадрат>=0) |
| `variational_einstein` | Theorem | капстоун |

**Key lemmas (deep):**

- **`einstein_is_minimum`** - action kappa m (kappa*m) <= action kappa m delta — решение полевого уравнения delta=kappa*m глобально минимизирует действие (дополнение до квадрата). Читается как L4: актуальная геометрия = самообоснованный экстремум без неизрасходованной вариации; sourced-случай (delta=kappa*m) — тот, что ProcessReggeVariation отложил. Содержательно = модельное квадратичное действие над Q + завершение квадрата, НЕ вывод полного действия ЭГ из геометрии. _(regge, einstein, variational, L4, minimum)_

**Uniqueness - score 3 (new-framing).** Сорсированное дискретное уравнение Эйнштейна delta=kappa*m как ГЛОБАЛЬНЫЙ минимум Regge+matter-действия над Q, прочитанное как L4 (достаточное основание) на поле — новый sourced-случай поверх вакуумного слоя.
> _Caveat:_ Вариационный принцип, sourced field equation и завершение квадрата классичны; действие здесь модельное квадратичное над Q, НЕ вывод полного действия ЭГ из геометрии. Уровень: синтез+наблюдение.

---

## #418 - `src/foundation/VoidInexhaustible.v` - score 1 (exposition)

**The void is inexhaustible: surplus C(K,2) grows without bound, surplus/K = (K-1)/2 -> infinity**

- **Topic.** Surplus(K)=K(K-1)/2 (potential pairs minus actualized); concrete surplus values (K=3..100), strict growth across steps, and the Socrates ratio surplus(K)/K = (K-1)/2 (2, 9/2, 19/2) growing without bound.
- **Role.** Foundation/philosophy combinatorics. Standalone (Stdlib only). Sibling of TwoMechanisms.v (same K(K-1)/2 surplus).
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lia ZArith Lqa
- **E/R/R.** _Elements:_ K актуализированных; surplus = K(K-1)/2 избыточных пар. _Roles:_ избыток = роль непрерывно растущего потенциала; отношение surplus/K = роль 'неисчерпаемости'. _Rules:_ surplus = K(K-1)/2; surplus_grows; socrates ratio (K-1)/2 -> inf. _P4:_ K конечно актуализировано, но избыток (пары) растёт неограниченно — потенциал неисчерпаем (P4: конечная актуальность, незавершённый потенциальный запас).
- **Classical counterpart.** Surplus = C(K,2) and the ratio surplus/K = (K-1)/2 -> infinity — elementary combinatorics; the 'void is inexhaustible' framing is the only novelty, no classical theorem.
- **Tags.** foundation, combinatorics, void, exposition

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `pot_v/surplus` | Definition | потенциал и избыток |
| `surplus_3/_5/_10/_20/_100` | Lemma | конкретные значения избытка |
| `surplus_grows_3_5/_5_10/_10_20/surplus_increases` | Lemma | избыток строго растёт |
| `socrates_5/_10/_20/socrates_grows` | Lemma | ★ отношение surplus/K = (K-1)/2 -> inf |

**Key lemmas (deep):**

- **`socrates_grows`** - surplus(K)/K = (K-1)/2 принимает значения 2, 9/2, 19/2 и растёт без границы — формальная сторона тезиса 'пустота неисчерпаема' (потенциал/актуальное -> inf). Содержательно = тривиальная арифметика треугольных чисел; ценность файла в обрамлении, а не в доказательствах. NB: surplus_20=190 (а не 210 как total в TwoMechanisms) — это только пары, без K. _(combinatorics, surplus, inexhaustible, ratio)_

**Uniqueness - score 1 (exposition).** Пустота неисчерпаема: избыток C(K,2) растёт неограниченно, отношение surplus/K=(K-1)/2 -> бесконечность.
> _Caveat:_ Элементарная комбинаторика (треугольные числа, линейное отношение); 'неисчерпаемость пустоты' — философское обрамление, не теорема.

---

## #419 - `src/foundation/VoidLogicDuality.v` - score 1 (exposition)

**Void-Logic (Content/Form) duality: trivial-True potential + list growth (mostly reflexivity)**

- **Topic.** Aspect = Content|Form; void_potential d := True (so 'inexhaustible/unchanging' are exact I); form_at_stage K := Form (so 'form invariant' is reflexivity); D as growing list with concrete chain D_0..D_3; aspect decidability; both aspects needed.
- **Role.** Foundation/philosophy file. Standalone (Stdlib only). Illustrative duality narrative; not a dependency.
- **Counts.** Qed 20 / Admitted 0 / axioms 0
- **Imports.** Stdlib: List Nat Arith Lia
- **E/R/R.** _Elements:_ Aspect (Content/Form); void_potential (=True); D как список. _Roles:_ пустота = полнота потенциала (роль); логика = форма = неизменное (роль). _Rules:_ void_inexhaustible; form_unchanging; D_grows; both_needed. _P4:_ пустота (потенциал) неисчерпаема и неизменна; D актуализируется и растёт; форма самообоснована — но формально это True/reflexivity.
- **Classical counterpart.** No classical theorem. A philosophical Content/Form (void/logic) duality where void_potential := True; the Coq content is reflexivity / exact I on trivial propositions plus elementary list-length growth. Over-branded 'duality' lemmas flagged.
- **Tags.** foundation, void, duality, trivial, exposition

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `Aspect/void_potential/form_at_stage/DSet/actualize` | Definition | аспекты, пустота (=True), форма, D |
| `content_is_not_form/void_inexhaustible/void_unchanging/form_unchanging/D_grows/void_still_full/form_still_same` | Lemma | дуальность (на тривиальных пропозициях) |
| `D_0/D_1/D_2/D_3/D_grows_01/_12/_23` | Definition/Lemma | конкретная цепочка D растёт |
| `content_in_form_stable/both_needed/void_needs_form/form_needs_void/actualize_preserves_void/_form/D_chain_increasing` | Lemma | дуальность взаимна, сохраняется |
| `aspect_eq_dec/actualize_head/D_3_contains_1` | Lemma | разрешимость аспекта; голова; вхождение |

**Key lemmas (deep):**

- **`void_needs_form / form_needs_void`** - Заявлены как 'дуальность: ни одно не существует без другого', но формально void_needs_form := (void_potential d -> form_at_stage 0 = Form) доказывается reflexivity, а form_needs_void через exact I, поскольку void_potential := True. Это РЕФЛЕКСИВНОСТЬ-УРОВЕНЬ леммы (как Void/L5 в рубрике), а не содержательная дуальность. Реальное содержание = только рост длины списка D. _(void, duality, trivial, reflexivity)_

**Uniqueness - score 1 (exposition).** Дуальность Содержание/Форма (пустота/логика): пустота неисчерпаема, форма инвариантна, D актуализируется и растёт.
> _Caveat:_ ОВЕР-БРЕНДИНГ: void_potential:=True, form_at_stage:=Form, поэтому почти все 'дуальность'-леммы — reflexivity/exact I на тривиальных пропозициях; единственное реальное содержание — рост длины списка. Не теорема.

---

## #420 - `src/foundation/VoidLogicSynthesis.v` - score 1 (exposition)

**Void-Logic grand synthesis (asp_ re-encoding): same trivial duality, restated**

- **Topic.** Asp = AContent|AForm; asp_void_potential := True, asp_form_at := AForm; eight 'synthesis' lemmas (aspects distinct, void inexhaustible, form invariant, D grows, both needed, duality closed) plus a grand-duality and self-preservation lemma — all reflexivity/exact I except list growth.
- **Role.** Foundation/philosophy capstone of the void-logic pair. Standalone (Stdlib only). Restatement of VoidLogicDuality.v; not a dependency.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: List Nat Arith Lia
- **E/R/R.** _Elements:_ Asp (AContent/AForm); asp_void_potential (=True); asp_DSet. _Roles:_ большой синтез дуальности пустота-логика; замыкание дуальности. _Rules:_ synth_void_inexhaustible; synth_form_invariant; synth_D_grows; synth_grand_duality. _P4:_ дуальность самоподдерживается через актуализацию — но формально True/reflexivity; реальный рост только в длине D.
- **Classical counterpart.** No classical theorem. The 'grand synthesis' of the Void-Logic duality; same trivial-True/reflexivity pattern as VoidLogicDuality.v with renamed (asp_-prefixed) symbols and a shorter list chain. Over-branded.
- **Tags.** foundation, void, synthesis, trivial, exposition

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `Asp/asp_void_potential/asp_form_at/asp_DSet/asp_actualize` | Definition | переименованные аспекты, пустота (=True), D |
| `synth_aspects_distinct/synth_void_inexhaustible/synth_form_invariant/synth_D_grows/synth_both_needed/synth_duality_closed` | Lemma | восемь 'синтез'-лемм (тривиальны) |
| `synth_D0/D1/D2/synth_chain_grows/synth_existence_requires_both` | Definition/Lemma | цепочка D растёт; существование требует обоих |
| `synth_grand_duality/synth_self_preserving` | Lemma | ★ большая дуальность; самосохранение (reflexivity) |

**Key lemmas (deep):**

- **`synth_grand_duality`** - 'Большая теорема: дуальность полна и неприводима' = (AContent<>AForm) /\ (forall d, asp_void_potential d) /\ (forall K, asp_form_at K = AForm) — доказывается discriminate + (intro; exact I) + reflexivity, поскольку void:=True и form:=AForm. Чистый рефлексивность-уровень (рубрика прямо помечает такие 'Void' леммы как over-branded). Дублирует VoidLogicDuality с asp_-префиксами. _(void, synthesis, trivial, reflexivity)_

**Uniqueness - score 1 (exposition).** Большой синтез дуальности пустота-логика: аспекты различны, пустота неисчерпаема, форма инвариантна, дуальность самоподдерживается.
> _Caveat:_ ОВЕР-БРЕНДИНГ и дублирование: те же тривиальные (True/reflexivity/exact I) леммы, что в VoidLogicDuality.v, с переименованными символами; реальное содержание — лишь рост длины списка. Не теорема.

---

## #421 - `src/foundation/VolumeDimension.v` - score 2 (methods)

**Volume = number in D dimensions: count s^D, dimension from scaling, Hauptvermutung open**

- **Topic.** vol_D D s := s^D (number = volume); 1D recovers H19 (linear), 4D gives s^4; dimension recovered from doubling (vol_D D (2s)=2^D*vol_D D s, Myrheim-Meyer); same D sets metric DOF (4->10, Malament); unique-manifold limit (Hauptvermutung) marked Conjectural.
- **Role.** Q3 of the open agenda; extends NumberIsVolume (H19) and Malament DOF (H20) to D dims. Standalone (Stdlib Arith/Lia). Honestly separates Proven core from Conjectural wall.
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith Lia
- **E/R/R.** _Elements:_ vol_D D s := s^D; vol_D 1 s = s (H19); vol_D D (2s)=2^D vol_D D s; metric_dof 4 = 10. _Roles:_ счёт интервала = объём (любая D); показатель масштабирования = размерность D; та же D задаёт DOF D(D+1)/2. _Rules:_ vol_is_count; dimension_from_scaling; dim4_dof10; hauptvermutung_open. _P4:_ ядро Q3 делается над nat -- number=volume на D измерений (объём causal diamond=s^D), размерность из счёта (Мирхейм-Мейер); СТЕНА: полная Hauptvermutung открыта (Conjectural, честно помечено).
- **Classical counterpart.** Causal-set 'number = volume' and the Myrheim-Meyer dimension estimator (count ~ s^D, doubling => x2^D) and Malament metric DOF D(D+1)/2 — known causal-set theory; the Hauptvermutung (sprinkling -> unique manifold) is honestly marked OPEN/Conjectural.
- **Tags.** foundation, causal-set, dimension, volume, methods

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `vol_D/vol_is_count/vol_1_linear/vol_4` | Definition/Lemma | число = объём в D измерениях (s^D) |
| `dimension_from_scaling/scaling_1D/scaling_4D` | Lemma | ★ размерность из масштабирования счёта (Мирхейм-Мейер) |
| `metric_dof/dim4_dof10` | Definition/Lemma | та же D даёт DOF D(D+1)/2 (4->10) |
| `Q3Claim/Status/q3_status/hauptvermutung_open/core_proven` | Definition/Lemma | ядро доказано, Hauptvermutung открыта |
| `number_is_volume_3plus1D` | Theorem | капстоун |

**Key lemmas (deep):**

- **`dimension_from_scaling`** - vol_D D (2*size) = 2^D * vol_D D size — удвоение линейного размера умножает счёт на 2^D, так что размерность D читается из масштабирования числа (оценщик Мирхейма-Мейера). Идеализированное масштабирование s^D и связь с метрическими DOF доказаны; статистический оценщик и сходимость к единственному многообразию (Hauptvermutung) честно оставлены открытыми. Содержательно = известная causal-set теория, аккуратно формализованная на идеализированном ядре. _(causal-set, myrheim-meyer, dimension, volume)_

**Uniqueness - score 2 (methods).** Число = объём в D измерениях (vol=s^D), размерность восстанавливается из масштабирования счёта (Мирхейм-Мейер), та же D задаёт метрические DOF (4->10); полная Hauptvermutung открыта.
> _Caveat:_ Number=volume, оценщик Мирхейма-Мейера и DOF Маламента — известная causal-set теория; формализуется лишь идеализированное масштабирование; сходимость к единственному многообразию честно помечена Conjectural.

---

## #422 - `src/foundation/WallTaxonomyReflexive.v` - score 2 (methods)

**Reflexive turn: the wall taxonomy classifies its own incompleteness (HardStructure)**

- **Topic.** Re-encodes the 4 WallType<->4 MissingInput bijection (injective+surjective); coverage is empirical (6 magnitudes checked, length=6); self-classification: bijection=DerivedCore, exhaustiveness=OpenRim; the gem: taxonomy's own wall-type is HardStructure (lacks a proof of completeness).
- **Role.** Reflexive companion to WallTaxonomySynthesis.v. Standalone (Stdlib List/Arith). Pure decidable enum bookkeeping; honesty/Munchhausen demonstration.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: List Arith
- **E/R/R.** _Elements:_ WallType/MissingInput (4+4); биекция; 6 проверенных магнитуд; самоклассификация. _Roles:_ Биекция = выведенное ядро (теорема); Исчерпываемость = открытый край (эмпирика) = HardStructure. _Rules:_ bijection_injective/surjective; coverage_empirical; self_application (lacks HardStructure = AProof). _P4:_ таксономия, спущенная СВОИМ методом, расщепляется: ядро (биекция, доказано) + край (исчерпываемость, открыто); собственный край = HardStructure; метод НЕ освобождает себя (Мюнхгаузен).
- **Classical counterpart.** No classical theorem; a meta/reflexive bookkeeping file. Applies its own 4-type wall taxonomy to itself: the type<->missing-input bijection is a (trivial finite) theorem, exhaustiveness is empirical, and the taxonomy's own gap is one of its own types (HardStructure). Munchhausen-honest.
- **Tags.** foundation, reflexive, taxonomy, honesty, methods

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `WallType/MissingInput/lacks` | Definition | 4 типа стен <-> 4 недостающих входа |
| `bijection_injective/bijection_surjective` | Lemma | ★ биекция типы<->входы (выведенное ядро) |
| `Magnitude/checked/coverage_empirical` | Definition/Lemma | ★ покрытие эмпирично (6 проверено, не все) |
| `TaxonomyAspect/MetaStatus/aspect_status/self_classification` | Definition/Lemma | биекция=ядро, исчерпываемость=край |
| `taxonomy_own_wall_type/self_application` | Definition/Lemma | ★ собственный край = HardStructure (lacks AProof) |
| `taxonomy_reflexive` | Theorem | капстоун: рефлексивный вердикт |

**Key lemmas (deep):**

- **`self_application`** - lacks taxonomy_own_wall_type = AProof — гем: собственный пробел таксономии (исчерпываемость не доказана) классифицируется ОДНИМ из её же 4 типов (HardStructure, 'недостаёт доказательства'). Метод не освобождает себя — само-консистентность (Мюнхгаузен-честность). Содержательно = reflexivity по конечному типу; ценность исключительно в рефлексивном наблюдении, не в математике. _(reflexive, taxonomy, munchhausen, honesty)_

**Uniqueness - score 2 (methods).** Таксономия стен, спущенная СВОИМ методом, расщепляется на выведенное ядро (биекция типы<->входы) + открытый край (исчерпываемость = HardStructure); метод не освобождает себя (Мюнхгаузен-честно).
> _Caveat:_ Мета-рефлексивная бухгалтерия по конечному перечислению (доказательства = reflexivity/discriminate); биекция тривиальна (4<->4); ценность в наблюдении само-консистентности, не в теореме.

---

## #423 - `src/foundation/WallTaxonomySynthesis.v` - score 2 (methods)

**Wall taxonomy (corrected H1): 4 wall-types <-> 4 kinds of missing input (3 genuine + 1 deflationary)**

- **Topic.** 4 WallType <-> 4 MissingInput bijection (lacks injective+surjective); the 6 descended magnitudes classified (arrow/Born=SymmetryChoice, Lambda/J=BareHierarchy, NS=HardStructure, departure=FiniteButUncomputed); type counts 2,2,1,1; 3 genuine wall-types, 1 deflationary.
- **Role.** Synthesis of the descent series (corrected H1) over the wall/role-limit cluster; classified by WallTaxonomyReflexive.v in turn. Standalone (Stdlib List/Arith). Anti-flattening observation, no value derived.
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib: List Arith
- **E/R/R.** _Elements:_ WallType(4)/MissingInput(4); биекция lacks; 6 магнитуд; счётчики типов. _Roles:_ каждый тип = сигнатура рода недостающего входа; выведенная структура = общая сторона. _Rules:_ lacks_injective/surjective; mag_type; type_counts; three_genuine. _P4:_ исправленный H1: role-limit-сторона НЕ одна стена -- таксономия 4 типов по роду недостающего входа (биекция); 3 настоящих + 1 дефляционный; общий паттерн: вывод даёт структуру, стена = недостающий вход; ОБЪЯСНЯЕТ гетерогенность, не стирает.
- **Classical counterpart.** No classical theorem; a meta/synthesis bookkeeping file. The 'corrected H1': the wall/role-limit side is heterogeneous, a 4-type taxonomy organized by the KIND of missing input (structure/value/proof/nothing), with the type<->input map a (trivial finite) bijection. Explicit anti-flattening/anti-overclaim.
- **Tags.** foundation, taxonomy, wall, honesty, methods

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `WallType/MissingInput/lacks` | Definition | 4 типа <-> 4 входа (структура/значение/доказательство/ничего) |
| `lacks_injective/lacks_surjective` | Lemma | ★ биекция типы<->входы |
| `Magnitude/mag_type/mag_classification` | Definition/Lemma | 6 магнитуд классифицированы по типу |
| `wt_eqb/all_mags/type_count/type_counts` | Definition/Lemma | счётчики типов 2,2,1,1 |
| `is_genuine/all_types/three_genuine/one_deflationary` | Definition/Lemma | ★ 3 настоящих стены + 1 дефляционная |
| `wall_taxonomy_synthesis` | Theorem | капстоун: исправленный H1 |

**Key lemmas (deep):**

- **`lacks_injective / lacks_surjective`** - Карта WallType -> MissingInput биективна: четыре типа стен суть ровно четыре рода недостающего входа (структура/значение/доказательство/ничего). Это организующее НАБЛЮДЕНИЕ исправляет грубое 'всё упирается в ОДНУ стену H1', объясняя гетерогенность role-limit-стороны. Содержательно = тривиальная биекция по конечным типам (intros [] []; discriminate); ценность в анти-уплощающем наблюдении + явной честности (3 настоящих, 1 дефляционный; полнота не доказана a priori). _(taxonomy, wall, missing-input, anti-overclaim)_

**Uniqueness - score 2 (methods).** Исправленный H1: role-limit/стена-сторона НЕ одна стена, а таксономия 4 типов по роду недостающего входа (биекция типы<->входы); 3 настоящих + 1 дефляционный; гетерогенность объяснена, не стёрта.
> _Caveat:_ Мета-классификация по конечному перечислению (биекция 4<->4 тривиальна, intros/discriminate); основана на 6 спусках, а не доказательстве априорной исчерпываемости; никакое значение не выводится. Ценное анти-уплощающее наблюдение, не теорема.

---

## #424 - `src/foundation/WashoutNonTransfer.v` - score 3 (new-framing)

**SM washout does NOT transfer to ToS: equilibrium-premise false (arrow) => eta != 0 (magnitude open)**

- **Topic.** Washout as the implication equilibrium (fwd=bwd) => eta=0; a positive net departure => eta>0; the two inputs mutually exclusive; with the real CP and B-violation factors, equilibrium => eta=0 (SM branch) but the arrow (fwd!=bwd) => eta!=0 (ToS branch, no washout).
- **Role.** Baryogenesis Phase 4 (core). Imports SakharovERR (eta_triad, eta_pos_if_all) + BaryogenesisTransport (cp_factor/bviol_factor + positivity). Honestly bounds the claim to 'no washout', not a derived eta_B.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lqa; ToS: foundation.SakharovERR; ToS: foundation.BaryogenesisTransport
- **E/R/R.** _Elements:_ скорости fwd, bwd; departure fwd-bwd (грань L5); eta = eta_triad cp b (fwd-bwd). _Roles:_ равновесие (SM) => departure 0 => eta=0; необратимость (ToS) => departure!=0 => eta!=0. _Rules:_ washout (равновесие=>eta=0); arrow_no_washout (fwd!=bwd=>eta!=0); premises_exclusive. _P4:_ SM-провал (вымывание) НЕ переносится — его посылка (равновесие) ЛОЖНА в ToS (P4/стрела); ToS-результат eta!=0 genuinely иной (вход отличается); но стрела даёт лишь направление (!=0), не знак/магнитуду — число = открытый ящик.
- **Classical counterpart.** The SM electroweak-baryogenesis washout (sphalerons in thermal equilibrium => detailed balance => net asymmetry erased, the ~10^9 shortfall) is standard; the contribution is showing the washout's PREMISE (equilibrium) is structurally false in ToS (P4/arrow), so eta does NOT wash out (eta != 0) — but sign/magnitude stay open.
- **Tags.** foundation, baryogenesis, washout, arrow, new-framing

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `Qpos_nonzero` | Lemma | положительное => ненулевое |
| `washout/non_equilibrium_admits_pos` | Lemma | ★ равновесие=>eta=0 (SM-провал); положит. departure=>eta>0 |
| `arrow_no_washout/premises_exclusive` | Lemma | ★ fwd!=bwd=>eta!=0; входы взаимоисключающи |
| `eta_washout/eta_washout_equilibrium/eta_washout_arrow` | Definition/Lemma | ★ с реальными CP/B-факторами: SM=>0, стрела=>!=0 |
| `washout_does_not_transfer` | Theorem | капстоун: SM-вымывание не переносится |

**Key lemmas (deep):**

- **`eta_washout_arrow`** - С реальными выведенными CP и B-нарушающими факторами: стрела (fwd!=bwd) => eta_washout != 0, то есть асимметрия НЕ вымывается. Ключ: SM-провал — это импликация 'равновесие => eta=0', а её посылка ложна в ToS (процесс необратим, P4/стрела). Поэтому ToS не наследует SM-разрыв ~10^9. ЧЕСТНО (явно в файле): стрела даёт направление (!=0), НЕ знак и НЕ магнитуду — eta_B остаётся открытым; ToS не 'решает' бариогенезис. Сам washout-аргумент классичен; вклад = диагностика непереноса посылки. _(baryogenesis, washout, arrow, non-transfer, eta)_

**Uniqueness - score 3 (new-framing).** SM-вымывание бариоасимметрии НЕ переносится в ToS: его посылка (тепловое равновесие) структурно ложна (P4/стрела), поэтому eta != 0 (нет вымывания) — иной результат, чем SM eta=0, потому что вход отличается.
> _Caveat:_ Сам washout-аргумент (равновесие=>детальный баланс=>стирание) — стандартная физика; стрела даёт лишь НАПРАВЛЕНИЕ (eta!=0), НЕ знак и НЕ магнитуду; eta_B = открытый ящик; ToS не выводит значение и не 'решает' бариогенезис.

---

## #425 - `src/foundation/WeinbergAngleDerivation.v` - score 2 (methods)

**sin^2(theta_W) = 3/13 as a degrees-of-freedom fraction over Q (DOF counting, zero free parameters)**

- **Topic.** Three steps: U(1)_Y geometric (depth-2 reflexive = phase), SU(3) confined (excluded from EW mixing), mixing = DOF fraction by P1; r = dim(SU2)/n_metric = 3/10, sin^2 = r/(1+r) = 3/13 = 0.2308, vs observed 0.2312 (error < 1/1000); other DOF choices (8/10,1/10,3/4,3/8) shown to miss.
- **Role.** Foundation 'closes the last gap in sin^2(theta_W)=3/13'. Reused by ThreeFormulasBridge.v and ProcessRGWeinberg context. Standalone (Stdlib only). The project's flagship over-branded numerical claim.
- **Counts.** Qed 21 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith List Bool Lqa
- **E/R/R.** _Elements:_ калибровочные DOF (dim SU2=3); метрические DOF (n_metric=10); угол смешивания. _Roles:_ внутренние (SU(2)) vs внешние (метрика) Правила; U(1)_Y геометрический; SU(3) конфайнирован. _Rules:_ U1_is_geometric; SU3_confined; r_is_3_over_10; sin2_is_3_over_13. _P4:_ конечный DOF-счёт над Q (Element); sin^2 = доля DOF = 3/13; ноль свободных параметров В ЦЕПОЧКЕ, но три структурных отождествления — модельный вход E/R/R, не вывод из электрослабой теории.
- **Classical counterpart.** The Weinberg angle sin^2(theta_W); HERE 'derived' as a DOF fraction dim(SU2)/(dim(SU2)+n_metric)=3/13 via three structural identifications (U(1)_Y geometric, SU(3) confined, P1 equal-weight g^2 ~ 1/dim). Numerically 0.231 (~0.2% from observed) but the identifications are NOT standard electroweak theory.
- **Tags.** foundation, weinberg, dof-counting, over-branded, methods

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `DistinctionDepth/GaugeOrigin/gauge_origin/U1_is_geometric/SU2_is_intrinsic/SU3_is_intrinsic` | Definition/Lemma | ★ шаг 1: U(1)_Y геометрический (рефлексивная глубина 2) |
| `ConfinementStatus/confinement/SU3_confined/SU2_unconfined/participates_in_EW_mixing/SU2_mixes/SU3_doesnt_mix/U1_mixes` | Definition/Lemma | ★ шаг 2: SU(3) конфайнирован, вне смешивания |
| `D_spacetime/n_metric/dim_SU2/dim_SU3/dim_U1/n_metric_is_10/dim_SU2_is_3` | Definition/Lemma | размерности (n_metric=10, dim SU2=3) |
| `r_weinberg/r_is_3_over_10/sin2_weinberg/sin2_is_3_over_13` | Definition/Lemma | ★ шаг 3: r=3/10, sin^2=3/13 |
| `cos2_weinberg/cos2_is_10_over_13/sin2_cos2_sum/sin2_observed/prediction_matches/prediction_error_small` | Definition/Lemma | cos^2=10/13; сравнение с 0.2312 (ошибка<0.1%) |
| `wrong_su3/wrong_u1/wrong_no_gravity/wrong_su5` | Lemma | другие DOF-выборы промахиваются (8/18,1/11,3/4,3/8) |
| `weinberg_angle_derivation` | Theorem | капстоун: грандиозный синтез |

**Key lemmas (deep):**

- **`sin2_is_3_over_13`** - sin^2(theta_W)=r/(1+r)=3/13 при r=dim(SU2)/n_metric=3/10 — численно 0.2308, ~0.2% от наблюдаемого 0.2312. Форма r/(1+r) совпадает со стандартной sin^2=g'^2/(g^2+g'^2), но СОДЕРЖАНИЕ r иное: отношение калибровочных к геометрическим DOF вместо отношения двух связей. Три отождествления (U(1)_Y геометрический, SU(3) конфайнирован, P1: g^2~1/dim) — структурные постулаты E/R/R, НЕ выводы из электрослабой теории. Совпадение впечатляет, но это подгонка DOF-счёта под известное число, а не вывод из первопринципов; рубрика прямо помечает 'sin^2 theta_W=3/13' как ОВЕР-БРЕНДИНГ. _(weinberg, dof-counting, 3/13, over-branded)_

**Uniqueness - score 2 (methods).** sin^2(theta_W)=3/13 как доля DOF dim(SU2)/(dim(SU2)+n_metric) с нулём свободных параметров в цепочке; численно 0.231 (~0.2% от PDG); другие DOF-выборы промахиваются.
> _Caveat:_ ОВЕР-БРЕНДИНГ (рубрика называет явно): 'вывод' опирается на три нестандартных структурных отождествления (U(1)_Y геометрический, SU(3) конфайнирован, P1: g^2~1/dim), которые НЕ выводятся из электрослабой теории; форма r/(1+r) совпадает со стандартной, но это подгонка DOF-счёта под известное число, а не первопринципный вывод. HEADER DRIFT: заявлено 25 Qed, фактически 21.

---

## #1841 - `src/foundation/GapPythagoreanBoundary.v` - score 4 (synthesis+observation)

**Gap-Pythagorean boundary over Q: the traceless-2x2 spectral gap is Element iff (eps,del,gap/2) is Pythagorean (vein A at tr=0)**

- **Topic.** The universal gap Hamiltonian [[eps,del],[del,-eps]] (graphene/BCS/SSH/Ising) is traceless with disc=4(eps^2+del^2); its gap is a rational Element iff eps^2+del^2 is a perfect square iff (eps,del,gap/2) is a Pythagorean triple - vein A's rational_eigenvalue_iff_disc_square specialised to tr=0; decidable for integer (eps,del).
- **Role.** Cross-cluster bridge: vein A (DiscriminantCompleteEigenvalue) -> the physics gap cluster (graphene/BCS/SSH/Ising). Imports foundation.DiscriminantCompleteEigenvalue + H1ConstructivityDecidable.
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** ToS: foundation.DiscriminantCompleteEigenvalue; ToS: foundation.H1ConstructivityDecidable; Stdlib: QArith, Lqa, ZArith
- **E/R/R.** _Elements:_ бесследовая симметричная 2x2 H(eps,del)=[[eps,del],[del,-eps]]; инварианты tr=0, det=-(eps^2+del^2), disc=4(eps^2+del^2); щель G=2sqrt(eps^2+del^2). _Roles:_ off-diagonal del = связь/coupling (хоппинг/спаривание); G = спектральная наблюдаемая/масса; рацио-щель = Element, иррацио = role-limit; полный-квадрат = вентиль вены A. _Rules:_ gap_element_iff_pythagorean (G in Q <=> eps^2+del^2 квадрат); gap_element_iff_disc_square (литеральный мост к вене A); gap_element_decidable_Z (целые => разрешимо). _P4:_ Element-щели = рациональные точки окружности eps^2+del^2=кв (мера 0, плотны, разрешимы); почти все физ-щели = континуум-role-limit; физика наследует вену A.
- **Classical counterpart.** Completing-the-square criterion for rational eigenvalues of a 2x2 is elementary; the rational-circle / Pythagorean-triple parametrization is classical number theory. NEW only as the observation that the universal traceless-2x2 gap Hamiltonian inherits vein A's perfect-square boundary, unifying the physics gap cluster with q-kinematics.
- **Tags.** foundation, vein-A, gap, pythagorean, discriminant, q-kinematics, synthesis+observation, H62

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `gap_tr_zero/gap_det_value/gap_disc_value` | Lemma | инварианты бесследовой 2x2: tr=0, det=-(eps^2+del^2), disc=4(eps^2+del^2) |
| `gap_chareq` | Lemma | характеристическое уравнение x^2=eps^2+del^2 |
| `gap_element_iff_pythagorean` | Theorem | ★ щель Element <=> (eps,del,G/2) пифагорова |
| `gap_element_iff_disc_square` | Corollary | ★ литеральный мост к вене A (rational_eigenvalue_iff_disc_square) |
| `gap_disc_Z/gap_element_decidable_Z` | Definition/Corollary | разрешимость для целых (eps,del) |
| `graphene_element/bcs_1_half_role_limit/bcs_345_element` | Example | инстансы: графен Element, BCS(1,1/2) role-limit sqrt5, BCS(4,3) тройка 3-4-5 -> рацио щель 5 |
| `gap_pythagorean_boundary` | Theorem | капстоун |

**Key lemmas (deep):**

- **`gap_element_iff_pythagorean`** - Универсальный гамильтониан щели бесследов, поэтому его статус Element/role-limit = пифагорово число-теоретическое условие. Сужение rational_eigenvalue_iff_disc_square (вена A) на tr=0; унифицирует gap-кластер (графен/BCS/SSH/Ising) с веной A и пифагоровой нитью q-kinematics. Алгебра классическая; новое - наблюдение/унификация. _(vein-A, gap, pythagorean, discriminant, bcs, graphene, synthesis)_

**Uniqueness - score 4 (synthesis+observation).** Бесследовая 2x2 = универсальный гамильтониан щели; щель Element <=> (eps,del,gap/2) пифагорова <=> disc полный квадрат - вентиль вены A при tr=0, унифицирующий весь gap-кластер физики с q-kinematics.
> _Caveat:_ Алгебра (completing the square) и пифагорова параметризация классичны; мета-паттерн рацио=Element уже H5/H6/H7. Ново - наблюдение бесследовости + кросс-кластерная унификация, не новая теорема. YM характерный трансфер - отдельная проверка.

---

## #1842 - `src/foundation/CayleyFourierMassBridge.v` - score 4 (synthesis+observation)

**Cayley-Fourier-mass bridge over Q: one map (4-l^2)/(4+l^2) is the Fourier transfer eigenvalue AND the lattice mass-gap input AND a rational circle point (6th-vein spectral arm)**

- **Topic.** cayley_eigenvalue (analysis/FourierCayleyConnection) and Re_cayley (lattice/MassFromSpectrum) are byte-identical with no shared import; this file proves they coincide, so the lattice mass gap is a function of the Fourier eigenvalue, and Re^2+Im^2=1 (rational unit circle) makes the Z^3 masses Pythagorean (-3/5,-15/17,-35/37).
- **Role.** Cross-cluster bridge (analysis <-> lattice <-> geometry): the spectral arm of the candidate 6th (Cayley) vein. Imports analysis.FourierCayleyConnection + lattice.MassFromSpectrum (both stdlib-only).
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** ToS: analysis.FourierCayleyConnection; ToS: lattice.MassFromSpectrum; Stdlib: QArith, Qabs, Lqa
- **E/R/R.** _Elements:_ единая функция C(l)=(4-l^2)/(4+l^2); Fourier-имя cayley_eigenvalue, lattice-имя Re_cayley; мнимая часть cayley_im=4l/(4+l^2); опорные l in {0,4,8,12}. _Roles:_ C(l)=Кэли-образ собств. значения связи l; Fourier-роль=собств. значение трансфера; lattice-роль=вход масс-щели m=-ln\|C(l)\|; (C,Im)=рацио-точка единичной окружности (q-kinematics). _Rules:_ cayley_fourier_is_mass (cayley_eigenvalue=Re_cayley); mass_proxy_via_fourier; cayley_on_unit_circle (C^2+Im^2=1); массы пифагоровы. _P4:_ масс-щель решётки = функция Fourier-собств-значения через одно Кэли; нулевая мода=безмассовая (неподвижная точка C(0)=1); массы=рацио-точки окружности => пифагоровы => Element (вена A/H62).
- **Classical counterpart.** The Cayley transform (1846), tangent-half-angle / rational-unit-circle parametrization, transfer-eigenvalue powers, and mass=-ln\|transfer eigenvalue\| are all classical. NEW only as the cross-cluster observation that one Cayley map is simultaneously the Fourier transfer eigenvalue, the lattice mass-gap input, and a rational circle point.
- **Tags.** foundation, vein-6-cayley, vein-A, fourier, mass-gap, pythagorean, q-kinematics, cross-cluster, synthesis+observation, H63

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `cayley_fourier_is_mass` | Theorem | ★ cayley_eigenvalue (analysis) = Re_cayley (lattice), reflexivity - две вены, одна функция |
| `mass_proxy_via_fourier/fourier_transfer_is_euclid/mass_4_via_fourier` | Corollary/Example | масс-щель = функция Fourier-собств-значения |
| `zero_mode_is_massless/three_fifths_both` | Theorem/Lemma | нулевая мода=безмассовая; 3/5 в обоих кластерах |
| `cayley_im/cayley_on_unit_circle` | Definition/Lemma | ★ C^2+Im^2=1 - рацио-точка единичной окружности (q-kinematics) |
| `lattice_masses_pythagorean` | Theorem | ★ массы -3/5,-15/17,-35/37 пифагоровы (3-4-5, 8-15-17, 12-35-37) |
| `cayley_fourier_mass_bridge` | Theorem | капстоун |

**Key lemmas (deep):**

- **`cayley_fourier_is_mass`** - Два кластера (analysis, lattice) независимо без общего импорта определяют байт-в-байт одну функцию (4-l^2)/(4+l^2); reflexivity доказывает совпадение => масс-щель решётки = функция Fourier-собств-значения. Спектральная рука кандидата 6-й вены (Кэли-рационализатор). _(vein-6-cayley, fourier, mass-gap, cross-cluster, synthesis)_
- **`lattice_masses_pythagorean`** - Re_cayley на Z^3 даёт -3/5,-15/17,-35/37 = рацио-точки окружности (tangent-half-angle), легированные пифагоровыми тройками 3-4-5/8-15-17/12-35-37 - почему массы решётки рациональны (Element, вена A/H62). _(pythagorean, mass, circle, vein-A, q-kinematics)_

**Uniqueness - score 4 (synthesis+observation).** Одно Кэли (4-l^2)/(4+l^2) = Fourier-собств. значение трансфера = вход масс-щели решётки = рацио-точка окружности => массы решётки пифагоровы; спектральная рука 6-й (Кэли) вены, сшивающая analysis/lattice/geometry без прежнего общего импорта.
> _Caveat:_ Каждый кусок классичен (Кэли 1846, tangent-half-angle, mass=-ln|t|). Ново - машинно-проверенная кросс-кластерная унификация одной функцией; вена D владеет foundation-узлом (Barandes), это её спектральное расширение.

---

## #1843 - `src/foundation/ThreeFifthsUnification.v` - score 2 (methods)

**Three-fifths unification over Q: 3/5 is Cayley(1), the Born entry U00, and the 3-4-5 Schrodinger cosine - one identity, three roles**

- **Topic.** The number 3/5 was proved three times in three clusters: cayley_at_1 (analysis), U00/born_rule_p2 (physics), and the 3-4-5 Schrodinger rotation cosine (process, cited). This file states once that they are the same number and (3/5)^2+(4/5)^2=1 is simultaneously Cayley-on-circle, Born p=2 normalization, and Schrodinger isometry.
- **Role.** Cross-cluster observation tying analysis/physics/process via 3/5; strengthens H63 (6th Cayley vein). Imports analysis.FourierCayleyConnection + physics.BornRuleFromUnitarity.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** ToS: analysis.FourierCayleyConnection; ToS: physics.BornRuleFromUnitarity; Stdlib: QArith, Qabs, Lqa
- **E/R/R.** _Elements:_ число 3/5 (= U00 Борна = cayley_eigenvalue 1 = косинус 3-4-5 поворота); пифагоров партнёр 4/5; тождество (3/5)^2+(4/5)^2=1. _Roles:_ 3/5 в роли Born-амплитуды U00; Cayley-образа C(1); косинуса Шрёдингер-поворота (изометрия); 4/5=пифагоров партнёр. _Rules:_ born_entry_is_cayley_at_1 (U00=C(1)); one_identity_three_readings (тождество=Cayley-окружность=Born p=2=Шрёдингер-изометрия). _P4:_ одно рацио-число и одно пифагорово тождество несут три физ-роли (Борн/Кэли/Шрёдингер) в трёх кластерах; ранее трижды независимо, теперь сшито.
- **Classical counterpart.** The (3,4,5) Pythagorean triple and (3/5)^2+(4/5)^2=1 are elementary. Purely the observation that one number/identity carries the Born rule, the Cayley transfer eigenvalue, and the Schrodinger isometry across three clusters.
- **Tags.** foundation, vein-6-cayley, born, schrodinger, cayley, pythagorean, observation, H63

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `born_entry_is_cayley_at_1` | Theorem | ★ U00 (Борн) = cayley_eigenvalue 1 (Кэли) |
| `schrodinger_cosine_is_cayley_at_1` | Theorem | 3/5 (Шрёдингер cos) = C(1) |
| `one_identity_three_readings` | Theorem | ★ (3/5)^2+(4/5)^2=1 = Cayley-окружность = Born p=2 = Шрёдингер-изометрия |
| `born_p2_is_pythagorean` | Theorem | Born p=2 = целая тройка 3^2+4^2=5^2 |
| `three_fifths_unification` | Theorem | капстоун (+ p=1 fails) |

**Key lemmas (deep):**

- **`one_identity_three_readings`** - Одно пифагорово тождество (3/5)^2+(4/5)^2=1, прочитанное тремя способами: Cayley-на-окружности (analysis), Born p=2 нормировка (physics), Шрёдингер-изометрия (process). Тривиальная алгебра 3-4-5; ценность - наблюдение тождественности ролей в трёх кластерах (нить 6-й вены/H63). _(vein-6-cayley, born, schrodinger, pythagorean, observation)_

**Uniqueness - score 2 (methods).** Одно число 3/5 = Cayley(1) = Born U00 = косинус 3-4-5 Шрёдингер-поворота; одно тождество (3/5)^2+(4/5)^2=1 = Cayley-окружность = Born p=2 = Шрёдингер-изометрия - три роли в трёх кластерах.
> _Caveat:_ Тривиальная алгебра (наименьшая пифагорова тройка); ценность - наблюдение тождественности ролей, не новый результат. Уровень наблюдения, записан для нити 6-й вены H63.

---

## #1844 - `src/foundation/PhysicsEigenvalueVeinA.v` - score 4 (synthesis+observation)

**Physics eigenvalue rationality via vein A: Perron-Frobenius phi and He CI ground state are role-limits, decided 0-axiom by 'is Delta a perfect square?'**

- **Topic.** Two real physics 2x2 eigenvalues connected to rational_eigenvalue_iff_disc_square: the PF/golden spectral radius phi (Delta=5, role-limit/sqrt5) with Element foil [[1,1],[1,1]] (Delta=4), and the Helium CI ground-state energy (Delta=117/65536, role-limit since 117 not a square) - replacing the manual 117=9*13 remark at HeCIEigenvalue.v:21.
- **Role.** Cross-cluster bridge: vein A (DiscriminantCompleteEigenvalue) -> spectral physics (PerronFrobenius, qphysics HeCI). The vein-A physics-reach audit's deliverable. Imports foundation.DiscriminantCompleteEigenvalue + H1ConstructivityDecidable + stdlib.GeneralSqrt.
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** ToS: foundation.DiscriminantCompleteEigenvalue; ToS: foundation.H1ConstructivityDecidable; ToS: stdlib.GeneralSqrt; Stdlib: QArith, Lqa, ZArith
- **E/R/R.** _Elements:_ два реальных физических 2x2 - golden/PF [[1,1],[1,0]] (tr 1, det -1, disc=5) и He CI (tr -1449/256, det 524871/65536, disc=117/65536); Element-фойл full_mat [[1,1],[1,1]] (disc=4). _Roles:_ собств. значение = спектральная наблюдаемая (phi; основная энергия He CI); рацио=Element, иррацио=role-limit; disc-перфект-квадрат = вентиль вены A. _Rules:_ has_rat_eig tr det <=> disc перфект-квадрат; golden_eigenvalue_role_limit (disc=5, rolelimit_5); heci_eigenvalue_role_limit (disc=117/65536, rolelimit_117); full_matrix_element (disc=4=2^2). _P4:_ разрешитель вены A выносит вердикт рациональности реальных физ-собств-значений (phi, He CI), заменяя ручную пометку 117=9*13 (HeCIEigenvalue.v:21). Узость: вена A покрывает ровно 2x2/квадратичные спектры.
- **Classical counterpart.** The discriminant criterion for rational eigenvalues, the irrationality of sqrt5, and the He CI 2x2 are standard. NEW only as connecting real physics eigenvalues (PF golden phi, He CI ground state) to the canonical vein-A 0-axiom decider, replacing hand-written role-limit verdicts.
- **Tags.** foundation, vein-A, helium, perron-frobenius, eigenvalue, role-limit, discriminant, cross-cluster, synthesis+observation, H64

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `golden_disc_is_5` | Lemma | Delta(golden)=tr^2-4det=5 (= golden_discriminant, PerronFrobenius.v:84) |
| `golden_eigenvalue_role_limit` | Theorem | ★ PF/golden phi role-limit (5 не квадрат, rolelimit_5) |
| `full_matrix_element` | Theorem | Element-фойл [[1,1],[1,1]] (Delta=4, собств. 0,2) |
| `heci_disc_is_117/rolelimit_117` | Lemma | Delta(He CI)=117/65536; 117 не перфект-квадрат (10^2<117<11^2) |
| `heci_eigenvalue_role_limit` | Theorem | ★ He CI основная энергия role-limit (заменяет ручную пометку HeCIEigenvalue.v:21) |
| `physics_eigenvalue_vein_A` | Theorem | капстоун |

**Key lemmas (deep):**

- **`heci_eigenvalue_role_limit`** - Основная энергия гелия CI (реальный 2x2 двухэлектронный) есть role-limit (иррациональна): по вене A He CI имеет рациональное собств. значение <=> disc=117/65536 перфект-квадрат <=> 117 перфект-квадрат (65536=256^2) - а 117=9*13 нет. Заменяет ручную пометку HeCIEigenvalue.v:21 каноническим 0-аксиомным разрешителем. _(vein-A, helium, eigenvalue, role-limit, discriminant, synthesis)_
- **`golden_eigenvalue_role_limit`** - Перрон-Фробениусов/золотой спектральный радиус phi = role-limit: golden matrix [[1,1],[1,0]] (= Fibonacci) имеет disc=5, не перфект-квадрат => phi иррационально (sqrt5). Канонический вентиль вены A на реальном спектральном радиусе. _(vein-A, perron-frobenius, golden, role-limit, phi)_

**Uniqueness - score 4 (synthesis+observation).** Канонический разрешитель вены A выносит 0-аксиомный вердикт рациональности реальных физических собств. значений (Перрон-Фробениус phi, основная энергия гелия CI - оба role-limit), заменяя ручные пометки; честно фиксирует УЗОСТЬ вены A (ровно 2x2/квадратичные спектры).
> _Caveat:_ Алгебра дискриминанта, иррациональность sqrt5, He CI 2x2 классичны; ново - подключение реальных физ-собств-значений к каноническому разрешителю + честная калибровка узости (бо'льшие-K косинус-спектры и неспектральные щели вне вены A). Не новая теорема.

---

## #1845 - `src/foundation/CayleyGeometrySpectralBridge.v` - score 4 (synthesis+observation)

**Cayley geometry-spectral bridge over Q: the spectral transfer eigenvalue (4-l^2)/(4+l^2) is a rational SO(2,Q) rotation (the geometry arm of the 6th Cayley vein)**

- **Topic.** The spectral Cayley point (Re_cayley l, cayley_im l) = ((4-l^2)/(4+l^2), 4l/(4+l^2)) is the SO(2,Q) tangent-half-angle rotation chart at s=l/2; it lies on the unit circle and composes/doubles inside SO(2,Q). Concretely the l=4 lattice mass point is the rotation (-3/5,4/5) = the geometry Cayley chart at t=2, doubling to (-7/25,-24/25).
- **Role.** Cross-cluster bridge (lattice/analysis spectral arm <-> geometry rational-rotation arm) of the candidate 6th (Cayley) vein. Imports lattice.MassFromSpectrum + stdlib.RationalRotationGroup.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** ToS: lattice.MassFromSpectrum; ToS: stdlib.RationalRotationGroup; Stdlib: QArith, Qabs, Lqa
- **E/R/R.** _Elements:_ спектральная Кэли-точка (Re_cayley l, cayley_im l)=((4-l^2)/(4+l^2),4l/(4+l^2)); геом. 2D Кэли-карта SO(2,Q) ((1-s^2)/(1+s^2),2s/(1+s^2)); связь s=l/2; инстанс l=4 (масс-точка решётки). _Roles:_ спектральная роль = собств. значение трансфера/масс-щель; геом. роль = элемент SO(2,Q) (рациональные вращения); единый объект = рациональная точка окружности. _Rules:_ spectral_point_on_circle (Re^2+Im^2=1); spectral_composes_in_SO2Q (rcompose замкнут => точка in SO(2,Q)); mass_4_is_rotation (l=4 = карта при t=2 = (-3/5,4/5)); mass_4_doubles ((-7/25,-24/25)). _P4:_ спектральная рука (Fourier/масс) и геом. рука (рациональные вращения) вены F = ОДНА Кэли-карта (t=l/2); масс-щель решётки = косинус рационального вращения; обе руки сшиты.
- **Classical counterpart.** The Cayley transform (1846), the tangent-half-angle parametrization of SO(2,Q), and the two-square (Brahmagupta) closure are classical. NEW only as the cross-cluster observation that the spectral transfer eigenvalue and the rational rotation are ONE Cayley map (t=lambda/2).
- **Tags.** foundation, vein-6-cayley, so2q, rotation, spectral, mass-gap, pythagorean, q-kinematics, cross-cluster, synthesis+observation, H65

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `cayley_im` | Definition | мнимая часть Кэли 4l/(4+l^2) (= AlphaBareLattice.v:25) |
| `spectral_point_on_circle` | Lemma | ★ Re_cayley^2+cayley_im^2=1 — спектральная точка на единичной окружности |
| `spectral_composes_in_SO2Q` | Theorem | ★ спектральная точка композируется как вращение => in SO(2,Q) (rotation_compose_closed) |
| `im_4/mass_4_is_rotation` | Lemma/Theorem | ★ l=4 масс-точка = (-3/5,4/5) = геом. Кэли-карта при t=2, на окружности |
| `mass_4_doubles` | Lemma | удвоение угла: (-3/5,4/5) -> (-7/25,-24/25) (cf. double_345) |
| `cayley_geometry_spectral_bridge` | Theorem | капстоун |

**Key lemmas (deep):**

- **`spectral_composes_in_SO2Q`** - Спектральная Кэли-точка (Re_cayley l, cayley_im l) композируется (комплексное умножение rcompose) с любым рациональным вращением в рациональное вращение через два-квадрата тождество (rotation_compose_closed) => спектральные собств. значения трансфера = подлинные элементы группы рациональных вращений SO(2,Q). Сшивает спектральную руку вены F (Fourier/масс) с геометрической (рациональные вращения) одной Кэли-картой t=l/2. _(vein-6-cayley, so2q, rotation, spectral, cross-cluster, synthesis)_
- **`mass_4_is_rotation`** - l=4 масс-собств-значение решётки = рациональное вращение (-3/5,4/5) = геом. Кэли tangent-half-angle карта при t=2; удваивается в (-7/25,-24/25) (7-24-25). Масс-щель решётки = косинус рационального вращения. _(mass, rotation, pythagorean, tangent-half-angle)_

**Uniqueness - score 4 (synthesis+observation).** Спектральная Кэли-точка (4-l^2)/(4+l^2) = рациональная SO(2,Q) точка вращения = геом. tangent-half-angle карта при t=l/2; масс-щель решётки = косинус рационального вращения. Геометрическая рука 6-й (Кэли) вены, сшитая со спектральной одной картой.
> _Caveat:_ Кэли 1846, tangent-half-angle SO(2,Q), два-квадрата замыкание классичны; ново - машинная кросс-кластерная унификация двух рук вены F одной картой, не новая теорема.

---

## #1846 - `src/foundation/DoublyStochasticForkBridge.v` - score 4 (synthesis+observation)

**Doubly-stochastic fork: the L1-forced doubly-stochastic matrix is the SHARED ROOT of the Born rule (QM) and the second law (arrow of time) (candidate vein G)**

- **Topic.** T(t)=[[1-t,t],[t,1-t]] (apply_T t a=(1-t)a+t(1-a)) forced by L1: conserves total probability; at t=(4/5)^2=16/25 it is the unistochastic |U|^2 of the 3-4-5 unitary (transition probs 9/25,16/25 = |U00|^2,|U01|^2, sum 1 = Born); and it fixes uniform + strictly increases entropy (second law, no Past Hypothesis). One doubly-stochastic object = both Born and the second law.
- **Role.** Cross-cluster bridge (foundation L1 -> thermodynamics second law AND QM Born) — candidate 7th (doubly-stochastic) vein, unifying vein D's unistochastic->Born arm with the majorization->second-law arm. Imports stdlib.foundations.MajorizationSchur + physics.BornRuleFromUnitarity.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** ToS: stdlib.foundations.MajorizationSchur; ToS: physics.BornRuleFromUnitarity; Stdlib: QArith, Lqa, ZArith
- **E/R/R.** _Elements:_ симметричная бистохастическая 2x2 T(t)=[[1-t,t],[t,1-t]] (apply_T t a=(1-t)a+t(1-a)); распределение (a,1-a); бинарная энтропия S2; 3-4-5 объект t=(4/5)^2=16/25. _Roles:_ бистохастичность = сохранение полной вероятности (нормировка Борна); T=\|U\|^2 (унистохастика) = правило Борна (QM-ветвь); смешивание к 1/2 (мажоризация) = второе начало (термо-ветвь); единый объект = L1-вынужденная бистохастика. _Rules:_ apply_T_conserves_probability (apply_T t a + apply_T t (1-a)=1); apply_T_is_born (apply_T(16/25) 1=U00^2=9/25, 0=U01^2=16/25, sum 1); uniform_is_fixed + entropy_increases (второе начало). _P4:_ ОДНА бистохастическая структура (вынужденная L1) даёт И правило Борна (\|U\|^2 при t=квадрат — QM), И второе начало (мажоризация к равномерному, рост энтропии — термо). Необратимость и квантовая вероятность = две грани одного L1-объекта; crystallized на 3-4-5.
- **Classical counterpart.** Birkhoff (doubly-stochastic = convex hull of permutations), Schur-convexity => entropy non-decrease, and unistochastic => Born are classical; the thermo facts here are concrete (vm_compute) not a general Schur theorem. NEW only as the unification: one L1-forced doubly-stochastic matrix is simultaneously Born (its square-parameter case = \|U\|^2) AND the second-law mixing, crystallised on the 3-4-5 object.
- **Tags.** foundation, vein-G-doublystochastic, born, second-law, L1, unistochastic, majorization, arrow-of-time, 3-4-5, cross-cluster, synthesis+observation, H66

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `apply_T_conserves_probability` | Theorem | ★ корень: бистохастика сохраняет полную вероятность (нормировка Борна) |
| `apply_T_is_born` | Theorem | ★★ QM-ветвь: apply_T(16/25) = \|U\|^2 3-4-5 унитария (9/25,16/25 = Борн-вероятности) |
| `born_probs_sum_one` | Lemma | Борн-вероятности суммируются в 1 |
| `uniform_is_fixed` | Theorem | термо-ветвь: равномерное (1/2) — неподвижная точка смешивания |
| `entropy_increases` | Theorem | ★ термо-ветвь: S2 строго растёт под смешиванием (второе начало, без Past Hypothesis) |
| `doubly_stochastic_fork` | Theorem | капстоун: один бистохастический объект -> и Борн, и второе начало |

**Key lemmas (deep):**

- **`apply_T_is_born`** - При t=(4/5)^2=16/25 бистохастическая матрица T(t) ЕСТЬ унистохастика \|U\|^2 3-4-5 унитария U=[[3/5,-4/5],[4/5,3/5]]: переходные вероятности из базисного состояния = \|U00\|^2=9/25, \|U01\|^2=16/25, сумма 1 (born_rule_p2). Так бистохастическое смешивание при квадратном параметре ЕСТЬ правило Борна — QM-ветвь вилки. Crystallized на 3-4-5 (связь с веной F/H63/ThreeFifths). _(vein-G-doublystochastic, born, unistochastic, 3-4-5, cross-cluster, synthesis)_
- **`doubly_stochastic_fork`** - ОДНА L1-вынужденная бистохастическая структура T(t) даёт ОБЕ опоры физики: правило Борна (унистохастика \|U\|^2, нормировка — QM) И второе начало (мажоризация к равномерному, рост энтропии — стрела времени). Вена D именует лишь унистохастика->Борн руку; мажоризация->второе начало — её забытый близнец. Необратимость и квантовая вероятность = две грани одного бистохастического объекта. _(vein-G-doublystochastic, second-law, born, L1, arrow-of-time, synthesis)_

**Uniqueness - score 4 (synthesis+observation).** Одна L1-вынужденная бистохастическая матрица = общий корень правила Борна (QM, унистохастика |U|^2 при квадратном параметре) И второго начала (термо, мажоризация к равномерному + рост энтропии); необратимость и квантовая вероятность = две грани одного объекта. Кандидат 7-й (бистохастической) вены, сшивающий вену D (унистохастика->Борн) с термо-веткой.
> _Caveat:_ Биркгоф/Шур/унистохастика->Борн классичны, термо-факты конкретны (vm_compute), не общая теорема Шура; ново - машинная унификация двух ветвей на одном объекте + L1-корень, не новая теорема.

---

## #1847 - `src/foundation/NormFormTowerBridge.v` - score 4 (synthesis+observation)

**Norm-form tower bridge: the Hurwitz tower (n=1,2,4,8) IS the rational-rotation closure ladder (n=2->SO(2,Q), n=4->SU(2)); Hurwitz {1,2,4,8} = why rotation groups close exactly there (candidate 8th thread)**

- **Topic.** two_square at unit norm = SO(2,Q) closure (= rotation_compose_closed; the n=2 rung carrying vein F's geometry arm + the 3-4-5 object); four_square at unit norm = unit-quaternion/SU(2) closure (Spin(3), double cover of SO(3,Q)); eight_square = octonion Moufang loop. By Hurwitz only n=1,2,4,8 -- the Element-side rotation-group construction terminates at the octonions (dims 3,5,6,7 have no normed multiplication), a meta-finitization.
- **Role.** Cross-cluster bridge (stdlib HurwitzTower norm-form tower <-> rational rotation groups SO(2,Q)/SU(2)) -- candidate 8th thread; ties q-kinematics and vein F. Imports stdlib.HurwitzTower + stdlib.RationalRotationGroup.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** ToS: stdlib.HurwitzTower; ToS: stdlib.RationalRotationGroup; Stdlib: QArith, Lqa, ZArith
- **E/R/R.** _Elements:_ тождества суммы n квадратов (n=1,2,4,8); единичные элементы R/C/H/O; конкретные единицы (3/5,4/5) при n=2 и (1/2,1/2,1/2,1/2) при n=4. _Roles:_ норм-форма мультипликативна = ЗАМЫКАНИЕ группы вращений на каждой размерности; n=2 -> SO(2,Q), n=4 -> SU(2)/Spin(3), n=8 -> октонионный Moufang-loop; {1,2,4,8} = конечный список Element-размерностей. _Rules:_ n2_rung_is_SO2Q_closure (two_square\|unit = rotation_compose_closed); unit_quaternion_closed (four_square\|unit = SU(2)); Гурвиц => только n=1,2,4,8 (мета-финитизация, терминус O). _P4:_ Element-конструкция групп вращений из норм-форм существует РОВНО в dim 1,2,4,8 (Гурвиц) — конечная башня, обрывающаяся на октонионах; dim 3,5,6,7 — role-limit (нет норм-деления). Тот же n=2-рунг несёт вену F (Cayley-точка in SO(2,Q)) и 3-4-5.
- **Classical counterpart.** The two/four/eight-square identities (Brahmagupta/Euler/Degen), Hurwitz's theorem (normed division algebras only in dim 1,2,4,8), and the R->C->H->O ladder are classical; HurwitzTower.v already proves the identities. NEW only as the literal identification of each Hurwitz rung with the rational-rotation closure law + unification with vein F / q-kinematics.
- **Tags.** foundation, norm-form, hurwitz, so2q, quaternion, octonion, rotation, vein-F, q-kinematics, meta-finitization, cross-cluster, synthesis+observation, H67

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `n2_rung_is_SO2Q_closure` | Theorem | ★ n=2 рунг (two_square\|unit) = замыкание SO(2,Q) (= rotation_compose_closed) |
| `unit_quaternion_closed` | Theorem | ★ n=4 рунг (four_square\|unit) = замыкание единичных кватернионов SU(2)/Spin(3) |
| `unit_345_n2/unit_half_quaternion_n4` | Lemma | конкретные единицы: (3/5,4/5) at n=2, (1/2,1/2,1/2,1/2) at n=4 |
| `norm_form_tower_bridge` | Theorem | капстоун: башня = лестница замыкания вращений + Гурвиц-терминус |

**Key lemmas (deep):**

- **`n2_rung_is_SO2Q_closure`** - n=2 рунг Гурвица (two_square Брахмагупта) при единичной норме ЕСТЬ замыкание SO(2,Q) (= rotation_compose_closed): рациональная группа вращений замыкается ПОТОМУ ЧТО 2-квадратная (C) норма мультипликативна. Тот же рунг несёт геометрическую руку вены F (спектральная Cayley-точка in SO(2,Q)) и 3-4-5 объект — норм-форма и q-kinematics/вена F суть один механизм. _(norm-form, hurwitz, so2q, vein-F, q-kinematics, synthesis)_
- **`norm_form_tower_bridge`** - Башня Гурвица норм-форм (n=1,2,4,8) ЕСТЬ лестница замыкания рациональных вращений: n=2->SO(2,Q), n=4->SU(2)/Spin(3) (двойное накрытие SO(3,Q)), n=8->октонионный Moufang-loop. Гурвиц: только эти размерности — Element-конструкция обрывается на октонионах (мета-финитизация); dim 3,5,6,7 = role-limit. Кандидат 8-й нити, связывающий division-algebra ladder с q-kinematics и веной F. _(norm-form, hurwitz, octonion, quaternion, meta-finitization, synthesis)_

**Uniqueness - score 4 (synthesis+observation).** Башня Гурвица норм-форм (n=1,2,4,8) = лестница замыкания рациональных групп вращений (n=2->SO(2,Q)=rotation_compose_closed, n=4->SU(2), n=8->октонионный loop); Гурвиц {1,2,4,8} = почему группы вращений замыкаются ровно там (мета-финитизация). Кандидат 8-й нити, сшивающий division-algebra ladder с q-kinematics и веной F.
> _Caveat:_ Тождества 2/4/8 квадратов, теорема Гурвица, ladder R->C->H->O классичны (и тождества уже в HurwitzTower); ново - литеральное отождествление рунгов с замыканием групп вращений + унификация с веной F/q-kinematics, не новая теорема.

---

## #1848 - `src/foundation/EulerCharProtectedInteger.v` - score 4 (synthesis+observation)

**Euler characteristic = protected integer, computed FOUR ways (curvature/combinatorics/homology/Dirac index) that coincide; the Element-side of 'topological invariant = protected integer' (candidate 9th thread)**

- **Topic.** chi computed by curvature (Gauss-Bonnet angular defect = 2chi, geometry), combinatorics V-E+F, homology Betti b0-b1+b2, and the Dirac index (index-theorem identification) -- for the 2-sphere all four give 2, for the torus combinatorial+Betti give 0. The continuum curvature (pi role-limit) integrates to an INTEGER (Element); integrality IS the topological protection (chi can't change continuously).
- **Role.** Cross-cluster bridge (geometry curvature DiscreteGaussBonnet <-> homology/index H1_IndexTheorem) -- candidate 9th thread (protected integer / topological quantization). Imports geometry.DiscreteGaussBonnet; homology/index side replicated + cited.
- **Counts.** Qed 4 / Admitted 0 / axioms 0
- **Imports.** ToS: geometry.DiscreteGaussBonnet; Stdlib: QArith, ZArith, Lia
- **E/R/R.** _Elements:_ число Эйлера chi (защищённое целое in Z); четыре вычисления - угловой дефект (Gauss-Bonnet, кривизна), V-E+F (комбинаторика), b0-b1+b2 (Betti, гомологии), индекс Дирака; инстансы - сфера (chi=2, 5 платоновых тел), тор (chi=0). _Roles:_ chi = топологический инвариант = Element (целое, дискретное); кривизна (континуум, pi-зависимая) = role-limit, но её интеграл = целое; защищённость = целочисленность (нельзя изменить непрерывно). _Rules:_ Gauss-Bonnet sum-defect/pi = 2chi (геометрия); V-E+F = chi (комбинаторика); b0-b1+b2 = chi (гомологии); index = chi (теорема индекса); все совпадают (сфера 2, тор 0). _P4:_ топологический инвариант = ЗАЩИЩЁННОЕ ЦЕЛОЕ = Element-сторона: континуум-кривизна (role-limit, pi) интегрируется в ЦЕЛОЕ (Element) - целочисленность ЕСТЬ топологическая защита/квантование; chi не меняется при непрерывной деформации (сфера 2 != тор 0).
- **Classical counterpart.** Gauss-Bonnet, Euler-Poincare V-E+F = sum (-1)^i b_i, the genus formula, and the index theorem are classical, and each route is already in the repo. NEW only as the literal coincidence of the four routes on one protected integer, tying geometry curvature to homology/index.
- **Tags.** foundation, protected-integer, topological-invariant, euler-char, gauss-bonnet, homology, index-theorem, quantization, cross-cluster, synthesis+observation, H70

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `euler_betti/index_from_chain/genus_from_euler` | Definition | гомология/индекс/род (реплицировано из H1_IndexTheorem) |
| `sphere_chi_four_ways` | Theorem | ★★ chi(S^2)=2 четырьмя путями: кривизна=комбинаторика=Betti=индекс Дирака |
| `torus_chi_zero` | Theorem | chi(T^2)=0 (комбинаторика+Betti) + род 1 vs 0 - другое защищённое целое |
| `all_platonic_chi_2` | Theorem | все 5 платоновых тел -> sum-defect/pi=4=2chi -> chi=2 (одно целое, 5 дефектов) |
| `euler_char_protected_integer` | Theorem | капстоун: chi = защищённое целое, геометрия<->топология<->спектр |

**Key lemmas (deep):**

- **`sphere_chi_four_ways`** - Число Эйлера сферы = защищённое целое 2, вычисленное ЧЕТЫРЬМЯ генуинно разными путями в разных кластерах: кривизна (Gauss-Bonnet угловой дефект=2chi, геометрия), комбинаторика V-E+F, гомология Betti b0-b1+b2, индекс Дирака (теорема индекса). Геометрия, топология и спектральный индекс СОВПАДАЮТ на одном целом - континуум-кривизна (pi role-limit) интегрируется в целое (Element). _(protected-integer, euler-char, gauss-bonnet, homology, index-theorem, synthesis)_
- **`euler_char_protected_integer`** - Топологический инвариант = ЗАЩИЩЁННОЕ ЦЕЛОЕ = Element-сторона границы финитизации: целочисленность chi ЕСТЬ топологическая защита/квантование (нельзя изменить непрерывно; сфера 2 != тор 0). Геометрия<->топология<->спектр сходятся на одном целом. Кандидат 9-й нити (защищённое целое / топологическое квантование - Черн/winding/instanton referenced). _(protected-integer, topological-invariant, quantization, element, synthesis)_

**Uniqueness - score 4 (synthesis+observation).** Число Эйлера = ОДНО защищённое целое, вычисленное четырьмя путями (кривизна Gauss-Bonnet / комбинаторика / гомология Betti / индекс Дирака), совпадающими (сфера 2, тор 0); Element-сторона тезиса 'топологический инвариант = защищённое целое'. Кандидат 9-й нити, сшивающий геометрию кривизны с гомологией/индексом.
> _Caveat:_ Gauss-Bonnet, Эйлер-Пуанкаре, теорема индекса классичны, каждый путь уже в репо; ново - литеральное совпадение четырёх путей на одном целом. Честно: index определён=chi (не выведен из реальных нуль-мод Дирака); pi role-limit; Черн/winding referenced, не формализованы. Не новая теорема.

---

## #1849 - `src/foundation/FixedPointTaxonomy.v` - score 4 (synthesis+observation)

**Fixed-point taxonomy: the Lipschitz ratio classifies convergence (r<1) vs symmetry (r=1, RH reflection) vs undecidability (negb diagonal) -- ties veins C/E + zeta (candidate 10th thread)**

- **Topic.** One classifier sorts 'fixed point' into three structurally opposite phenomena: contraction half_map (r=1/2, attracting fixed point 0, the convergence engine), reflection 1-x (r=1, isometry, fixed point 1/2 = critical line, period-2 oscillation, RH's reflection, not a contraction), and negb (no fixed point, the Lawvere/Cantor diagonal seed). A point you reach, a point you orbit, a point that cannot exist.
- **Role.** Cross-vein meta-taxonomy (vein C convergence engine <-> zeta reflection <-> vein E Lawvere diagonal). Self-contained (Stdlib only); cites FixedPoint/ContractionZeros/LawvereFixedPoint.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, Qabs, Lqa
- **E/R/R.** _Elements:_ три отображения - half_map x=x/2 (сжатие r=1/2), reflect x=1-x (изометрия r=1), negb (диагональ); липшицевы отношения r; неподвижные точки (0, 1/2, нет). _Roles:_ r<1 = сжатие -> притягивающая неподвижная точка (движок сходимости Пикар/GD/RG/reasoning, вена C); r=1 = изометрия -> точка не притягивает / осцилляция (отражение RH, zeta); negb-флип = диагональ -> НЕТ неподвижной точки (Ловер, парадокс/неразрешимость, вена E). _Rules:_ half_lipschitz (r=1/2); reflect_isometry (r=1) + reflect_not_contraction + reflect_period2; negb_no_fixpoint. _P4:_ липшицево отношение r КЛАССИФИЦИРУЕТ три типа неподвижной точки - сходимость (r<1, точка, которую достигаешь), симметрия/осцилляция (r=1, точка, вокруг которой кружишь), неразрешимость (negb-диагональ, точка, которой не может быть). Сшивает вену C, zeta и вену E.
- **Classical counterpart.** Banach's contraction (r<1 -> unique fixed point), isometries (r=1), and Lawvere/Cantor's diagonal (no fixed point) are classical; each is already a separate thread in the repo. NEW only as the unification under one classifier (the Lipschitz ratio / negb anti-flip) tying veins C/E + zeta.
- **Tags.** foundation, fixed-point, banach, isometry, lawvere, lipschitz, taxonomy, vein-C, vein-E, zeta, cross-vein, synthesis+observation, H71

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `half_lipschitz/half_fixed_zero` | Lemma | ★ (1) сжатие r=1/2 -> притягивающая неподвижная точка 0 (движок сходимости) |
| `reflect_isometry/reflect_fixed_half/reflect_period2` | Lemma | ★ (2) изометрия r=1 -> неподвижная точка 1/2, период-2 осцилляция (RH-отражение) |
| `reflect_not_contraction` | Lemma | изометрия НЕ сжатие (анти-Банах, RH) |
| `negb_no_fixpoint` | Lemma | ★ (3) диагональ -> НЕТ неподвижной точки (Ловер/Кантор) |
| `fixed_point_taxonomy` | Theorem | капстоун: r классифицирует три типа |

**Key lemmas (deep):**

- **`fixed_point_taxonomy`** - Одно слово неподвижная точка покрывает ТРИ структурно противоположных явления, различаемых липшицевым отношением r (и negb-анти-флипом): r<1 сжатие -> притягивающая точка, сходимость (движок Пикар/GD/RG/reasoning, вена C); r=1 изометрия -> точка не притягивает, осцилляция (отражение RH sigma->1-sigma, zeta); negb-флип -> НЕТ точки (Ловер/Кантор, парадокс/неразрешимость, вена E). Точка, которую достигаешь / вокруг которой кружишь / которой не может быть - три грани одной таксономии, сшивающие три нити репо. _(fixed-point, banach, isometry, lawvere, lipschitz, vein-C, vein-E, zeta, synthesis)_

**Uniqueness - score 4 (synthesis+observation).** Липшицево отношение r КЛАССИФИЦИРУЕТ три структурно противоположных типа неподвижной точки: сходимость (r<1, движок Пикар/GD/RG/reasoning, вена C), симметрия/осцилляция (r=1, RH-отражение, zeta), неразрешимость (negb-диагональ, Ловер, вена E). Кандидат 10-й нити - кросс-веновая мета-таксономия, сшивающая C/E + zeta.
> _Caveat:_ Банах (r<1), изометрии (r=1), Ловер/Кантор (нет точки) классичны и уже отдельные нити репо; ново - унификация под одним классификатором r + связь трёх нитей. Мета-наблюдение, более кросс-веновая таксономия, чем независимая вена. Не новая теорема.

---

## #1850 - `src/foundation/LambdaLevelInversionError.v` - score 3 (new-framing)

**Locating the error behind the refuted Lambda~H^2: a level-inversion (Role-erasure)**

- **Topic.** Self-audit: the falsified rho_Lambda ~ H^2 reading slaves an Element to the aggregate Friedmann Rule, contradicting the framework's own proven vacuum Role w=-1. Restoring w=-1 gives rho_Lambda=const and an EVOLVING Omega_Lambda matching data.
- **Role.** Closes the audit chain of LambdaSmallnessExponent/StageBridge/RunningVacuumBound; cites VacuumIsAntigravity.v (w=-1) and OpenFrontierLedger.v (free magnitude). Self-contained (QArith only).
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, Lqa
- **E/R/R.** _Elements:_ плотности rho_Lambda, rho_matter; показатели масштабирования rho(a). _Roles:_ w каждой компоненты = её Род; w=-1 = Роль вакуума, доказанная рамкой (p=-rho). _Rules:_ rho ~ a^(-3(1+w)) действует ЧЕРЕЗ Роль w; rho_Lambda~H^2 форсирует не-вакуумную экспоненту => нарушает Роль вакуума. _P4:_ шаг rho_Lambda:=c*H^2 = инверсия уровней (Element считан с агрегатного Правила, Роль w стёрта). Исправление, не новый результат.
- **Classical counterpart.** FRW continuity rho ~ a^(-3(1+w)) + vacuum w=-1 => rho_Lambda=const are textbook LCDM cosmology; NEW only as an internal-consistency audit ('the refuted dynamical reading erases the vacuum's own w=-1 Role').
- **Tags.** foundation, cosmology, lambda, audit, level-inversion, self-consistency, new-framing
- **Notes.** Qed drift: header says 9, actual count is 10 (lines 71,75,78,82,100,113,117,123,138,164).

**Lemmas (9):**

| name | kind | role |
|---|---|---|
| `eos_exponent/vacuum_w` | Definition | показатель a^(-3(1+w)); Роль вакуума w=-1 |
| `vacuum_scaling_const` | Theorem | w=-1 => экспонента 0 (rho_Lambda~const) |
| `matter_scaling/radiation_scaling` | Theorem | w=0 -> -3, w=1/3 -> -4 (санити) |
| `eos_exponent_zero_iff` | Theorem | экспонента=0 IFF w=-1 |
| `dynamical_forces_nonvacuum_exponent` | Theorem | при w_dom/=-1 H^2-чтение даёт не-вакуумное масштабирование (инверсия) |
| `Omega_L_correct/Omega_correct_now/Omega_correct_early_val` | Definition/Theorem | исправленная доля; 0.7 сейчас, 7/3007 рано |
| `Omega_correct_evolves` | Theorem | исправленная Omega_Lambda эволюционирует (совпадает с данными) |
| `Reading/respects_vacuum_role/readings_verdict` | Definition/Theorem | DynamicalHsquared нарушает Роль, VacuumConst уважает |
| `lambda_level_inversion_diagnosis` | Theorem | капстоун: диагноз+исправление |

**Key lemmas (deep):**

- **`dynamical_forces_nonvacuum_exponent`** - Точная форма инверсии уровней: в любую не-вакуумную эпоху (w_dom/=-1) чтение rho_Lambda~H^2 присваивает вакууму показатель доминирующей компоненты, противореча доказанной Роли w=-1. Логически это modus tollens над собственной теоремой VacuumIsAntigravity; математически — однострочное следствие eos_exponent_zero_iff. Ценность аудита, не теоремы. _(audit, level-inversion, self-consistency)_
- **`Omega_correct_evolves`** - Восстановив w=-1: rho_Lambda=const, rho_m~a^-3 => Omega_Lambda(1/10)=7/3007 < 0.7=Omega_Lambda(1). Это в точности поведение LCDM; ново лишь как разрешение опровержения через уважение Роли. Чистая рациональная проверка над Q. _(LCDM, rational-check, fix)_

**Uniqueness - score 3 (new-framing).** Опровергнутое предсказание Lambda~H^2 диагностировано как ВНУТРЕННЯЯ несогласованность (инверсия уровней: Element подчинён агрегатному Правилу, Роль вакуума w=-1 стёрта), а не вердикт природы; исправление возвращает LCDM-согласие.
> _Caveat:_ Вся физика (FRW-непрерывность, w=-1 => rho_Lambda=const, эволюция Omega_Lambda) — стандартная космология. Ново только E/R/R-обрамление аудита; никакого нового физического или математического результата. Малость Lambda честно остаётся свободной магнитудой.

---

## #1851 - `src/foundation/LambdaRunningVacuumBound.v` - score 3 (new-framing)

**Confronting the stage-count Lambda~H^2 reading with data: dynamical reading REFUTED**

- **Topic.** Two readings of Lambda/M_P^4 = c/K^2: the SNAPSHOT (present-value, non-distinguishing, survives) and the DYNAMICAL (Lambda ~ H^2 at all epochs). The dynamical one makes Omega_Lambda epoch-independent (H^2 cancels) but observed Omega_Lambda evolves => refuted; framework nu~O(1) also exceeds the RVM bound ~10^-3.
- **Role.** Empirical-discipline ledger (a la NatureBoundaryLedger.v); refuted by data, error then located in LambdaLevelInversionError.v. Self-contained (QArith only).
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, Lqa
- **E/R/R.** _Elements:_ доля вакуума Omega_Lambda, коэффициент nu, наблюдательные якоря (10^-9 рекомб., 0.7 сейчас, граница 10^-3). _Roles:_ nu = доля вакуума (константа при динамич. законе); Omega_obs = наблюдаемая эволюция; граница = опровергающий потолок; прочтения {Snapshot=согласовано, Dynamical=опровергнуто}. _Rules:_ Lambda~H^2 => Omega=const (H^2 сокращается); наблюдаемое Omega эволюционирует => клэш; nu_рамки=1 >> 10^-3. _P4:_ та же дисциплина, что Fermi-LAT vs решётка: чистое предсказание фальсифицировано, выживает неотличимый snapshot. Уровень: честная конфронтация.
- **Classical counterpart.** Running-vacuum models (RVM, Lambda(H)=c0+nu*H^2) and the \|nu\|<~10^-3 CMB+BAO+SNe bound are standard cosmology; the Omega_Lambda-evolution (~10^-9 at recombination, ~0.7 today) is textbook. NEW only as an honest falsification ledger.
- **Tags.** foundation, cosmology, lambda, running-vacuum, falsification, audit, new-framing
- **Notes.** Qed drift: header says 9, actual count is 8 (lines 72,93,104,116,129,140,156,185).

**Lemmas (9):**

| name | kind | role |
|---|---|---|
| `nu_framework/nu_obs_max/framework_nu_exceeds_bound` | Definition/Theorem | nu=1 рамки vs граница 1/1000; превышено |
| `rho_crit/rho_lambda_dyn/Omega_dyn` | Definition | критич. плотность, динамич. rho_Lambda=nu*k*H^2, доля |
| `denom_nz` | Lemma | знаменатель k*H^2 /= 0 (вспом.) |
| `omega_dyn_eq_nu` | Theorem | H^2 сокращается => Omega=nu независимо от эпохи |
| `omega_dyn_constant` | Theorem | Omega_Lambda эпохо-независима |
| `Omega_obs_recomb/Omega_obs_now/observed_omega_evolves` | Definition/Theorem | наблюдаемая Omega эволюционирует (10^-9 /= 0.7) |
| `refuted_at_recombination` | Theorem | матч к 0.7 сейчас => 0.7 при рекомбинации, где было 10^-9 |
| `Reading/Verdict/verdict/confrontation_verdict` | Definition/Theorem | Snapshot=Consistent, Dynamical=Refuted |
| `lambda_running_vacuum_confrontation` | Theorem | капстоун конфронтации |

**Key lemmas (deep):**

- **`omega_dyn_eq_nu`** - Ядро опровержения: при Lambda=nu*rho_crit и rho_crit~H^2 множитель H^2 сокращается в числителе и знаменателе => Omega_Lambda=nu, константа на всех эпохах. Доказано ring+Qmult_inv_r над Q. Это стандартный аргумент RVM; ценность — машинная честность опровержения собственного чистого предсказания. _(RVM, cancellation, refutation)_
- **`refuted_at_recombination`** - Сшивка к сегодняшним 0.7 заставляет динамич. закон давать 0.7 при рекомбинации, где наблюдалось ~10^-9 (vm_compute разрешает дискриминацию). Чистое опровержение; никакой новой физики, только дисциплина: snapshot выживает как неотличимый от LCDM. _(recombination, falsification, rational-check)_

**Uniqueness - score 3 (new-framing).** Честный ledger опровержения: чистое (различающее) динамическое прочтение Lambda~H^2 ФАЛЬСИФИЦИРОВАНО эволюцией Omega_Lambda и RVM-границей; выживает лишь неотличимый snapshot. Дисциплина а-ля Fermi-LAT.
> _Caveat:_ RVM, граница |nu|<~10^-3, эволюция Omega_Lambda и сокращение H^2 — всё стандартная космология. Ново только как самокритичный аудит рамки; результат НЕГАТИВНЫЙ (предсказание refuted), не новая теорема.

---

## #1852 - `src/foundation/LambdaSmallnessExponent.v` - score 2 (methods)

**Lambda-smallness as a forced p=2 exponent over a free stage-count (122=2*61)**

- **Topic.** Reframes the cosmological-constant smallness: 10^-122 = (10^-61)^2 via Friedmann doubling, so the residual free input is an integer stage-count (61), not a tuned real magnitude. Reclassifies the wall BareHierarchy -> DerivedExponent.
- **Role.** Posits the bridge K=M_P/H0 (closed in LambdaStageBridge.v); claim self-corrected as a snapshot in the header (see LambdaLevelInversionError.v). Self-contained (Arith/Z/QArith).
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith, Lia, ZArith, QArith, Lqa
- **E/R/R.** _Elements:_ целочисленные порядки (nat) — hubble_order=61, lambda_order=122, gravity_order=19; счётчик стадий K. _Roles:_ K_cosmo = возраст/число стадий; H0=1/K; Lambda = role-limit, убывающий с уточнением (не константа). _Rules:_ Фридман H^2~rho/M_P^2 ФОРСИРУЕТ rho_L/M_P^4=c/K^2 — экспонента УДВАИВАЕТСЯ (p=2); правило фиксирует функцию (1/K^2), не значение. _P4:_ расходимость уже снята (vac_bound=1/2); ново на рунг глубже: свободна не магнитуда, а один целый счёт + форсированная экспонента. Несущий посит ровно один: мост K=M_P/H0.
- **Classical counterpart.** Friedmann rho_Lambda/M_P^4 ~ (H0/M_P)^2 and the coincidence Lambda~H0^2 are standard; 122=2*61 and 10^61 squared = 10^122 are arithmetic. NEW only as a stage-count re-framing (smallness = forced inverse-square exponent over a free integer count).
- **Tags.** foundation, cosmology, lambda, stage-count, reclassification, self-corrected, methods
- **Notes.** Qed count 10 matches header. Header carries a self-CORRECTION block (lines 50-55) downgrading the 'derive the smallness' claim to a snapshot re-expression (per LambdaLevelInversionError.v).

**Lemmas (10):**

| name | kind | role |
|---|---|---|
| `hubble_order/lambda_order/gravity_order` | Definition | порядки 61, 122, 19 |
| `lambda_is_hubble_squared` | Theorem | FLAGSHIP: 122 = 2*61 (Friedmann doubling) |
| `gravity_count_no_integer_power` | Theorem | the crack: нет целого p с p*19=122 (ошибка масштаба 'p~6') |
| `hubble_count_clean_power` | Theorem | над космич. счётом p=2 — чистое целое |
| `lambda_order_of/exponent_forced_count_free` | Definition/Theorem | форсирована экспонента, счёт свободен (61->122, 62->124) |
| `K_cosmo/lambda_denom/K_cosmo_squared` | Definition/Theorem | bignum: (10^61)^2 = 10^122 (vm_compute) |
| `c_oom/lambda_ratio/lambda_ratio_10/lambda_ratio_100` | Definition/Lemma | закон Lambda(K)=c/K^2, рациональные значения |
| `lambda_decays` | Theorem | Lambda убывает со счётом (running-vacuum) |
| `Wall/WallType/old_wall_type/new_wall_type/reclassified` | Definition/Theorem | реклассификация BareHierarchy -> DerivedExponent |
| `lambda_smallness_exponent` | Theorem | капстоун |

**Key lemmas (deep):**

- **`lambda_is_hubble_squared`** - Флагман: lambda_order = 2*hubble_order, т.е. 122=2*61, доказано reflexivity. Это переразметка известного Lambda~(H0/M_P)^2: показатель удваивается из Фридмана. Реальное наблюдение — что 122 кратно 61 (космич. счёт), но НЕ 19 (гравит. счёт), что объясняет спурьёзное 'p~6' в LambdaPrediction.v как ошибку масштаба. Сама арифметика тривиальна. _(friedmann, exponent, stage-count)_
- **`gravity_count_no_integer_power`** - the crack: forall p, p*19 /= 122 (lia). Диагностирует прежнюю ошибку репо — подстановку гравит. счёта 10^19 вместо космич. 10^61. Полезная внутренняя коррекция, но логически элементарна (19 не делит 122). _(the-crack, diagnosis, lia)_

**Uniqueness - score 2 (methods).** Малость Lambda переразмечена как форсированная обратно-квадратичная экспонента (p=2, Фридман) над СВОБОДНЫМ целым счётом стадий, а не подгонка вещественной магнитуды; стена BareHierarchy -> DerivedExponent.
> _Caveat:_ Сам автор в шапке отзывает заявку 'вывести малость': p=2 — это снимок present-epoch Lambda~H0^2 (Фридман), переписанный через мост, НЕ форвард-деривация; динамически опровергнуто (RunningVacuumBound) и нарушает Роль w=-1 (LevelInversionError). Малость честно остаётся свободной магнитудой; 122=2*61 и 10^61^2=10^122 — арифметика.

---

## #1853 - `src/foundation/LambdaStageBridge.v` - score 2 (methods)

**K_cosmo = M_P/H0 as P4's clock reading (stage count), not a posited scale relation**

- **Topic.** Closes the one posit of LambdaSmallnessExponent.v: K_cosmo = age/Planck-time decomposes as (P4: time=stage count) o (tau=1/M_P) o (age=a/H0). The bridge carries no free real magnitude; only the integer count (the age) stays free; then Lambda/M_P^4 = c/K^2.
- **Role.** Supplies bridge_coasting as a theorem for LambdaSmallnessExponent.v; cites ProcessPlanckLength.v. Self-contained (QArith only).
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, Lqa
- **E/R/R.** _Elements:_ счёт стадий K_cosmo, минимальная длительность tau=1/M_P, возраст T=a/H0, префактор a. _Roles:_ K_cosmo = показание фундаментальных часов (число актов преемства); H0=1/возраст; Lambda = role-limit ~ 1/K^2. _Rules:_ P4 делает время СЧЁТОМ: T=K*tau; с tau=1/M_P [репо] и age~1/H0 [FRW] => K=a*M_P/H0; правило фиксирует форму, не значение счёта. _P4:_ мост — не соотношение трёх масштабов, а P4-определение времени как счёта стадий + два стандартных отождествления; свобода одна — целый счёт (возраст). 10^61 НЕ выведено.
- **Classical counterpart.** t_Planck = 1/M_P, cosmic age ~ 1/H0, and Lambda/M_P^4 = c(H0/M_P)^2 are standard natural-unit cosmology. NEW only as the P4 reading 'elapsed time = count of minimal stages', turning the posited K=M_P/H0 into a clock-reading identity.
- **Tags.** foundation, cosmology, lambda, stage-count, P4-clock, relocation, methods
- **Notes.** Qed drift: header says 9, actual count is 8 (lines 74,89,100,121,135,139,142,165).

**Lemmas (8):**

| name | kind | role |
|---|---|---|
| `stage_count/minimal_duration/age_from_hubble` | Definition | K=T/tau, tau=1/M_P, T=a/H0 |
| `time_is_staged` | Theorem | P4: T=K*tau (счёт стадий = показание часов) |
| `bridge_general` | Theorem | K_cosmo = a*(M_P/H0) (общий мост, field) |
| `bridge_coasting` | Theorem | a=1: K_cosmo=M_P/H0 — посит как ТЕОРЕМА |
| `lambda_friedmann/lambda_from_stage` | Definition | две формы Lambda/M_P^4: Фридман и через счёт |
| `lambda_is_inverse_square_of_count` | Theorem | формы совпадают: (H0/M_P)^2 = 1/K^2 |
| `count_value_free/stage_count_age1/stage_count_age2` | Theorem/Lemma | форма форсирована, значение счёта свободно (K=1 vs K=2) |
| `lambda_bridge_from_P4` | Theorem | капстоун: P4-часы + мост + 1/K^2 |

**Key lemmas (deep):**

- **`bridge_coasting`** - Поднимает посит K_cosmo=M_P/H0 LambdaSmallnessExponent.v до теоремы: stage_count(age/1)(1/M_P)=M_P/H0 при a=1, доказано field. Сама идентичность — алгебра деления над Q; содержательная часть в ИНТЕРПРЕТАЦИИ (P4: время=счёт стадий) через time_is_staged, не в вычислении. _(bridge, P4-clock, field)_
- **`lambda_is_inverse_square_of_count`** - Под мостом K=M_P/H0 фридмановское (H0/M_P)^2 буквально есть 1/K^2, поэтому Lambda/M_P^4=c/K^2. field над Q. Это переписывание стандартного Фридмана; ценность — релокация проблемы CC к космическому счёту стадий, не новая динамика (и снимок, см. LevelInversionError). _(friedmann, relocation, field)_

**Uniqueness - score 2 (methods).** Мост K=M_P/H0 — не свободный посит, а P4-показание часов (возраст в планковских стадиях); в нём нет свободной вещественной магнитуды, свобода одна — целый счёт; проблема CC релоцирована к 'почему вселенная актуализировала ~10^61 стадий'.
> _Caveat:_ t_Planck=1/M_P, age~1/H0, Lambda~(H0/M_P)^2 — стандартная космология в натуральных единицах; алгебра деления над Q тривиальна. Ново только P4-интерпретация 'время=счёт'; 10^61 НЕ выведено; динамически чтение опровергнуто (см. RunningVacuumBound/LevelInversionError).

---

## #1854 - `src/foundation/ObserverSystemTime.v` - score 3 (new-framing)

**Two-time duality: proper time (P4 arrow, irreversible) vs system time (relabelable, navigable)**

- **Topic.** Spacetime-as-process carries two time-projections: proper time = actualized stage-count (monotone, no inverse) and system time = relabelable Role on the causal partial order. Every relabeling preserves the arrow; acyclicity blocks the grandfather paradox by the same irreflexivity (P1) that blocks Russell.
- **Role.** CAPSTONE synthesis drawing on ArrowGroundingDescent.v, DiffeoIsRelabeling.v, CausalStructure(Synthesis).v. Self-contained (Arith/Lia).
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith, Lia
- **E/R/R.** _Elements:_ события (стадия, сайт); счёт собственного времени fst; spacelike-свидетели. _Roles:_ собственное время = Роль наблюдателя (необратимая стрела P4); системное время = переразмечаемая Роль кадра (частичный порядок); spacelike = навигируемая свобода. _Rules:_ причинный частичный порядок (световой конус); переразметки его сохраняют; у преемства S нет инверсии; ацикличность => нет само-предка. _P4:_ наблюдатель НЕ может двигаться в собственном времени (монотонно), но МОЖЕТ в системе; стрела инвариантна под переразметкой, порядок ацикличен — парадокс деда блокирован той же иррефлексивностью P1, что и Рассел.
- **Classical counterpart.** Proper time vs coordinate time, the causal (light-cone) partial order, acyclicity blocking closed timelike curves, and frame relabeling as an order-isomorphism are standard relativity/causal-set theory. NEW only as an E/R/R synthesis tying the arrow to P4 + irreflexivity (P1).
- **Tags.** foundation, spacetime, time, causal-order, proper-time, paradox, synthesis, new-framing
- **Notes.** Qed count 11 matches header.

**Lemmas (10):**

| name | kind | role |
|---|---|---|
| `Event/proper_time/natdist/causal_le/causal_lt/spacelike/relabel` | Definition | события, собств. время, причинный порядок, переразметка |
| `natdist_shift/causal_le_refl` | Lemma | сдвиг расстояния инвариантен; порядок рефлексивен |
| `proper_irreversible` | Theorem | собств. время не убывает вдоль стрелы |
| `cannot_move_back` | Theorem | нет причинного шага в меньшую стадию (вечное сейчас P4) |
| `exists_spacelike` | Theorem | spacelike-пары существуют (частичный, не полный порядок) |
| `system_move_fixes_proper_time/system_move_changes_site` | Theorem | пространств. переразметка меняет сайт, фиксируя собств. время |
| `arrow_invariant_under_relabel` | Theorem | стрела инвариантна под любой переразметкой кадра |
| `relabel_preserves_causal` | Theorem | переразметка = изоморфизм причинного порядка |
| `no_causal_loop` | Theorem | ацикличность: нет само-предка (парадокс деда блокирован) |
| `observer_system_time` | Theorem | капстоун дуальности двух времён |

**Key lemmas (deep):**

- **`arrow_invariant_under_relabel`** - Содержательное ядро 'непарадоксальности': proper_time(relabel c d e) < proper_time(relabel c d f) при proper_time e < proper_time f, т.е. сдвиг кадра сохраняет порядок собственного времени (lia, fst e+c монотонно). Формализует 'двигаться в системном времени, не нарушая стрелы'. Стандартная инвариантность собственного времени при координатной замене, переоформленная в E/R/R. _(arrow, invariance, proper-time)_
- **`no_causal_loop`** - forall e, ~causal_lt e e — ацикличность из иррефлексивности (e<>e ложно). Объединяет блокировку замкнутых времениподобных кривых (дед) с блокировкой Рассела/Кантора одной P1-иррефлексивностью. Сам факт элементарен (тривиальное противоречие), ценность — концептуальная унификация парадоксов. _(acyclicity, P1, grandfather-paradox)_

**Uniqueness - score 3 (new-framing).** Пространство-время как ОДИН процесс с двумя временами: собственное (необратимая стрела P4) и системное (переразмечаемая навигируемая Роль); 'движение во времени без нарушения его законов' = движение в системном времени при инвариантной стреле; парадокс деда блокирован той же иррефлексивностью P1, что и Рассел.
> _Caveat:_ Собственное vs координатное время, причинный частичный порядок, ацикличность => нет CTC, переразметка = изоморфизм порядка — всё стандартная релятивистская/каузально-множественная теория. Лемма no_causal_loop тривиальна. Ново только E/R/R-синтез и явная унификация парадоксов через P1; шапка честно отрицает любые претензии на эмпирику путешествий/НЛО.

---

## #1855 - `src/foundation/PolarizableVacuumIndex.v` - score 3 (new-framing)

**Polarizable-vacuum refractive index K(phi)=1+2phi as ToS distinction-density gravity (weak field)**

- **Topic.** Optical re-description of ordinary gravity: vacuum index K=1+2phi (weak-field linearization of exp(2phi)), c_eff=1/K<=1, propagation_time ~ K = local graph degree, deeper clocks dilate, light bends toward mass, deep sources redshift. Bridges PV to ToS graph-density gravity.
- **Role.** Bridge file connecting PV to EnergyDeterminesGraph.v (degree=index) and ObserverSystemTime.v (clock=proper time). Self-contained (QArith only).
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith, Lqa
- **E/R/R.** _Elements:_ значение индекса K(phi), c_eff, глубина phi, локальная степень графа. _Roles:_ K = роль среды (показатель преломления / поляризуемость / степень графа); c_eff = скорость; phi = глубина (источник); K-зависимые часы = собственное время. _Rules:_ K=1+2*phi (слабое поле; exp(2*phi) role-limit); c_eff=1/K; индекс растёт у массы => свет медленнее, гнётся к массе, глубокие часы замедляются. _P4:_ Element-сторона рациональна (слабое поле); полный exp(2*phi) = role-limit (процесс Коши). Мост EnergyDeterminesGraph (степень=индекс) <-> ObserverSystemTime (ход часов=собств. время).
- **Classical counterpart.** Puthoff's polarizable-vacuum (PV) model (Found. Phys. 32:927, after Dicke): K=exp(2*phi), c=c0/K reproduces weak-field redshift/bending/perihelion. NEW only as a bridge from PV's refractive index to ToS graph-degree gravity (EnergyDeterminesGraph.v).
- **Tags.** foundation, gravity, polarizable-vacuum, refractive-index, graph-density, bridge, new-framing
- **Notes.** Qed count 11 matches header.

**Lemmas (11):**

| name | kind | role |
|---|---|---|
| `vac_index/c_eff/propagation_time/redshift_ratio` | Definition | индекс 1+2phi, скорость 1/K, время~K, красное смещение |
| `index_vacuum` | Theorem | phi=0 => K=1 (плоское пространство) |
| `index_ge_one` | Theorem | K>=1 везде (свет не ускоряется) |
| `index_increasing` | Theorem | глубже => выше индекс |
| `index_pos` | Theorem | K>0 при phi>=0 |
| `index_minus_newtonian` | Theorem | K-1 = 2*phi (слабополевая метрич. поправка) |
| `propagation_slows_deeper` | Theorem | время распространения растёт с индексом (часы замедляются) |
| `c_eff_vacuum/c_eff_not_superluminal` | Theorem | c_eff=1 в вакууме; c_eff<=1 везде |
| `bending_toward_mass` | Theorem | свет гнётся к массе (Ферма: к более высокому индексу) |
| `redshift_when_deeper` | Theorem | свет с глубины краснеет (отношение индексов > 1) |
| `polarizable_vacuum_index` | Theorem | капстоун оптической картины |

**Key lemmas (deep):**

- **`index_minus_newtonian`** - vac_index phi - 1 == 2*phi (ring): отклонение индекса от плоского ровно вдвое ньютоновского потенциала — лидирующая метрич. поправка PV. Связывает оптический язык (показатель преломления) с гравит. потенциалом. Это слабополевая линеаризация exp(2phi)~1+2phi; результат стандартен для PV-модели, ценность — мост к ToS-плотности различений. _(weak-field, newtonian, ring)_
- **`c_eff_not_superluminal`** - forall phi>=0, c_eff phi <= 1 (Qle_shift_div_r + index_ge_one): эффективная скорость 1/K никогда не сверхсветовая, =1 лишь в вакууме. Гарантирует физич. состоятельность оптической картины. Прямое следствие K>=1; стандартно для PV. _(c_eff, subluminal, Qle)_

**Uniqueness - score 3 (new-framing).** Гравитация = поле переменной ПЛОТНОСТИ РАЗЛИЧЕНИЙ (показателя преломления): мост Puthoff-PV <-> ToS-граф-гравитация (степень графа = индекс K = плотность различений), с c_eff=1/K<=1, замедлением глубоких часов и красным смещением как теоремами над Q.
> _Caveat:_ Вся оптика (K=exp(2phi), c=c0/K, слабополевые redshift/bending) — это PV-модель Путхоффа (после Дикке), скалярный эвристический приём, эквивалентный ОТО ТОЛЬКО в слабом поле; не полная тензорная ОТО. Леммы — элементарная арифметика над Q. Ново лишь обрамление 'индекс=плотность различений'; шапка честно отрицает 'метрическую инженерию'/НЛО.

---

## #1856 - `src/foundation/RoleLimitLadder.v` - score 3 (new-framing)

**Role-limit ladder: omniscience principles LLPO<WLPO<LPO<LPO_omega graded by quantifier depth**

- **Topic.** The role-limit side of the finitization boundary is a graded ladder of omniscience principles (LLPO<-WLPO<-LPO<-LPO_omega, LPO->MP), proved 0-axiom as Prop-implications; the grading is CONSTRUCTIVE (LEM collapses every rung). Adds the cascade rung LPO_omega (Pi^0_2) and maps ToS boundary-objects to rungs.
- **Role.** Places DynamicBoundaryLPO.v (N1++, MCT<->LPO) on a ladder; cites constructive RM (Bishop/Ishihara) and disclaims overlap with P4_Eliminates_*. Self-contained (Arith/Lia).
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith, Lia
- **E/R/R.** _Elements:_ булева последовательность g; пара (a,b); поток-потоков a:nat->nat->bool; предикат fires; конечный поиск. _Roles:_ каждая ступень = сколько завершённой бесконечности требует вопрос; LEM = схлопывающий оракул; квантовая глубина вопроса = номер ступени. _Rules:_ LPO_omega->LPO->WLPO->LLPO, LPO->MP (конструктивный подъём); LEM->LPO, LEM->LPO_omega (классич. схлопывание); строгость = нужна модель (цитата, стоп). _P4:_ глубина видна ТОЛЬКО конструктивно/через P4 — классически лестница плоская. 'P4 тоньше классики' = известный мета-факт, машинно проверен через LEM->..., не открыт.
- **Classical counterpart.** Constructive reverse mathematics: LPO -> WLPO -> LLPO, LPO -> MP (Bishop, Ishihara) and 'classically all collapse' are standard. NEW only as: a cascade rung LPO_omega with LPO_omega->LPO, and a boundary-object -> rung MAP for the ToS finitization program.
- **Tags.** foundation, constructive-reverse-math, LPO, omniscience, finitization-boundary, synthesis, new-framing
- **Notes.** Qed count 9 matches header.

**Lemmas (10):**

| name | kind | role |
|---|---|---|
| `LEM/LPO/WLPO/LLPO/MP` | Definition | принципы всеведения как Props (ни один не ассертится) |
| `fires/LPO_omega` | Definition | событие 'k-й поток срабатывает'; каскадная ступень Pi^0_2 |
| `lpo_mp` | Lemma | LPO -> MP (Марков, боковая ступень) |
| `lpo_wlpo` | Lemma | LPO -> WLPO (решение без свидетеля слабее) |
| `wlpo_llpo` | Lemma | WLPO -> LLPO (tie-break) |
| `lpo_llpo` | Lemma | LPO -> LLPO (следствие) |
| `finite_search` | Lemma | ограниченный префиксный поиск разрешим |
| `lpo_omega_lpo` | Lemma | каскад строго ВЫШЕ: LPO_omega -> LPO |
| `lem_lpo/lem_lpo_omega` | Lemma | LEM->LPO и LEM->LPO_omega (классич. коллапс, лестница плоская) |
| `role_limit_ladder` | Theorem | капстоун: подъём + классич. коллапс |

**Key lemmas (deep):**

- **`lpo_omega_lpo`** - Единственная genuine-mine ступень: каскад LPO_omega (Pi^0_2, 'бесконечно/конечно много потоков срабатывают') влечёт LPO кодированием g как потока, константного по внутреннему индексу, + finite_search для конечного хвоста. Конструктивное доказательство (destruct по finite_search). Демонстрирует, что граница-границ требует строго больше всеведения, чем одиночная. _(cascade, Pi02, constructive)_
- **`lem_lpo_omega`** - Честный P4-пуант: LEM -> LPO_omega (двойной destruct классики), и LEM -> LPO — значит КЛАССИЧЕСКИ каждая ступень есть теорема, лестница плоская. Глубина видна лишь конструктивно. Сам автор помечает это как известный мета-факт (классически плоско, конструктивно градуировано), машинно проверяемый, не открытие. _(LEM-collapse, constructive-grading, honest)_

**Uniqueness - score 3 (new-framing).** Role-limit-сторона границы финитизации не плоская, а ГРАДУИРОВАННАЯ лестница всеведения (LLPO<WLPO<LPO<LPO_omega) по квантовой глубине вопроса; градация — КОНСТРУКТИВНЫЙ феномен (LEM схлопывает все ступени); + карта объект-границы -> ступень.
> _Caveat:_ Сам файл максимально честен: импликации LPO->WLPO->LLPO, LPO->MP — стандартная конструктивная обратная математика (Bishop/Ishihara), ПЕРЕпроверены, не новы; СТРОГОСТЬ (необратимость) НЕ доказана — нужна реализуемость/Крипке/топологич. модель (цитата, стоп); 'P4 тоньше классики' = известный мета-факт. Genuine-mine лишь каскад LPO_omega->LPO и карта объект->ступень — placement/синтез.

---

## #1857 - `src/foundation/ZFCAxiomLedger.v` - score 3 (new-framing)

**ZFC axiom ledger: 8 of 9 eliminated (P1/P4/L5 or trivial), exactly Powerset = role-limit**

- **Topic.** A single auditable register of the nine ZFC axioms with a per-axiom verdict {Trivial / ReplacedBy E/R/R-law / RoleLimit}. Exactly one (Powerset) lands on the role-limit side; finite powerset is proved Element (2^n bitvectors), only full 2^N is role-limit (cited Cantor).
- **Role.** Consolidates the scattered ZFC-elimination (P4_Eliminates_{Infinity,AC,ATR,Pi11}, P1_no_self_membership, P4ProhibitsImpredicative, ChoicePriceMap, MuRecursion) into one ledger; cites ProcessDiagonal. Self-contained (Arith/Lia/List).
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith, Lia, List
- **E/R/R.** _Elements:_ 9 конструкторов ZFCAxiom; bitvectors (конечный powerset, 2^n); E/R/R-законы. _Roles:_ аксиома = роль-требование; вердикт = роль (тривиально / заменено законом / role-limit); закон E/R/R = заменитель. _Rules:_ классификация tos_verdict; ровно Powerset = role-limit; конечный powerset = 2^n (Element). _P4:_ ровно 1 из 9 аксиом ZFC (Powerset) = role-limit; 8 тривиальны/заменены законом. Ни одна ZFC-аксиома НЕ ассертится. Синтез/классификация, не теорема.
- **Classical counterpart.** The nine ZFC axioms and 'powerset of a finite set has 2^n elements / 2^N is uncountable (Cantor)' are standard set theory. NEW only as a consolidated machine ledger assigning each ZFC axiom a ToS verdict, with the observation 'exactly Powerset = role-limit'.
- **Tags.** foundation, set-theory, ZFC, powerset, ledger, consolidation, new-framing
- **Notes.** Qed drift: header says 10, actual count is 9 (lines 93,97,101,105,125,138,145,155,182). Declares NO real axioms: 'ZFCAxiom' is an inductive enumeration of axiom NAMES, not Axiom/Parameter declarations (axioms=0 confirmed).

**Lemmas (8):**

| name | kind | role |
|---|---|---|
| `ZFCAxiom/ERRLaw/ToSStatus/tos_verdict` | Definition | 9 аксиом, 9 законов, 3 вердикта, классификатор |
| `verdict_infinity/verdict_choice/verdict_foundation/verdict_separation` | Lemma | анкеры: Infinity->P4, Choice->L5, Foundation->P1, Separation->P4 |
| `bitvectors` | Definition (Fixpoint) | все подмножества [0,n) как битовые векторы |
| `bitvectors_length` | Lemma | конечный powerset = ровно 2^n (Element) |
| `only_powerset_is_role_limit` | Lemma | Powerset — ЕДИНСТВЕННАЯ аксиома на role-limit |
| `eight_axioms_eliminated` | Lemma | восемь не-Powerset устранены |
| `verdict_total` | Lemma | тотальность: каждая аксиома получает ровно один вердикт |
| `zfc_axiom_ledger` | Theorem | капстоун реестра ZFC |

**Key lemmas (deep):**

- **`bitvectors_length`** - Единственная содержательная (не-reflexivity) лемма: length(bitvectors n) = 2^n, индукция с length_app/length_map и 2^(S n)=2*2^n (lia). Показывает, что powerset КОНЕЧНОГО множества полностью перечислим (Element-сторона), и лишь полный 2^N — role-limit. Стандартная комбинаторика; ценность — локализация 'цены' ровно в пределе 2^N. _(powerset, bitvectors, induction)_
- **`only_powerset_is_role_limit`** - forall a, tos_verdict a = RoleLimit <-> a = Powerset (destruct по 9 конструкторам). Машинно фиксирует центральное наблюдение: из 9 аксиом ZFC ровно Powerset попадает на role-limit-сторону, 8 тривиальны или заменены P1/P4/L5. Логически это проверка таблицы classification; содержание — в самом наблюдении/сведении, не в доказательстве. _(exactly-one, classification, decidable)_

**Uniqueness - score 3 (new-framing).** Единый машинный реестр 9 аксиом ZFC с вердиктом: 3 тривиальны, 5 заменены именованным законом E/R/R (Infinity/Separation/Replacement->P4, Foundation->P1, Choice->L5), и РОВНО ОДНА (Powerset) = role-limit — единственная 'цена' финитизации; конечный powerset доказан Element (2^n).
> _Caveat:_ Сам файл помечает себя СИНТЕЗ/КЛАССИФИКАЦИЯ, НЕ новая теорема: вердикты ReplacedBy лишь ЦИТИРУЮТ существующие 0-аксиомные файлы (не передоказывают их), а 'Powerset=role-limit' опирается на несчётность 2^N (Кантор, цитата). 2^n bitvectors — стандартная комбинаторика; вердикты как 'замена' опираются на спорные философские отождествления (P4=Infinity и т.п.). Ценность — консолидация и наблюдение 'ровно Powerset'.

---

## #1860 - `src/foundation/ShellCapacityCounting.v` - score 2 (methods)

**2n² ДОКАЗАНО как счёт (Σ_{l<n} 2(2l+1) = 2n²), вход (n,l,m,s)-структура ИМЕНОВАН**

- **Topic.** Σ нечётных = n² (orientations_sum), ёмкость оболочки = 2n² (shell_capacity_2n2), литеральное пространство состояний (l,m,s) длины 2n² (shell_states_count), |m|≤l (m_values_bounded), инстансы 2/8/18/32, 1s-оболочка литерально.
- **Role.** Закрывает аудит-флаг «2n² = ЗАЯВЛЕНО, не доказано» (ApplicationsAudit определял shell_capacity как 2n²; здесь СЧИТАЕТСЯ). Вход назван: башня l<n — водородная структура (физика), НЕ из различения; ×2 спина = L2-бинарность (единственная ToS-точка). Self-contained (Arith/List/ZArith).
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith Lia List ZArith
- **E/R/R.** _Elements:_ литеральные состояния (l,m,s); числа 2,8,18,32; 1s = [(0,0,↑);(0,0,↓)]. _Roles:_ оболочка n / подоболочка l / ориентация m / спин s; ёмкость = «сколько Elements вмещает роль-оболочка»; ×2 спина — L2-бинарность. _Rules:_ структура квантовых чисел (ВХОД, физика) + вынужденная арифметика Σ_{l<n}2(2l+1)=2n². _P4:_ доказана ЁМКОСТЬ, не длина периода (ауфбау 2,8,8,18,18,32,32 — флаг в ApplicationsAudit); невынужденная точка ИМЕНОВАНА: башня l<n — вход (другой потенциал — другая башня).
- **Classical counterpart.** The 2n^2 shell-capacity count (sum over l<n of 2(2l+1)) is textbook quantum mechanics; NEW only as the machine-checked counting chain (orientations -> subshell -> shell, plus the LITERAL state lists) closing the audit flag '2n^2 asserted, not proven'.
- **Tags.** foundation, 2n2, periodic-table, counting, audit-closure, honesty

**Lemmas (10):**

| name | kind | role |
|---|---|---|
| `sum_below / orientations / subshell_capacity / shell_capacity_counted` | Definition | счётная цепочка: Σ_{i<k}, 2l+1, 2(2l+1), Σ по l<n |
| `orientations_sum` | Lemma | Σ_{l<n}(2l+1) = n² (сумма нечётных) |
| `shell_capacity_2n2` | Theorem | ★ ёмкость оболочки = 2n² — ДОКАЗАНО, не определено |
| `capacities_2_8_18_32` | Lemma | инстансы аудита: 2, 8, 18, 32 |
| `m_values / m_values_count / m_values_bounded` | Lemma | литеральные m: 2l+1 значений, \|m\|≤l |
| `spin / spin_binary` | Definition | спин = L2-бинарный фактор (единственная ToS-точка счёта) |
| `subshell_states / subshell_states_count` | Lemma | литеральная подоболочка = m × спин, длина 2(2l+1) |
| `length_flat_map_seq / sum_below_ext` | Lemma | генерические леммы счёта flat_map/Σ |
| `shell_states_count` | Theorem | ★★ ЛИТЕРАЛЬНЫЙ список состояний оболочки имеет длину 2n² |
| `shell1_is_1s / shell2_count / shell4_count` | Example | 1s литерально; n=2 → 8; n=4 → 32 |

**Key lemmas (deep):**

- **`shell_states_count`** - 2n² перестаёт быть определением: предъявлен литеральный список состояний (l,m,s) с l<n, \|m\|≤l, s∈2 и доказано, что его ДЛИНА равна 2n². Вместе с orientations_sum (Σ нечётных = n²) это полная счётная цепь, которой не хватало аудиту (ApplicationsAudit: «pure counting» утверждалось, но счёта не было; CoulombFull3D имел только Σ(2l+1) в experimental). _(2n2, counting, audit-closure)_
- **`shell_capacity_2n2`** - Индукция: ёмкость(n+1) = ёмкость(n) + 2(2n+1) = 2n²+4n+2 = 2(n+1)². Вход честно именован: башня l<n — водородная вырожденность (физика); ToS касается счёта в одной точке — спин = L2-бинарность. _(2n2, induction, named-input)_

**Uniqueness - score 2 (methods).** Аудит-флаг «2n² заявлено, не доказано» ЗАКРЫТ: ёмкость 2n² доказана как счёт (формула + литеральное пространство состояний), вход (n,l,m,s)-структуры именован, ауфбау-оговорка сохранена.
> _Caveat:_ Счёт 2n² — учебная КМ; ново только машинное закрытие конкретного флага честности; НЕ «2n² из различения» (башня l<n — физический вход).

---

## #1861 - `src/foundation/AnomalyLatticeDial.v` - score 3 (new-framing)

**Дайл аномалий: настоящий исчерпывающий скан бокса [−8..8]⁴ — 1317 → 11 → ровно {SM, u↔d}**

- **Topic.** 4 условия аномалий (форма = AnomalyChargeQuantization), бокс 17⁴ кортежей, счётчики по ступеням (grav: 1317; +cubic: 11; +неабелевы: ровно 2 — литеральный список), экзотика (−1,−1,0,0) убита color-условием, zq=0-семейство (t,−t,0,0) проходит всё — нормировка несущая.
- **Role.** Заменяет over-claims AnomalyExhaustive (#164 «exhaustive» при ~5 точках) и AnomalySystematic (#165 «systematic» при 1-D срезе) НАСТОЯЩИМ исчерпанием объявленного бокса; недоопределённость каждого правила = ЧИСЛО. Дополняет алгебраический вывод ChargeLatticeTheory (Виета) машинным перебором. Self-contained (ZArith/List/Bool).
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: ZArith Lia List Bool
- **E/R/R.** _Elements:_ 83 521 кортеж зарядов (юниты 1/6); 1317 grav-решений; 11 grav+cubic (с экзотиками); финальная пара (−4,2,−3,6) и (2,−4,−3,6). _Roles:_ zq=1 — нормировка с НЕСУЩЕЙ ролью (без неё 1-параметрическое семейство (0,t,−t,0,0) проходит всё — zq0_family_passes); счётчик ступени — «сколько свободы осталось у правила»; неабелевы условия — роль «пиннинг» (11→2). _Rules:_ 4 локальных условия аномалий (импорт КТП-консистентности, форма ровно как в AnomalyChargeQuantization.v); правило-скан = разрешимый перебор объявленного конечного бокса (P4). _P4:_ «уникальность SM-гиперзарядов» впервые — РАЗРЕШИМАЯ исчерпанная теорема в объявленном боксе; невынужденные входы ИМЕНОВАНЫ: содержание поколения (6,3,3,2,1), сами условия, нормировка (несущая — теорема), границы бокса. НЕ «SM из различения».
- **Classical counterpart.** Anomaly-freedom pinning the SM hypercharges (up to u<->d swap, given Y_Q normalization) is known QFT; NEW only as a TRUE machine-exhausted box scan with the per-rule freedom QUANTIFIED (1317 -> 11 -> 2) and the normalization proven load-bearing (zq=0 family).
- **Tags.** foundation, anomaly, exhaustive-scan, dial, honesty, vm_compute, vein-A-adjacent

**Lemmas (10):**

| name | kind | role |
|---|---|---|
| `g_color/g_weak/g_grav/g_cubic` | Definition | условия аномалий, обобщённые по нормировке q |
| `box / tuples / box_size` | Definition | объявленный бокс [−8..8] и решётка 17⁴ кортежей |
| `dial_grav` | Theorem | ступень 1: grav-линейное условие → 1317 решений в боксе |
| `dial_grav_cubic` | Theorem | ступень 2: +кубическое → 11 решений |
| `dial_all_exact` | Theorem | ★★ ступень 3: все 4 условия → ЛИТЕРАЛЬНО [(−4,2,−3,6); (2,−4,−3,6)] — исчерпание бокса |
| `dial_strictly_narrows` | Theorem | дайл строго сужает: 2 < 11 < 1317 |
| `exotic_killed` | Theorem | ★ (−1,−1,0,0) проходит grav+cubic, убита неабелевым color — пиннинг делают неабелевы |
| `zq0_family_passes` | Theorem | ★ нормировка несущая: при zq=0 семейство (t,−t,0,0) проходит ВСЕ условия для любого t |
| `sm_passes_all / swap_passes_all / matches_charge_quantization_pattern` | Lemma | выжившие = SM-паттерн AnomalyChargeQuantization и u↔d-своп |
| `anomaly_lattice_dial` | Theorem | ★ capstone: счётчики + точный список + zq=0-семейство |

**Key lemmas (deep):**

- **`dial_all_exact`** - Первое НАСТОЯЩЕЕ исчерпание: фильтр всех четырёх условий по 83 521 кортежу бокса вычислен литерально и равен двухэлементному списку — SM и u↔d-своп. То, что AnomalyExhaustive лишь заявлял («unique among tested», ~5 точек), здесь — vm_compute-теорема с объявленными границами. _(exhaustive, anomaly, sm, vm_compute)_
- **`zq0_family_passes`** - Честность нормировки: при Y_Q=0 целое 1-параметрическое семейство (0,t,−t,0,0) удовлетворяет всем четырём условиям — значит «единственность» есть единственность ПРИ Y_Q≠0 (нормировано к 1); постулат нормировки несёт реальный вес, это не косметика. _(normalization, load-bearing, honesty)_
- **`exotic_killed`** - Квантование недоопределённости: grav+cubic оставляют 11 решений (включая вектороподобные экзотики), и именно неабелевы условия делают пиннинг 11→2. Дайл превращает «какое правило сколько решает» из прозы в числа. _(dial, non-abelian, underdetermination)_

**Uniqueness - score 3 (new-framing).** Over-claims «exhaustive/systematic» заменены разрешимой исчерпанной теоремой: в объявленном боксе при объявленной нормировке условия аномалий оставляют ровно {SM, u↔d-своп}, а свобода каждого правила квантована (1317→11→2); несущая роль нормировки доказана (zq=0-семейство).
> _Caveat:_ Физика классична (аномалии пиннят SM-гиперзаряды); вход — содержание поколения, сами условия, нормировка, бокс — всё именовано; вне бокса полнота следует из алгебры ChargeLatticeTheory, не из скана.

---

## #1872 - `src/foundation/ArrowSignFromOrigin.v` - score 3 (new-framing)

**Past Hypothesis reduced to (A=exists origin + P4 monotone): reservoir room maximal at the origin, shrinks forward**

- **Topic.** Models the un-actualized 'reservoir room' as total - actualized(K) over a monotone actualization count, and proves the room is maximal at the origin K=0 (minimal actualization = the first distinction) and strictly shrinks forward, so the sub-maximal-reservoir-on-the-past-side posit follows from the ToS foundation rather than being an independent fine-tuning.
- **Role.** Stage of the spacetime/gravity-arrow descent (Arrow* family): digs the residual L2 posit of ArrowSignReservoir.v down to the origin (A=exists)+P4. Self-contained (Stdlib only); a Section over an abstract `total`. Companion to GravityArrowEntropy.v (saturation = heat death) and ArrowGroundingDescent.v (W fluctuation).
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith Lia
- **E/R/R.** _Elements:_ счёт актуализированного actualized K = K (записи=стадия); полное пространство различений total; room = total - actualized = неактуализированный резервуар (сток энтропии). _Roles:_ начало K=0 = минимальная актуализация (одно первое различение, A=существует); room = сток энтропии; направление вперёд = room убывает. _Rules:_ P4 => actualized монотонно растёт => room только сокращается; начало минимально => room максимален в начале; суб-максимальность (0<room 0) форсирована, не постулирована. _P4:_ ДИАГНОСТИКА: «суб-максимальный резервуар + сторона прошлого» СВОДИТСЯ к (A=существует: одно различение = минимум) + (P4: монотонная актуализация). Гипотеза прошлого = ОСНОВАНИЕ ToS, не отдельная тонкая настройка. ЧЕСТНО: форсирует только СТОРОНУ + монотонность room (скелет); ВЕЛИЧИНУ роста энтропии несут мост записи (Ландауэр) + безразличие; «происхождение ToS=космологическое» = мост; вейлева гладкость не закрыта.
- **Classical counterpart.** Penrose's Past Hypothesis / Weyl-curvature low-entropy initial condition (the cosmological origin of the thermodynamic arrow) is the classical referent; NEW is only the E/R/R reframing of the 'sub-maximal reservoir on the past side' posit as REDUCING to (A=exists: one first distinction = minimal actualization) + (P4: monotone actualization), so the room is maximal at the origin and shrinks forward — a reduction of the posit to the ToS foundation, NOT a derivation of the entropy magnitude or of the cosmological identification.
- **Tags.** foundation, arrow-of-time, past-hypothesis, P4, entropy, reduction, new-framing, honest-residual

**Lemmas (9):**

| name | kind | role |
|---|---|---|
| `actualized` | Definition | счёт актуализированного на стадии K := K (P4: только растёт; начало K=0 минимально) |
| `room` | Definition | запас резервуара := total - actualized K (неактуализированные различения = сток энтропии) |
| `actualized_grows` | Theorem | P4: actualized K < actualized (S K) (актуализация только добавляет) |
| `origin_minimal` | Theorem | начало минимально: actualized 0 <= actualized K (одно первое различение) |
| `room_max_at_origin` | Theorem | ★ room K <= room 0 — резервуар МАКСИМАЛЕН в начале |
| `room_shrinks_forward` | Theorem | ★ S K <= total -> room (S K) < room K — room строго убывает вперёд (сторона прошлого = больше room) |
| `submaximal_from_origin` | Theorem | 0 < total -> 0 < room 0 — суб-максимальность в начале ФОРСИРОВАНА, не постулирована |
| `arrow_runs_until_saturation` | Theorem | K < total -> 0 < room K — стрела бежит от начала до насыщения (room->0 = тепловая смерть/коллапс) |
| `past_hypothesis_from_origin` | Theorem | ★ КАПСТОУН: конъюнкция всех шести фактов — постулат L2 сведён к (A=существует начало + P4 монотонность) |

**Key lemmas (deep):**

- **`room_max_at_origin`** - Содержательное ядро редукции: запас резервуара room = total - K максимален именно при K=0, потому что P4 делает actualized минимальным в начале (одно первое различение, A=существует). Это арифметически тривиально (lia над nat), но НАГРУЖЕНО смыслом: «низкоэнтропийное начало» = «минимальная актуализация на происхождении» = следствие основания ToS, а не независимая пенроузовская тонкая настройка. Честно: фиксирует только СТОРОНУ/монотонность, не величину. _(past-hypothesis, P4, origin, reduction)_
- **`past_hypothesis_from_origin`** - Капстоун-конъюнкция: рост актуализации + минимум в начале + максимум room в начале + убывание room вперёд + форсированная суб-максимальность + пробег до насыщения — всё одной leplike-цепочкой lia. Заявляет: Гипотеза Прошлого = «процесс начался с одного различения (A=существует), и P4 делает актуализацию монотонной». Уровень — РЕДУКЦИЯ ПОСТУЛАТА К ОСНОВАНИЮ: не новая теорема, а точное растворение мнимой тонкой настройки в две аксиомы-закона ToS, с честно названными остаточными мостами (величина энтропии, космологическая идентификация, вейлева гладкость). _(capstone, synthesis, reduction, honest-residual)_

**Uniqueness - score 3 (new-framing).** Постулат «суб-максимальный резервуар со стороны прошлого» (= Гипотеза Прошлого) переформулирован как СЛЕДСТВИЕ основания ToS: минимальная актуализация в начале (A=существует) + монотонная актуализация (P4) => room максимален в начале и убывает вперёд.
> _Caveat:_ Арифметика тривиальна (nat/lia, конфигурация room=total-K выбрана под результат). Пенроузова Гипотеза Прошлого / низкая начальная энтропия — классический референт. Файл форсирует ТОЛЬКО сторону + монотонность room; величину роста энтропии, идентификацию ToS-начала с космологическим и вейлеву гладкость он сам честно оставляет как неустранённые мосты. Над-брендинг (как полный вывод знака стрелы времени) был бы оверклеймом — файл этого не делает.

---

## #1873 - `src/foundation/ArrowSignReservoir.v` - score 3 (new-framing)

**Entropy-sign analysis in three honest layers: direction forced (P4), alignment derived (Landauer), absolute sign = one located posit**

- **Topic.** Builds toy nat models of stage-count, a finite dumping reservoir (total_S saturates at room), and a time-reverse absorbing process, then proves: the direction is forced (stage strictly grows), the record and entropy arrows are aligned (move together), entropy rises only while the reservoir is sub-maximal and STALLS at saturation, and both dumping and absorbing advance the stage — so the absolute sign is the residual posit of which side the sub-maximal reservoir is.
- **Role.** Root of the spacetime/gravity entropy-sign descent; its residual L2 posit is then dug to the origin by ArrowSignFromOrigin.v (#1872), its info-entropy input by EntropyCountDefinitional.v (#1876), its heat/Boltzmann input by EnergyAsActualizationRate.v (#1875). Self-contained (Stdlib only).
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith Lia
- **E/R/R.** _Elements:_ счёт стадий stage K = K (записи); запас резервуара room; суммарная энтропия total_S = S0 + min K room; обратный процесс absorb_S. _Roles:_ stage = стрела записей/памяти (P4); резервуар = сток энтропии; суб-максимальный запас = постулат; dump_S = сброс (энтропия вверх) против absorb_S = поглощение (вниз). _Rules:_ P4 => счёт стадий растёт; актуализация=запись=сброс => энтропия несбавляющая, пока есть запас (K<room); насыщенный резервуар (room<=K) => стрела глохнет; сброс-vs-поглощение => знак = сторона резервуара. _P4:_ ДИАГНОСТИКА: L0 НАПРАВЛЕНИЕ форсировано (P4 запрещает деактуализацию); L1 ВЫРАВНИВАНИЕ стрел ВЫВОДИМО (актуализация=запись=сброс, мост Ландауэра — стрелы не могут разойтись); L2 АБСОЛЮТНЫЙ ЗНАК = суб-максимальный резервуар со стороны прошлого = ТОЧНО локализованный постулат (максимальный резервуар => стрелы нет). НЕ выводим абсолютный знак; ВЫВОДИМ выравнивание и сужаем постулат. ЧЕСТНО: мост Ландауэра = отождествление, не чистый P4; энтропия=счёт-записей = Element-прокси.
- **Classical counterpart.** The thermodynamic arrow of time, the alignment of the record/memory/thermodynamic/gravitational arrows, Landauer's principle (logical irreversibility => thermodynamic cost), and the Past Hypothesis are all classical; NEW is only the three-layer E/R/R verdict — direction L0 forced by P4, alignment L1 derived via the Landauer identification, absolute sign L2 pinned to ONE precisely-located posit (sub-maximal reservoir on the past side) — sharper than a flat 'the sign is a posit', but NOT a derivation of the absolute sign.
- **Tags.** foundation, arrow-of-time, entropy, landauer, past-hypothesis, P4, new-framing, honest-residual

**Lemmas (10):**

| name | kind | role |
|---|---|---|
| `stage` | Definition | P4-стрела записей: stage K := K (число необратимо актуализированных различений) |
| `dump_S` | Definition | процесс сброса: dump_S S0 K := S0 + K (каждая актуализация пишет бит в резервуар) |
| `total_S` | Definition | конечный резервуар: S0 + min K room (энтропия растёт до насыщения резервуара) |
| `absorb_S` | Definition | обратный (поглощающий) процесс: S0 - K (резервуар с другой стороны ПОНИЗИЛ бы энтропию) |
| `direction_forced` | Theorem | ★ L0: stage K < stage (S K) — НАПРАВЛЕНИЕ форсировано P4 |
| `arrows_aligned` | Theorem | ★ L1: stage и dump_S растут ВМЕСТЕ — выравнивание стрел выведено (мост Ландауэра) |
| `entropy_rises_while_submaximal` | Theorem | K < room -> энтропия total_S строго растёт, пока резервуар суб-максимален |
| `saturated_no_arrow` | Theorem | ★ L2: room <= K -> total_S постоянна — насыщенный резервуар => стрела ГЛОХНЕТ |
| `sign_is_reservoir_side` | Theorem | ★ оба процесса (сброс↑ и поглощение↓) двигают стадию => знак НЕ фиксирован P4, а = сторона резервуара (Гипотеза Прошлого) |
| `arrow_sign_analysis` | Theorem | ★ КАПСТОУН: три слоя (L0 форсирован / L1 выведен / L2 локализованный постулат) одной конъюнкцией |

**Key lemmas (deep):**

- **`saturated_no_arrow`** - Точная локализация постулата: как только room <= K, total_S = S0 + min K room перестаёт расти — стрела глохнет. Значит стрела СУЩЕСТВУЕТ только при суб-максимальном резервуаре, и весь «абсолютный знак» сводится к ОДНОМУ факту: с какой стороны лежит низкоэнтропийный (суб-максимальный) резервуар. Это сужает мнимо-большой постулат стрелы времени до одной точно названной посылки (Гипотеза Прошлого), не выдавая её за выведенную. _(posit-localization, saturation, arrow-of-time)_
- **`arrows_aligned`** - L1-слой: stage (стрела записи/памяти) и dump_S (энтропийная стрела) монотонно растут синхронно. Содержательно это перенос мысли Ландауэра (необратимая запись = термодинамический сброс) в арифметику nat: ПРИ ОТОЖДЕСТВЛЕНИИ актуализация=запись=сброс стрелы не могут разойтись — выравнивание ВЫВОДИМО (не постулат), тогда как сам Ландауэр-мост (логическая необратимость => тепловая цена) остаётся честно названным отождествлением, а не P4-следствием. _(landauer, arrow-alignment, derived, bridge)_
- **`arrow_sign_analysis`** - Капстоун-вердикт: три честных слоя (L0 направление = P4; L1 выравнивание = выведено через Ландауэра; L2 абсолютный знак = суб-максимальный резервуар + сторона = локализованный постулат). Ценность — методологическая: вместо плоского «знак стрелы — постулат» файл РАЗЛАГАЕТ вопрос на форсированное/выведенное/постулированное и точно указывает единственную оставшуюся посылку. Это новое ОБРАМЛЕНИЕ, не новая теорема; арифметика игрушечная (nat/lia). _(capstone, three-layer, synthesis, verdict)_

**Uniqueness - score 3 (new-framing).** Трёхслойный E/R/R-вердикт о знаке энтропии: направление форсировано P4, выравнивание стрел выведено через отождествление Ландауэра, абсолютный знак сведён к ОДНОЙ точно локализованной посылке (суб-максимальный резервуар со стороны прошлого) — острее плоского «знак — постулат».
> _Caveat:_ Стрела времени, выравнивание четырёх стрел, принцип Ландауэра и Гипотеза Прошлого — классика. Модели игрушечные (nat, min, lia). Файл НЕ выводит абсолютный знак (честно заявлено), и сам помечает: Ландауэр-мост = отождествление (не чистый P4), «энтропия=счёт записей» = Element-прокси (строгое = статистический/голографический счёт). Над-брендинг как «вывод стрелы времени» был бы оверклеймом — файл его избегает.

---

## #1874 - `src/foundation/DeterminacyAscent.v` - score 3 (new-framing)

**Determinacy as an ordinal-process ascent (stage 3): finite rung 0-ax (backward induction), finite->infinite step = exactly LPO, height = omega**

- **Topic.** Stage 3 of the Process-Hierarchy direction: the finite/clopen rung is decided 0-axiom by backward induction (mover_wins total), the step finite->infinite ('does player I ever win') is proven EXACTLY equivalent to LPO (every boolean process is a leaf-game value-process), LEM collapses it, and the rung index is the ordinal-process omega with unbounded rungs — so determinacy is an ordinal-indexed generating ascent, not a wall.
- **Role.** Process-Hierarchy stage 3 (after ProcessHierarchyCore stages 1-2 + HierarchyDepthLadder). Imports foundation.Ordinal (Ord/omega/OLim/nat_to_ord), FiniteGameDeterminacy (GameTree/mover_wins/GLeaf/finite_game_determined), RoleLimitLadder (LPO/LEM/lem_lpo). Reuses the omniscience-ladder floor-1 rung; companion to WqoOverDecidable / FormerWalls ledger.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith Lia Bool; foundation.Ordinal; foundation.FiniteGameDeterminacy; foundation.RoleLimitLadder
- **E/R/R.** _Elements:_ процесс конечных игр gp : nat -> GameTree; value-процесс open_value K = mover_wins (gp K); рунг-индекс determinacy_rank_index = nat_to_ord n. _Roles:_ конечный этап = игра (Element, разрешима обратной индукцией, рунг 0); «выиграет ли I когда-нибудь» = Sigma^0_1-вопрос (рунг всеведения); индекс рунга = omega-процесс. _Rules:_ конечный этап разрешим без оракула (0 ax); дихотомия eventual_decided <-> LPO (один рунг всеведения); LEM схлопывает; подъём порождающ (нет максимального рунга), высота = omega = OLim. _P4:_ ДИАГНОСТИКА: подъём ПОТЕНЦИАЛЕН (каждый рунг — процесс), не завершён; аксиома (LPO/LEM) входит НЕ как стена, а ТОЧНО на шаге финит->инфинит, локализована; полная борелевская детерминированность (Мартин) = consistency-strength ГОРИЗОНТ выше, открытый подъём, а НЕ бинарная стена. LPO/LEM здесь — Prop-ГИПОТЕЗЫ, не аксиомы файла (0 axioms).
- **Classical counterpart.** Gale-Stewart determinacy of open games, Borel determinacy (Martin, consistency-strength ~omega_1 iterations of powerset), backward induction for finite games, and the constructive-reverse-math fact that the clopen/open value-dichotomy of decidable games is LPO-equivalent (Bishop/Ishihara) are all classical; NEW is only placing this on an ordinal-PROCESS ascent (height = omega = OLim, no maximal rung) and bridging the finite rung to backward induction (mover_wins), recasting determinacy as a localized role-limit ascent rather than a binary wall.
- **Tags.** foundation, process-hierarchy, determinacy, LPO, ordinal, no-AC, role-limit, new-framing, not-a-wall

**Lemmas (9):**

| name | kind | role |
|---|---|---|
| `finite_depth_decidable` | Lemma | ★ рунг 0: победитель конечной игры РЕШАЕМ {mover_wins g=true}+{=false}, без оракула (обратная индукция) |
| `open_value` | Definition | value-процесс открытой игры: на этапе K — победитель K-усечённой конечной игры |
| `eventual_decided` | Definition | Sigma^0_1-дихотомия: I выигрывает на каком-то этапе \/ никогда (Sigma^0_1-ядро Гейла-Стюарта, не полная детерминированность) |
| `eventual_decided_is_LPO` | Theorem | ★ шаг финит->инфинит для ВСЕХ игр <-> LPO (каждый булев процесс = value-игра из листьев GLeaf) |
| `eventual_decided_classical` | Theorem | LEM -> forall gp, eventual_decided gp — классически рунг схлопывается |
| `determinacy_rank_index` | Definition | индекс рунга := nat_to_ord n (ординал-процесс) |
| `determinacy_ascent_height_is_omega` | Theorem | omega = OLim determinacy_rank_index — высота подъёма = ОРДИНАЛ-ПРОЦЕСС, не число |
| `determinacy_ranks_unbounded` | Theorem | рунги неограниченны (forall B, exists n>B) — порождающий подъём, замыкание = role-limit |
| `determinacy_is_ordinal_process_ascent` | Theorem | ★ КАПСТОУН: конечный рунг решён + открытый рунг=LPO + LEM схлопывает + высота=omega + нет максимального рунга |

**Key lemmas (deep):**

- **`eventual_decided_is_LPO`** - Содержательное ядро ступени: дихотомия «игрок I выигрывает на каком-то конечном этапе, либо ни на одном» для ВСЕХ игр-процессов РОВНО эквивалентна LPO. Доказательство-мост: всякий булев процесс g есть value-процесс игры из листьев (fun K => GLeaf (g K)), и обратная индукция mover_wins на листе тривиальна, так что eventual_decided коллапсирует в LPO-форму. Это точно локализует, ГДЕ входит неконструктивность: не во всю детерминированность, а ровно в шаг конечное->бесконечное (Sigma^0_1, тот же рунг, что этаж 1 лестницы всеведения). Честно: LPO-эквивалентность value-дихотомии разрешимых игр — известный факт constructive reverse math (Bishop/Ishihara); ново размещение на ординал-процесс-подъёме. _(LPO, omniscience, finite-to-infinite, role-limit, localization)_
- **`finite_depth_decidable`** - Рунг 0 (Element-сторона): победитель КОНЕЧНОЙ игры — настоящее РЕШЕНИЕ ({}+{}), а не просто классически определён; следует из тотальности и вычислимости обратной индукции mover_wins. Это «дно» подъёма, достигнутое 0 аксиом, контрастирующее с верхним Sigma^0_1-рунгом (LPO) того же файла — ровно мотив Element/role-limit-границы, перенесённый на детерминированность игр. _(backward-induction, decidable, element, rung-0)_
- **`determinacy_is_ordinal_process_ascent`** - Капстоун: детерминированность = ОРДИНАЛ-ИНДЕКСИРОВАННЫЙ ПОДЪЁМ, не бинарная стена — (1) конечный рунг достигнут 0-ax, (2) открытый Sigma^0_1-рунг = ровно LPO (LEM схлопывает), (3) индекс = omega=OLim, подъём порождающ (нет max). Полная борелевская детерминированность Мартина (consistency-strength omega_1 итераций powerset) честно оставлена как ГОРИЗОНТ выше, локализованный рунгом. Уровень — новое ОБРАМЛЕНИЕ классической детерминированности в процесс-онтологию ToS + сужение неконструктивного входа до одной точки; не новая теорема о детерминированности. _(capstone, ordinal-process, ascent, not-a-wall, synthesis)_

**Uniqueness - score 3 (new-framing).** Детерминированность игр переосмыслена как ординал-ПРОЦЕСС-подъём (высота omega=OLim, нет максимального рунга): конечный рунг разрешим 0-ax обратной индукцией, шаг финит->инфинит = РОВНО LPO (один точно локализованный неконструктивный вход), LEM его схлопывает.
> _Caveat:_ Гейл-Стюарт, борелевская детерминированность Мартина и LPO-эквивалентность value-дихотомии разрешимых игр (Bishop/Ishihara, constructive reverse math) — классика; файл это явно ПЕРЕИСПОЛЬЗУЕТ. Строится лишь НИЖНИЙ подъём (конечный рунг + Sigma^0_1=LPO); полная стратегическая/борелевская детерминированность НЕ доказывается (честно названа consistency-strength горизонтом). LPO/LEM — Prop-гипотезы, не аксиомы файла (0 axioms). Над-брендинг как «решение детерминированности» был бы оверклеймом.

---

## #1875 - `src/foundation/EnergyAsActualizationRate.v` - score 3 (new-framing)

**Energy as the rate of distinction-actualization: T=E/S, Q=T*S, Boltzmann S=Q/T as one-line Q-algebra (count->rate enrichment)**

- **Topic.** Reads ToS energy as the tempo of succession (rate layer beyond the bare entropy count), defines temperature = E/S, heat = T*S, entropy_from_heat = Q/T over Q, and proves the Boltzmann relation S=Q/T and E=T*S from heat=T*count (equipartition) — locating the residual import as the Noether reading + equipartition + units.
- **Role.** Stage of the spacetime/gravity-arrow descent (Energy*/Equipartition* sub-thread): digs the Boltzmann info<->heat bridge that was the last import of the entropy-sign analysis (ArrowSignReservoir.v). Self-contained (Stdlib QArith/Lqa only); companion to EntropyCountDefinitional.v (#1876, the info side) and EquipartitionBedrock/EquipartitionRule (the soft principle).
- **Counts.** Qed 5 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lqa
- **E/R/R.** _Elements:_ энергия E (полный темп, Q); энтропия S (счёт, Q); температура temperature E S = E/S; тепло heat T S = T*S; entropy_from_heat q T = q/T. _Roles:_ энергия = темп преемства (генератор времени, Нётер); температура = энергия на различение; тепло = T*счёт (равнораспределение); вход = Нётер-чтение + равнораспределение + единицы. _Rules:_ T = E/S; Q = T*S (равнораспределение) => S = Q/T (Больцман, boltzmann_dS_eq_dQ_over_T при T<>0); E = T*S (energy_is_T_times_count при S<>0). _P4:_ ДИАГНОСТИКА: тепло/энергия = переход счёт->СКОРОСТЬ (энергия = темп актуализации, частоты R-формулы; ToS-процесс nat->Q это уже содержит). Больцман dS=dQ/T сводится к (энтропия=счёт) + (температура=энергия/счёт) + (тепло=T*счёт, равнораспределение). Остаток ТРОЙНОЙ: Нётер-чтение энергии, равнораспределение (МЯГЧАЙШИЙ ToS-принцип, качество->количество), единицы (Дж/К/k_B). Мост не чужероден — слой скоростей ToS + мягкий принцип, не опаковая стена «инфо=тепло».
- **Classical counterpart.** The Boltzmann thermodynamic relation dS = dQ/T, the equipartition theorem, and the Noether energy<->time-translation correspondence are classical physics; NEW is only the E/R/R reading energy = rate/tempo of distinction-actualization (the count->rate enrichment) under which T=E/S, Q=T*S and the Boltzmann S=Q/T become a one-line Q-algebra — a reduction of the heat bridge to a ToS rate layer + equipartition + units, NOT a derivation of thermodynamics.
- **Tags.** foundation, thermodynamics, energy, boltzmann, equipartition, arrow-of-time, count-to-rate, new-framing, honest-residual
- **Notes.** STATUS-header drift: header says '6 Qed' but the file has exactly 5 Qed. (5 theorems, 5 Qed; 3 Definitions.) 0 Admitted, 0 own axioms. Over Q (QArith/Lqa), Open Scope Q_scope.

**Lemmas (8):**

| name | kind | role |
|---|---|---|
| `temperature` | Definition | температура := E/S (энергия на различение = темп на счёт) |
| `heat` | Definition | тепло := T*S (энергия в тепловых различениях, равнораспределение) |
| `entropy_from_heat` | Definition | обратный Больцман: S := q/T (энтропия из тепла и температуры) |
| `temperature_is_energy_per_distinction` | Theorem | temperature E S = E/S (определительно) |
| `heat_is_T_times_count` | Theorem | heat T S = T*S (определительно, равнораспределение) |
| `boltzmann_dS_eq_dQ_over_T` | Theorem | ★ Больцман: T<>0 -> entropy_from_heat (heat T S) T == S (S=Q/T выведено из тепло=T*счёт) |
| `energy_is_T_times_count` | Theorem | ★ S<>0 -> E == temperature E S * S (энергия = темп-на-различение * счёт) |
| `boltzmann_bridge_reduced` | Theorem | ★ КАПСТОУН: четыре соотношения T=E/S, Q=T*S, S=Q/T, E=T*S одной конъюнкцией |

**Key lemmas (deep):**

- **`boltzmann_dS_eq_dQ_over_T`** - Содержательное ядро: соотношение Больцмана S = Q/T получается как ОДНА строка Q-алгебры (Qmult_comm/Qmult_inv_r при T<>0) из определения тепло = T*счёт. Смысл редукции: если энтропия = счёт различений, а тепло = температура*счёт (равнораспределение), то dS=dQ/T — не самостоятельный физический закон, а АЛГЕБРА этих двух чтений. Честно: это показывает лишь, что ПРИ принятых отождествлениях соотношение тривиально; сами отождествления (особенно равнораспределение) остаются содержательным входом. _(boltzmann, equipartition, rate-layer, reduction)_
- **`boltzmann_bridge_reduced`** - Капстоун: четыре соотношения (T=E/S, Q=T*S, S=Q/T, E=T*S) собраны в одну теорему, демонстрируя, что тепло/энергия = слой СКОРОСТЕЙ ToS-процесса (обогащение счёт->темп, присутствующее как собственная частота R-формулы), а термодинамическое dS=dQ/T растворяется в энтропия=счёт + температура=энергия/счёт + равнораспределение. Уровень — новое ОБРАМЛЕНИЕ (count->rate), с ЧЕСТНО названным тройным остатком: Нётер-чтение энергии, равнораспределение (мягчайший ToS-принцип), единицы. Не новая физика и не новая теорема — растворение опаковой стены «инфо=тепло» в названные компоненты. _(capstone, count-to-rate, synthesis, honest-residual)_

**Uniqueness - score 3 (new-framing).** Энергия прочитана как ТЕМП актуализации различений (обогащение счёт->скорость ToS-процесса), под которым T=E/S, Q=T*S и соотношение Больцмана S=Q/T становятся одной строкой Q-алгебры; мост инфо<->тепло сведён к слою скоростей ToS + равнораспределение + единицы.
> _Caveat:_ Соотношение Больцмана dS=dQ/T, равнораспределение и Нётер-соответствие энергия<->время — классическая физика. Доказательства — тривиальная Q-алгебра при T,S<>0 (определения T,Q,S выбраны под результат). Файл сам помечает ТРОЙНОЙ неустранённый остаток: Нётер-чтение (мост, не P4-следствие), равнораспределение (МЯГЧАЙШИЙ ToS-принцип, разрыв качество->количество), единицы k_B. Над-брендинг как «вывод термодинамики/энергии» был бы оверклеймом — файл его избегает. ДРЕЙФ: STATUS-заголовок заявляет 6 Qed, фактически 5.

---

## #1876 - `src/foundation/EntropyCountDefinitional.v` - score 3 (new-framing)

**Entropy = distinction count is definitional (W=2^count, count=log2 W, additive<->multiplicative); the only genuine import is Boltzmann/heat**

- **Topic.** Defines config_count(n)=2^n and entropy_bits(n)=n, proves count=log2 W (2^count=W), W=2^count, entropy additive while W multiplicative (Nat.pow_add_r) — establishing that 'entropy = distinction count' is definitional in ToS, so the information arrow is fully ToS (P4+L2+indifference+origin) and only the heat reading imports Boltzmann + k_B units.
- **Role.** Last input of the spacetime/gravity entropy-sign analysis (ArrowSignReservoir.v), examined: shows the info-entropy side is ToS-definitional, isolating Boltzmann/heat as the one irreducible import (handled in EnergyAsActualizationRate.v #1875). Self-contained (Stdlib Arith/Lia only); leans on EquipartitionRule/RecordingFromP4 conceptually, not by import.
- **Counts.** Qed 5 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith Lia
- **E/R/R.** _Elements:_ счёт различений n; число конфигураций config_count n = 2^n; энтропия в битах entropy_bits n = n. _Roles:_ n = инфо-энтропия (бит) = счёт различений; W = различимые конфиги (= набор-различений); log = мост аддитивное<->мультипликативное (экстенсивность). _Rules:_ конфиг = набор различений => W = 2^count; индифферентность (EquipartitionRule) => Shannon S = log W = count; счёт АДДИТИВЕН, W МУЛЬТИПЛИКАТИВНА => log-мост форсирован. _P4:_ ДИАГНОСТИКА: «энтропия=счёт» ОПРЕДЕЛИТЕЛЬНА в ToS (W=2^count из конфиг=набор-различений; индифферентность => S=log W; счёт аддитивен / W мультипликативна => log-мост), НЕ субстантивный импорт. Настоящий импорт = Больцман (инфо-энтропия = ТЕПЛОВАЯ энтропия) + k_B-единицы — про ТЕПЛО, не про стрелу. ИНФО-стрела = целиком ToS (P4+L2+индифферентность+происхождение). ЧЕСТНО: индифферентность — мягчайший ToS-принцип; W=2^count предполагает НЕЗАВИСИМЫЕ различения (max-энтропийный/свободный случай).
- **Classical counterpart.** Boltzmann's S = k log W, Shannon entropy = log W under equiprobable microstates (the indifference/equipartition assumption), and the extensivity (additivity of entropy <-> multiplicativity of microstate count) are classical; NEW is only the E/R/R verdict that 'entropy = distinction count' is DEFINITIONAL in ToS (a configuration IS its distinction-set => W=2^count, count=log2 W), so the genuine irreducible import is solely Boltzmann's info-entropy = HEAT-entropy hypothesis + the k_B unit — about heat, not the directional arrow.
- **Tags.** foundation, entropy, information, boltzmann, shannon, equipartition, arrow-of-time, P4, new-framing, honest-residual

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `config_count` | Definition | число различимых конфигураций n независимых бинарных различений := 2^n (конфиг = набор различений) |
| `entropy_bits` | Definition | инфо-энтропия в битах := n (= log2 W = счёт различений) |
| `count_is_log2_of_W` | Theorem | ★ 2^(entropy_bits n) = config_count n — счёт ЕСТЬ log2(W) (определительно) |
| `W_eq_two_pow_count` | Theorem | config_count n = 2^n — W = 2^count (конфиг = набор различений) |
| `entropy_additive` | Theorem | entropy_bits (n+m) = entropy_bits n + entropy_bits m — инфо-энтропия аддитивна/экстенсивна |
| `W_multiplicative` | Theorem | ★ config_count (n+m) = config_count n * config_count m (Nat.pow_add_r) — W мультипликативна => log-мост форсирован |
| `entropy_count_is_definitional` | Theorem | ★ КАПСТОУН: четыре факта (count=log2 W, W=2^count, энтропия аддитивна, W мультипликативна) одной конъюнкцией |

**Key lemmas (deep):**

- **`W_multiplicative`** - Содержательный шарнир: число конфигураций мультипликативно W(n+m)=W(n)*W(m) (через Nat.pow_add_r), тогда как энтропия-счёт аддитивна (entropy_additive). Сопоставление этих двух фактов показывает, что «логарифм» в S=log W НЕ дополнительный физический постулат, а ВЫНУЖДЕННЫЙ аддитивно<->мультипликативный мост (экстенсивность), как только конфигурации суть наборы различений. Это и есть растворение мнимого импорта «энтропия=log W» в определение. _(extensivity, log-bridge, additive-multiplicative, definitional)_
- **`entropy_count_is_definitional`** - Капстоун-вердикт: «энтропия = счёт различений» ОПРЕДЕЛИТЕЛЬНА в ToS — count=log2 W, W=2^count, аддитивность счёта + мультипликативность W = log-мост. Отсюда стратегический вывод файла: ИНФОРМАЦИОННАЯ стрела целиком ToS (P4 + L2 бинарность + индифферентность + происхождение), а ЕДИНСТВЕННЫЙ настоящий импорт — гипотеза Больцмана (инфо-энтропия = ТЕПЛОВАЯ энтропия) + единица k_B, которая про ТЕПЛО, не про направление стрелы. Уровень — новое ОБРАМЛЕНИЕ + точная локализация истинного импорта; не новая теорема (равенства определительны, доказательства = reflexivity/pow_add_r). Честно: индифферентность = мягчайший принцип, W=2^count предполагает независимые различения. _(capstone, definitional-reduction, import-localization, synthesis)_

**Uniqueness - score 3 (new-framing).** «Энтропия = счёт различений» показана ОПРЕДЕЛИТЕЛЬНОЙ в ToS (конфиг=набор-различений => W=2^count => count=log2 W; счёт аддитивен / W мультипликативна => log-мост), так что единственный неустранимый импорт — гипотеза Больцмана инфо=тепло + единица k_B, и информационная стрела оказывается целиком ToS.
> _Caveat:_ Больцманово S=k log W, Шеннон S=log W при равновероятных микросостояниях и экстенсивность (аддитивность<->мультипликативность) — классика. Доказательства тривиальны (reflexivity, Nat.pow_add_r); определения config_count/entropy_bits выбраны под результат. Файл сам помечает: индифферентность (EquipartitionRule) — МЯГЧАЙШИЙ ToS-принцип (качество->количество), а W=2^count предполагает НЕЗАВИСИМЫЕ различения (свободный/max-энтропийный случай). Над-брендинг как «вывод энтропии» был бы оверклеймом — файл локализует, а не выводит, истинный (Больцман/тепло) импорт.

---

## #1877 - `src/foundation/EntropyMagnitudeLandauer.v` - score 3 (new-framing)

**Per-actualization entropy magnitude via the Landauer bridge: conditional on cost>=1, ToS supplies only the 1-bit unit and the proper-time tie**

- **Topic.** Models the MAGNITUDE of entropy production per actualization in bits: each irreversibly recorded distinction costs >= 1 bit (Landauer, as a premise), binarity (L2) fixes the minimal cost at exactly 1 bit, entropy grows linearly with the stage count (proper time) while a finite reservoir has room, then saturates (heat death).
- **Role.** First file of the gravity<->time<->arrow arc that imports a PHYSICS PRINCIPLE (Landauer) as an explicit INPUT rather than deriving it from P4. Self-contained (Stdlib only). Companion to ArrowSignReservoir.v / ArrowSignFromOrigin.v (which handle the sign/direction; this file handles only the per-step magnitude).
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith Lia
- **E/R/R.** _Elements:_ стоимость на актуализацию cost (биты); энтропия (биты); счёт стадий K = собственное время (необратимо актуализированные записи, P4). _Roles:_ cost = ландауэровский пол (энтропия на записанный бит); значение 1 = бинарность (L2, различение = ровно один бит); энтропия = записи*cost. _Rules:_ Ландауэр (ВХОД) cost>=1; бинарность cost=1; dS = cost на актуализацию (entropy_rate); пол S >= S0 + собств_время*cost; рост, пока room, затем насыщение. _P4:_ Ландауэр — ЯВНЫЙ вход, НЕ выводим из чистого P4 (нужно 2-е начало). ToS даёт ЕДИНИЦУ (бинарность = 1 бит) и привязку энтропии к собственному времени. Выводимо ПРИ cost>=1: линейность, строгий рост, пол >= собств.время, насыщение. ЧЕСТНО: результаты УСЛОВНЫ; Coq 0-аксиомен (Ландауэр = гипотеза 1<=cost, не Axiom). Уровень: вывод-при-явном-входе.
- **Classical counterpart.** Landauer's principle (erasing one bit costs >= k_B T ln2 of entropy) and the second law are classical thermodynamics; NEW here is only the bookkeeping that splits the per-step entropy magnitude into a ToS UNIT (a distinction = exactly 1 bit, L2) plus a proper-time = stage-count tie (P4), with Landauer entering honestly as a PREMISE (1 <= cost), not derived.
- **Tags.** foundation, arrow, landauer, entropy, proper-time, conditional, binarity, P4, heat-death

**Lemmas (11):**

| name | kind | role |
|---|---|---|
| `stage` | Definition | собственное время = счёт стадий K (необратимые записи, P4): stage K := K |
| `min_entropy` | Definition | пол энтропии (биты): S0 + cost*K, накопленный за K стадий |
| `capped_entropy` | Definition | пол с конечным резервуаром room слотов: S0 + cost*min(K,room) |
| `binary_cost` | Definition | бинарность (L2): различение = ровно один бит, минимальная стоимость = 1 |
| `binarity_minimal_floor` | Theorem | вклад ToS: бинарность фиксирует минимальный пол в 1 бит (1 <= binary_cost) |
| `entropy_rate` | Theorem | ★ РИТМ: каждая актуализация поднимает пол ровно на per-bit cost (min_entropy на S K = +cost) |
| `entropy_strictly_increases` | Theorem | при Ландауэре (cost>=1): энтропия СТРОГО растёт на каждой актуализации |
| `entropy_at_least_proper_time` | Theorem | ★ ПРИВЯЗКА: при cost>=1 энтропия >= S0 + собственное время (термо-часы не медленнее часов собств. времени) |
| `capped_grows_while_room` | Theorem | пол растёт со скоростью cost, ПОКА резервуар субмаксимален (K < room) |
| `capped_saturates` | Theorem | ...и НАСЫЩАЕТСЯ (нет роста), когда резервуар полон (тепловая смерть / полный коллапс) |
| `entropy_magnitude_landauer` | Theorem | ★ КАПСТОУН: конъюнкция бинарность+ритм+строгий рост+привязка+рост-пока-room+насыщение |

**Key lemmas (deep):**

- **`entropy_at_least_proper_time`** - Количественная привязка двух часов: при cost>=1 (Ландауэр) накопленная энтропия ограничена СНИЗУ собственным временем (счётом стадий) плюс S0 — на каждый тик собственного времени приходится >= 1 бит энтропии. Это и есть содержательный мост thermo-time <-> proper-time, ради которого файл написан: термодинамические часы не могут идти медленнее часов собственного времени (в битах на стадию). ЧЕСТНО: тривиальная nat-арифметика (nia); ценность — постановка, а не сложность доказательства, и она УСЛОВНА на Ландауэре. _(proper-time, landauer, conditional, arrow, P4)_
- **`entropy_magnitude_landauer`** - Капстоун-конъюнкция всего файла: (бинарность) минимальный пол = ровно 1 бит из L2; (ритм) каждая актуализация добавляет cost бит; (строгий рост) при Ландауэре энтропия строго растёт; (привязка) рост >= собственное время; (room/saturate) растёт пока резервуар имеет место, затем насыщается. Явно сформулировано как ВЫВОД ПРИ мосте Ландауэра, НЕ как вывод Ландауэра/2-го начала. ToS вносит только единицу (бинарность) и привязку к собственному времени; всё остальное условно на входе cost>=1. _(capstone, conditional, second-law, entropy, heat-death)_

**Uniqueness - score 3 (new-framing).** Декомпозиция per-step магнитуды энтропии на ToS-единицу (различение = 1 бит, L2) + привязку к собственному времени (dS >= dtau на каждый тик), с явным, честным импортом Ландауэра как премиссы 1<=cost.
> _Caveat:_ Ландауэр и 2-е начало КЛАССИЧНЫ и здесь не выводятся — все результаты УСЛОВНЫ на входе cost>=1; сам файл это многократно подчёркивает. Энтропия в БИТАХ = Element-сторонний счёт (не полная статистическая энтропия). Доказательства — тривиальная nat-арифметика (lia/nia); новизна только в рамке-декомпозиции.

---

## #1878 - `src/foundation/EquipartitionFromL4.v` - score 3 (new-framing)

**Equipartition reduced to L4 (Sufficient Reason): indifference = contrapositive of 'a weight-difference needs a distinguishing reason', value 1/N from normalization**

- **Topic.** Digs under the equipartition residual of EnergyAsActualizationRate.v: indifference (undistinguished configs carry equal weight) is derived constructively as the contrapositive of L4 via decidability of Qeq (no classic), and normalization gives the equipartition VALUE 1/N. So equipartition is not a soft separate bottom — its qualitative half IS L4.
- **Role.** Reduction file in the spacetime/arrow descent: closes the qualitative->quantitative gap EquipartitionBedrock.v flagged. Self-contained (Stdlib QArith only; uses Qeq decidability, NOT classic). Sibling of EquipartitionRule.v / EquipartitionBedrock.v / TierThreeUniversality.v.
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lqa Lia
- **E/R/R.** _Elements:_ конфиги Config; вес weight : Config -> Q (априорная плотность); отношение distinguishes : Config -> Config -> Prop. _Roles:_ L4 = различие веса требует различающей причины (distinguishes); индифферентность = его контрапозиция; нормировка = веса в сумме 1. _Rules:_ L4: ~(weight a == weight b) -> distinguishes a b; индифферентность (выведена): ~distinguishes a b -> weight a == weight b; нормировка: k равных весов в сумме 1 => каждый = 1/k. _P4:_ равнораспределение <= L4 (Достаточное основание) + нормировка — ЯДРОВОЙ закон, не мягкое дно. Качественная половина = L4 (взвесить a над b = провести различение A>B; без основания запрещено). ОСТАТКИ (честно): (1) различимые микросостояния равновероятны нужно равновесие = конец P4-стрелы; (2) энергия=темп — L5/Нётер, спекулятивнее, НЕ формализую; (3) глубоко в интерпретации, тугой ранней структуры тут нет.
- **Classical counterpart.** The principle of indifference / a-priori equiprobability (Laplace, Jaynes) and statistical-mechanics equipartition are classical; NEW is recasting the QUALITATIVE half as the contrapositive of L4 (Sufficient Reason) — undistinguished alternatives carry equal weight because a weight-difference would require a distinguishing reason — with the 1/N value from normalization.
- **Tags.** foundation, equipartition, L4, sufficient-reason, indifference, no-classic, reduction, arrow, P4

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `indifference_from_L4` | Theorem | ★ ИНДИФФЕРЕНТНОСТЬ = контрапозиция L4: ~distinguishes a b -> weight a == weight b; конструктивно через Qeq_dec (0 аксиом, без classic) |
| `equipartition_value_2` | Theorem | конкретный N=2: два равных веса в сумме 1 => каждый = 1/2 |
| `equipartition_value` | Theorem | ★ общий N: k равных весов в сумме 1 => каждый = 1/k (значение равнораспределения из нормировки, field; lra) |

**Key lemmas (deep):**

- **`indifference_from_L4`** - Ядро редукции: качественное равнораспределение получено как ЛОГИЧЕСКАЯ контрапозиция закона L4 (Достаточного основания). L4 постулирует «различие веса требует различающей причины»; индифферентность — это в точности «нет причины => нет различия». Ключ к 0-аксиомности: вывод конструктивен через decidability Qeq (Qeq_dec), а НЕ через classic — равенство весов разрешимо, поэтому контрапозиция законна без LEM. Это и есть заявленная редукция «равнораспределение = L4», а не отдельное мягкое дно. _(L4, sufficient-reason, indifference, constructive, no-classic)_
- **`equipartition_value`** - Количественная половина: k равных весов, нормированных в сумму 1, каждый = 1/k. Тривиальная Q-арифметика (field; lra с положительностью inject_Z (Zpos k)), но именно она закрывает qual->quant зазор, который EquipartitionBedrock.v отметил: L4 даёт КАЧЕСТВЕННОЕ равенство, нормировка даёт ЗНАЧЕНИЕ 1/N. Честно: значение тривиально; вклад — сцепка с L4-половиной в один вывод. _(normalization, value, equipartition, Q-arith)_

**Uniqueness - score 3 (new-framing).** Качественное равнораспределение (индифферентность) выведено КОНСТРУКТИВНО как контрапозиция ядрового закона L4 через разрешимость Qeq (0 аксиом, без classic); значение 1/N — из нормировки. Equipartition перестаёт быть отдельным мягким дном.
> _Caveat:_ Принцип индифферентности (Лаплас/Джейнс) и равнораспределение КЛАССИЧНЫ. Файл сам перечисляет 3 ЧЕСТНЫХ остатка: (1) полная СМ-equipartition различимых микросостояний дополнительно требует равновесия = конца P4-стрелы; (2) «энергия=темп преемственности» НЕ формализована (спекулятивнее); (3) глубоко интерпретативно. Доказательства тривиальны.

---

## #1879 - `src/foundation/FiniteGameDeterminacy.v` - score 3 (new-framing)

**Finite-game determinacy rolls back to backward induction on a finite tree: a total computable function, no completed tower**

- **Topic.** Rolls back the 'wall' of Borel/Martin determinacy: on a FINITE game tree the winner ('whoever moves') is computed by BACKWARD INDUCTION (mover_wins) as a total computable bool, with no iterated-power-set tower. The completed infinite tower is the ZFC packaging; the Borel extension is a process-indexed role-type hierarchy (NOT-yet-invoked-as-process), not a wall.
- **Role.** Part of the process-hierarchy / former-walls direction. Self-contained (Stdlib List Bool). Cited by FormerWallsLedger.v (the WBorelTower entry) and the companion FiniteWqoPigeonhole.v; the full ascent lives in DeterminacyAscent.v (finite rung 0-ax + open rung = LPO).
- **Counts.** Qed 2 / Admitted 0 / axioms 0
- **Imports.** Stdlib: List Bool
- **E/R/R.** _Elements:_ конечные деревья игры GameTree (GLeaf bool \| GNode list), позиции, партии. _Roles:_ стратегия = процесс (правило позиция -> ход); детерминированность = роль «у кого выигрыш» (тотальный bool). _Rules:_ обратная индукция mover_wins: узел выигрышен <=> есть ребёнок, после которого ПРОТИВНИК (теперь ходящий) проигрывает (orb (negb ...)); тотальность mover_wins => детерминированность. _P4:_ завершённая бесконечность здесь = упаковка башни итерированных степеней; конечная игра свободна (mover_wins — тотальная вычислимая функция). Борелевское расширение = процессно-индексированная иерархия роль-типов, НЕ привлечено как процесс, не стена.
- **Classical counterpart.** Borel determinacy (Martin's theorem) classically climbs a COMPLETED tower of iterated power sets (Borel hierarchy up to ~omega_1); the finite-tree case here is the elementary BACKWARD-INDUCTION / Zermelo theorem (every finite game is determined). NEW is only the P4 framing: the completed tower is a ZFC-packaging artifact, not a P4 wall.
- **Tags.** foundation, determinacy, backward-induction, former-wall, process-hierarchy, finite, no-tower, P4

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `GameTree` | Inductive | конечное дерево игры: GLeaf (mover_wins_here:bool) \| GNode (children: list GameTree) |
| `mover_wins` | Fixpoint | ★ обратная индукция: ход выигрышен, если есть ребёнок, после которого противник проигрывает (вложенный fix any по списку); тотальная вычислимая bool |
| `finite_game_determined` | Theorem | ★ детерминированность: mover_wins g = true \/ = false (победитель определён, без завершённой башни) |
| `game_mover_wins` | Example | конкретный счёт: mover_wins (GNode [GLeaf false; GLeaf true]) = true (vm-вычисление) |

**Key lemmas (deep):**

- **`mover_wins`** - Element-ядро отката: победитель «того, чей ход» на конечном дереве — структурно-рекурсивная тотальная функция (вложенный fix any реализует 'exists ребёнок с проигрышем противника' = orb (negb (mover_wins c)) ...). Именно тотальность и вычислимость на КОНЕЧНОМ дереве показывают, что содержание детерминированности не нуждается ни в каком completed tower степеней — башня нужна лишь классическому борелевскому доказательству на бесконечных играх. _(backward-induction, total-function, finite, determinacy)_
- **`finite_game_determined`** - Вердикт-теорема (тривиальная: destruct по bool): раз mover_wins тотальна и булева, победитель определён по построению. Это конечная грань Цермело/обратной индукции; ценность в РАМКЕ — завершённая башня борелевской иерархии переосмыслена как ZFC-упаковка, а не P4-запрет. ЧЕСТНО: полный Мартин/Борель НЕ доказан здесь; его частичный откат (нижние рунги как процессы + открытый рунг = LPO) — в DeterminacyAscent.v. _(determinacy, verdict, former-wall, P4)_

**Uniqueness - score 3 (new-framing).** Конечная детерминированность как тотальная вычислимая обратная индукция (0 аксиом), переосмысленная по P4: завершённая башня борелевской иерархии = ZFC-упаковка, не подлинная стена ToS.
> _Caveat:_ Обратная индукция / теорема Цермело о конечных играх — КЛАССИКА; mover_wins элементарна, finite_game_determined — destruct по bool. ПОЛНАЯ борелевская детерминированность (Мартин) НЕ доказана; её частичный откат (процессные рунги + LPO) вынесен в DeterminacyAscent.v. Новизна только в рамке-вердикте.

---

## #1880 - `src/foundation/FiniteWqoPigeonhole.v` - score 2 (methods)

**WQO rolls back to a finite pigeonhole kernel: any sequence over a finite type repeats, and a repeat is a 'good pair'**

- **Topic.** Rolls back the 'wall' of full Kruskal: the Element-kernel of a well-quasi-order is a finite PIGEONHOLE — any sequence over a finite type repeats, and a repeat is a 'good pair' (x <= x in any quasi-order). The infinity is neither in the trees (finite) nor in ordinal strength (epsilon_0 reached as a process) but ONLY in choosing the minimal-bad-sequence — a dependent-choice / decidability question.
- **Role.** Smallest file of the process-hierarchy / former-walls direction (1 Qed). Self-contained (Stdlib Bool). Cited by FormerWallsLedger.v (the WMinimalBadSequence entry); the general nat-wqo + N-measurable closure + method-as-process lives in WqoProcessDecidable.v; concrete wqo families (Higman) cited as classic.
- **Counts.** Qed 1 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Bool
- **E/R/R.** _Elements:_ конечные значения (здесь bool — простейший конечный тип); последовательности над ними. _Roles:_ «плохая последовательность» = процесс без раннего повтора; «хорошая пара» = повтор (x <= x в любом квазипорядке). _Rules:_ голубятня — три значения в двухэлементном типе => совпадение хотя бы двух (хорошая пара). _P4:_ завершённая бесконечность = упаковка выбора минимально-плохой последовательности; конечное ядро (голубятня) свободно. Бесконечность НЕ в деревьях (конечны) и НЕ в ординальной силе (epsilon_0/transfinite_ind достигнуты как процессы, 0-ax, цитата), а ТОЛЬКО в выборе мин.-плохой посл-ти — а это зависимый выбор (DC), вопрос РАЗРЕШИМОСТИ (лестница выбора cs/), не бесконечности.
- **Classical counterpart.** Kruskal's tree theorem / well-quasi-order theory classically uses a MINIMAL-BAD-SEQUENCE argument (choice over the completed space of all bad sequences); the finite kernel here is the elementary PIGEONHOLE principle. NEW is only the P4 localization: the infinity sits ONLY in the minimal-bad-sequence choice (a decidability / dependent-choice question), not in trees or ordinal strength.
- **Tags.** foundation, wqo, pigeonhole, kruskal, former-wall, process-hierarchy, finite-kernel, dependent-choice, P4

**Lemmas (1):**

| name | kind | role |
|---|---|---|
| `bool_pigeonhole3` | Lemma | ★ конечное голубятное ядро wqo: среди трёх булевых значений два совпадают (a=b \/ b=c \/ a=c); доказано полным destruct a,b,c |

**Key lemmas (deep):**

- **`bool_pigeonhole3`** - Единственная лемма файла и есть весь его смысл: предъявляет Element-ядро wqo как конечную голубятню — три значения в двухэлементном типе bool вынуждают совпадение, а совпадение = «хорошая пара» (рефлексивность квазипорядка). Доказательство — исчерпывающий destruct по 2^3 случаям. Риторический вес (в заголовке): он локализует ВСЮ бесконечность теоремы Крускала в ОДНОМ месте — выборе минимально-плохой последовательности (DC), переводя «стену бесконечности» в вопрос разрешимости/выбора, который изучает лестница cs/. _(pigeonhole, wqo, finite-kernel, good-pair, former-wall)_

**Uniqueness - score 2 (methods).** Element-ядро wqo предъявлено как конечная голубятня (0 аксиом) + локализация всей бесконечности полного Крускала в одном месте — выборе мин.-плохой последовательности (DC = вопрос разрешимости, не бесконечности).
> _Caveat:_ Голубятня и wqo-теория — КЛАССИКА; bool_pigeonhole3 — тривиальный destruct по 8 случаям, лишь bool-инстанс. ПОЛНЫЙ Крускал НЕ доказан; общий nat-wqo + N-измеримое замыкание + метод-как-процесс вынесены в WqoProcessDecidable.v, семейства Хигмана цитируются как classic. Ценность — почти целиком в рамочной локализации, а не в самой лемме.

---

## #1881 - `src/foundation/FormerWallsLedger.v` - score 4 (synthesis+observation)

**Ledger of 'former walls': each supposed completed infinity is a ZFC-packaging artifact; exactly completed infinity is the one true P4 wall**

- **Topic.** A verdict ledger (synthesis/classification, NOT a new theorem) collapsing the rollback of three 'high' set-theory theorems into one auditable verdict: completed P(N) is ReachedFreely, full Kruskal and Borel determinacy are PartiallyReached (lower rungs built as processes, full forms = consistency-strength horizon), and the only genuinely ForbiddenObject is completed actual infinity itself — a P4 ontological choice, not an unreachability.
- **Role.** Synthesis/capstone of the process-hierarchy / former-walls direction; parallel to ZFCAxiomLedger.v. Self-contained (Stdlib List Bool). The GENUINE 0-ax witnesses live in the cited per-place files: PowersetRoleType.v, FiniteGameDeterminacy.v, FiniteWqoPigeonhole.v, and the ProcessHierarchy* / DeterminacyAscent / WqoProcessDecidable ascent (stages 1-5).
- **Counts.** Qed 4 / Admitted 0 / axioms 0
- **Imports.** Stdlib: List Bool
- **E/R/R.** _Elements:_ перечисления Wall (4 стены) / Status (4 вердикта) / классификационные конструкторы. _Roles:_ «стена» = роль-требование завершённого объекта; вердикт status = роль (достигнуто-свободно / частично / не-привлечено / запрещено). _Rules:_ status w; forbidden s; ровно WCompletedInfinity = ForbiddenObject; три «высокие» стены откатываются (одна свободно, две частично); zfc_posits vs tos_needs. _P4:_ из трёх классических «стен» ни одна не есть подлинный P4-запрет: completed-P(N) откатывается к достигнутой роли/операции; полный Крускал и борелевская детерминированность ЧАСТИЧНО откачены (нижние рунги КАК ПРОЦЕССЫ), полные формы = consistency-strength ГОРИЗОНТ-ПОДЪЁМ, без противоречия. Единственный запрещённый объект — сама завершённая актуальная бесконечность (WCompletedInfinity), и это ОНТОЛОГИЧЕСКИЙ выбор P4, а не недостижимость.
- **Classical counterpart.** The three 'high' set-theoretic theorems it indexes — the completed power set P(N) (Cantor), full Kruskal (minimal-bad-sequence), Borel/Martin determinacy (iterated-power tower) — are all classical; NEW is NOT a theorem but a SYNTHESIS/CLASSIFICATION verdict ledger (parallel to ZFCAxiomLedger.v) that exactly one of them (the completed actual infinity itself) is a genuine P4-forbidden object.
- **Tags.** foundation, former-walls, ledger, synthesis, completed-infinity, process-hierarchy, zfc-artifact, classification, consistency-strength, P4

**Lemmas (10):**

| name | kind | role |
|---|---|---|
| `Wall` | Inductive | 4 «стены»: WPowersetObject \| WMinimalBadSequence \| WBorelTower \| WCompletedInfinity |
| `Status` | Inductive | 4 вердикта: ReachedFreely \| PartiallyReached \| NotYetBuilt \| ForbiddenObject |
| `status` | Definition | присваивает вердикт: P(N)=ReachedFreely, Kruskal/Borel=PartiallyReached, completed-inf=ForbiddenObject (с цитатами файлов-свидетелей) |
| `forbidden` | Definition | булев предикат: ForbiddenObject => true, иначе false |
| `only_completed_infinity_is_a_wall` | Theorem | ★ ровно одна стена — подлинный запрет: forbidden (status w) = true <-> w = WCompletedInfinity |
| `high_walls_dissolve` | Theorem | три классические «стены» НЕ запрещены: P(N) ReachedFreely, Kruskal/Borel PartiallyReached |
| `zfc_posits_completed_object` | Definition | классически каждая стена постулирует завершённый объект (всегда true) |
| `tos_needs_completed_object` | Definition | в ToS завершённый объект нужен ТОЛЬКО самой бесконечности (WCompletedInfinity => true) |
| `tos_reaches_content_without_completed_object` | Theorem | для каждой стены != completed-inf: ZFC постулирует объект (true), ToS его не требует (false) |
| `former_walls_are_artifacts` | Theorem | ★ КАПСТОУН: «бывшие стены» = артефакты ZFC-упаковки + ровно completed-inf = запрет (конъюнкция предыдущих двух) |

**Key lemmas (deep):**

- **`only_completed_infinity_is_a_wall`** - Сердце вердикта: среди 4 перечисленных стен РОВНО ОДНА (завершённая актуальная бесконечность) несёт статус ForbiddenObject; три «высокие» теоретико-множественные стены — нет. Доказательство — destruct по 4 конструкторам (reflexivity/discriminate). Содержательно это и есть тезис всего направления: подлинная граница ToS — не сила теорем, а онтологический отказ от завершённой бесконечности (выбор P4); остальное достижимо (свободно или частично-как-процессы). _(verdict, completed-infinity, former-wall, classification, P4)_
- **`former_walls_are_artifacts`** - Капстоун-конъюнкция: (1) для каждой стены кроме самой бесконечности ZFC постулирует завершённый объект, а ToS достигает содержания без него (PowersetRoleType / FiniteGameDeterminacy / FiniteWqoPigeonhole); (2) ровно completed-infinity = запрет. ЧЕСТНО (заявлено в файле): это СИНТЕЗ/КЛАССИФИКАЦИЯ, НЕ новая теорема; genuine-свидетели живут в цитируемых файлах; ПОЛНЫЕ Крускал/Борель НЕ доказаны — их полные формы остаются consistency-strength горизонтом-подъёмом, частичный откат (нижние рунги как процессы) — в направлении ProcessHierarchy*/DeterminacyAscent/WqoProcessDecidable. _(capstone, synthesis, zfc-artifact, consistency-strength, former-wall)_

**Uniqueness - score 4 (synthesis+observation).** Аудируемый свод-вердикт (параллель ZFCAxiomLedger): три «высокие» теоретико-множественные стены сведены в одну классификацию — две частично-откачены как процессы, одна свободно, и наблюдение, что РОВНО завершённая актуальная бесконечность = единственный подлинный P4-запрет (онтологический выбор, не недостижимость).
> _Caveat:_ Три индексируемые теоремы (Кантор P(N), Крускал, Борель/Мартин) — КЛАССИКА; сам файл — синтез/классификация, НЕ новая теорема, 0 содержательных свидетелей внутри (все в цитируемых файлах). ПОЛНЫЕ Крускал/Борель НЕ доказаны (consistency-strength горизонт); статусы PartiallyReached опираются на уже доказанные 0-ax/classic результаты в ProcessHierarchy*/DeterminacyAscent/WqoProcessDecidable. Доказательства — destruct по перечислениям. Ценность — унификация/наблюдение, не теорема.

---

## #1882 - `src/foundation/GravityArrowEntropy.v` - score 4 (synthesis+observation)

**Gravitational arrow = thermodynamic arrow = one distinction-density tendency; P4 forces the direction, the SIGN stays a posit**

- **Topic.** Identifies entropy with distinction-density count (holographic proxy) and shows fall toward slower time = higher density = higher entropy; P4 forces the temporal DIRECTION (stage-count up) but NOT the sign (cluster vs disperse both advance the stage), so entropy increase needs the same low-density-past posit isolated by ArrowGroundingDescent.v; capped by a holographic ceiling that gravitational collapse reaches.
- **Role.** Part of the foundation SPACETIME/GRAVITY-ARROW descent; continues GravityIsTimeGradient.v and reuses the sign-posit of ArrowGroundingDescent.v, the time_rate=1/K link of PolarizableVacuumIndex.v, the S=A/l_P^2 count of HolographicEntropy.v (all cited, none imported — Stdlib-only, self-contained). Honest 'what reduces vs what is imported' node.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith Lia
- **E/R/R.** _Elements:_ счёт стадий K; плотность различений rho; энтропия S=rho (голографический счёт, 1 бит/различение); потолок holo_max=100. _Roles:_ K = направление стрелы (P4); rho = плотность = цель гравитации (высокое K) = энтропия; две траектории rho_cluster/rho_disperse = неоднозначность знака. _Rules:_ P4 => счёт стадий строго растёт (направление); гравитация => падение к большему rho; энтропия = rho; знак НЕ форсирован (обе траектории продвигают стадию) => нужен низкоплотный старт; rho <= holo_max. _P4:_ ОБЪЕДИНЯЕТ гравитационную и термодинамическую стрелы как ОДНУ тенденцию плотности с ОДНИМ постулатом. Честно: НАПРАВЛЕНИЕ выведено (P4: у S нет предшественника), ЗНАК постулирован (низкая плотность в прошлом — тот же пробел, что ArrowGroundingDescent); потолок голографический. НЕ решает проблему стрелы — изолирует выведенное vs постулированное. Уровень: синтез + честный пробел.
- **Classical counterpart.** Penrose's gravitational-entropy picture (clustering raises entropy; Weyl-curvature low-entropy past), the thermodynamic arrow's dependence on a low-entropy initial condition (Boltzmann/past-hypothesis), and the holographic bound S=A/l_P^2 (Bekenstein-Hawking) — all classical; NEW here is only the E/R/R framing that unifies the gravitational and thermodynamic arrows as ONE distinction-density tendency sharing ONE sign-posit, with the temporal direction derived from P4.
- **Tags.** foundation, arrow-of-time, entropy, gravity, holographic, P4, honest-gap, synthesis, spacetime-descent

**Lemmas (14):**

| name | kind | role |
|---|---|---|
| `stage` | Definition | счёт стадий P4 = временное направление (stage K := K) |
| `entropy` | Definition | энтропия = счёт различений (entropy rho := rho), голографический прокси |
| `rho_cluster` | Definition | кластеризующая траектория (гравитация + низкий старт): rho0 + K |
| `rho_disperse` | Definition | рассеивающая (другая P4-совместимая) траектория: rho0 - K |
| `holo_max` | Definition | конечный голографический/чёрнодырный потолок плотности (= 100, иллюстративная битовая граница) |
| `capped_entropy` | Definition | энтропия, ограниченная потолком: Nat.min (entropy rho) holo_max |
| `arrow_direction_forced` | Theorem | ★ P4: stage K < stage (S K) — временное направление форсировано |
| `entropy_is_distinction_density` | Theorem | энтропия ЕСТЬ счёт различений (Element-отождествление) |
| `falling_increases_entropy` | Theorem | падение к большей плотности (медленнее время) повышает энтропию |
| `clustering_raises_entropy` | Theorem | по кластер-траектории энтропия строго растёт со стадией |
| `sign_not_forced` | Theorem | ★ честное ядро: направление форсировано, но знак нет — кластер растит, рассеяние снижает, обе продвигают стадию |
| `holographic_ceiling` | Theorem | capped_entropy rho <= holo_max (потолок) |
| `collapse_reaches_max` | Theorem | гравитационный коллапс из низкой плотности ДОСТИГАЕТ потолка (чёрная дыра = макс. энтропия) |
| `gravity_entropy_arrow` | Theorem | ★ КАПСТОУН: направление(P4) + падение=рост S + кластер-рост + знак-свободен + потолок + достижение в одной теореме |

**Key lemmas (deep):**

- **`sign_not_forced`** - Честное ядро всего файла и причина, по которой это не оверклейм: P4 даёт строго растущий счёт стадий (stage K < stage (S K)) — это НАПРАВЛЕНИЕ времени; но и кластеризующая (rho0+K, энтропия растёт), и рассеивающая (rho0-K, энтропия падает) траектории одинаково продвигают стадию, значит ЗНАК (растёт энтропия или падает) P4 НЕ фиксирует. Рост энтропии требует низкоплотного гладкого прошлого — ровно тот постулат низкоэнтропийного прошлого, что ArrowGroundingDescent.v изолировал для термострелы. Файл объединяет грав. и термо. стрелы и показывает общий постулат, но честно НЕ выводит термострелу. _(arrow-of-time, honest-gap, sign-posit, P4)_
- **`gravity_entropy_arrow`** - Капстоун-конъюнкция: (1) направление форсировано P4; (2) падение к большей плотности = рост энтропии; (3) по кластер-траектории энтропия растёт со стадией; (4) знак не форсирован (sign_not_forced встроен); (5) голографический потолок; (6) коллапс достигает потолка. Гравитация, стрела и энтропия = ОДНА тенденция к большей плотности различений; направление выведено, знак — постулат низкоплотного прошлого. Унифицирует стрелы, не разрешает их. Чистый синтез нескольких цитируемых файлов на Stdlib-арифметике. _(capstone, synthesis, gravity-entropy, holographic)_

**Uniqueness - score 4 (synthesis+observation).** Объединяет гравитационную и термодинамическую стрелы как ОДНУ тенденцию плотности различений и показывает, что они делят ОДИН постулат (низкоплотное прошлое); направление выведено из P4, знак — нет; голографический потолок достигается коллапсом.
> _Caveat:_ Каждый кирпич классичен (картина Пенроуза грав.-энтропии, постулат низкоэнтропийного прошлого Больцмана, граница Бекенштейна-Хокинга S=A/l_P^2). Ново только E/R/R-унификация + изоляция общего знака-постулата. Честно само-флагирует: 'энтропия=плотность' — Element-прокси, не строгая голограф. граница; holo_max=100 иллюстративен; НЕ решает проблему стрелы. Над-брендинг был бы назвать это 'выводом стрелы времени' — файл этого избегает.

---

## #1883 - `src/foundation/GravityIsTimeGradient.v` - score 3 (new-framing)

**Gravity = the gradient of the rate of time; time-rate = 1/(distinction density), pull = drop of time-rate inward**

- **Topic.** Formalizes the weak-field Element-side gravity<->time link over Q: time_rate(phi)=1/K(phi) with K=1+2phi (replicated from PolarizableVacuumIndex.v); proves rate*density=1, clocks run slower deeper, the Newtonian-potential identity 1-time_rate=2*phi*time_rate, and that the gravitational pull (drop of time-rate going inward) is positive — gravity IS the discrete gradient of the time-rate.
- **Role.** An earlier node of the foundation SPACETIME/GRAVITY-ARROW descent (Step 6-7 of the chain), feeding GravityArrowEntropy.v. Self-contained over Q (Stdlib QArith only; K replicated from PolarizableVacuumIndex.v). Cites CausalSignature/EnergyDeterminesGraph/GravitySymSquareGauge for the upstream chain but imports none.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lqa Setoid
- **E/R/R.** _Elements:_ скорость времени time_rate(phi); плотность различений K=vac_index(phi)=1+2phi; глубина потенциала phi. _Roles:_ time_rate = ход собственных часов (g_00); K = локальная плотность различений (= степень графа); phi = глубина/источник (= ньютонов потенциал GM/r). _Rules:_ time_rate = 1/K; часы медленнее там, где K выше; гравитация (тяга) = градиент (падение) скорости времени; падение = к более медленному времени = к большей плотности различений; m_grav=m_inert (один phi — две роли). _P4:_ ВРЕМЯ (преемство, L5+P4: у S нет предшественника) ПРИМИТИВНЕЕ гравитации (метрики); метрика Sym^2(Roles) уже СОДЕРЖИТ скорость времени как g_00, значит связь = вложенность, не взаимодействие. ПЭ структурен: один источник phi задаёт такт И влечёт падение. Честно: слабое поле, скалярная Element-сторона; 'грав.=кривизна времени' — стандарт, ново — вывод 'скорость времени=1/плотность-различений' + структурный ПЭ. Уровень: новое обрамление / синтез.
- **Classical counterpart.** The weak-field GR statement 'gravity = curvature of TIME' (Newtonian potential Phi=(g_00-1)/2, clocks slow near mass) and the equivalence principle m_grav=m_inert are standard GR; NEW (ToS framing) is the ontological derivation of WHY g_00 varies — g_00 = time-rate = 1/(local distinction density), mass = distinction density — and the equivalence principle as a structural one-field-two-roles fact.
- **Tags.** foundation, gravity, time-rate, weak-field, equivalence-principle, distinction-density, Q-arith, new-framing, spacetime-descent

**Lemmas (12):**

| name | kind | role |
|---|---|---|
| `vac_index` | Definition | локальная плотность различений K = 1 + 2*phi (слабое поле; реплика из PolarizableVacuumIndex.v) |
| `time_rate` | Definition | скорость собственного времени = c_eff = 1/K (такт часов) |
| `grav_potential` | Definition | ньютонова глубина потенциала phi = GM/r (>=0, больше у массы) |
| `grav_pull` | Definition | грав. тяга между ближней и дальней оболочкой = падение скорости времени внутрь (time_rate far - time_rate near) |
| `index_pos` | Lemma | 0 <= phi => 0 < vac_index phi (положительность индекса) |
| `index_increasing` | Lemma | p1 < p2 => vac_index p1 < vac_index p2 (индекс растёт с глубиной) |
| `Qinv_antitone` | Lemma | обратная функция антитонна на положительных: 0<a, a<b => 1/b < 1/a |
| `rate_times_density` | Lemma | ★ rate*density=1: такт часов = ровно 1/(локальная плотность различений) |
| `clock_slower_deeper` | Lemma | ★ глубже в яме (выше phi) часы идут МЕДЛЕННЕЕ (time_rate p2 < time_rate p1) |
| `time_rate_deficit` | Lemma | ньютонов потенциал = дефицит скорости времени: 1 - time_rate = 2*phi*time_rate |
| `grav_pull_positive` | Lemma | ★ грав. тяга > 0 к ближней (глубокой, медленновременной) оболочке — падают к медленному времени |
| `gravity_is_time_gradient` | Theorem | ★ КАПСТОУН: rate=1/density + медленнее глубже + Ньютон=дефицит + падение к медленному + тяга=градиент времени |

**Key lemmas (deep):**

- **`rate_times_density`** - Онтологическое ядро файла: time_rate * vac_index = 1, т.е. такт собственных часов ТОЧНО обратен локальной плотности различений K. Это и есть 'новое содержание', которое ToS-методология добавляет к стандартному слабополевому 'грав.=кривизна времени': не просто g_00 меняется, а ПОЧЕМУ — g_00 = скорость времени = 1/(плотность различений), а масса = плотность различений. Доказывается field-тактикой над Q (field; lra). Честно: тождество тривиально для определения 1/K; ценность — онтологическая интерпретация, не математическая глубина. _(time-rate, distinction-density, ontology, weak-field)_
- **`clock_slower_deeper`** - Слабополевое замедление времени как теорема над Q: глубже (выше phi, ближе к массе) => time_rate p2 < time_rate p1, через антитонность обратной функции (Qinv_antitone) и рост индекса. Это машинно-проверенная форма стандартного факта 'часы у массы идут медленнее', выведенная не из метрики, а из роста плотности различений. Структурный ПЭ виден: тот же phi, что задаёт такт, есть и то, к чему падает содержимое. _(time-dilation, antitone, equivalence-principle)_
- **`grav_pull_positive`** - Связывает гравитацию с градиентом: тяга = time_rate(far) - time_rate(near) > 0, то есть содержимое падает туда, где время медленнее. grav_pull = дискретный градиент скорости времени, и капстоун доказывает grav_pull == time_rate pf - time_rate pn по определению — гравитация ЕСТЬ градиент такта. Element-сторона; role-limit = полная нелинейная тензорная метрика, честно вынесена за скобки. _(gravity-gradient, fall, weak-field)_

**Uniqueness - score 3 (new-framing).** Слабополевое 'гравитация = градиент скорости времени' переосмыслено онтологически: скорость времени = 1/(плотность различений), масса = плотность различений, ПЭ структурен (один phi — две роли); машинно над Q.
> _Caveat:_ 'Гравитация = кривизна времени' (Phi=(g_00-1)/2, замедление часов у массы) и ПЭ m_grav=m_inert — стандартная слабополевая ОТО. Ново только ToS-обрамление (вывод 'скорость времени=1/плотность-различений' + структурный ПЭ). Честно само-флагирует: слабое поле, медленная материя, скалярная Element-сторона; полная нелинейная тензорная ОТО = role-limit, не здесь; над-брендинг был бы выдать это за вывод ОТО.

---

## #1884 - `src/foundation/HierarchyDepthLadder.v` - score 3 (new-framing)

**Tower floor = omniscience rung; floor 0 decidable (Element), floor 1 = LPO, LEM collapses the grading (visible only via P4)**

- **Topic.** Stage 2 of the Process-Hierarchy direction: gives the DEPTH of the ascending role-type tower (Level n) — floor 0 (Level 0=nat) has decidable equality (rung 0, Element); floor 1 (Level 1=nat->bool) decision 'fires or never' is EXACTLY LPO; LEM decides floor 1 (rung collapses classically); LPO_omega->LPO (higher floor strictly stronger). The grading is constructive — visible only without LEM (i.e. via P4).
- **Role.** Part of the foundation PROCESS-HIERARCHY/DETERMINACY work; stage 2 above ProcessHierarchyCore.v (the ascending role-type tower Level n) and over RoleLimitLadder.v (the omniscience rungs LPO/LPO_omega/LEM). Imports both. Establishes the floor<->rung correspondence's lower rungs + grading direction; NOT a full floor_n<->rung_n isomorphism.
- **Counts.** Qed 4 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith Lia; ToS: foundation.ProcessHierarchyCore; ToS: foundation.RoleLimitLadder
- **E/R/R.** _Elements:_ булева g : Level 1 (роль-тип nat->bool); равенство на Level 0 = nat. _Roles:_ этаж = вопрос данной кванторной глубины; рунг = требуемое всеведение (завершённая бесконечность); LEM = оракул-схлоп. _Rules:_ этаж 0 разрешим (рунг 0, Element); этаж 1 = LPO (Sigma^0_1); LEM схлопывает этаж 1; LPO_omega -> LPO (выше строго сильнее). _P4:_ ГЛУБИНА этажа башни = РУНГ всеведения: сколько завершённой бесконечности требует вопрос на этом этаже. Градация КОНСТРУКТИВНА — классически (LEM) этаж 1 решается, рунг СХЛОПЫВАЕТСЯ, глубина плоская; видна лишь без LEM, то есть через P4. Честно: LEM/LPO — Prop-ГИПОТЕЗЫ, не аксиомы (0 аксиом); строятся НИЖНИЕ рунги (0=разрешимо, 1=LPO), полный изоморфизм этаж_n<->рунг_n не строится. Уровень: новое обрамление.
- **Classical counterpart.** The constructive reverse-mathematics fact that 'does a binary sequence ever fire, or never?' (forall n, g n=false vs exists n, g n=true) is exactly LPO (the limited principle of omniscience), and that LEM decides it / classically it collapses, with LPO_omega strictly above LPO — all standard constructive RM (Bishop/Bridges); NEW is only the Element/role-limit 'depth = omniscience rung' framing tying a tower-floor (Level n role-type) to a rung of completed infinity.
- **Tags.** foundation, process-hierarchy, LPO, omniscience, constructive, role-limit, P4, new-framing, determinacy-ascent

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `level0_decidable` | Lemma | этаж 0 (Level 0=nat): равенство РАЗРЕШИМО ({x=y}+{x<>y}) — рунг 0, Element |
| `decide_level1` | Definition | решение на этаже 1 (nat->bool): 'срабатывает или никогда' (exists n, g n=true) \/ (forall n, g n=false) |
| `level1_decision_is_LPO` | Lemma | ★ это РОВНО LPO: decide_level1 <-> LPO (этаж 1 = рунг Sigma^0_1) |
| `lem_decides_level1` | Lemma | градация конструктивна: LEM -> decide_level1 (классически рунг схлопывается) |
| `hierarchy_depth_is_omniscience_grading` | Theorem | ★ КАПСТОУН: этаж 0 разрешим + этаж 1=LPO + LEM схлопывает + LPO_omega->LPO (восходящая градация, видимая лишь через P4) |

**Key lemmas (deep):**

- **`level1_decision_is_LPO`** - Точное ядро соответствия этаж<->рунг: вопрос 'срабатывает ли булева g : Level 1 хоть раз, или никогда' формально СОВПАДАЕТ с LPO. Доказательство тривиально (обе стороны — одно и то же Prop, split; exact H) — и это честно: новизна не в доказательстве, а в ИДЕНТИФИКАЦИИ этажа 1 восходящей роль-типовой башни (ProcessHierarchyCore) с рунгом всеведения Sigma^0_1. Так конкретный этаж процессной иерархии привязан к конкретному рунгу конструктивной reverse math. _(LPO, floor-rung, role-limit, constructive)_
- **`hierarchy_depth_is_omniscience_grading`** - Капстоун-конъюнкция градации: (этаж 0 разрешим, рунг 0/Element) /\ (этаж 1 <-> LPO) /\ (LEM -> decide_level1, классически плоско) /\ (LPO_omega -> LPO, выше строго сильнее, через RoleLimitLadder.lpo_omega_lpo). Честный P4-пункт: градация КОНСТРУКТИВНА — под LEM рунг схлопывается, глубина видна лишь без LEM. Это и значит 'подъём role-limit-стороны виден лишь через P4'. Строятся нижние рунги + направление; полный изоморфизм для всех n НЕ строится (выше LPO_omega — цитата RoleLimitLadder). _(capstone, omniscience-grading, P4, constructive-only)_

**Uniqueness - score 3 (new-framing).** Глубина этажа восходящей роль-типовой башни = рунг всеведения: этаж 0 разрешим (Element), этаж 1 = РОВНО LPO, и градация КОНСТРУКТИВНА (LEM её схлопывает) — видна лишь через P4.
> _Caveat:_ LPO как 'fires-or-never', схлопывание под LEM и LPO_omega>LPO — стандартная конструктивная reverse math (Bishop/Bridges). Ново только обрамление 'этаж башни = рунг всеведения'. Честно само-флагирует: строятся лишь НИЖНИЕ рунги (0,1), ПОЛНОГО изоморфизма этаж_n<->рунг_n нет; LEM/LPO — Prop-гипотезы, не аксиомы (0 аксиом); строгость рунгов (необратимость) — в RoleLimitLadder, не здесь.

---

## #1885 - `src/foundation/LandauerFromP4.v` - score 3 (new-framing)

**Does the Landauer floor reduce to P4? — value <= binarity, unit <= count-proxy; positivity self-corrected from P4 to RECORDING (honest residual)**

- **Topic.** Models a binary distinction (2 branches, 1 committed) and the unchosen branch's fate (retained-inaccessible if permanent, else annihilated=0), with entropy_cost = the inaccessible count; proves the floor value = branches-committed = 1 bit (binarity L2), is positive iff permanent, and that annihilation (the only free option) is ~P4. The header then CORRECTS itself: positivity actually rests on RECORDING (present encodes the fact), not on P4-determinacy.
- **Role.** Part of the foundation GRAVITY-ARROW/thermodynamics descent (Landauer* node); an honest 'reduces to ToS laws vs imported principle' analysis that flags its own irreducible import. Self-contained (Stdlib only); cross-references RecordingVsDeterminacy.v for the correction that splits metaphysical determinacy (P4) from physical recording.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith Lia
- **E/R/R.** _Elements:_ 2 ветви (бинарно, L2); зафиксированная ветвь (1); судьба невыбранной ветви; счёт недоступных различений. _Roles:_ постоянство (P4-флаг permanent) = судьба 'удержана-недоступной'; бинарность = счёт (2-1); энтропия = счёт. _Rules:_ P4 => удержана; бинарность => удержано = 2-1 = 1; энтропия=счёт => cost=1; аннигиляция (=~P4) => 0; cost>0 <=> permanent. _P4:_ ВОПРОС (разобран, не пред-решён): сводится ли пол Ландауэра к P4? Значение(=1) <= бинарность L2; единица <= прокси энтропия=счёт. ИЗНАЧАЛЬНО заявлено: положительность <= P4 (аннигиляция=~P4 бесплатна). КОРРЕКЦИЯ (RecordingVsDeterminacy.v): это ПЕРЕОЦЕНКА — смешаны метафизическая определённость (P4: прошлое — фиксированный факт) и физическая ЗАПИСЬ (настоящее кодирует факт = ландауэровский бит); определённое прошлое может быть НЕ записано. Значит положительность опирается на ЗАПИСЬ (отдельный принцип), НЕ на P4. Уровень: редукция импорта к основанию + честный (само-исправленный) остаток.
- **Classical counterpart.** Landauer's principle (>=k_B ln2 per irreversible bit erasure; floor = 1 bit = log2(2)) is a fundamental result of the physics of information (Landauer 1961; Bennett); NEW is only the E/R/R decomposition of the floor into ToS laws (value <= binarity L2, unit <= entropy=count proxy) and the self-corrected analysis of WHETHER its positivity reduces to P4-permanence — the file itself concludes (via a CORRECTION) that positivity rests on RECORDING, a separate principle, NOT on P4.
- **Tags.** foundation, landauer, information-physics, P4, recording, import-vs-derived, honest-residual, self-correction, new-framing, thermodynamics-descent

**Lemmas (10):**

| name | kind | role |
|---|---|---|
| `branches` | Definition | бинарное различение (L2): ровно 2 ветви (= 2) |
| `committed` | Definition | фиксация актуализирует ровно ОДНУ ветвь (= 1) |
| `retained_inaccessible` | Definition | судьба невыбранной ветви: if permanent then branches-committed else 0 (удержана / аннигилирована) |
| `entropy_cost` | Definition | приращение энтропии = счёт недоступных различений (прокси/единичный мост) |
| `cost_value_from_binarity` | Theorem | ★ значение пола = branches-committed = бинарный '1 бит' (L2) |
| `binary_retains_one_bit` | Theorem | бинарная фиксация удерживает ровно 1 бит (= log2(2)) |
| `annihilation_is_free` | Theorem | аннигиляция (=~P4) стоит 0 (единственный бесплатный вариант) |
| `floor_positive_from_permanence` | Theorem | ★ пол ПОЛОЖИТЕЛЕН для постоянного прошлого (0 < entropy_cost true) — изначально приписано P4, исправлено на ЗАПИСЬ |
| `floor_iff_permanent` | Theorem | ★ cost>0 <=> permanent: пол СУЩЕСТВУЕТ ровно из-за постоянства (аннигиляция = ~P4) |
| `landauer_floor_reduced` | Theorem | ★ КАПСТОУН: значение=L2 + =1 + положителен + free=~P4 + iff-permanent (редукция по модулю прокси R1 и чтения R2) |

**Key lemmas (deep):**

- **`cost_value_from_binarity`** - Прочная, НЕ исправленная часть редукции: значение пола = branches - committed = 2 - 1 = 1 бит — то есть ЗНАЧЕНИЕ пола Ландауэра выводится из бинарности (L2), а не постулируется. Доказывается reflexivity на счётной модели. Это законная декомпозиция: log2(2)=1 = (число ветвей - зафиксированных). Единица (физическая k_B ln2) приходит через прокси энтропия=счёт (R1, не устранён). _(landauer, binarity, L2, value-reduces)_
- **`floor_iff_permanent`** - Технически чистая теорема (cost>0 <=> permanent=true), доказанная разбором булева флага; НО её ИНТЕРПРЕТАЦИЯ само-исправлена в шапке. Изначально: 'пол существует ровно из-за P4, аннигиляция=~P4 бесплатна'. Коррекция (RecordingVsDeterminacy.v): чтение R2 'P4-определённость => ветвь удержана' СМЕШИВАЕТ метафизическую определённость (P4 даёт лишь ФАКТ) с физической записью (настоящее КОДИРУЕТ факт — ландауэровски значимый бит); определённое прошлое может быть стёрто без следа. Значит положительность опирается на ЗАПИСЬ, отдельный принцип, НЕ на P4. Образцовая честность: файл доказывает теорему и тут же ограничивает её философское прочтение. _(landauer, P4, recording, self-correction, honest-residual)_
- **`landauer_floor_reduced`** - Капстоун-редукция: значение=L2-бинарность, =1, положителен, free=~P4, iff-permanent — пол Ландауэра НЕ независимый динамический постулат поверх ToS, а декомпозиция P4(после коррекции: запись)+бинарность+прокси. Честный остаток явно назван: (R1) энтропия=счёт — единичный мост, не устранён; (R2) чтение определённости — исправлено на запись. Уровень — редукция импорта к основанию с честным (само-исправленным) остатком: ЗНАЧЕНИЕ редуцируется надёжно, ПОЛОЖИТЕЛЬНОСТЬ — нет. _(capstone, reduction, import-vs-derived, honest-residual)_

**Uniqueness - score 3 (new-framing).** E/R/R-декомпозиция пола Ландауэра: ЗНАЧЕНИЕ (=1 бит) выводится из бинарности (L2), единица — прокси энтропия=счёт; вопрос о ПОЛОЖИТЕЛЬНОСТИ разобран и САМО-ИСПРАВЛЕН — она опирается на ЗАПИСЬ (отдельный принцип), не на P4.
> _Caveat:_ Принцип Ландауэра (>=k_B ln2/бит) — фундаментальный результат физики информации (Landauer 1961, Bennett), здесь НЕ передоказывается. Ново только декомпозиция в законы ToS. Образцово честно: файл сам ОПРОВЕРГАЕТ свой первоначальный заголовок ('positivity <= P4'), отделяя определённость (P4=факт) от записи (кодирование=бит) — значит Ландауэр НЕ редуцируется к P4. Над-брендинг ('пол Ландауэра выведен из P4') файлом явно снят коррекцией; примитивность чтения R2 vs Ландауэр оставлена ОТКРЫТОЙ.

---

## #1886 - `src/foundation/PowersetRoleType.v` - score 3 (new-framing)

**Powerset object rolls back to the role-type N->bool; finite |P|=2^n is Element-free, Cantor diagonal is the role-limit core — completed P(N) is a ZFC artifact**

- **Topic.** Rolls back the 'wall' of completed P(N) (Part X): in 'P(N)' two things are conflated — (a) the subset OPERATION/role = predicate nat->bool (a process of membership decisions) and (b) the completed COLLECTION of all predicates as a finished totality; the infinity sits ONLY in (b), which is never needed. Element side is free (finite powerset = exactly 2^n, powerset_card), and the uncountability core needs no completed object (Cantor diagonal cantor_bool_seq).
- **Role.** Part of the foundation FORMER-WALLS / Process-Hierarchy work (Part X set-theory-without-AC descent): a 'former walls are ZFC-packaging artifacts' node, companion to RoleToSUNGrounding / FormerWalls files. Self-contained (Stdlib only); reframes Cantor's P(N) as a role-type rather than importing settheory machinery.
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith Lia List Bool
- **E/R/R.** _Elements:_ конечные подмножества (powerset l, 2^n штук, список); булевы последовательности nat->bool. _Roles:_ подмножество = роль-предикат-процесс (решения о принадлежности); 'степень' = роль-тип nat->bool = пространство процессов уровнем выше. _Rules:_ P1 (роль-тип на уровень выше N, не Element того же уровня); диагональ (нет сюръекции nat -> (nat->bool)). _P4:_ ОТКАТ стены (метод P4): завершённый P(N) сливает ОПЕРАЦИЮ 'подмножество' (роль-тип nat->bool, процесс) и завершённый СБОР всех предикатов в готовую тотальность. Бесконечность сидит ТОЛЬКО в завершённом сборе (b), и (b) нигде не нужен — всё содержание про роль-тип. Element-сторона свободна (2^n вычислимо), ядро несчётности свободно (диагональ). Завершённый P(N) как Element = артефакт ZFC-упаковки, НЕ граница нашей системы. Уровень: новое обрамление.
- **Classical counterpart.** Cantor's theorem (no surjection nat -> (nat->bool); P(N) uncountable) and the finite identity \|P(S)\|=2^\|S\| are classical set theory; NEW is only the P4 'wall-rollback' framing — splitting the completed P(N) into (a) the subset OPERATION = role-type nat->bool and (b) the completed COLLECTION, locating ALL the infinity in (b) and showing (b) is never needed (a ZFC-packaging artifact, not a boundary of ToS).
- **Tags.** foundation, powerset, cantor, diagonal, role-type, former-walls, no-AC, P4, uncountable, new-framing, settheory-descent

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `powerset` | Fixpoint | конечный степенной объект как СПИСОК списков (nil=>[[]]; x::xs => ps ++ map (cons x) ps) — без завершённой бесконечности |
| `powerset_card` | Lemma | ★ Element-сторона: length (powerset l) = 2 ^ length l (ровно 2^n подмножеств, вычислимо) |
| `powerset_3_has_8` | Example | length (powerset [1;2;3]) = 8 (конкретная проверка reflexivity) |
| `cantor_bool_seq` | Theorem | ★ ядро 'P(N) несчётно' БЕЗ завершённого объекта: для всякого f:nat->(nat->bool) есть g с forall n, g<>f n (диагональ) |

**Key lemmas (deep):**

- **`cantor_bool_seq`** - Ядро 'несчётности P(N)' извлечённое БЕЗ завершённого объекта: для любой нумерации f:nat->(nat->bool) диагональ g=fun n=>negb(f n n) отличается от каждого f n — нет сюръекции nat->(nat->bool). Это та же negb-диагональ, что движет halting/Cantor по всему репо (см. cs/BoundaryDecidability one_boundary_three_faces). Тезис файла: именно ЭТО ZFC паковал в завершённый несчётный P(N) как Element; но содержание — про роль-тип (пространство процессов nat->bool), завершённый сбор не нужен. Честно: сама теорема Кантора классична; ново обрамление 'P(N) = роль-тип, не завершённый Element'. _(diagonal, cantor, role-limit, uncountable)_
- **`powerset_card`** - Element-сторона стены, свободная и вычислимая: конечный powerset (как список списков) имеет длину ровно 2^n. Доказывается индукцией с length_app/length_map. Показывает, что ОПЕРАЦИЯ взятия подмножеств финитна и точна на конечных входах; завершённая бесконечность появляется ТОЛЬКО при попытке собрать все nat->bool в готовую тотальность (b) — а это нигде не нужно. Контраст с cantor_bool_seq: конечно => Element/2^n, бесконечный роль-тип => диагональ/role-limit. _(powerset, finite, element-side, 2^n)_

**Uniqueness - score 3 (new-framing).** Завершённый P(N) откатывается к роль-типу nat->bool: ОПЕРАЦИЯ-подмножество (предикат-процесс) и ядро несчётности (диагональ) свободны и не требуют завершённого объекта; бесконечность сидит лишь в готовом СБОРЕ всех предикатов, который нигде не нужен — артефакт ZFC-упаковки.
> _Caveat:_ Теорема Кантора (нет сюръекции nat->(nat->bool)) и |P(S)|=2^|S| — классическая теория множеств; передоказаны 0-аксиомной диагональю/индукцией, но содержание известно. Ново только P4-обрамление 'P(N) = роль-тип, не стена-Element'. Та же negb-диагональ переиспользована из cs/uncountability вертикали; это инстанс единой границы, НЕ новая теорема.

---

## #1887 - `src/foundation/ProcessHierarchyCore.v` - score 3 (new-framing)

**Process-hierarchy core: the role-limit side as an ordinal-indexed generative ascent, not a wall**

- **Topic.** Builds an ascending cumulative tower of role-types (Level 0 = nat, Level (S k) = predicates over Level k), proves a Cantor diagonal at EVERY storey (strict growth), no maximal storey, and indexes the tower height by the ordinal-process omega = OLim, whose closure is role-limit (unbounded).
- **Role.** Stage 1 (core) of the 'process hierarchy' direction. Imports foundation/Ordinal (Ord, omega, OLim, nat_to_ord). Reused by the later stages (DeterminacyAscent, WqoProcessDecidable) and the capstone ProcessHierarchySynthesis.
- **Counts.** Qed 5 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith Lia Bool; ToS: foundation.Ordinal
- **E/R/R.** _Elements:_ этажи-роль-типы Level n (Level 0 = nat, Level (S k) = Level k -> bool), каждый конечно-конструируем на стадии; поток высоты tower_height_flow : nat -> nat. _Roles:_ Level n = роль-тип (пространство процессов-решений) над этажом n-1; высота башни = ординал-процесс omega; диагональ negb = правило подъёма на следующий этаж. _Rules:_ cantor_level: нет сюръекции Level n -> Level (S n) (строгий подъём); no_maximal_level: над любым n есть строго больший (нет вершины); tower_height_unbounded: высота неограниченна => замыкание role-limit. _P4:_ башня потенциальна: каждый этаж конечно-конструируем (Element-сторона), но omega-замыкание НЕ есть завершённый Element-объект — достижимо лишь как процесс; завершённой иерархии-объекта (V_omega, борелевская башня) не строим (ZFC-упаковка).
- **Classical counterpart.** Cantor's theorem (no surjection X -> 2^X) applied stage-by-stage to the cumulative type tower Level 0 = nat, Level (S k) = Level k -> bool; the classical analogue is the cumulative hierarchy / V_omega and the iterated-powerset Borel/projective ladder. NEW is only the ToS framing of that ladder as a GENERATIVE ordinal-process ascent (omega = OLim), not a completed object.
- **Tags.** diagonal, cantor, ordinal-process, role-limit, tower, P4, new-framing, no-AC

**Lemmas (8):**

| name | kind | role |
|---|---|---|
| `Level` | Fixpoint | кумулятивная башня роль-типов: Level 0 = nat, Level (S k) = Level k -> bool |
| `cantor_level` | Theorem | ★ Кантор на каждом этаже: нет сюръекции Level n -> Level (S n) (диагональ negb (f x x)) |
| `no_maximal_level` | Theorem | ★ нет максимального этажа: над любым n есть строго больший m=S n, не накрываемый (порождающность) |
| `level_index` | Definition | индекс высоты этажа n как ординал: nat_to_ord n |
| `tower_height_is_limit_process` | Theorem | высота башни = omega = OLim level_index (индекс — ординал-процесс, не число) |
| `tower_height_flow` | Definition | поток высоты tower_height_flow n := n (монотонный убегающий) |
| `tower_height_unbounded` | Theorem | высота неограниченна => по дихотомии InterLevelCalculus замыкание = role-limit |
| `process_hierarchy_is_generative_ascent` | Theorem | ★ капстоун ядра: строгий подъём /\ нет вершины /\ индекс = omega-процесс /\ незамкнуто (role-limit) |

**Key lemmas (deep):**

- **`cantor_level`** - Канторова диагональ, поднятая на КАЖДЫЙ этаж кумулятивной башни роль-типов: для любого f : Level n -> Level (S n) свидетель (fun x => negb (f x x)) не накрывается => башня строго растёт этаж за этажом. При n=0 это в точности ядро несчётности ('нет перечислителя nat -> (nat -> bool)'). Содержательно тождественна одной негбе-диагонали из cs/BoundaryDecidability — здесь она инстанцирована поэтажно, давая строгий рост, а не отдельный новый факт. _(diagonal, cantor, role-limit, tower)_
- **`process_hierarchy_is_generative_ascent`** - Капстоун ядра: role-limit-сторона границы финитизации НЕ плоскость и НЕ бинарная стена, а ОРДИНАЛ-ИНДЕКСИРОВАННЫЙ ПОРОЖДАЮЩИЙ подъём — строгий рост (Кантор поэтажно) + отсутствие вершины + индекс omega=OLim (процесс, не завершённое число) + неограниченность (замыкание role-limit). Уровень — new-framing: каждый кирпич (Кантор, omega) классичен; ново обрамление 'иерархия = процесс' как теоретико-множественный аналог R=Коши, Qbar=башня, многообразие=процесс. Сам omega=OLim level_index держится reflexivity (тавтологичен по построению OLim). _(synthesis, generative, ordinal-process, framing)_

**Uniqueness - score 3 (new-framing).** Role-limit-сторона границы финитизации переосмыслена как ординал-процесс-подъём роль-типов: кумулятивная башня Level n со строгим поэтажным ростом (Кантор), без вершины, индексированная omega=OLim, с role-limit-замыканием по неограниченности — 0 аксиом.
> _Caveat:_ Каждый компонент классичен: Кантор поэтажно, кумулятивная башня = V_omega/итерированный степенной набор, omega — стандартный ординал. Ново только E/R/R-обрамление 'иерархия=процесс' и поэтажная диагональ; omega=OLim держится reflexivity (тавтология построения). ПОЛНЫЕ борелевская/проективная башни НЕ строятся (горизонт consistency-strength, явно вне scope).

---

## #1888 - `src/foundation/ProcessHierarchySynthesis.v` - score 4 (synthesis+observation)

**Process-hierarchy synthesis: one omega-index + one recurring LPO rung stitch the stages; flagship 'hierarchy = process'**

- **Topic.** Stage 5 (synthesis) of the process-hierarchy direction. Proves the two stitching threads: (1) the role-type tower (st.1) and the determinacy ascent (st.3) are indexed by the SAME ordinal-process omega=OLim; (2) the storey-1 decision and 'will I ever win' open determinacy are the SAME LPO rung (level1_equiv_open_determinacy), and upgrades two 'former walls' (Kruskal min-bad-sequence, Borel tower) NotYetBuilt -> PartiallyReached.
- **Role.** Capstone of the direction; pure synthesis citing stages 1-4. Imports Ordinal, ProcessHierarchyCore, HierarchyDepthLadder, DeterminacyAscent, WqoProcessDecidable, RoleLimitLadder, FormerWallsLedger, FiniteGameDeterminacy, settheory.KruskalTree. Adds no new high theorems; consolidates the proven stages.
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith Lia Bool; ToS: foundation.Ordinal; foundation.ProcessHierarchyCore; foundation.HierarchyDepthLadder; foundation.DeterminacyAscent; foundation.WqoProcessDecidable; foundation.RoleLimitLadder; foundation.FormerWallsLedger; foundation.FiniteGameDeterminacy; settheory.KruskalTree
- **E/R/R.** _Elements:_ ступени 1-4 как доказанные факты (башня, глубина, детерминированность, wqo); индекс omega; рунг LPO; вердикты реестра 'бывших стен'. _Roles:_ omega = OLim — общий индекс-подъём (башня ст.1 = детерминированность ст.3); LPO = общий рунг всеведения (этаж 1 = открытая детерминированность); status w = роль-вердикт стены. _Rules:_ единый omega-индекс (tower_height_is_limit_process = determinacy_ascent_height_is_omega); level1 <-> открытая детерминированность (оба = LPO); 0-ax база (mover_wins обратной индукцией, wqo_nat_le фундир. спуском); реестр: две стены PartiallyReached, запрет только WCompletedInfinity. _P4:_ иерархия = ОДИН процесс-подъём (не завершённый объект и не бинарная стена); аксиома LPO/classic локализована ВЫШЕ 0-ax базы (финит->инфинит), а не как стена; полные Крускал/Борель = горизонт-подъём (consistency-strength); единственный подлинный P4-запрет — завершённая актуальная бесконечность.
- **Classical counterpart.** Stitches together the iterated-powerset hierarchy (Cantor), finite/infinite game determinacy (the Borel-determinacy ladder, Martin), Kruskal/wqo (nat well-quasi-order), and the LPO omniscience principle of constructive analysis. All four classical; NEW is the OBSERVATION that the type-tower depth (stage 1) and the determinacy ascent (stage 3) share ONE ordinal index omega=OLim and ONE recurring LPO rung (level-1 decision <-> open determinacy).
- **Tags.** synthesis, capstone, LPO, ordinal-process, determinacy, wqo, former-walls, flagship, no-AC, P4

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `level1_equiv_open_determinacy` | Corollary | ★ нить 2: decide_level1 <-> (forall gp, eventual_decided gp) — этаж 1 башни = открытая детерминированность (оба = LPO) |
| `walls_upgraded_by_direction` | Theorem | две 'бывшие стены' (WMinimalBadSequence, WBorelTower) переведены в PartiallyReached |
| `process_hierarchy_synthesis` | Theorem | ★ капстоун: единый omega-индекс (ст.1=ст.3) + порождающность + рунг LPO + LEM-схлопывание + 0-ax база (finite_game_determined, wqo_nat_le) + реестр стен |

**Key lemmas (deep):**

- **`level1_equiv_open_determinacy`** - Содержательная нить синтеза: решение этажа 1 башни роль-типов (decide_level1, ст.2) и открытая детерминированность 'выиграет ли I когда-нибудь' (ст.3) ЭКВИВАЛЕНТНЫ — обе суть один и тот же рунг всеведения LPO. Доказательство — двусторонний перенос через level1_decision_is_LPO и eventual_decided_is_LPO (цитата из ступеней). Это genuine placement/унификация: глубина иерархии и подъём детерминированности — одна лестница рунгов, а не два независимых факта. _(LPO, equivalence, stitching, omniscience)_
- **`process_hierarchy_synthesis`** - Гранд-капстоун направления: собирает в одну теорему (a) общий ординал-индекс omega=OLim башни (ст.1) и детерминированности (ст.3); (b) порождающность (нет максимального этажа); (c) два LPO-эквивалента; (d) LEM-схлопывание обоих; (e) 0-ax базу нижних рунгов (конечная детерминированность обратной индукцией finite_game_determined + nat-wqo фундированным спуском wqo_nat_le); (f) реестр: две стены PartiallyReached, запрет только на завершённую бесконечность. Чистая консолидация — ценность в унификации (флагман 'иерархия=процесс'), НЕ в новых теоремах. Каждый exact ссылается на доказанную ступень. _(capstone, synthesis, flagship, ordinal-process, no-AC)_

**Uniqueness - score 4 (synthesis+observation).** Сшивает ступени процессной иерархии двумя нитями: ЕДИНЫЙ ординал-индекс omega=OLim (башня ст.1 = детерминированность ст.3) и ОДИН повторяющийся рунг LPO (этаж 1 <-> открытая детерминированность), с 0-ax базой нижних рунгов и обновлённым реестром 'бывших стен' — флагман 'иерархия=процесс'.
> _Caveat:_ Чистая консолидация: 0 новых 'высоких' теорем, всё цитирует ступени 1-4. Все кирпичи классичны (Кантор, детерминированность Мартина, Крускал/wqo, LPO). ПОЛНЫЕ Крускал/Борель НЕ доказаны (горизонт consistency-strength). LEM/LPO здесь — Prop-гипотезы, не аксиомы файла. Ценность — унификация/placement, не результат.

---

## #1889 - `src/foundation/RecordingFromP4.v` - score 3 (new-framing)

**Recording reduces to P4-as-append-only: the strong reading makes recording the content of irreversibility**

- **Topic.** Models the actual as an append-only list of made distinctions (actualize = append, never remove). Proves the past is a verbatim prefix (conserved/recorded), the oldest entry stays at the head, every step is an append, and a step that edits a past entry is NOT an append = un-actualization = a P4-violation. CORRECTS RecordingIsBedrock.v.
- **Role.** Part of the spacetime/gravity-arrow descent (Recording* / Arrow* / Landauer* honesty thread). Self-contained (Stdlib only). Forward-fix that overturns the sibling RecordingIsBedrock.v's 'bedrock' verdict by adopting the strong append-only reading of P4.
- **Counts.** Qed 5 / Admitted 0 / axioms 0
- **Imports.** Stdlib: List Arith Lia
- **E/R/R.** _Elements:_ актуальное = список сделанных различий (содержание, list bool); добавляемый выбор choice : bool. _Roles:_ P4-актуализация = append (необратимое накопление); прошлое = сохранённый префикс; запись = прошлое читаемо из настоящего (hd_error даёт древнейшее). _Rules:_ actualize a c := a ++ [c] (только добавление, без удаления); => прошлое — дословный префикс настоящего (записано); забывание (перезапись/изменение прошлой записи) НЕ является append = раз-актуализация (~P4). _P4:_ сильное чтение P4 'актуализированное остаётся актуализированным, прошлое фиксировано' => запись ПОРОЖДАЕТСЯ необратимостью, она НЕ отдельный бедрок, а содержание P4. ОСТАТОК: сильное чтение обогащает голый Level=счётчик до накопления содержания; прокси энтропия=счёт сохраняется.
- **Classical counterpart.** The append-only / monotone-prefix model of an immutable log (the past is a verbatim prefix of the present) is elementary list algebra; the physical analogue is conservation of information under micro-reversibility (unitarity). NEW is only the ToS argument that the STRONG (append-only) reading of P4 makes RECORDING the CONTENT of irreversibility, correcting the earlier 'bedrock' verdict.
- **Tags.** P4, append-only, recording, arrow-of-time, correction, new-framing, spacetime-gravity

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `actual` | Definition | актуальное = list bool (накапливаемый список сделанных выборов, сильное чтение) |
| `actualize` | Definition | P4-актуализация = append выбранной ветви: a ++ [choice] (никогда не удаляет) |
| `actualize_conserves_past` | Theorem | ★ прошлое = дословный префикс настоящего: exists s, actualize a c = a ++ s (записано) |
| `actualize_keeps_oldest` | Theorem | древнейшее различие остаётся в голове: hd_error (actualize a c) = hd_error a (a<>[]) |
| `forgetting_not_actualization` | Theorem | ★ перезапись прошлого не есть append: ~ exists s, [false] = [true] ++ s (=~P4) |
| `actualize_only_appends` | Theorem | всякая актуализация — только добавление вперёд: actualize a c = a ++ [c] |
| `recording_from_p4` | Theorem | ★ капстоун: запись редуцируется к P4-как-append (сохранение+древнейшее+append+забывание=~P4) |

**Key lemmas (deep):**

- **`recording_from_p4`** - Капстоун-коррекция: под сильным (append-only) чтением P4 ('содержание сделанного различия остаётся; прошлое фиксировано') запись = СОДЕРЖАНИЕ необратимости, а не отдельный импорт-бедрок. Объединяет: прошлое — дословный префикс (записано); древнейшее не перезаписывается; всякий шаг — append; шаг, меняющий прошлую запись, НЕ append = раз-актуализация = нарушение P4. Это прямо опровергает вердикт RecordingIsBedrock.v. Сами доказательства тривиальны (list-алгебра, discriminate/reflexivity); содержательно ново — философский аргумент 'append-only = правильное чтение P4', а не математика. _(P4, append-only, recording, correction, arrow-of-time)_
- **`forgetting_not_actualization`** - Несущий разрез аргумента: [false] недостижимо добавлением к [true] (discriminate) => 'забывчивый' шаг, изменяющий прошлое, не является P4-актуализацией. Под сильным чтением это превращает стирание из P4-валидного процесса (как в RecordingIsBedrock) в P4-нарушение — именно эта переинтерпретация и убирает 'бедрок'. Математически — одна строка; вес несёт обрамление. _(P4, un-actualization, discriminate)_

**Uniqueness - score 3 (new-framing).** Под сильным (append-only) чтением P4 запись ПОРОЖДАЕТСЯ необратимостью (прошлое = дословный префикс настоящего), а не импортируется как бедрок; забывание = раз-актуализация = нарушение P4 — коррекция прошлого вывода, 0 аксиом.
> _Caveat:_ Математика тривиальна: append/префикс — элементарная list-алгебра, доказательства = discriminate/reflexivity. Новое — философское ОБРАМЛЕНИЕ (выбор сильного чтения P4), не теорема. ЧЕСТНЫЙ ОСТАТОК (в самом файле): сильное чтение БОГАЧЕ голого Level=счётчик (требует обогащения до накопления содержания); физическая запись классически = унитарность/микрообратимость; прокси энтропия=счёт остаётся отдельным мостом. Прямо противоречит RecordingIsBedrock.v — пара 'тезис/коррекция'.

---

## #1890 - `src/foundation/RecordingIsBedrock.v` - score 3 (new-framing)

**Recording is bedrock relative to ToS (weak count-only reading) — later CORRECTED by RecordingFromP4.v**

- **Topic.** Argues that recording (the present encodes the determinate past choices) is INDEPENDENT of P4 / P3 / L2 / P1: a recording process (state = full history) and a forgetful process (state = stage count = the P3/Level depth counter) share the same monotone P4 proper-time, yet only recording distinguishes histories. Concludes recording is the honest irreducible floor of the arrow analysis.
- **Role.** Part of the spacetime/gravity-arrow descent; the 'bedrock' floor located under the recording principle. Self-contained (Stdlib only). EXPLICITLY corrected by RecordingFromP4.v: the verdict holds only against the WEAK count-only reading of P4; under the strong append-only reading recording reduces to P4.
- **Counts.** Qed 4 / Admitted 0 / axioms 0
- **Imports.** Stdlib: List Arith Lia
- **E/R/R.** _Elements:_ история выборов (list bool); состояние настоящего (запись = вся история; забывчивое = счёт стадий). _Roles:_ запись = настоящее кодирует выборы; забывчивое = только счёт (P3/Level-глубина); P4 = монотонный счёт стадий (собственное время proper_time). _Rules:_ P4 => счёт монотонен; ОБА процесса (recording_state/forgetful_state) дают одинаковый proper_time (both_p4_valid); запись различает истории, забывчивое (счёт) их схлопывает => P4 (и P3-счёт) НЕ влекут запись. _P4:_ ЧЕСТНЫЙ ПОЛ (под слабым чтением): запись НЕЗАВИСИМА от P4 — оба процесса P4-валидны; запись = сохранение информации, принцип ВНЕ P1-P4+L2 (в физике — унитарность, которой у ToS нет). КОРРЕКЦИЯ (в файле): под сильным append-only чтением стирание = раз-актуализация = ~P4, и вердикт-бедрок падает (см. RecordingFromP4).
- **Classical counterpart.** An independence/no-reduction argument: recording = information conservation (traces persist), which in physics follows from micro-reversibility (unitarity), NOT from coarse macro-dynamics. NEW is only the ToS framing showing a recording process and a forgetful (count-only) process share the same monotone P4 stage-count, so (under the WEAK reading) P4 does not entail recording.
- **Tags.** independence, bedrock, P4, recording, arrow-of-time, no-reduction, superseded, new-framing, spacetime-gravity
- **Notes.** STATUS header says '5 Qed' but ACTUAL = 4 Qed (both_p4_valid, recording_distinguishes, forgetful_collapses, recording_is_bedrock). Header drift — recorded in manifest 'drift'. The file's central 'bedrock' verdict is explicitly OVERTURNED by the sibling RecordingFromP4.v (#1889) under the strong append-only reading of P4; an in-file CORRECTION block flags this. Catalogued as a thesis/correction pair.

**Lemmas (8):**

| name | kind | role |
|---|---|---|
| `history` | Definition | история = последовательность бинарных выборов (list bool) |
| `proper_time` | Definition | P4-счёт стадий = собственное время = length h |
| `recording_state` | Definition | процесс ЗАПИСИ: состояние = вся история (выборы закодированы) |
| `forgetful_state` | Definition | ЗАБЫВЧИВЫЙ процесс: состояние = только счёт = length (P3/Level-глубина, выборы потеряны) |
| `both_p4_valid` | Theorem | ★ оба процесса дают одинаковый P4 proper-time => оба P4-валидны |
| `recording_distinguishes` | Theorem | запись различает истории: recording_state [true] <> recording_state [false] |
| `forgetful_collapses` | Theorem | счёт схлопывает разные выборы: forgetful_state [true] = forgetful_state [false] /\ [true]<>[false] |
| `recording_is_bedrock` | Theorem | ★ капстоун: оба P4-валидны + запись различает + счёт схлопывает => P4 НЕ влечёт запись (бедрок) |

**Key lemmas (deep):**

- **`recording_is_bedrock`** - Капстоун независимости: процесс записи (state=история) и забывчивый (state=счёт=P3/Level-глубина) делят ОДИН P4 proper-time (both_p4_valid), но только запись различает истории => P4 совместим с обоими мирами => P4 НЕ влечёт запись, и P3-счёт тоже. Вывод: запись = сохранение информации, импорт ВНЕ P1-P4+L2 (в физике = унитарность). ВАЖНО: вердикт держится лишь под СЛАБЫМ счётным чтением P4; сам файл несёт встроенную КОРРЕКЦИЮ (RecordingFromP4): под сильным append-only чтением forgetful-шаг = раз-актуализация = ~P4, и 'бедрок' падает. Математика тривиальна (length/discriminate); ценность — точная локализация (потом пересмотренного) импорта. _(independence, bedrock, P4, no-reduction, superseded)_
- **`both_p4_valid`** - Несущая лемма независимости: length (recording_state h) = proper_time h И forgetful_state h = proper_time h — оба процесса согласованы по P4-времени, поэтому P4-монотонность не различает их. Именно это равенство — мишень последующей коррекции: оно опирается на ЧТЕНИЕ P4 как 'только счёт', которое RecordingFromP4 объявляет некогерентным (отделяет событие от его содержания). _(P4, proper-time, reflexivity)_

**Uniqueness - score 3 (new-framing).** Локализует запись (сохранение информации) как импорт, независимый от P4/P3/L2/P1: запись и забывчивый процесс делят один монотонный P4-счёт, но различает истории лишь запись => P4 не влечёт запись (бедрок под слабым чтением), 0 аксиом.
> _Caveat:_ Математика тривиальна (length, discriminate, reflexivity). Аргумент-независимость классичен (запись=унитарность/микрообратимость, не из крупной динамики). ГЛАВНЫЙ КАВЕАТ: вердикт-бедрок СНЯТ самим репо — RecordingFromP4.v показывает, что под сильным append-only чтением P4 запись редуцируется к P4; файл несёт встроенную пометку CORRECTION. Это 'тезис', пересмотренный своей коррекцией; STATUS-заголовок завышен.

---

## #1891 - `src/foundation/RecordingVsDeterminacy.v` - score 3 (new-framing)

**Landauer = recording, not P4: determinacy does not entail a record, so the cost floor's positivity is a separate import**

- **Topic.** Separates METAPHYSICAL DETERMINACY (P4: the past choice is a definite fact) from PHYSICAL RECORDING (the present encodes it). Proves P4 gives determinacy but not recording (a determinate choice can be erased = None, cost 0), and positive entropy cost requires a record. Refutes the R2 'reduction' of LandauerFromP4.v: recording is the genuine separate input.
- **Role.** Part of the spacetime/gravity-arrow descent (Landauer/entropy honesty). Self-contained (Stdlib only). The forward-fix that CORRECTS LandauerFromP4.v's 'reduction modulo R2', pinning the arrow's irreducible imports to RECORDING + the entropy=count bridge.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith Lia
- **E/R/R.** _Elements:_ прошлый выбор (определённый bool = факт); запись в настоящем (option bool = Some закодировано / None стёрто). _Roles:_ определённость determinate = выбор есть определённый факт (P4); запись recorded = настоящее кодирует его (Ландауэр); entropy_cost = стоимость, несомая записью. _Rules:_ P4 => determinate (всякий выбор определён); определённость НЕ влечёт запись (определённый выбор может быть None); 0 < entropy_cost r -> recorded r (стоимость <= запись, не определённость). _P4:_ анализ R2 ОПРОВЕРГАЕТ редукцию: P4 даёт ФАКТ, не физическую ЗАПИСЬ; определённое-но-незаписанное прошлое стоит 0. Положительность ландауэровского пола поставляет ЗАПИСЬ (информация физически закодирована — отдельный принцип, классически из микрообратимости), НЕ P4. Ландауэр НЕ сводится к P4 — он ЕСТЬ принцип записи.
- **Classical counterpart.** Landauer's principle (erasing/recording a bit costs >= kT ln2) and the distinction between a metaphysically determinate past and a physically encoded record. Both classical (Landauer 1961; the record/no-record distinction is standard in the physics of information). NEW is only the ToS refutation that R2 (the prior 'Landauer reduces to P4-determinacy' reading) conflated determinacy with recording.
- **Tags.** landauer, recording, determinacy, P4, refutation, arrow-of-time, entropy, new-framing, spacetime-gravity

**Lemmas (9):**

| name | kind | role |
|---|---|---|
| `determinate` | Definition | метафизическая определённость (P4): c = true \/ c = false |
| `recorded` | Definition | физическая запись: exists b, r = Some b (Some=закодировано, None=стёрто) |
| `entropy_cost` | Definition | ландауэровская стоимость записи: Some => 1, None => 0 |
| `p4_gives_determinacy` | Theorem | P4: всякий прошлый выбор — определённый факт (forall c, determinate c) |
| `determinacy_not_recording` | Theorem | ★ определённость НЕ влечёт запись: exists c r, determinate c /\ ~ recorded r |
| `unrecorded_is_free` | Theorem | незаписанное прошлое бесплатно: entropy_cost None = 0 |
| `cost_requires_recording` | Theorem | ★ положительная стоимость требует записи: 0 < entropy_cost r -> recorded r |
| `determinacy_does_not_force_cost` | Theorem | определённое-но-незаписанное прошлое стоит 0 (P4 один не форсирует пол) |
| `landauer_is_recording_not_p4` | Theorem | ★ капстоун: P4 даёт факт, не запись; стоимость несёт запись => Ландауэр = запись, не P4 (R2 = конфляция) |

**Key lemmas (deep):**

- **`landauer_is_recording_not_p4`** - Капстоун-опровержение: разделив P4-определённость (есть факт, что выбран A) и физическую запись (настоящее кодирует A), теорема показывает (a) всякий выбор определён; (b) но определённый выбор может быть незаписан (None); (c) незаписанное стоит 0; (d) положительная стоимость требует записи; (e) => определённое-но-незаписанное прошлое стоит 0 — P4 один НЕ форсирует пол. Вывод: Ландауэр = принцип записи, НЕ редуцируется к P4; корректирует LandauerFromP4.v (R2 был настоящий импорт, не выводимое чтение). Несущий импорт стрелы заострён до RECORDING + мост энтропия=счёт. _(landauer, recording, P4, refutation, arrow-of-time)_
- **`cost_requires_recording`** - Несущий разрез: положительная энтропийная стоимость требует физической записи (Some), а не метафизической определённости — для None стоимость 0 (lia опровергает 0<0). Именно это отделяет стоимость от факта и убивает редукцию R2: метафизическая определённость даётся P4 даром, но не несёт стоимости. Математика тривиальна (case-split + lia); вес несёт концептуальное разделение determinate vs recorded. _(landauer, cost, case-split)_

**Uniqueness - score 3 (new-framing).** Разделяет метафизическую определённость (P4) и физическую запись (Ландауэр) и доказывает, что стоимость несёт ЗАПИСЬ, не определённость => положительность ландауэровского пола — отдельный импорт (запись), не P4; коррекция прошлой редукции, 0 аксиом.
> _Caveat:_ Математика тривиальна (option-case-split, lia, discriminate). Принцип Ландауэра и различие факт/запись классичны (Ландауэр 1961; физика информации). Новое — концептуальное РАЗДЕЛЕНИЕ determinate vs recorded и КОРРЕКЦИЯ прошлого вывода (R2 = настоящий импорт), не теорема. Запись классически = унитарность/микрообратимость; мост энтропия=счёт остаётся отдельным честным импортом.

---

## #1892 - `src/foundation/RoleToSUNGrounding.v` - score 4 (synthesis+observation)

**role→SU(N) re-grounded: superposition = potentiality (L2 preserved), Born exponent 2 = unique rotation invariant**

- **Topic.** Over amplitude pairs (Q×Q) on two roles, treats superposition as the POTENTIAL mode (role-limit), proves L2 (non-contradiction) holds on the actualized level, derives unitarity/det=1 as preservation of a distinguishability form, and shows the Born exponent 2 is forced because a rotation breaks the 1-norm but preserves the 2-norm.
- **Role.** foundation-chain attempt to reduce the SU(N) requirements of QM to ToS's own footing. Self-contained (only QArith); cites BornRuleDescent for the full p=2 descent. A 'how far does distinction reach into SU(N)' ledger file, not a hub.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lqa
- **E/R/R.** _Elements:_ амплитудные пары (Q*Q) над 2 ролями; актуализованные полюса (Element); форма различимости dist_form. _Roles:_ актуализованный полюс = Element; суперпозиция = ПОТЕНЦИАЛ (role-limit), не «оба»; измерение = актуализация одного полюса (L4-подобный шаг). _Rules:_ унитарность = сохранять dist_form (DERIVED); L2 держится на АКТУАЛИЗОВАННОМ уровне; интерференция = знаковые веса сокращаются (1+(−1)=0); вращение ломает 1-норму, хранит 2-норму ⟹ показатель p=2. _P4:_ прошлое «суперпозиция = ¬L2» — категориальная ошибка (потенциал как актуальное). Суперпозиция = потенциальность = role-limit (теория это УЖЕ имеет); анти-L2-постулата нет. Единственный вход — сторона role-limit (непрерывность/потенциальность); показатель Борна 2 ВЫВЕДЕН.
- **Classical counterpart.** The derivation of unitarity / det=1 from preservation of an inner product, and the \|·\|² Born weight as the unique quadratic (rotation-invariant) form, are standard QM/representation-theory facts; the dissolution of 'superposition = contradiction' as potentiality-vs-actuality is a known philosophical move. NEW here is only the E/R/R re-grounding: casting superposition as role-limit potentiality (so L2 is preserved on the actualized level), relocating the genuine quantum content to signed-weight interference, and exhibiting p=2 as the unique p-norm surviving a rational rotation.
- **Tags.** foundation, su-n, born-rule, L2, potentiality, role-limit, interference, P4, synthesis
- **Notes.** STATUS header says '14 Qed' but actual Qed. count is 10 (drift). 0 own axioms (imports no ToS axiom module here; uses only QArith). Born p=2 uniqueness is delegated to BornRuleDescent (cited, not in-file).

**Lemmas (32):**

| name | kind | role |
|---|---|---|
| `RoleState` | Definition | тип состояния = амплитудная пара (Q*Q) над 2 ролями |
| `amp_plus` | Definition | амплитуда +-полюса (fst) |
| `amp_minus` | Definition | амплитуда −-полюса (snd) |
| `has_pos_amp` | Definition | ненулевая +-амплитуда = ПОТЕНЦИАЛ полюса, не актуализация |
| `has_neg_amp` | Definition | ненулевая −-амплитуда = потенциал полюса |
| `actual_positive` | Definition | АКТУАЛИЗОВАННЫЙ + (Element): + есть, − отсутствует |
| `actual_negative` | Definition | актуализованный − (Element): + отсутствует, − есть |
| `in_potential` | Definition | ПОТЕНЦИАЛ (role-limit): обе амплитуды есть — ни один полюс не актуализован |
| `L2_holds_on_actualized` | Theorem | ★ L2 держится: ни одно состояние не есть и актуализ.-+, и актуализ.-− |
| `superposition_is_potential_not_both` | Theorem | ★ суперпозиция актуализовала НИ ОДИН полюс — потенциал, не «оба» (отзыв ¬L2-чтения) |
| `superposed` | Definition | конкретная суперпозиция (1,1) = \|+⟩+\|−⟩ |
| `superposed_is_potential` | Theorem | (1,1) находится в потенциале |
| `resolve_plus` | Definition | измерение = разрешение потенциала к +-полюсу |
| `resolution_actualizes` | Theorem | разрешение даёт актуализ.-+ и выводит из потенциала (L4-подобный шаг) |
| `dist_form` | Definition | форма различимости = внутр. произведение a+²+a−² (квадратичная) |
| `apply2` | Definition | применение 2×2 преобразования к состоянию |
| `swap` | Definition | дискретная симметрия S_2 (перестановка ролей) |
| `swap_preserves_dist` | Theorem | перестановка сохраняет dist_form (ring) |
| `rot` | Definition | вращение с c²+s²=1 (непрерывное замыкание) |
| `rot_preserves_dist` | Theorem | ★ УНИТАРНОСТЬ DERIVED: вращение c²+s²=1 сохраняет dist_form |
| `one_norm_broken_by_rotation` | Lemma | ★ 1<\|3/5\|+\|4/5\| — вращение ЛОМАЕТ 1-норму (образ (3,4,5)) |
| `global_phase` | Definition | глобальная фаза (−I) = рефлексивное самоотличие |
| `phase_preserves_dist` | Theorem | ★ det=1 DERIVED: глобальная фаза сохраняет всё наблюдаемое |
| `interference_cancels` | Theorem | ★ ИНТЕРФЕРЕНЦИЯ: два ненулевых знаковых вклада дают 0 (1+(−1)=0) |
| `classical_no_cancel` | Theorem | ★ классич. потенциал (p,q≥0) НЕ сокращается — контраст квантового |
| `SUNRequirement` | Inductive | 5 требований SU(N): Linearity/Unitarity/SpecialDet/Continuity/BornWeight |
| `ToSStatus` | Inductive | статус: Derived \| RoleLimit \| Posit |
| `status` | Definition | присвоение статуса каждому требованию (3 Derived, 2 RoleLimit, 0 Posit) |
| `linearity_is_potentiality_not_posit` | Theorem | ★ Linearity = RoleLimit (потенциальность, не постулат) |
| `no_antilaw_posit` | Theorem | ★ ни одно требование не есть Posit — ¬L2-чтение снято |
| `born_exponent_is_derived` | Theorem | ★ показатель Борна 2 ВЫВЕДЕН: 2-норма хранится, 1-норма ломается ⟹ status=Derived |
| `role_to_SUN_attempt` | Theorem | ★ капстоун: L2-сохранение ∧ потенциал ∧ унитарность ∧ фаза ∧ интерференция ∧ нет постулата |

**Key lemmas (deep):**

- **`born_exponent_is_derived`** - Ядро файла: показатель Борна p=2 выводится как ЕДИНСТВЕННАЯ p-норма, переживающая рациональное вращение — rot_preserves_dist хранит 2-норму, а one_norm_broken_by_rotation показывает 1<\|3/5\|+\|4/5\| (образ (1,0) под (3,4,5)-вращением имеет 1-норму 7/5). Честно: это конкретный свидетель против p=1, а не доказательство единственности по всем p (полный спуск делегирован BornRuleDescent.square_preserved). Element-сторона (рациональные точки вращения) точна и 0-аксиомна. _(born-rule, p2, rotation-invariant, derived)_
- **`superposition_is_potential_not_both`** - Концептуальный поворот: суперпозиция (обе амплитуды ненулевы) актуализовала НИ ОДИН полюс, поэтому L2_holds_on_actualized не нарушается. Это снимает прежнее чтение «суперпозиция = ослабленный L2» как категориальную ошибку (потенциал трактовался как актуальное). Доказательство тривиально (две импликации по определениям); ценность — в онтологической рамке, не в технике. _(potentiality, L2, role-limit, framing)_
- **`role_to_SUN_attempt`** - Капстоун-конъюнкция всего ledger'а: L2-сохранение + потенциальность + выведенная унитарность (S_2 ∧ фаза) + интерференция (знаковое сокращение, которого классич. потенциал не имеет) + отсутствие анти-законного постулата. Чистая сборка ранее доказанных лемм. Заявка скромная и честная: role→SU(N) сведён к фундаменту теории (role-limit + 2 аксиомы) + выведенной структуре, БЕЗ нового SM-специфичного постулата. _(synthesis, capstone, ledger, su-n)_

**Uniqueness - score 4 (synthesis+observation).** Ре-обоснование требований SU(N) в E/R/R: суперпозиция = role-limit-потенциальность (L2 сохранён), квантовое содержание = знаковая интерференция, показатель Борна 2 выведен как единственный вращательный инвариант — без нового анти-законного постулата.
> _Caveat:_ Каждый технический кирпич классичен (унитарность из сохранения формы, det=1, |·|² как единств. квадратичный инвариант; потенциальность-vs-актуальность — известный филос. ход). Ново лишь обрамление + сборка. p=2 выведен лишь ПРОТИВ p=1 конкретным свидетелем (полная единственность — в BornRuleDescent, цитата). Над ℚ; непрерывность/Linearity остаются role-limit-входом. Header заявляет 14 Qed — фактически 10.

---

## #1893 - `src/foundation/WqoProcessDecidable.v` - score 4 (synthesis+observation)

**wqo as a process over decidable orders: minimal-bad-sequence selection without Dependent Choice (0 axioms)**

- **Topic.** Stage 4 of the Process-Hierarchy direction: over (ℕ,≤) no bad sequence exists, any order-reflecting ℕ-measure pulls back wqo, and the Nash-Williams minimal-bad-sequence choice becomes the deterministic least-successor process dc_chain — all 0-axiom, with full Kruskal flagged as a horizon-ascent (Π¹₁-CA₀), not a binary wall.
- **Role.** Process-Hierarchy / determinacy-ascent file. Imports settheory.KruskalTree (is_wqo, wqo_nat_le) and cs.CountableDependentChoiceFree (dc_chain, next, next_least) — a BRIDGE that re-uses the vein-B no-DC chain to give the wqo method a process reading. Companion to ProcessHierarchy*/Determinacy*/FormerWalls*.
- **Counts.** Qed 4 / Admitted 0 / axioms 0
- **Imports.** Stdlib: PeanoNat Arith Lia; ToS: settheory.KruskalTree; ToS: cs.CountableDependentChoiceFree
- **E/R/R.** _Elements:_ последовательность f : nat→A; ℕ-мера h : A→nat; разрешимое тотальное R : nat→nat→bool. _Roles:_ good-пара = роль «свидетель wqo»; наименьший-преемник = роль, назначаемая ПРАВИЛОМ (не свободный выбор); ℕ-мера = спина рунга. _Rules:_ wqo_nat_le (фундированный спуск, 0-ax); над ℕ плохой последовательности нет; ℕ-мера, отражающая порядок ⟹ wqo (pullback); dc_chain = минимальный детерминированный шаг (без DC). _P4:_ над разрешимым/ℕ-измеримым и теорема (wqo), и метод (минимально-плохой выбор) — терминирующие 0-ax процессы; общий Крускал = consistency-strength горизонт-подъём (Π¹₁-CA₀), градуированный разрешимостью пространства, а НЕ бинарная стена.
- **Classical counterpart.** Well-quasi-orders, Nash-Williams' minimal-bad-sequence engine, and Higman/Kruskal's tree theorem are classical (the minimal-bad-sequence argument classically needs Dependent Choice; full Kruskal sits at Π¹₁-CA₀). The pullback fact 'an order-reflecting ℕ-measure ⟹ wqo' and well-foundedness of (ℕ,≤) are textbook. NEW is only the ToS process re-packaging: over a DECIDABLE / ℕ-measurable order, both the wqo theorem AND its minimal-bad-sequence METHOD are 0-axiom terminating processes (least-successor, no DC), with full Kruskal honestly localized as a consistency-strength horizon-ascent rather than a wall.
- **Tags.** foundation, wqo, kruskal, no-DC, minimal-bad-sequence, process-hierarchy, former-walls, P4, horizon-ascent
- **Notes.** STATUS header says '5 Qed' but actual Qed. count is 4 (drift; the 6th declaration wqo_pairs_by_fst is an Example closed by Qed too — recount confirms 4 Qed total: no_bad_seq_nat, wqo_pullback_nat, wqo_pairs_by_fst, minimal_selection_is_process and the capstone share... actual grep = 4). Re-uses cs.CountableDependentChoiceFree (the vein-B no-DC tower) as a bridge. 0 own axioms.

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `bad_seq` | Definition | плохая последовательность: нет ни одной good-пары (i<j с le (f i)(f j)) |
| `no_bad_seq_nat` | Lemma | ★ над ℕ плохой последовательности НЕ существует (прямо из wqo_nat_le, фундированный спуск) |
| `wqo_pullback_nat` | Theorem | ★ монотонная ℕ-мера, отражающая порядок ⟹ is_wqo (good-пара спуском по h∘f) |
| `wqo_pairs_by_fst` | Example | пары, сравниваемые по fst, — wqo (через ℕ-меру fst) |
| `minimal_selection_is_process` | Theorem | ★ минимально-плохой выбор над разрешимым R = детерм. процесс наименьшего-преемника dc_chain (валиден ∧ минимален, без DC) |
| `wqo_is_process_over_decidable` | Theorem | ★ капстоун: (ℕ,≤) wqo ∧ нет плохой ∧ pullback ∧ dc_chain-шаг — всё 0-ax процессы |

**Key lemmas (deep):**

- **`minimal_selection_is_process`** - Сердцевина: классический аргумент Нэша–Уильямса берёт на каждом шаге МИНИМАЛЬНОЕ плохое продолжение — за что классике нужен Dependent Choice. Над РАЗРЕШИМЫМ тотальным R этот выбор реифицируется в детерминированный процесс наименьшего-преемника dc_chain (из cs/CountableDependentChoiceFree): шаг всегда валиден (dc_chain_step) и каждый шаг минимален (next_least). Каноничен, единствен, 0-ax, без DC. Это мост-переупаковка, а не новая теорема — наименьший-преемник стандартен (Бишоп). _(no-DC, minimal-bad-sequence, least-successor, process, vein-B)_
- **`wqo_pullback_nat`** - Замыкание как процесс: если h:A→nat отражает порядок (h a ≤ h b ⟹ le a b), то le — wqo, ибо good-пара находится спуском wqo_nat_le по (h∘f). Тот же приём, что depth1_wqo (num_children) в KruskalFull — он достаёт разрешимую ℕ-измеримую ПОДчасть Крускала как терминирующий процесс. Честно: это перенос фундированности ℕ через меру, а не общий Higman. _(pullback, nat-measure, wqo, process)_
- **`wqo_is_process_over_decidable`** - Капстоун стадии 4: над разрешимым/ℕ-измеримым wqo — не стена, а процесс (базовый рунг ℕ + pullback-замыкание + минимально-плохой метод). Полный Крускал (произвольные деревья: Higman на произв. wqo-алфавитах — в KruskalFull лишь unit/bool — + общая минимально-плохая по структуре дерева) НЕ строится и честно помечен как горизонт-подъём Π¹₁-CA₀, локализованный разрешимостью, а не бинарная стена. Это и есть ценность файла: точная локализация горизонта. _(capstone, horizon-ascent, kruskal, former-walls)_

**Uniqueness - score 4 (synthesis+observation).** Над разрешимым/ℕ-измеримым порядком и теорема wqo, и её минимально-плохой МЕТОД (Нэш–Уильямс) суть 0-аксиомные терминирующие процессы наименьшего-преемника (без Dependent Choice); полный Крускал точно локализован как consistency-strength горизонт-подъём, а не стена.
> _Caveat:_ Все кирпичи классичны (wqo, фундированность ℕ, pullback-факт, наименьший-преемник = Бишоп; минимально-плохая последовательность = Нэш–Уильямс). Ново лишь process-упаковка + локализация горизонта. ПОДчасть мала: closure требует МОНОТОННОЙ ℕ-меры, отражающей порядок (incl. лишь depth-1 деревья), общий Higman/Kruskal НЕ формализован. Header заявляет 5 Qed — фактически 4.

