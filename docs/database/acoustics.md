# Database - cluster `acoustics`

_Generated from `acoustics.json` by `generate.ps1` - do not edit by hand; edit the JSON._

**10 files / 113 Qed.** Score distribution: s5=0 / s4=0 / s3=2 / s2=3 / s1=5 / s0=0

---

## #7 - `src/acoustics/AcousticsSynthesis.v` - score 1 (exposition)

**Grand synthesis of acoustics: six aspects of sound (oscillation→propagation→spectrum→harmony→loudness) on rational instances**

- **Topic.** Top-of-cluster synthesis: bundles an AcousticSystem record + Timbre as spectral fingerprint, then collects six aspects of sound — each a concrete Q computation re-exported from the cluster's files (Oscillation, WavePropagation, SoundSpectrum, Harmony, Loudness) — into one grand sound_from_first_principles theorem.
- **Role.** Capstone/aggregator of the acoustics cluster; pure consolidation (imports all five aspect files, re-exports their results). No new physics content; depends on Oscillation/WavePropagation/SoundSpectrum/Harmony/Loudness. Exposition layer for the book's acoustics narrative.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lia ZArith List Lqa; ToS.acoustics.Oscillation; ToS.acoustics.WavePropagation; ToS.acoustics.SoundSpectrum; ToS.acoustics.Harmony; ToS.acoustics.Loudness
- **E/R/R.** _Elements:_ AcousticSystem (размер графа, связь, число мод, основной тон); Timbre = list Q (спектральный отпечаток); конкретные рациональные инстансы. _Roles:_ L1–L5 + P4 → колебание→распространение→спектр→гармония→громкость: каждый закон играет роль ступени цепочки; тембр = роль-различитель источников. _Rules:_ колебание (L2+L3+L5) → распространение (+связь графа=волна) → дискретный спектр (+P4, конечный граф) → гармония (+L1, возврат тождества) → громкость (+правило Борна p=2, \|амплитуда\|²). _P4:_ конечный граф ⟹ ДИСКРЕТНЫЙ спектр мод (P4-грань: счётность ступеней). Звук = распространение повторяющихся актов различения по графу связанных вершин — переописание стандартной волновой физики в ToS-словаре, НЕ вывод нового содержания.
- **Classical counterpart.** Standard acoustics — the damped/undamped harmonic oscillator, wave propagation on a coupled chain, discrete normal-mode spectrum, consonance via small-integer frequency ratios (Pythagorean/just intonation), and the inverse-square + \|amplitude\|² (Born/intensity) laws — all classical wave physics; NEW is only the rhetorical 'derived from L1–L5 + P4' E/R/R packaging on concrete rational instances.
- **Tags.** acoustics, synthesis, capstone, wave-physics, exposition, timbre, ERR
- **Notes.** Qed DRIFT: STATUS-заголовок заявляет 10 Qed, фактический счёт = 8 (timbre_distinguishes, modes_equal_vertices, aspect_oscillation/propagation/spectrum/harmony/loudness, sound_from_first_principles). 0 Admitted, 0 собственных аксиом.

**Lemmas (14):**

| name | kind | role |
|---|---|---|
| `AcousticSystem` | Record | акустическая система: {размер графа; связь; число мод; основной тон} |
| `make_acoustic` | Definition | конструктор: N вершин, c² связь → система с N модами, основным тоном 2c² |
| `Timbre` | Definition | тембр = list Q (спектральный отпечаток) |
| `flute_timbre` | Definition | тембр флейты [0;1;1/10;1/100;0] |
| `string_timbre` | Definition | тембр струны [0;1;4/5;3/5;2/5] |
| `different_timbre` | Definition | тембры различны: ∃k, k-я гармоника отличается |
| `timbre_distinguishes` | Lemma | флейта ≠ струна (на 2-й гармонике, discriminate) |
| `modes_equal_vertices` | Lemma | число мод = число вершин (make_acoustic 64 → 64 моды) |
| `aspect_oscillation` | Theorem | Аспект 1: осциллятор k=2 период 4, переход через ноль (L2+L3+L5) |
| `aspect_propagation` | Theorem | Аспект 2: импульс распространяется, волновой фронт причинен (+связь) |
| `aspect_spectrum` | Theorem | Аспект 3: 4 моды, основной тон = 2 (+P4) |
| `aspect_harmony` | Theorem | Аспект 4: октава консонантнее квинты, период октавы = 2 (L1) |
| `aspect_loudness` | Theorem | Аспект 5: энергия ∝ амплитуда², закон обратных квадратов (Борн) |
| `sound_from_first_principles` | Theorem | ★ ГРАНД-СИНТЕЗ: все шесть аспектов звука в одной теореме |

**Key lemmas (deep):**

- **`sound_from_first_principles`** - Капстоун кластера: одна конъюнкция собирает шесть аспектов звука — осциллятор (период 4, переход через ноль), распространение (импульс идёт, фронт причинен), спектр (4 моды, основной тон 2), гармония (октава>квинта, период тритона 1440), громкость (E∝A², обратные квадраты) — каждый кусок exact-доказан в соответствующем файле кластера. Чистая агрегация: ценность педагогическая (нарратив «звук из законов логики»), не новое содержание. Честно: всё это стандартная волновая физика на рациональных инстансах. _(synthesis, capstone, aggregation, acoustics)_
- **`timbre_distinguishes`** - Тембр как спектральный отпечаток: флейта [0;1;1/10;…] и струна [0;1;4/5;…] различаются уже на 2-й гармонике (discriminate). Иллюстрирует, что Element-данные (рациональные амплитуды гармоник) различают источники звука — наглядно, но тривиально (несовпадение двух конкретных списков). _(timbre, spectrum, example)_

**Uniqueness - score 1 (exposition).** Чистая агрегация акустического кластера: шесть аспектов звука (колебание→распространение→спектр→гармония→громкость) собраны в один грант-синтез на рациональных инстансах, обрамлённые нарративом «звук = распространение актов различения».
> _Caveat:_ Всё содержание классическое (гармонический осциллятор, волна на цепочке, нормальные моды, консонанс малых отношений, обратные квадраты, |A|²). Никакого нового вывода — только E/R/R-переописание и агрегация. STATUS-заголовок завышает: заявлено 10 Qed, фактически 8 (DRIFT). Возможный оверклейм в фразе «derived, not described».

---

## #8 - `src/acoustics/DampingAndDissipation.v` - score 1 (exposition)

**Damping as vibration→wave: amplitude decay & energy radiation on rational instances**

- **Topic.** Models the damped oscillator as a rational finite-difference recurrence damped_next, shows γ=0 recovers the undamped oscillator, that small damping shrinks amplitude, computes concrete damped trajectories (γ=1/4, 1/2), derives damping from a coupling ratio, and does simple radiated-energy accounting (initial − remaining).
- **Role.** Mid-cluster acoustics file (damping/dissipation aspect). Imports acoustics.VibrationCore (next_state). Feeds the cluster's narrative on why sound dies out; consumed indirectly by the AcousticsSynthesis capstone's propagation/loudness story. Pure rational vm_compute / ring exposition.
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS.acoustics.VibrationCore
- **E/R/R.** _Elements:_ конкретные рациональные траектории damped_next (k,γ,d_prev,d_curr); энергии E_initial/E_remaining; коэффициенты связи — все актуальны (P4). _Roles:_ связь со средой = роль-канал утечки энергии; γ (затухание) = роль-параметр; «громкость» = скорость умирания (роль: чем громче, тем быстрее затухает). _Rules:_ затухание = эмиссия волны: энергия течёт ИЗ локального колебания к связанным соседям; damped_next = осциллятор с потерей; γ из связи = k_env/(k_int+k_env); излучённая энергия = начальная − оставшаяся. _P4:_ тишина = L1–L5-напряжение, РАСПРЕДЕЛённое по всем степеням свободы (а не исчезнувшее) — энергобаланс конечен и сохранён. Стандартная диссипативная динамика в ToS-словаре «колебание становится волной»; нового вывода нет.
- **Classical counterpart.** The damped harmonic oscillator (finite-difference recurrence dₙ₊₁=(2−k−γ)dₙ−(1−γ)dₙ₋₁), energy radiation = energy in − energy out, and damping rate from a coupling ratio k_env/(k_int+k_env) are textbook classical mechanics / wave dissipation; NEW is only the E/R/R reading 'damping = vibration energy becoming wave; silence = tension distributed across all DOF'.
- **Tags.** acoustics, damping, dissipation, harmonic-oscillator, energy, exposition, ERR
- **Notes.** Qed DRIFT: STATUS-заголовок заявляет 12 Qed, фактический счёт = 13 (undamped_is_standard, undamped_k2_period, damped_decreasing, damped_g14_d1, damped_g14_d2, damped_g12_d1, damping_weak/equal/strong_coupling, stronger_coupling_more_damping, energy_accounting, no_damping_no_radiation, damping_synthesis). 0 Admitted, 0 собственных аксиом.

**Lemmas (16):**

| name | kind | role |
|---|---|---|
| `damped_next` | Definition | затухающий шаг: (2−k−γ)·d_curr − (1−γ)·d_prev |
| `energy_radiated` | Definition | излучённая энергия = E_initial − E_remaining |
| `damping_from_coupling` | Definition | затухание из связи: k_env/(k_int+k_env) |
| `undamped_is_standard` | Lemma | γ=0 сводит к стандартному next_state (ring) |
| `undamped_k2_period` | Lemma | незатухающий k=2: damped_next 2 0 0 1 = 0, …1 0 = −1 |
| `damped_decreasing` | Lemma | малое затухание γ=1/10: \|d1\|<1 (амплитуда падает, vm_compute) |
| `damped_g14_d1` | Lemma | γ=1/4: damped_next 2 (1/4) 0 1 = −1/4 |
| `damped_g14_d2` | Lemma | γ=1/4 второй шаг = −11/16 |
| `damped_g12_d1` | Lemma | тяжёлое затухание γ=1/2: первый шаг = −1/2 |
| `damping_weak_coupling` | Lemma | слабая связь: damping_from_coupling 2 (1/10) = 1/21 |
| `damping_equal_coupling` | Lemma | равная связь: damping_from_coupling 1 1 = 1/2 |
| `damping_strong_coupling` | Lemma | сильная связь: damping_from_coupling 1 9 = 9/10 |
| `stronger_coupling_more_damping` | Lemma | сильнее связь ⟹ больше затухание (1/1 < 1/9 связь) |
| `energy_accounting` | Lemma | баланс энергии: energy_radiated 10 3 = 7 (ring) |
| `no_damping_no_radiation` | Lemma | нет затухания ⟹ нет излучения: energy_radiated 10 10 = 0 |
| `damping_synthesis` | Theorem | ★ СИНТЕЗ: γ=0=стандарт ∧ амплитуда↓ ∧ связь↑⟹затухание↑ ∧ нет затух.⟹нет излуч. |

**Key lemmas (deep):**

- **`damping_synthesis`** - Локальный капстоун файла: одна конъюнкция связывает четыре факта затухания — γ=0 даёт незатухающий осциллятор (ring), малое затухание уменьшает амплитуду (\|d1\|<1), более сильная связь даёт большее затухание, и отсутствие затухания означает нулевое излучение. Все куски — конкретные vm_compute/ring над ℚ. Чистая экспозиция диссипативной динамики; E/R/R-рамка «затухание = колебание становится волной, тишина = распределённое напряжение» риторическая, не выводящая. _(synthesis, damping, energy-balance, exposition)_
- **`undamped_is_standard`** - Корректность модели: при γ=0 рекуррентность damped_next точно совпадает с базовым осциллятором next_state из VibrationCore (доказано ring). Это санити-якорь — показывает, что затухающая динамика непрерывно расширяет незатухающую, а не подменяет её. Стандартный предельный переход γ→0. _(sanity-check, undamped-limit, ring)_

**Uniqueness - score 1 (exposition).** Затухание представлено как переход колебание→волна: затухающая рекуррентность над ℚ, восстановление незатухающего предела при γ=0, конкретные траектории, затухание из отношения связи и баланс излучённой энергии — обрамлено «тишина = напряжение, распределённое по всем DOF».
> _Caveat:_ Всё классическое: затухающий гармонический осциллятор, энергобаланс, скорость затухания из связи. Нового вывода нет — только рациональные инстансы + E/R/R-переописание. STATUS-заголовок занижает: заявлено 12 Qed, фактически 13 (DRIFT).

---

## #9 - `src/acoustics/Harmony.v` - score 1 (exposition)

**Музыкальные интервалы из отношений мод: консонанс C(p,q)=1/(p*q) на рациональных примерах**

- **Topic.** Определяет меру консонанса consonance p q = 1/(p*q), табличные интервалы (октава 2, квинта 3/2, кварта 4/3, тритон 45/32), комбинированный период = lcm(p,q) и гармонический ряд; всё проверяется vm_compute на конкретных числах (A=440).
- **Role.** Лист кластера acoustics, прикладной/экспозиционный. Зависит только от Stdlib (QArith/Lqa). Не импортируется другими файлами — иллюстрация «музыка = следствие L1».
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lia ZArith PeanoNat Lqa
- **E/R/R.** _Elements:_ пары тонов с целыми отношениями p/q; конкретные интервалы (октава, квинта, кварта, б.терция, тритон) как Q. _Roles:_ L1 (тождество → периодический возврат): короткий совместный период = устойчивость = консонанс; роль = ранг в порядке консонанса. _Rules:_ C(p,q) = 1/(p*q): простое отношение → большой консонанс; комбинированный период = lcm(p,q); гармоника n = n*fundamental. _P4:_ конечные целые отношения дают конечный совместный период (lcm) — Element-сторона: возврат достижим за lcm(p,q) шагов; иррациональные отношения (равномерная темперация) сюда НЕ попадают — это role-limit, формализуемый в соседнем MusicTemperament.v, не здесь.
- **Classical counterpart.** Пифагоров строй и ранжирование интервалов по простоте целочисленного отношения (Эйлеров gradus suavitatis, теория консонанса Гельмгольца) — классика теории музыки. Иррациональная сторона (пифагорова комма, равная темперация) формализована отдельно в MusicTemperament.v; НОВОГО результата здесь нет.
- **Tags.** acoustics, music, consonance, exposition, L1, over-branding

**Lemmas (22):**

| name | kind | role |
|---|---|---|
| `consonance` | Definition | мера консонанса 1/(p*q): чем проще отношение, тем больше |
| `unison_ratio` | Definition | унисон = 1 |
| `octave_ratio` | Definition | октава = 2 |
| `fifth_ratio` | Definition | квинта = 3/2 |
| `fourth_ratio` | Definition | кварта = 4/3 |
| `major_third_ratio` | Definition | большая терция = 5/4 |
| `tritone_ratio` | Definition | тритон = 45/32 |
| `octave_most_consonant` | Lemma | C(2,1) > C(3,2): октава консонантнее квинты (vm_compute) |
| `fifth_more_than_tritone` | Lemma | C(3,2) > C(45,32): квинта консонантнее тритона |
| `consonance_ordering` | Lemma | унисон > октава > квинта > кварта > б.терция (цепь неравенств) |
| `combined_period_factor` | Definition | совместный период = lcm(p,q) |
| `octave_period` | Lemma | lcm(2,1) = 2 |
| `fifth_period` | Lemma | lcm(3,2) = 6 |
| `tritone_period` | Lemma | lcm(45,32) = 1440 (длинный период тритона) |
| `harmonic_freq` | Definition | частота n-й гармоники = n*fundamental |
| `harmonic_2` | Lemma | 2-я гармоника 440 = 880 |
| `harmonic_3` | Lemma | 3-я гармоника 440 = 1320 |
| `octave_is_second_harmonic` | Lemma | октава = 2-я гармоника |
| `shared_harmonics` | Fixpoint | счётчик общих гармоник двух тонов в окне K |
| `shared_harmonics_octave` | Lemma | октава делит 3 из 6 гармоник |
| `shared_harmonics_fifth` | Lemma | квинта делит 2 из 6 гармоник |
| `harmony_synthesis` | Theorem | ★ свод: порядок консонанса + периоды + октава=2-я гармоника |

**Key lemmas (deep):**

- **`consonance_ordering`** - Главное содержательное утверждение файла: 1/(p*q) задаёт строгий порядок унисон>октава>квинта>кварта>б.терция. Это не теорема о консонансе вообще, а проверка одной выбранной формулы на пяти числах через vm_compute. Классически совпадает с ранжированием по простоте отношения (теория консонанса Гельмгольца/Эйлера gradus suavitatis); ново только E/R/R-обрамление «короткий lcm-возврат = L1-устойчивость». _(consonance, exposition, L1)_
- **`combined_period_factor`** - lcm(p,q) = число периодов основного тона до совместного возврата; тритон 45/32 даёт 1440 (диссонанс) против октавы 2 (консонанс). Это и есть «Element-сторона»: целое отношение ⟹ конечный возврат. Честно: всё на конкретных p,q, никакого общего теоремного утверждения о монотонности консонанс↔lcm нет. _(period, lcm, vibration-return)_

**Uniqueness - score 1 (exposition).** Чистая экспозиция: стандартная теория консонанса (1/(p*q), интервалы, lcm-период, гармонический ряд) аккуратно проверена над Q на конкретных интервалах, в E/R/R-обрамлении «консонанс из L1».
> _Caveat:_ Всё классично (Пифагор/Эйлер/Гельмгольц) и проверено лишь на отдельных числах через vm_compute — не общие теоремы. Лозунг шапки «Music theory = CONSEQUENCE of ToS» — оверклейм: формула 1/(p*q) ПОСТУЛИРОВАНА, а не выведена из законов; иррациональная (role-limit) сторона музыки в этом файле отсутствует.

---

## #10 - `src/acoustics/HierarchyTheorem.v` - score 2 (methods)

**Лестница Колебание < Вибрация < Волна > Звук: каждый уровень = предыдущий + один ингредиент**

- **Topic.** Вводит записи VibrationRec/WaveRec/SoundRec, вложения wave→vib и sound→wave, и показывает на примерах, что убирание ингредиента (связи c=0, восстанавливающей силы k=0) рушит соответствующий уровень, а слышимость = 20..20000 Гц.
- **Role.** Капстоун кластера acoustics: связывает VibrationCore и WavePropagation в иерархию записей. Импортирует acoustics.VibrationCore, acoustics.WavePropagation; верхний файл цепочки.
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lia ZArith PeanoNat Lqa; ToS: acoustics.VibrationCore; ToS: acoustics.WavePropagation
- **E/R/R.** _Elements:_ записи-уровни VibrationRec{k}, WaveRec{k,coupling,size}, SoundRec{wave,freq}; конкретные обитатели (камертон k=2, воздушная волна). _Roles:_ каждый уровень = роль-ярус: вибрация (L1 восстановление + L5 инерция), волна (+ пространственный граф + связь), звук (+ слышимость); вложение = «содержит предыдущий». _Rules:_ wave_to_vib/sound_to_wave проектируют вниз; убрать ингредиент (c=0 ⟹ нет распространения; k=0 ⟹ линейный дрейф) ⟹ уровень коллапсирует; 20<=freq<=20000. _P4:_ лестница конечных уровней, каждый отделён ОДНИМ конструктивным ингредиентом; коллапс при обнулении ингредиента наблюдаем на конкретных значениях (no_coupling, no_restoring) — это демонстрация необходимости ингредиента, а не общая теорема о минимальности.
- **Classical counterpart.** Стандартная физика: гармонический осциллятор (восстанавливающая сила + инерция), волновое уравнение на связанной решётке, слышимый диапазон 20 Гц–20 кГц. НОВОГО результата нет; ново лишь обрамление «уровень = предыдущий + один ингредиент» как лестница записей в E/R/R.
- **Tags.** acoustics, hierarchy, records, methods, collapse, drift
- **Notes.** STATUS-шапка: 10 Qed; фактически 11 Qed (дрейф +1). 0 Admitted, 0 собственных аксиом. Делегирует no_coupling_no_propagation и impulse_propagates в acoustics.WavePropagation.

**Lemmas (18):**

| name | kind | role |
|---|---|---|
| `VibrationRec` | Record | уровень вибрации: жёсткость k>0 |
| `WaveRec` | Record | уровень волны: k>0, связь>0, граф>1 вершины |
| `SoundRec` | Record | уровень звука: волна + слышимая частота 20..20000 |
| `wave_to_vib` | Definition | проекция волна→вибрация (забывает связь/граф) |
| `sound_to_wave` | Definition | проекция звук→волна (поле sr_wave) |
| `wave_has_vibration` | Lemma | волна содержит вибрацию: k>0 |
| `sound_has_wave` | Lemma | звук содержит волну: граф>1 |
| `tuning_fork` | Definition | камертон = VibrationRec с k=2 (через lra) |
| `air_wave` | Definition | воздушная волна = WaveRec(k=2,c=1/4,size=100) |
| `tuning_fork_k` | Lemma | k камертона = 2 |
| `air_wave_size` | Lemma | размер графа воздушной волны = 100 |
| `no_coupling_collapse` | Lemma | ★ связь=0 ⟹ нет распространения (делегирует WavePropagation) |
| `no_restoring_drift` | Lemma | ★ k=0 ⟹ линейный дрейф next_state, нет колебания |
| `both_present_oscillation` | Lemma | k=2 и связь>0 ⟹ колебание + распространение |
| `concert_A_audible` | Lemma | 440 Гц в слышимом диапазоне |
| `ultrasound_inaudible` | Lemma | 40000 Гц > 20000 (ультразвук неслышим) |
| `infrasound_inaudible` | Lemma | 20 не <= 10 (инфразвук-граница) |
| `hierarchy_synthesis` | Theorem | ★ свод: вложение + два коллапса + оба ингредиента + слышимость A |

**Key lemmas (deep):**

- **`no_restoring_drift`** - Содержательное ядро «лестницы»: при k=0 рекуррентность next_state вырождается в линейный дрейф 1,2,3 (нет возврата к нулю), т.е. без L1-восстановления нет колебания. Вместе с no_coupling_collapse это и есть «убери ингредиент → коллапс уровня». Честно: оба факта проверены на конкретных значениях, а не как теоремы для всех начальных условий. _(collapse, restoring-force, L1)_
- **`hierarchy_synthesis`** - Свод-капстоун: волна содержит вибрацию, обнуление связи/восстановления рушит распространение/колебание, оба вместе дают и колебание, и распространение, и 440 Гц слышимо. Архитектурно полезен (связывает VibrationCore↔WavePropagation в одну запись-иерархию), но это демонстрационная конъюнкция примеров, а не новый математический результат. _(synthesis, hierarchy, records)_

**Uniqueness - score 2 (methods).** Необычная формализация-обрамление обычной акустики: четыре уровня (колебание/вибрация/волна/звук) как лестница записей с вложениями и наблюдаемым коллапсом при обнулении ингредиента (связь, восстановление).
> _Caveat:_ Содержание (осциллятор, волна на решётке, слышимость) полностью классично; коллапсы доказаны на конкретных значениях, не как общие теоремы. Шапка заявляет 10 Qed — фактически 11 (дрейф +1). Уровни L1/L2/L3/L5 в комментариях — интерпретация, не выведенные сущности.

---

## #11 - `src/acoustics/Loudness.v` - score 1 (exposition)

**Громкость = |амплитуда|^2 и закон обратных квадратов на рациональных примерах**

- **Topic.** Определяет sound_energy a = a*a (энергия = квадрат амплитуды, мотивируется правилом Борна p=2), интенсивность E/n и обратно-квадратичное затухание E/(r*r); проверяет 2x амплитуды → 4x энергии, неотрицательность, тишину и 1/r^2 на конкретных числах.
- **Role.** Лист кластера acoustics, прикладной/экспозиционный. Зависит только от Stdlib (QArith/Lqa). Не импортируется другими файлами.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lia ZArith Lqa
- **E/R/R.** _Elements:_ амплитуда как Q; конкретные значения (3/5, 2, 3, -7, 0); расстояния r=1,2,3. _Roles:_ правило Борна (p=2) → роль «энергия = квадрат»; интенсивность = энергия/вершины; затухание = энергия/r^2. _Rules:_ E = A^2; I = E/n; I(r) = E/r^2; показатель 2 берётся как «выведенный из унитарности» (в соседних файлах), здесь зафиксирован. _P4:_ квадратичная мера на конечных рациональных амплитудах всегда вычислима (Element-сторона); неотрицательность energy_nonneg — единственное общее утверждение, остальное — конкретные примеры.
- **Classical counterpart.** Стандартная акустика/КМ: интенсивность ~ квадрат амплитуды (правило Борна) и закон обратных квадратов I~1/r^2. Уникальность показателя 2 (Борн из унитарности / Глисон) — известный результат, формализуемый отдельно; здесь p=2 зафиксирован и применён, не выведен.
- **Tags.** acoustics, loudness, born-rule, inverse-square, exposition, over-branding

**Lemmas (13):**

| name | kind | role |
|---|---|---|
| `sound_energy` | Definition | энергия звука = amplitude*amplitude (Борн p=2) |
| `intensity` | Definition | интенсивность = полная энергия / число вершин |
| `inverse_square` | Definition | затухание = энергия / r^2 |
| `energy_is_amplitude_squared` | Lemma | E(3/5) = 9/25 |
| `double_amplitude_quadruple_energy` | Lemma | удвоение амплитуды → учетверение энергии |
| `triple_amplitude` | Lemma | утроение амплитуды → 9x энергии |
| `energy_nonneg` | Lemma | ★ E(a) >= 0 для ВСЕХ a (единственное общее утверждение) |
| `energy_zero_iff_silent` | Lemma | E(0) = 0 (тишина) |
| `inverse_square_decreases` | Lemma | I(r=2) < I(r=1): убывание с расстоянием |
| `inverse_square_r1` | Lemma | I(1) = 1 |
| `inverse_square_r2` | Lemma | I(2) = 1/4 |
| `inverse_square_r3` | Lemma | I(3) = 1/9 |
| `loudness_synthesis` | Theorem | ★ свод: E=A^2 + квадратичность + E>=0 + тишина + 1/r^2 |

**Key lemmas (deep):**

- **`energy_nonneg`** - Единственная содержательная общая лемма файла: для любой рациональной амплитуды a квадрат a*a >= 0 (разбор знака + Qmult_le_0_compat). Тривиальный факт о квадрате, но это и есть честное «E>=0 всегда»; остальные леммы — E(A^2), 2x→4x, 1/r^2 — проверены лишь на конкретных числах. _(nonneg, born, general)_
- **`double_amplitude_quadruple_energy`** - Иллюстрация показателя p=2: 2x амплитуды ⟹ 4x энергии. Это определение sound_energy=A^2, проверенное на a=1,2 через vm_compute, а не вывод p=2 из чего-либо. «Born rule p=2 unique from unitarity» из шапки в этом файле НЕ доказывается — лишь постулируется и применяется. _(born-exponent, quadratic, exposition)_

**Uniqueness - score 1 (exposition).** Экспозиция: громкость=A^2 и 1/r^2 над Q на конкретных амплитудах/расстояниях, с единственным общим фактом energy_nonneg.
> _Caveat:_ Всё классично (Борн, обратные квадраты) и проверено на отдельных числах. Шапка «Loudness = amplitude squared ... CONSEQUENCE of Born rule (p=2 unique from unitarity)» — оверклейм: показатель 2 здесь ПОСТУЛИРОВАН (sound_energy:=a*a), а не выведен; вывод p=2 живёт в других файлах, не в этом.

---

## #12 - `src/acoustics/Oscillation.v` - score 2 (methods)

**Дискретный гармонический осциллятор delta(t+1)=(2-k)delta(t)-delta(t-1): периоды k=1,2,3, перезатухание k>=4**

- **Topic.** Fixpoint oscillator реализует трёхчленную рекуррентность гармонического осциллятора над Q; на конкретных k проверяет период 4 (k=2), значения k=1/k=3, пересечение нуля, тишину, перезатухание k=4 и величины энергии (3/2, 1/2, перераспределение).
- **Role.** Лист кластера acoustics, прикладной/экспозиционный. Зависит только от Stdlib (QArith/Lqa). Реализует динамическое ядро, на которое концептуально опирается остальная акустика (но без импортов).
- **Counts.** Qed 14 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lia ZArith Lqa
- **E/R/R.** _Elements:_ отклонение delta(t) как Q; жёсткость k (1,2,3,4); начальные (d0,d1); энергия как Q. _Roles:_ L2 (отклонение реально → восстанавливающая сила k>0) + L3 (состояние определённо → динамика корректна) + L5 (переход требует времени → инерция → овершут → колебание). _Rules:_ delta(t+1) = (2-k)*delta(t) - delta(t-1); энергия = (Δскорость)^2/2 + k*x^2/2; 0<k<4 колебательно, k>=4 перезатухание. _P4:_ конечная рекуррентность над Q: каждый шаг вычислим (Fixpoint, vm_compute) — Element-сторона; период/коллапс наблюдаемы на конкретных k, но это табличные проверки, а не теоремы «для всех t период = 4» или «энергия сохраняется».
- **Classical counterpart.** Стандартный дискретный гармонический осциллятор / линейная трёхчленная рекуррентность; устойчивость и период задаются собственными значениями (2-k)±... = корнями из единицы при подходящих k. Классика численной физики; ново лишь E/R/R-чтение «осцилляция из L2+L3+L5» и честная фиксация несохранения дискретной энергии.
- **Tags.** acoustics, oscillator, recurrence, energy, methods, honesty, drift
- **Notes.** STATUS-шапка: 12 Qed; фактически 14 Qed (дрейф +2). 0 Admitted, 0 собственных аксиом. energy_redistributes — честная фиксация несохранения дискретной энергии.

**Lemmas (16):**

| name | kind | role |
|---|---|---|
| `oscillator` | Fixpoint | трёхчленная рекуррентность гармонического осциллятора над Q |
| `energy` | Definition | энергия = (d_curr-d_prev)^2/2 + k*d_curr^2/2 |
| `osc_k2_period4` | Lemma | ★ k=2: значения 1,0,-1,0,1 (период 4) на 5 шагах |
| `osc_k1_values` | Lemma | k=1: 1,1,0,-1 (медленнее) |
| `energy_t0` | Lemma | энергия при t=0 = 3/2 |
| `energy_t1` | Lemma | энергия при t=1 = 1/2 |
| `energy_redistributes` | Lemma | ★ E(t0) > E(t1): дискретная энергия НЕ сохраняется (честная оговорка) |
| `zero_crossing` | Lemma | osc 2 1 0 2 < 0: пересечение нуля = овершут |
| `silence_is_no_distinction` | Lemma | d0=d1=0 ⟹ всё 0 (тишина = нет различения) |
| `osc_k3_values` | Lemma | k=3: 1,0,-1,1 (период 3) |
| `overdamped_k4_0` | Lemma | k=4 шаг 0 = 1 |
| `overdamped_k4_1` | Lemma | k=4 шаг 1 = 0 |
| `overdamped_k4_2` | Lemma | k=4 шаг 2 = -1 |
| `energy_positive_k2` | Lemma | 0 < E(k=2,1,0): энергия положительна |
| `energy_zero_silence` | Lemma | E(k=2,0,0) = 0 |
| `oscillation_synthesis` | Theorem | ★ свод: период 4 + пересечение нуля + энергия 3/2 + тишина + E>0 |

**Key lemmas (deep):**

- **`osc_k2_period4`** - Ядро файла: при k=2 рекуррентность даёт 1,0,-1,0,1 — период 4. Это и есть «колебание из L2+L3+L5»: целая жёсткость → возврат. Честно: проверены пять конкретных шагов через vm_compute, а не доказан период для всех t; общая теорема о периодичности (собственные значения характеристического уравнения = корни из единицы при рац. k) НЕ формализована. _(oscillator, period, recurrence)_
- **`energy_redistributes`** - Редкая для кластера ЧЕСТНАЯ оговорка: дискретная энергия (d_curr-d_prev)^2/2 + k*x^2/2 НЕ сохраняется — E(t0)=3/2 > E(t1)=1/2. Файл не выдаёт дискретный гамильтониан за сохраняющийся, прямо фиксируя перераспределение. Сильная сторона на фоне общей экспозиционности. _(energy, non-conservation, honesty)_

**Uniqueness - score 2 (methods).** Необычная формализация обычного дискретного осциллятора над Q с честной оговоркой о несохранении дискретной энергии; периоды k=1/2/3 и перезатухание k=4 проверены на конкретных значениях.
> _Caveat:_ Содержание классично; периоды доказаны как табличные равенства (5 шагов), а не как общие теоремы о периодичности для всех t. Связь с L2/L3/L5 — интерпретация. Шапка заявляет 12 Qed — фактически 14 (дрейф +2).

---

## #13 - `src/acoustics/SoundSpectrum.v` - score 1 (exposition)

**Дискретный спектр из мод конечного графа (DFT): N вершин → N мод, фундаментальная и спектральная энергия**

- **Topic.** На цепи C_4 берёт лапласовы собственные значения omega^2 = [0;2;4;2], находит фундаментальную (наименьшую ненулевую = 2) и максимальную (=4), считает спектральную энергию E=Sum A_k^2 * omega_k и фиксирует P4: число мод = число вершин = длина списка.
- **Role.** Лист кластера acoustics, прикладной/экспозиционный. Зависит только от Stdlib (QArith/List/Lqa). Не импортируется другими файлами — иллюстрация «P4: конечный граф → дискретный спектр».
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lia ZArith List Lqa
- **E/R/R.** _Elements:_ конкретный список собственных значений omega_sq_4=[0;2;4;2] (лапласиан C_4); амплитуды мод как list Q. _Roles:_ P4 (конечный граф) → конечное число мод → квантованная частота; каждая мода = «чистый тон» omega_k; роль = ярус спектра. _Rules:_ n_modes N = N; фундаментальная = наименьшая ненулевая omega^2; max = наибольшая; E = Sum A_k^2 * omega_k. _P4:_ ЯДРО P4-демонстрации: конечный граф (N вершин) ⟹ РОВНО N мод ⟹ дискретный (не континуальный) спектр; modes_eq_vertices фиксирует это как равенство length omega_sq_4 = n_modes 4 — но только на N=4, не для общего N.
- **Classical counterpart.** Дискретное преобразование Фурье / нормальные моды связанной цепочки: симметричная матрица N×N имеет N собственных мод, спектр графа = собственные значения лапласиана (здесь C_4: {0,2,4,2}). Классика линейной алгебры/физики; ново лишь P4-обрамление «конечный граф → дискретный спектр», проверенное на одном графе.
- **Tags.** acoustics, spectrum, DFT, graph-laplacian, P4, exposition, drift
- **Notes.** STATUS-шапка: 10 Qed; фактически 9 Qed (дрейф -1). 0 Admitted, 0 собственных аксиом. Собственные значения C_4 заданы литералом omega_sq_4=[0;2;4;2], не вычислены из лапласиана.

**Lemmas (17):**

| name | kind | role |
|---|---|---|
| `omega_sq_4` | Definition | лапласовы собственные значения C_4: [0;2;4;2] |
| `n_modes` | Definition | число мод = размер графа N |
| `four_modes` | Lemma | n_modes 4 = 4 |
| `qlt_bool` | Definition | булево <  на Q через Qcompare |
| `qeq_bool` | Definition | булево == на Q через Qcompare |
| `find_fundamental` | Fixpoint | наименьшее ненулевое значение списка |
| `fundamental_chain4` | Lemma | ★ фундаментальная C_4 = 2 |
| `find_max` | Fixpoint | максимум списка |
| `max_freq_chain4` | Lemma | макс частота C_4 = 4 |
| `spectral_energy_aux` | Fixpoint | Sum A_k^2 * omega_k (рекурсия по двум спискам) |
| `spectral_energy` | Definition | обёртка спектральной энергии |
| `spectral_energy_equal_amps` | Lemma | равные амплитуды [1;1;1;1] → E = 8 |
| `spectral_energy_silent` | Lemma | нулевые амплитуды → E = 0 |
| `single_mode_energy` | Lemma | одна мода [0;3;0;0] → E = 18 |
| `spectrum_size` | Lemma | length omega_sq_4 = 4 |
| `modes_eq_vertices` | Lemma | ★ P4: n_modes 4 = length omega_sq_4 (моды = вершины) |
| `sound_spectrum_synthesis` | Theorem | ★ свод: 4 моды + фундаментальная 2 + макс 4 + энергии 8/0 |

**Key lemmas (deep):**

- **`modes_eq_vertices`** - Заявленное P4-ядро: число мод = число вершин графа, т.е. конечный граф ⟹ дискретный конечный спектр (а не континуум). Честно: это равенство reflexivity на КОНКРЕТНОМ N=4 (n_modes 4 = length [0;2;4;2]); общего утверждения «для графа на N вершинах ровно N собственных мод» (спектральная теорема для симметричного лапласиана) здесь НЕТ — оно лишь иллюстрируется. _(P4, discrete-spectrum, finite-graph)_
- **`fundamental_chain4`** - find_fundamental на [0;2;4;2] даёт 2 (наименьшее ненулевое). Собственные значения C_4 {0,2,4,2} ВПИСАНЫ как литерал, а не вычислены из матрицы лапласиана — то есть «DFT/нормальные моды» из шапки не выводятся, а табулируются. spectral_energy_equal_amps=8 = просто сумма частот при единичных амплитудах. _(fundamental, eigenvalues, hardcoded)_

**Uniqueness - score 1 (exposition).** Экспозиция: дискретный спектр конечного графа (C_4, моды=вершины, фундаментальная/макс частота, спектральная энергия) над Q на одном конкретном примере, в P4-обрамлении.
> _Caveat:_ Содержание классично (спектр лапласиана, DFT). Собственные значения [0;2;4;2] ЗАХАРДКОЖЕНЫ, а не выведены из матрицы; «N вершин → N мод» проверено лишь для N=4 (reflexivity), не как общая спектральная теорема. Шапка заявляет 10 Qed — фактически 9 (дрейф -1).

---

## #14 - `src/acoustics/VibrationCore.v` - score 3 (new-framing)

**Vibration as forced L1<->L5 tension: restoring identity vs change-takes-time, on Q instances**

- **Topic.** Defines the rational leapfrog oscillator next_state, velocity, and kinetic/potential energy, and shows by concrete Q computation that L1-alone or L5-alone gives no oscillation while L1+L5 forces a period-4 cycle with nonzero velocity at the equilibrium crossing.
- **Role.** First file of the acoustics chain. Imports acoustics.Oscillation; reused by VibrationSynthesis (vibration_wave_connection bridges next_state to wave_step). Pure single-vertex base for WavePropagation.
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith PeanoNat Lqa; acoustics.Oscillation
- **E/R/R.** _Elements:_ восстанавливающая сила, состояние next_state, скорость, фаза, энергия — конкретные рациональные значения (P4: каждый шаг актуален). _Roles:_ L1 = роль возврата к тождеству (отклонение delta!=0 -> сила); L5 = роль инерции (скорость переносится через равновесие); пара ролей = вынужденное колебание. _Rules:_ L1 один -> мгновенный возврат, стоп (нет колебания); L5 один (k=0) -> линейный дрейф, не возвращается; L1+L5 (k=2) -> период-4 цикл 0,-1,0,1. _P4:_ колебание = ВЕЧНЫЙ КОМПРОМИСС двух ролей: ни L1 (L5 мешает остановиться), ни L5 (L1 мешает уйти) не побеждают; скорость!=0 при delta=0 форсирует перелёт. Колебание — логическая необходимость при L1+L5+возмущении; всё на конечных Q-инстансах.
- **Classical counterpart.** The discrete (leapfrog) harmonic oscillator d(t+1)=(2-k)d(t)-d(t-1) and its energy partition (kinetic <-> potential) are standard SHM / Verlet-integrator physics; NEW is only the E/R/R reading of oscillation as a forced L1<->L5 compromise (restoring identity vs change-takes-time), proved on rational instances.
- **Tags.** acoustics, oscillation, L1-L5, err-framing, energy, P4
- **Notes.** STATUS header says 15 Qed; actual Qed. count = 12 (drift). 0 Admitted, 0 own axioms/Parameters.

**Lemmas (22):**

| name | kind | role |
|---|---|---|
| `restoring_force` | Definition | L1-сила -k*delta |
| `next_state` | Definition | лип-фрог шаг (2-k)*d_curr - d_prev (дискретный осциллятор) |
| `velocity` | Definition | скорость d_curr - d_prev |
| `phase_state` | Definition | фазовая точка (положение, скорость) |
| `kinetic_energy` | Definition | кинетическая энергия v*v/2 (L5) |
| `potential_energy` | Definition | потенциальная энергия k*delta^2/2 (L1) |
| `total_energy_vib` | Definition | полная энергия = кинетическая + потенциальная |
| `L1_without_L5_no_vibration` | Lemma | мгновенный возврат = 0, нет колебания (тривиально) |
| `L5_without_L1_no_vibration` | Lemma | k=0: дрейф 1->2->3->4 (никогда не возвращается) |
| `drift_never_returns` | Lemma | k=0: next_state > 1 (монотонный уход) |
| `L1_plus_L5_forced_oscillation` | Lemma | ★ k=2: период-4 цикл d1..d4 = 0,-1,0,1 (vm_compute) |
| `velocity_nonzero_at_equilibrium` | Lemma | скорость = -1 при пересечении delta=0 |
| `velocity_not_zero` | Lemma | скорость != 0 в равновесии -> ОБЯЗАН перелёт |
| `energy_at_max` | Lemma | энергия 3/2 при максимальном смещении |
| `energy_at_zero` | Lemma | энергия 1/2 при нулевом пересечении |
| `pure_kinetic_at_zero` | Lemma | потенциальная = 0 при delta=0 (вся энергия кинетическая) |
| `potential_at_max` | Lemma | потенциальная = 1 при delta=1 (вся энергия потенциальная) |
| `BinaryState` | Inductive | двоичное состояние StateA / StateNotA |
| `binary_oscillation` | Definition | чётность t -> StateA/StateNotA (дискретное чередование) |
| `binary_alternates` | Lemma | A,NotA,A на t=0,1,2 (минимальное колебание) |
| `is_audible` | Definition | омега в диапазоне слуха 20..20000 Гц |
| `vibration_core_synthesis` | Theorem | ★ синтез: дрейф (L5), период-4 (L1+L5), скорость -1, энергобаланс — в одной теореме |

**Key lemmas (deep):**

- **`L1_plus_L5_forced_oscillation`** - Ядро файла: при k=2 итерация next_state даёт ТОЧНЫЙ период-4 цикл 0,-1,0,1 на рациональных числах (vm_compute, без приближения). Контрастно к L5_without_L1 (дрейф) и L1_without_L5 (мгновенный стоп) — это машинная демонстрация тезиса 'колебание = вынужденный компромисс L1 и L5'. Честно: это стандартный дискретный осциллятор (Верле/лип-фрог) на одном инстансе k=2; новизна — рамка E/R/R, не вычисление. _(oscillation, L1-L5, period-4, err-framing)_
- **`velocity_not_zero`** - Формализует 'натяжение': в момент пересечения равновесия (delta=0) скорость !=0, поэтому система ОБЯЗАНА проскочить — L1 не может остановить из-за L5. Логический мостик от энергии к необходимости перелёта; доказано через точное Q-значение -1 (lra). Содержательно тривиально, концептуально несёт всю историю файла. _(velocity, overshoot, tension)_

**Uniqueness - score 3 (new-framing).** Колебание переосмыслено как вынужденный неустранимый компромисс двух законов ToS (L1 возврат-к-тождеству и L5 изменение-требует-времени), с машинно-проверенными конкретными Q-инстансами (период-4, скорость!=0 в равновесии, энергобаланс).
> _Caveat:_ Дискретный гармонический осциллятор и обмен кинетика<->потенциал классичны (Верле/SHM); ново только E/R/R-обрамление. Всё на единичных рациональных инстансах (k=2 и т.п.), не общая теорема о колебаниях. DRIFT: заголовок STATUS заявляет 15 Qed, фактически 12.

---

## #15 - `src/acoustics/VibrationSynthesis.v` - score 3 (new-framing)

**Grand acoustics synthesis: one L1-L5 tension across wave/phonon/thermal/compression/vacuum**

- **Topic.** Bundles results from the acoustics chain into one narrative: a single-vertex wave step equals next_state (vibration), phonon modes are finite, mode truncation loses energy, the zero-point sum is positive (vacuum not silent), and undamped=eternal vs damped=decaying.
- **Role.** Capstone of the acoustics cluster (pure consolidation, little new content). Imports VibrationCore, DampingAndDissipation, HierarchyTheorem, WavePropagation, Oscillation, SoundSpectrum.
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith List Lqa; acoustics.VibrationCore; acoustics.DampingAndDissipation; acoustics.HierarchyTheorem; acoustics.WavePropagation; acoustics.Oscillation; acoustics.SoundSpectrum
- **E/R/R.** _Elements:_ связь вибрация-волна, фонон, сжатие (выбор мод), тепловое распределение — конкретные Q-инстансы; конечное число мод (P4). _Roles:_ ОДНА роль (натяжение L1-L5) играется в шести аренах: акустика, КТП (фонон), термодинамика, сжатие данных, вакуум, музыка. _Rules:_ волна на одной вершине = вибрация (field-уравнение); фонон = квант моды; сжатие = усечение мод (теряет энергию); нулевая энергия = сумма omega/2 > 0. _P4:_ одна концепция = L1-L5 натяжение унифицирует домены; конечность мод (n_modes 64) = грань P4; вакуум не молчит (zpe>0) = неустранимое натяжение. Каждая связь — на конечном инстансе, не общий закон.
- **Classical counterpart.** Each piece is standard: lattice wave equation as a single-vertex limit, phonon energy E=hbar*omega*n, spectral truncation losing energy, zero-point energy sum omega/2 (Casimir/vacuum), damped vs undamped oscillator. NEW is only the umbrella E/R/R claim that one L1-L5 tension underlies acoustics/QFT/thermo/compression/vacuum.
- **Tags.** acoustics, synthesis, L1-L5, phonon, vacuum, compression, err-framing

**Lemmas (13):**

| name | kind | role |
|---|---|---|
| `vibration_wave_connection` | Lemma | ★ волновой шаг без соседей = next_state (вибрация = волна на одной вершине), field |
| `phonon_modes_finite` | Lemma | число фононных мод = 64 = число вершин (P4) |
| `phonon_energy` | Definition | энергия фонона omega*n |
| `zero_phonons_zero_energy` | Lemma | 0 фононов -> 0 энергии |
| `one_phonon_energy` | Lemma | 1 фонон при omega=2 -> энергия 2 |
| `truncated_energy` | Lemma | усечённый спектр (1 из 4 мод) -> энергия 2 |
| `full_energy` | Lemma | полный спектр (4 моды) -> энергия 8 |
| `compression_loses_energy` | Lemma | ★ сжатие (усечение мод) теряет энергию (2 < 8) |
| `zero_point_energy` | Definition | нулевая энергия = sum omega/2 |
| `zpe_chain4` | Lemma | нулевая энергия цепочки-4 = 4 |
| `vacuum_not_silent` | Lemma | ★ нулевая энергия > 0 (вакуум не молчит, Казимир) |
| `damping_connects` | Lemma | недемпфированное = next_state; демпфированное -> амплитуда убывает <1 |
| `vibration_grand_synthesis` | Theorem | ★ КАПСТОУН: 6 доменов (волна/фонон/сжатие/вакуум/демпфирование) в одной теореме |

**Key lemmas (deep):**

- **`vibration_wave_connection`** - Несущий мост кластера: волновой шаг wave_step с одной вершиной (без соседей) ТОЧНО равен next_state из VibrationCore — то есть вибрация = вырожденный случай волнового уравнения. Доказано field на Q. Это содержательная связь (а не просто перечисление): волна = вибрация + связь между вершинами. Классически это стандартный предел решёточного уравнения, но здесь явно сшивает два файла кластера. _(wave, vibration, bridge, single-vertex)_
- **`vibration_grand_synthesis`** - Капстоун-наблюдение: одно L1-L5 натяжение проявляется в шести доменах (акустика, фонон-КТП, сжатие, вакуум, демпфирование, музыка), собранных в одну конъюнкцию из ранее доказанных лемм. Уровень — синтез/наблюдение, НЕ новая теорема: всё содержание уже доказано в импортируемых файлах, ценность — унификация под один концепт. Честно: каждый домен на конечном Q-инстансе, аналогии физически известны. _(capstone, synthesis, six-domains, unification)_

**Uniqueness - score 3 (new-framing).** Унификация шести физических доменов (волна/фонон/термо/сжатие/вакуум/музыка) под одним концептом L1-L5 натяжения, с машинной сшивкой вибрация=волна-на-одной-вершине и вакуум-не-молчит.
> _Caveat:_ Чистая консолидация ранее доказанного; каждый кирпич (фононы, нулевая энергия, демпфирование) классичен и взят на единичных Q-инстансах. Аналогия 'одно натяжение' — обрамление, не теорема. Заголовок STATUS (11 Qed) совпадает с фактическим.

---

## #16 - `src/acoustics/WavePropagation.v` - score 2 (methods)

**Discrete chain wave equation as oscillation+coupling: causal impulse propagation over Q**

- **Topic.** Defines the 1D leapfrog wave step on a finite chain and shows by exact Q computation that an impulse spreads to its neighbour, the wavefront is causal (further vertices stay at rest one step), zero coupling kills propagation, and larger coupling transfers more.
- **Role.** Second file of the acoustics chain (oscillation -> coupling -> propagation). Self-contained over Q (no ToS imports). Reused by VibrationSynthesis (wave_step appears in vibration_wave_connection and the grand synthesis).
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lia ZArith PeanoNat Lqa
- **E/R/R.** _Elements:_ wave_step, импульс-отклик, фронт волны — конкретные рациональные значения на цепочке из 4 вершин (P4: конечная решётка). _Roles:_ колебание (роль одной вершины) + связь с соседями (роль ребра графа) -> бегущая волна; коэффициент связи c^2 = роль скорости. _Rules:_ delta(v,t+1)=(2-2c^2)*delta(v,t)+c^2*(сосед_лев+сосед_прав)-delta(v,t-1) (= Клейн-Гордон m=0); c^2=0 -> нет переноса. _P4:_ осциллятор один -> вибрация (не звук); связанные осцилляторы на конечном графе -> волна, которая бежит; фронт причинный (за один шаг возмущение доходит только до соседа). Всё на конечной решётке, точные Q-значения.
- **Classical counterpart.** The discrete (leapfrog) wave equation on a 1D chain — equivalently the massless Klein-Gordon / lattice field equation — with finite propagation speed (causal wavefront) and an energy density; all standard numerical wave physics. NEW is only its presentation as 'oscillation + coupling = sound' in the E/R/R chain.
- **Tags.** acoustics, wave-equation, klein-gordon, lattice, causality, methods, P4
- **Notes.** STATUS header says 12 Qed; actual Qed. count = 13 (drift). 0 Admitted, 0 own axioms/Parameters.

**Lemmas (17):**

| name | kind | role |
|---|---|---|
| `wave_step` | Definition | лип-фрог шаг волнового уравнения на цепочке (с краевыми условиями) |
| `impulse` | Definition | начальный импульс: 1 в v=0, иначе 0 |
| `zero_field` | Definition | нулевое поле (предыдущий слой в покое) |
| `wave_v0` | Lemma | источник v=0 после шага = 3/2 |
| `wave_v1` | Lemma | сосед v=1 после шага = 1/4 (возмущение дошло) |
| `impulse_propagates` | Lemma | ★ возмущение доходит до соседа (0 < wave_step ... 1) |
| `wavefront_causal` | Lemma | ★ v=2 ещё в покое за один шаг (причинность фронта) |
| `wavefront_causal_3` | Lemma | v=3 тоже в покое (фронт не обгоняет) |
| `no_coupling_no_propagation` | Lemma | ★ c^2=0 -> сосед остаётся 0 (нет переноса) |
| `no_coupling_source_stays` | Lemma | c^2=0 -> источник = 2 (стоит на месте, без затухания) |
| `energy_density` | Definition | плотность энергии (кинетическая + связь-потенциальная) |
| `energy_at_source` | Lemma | энергия у источника после импульса = 5/8 |
| `energy_zero_ahead` | Lemma | энергия впереди фронта = 0 (волна ещё не дошла) |
| `wave_v1_fast` | Lemma | c^2=1/2: сосед = 1/2 (быстрее) |
| `fast_propagation` | Lemma | c^2=1/2: 0 < перенос к соседу |
| `faster_coupling_more_transfer` | Lemma | ★ большая связь -> больше энергии соседу (1/4 < 1/2) |
| `wave_propagation_synthesis` | Theorem | ★ синтез: распространение + причинность + нет-связи-нет-волны + энергия + скорость |

**Key lemmas (deep):**

- **`wavefront_causal`** - Машинная причинность: за один шаг импульс из v=0 доходит до v=1, но v=2 строго остаётся 0 (vm_compute, точное Q). Это конечно-разностная конечная скорость распространения (домен зависимости лип-фрог-схемы) — корректность 'волна бежит, а не телепортируется'. Классически известно для дискретного волнового уравнения; ценность здесь — явная демонстрация на инстансе в составе цепочки 'колебание+связь=звук'. _(causality, wavefront, finite-speed)_
- **`no_coupling_no_propagation`** - Контрастная пара: при c^2=0 сосед остаётся 0 (нет переноса), при c^2>0 — переносится; faster_coupling_more_transfer ранжирует перенос по величине связи. Это формализует тезис 'волна = колебание + СВЯЗЬ': без связи каждая вершина колеблется отдельно (вибрация), со связью рождается распространение (звук). Стандартная физика решётки, на точных Q-инстансах. _(coupling, propagation, contrast)_

**Uniqueness - score 2 (methods).** Дискретное волновое уравнение на цепочке как 'колебание + связь = распространение', с точной рациональной проверкой причинного фронта, отсутствия переноса без связи и монотонности переноса по связи.
> _Caveat:_ Дискретное волновое уравнение = безмассовый Клейн-Гордон / решёточное поле — полностью классично (та же схема, что LatticeFieldEquations.v, как отмечает заголовок); новизна только в обрамлении и в 0-аксиомной Q-формализации на единичных инстансах. DRIFT: заголовок STATUS заявляет 12 Qed, фактически 13.

