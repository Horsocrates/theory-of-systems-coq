# Database - cluster `light`

_Generated from `light.json` by `generate.ps1` - do not edit by hand; edit the JSON._

**8 files / 79 Qed.** Score distribution: s5=0 / s4=0 / s3=0 / s2=1 / s1=7 / s0=0

---

## #594 - `src/light/ColorSpectrum.v` - score 1 (exposition)

**Color as frequency: edge-mode count over Q**

- **Topic.** Edge-mode counts and frequencies on small graphs, color identified with frequency, white as all modes, blackbody and 'vision as graph Fourier transform'.
- **Role.** Leaf of the light-from-graph branch. Self-contained.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ рёберные моды графа; частоты. _Roles:_ цвет = частота (роль); белый = все моды. _Rules:_ more_vertices_more_colors; color_is_frequency; white_is_all_modes. _P4:_ конечный набор мод графа (Element); цвет как частотная роль.
- **Classical counterpart.** That color corresponds to frequency and white light is a superposition of modes is elementary optics; here only a tiny graph-mode instance (more vertices -> more colors).
- **Tags.** light, color, graph-mode, exposition

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `n_edge_modes/mode_frequency/blackbody/vision_as_GFT` | Definition | моды, частоты, вид как GFT |
| `five_vertices_four_colors/eight_vertices_seven_colors/more_vertices_more_colors` | Theorem | ★ больше вершин — больше цветов |
| `color_is_frequency/white_is_all_modes/color_spectrum_synthesis` | Theorem | цвет=частота; белый=все моды |

**Key lemmas (deep):**

- **`color_is_frequency`** - Цвет отождествлён с частотой рёберной моды графа — простая модельная связь, не вывод физической оптики. Уникальности нет. _(color, frequency, graph-mode)_

**Uniqueness - score 1 (exposition).** Цвет как частота рёберной моды графа; больше вершин — больше цветов.
> _Caveat:_ Цвет=частота — элементарная оптика; графовая модель иллюстративна, не вывод физики.

---

## #595 - `src/light/EdgeField.v` - score 1 (exposition)

**Light as an edge field over Q: oscillation, causal propagation, darkness**

- **Topic.** Edge oscillators on a chain, an impulse, a zero (dark) field, a wave step, edge counts, period-4 oscillation, causal propagation, and that more vertices give more edges.
- **Role.** Leaf of the light-from-graph branch (the field carrier). Self-contained.
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ рёберные осцилляторы; импульс; нулевое поле. _Roles:_ свет = рёберное поле (роль); тьма = нулевое поле. _Rules:_ edge_wave_step; edge_period4; edge_propagates; edge_causal. _P4:_ конечная цепочка рёбер (Element); распространение причинно (конечная скорость).
- **Classical counterpart.** A discrete wave/oscillator on edges with finite propagation speed is a standard lattice model; here only a small Q instance ('light is an edge field', period-4 oscillation, darkness = zero field).
- **Tags.** light, edge-field, wave, exposition

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `n_edges_chain/edge_oscillator/edge_impulse/edge_zero_field/edge_wave_step/darkness` | Definition | рёберное поле, импульс, тьма |
| `edge_count/edge_oscillates/edge_period4/edge_propagates/edge_causal` | Theorem | ★ осцилляция (период 4), причинность |
| `impulse_at_zero/impulse_away/zero_field_is_zero/more_vertices_more_edges/edge_field_synthesis` | Theorem | импульс, нулевое поле, итог |

**Key lemmas (deep):**

- **`edge_causal`** - Распространение рёберной волны причинно (конечная скорость, edge_propagates) — корректное свойство дискретной волны, но это модель, не вывод электродинамики. _(edge-field, causal, wave)_

**Uniqueness - score 1 (exposition).** Свет как рёберное осциллирующее поле над Q: период-4 осцилляция, причинное распространение, тьма=нулевое поле.
> _Caveat:_ Дискретная волна на рёбрах — стандартная решёточная модель; иллюстрация, не физика.

---

## #596 - `src/light/LightGravityConnection.v` - score 1 (exposition)

**Light/gravity over Q: spin-1 vs spin-2, both massless at c**

- **Topic.** Transverse modes in 3D, light spin-1 vs gravity spin-2, edge wave speed, the causal limit, graviton speed, two polarizations, both massless at c, and a Kaluza-Klein hint.
- **Role.** Leaf relating the light and gravity sub-branches. Self-contained.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ поперечные моды; спины 1 и 2. _Roles:_ свет = поперечная роль (spin-1); гравитация = метрическая роль (spin-2). _Rules:_ light_spin_one; gravity_spin_two; both_massless; both_at_c. _P4:_ конечные моды (Element); безмассовость = распространение на причинном пределе.
- **Classical counterpart.** Light is spin-1 and the graviton spin-2, both massless propagating at c with two polarizations; here only a tiny graph-mode analogy (transverse=light, longitudinal=metric, a Kaluza-Klein hint).
- **Tags.** light, gravity, spin, exposition

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `n_transverse_3d/light_spin/gravity_spin/edge_wave_speed_low_k/causal_limit/graviton_speed/two_polarizations` | Definition | поперечные моды, спины, скорости |
| `light_spin_one/gravity_spin_two/both_massless/graviton_at_c/spin_difference` | Theorem | ★ спин-1 vs спин-2, оба безмассовы |
| `transverse_is_light/longitudinal_is_metric/kaluza_klein_hint/light_gravity_synthesis` | Theorem | поперечное=свет; продольное=метрика |

**Key lemmas (deep):**

- **`both_massless`** - Свет и гравитон оба безмассовы и движутся на причинном пределе c — модельная аналогия спинов 1/2, не вывод. Иллюстративна. _(spin, massless, graviton)_

**Uniqueness - score 1 (exposition).** Свет (spin-1) и гравитон (spin-2) над Q: оба безмассовы на причинном пределе, поперечное=свет / продольное=метрика.
> _Caveat:_ Спины и безмассовость света/гравитона — известная физика; графовая аналогия иллюстративна, не вывод.

---

## #597 - `src/light/LightSynthesis.v` - score 1 (exposition)

**Light synthesis: edge field, polarization, Maxwell, causal speed (summary node)**

- **Topic.** An 8-lemma grand synthesis tying the light leaves: light is an edge field, has polarization, propagates at the causal speed, obeys Maxwell, conserves energy, darkness is zero.
- **Role.** Summary node of the light branch. Self-contained.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ сводимые результаты ветви света. _Roles:_ узел-синтез ветви света. _Rules:_ light_is_edge_field; light_obeys_maxwell; light_speed_is_causal. _P4:_ агрегатор конечных результатов соседних файлов (Element).
- **Classical counterpart.** A summary node asserting light is an edge field obeying Maxwell, with polarization, causal speed and energy conservation — all proven in the sibling leaves.
- **Tags.** light, summary, exposition

**Lemmas (2):**

| name | kind | role |
|---|---|---|
| `light_is_edge_field/light_has_polarization/light_speed_is_causal/light_obeys_maxwell` | Theorem | свет=поле, поляризация, скорость, Максвелл |
| `light_propagates_causally/light_energy_conserved/light_darkness_is_zero/light_grand_synthesis` | Theorem | причинность, сохранение энергии, итог |

**Key lemmas (deep):**

- **`light_grand_synthesis`** - Узел-агрегатор ветви света; собственного содержания не несёт — собирает результаты EdgeField/MaxwellFromGraph/Polarization. _(summary, light)_

**Uniqueness - score 1 (exposition).** Сводка ветви света: рёберное поле, поляризация, причинная скорость, Максвелл, сохранение энергии.
> _Caveat:_ Чистый узел-агрегатор; собственного результата нет.

---

## #598 - `src/light/MaxwellFromGraph.v` - score 2 (methods)

**Maxwell from a graph over Q: discrete Gauss/Faraday/wave (a framing)**

- **Topic.** Magnetic field from electric, a discrete Gauss law (zero/positive charge), discrete magnetic divergence, antisymmetric curl, Faraday's law, the wave equation from Maxwell, charge as source, and 'Maxwell not postulated'.
- **Role.** Central leaf of the light-from-graph branch; the 'derivation' claim. Self-contained.
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ поля E,B на графе; заряд как источник. _Roles:_ уравнения Максвелла = роли (Гаусс, Фарадей, волна) на графе. _Rules:_ gauss_electric_sum; curl_antisymmetric; faraday; wave_from_maxwell. _P4:_ дискретный векторный анализ на конечном графе (Element); «Максвелл не постулируется» = переобрамление, не физический вывод.
- **Classical counterpart.** Maxwell's equations as discrete vector calculus (graph div/curl, Gauss, Faraday, wave equation) is the standard discrete-exterior-calculus picture; the framing 'Maxwell not postulated but derived from a graph' is a re-casting, not a new physical derivation.
- **Tags.** light, maxwell, discrete-calculus, over-branded, methods

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `magnetic_from_electric/gauss_electric_sum/gauss_zero_no_charge/gauss_positive_charge` | Definition/Theorem | закон Гаусса на графе |
| `magnetic_zero_uniform/magnetic_nonzero_curl/curl_antisymmetric_concrete/_concrete2/gauss_three_edges` | Theorem | ★ антисимметричный curl, магнитная дивергенция |
| `faraday/wave_from_maxwell/maxwell_not_postulated/charge_as_source/maxwell_from_graph_synthesis` | Theorem | ★ Фарадей, волна, заряд-источник |

**Key lemmas (deep):**

- **`wave_from_maxwell`** - Волновое уравнение получается из дискретных Максвелла на графе — корректная дискретно-векторная конструкция (DEC). Но это переобрамление известного, а не вывод физической электродинамики; caveat честно это фиксирует. _(maxwell, wave, discrete-calculus, framing)_
- **`maxwell_not_postulated`** - Заявка «Максвелл не постулируется, а следует из графа» — на деле дискретный векторный анализ (div/curl на рёбрах). Это OVER-BRANDED формулировка; реально доказано лишь дискретное тождество, не физическая необходимость уравнений. _(over-branded, framing, honest-caveat)_

**Uniqueness - score 2 (methods).** Уравнения Максвелла как дискретный векторный анализ на графе над Q: Гаусс, антисимметричный curl, Фарадей, волновое уравнение.
> _Caveat:_ Это стандартная дискретная экстерьерная алгебра; формулировка «Максвелл выведен из графа» OVER-BRANDED — доказаны дискретные тождества, не физическая необходимость.

---

## #599 - `src/light/Polarization.v` - score 1 (exposition)

**Polarization and Malus's law over Q**

- **Topic.** Polarized energy, horizontal/vertical polarization, Malus's law, polarizer halves unpolarized light, crossed polarizers block, Malus at aligned/crossed/45 degrees, orthogonal polarizations.
- **Role.** Leaf of the light branch. Self-contained.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ поляризованные состояния; энергия. _Roles:_ поляризатор = роль-проектор; закон Малюса как роль-затухание. _Rules:_ polarizer_halves; crossed_block; malus_aligned/crossed/45. _P4:_ конечные значения над Q (Element); Малюс как cos²-правило.
- **Classical counterpart.** Polarization states and Malus's law (I = I0 cos^2 theta) are elementary optics; here only a small Q instance (polarizer halves unpolarized, crossed blocks, Malus at 0/45/90).
- **Tags.** light, polarization, malus, exposition

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `polarized_energy/h_polarize/v_polarize/malus` | Definition | поляризация, Малюс |
| `h_polarized_energy/v_polarized_energy/unpolarized_energy/polarizer_halves/crossed_block` | Theorem | ★ поляризатор делит, скрещённые блокируют |
| `malus_aligned/malus_crossed/malus_45_approx/orthogonal_polarizations/polarization_synthesis` | Theorem | закон Малюса при разных углах |

**Key lemmas (deep):**

- **`polarizer_halves`** - Поляризатор пропускает половину неполяризованного света (crossed_block при скрещивании) — корректная Q-формализация закона Малюса. Учебная оптика. _(polarization, malus)_

**Uniqueness - score 1 (exposition).** Поляризация и закон Малюса над Q: поляризатор делит пополам, скрещённые блокируют, cos²-зависимость.
> _Caveat:_ Закон Малюса — элементарная оптика; Q-инстанс без нового содержания.

---

## #600 - `src/light/RefractionDiffraction.v` - score 1 (exposition)

**Refraction and diffraction over Q: Fresnel coefficients, R+T=1**

- **Topic.** Reflection/transmission coefficients, no reflection at matched impedance, concrete reflection values, full reflection at large mismatch, R+T energy conservation, total internal reflection, diffraction.
- **Role.** Leaf of the light branch. Self-contained.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ коэффициенты отражения/прохождения; импедансы. _Roles:_ граница раздела = роль; R,T как роли-доли энергии. _Rules:_ reflection_coeff/transmission_coeff; energy_conserved (R+T=1); total_internal_reflection. _P4:_ конечные коэффициенты над Q (Element); R+T=1 как точное тождество.
- **Classical counterpart.** Fresnel reflection/transmission coefficients, energy conservation R+T=1, total internal reflection and diffraction are standard wave optics; here only a small Q instance.
- **Tags.** light, refraction, fresnel, exposition

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `reflection_coeff/transmission_coeff/no_reflection_matched` | Definition/Theorem | коэффициенты Френеля |
| `reflection_1_2/_1_3/full_reflection_large_mismatch/transmission_complement` | Theorem | значения, полное отражение |
| `energy_conserved/reflection_symmetric/total_internal_reflection/diffraction/refraction_diffraction_synthesis` | Theorem | ★ R+T=1, полное внутреннее отражение |

**Key lemmas (deep):**

- **`energy_conserved`** - Сохранение энергии R+T=1 на границе раздела как точное Q-тождество — корректная формализация Френеля. Учебная волновая оптика. _(fresnel, energy-conservation)_

**Uniqueness - score 1 (exposition).** Преломление/дифракция над Q: коэффициенты Френеля, R+T=1, полное внутреннее отражение.
> _Caveat:_ Коэффициенты Френеля — стандартная волновая оптика; Q-инстанс без нового содержания.

---

## #601 - `src/light/SpeedOfLight.v` - score 1 (exposition)

**Speed of light over Q: c as a graph property, dispersion**

- **Topic.** The causal limit, edge/vertex wave speeds, massless (linear) vs massive (sub-c) dispersion, heavier is slower, c as a graph property, and 'why nothing is faster'.
- **Role.** Leaf of the light branch (kinematics). Self-contained.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ дисперсионные соотношения; скорости волн. _Roles:_ c = причинный предел графа (роль); масса как роль-замедление. _Rules:_ dispersion_massless (линейная); massive_slower; c_is_graph_property. _P4:_ конечные скорости над Q (Element); c как структурный предел графа.
- **Classical counterpart.** A dispersion relation with a maximal propagation speed (massless linear, massive slower) is a standard lattice picture; here the framing 'c is a graph property / why nothing is faster' is a re-casting.
- **Tags.** light, speed-of-light, dispersion, exposition

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `causal_limit/edge_wave_speed_low_k/vertex_wave_speed_approx/dispersion_massless/dispersion_massive_sq` | Definition | дисперсия, причинный предел |
| `edge_at_c/massive_slower/massless_at_c/speed_ratio/heavier_is_slower` | Theorem | ★ безмассовое на c, массивное медленнее |
| `massless_dispersion_linear/massive_dispersion_bigger/c_is_graph_property/why_nothing_faster/speed_of_light_synthesis` | Theorem | c как свойство графа |

**Key lemmas (deep):**

- **`c_is_graph_property`** - Скорость света отождествлена с причинным пределом графа; безмассовые моды движутся на c, массивные медленнее (heavier_is_slower) — корректная дисперсия дискретной модели. Формулировка «почему ничего не быстрее» — переобрамление, не вывод СТО. _(speed-of-light, dispersion, framing)_

**Uniqueness - score 1 (exposition).** c как причинный предел графа над Q: безмассовая линейная дисперсия на c, массивные моды медленнее.
> _Caveat:_ Дисперсия с максимальной скоростью — стандартная решётка; формулировка «c из графа» иллюстративна, не вывод СТО.

