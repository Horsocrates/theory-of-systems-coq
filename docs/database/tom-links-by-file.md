# База связей «том ↔ формализация» — по файлам

_Сгенерировано из `tom-links.json` скриптом `tom-links-generate.cjs`; руками не править — правится JSON._

**Файлов формализации, названных в проверенных главах: 50; записей с файлом: 465.**

| # | файл | записей | глав | расхождений |
|---|---|---|---|---|
| 29 | `src/analysis/BolzanoWeierstrass.v` | 1 | 1 | 1 |
| 61 | `src/analysis/Sqrt2Irrational.v` | 2 | 1 | 0 |
| 66 | `src/Archimedean_ERR.v` | 1 | 1 | 0 |
| 83 | `src/CauchyProcessBridge.v` | 12 | 4 | 0 |
| 84 | `src/CauchyReal.v` | 41 | 3 | 0 |
| 94 | `src/Countability_Q.v` | 3 | 2 | 0 |
| 136 | `src/EVT_idx.v` | 3 | 3 | 0 |
| 228 | `src/foundation/Distinction.v` | 1 | 1 | 0 |
| 342 | `src/foundation/P4_Eliminates_AC.v` | 7 | 1 | 0 |
| 343 | `src/foundation/P4_Eliminates_ATR.v` | 2 | 1 | 0 |
| 344 | `src/foundation/P4_Eliminates_Infinity.v` | 5 | 1 | 0 |
| 345 | `src/foundation/P4_Eliminates_Pi11.v` | 3 | 1 | 0 |
| 346 | `src/foundation/P4CompletedInfinity.v` | 8 | 1 | 0 |
| 347 | `src/foundation/P4ProhibitionSynthesis.v` | 6 | 1 | 0 |
| 348 | `src/foundation/P4ProhibitsAC.v` | 7 | 1 | 0 |
| 349 | `src/foundation/P4ProhibitsImpredicative.v` | 1 | 1 | 0 |
| 550 | `src/HeineBorel_ERR.v` | 4 | 2 | 0 |
| 559 | `src/IVT_CauchyReal.v` | 2 | 2 | 0 |
| 560 | `src/IVT_ERR.v` | 3 | 3 | 0 |
| 704 | `src/process/ProcessArithmetic.v` | 23 | 3 | 0 |
| 706 | `src/process/ProcessAxiomAudit.v` | 16 | 2 | 0 |
| 712 | `src/process/ProcessBinReal.v` | 8 | 2 | 0 |
| 717 | `src/process/ProcessBounds.v` | 6 | 1 | 0 |
| 718 | `src/process/ProcessBridge.v` | 11 | 2 | 0 |
| 719 | `src/process/ProcessBW.v` | 1 | 1 | 0 |
| 734 | `src/process/ProcessCore.v` | 23 | 6 | 0 |
| 749 | `src/process/ProcessDerivedVsConsistent.v` | 8 | 1 | 0 |
| 796 | `src/process/ProcessFourPrinciples.v` | 20 | 3 | 0 |
| 852 | `src/process/ProcessIVT.v` | 1 | 1 | 0 |
| 872 | `src/process/ProcessLimitColimit.v` | 2 | 1 | 0 |
| 888 | `src/process/ProcessNinePoint.v` | 19 | 2 | 0 |
| 897 | `src/process/ProcessOpenQuestions.v` | 1 | 1 | 0 |
| 1006 | `src/process/ProcessUncountable.v` | 19 | 3 | 0 |
| 1035 | `src/ProcessContinuumHypothesis.v` | 43 | 8 | 0 |
| 1036 | `src/ProcessDiagonal.v` | 16 | 4 | 0 |
| 1037 | `src/ProcessGeneral.v` | 14 | 2 | 0 |
| 1038 | `src/ProcessTypes.v` | 19 | 2 | 0 |
| 1047 | `src/RealField.v` | 6 | 2 | 0 |
| 1868 | `src/RealFieldApart.v` | 6 | 1 | 0 |
| 1049 | `src/RealPointSetoid.v` | 7 | 2 | 0 |
| 1050 | `src/RealPointTopology.v` | 3 | 1 | 0 |
| 1059 | `src/settheory/CantorBendixsonFull.v` | 1 | 1 | 0 |
| 1062 | `src/settheory/ChoicePriceMap.v` | 3 | 1 | 0 |
| 1064 | `src/settheory/HigmanLemma.v` | 1 | 1 | 1 |
| 1065 | `src/settheory/KruskalFull.v` | 2 | 1 | 0 |
| 1066 | `src/settheory/KruskalTree.v` | 3 | 2 | 0 |
| 1068 | `src/ShrinkingIntervals_ERR.v` | 53 | 12 | 0 |
| 1610 | `src/stdlib/RefinementSqrt.v` | 1 | 1 | 0 |
| 1789 | `src/TheoryOfSystems_Core_ERR.v` | 2 | 2 | 0 |
| 1793 | `src/ToS_Axioms.v` | 15 | 4 | 0 |

---

## #29 — `src/analysis/BolzanoWeierstrass.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ |  |  | V.2 Топология и компактность, стр. 1016 | не проверено | 12.11 не проверялось; очередь — аудит Части V |

---

## #61 — `src/analysis/Sqrt2Irrational.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ | файл |  | IV.6 P4 как фильтр, стр. 268 | верно | упоминание файла; проверено существование |
| `no_rational_sqrt2` (200) | Theorem | Closed under the global context | IV.6 P4 как фильтр, стр. 268 | верно | все 14 объявлений Sqrt2Irrational.v — «Closed under the global context» |

---

## #66 — `src/Archimedean_ERR.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ |  |  | V.3 Непрерывность, стр. 643 | верно | исправлено 12.11; сверена цена; формулировка — при аудите части; в файле нет объявлений Axiom и Parameter |

---

## #83 — `src/CauchyProcessBridge.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ | файл |  | IV.2 RealProcess как тип, стр. 271, 326, 576, 594 | верно | упоминание файла; проверено существование |
| _файл целиком_ | файл |  | IV.3 Точка как класс эквивалентности процессов, стр. 575 | верно | упоминание файла; проверено существование |
| `is_Cauchy_iff_is_cauchy` (47) | Lemma | Closed under the global context | IV.2 RealProcess как тип, стр. 580, 590, 1071 | верно | исправлено 12.11 (шаг 7, слово автора): было «Файл `ProcessGeneral.v` проводит между ними мост»; в ProcessGeneral.v нет is_Cauchy; мост is_Cauchy ↔ is_cauchy — лемма is_Cauchy_iff_is_cauchy (CauchyProcessBridge.v:47), как глава и пишет в § 2.5 |
| `is_Cauchy_iff_is_cauchy` (47) | Lemma | Closed under the global context | IV.2 RealProcess как тип, стр. 580, 590, 1071 | верно | CauchyProcessBridge.v:47–48: forall R, is_Cauchy R <-> is_cauchy R; доказательство — split; intro H; exact H (определения совпадают); допущений нет. |
| `is_Cauchy_iff_is_cauchy` (47) | Lemma | Closed under the global context | IV.2 RealProcess как тип, стр. 580, 590, 1071 | верно | исправлено 12.11 (шаг 7, слово автора): было «…, но первая и вторая линии не отождествлены машинно как единый терм» — оговорка, которую § 2.5.4 той же главы объявляет снятой; мосты is_Cauchy_iff_is_cauchy (CauchyProcessBridge.v:47) и process_equiv_iff_cauchy_equiv (:58) доказаны |
| `is_Cauchy_iff_is_cauchy` (47) | Lemma | Closed under the global context | IV.4 Несчётность процессов, стр. 604 | верно | исправлено 12.11 (шаг 11, слово автора «А»): было «мост, как мост между is_Cauchy и is_cauchy в Главе 4.2» — сравнение неточно; мост Главы 4.2 (is_Cauchy_iff_is_cauchy, CauchyProcessBridge.v:47) доказан развёрткой, определения совпадают буква в букву; мост этой главы (si_cauchy_compat, ProcessUncountable.v) — равносильность строгого и нестрогого рубежа, доказанная в обе стороны сдвигом рубежа |
| `to_CauchySeq` (51) | Definition | Closed under the global context | IV.2 RealProcess как тип, стр. 584 | верно | упоминание имени (Definition); проверено существование |
| `process_equiv_iff_cauchy_equiv` (58) | Lemma | Closed under the global context | IV.2 RealProcess как тип, стр. 583 | верно | CauchyProcessBridge.v:58 (для R1, R2 с доказательствами is_Cauchy), :51 (to_CauchySeq R H := mkCauchy R H); допущений нет. |
| `process_mul` (69) | Definition | Closed under the global context | IV.2 RealProcess как тип, стр. 324, 593, 927, 1081 | верно | CauchyProcessBridge.v: mul_preserves_Cauchy :74, process_mul_compat :82, а также process_mul_comm :95 и process_mul_assoc :102; все 7 лемм файла без допущений. |
| `process_mul` (69) | Definition | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 574 | верно | CauchyProcessBridge.v:69: поточечное произведение процессов; сохранение свойства Коши — mul_preserves_Cauchy (:74). |
| `mul_preserves_Cauchy` (74) | Lemma | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 157 | верно | исправлено 12.11 правкой формализации (шаг 1, слово автора «А»): второй пункт предиката теперь is_Cauchy (process_mul R1 R2) — замкнутость относительно умножения (ProcessFourPrinciples.v; лемма mul_preserves_Cauchy, CauchyProcessBridge.v:74); слова главы верны как есть. Было: пункт о паре процессов (process_product). |
| `mul_preserves_Cauchy` (74) | Lemma | Closed under the global context | IV.2 RealProcess как тип, стр. 325 | верно | CauchyProcessBridge.v:69 (process_mul), :74 (лемма); допущений нет. |

---

## #84 — `src/CauchyReal.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| `cs_seq` | внешнее | не применимо (поле записи CauchySeq) | IV.2 RealProcess как тип, стр. 426, 465 | верно | CauchyReal.v:49: поле объявлено как cs_seq :> nat -> Q. |
| _файл целиком_ |  |  | IV.2 RealProcess как тип, стр. 487 | верно | Шапка CauchyReal.v:2: «CAUCHY REALS: CONSTRUCTIVE COMPLETION OF Q». |
| _файл целиком_ |  |  | IV.2 RealProcess как тип, стр. 496 | верно | Верно: фактортипа в файле нет; глава точнее шапки файла, где цель записана как «Define real numbers as equivalence classes» (CauchyReal.v:6). |
| _файл целиком_ |  |  | IV.2 RealProcess как тип, стр. 525 | верно | Импорты CauchyReal.v:25–30 — только стандартная библиотека. |
| _файл целиком_ |  |  | IV.2 RealProcess как тип, стр. 792 | верно | Все 19 лемм и теорем CauchyReal.v — «Closed under the global context»; слова classic в файле нет, импорты только стандартной арифметики. |
| _файл целиком_ |  |  | IV.2 RealProcess как тип, стр. 855 | верно | Статус честный; наблюдение: в src/Completeness.v есть частичный шаг к ней — diagonal_converges (:464, без допущений): последовательность CauchySeq с равномерным условием meta_cauchy (:421) сходится к диагональному пределу; глава этот файл не называет. |
| _файл целиком_ |  |  | IV.2 RealProcess как тип, стр. 861 | верно | cauchy_rational_approx, cauchy_complete_self и добавленные шагом 6 cauchy_complete_self_lower, cauchy_complete_self_two_sided — «Closed under the global context», как и остальные леммы файла. |
| _файл целиком_ |  |  | IV.2 RealProcess как тип, стр. 1088 | верно | В CauchyReal.v нет Axiom и Admitted; все 19 доказанных утверждений — «Closed under the global context». |
| _файл целиком_ |  |  | IV.2 RealProcess как тип, стр. 1105 | верно | исправлено 12.11 (шаг 7, слово автора): было 18; после шага 6 в файле 21 Qed (4 Theorem + 17 Lemma), 0 Admitted, 0 Axiom; название шапки приведено верно |
| _файл целиком_ |  |  | IV.3 Точка как класс эквивалентности процессов, стр. 183 | верно | Notation "a ~~ b" := (cauchy_equiv a b) — CauchyReal.v:63 (область cauchy_scope). |
| _файл целиком_ |  |  | IV.3 Точка как класс эквивалентности процессов, стр. 329 | верно | В CauchyReal.v леммы о разбиении на классы действительно нет (в файле refl/sym/trans, строки 67–91); статус следствия назван честно. |
| _файл целиком_ |  |  | IV.3 Точка как класс эквивалентности процессов, стр. 389 | верно | Сверено со списком объявлений CauchyReal.v: CauchySeq (:48), cauchy_equiv (:57), три леммы эквивалентности; типа классов нет. |
| `is_cauchy` (43) | Definition | Closed under the global context | IV.2 RealProcess как тип, стр. 218, 266, 454, 543, 565, 574, 577, 590 | верно | Словесная формулировка (стр. 213–216) и блок кода (стр. 221) совпадают с CauchyReal.v:43. |
| `is_cauchy` (43) | Definition | Closed under the global context | IV.4 Несчётность процессов, стр. 605 | верно | упоминание имени (Definition); проверено существование; объявлений с таким именем 3 (по Locate в окружении файлов главы) |
| `CauchySeq` (48) | Record | Closed under the global context | IV.2 RealProcess как тип, стр. 416, 425, 432, 435, 436, 440, 445, 449 | верно | Блок кода (стр. 419) совпадает с CauchyReal.v:48; поля cs_seq, cs_cauchy и конструктор mkCauchy названы верно. |
| `CauchySeq` (48) | Record | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 13, 20, 24, 64, 130, 227, 232, 239 | верно | Record CauchySeq := mkCauchy { cs_seq; cs_cauchy : is_cauchy cs_seq } (CauchyReal.v:48) — процесс вместе с доказательством сходимости, как сказано. |
| `CauchySeq` (48) | Record | Closed under the global context | IV.4 Несчётность процессов, стр. 673 | верно | упоминание имени (Record); проверено существование |
| `cauchy_equiv` (57) | Definition | Closed under the global context | IV.2 RealProcess как тип, стр. 442, 498, 659, 681, 719, 793, 1038, 1054 | верно | Блок кода (стр. 662) совпадает с CauchyReal.v:57; знак a ~~ b — Notation на CauchyReal.v:63. |
| `cauchy_equiv` (57) | Definition | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 16, 41, 77, 172, 190, 202, 225, 229 | верно | Блок кода (стр. 175–178) совпадает с CauchyReal.v:57; словесное чтение (для всякой тесноты eps найдётся рубеж N) соответствует кванторам. |
| `cauchy_equiv` (57) | Definition | Closed under the global context | IV.4 Несчётность процессов, стр. 13, 21, 674 | верно | упоминание имени (Definition); проверено существование |
| `cauchy_equiv_refl` (67) | Lemma | Closed under the global context | IV.2 RealProcess как тип, стр. 677 | верно | CauchyReal.v:67: forall a, a ~~ a; допущений нет. |
| `cauchy_equiv_refl` (67) | Lemma | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 220, 331, 399 | верно | CauchyReal.v:67: forall a, a ~~ a; доказательство — разность нулевая, как в главе. |
| `cauchy_equiv_sym` (78) | Lemma | Closed under the global context | IV.2 RealProcess как тип, стр. 678 | верно | CauchyReal.v:78: a ~~ b -> b ~~ a; допущений нет. |
| `cauchy_equiv_sym` (78) | Lemma | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 220, 332 | верно | CauchyReal.v:78: a ~~ b -> b ~~ a; в доказательстве Qabs_opp — то самое \|−x\| = \|x\|. |
| `cauchy_equiv_trans` (91) | Lemma | Closed under the global context | IV.2 RealProcess как тип, стр. 679 | верно | CauchyReal.v:91: a ~~ b -> b ~~ c -> a ~~ c; допущений нет. |
| `cauchy_equiv_trans` (91) | Lemma | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 221, 332 | верно | CauchyReal.v:91: a ~~ b -> b ~~ c -> a ~~ c; в доказательстве Qabs_triangle и eps * (1#2) — как в главе. |
| `cauchy_add` (141) | Definition | Closed under the global context | IV.2 RealProcess как тип, стр. 523, 695 | верно | упоминание имени (Definition); проверено существование |
| `cauchy_neg` (157) | Definition | Closed under the global context | IV.2 RealProcess как тип, стр. 695 | верно | упоминание имени (Definition); проверено существование |
| `cauchy_sub` (160) | Definition | Closed under the global context | IV.2 RealProcess как тип, стр. 696 | верно | Мелкая неточность, не расхождение: cauchy_add, cauchy_neg, cauchy_const определены через mkCauchy (CauchyReal.v:141, :157, :173), а cauchy_sub — как cauchy_add a (cauchy_neg b) (:160), то есть через mkCauchy опосредованно. |
| `cauchy_const` (173) | Definition | Closed under the global context | IV.2 RealProcess как тип, стр. 696 | верно | cauchy_const существует (CauchyReal.v:173); но доказанная теорема о 0,999… записана на первой линии, через const_process 1 — см. запись о nine_equiv_one. |
| `cauchy_const` (173) | Definition | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 614 | верно | cauchy_const есть (CauchyReal.v:173); теорема nine_equiv_one сформулирована с const_process 1 (линия ProcessCore) — глава оговаривает это в § 3.7.5. |
| `cauchy_add_compat` (180) | Lemma | Closed under the global context | IV.2 RealProcess как тип, стр. 709 | верно | CauchyReal.v:180; блок кода (стр. 703) совпадает; допущений нет. |
| `cauchy_add_compat` (180) | Lemma | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 517, 558, 795, 825, 936 | верно | CauchyReal.v:180; блок кода (стр. 511) совпадает с исходником. |
| `cauchy_add_compat` (180) | Lemma | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 517, 558, 795, 825, 936 | верно | исправлено 12.11 (шаг 10, слово автора): было сокращение `add_compat`; полное имя — cauchy_add_compat (CauchyReal.v:180) |
| `cauchy_neg_compat` (203) | Lemma | Closed under the global context | IV.2 RealProcess как тип, стр. 710 | верно | CauchyReal.v:203; блок кода (стр. 705) совпадает; допущений нет. |
| `cauchy_neg_compat` (203) | Lemma | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 518, 558, 795, 936 | верно | CauchyReal.v:203; блок кода (стр. 513) совпадает с исходником. |
| `cauchy_le` (226) | Definition | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 531, 540, 550, 550, 555 | верно | CauchyReal.v:226: forall eps > 0, exists N, forall n >= N, a n < b n + eps. |
| `cauchy_le_of_equiv` (231) | Lemma | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 532 | верно | CauchyReal.v:231: a ~~ b -> cauchy_le a b; блок кода (стр. 535) совпадает; обратная сторона — через cauchy_equiv_sym. |
| `cauchy_rational_approx` (287) | Theorem | Closed under the global context | IV.2 RealProcess как тип, стр. 837, 854 | верно | CauchyReal.v:287: в формулировке стоит «exists q : Q»; то, что q — собственное приближение, видно из доказательства (exists (cs_seq a N), :294); допущений нет. |
| `cauchy_complete_self` (300) | Theorem | Closed under the global context | IV.2 RealProcess как тип, стр. 840, 855 | верно | верхняя сторона: cauchy_le (cauchy_sub a (cauchy_const (a n))) (cauchy_const eps) (CauchyReal.v:300); двусторонняя форма — cauchy_complete_self_two_sided (шаг 6, 12.11); допущений нет |
| `cauchy_complete_self_two_sided` (345) | Theorem | Closed under the global context | IV.2 RealProcess как тип, стр. 841 | верно | исправлено 12.11 (шаг 6, слово автора «А») — правка формализации: в CauchyReal.v добавлены cauchy_complete_self_lower (нижняя сторона: cauchy_le (cauchy_sub (cauchy_const (a n)) a) (cauchy_const eps)) и cauchy_complete_self_two_sided (обе стороны при одном N); прежняя cauchy_complete_self давала только верхнюю оценку; на странице добавлено имя двусторонней теоремы; Print Assumptions: Closed under the global context |

---

## #94 — `src/Countability_Q.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ | файл |  | IV.6 P4 как фильтр, стр. 268 | верно | упоминание файла; проверено существование |
| _файл целиком_ |  |  | X.2 Счётность конструктивна; несчётность — правило о процессах, стр. 29 | верно | в файле нет импорта классического модуля (шапка: «AXIOMS: NONE»); теоремы файла — при аудите Части X |
| `enum_surjective` (450) | Theorem | Closed under the global context | IV.6 P4 как фильтр, стр. 268 | верно | все 46 объявлений Countability_Q.v — «Closed under the global context»; в том же файле теперь и полная биекция для всего ℚ (Q_bijection) |

---

## #136 — `src/EVT_idx.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| `EVT_strong_process` (663) | Theorem | Axioms: EVT_idx.classic : forall P : Prop, P \/ ~ P | V.3 Непрерывность, стр. 983, 1128 | верно | цена сверена при заведении базы (12.11 не проверялось): аксиома `EVT_idx.classic`, объявленная в самом файле; формулировка — при аудите Части V |
| `EVT_strong_process` (663) | Theorem | Axioms: EVT_idx.classic : forall P : Prop, P \/ ~ P | Направления/Математика/index, стр. 96 | верно | цена сверена при заведении базы (12.11 не проверялось): `EVT_idx.classic` |
| `EVT_strong_process` (663) | Theorem | Axioms: EVT_idx.classic : forall P : Prop, P \/ ~ P | Формализация, стр. 104, 134 | верно | цена сверена при заведении базы (12.11 не проверялось): `EVT_idx.classic`; формулировка — при аудите Части V |

---

## #228 — `src/foundation/Distinction.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| `classic` (36) | Axiom | Axioms: Distinction.classic : forall P : Prop, P \/ ~ P | IV.1 P4 бесконечность как процесс, стр. 298, 309, 312, 360, 361, 362, 365, 1106 | верно | сомнительное: перечень неполон — classic переобъявлена в трёх файлах (foundation/Distinction.v:36, EVT_idx.v:338, settheory/BorelDeterminacy.v:21), а в допущениях девяти лемм стоит ещё аксиома стандартной библиотеки functional_extensionality_dep (ProcessWholeness.v:274, 283; DependentSystems.v:106; Conversion.v:127; stdlib/GameTheory.v:84, 91, 103; foundation/Ordinal.v:81, 92) |

---

## #342 — `src/foundation/P4_Eliminates_AC.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ |  |  | IV.1 P4 бесконечность как процесс, стр. 719 | верно | finite_choice (:47), finite_zorn (:124), P4_eliminates_AC_finite (:217); finite_choice_fn — голова списка (L5_choose, :25, :36) |
| `family` | внешнее |  | IV.1 P4 бесконечность как процесс, стр. 726, 1378, 1378, 1378 | верно | не объявление, а имя связанной переменной в формулировках P4_eliminates_AC (:201) и P4_eliminates_AC_finite (:217) |
| _файл целиком_ |  |  | IV.1 P4 бесконечность как процесс, стр. 1377 | верно | верно: 15 Qed, все объявления замкнуты (шапка файла называет 16 Qed — число в сноске не приводится) |
| `P4_eliminates_AC` (201) | Theorem | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 725 | верно | Theorem P4_eliminates_AC (:201): forall family, (forall i, family i <> nil) -> exists f, forall i, In (f i) (family i); заметка в файле о двух чтениях — :191–195 |
| `P4_eliminates_AC` (201) | Theorem | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 861 | верно | Theorem P4_eliminates_AC (:201); двоякое чтение (правило или график) записано в самом файле (:191–195) |
| `P4_eliminates_AC_finite` (217) | Theorem | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 859, 1378 | верно | forall family N, (forall i, i < N -> family i <> nil) -> forall i, i < N -> In (finite_choice_fn family i) (family i) (:217) |
| `P4_eliminates_AC_finite` (217) | Theorem | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 859, 1378 | верно | формулировка сноски совпадает с утверждением (:217) |

---

## #343 — `src/foundation/P4_Eliminates_ATR.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ |  |  | IV.1 P4 бесконечность как процесс, стр. 734 | верно | Inductive Ord: OZero, OSucc, OLim (:21–24); Fixpoint CB_transfinite (:43) — структурная рекурсия по Ord |
| _файл целиком_ |  |  | IV.1 P4 бесконечность как процесс, стр. 1379 | верно | исправлено 12.11 (шаг 5, слово автора): было 15; в файле 17 Qed (16 лемм и 1 теорема); шапка файла исправлена тем же шагом (15 → 17) |

---

## #344 — `src/foundation/P4_Eliminates_Infinity.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ |  |  | IV.1 P4 бесконечность как процесс, стр. 702 | верно | nat_induction_works, partial_sum, converges, strong_induction, factorial, finite_list_bounded — все есть в файле |
| _файл целиком_ |  |  | IV.1 P4 бесконечность как процесс, стр. 765 | верно | в P4_Eliminates_Infinity.v, P4_Eliminates_AC.v, P4_Eliminates_ATR.v нет ни Axiom, ни Parameter; все их объявления — «Closed under the global context» |
| _файл целиком_ |  |  | IV.1 P4 бесконечность как процесс, стр. 908 | верно | исправлено 12.11 (шаг 3, слово автора): было «и подтверждено аудитом ProcessAxiomAudit.v»; сплошной прогон Print Assumptions после правок 2026-11-12: в P4_Eliminates_Infinity.v, P4_Eliminates_AC.v, P4_Eliminates_ATR.v все объявления замкнуты; в P4_Eliminates_Pi11.v 16 объявлений стоят на параметре eval_program (абстрактная функция вычисления программ — не аксиома бесконечности и не аксиома выбора), лемма pi11_negation — ещё и на classic |
| _файл целиком_ |  |  | IV.1 P4 бесконечность как процесс, стр. 1376 | верно | исправлено 12.11 (шаг 5, слово автора): было 12; в файле 10 Qed (9 лемм и 1 теорема); шапка файла исправлена тем же шагом (12 → 10) |
| `P4_eliminates_Infinity` (79) | Theorem | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 705 | верно | четыре конъюнкта: индукция; forall n, n < S n; factorial 5 = 120; partial_sum (fun n => n) 3 = 6 (:79) |

---

## #345 — `src/foundation/P4_Eliminates_Pi11.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ |  |  | IV.1 P4 бесконечность как процесс, стр. 1380 | верно | 15 Qed; Parameter eval_program (:28) |
| `eval_program` (28) | Parameter | Axioms: P4_Eliminates_Pi11.eval_program : P4_Eliminates_Pi11.Program -> nat -> nat | IV.1 P4 бесконечность как процесс, стр. 749, 760 | верно | Parameter eval_program : Program -> nat -> nat (:28); P4_forall_functions — квантор по кодам (:35) |
| `eval_program` (28) | Parameter | Axioms: P4_Eliminates_Pi11.eval_program : P4_Eliminates_Pi11.Program -> nat -> nat | IV.1 P4 бесконечность как процесс, стр. 749, 760 | верно | Parameter без определения; все теоремы файла, говорящие о кодах, несут его в выводе Print Assumptions, pi11_negation (:73) — ещё и Classical_Prop.classic |

---

## #346 — `src/foundation/P4CompletedInfinity.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ |  |  | IV.1 P4 бесконечность как процесс, стр. 1381 | верно | исправлено 12.11 (шаг 5, слово автора): было 12; в файле 9 Qed (4 леммы и 5 теорем); шапка файла исправлена тем же шагом (12 → 9); оба названных файла импортируют P4CompletedInfinity |
| `CompletedInfSet` (29) | Definition | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 263, 277 | верно | Definition CompletedInfSet S := forall n, S n (:29) |
| `P4_stage_bounded` (33) | Definition | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 263, 277 | верно | формально: на каждой стадии все актуальные n не превосходят рубежа — forall stage, exists bound, forall n, actual stage n -> n <= bound (:33); слова «число актуальных элементов» повторяют комментарий файла |
| `bridge` (42) | Definition | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 264, 277 | верно | Definition bridge S actual := forall n, S n -> actual 0 n (:42) |
| `completed_inf_contradicts_P4` (64) | Theorem | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 806, 1252 | верно | соответствует теореме completed_inf_contradicts_P4 (P4CompletedInfinity.v:64) |
| `completed_inf_contradicts_P4` (64) | Theorem | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 806, 1252 | верно | CompletedInfSet S -> P4_stage_bounded actual -> bridge S actual -> False (:64); ход доказательства в главе (рубеж B, число B+1) совпадает с :69–80 |
| `completed_inf_contradicts_P4` (64) | Theorem | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 806, 1252 | верно | исправлено 12.11 (шаг 5, слово автора): было «(`P4_Eliminates_Infinity`: `nat` — правило индукции, не готовое множество)» — это файл слоя ненужности; теорема несовместимости — completed_inf_contradicts_P4 (P4CompletedInfinity.v:64), для nat — nat_not_completed_under_P4 (:146) |
| `potential_inf_exists` (87) | Lemma | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 893 | верно | Lemma potential_inf_exists : potential_infinity (P4CompletedInfinity.v:87); potential_infinity := forall n, exists m, n < m |

---

## #347 — `src/foundation/P4ProhibitionSynthesis.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ |  |  | IV.1 P4 бесконечность как процесс, стр. 1375 | верно | шапка P4ProhibitionSynthesis.v:8–16 — «WHAT CHANGED … UNNECESSARY / INCONSISTENT», «Prohibition ⇒ Reinterpretation» |
| _файл целиком_ |  |  | IV.1 P4 бесконечность как процесс, стр. 1383 | верно | исправлено 12.11 (шаг 5, слово автора): было 8; в файле 6 Qed (5 теорем и 1 лемма); шапка файла исправлена шагом 4 |
| `P4_prohibits_three` (30) | Theorem | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 1383 | верно | исправлено 12.11 (шаг 5, слово автора): было «полной аксиомой выбора»; три конъюнкта (:30) — условная несовместимость завершённого множества; AC_gives_completed_graph (функция выбора с графиком из выбранных пар, содержащим пару на всяком индексе); противоречивость множества Рассела. Сомнительным остаётся третье: в противоречивости множества Рассела P4 не участвует (лемма названа russell_contradiction_without_P1) |
| `P4_preserves_three` (49) | Theorem | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 934, 1383 | верно | три конъюнкта (:49): potential_infinity; конечный выбор; P4_stage_bounded nat_staged_actual — стадийная модель nat ограничена; «индуктивные типы» — прочтение третьего конъюнкта по комментарию файла |
| `P4_preserves_three` (49) | Theorem | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 934, 1383 | верно | см. запись к строке 924 |
| `prohibition_implies_reinterpretation` (72) | Theorem | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 887, 894 | верно | утверждение — «несовместимость -> potential_infinity» (:72); доказательство: intros _. exact potential_inf_exists. (:79) — посылка действительно не используется, как и сказано в главе |

---

## #348 — `src/foundation/P4ProhibitsAC.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ |  |  | IV.1 P4 бесконечность как процесс, стр. 837 | верно | статус назван честно: замкнутого отрицания в файле нет; после шага 4 файл говорит это сам — AC_on_nat_as_rule доказывает AC_on_nat, а противоречие (ac_completed_graph_contradicts_P4) условно: стадийная ограниченность и мост |
| _файл целиком_ |  |  | IV.1 P4 бесконечность как процесс, стр. 1382 | верно | исправлено 12.11 (шаг 5, слово автора): было 10; после шага 4 в файле 12 Qed (7 лемм и 5 теорем), 0 аксиом |
| `choice_graph` (49) | Definition | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 822 | верно | исправлено 12.11 (шаг 4, слово автора «А») — правка формализации, слова главы не менялись: теперь Definition choice_graph (f : nat -> nat) : nat -> nat -> Prop := fun n m => m = f n — совокупность пар «индекс, значение»; тотальность — лемма choice_graph_completed : forall f, CompletedInfSet (graph_indices (choice_graph f)), где graph_indices G n := exists m, G n m; было choice_graph f := fun n => True (от f не зависел) |
| `ac_implies_completed` (86) | Theorem | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 825 | верно | исправлено 12.11 (шаг 4, слово автора «А») — правка формализации, слова главы не менялись: теперь ac_implies_completed : AC_on_nat -> forall F, (forall n, F n <> nil) -> exists f, (forall n m, choice_graph f n m -> In m (F n)) /\ CompletedInfSet (graph_indices (choice_graph f)) — функция выбора привязана к семейству, посылка в доказательстве используется; Print Assumptions: Closed under the global context. Граница доказанного названа в самом файле: AC_on_nat_as_rule (посылка есть теорема) и completed_graph_contradicts_P4 (то же для графика любой функции) |
| `completed_graph_contradicts_P4` (108) | Theorem | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 834 | верно | исправлено 12.11 (шаг 4, слово автора «А») — фраза добавлена: forall f actual, P4_stage_bounded actual -> bridge (graph_indices (choice_graph f)) actual -> False; Closed under the global context |
| `ac_completed_graph_contradicts_P4` (122) | Theorem | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 831 | верно | исправлено 12.11 (шаг 4, слово автора «А») — фраза добавлена: AC_on_nat -> forall F, (forall n, F n <> nil) -> forall actual, P4_stage_bounded actual -> (forall f, (forall n, In (f n) (F n)) -> bridge (graph_indices (choice_graph f)) actual) -> False; Closed under the global context |
| `AC_on_nat_as_rule` (160) | Lemma | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 835 | верно | исправлено 12.11 (шаг 4, слово автора «А») — фраза добавлена: Lemma AC_on_nat_as_rule : AC_on_nat, свидетель fun n => L5_choose (F n) 0; Closed under the global context; то же утверждение — P4_Eliminates_AC.AC_is_L5 |

---

## #349 — `src/foundation/P4ProhibitsImpredicative.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ | файл |  | IV.1 P4 бесконечность как процесс, стр. 1381 | верно | упоминание файла; проверено существование |

---

## #550 — `src/HeineBorel_ERR.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| `not_coverable_half` (379) | Lemma | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P | V.2 Топология и компактность, стр. 607 | верно | сверена цена; формулировка — при аудите части; теоремы Гейне — Бореля от этой леммы не зависят |
| `Heine_Borel_uniform` (517) | Theorem | Closed under the global context | V.2 Топология и компактность, стр. 598, 613, 1009, 1016 | верно | исправлено 12.11; сверена цена; формулировка — при аудите части |
| `Heine_Borel` (536) | Theorem | Closed under the global context | V.2 Топология и компактность, стр. 588, 613, 1016 | верно | исправлено 12.11; сверена цена; формулировка — при аудите части |
| `Heine_Borel` (536) | Theorem | Closed under the global context | Формализация, стр. 106 | верно | сверена цена; формулировка — при аудите части |

---

## #559 — `src/IVT_CauchyReal.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| `ivt_cauchy_real` (309) | Theorem | Closed under the global context | V.3 Непрерывность, стр. 723, 1127, 1134 | верно | исправлено 12.11; сверена цена; формулировка — при аудите части |
| `ivt_cauchy_real` (309) | Theorem | Closed under the global context | Формализация, стр. 103 | верно | сверена цена; формулировка — при аудите части |

---

## #560 — `src/IVT_ERR.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| `IVT_process` (256) | Theorem | Closed under the global context | V.3 Непрерывность, стр. 645, 1127, 1134 | верно | исправлено 12.11; сверена цена; формулировка — при аудите части |
| `IVT_process` (256) | Theorem | Closed under the global context | Направления/Математика/index, стр. 96 | верно | сверена цена; формулировка — при аудите части |
| `IVT_process` (256) | Theorem | Closed under the global context | Формализация, стр. 103, 134 | верно | сверена цена; формулировка — при аудите части |

---

## #704 — `src/process/ProcessArithmetic.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ |  |  | IV.2 RealProcess как тип, стр. 321 | верно | Верно: в ProcessArithmetic.v умножения двух процессов нет (определения: add, neg, sub, scale, abs). |
| `classic` | внешнее | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P | IV.2 RealProcess как тип, стр. 788, 789, 794 | верно | В этом файле `classic` — аксиома стандартной библиотеки (Stdlib.Logic.Classical_Prop.classic, импорт ProcessArithmetic.v:22), по формулировке та же, что L3 формализации (foundation/Distinction.v:36); в самом ProcessArithmetic.v она не объявляется, а применяется. |
| _файл целиком_ |  |  | IV.2 RealProcess как тип, стр. 1104 | верно | исправлено 12.11 (шаг 7, слово автора): было 13; в файле 17 Qed (4 Theorem + 13 Lemma), 0 Admitted; шапка файла исправлена тем же шагом (13 → 17, два места) |
| _файл целиком_ | файл |  | IV.3 Точка как класс эквивалентности процессов, стр. 712 | верно | упоминание файла; проверено существование |
| _файл целиком_ |  |  | IV.6 P4 как фильтр, стр. 273 | верно | исправлено 12.11; арифметика (add / neg / sub / scale_preserves_Cauchy) замкнута; в том же ProcessArithmetic.v две леммы о монотонной сходимости — monotone_bounded_Cauchy (311), decreasing_bounded_Cauchy (339) — стоят на Classical_Prop.classic, к арифметике они не относятся |
| `process_add` (31) | Definition | Closed under the global context | IV.2 RealProcess как тип, стр. 287 | верно | Блок кода (стр. 293) совпадает с ProcessArithmetic.v:31; в файле есть ещё поточечный модуль process_abs (:43), глава его не называет. |
| `process_neg` (34) | Definition | Closed under the global context | IV.2 RealProcess как тип, стр. 296 | верно | Блок кода совпадает с ProcessArithmetic.v:34. |
| `process_sub` (37) | Definition | Closed under the global context | IV.2 RealProcess как тип, стр. 299 | верно | Блок кода совпадает с ProcessArithmetic.v:37. |
| `process_scale` (40) | Definition | Closed under the global context | IV.2 RealProcess как тип, стр. 302 | верно | Блок кода совпадает с ProcessArithmetic.v:40. |
| `add_preserves_Cauchy` (84) | Theorem | Closed under the global context | IV.2 RealProcess как тип, стр. 376 | верно | В файле ровно четыре Theorem (:84, :103, :114, :134); блок кода совпадает; допущений нет. |
| `add_preserves_Cauchy` (84) | Theorem | Closed under the global context | IV.2 RealProcess как тип, стр. 376 | верно | Ход доказательства описан верно: ProcessArithmetic.v:88–101 — eps * (1#2) для каждого слагаемого и Qabs_triangle; «классические рассуждения» здесь значит традиционные, аксиома classic не применяется. |
| `neg_preserves_Cauchy` (103) | Theorem | Closed under the global context | IV.2 RealProcess как тип, стр. 349 | верно | Блок кода совпадает с ProcessArithmetic.v:103; допущений нет. |
| `sub_preserves_Cauchy` (114) | Theorem | Closed under the global context | IV.2 RealProcess как тип, стр. 351 | верно | Блок кода совпадает с ProcessArithmetic.v:114; допущений нет. |
| `scale_preserves_Cauchy` (134) | Theorem | Closed under the global context | IV.2 RealProcess как тип, стр. 353 | верно | Блок кода совпадает с ProcessArithmetic.v:134; допущений нет. |
| `monotone_increasing` (173) | Definition | Closed under the global context | IV.2 RealProcess как тип, стр. 745 | верно | ProcessArithmetic.v:173: forall n, R n <= R (S n); блок кода совпадает. |
| `monotone_decreasing` (176) | Definition | Closed under the global context | IV.2 RealProcess как тип, стр. 747 | верно | ProcessArithmetic.v:176: forall n, R (S n) <= R n; блок кода совпадает. |
| `q_archimedean` (263) | Lemma | Closed under the global context | IV.2 RealProcess как тип, стр. 776 | верно | ProcessArithmetic.v:263–306: K := S (Z.to_nat (target / step)); формулировка на стр. 776–778 совпадает (d < K * eps при 0 < eps); допущений нет. |
| `q_archimedean` (263) | Lemma | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 711 | верно | ProcessArithmetic.v:263: forall d eps, 0 < eps -> exists K, d < inject_Z (Z.of_nat K) * eps; применена внутри доказательства nine_equiv_one (отдельной леммой оценка хвоста не выделена). Closed under the global context, хотя файл импортирует Classical. |
| `monotone_bounded_Cauchy` (311) | Lemma | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P | IV.2 RealProcess как тип, стр. 758, 786, 795, 925 | верно | ProcessArithmetic.v:311 (в файле объявлена как Lemma, в прозе названа теоремой); блок кода (стр. 761) совпадает; Print Assumptions: Classical_Prop.classic. |
| `monotone_bounded_Cauchy` (311) | Lemma | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P | IV.2 RealProcess как тип, стр. 758, 786, 795, 925 | верно | Print Assumptions: Axioms: Classical_Prop.classic; destruct (classic …) на ProcessArithmetic.v:316 и :324; импорт Classical — :22. |
| `monotone_bounded_Cauchy` (311) | Lemma | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P | IV.2 RealProcess как тип, стр. 758, 786, 795, 925 | верно | Print Assumptions: Classical_Prop.classic. |
| `monotone_bounded_Cauchy` (311) | Lemma | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P | IV.2 RealProcess как тип, стр. 758, 786, 795, 925 | верно | Print Assumptions: Classical_Prop.classic у monotone_bounded_Cauchy и decreasing_bounded_Cauchy; остальные 15 лемм ProcessArithmetic.v без допущений. |
| `decreasing_bounded_Cauchy` (339) | Lemma | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P | IV.2 RealProcess как тип, стр. 767 | верно | ProcessArithmetic.v:339; формулировка верна; цена та же, что у основной — Classical_Prop.classic (выводится из monotone_bounded_Cauchy для -R), глава отдельно её не называет. |

---

## #706 — `src/process/ProcessAxiomAudit.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ |  |  | IV.1 P4 бесконечность как процесс, стр. 349 | верно | шапка ProcessAxiomAudit.v после шага 3: «Part II gathers the six key results into one proof object and runs Print Assumptions on it at every build; the statement about the whole formalization rests on a full Print Assumptions sweep (run separately)» |
| _файл целиком_ |  |  | IV.1 P4 бесконечность как процесс, стр. 356 | верно | исправлено 12.11 (шаг 3, слово автора): сплошной прогон Print Assumptions после правок 2026-11-12 — functional_extensionality_dep: 0; не замкнутые теоремы стоят на Classical_Prop.classic (и трёх одноимённых объявлениях того же утверждения), ToS_Axioms.L4_witness, а в двух предметных местах — на модельных аксиомах Навье — Стокса (C_B_positive, B_coeff_bounded, параметры C_B, B_raw) и параметре eval_program; это не логические допущения; модулей выбора и унивалентности в импортах нет |
| _файл целиком_ |  |  | IV.1 P4 бесконечность как процесс, стр. 366 | верно | исправлено 12.11 (шаг 3, слово автора): было «процессная часть действительно обходится одним L3, тогда как L4 … почти не востребован»; сплошной прогон Print Assumptions после правок 2026-11-12, src/process: 4376 из 4429 теорем и лемм без допущений (98,8 %), 48 на classic, 7 из них ещё и на L4_witness (ProcessBW.v) |
| _файл целиком_ |  |  | IV.1 P4 бесконечность как процесс, стр. 1373 | верно | исправлено 12.11 (шаг 3, слово автора): было 13; после удаления трёх лемм-вывесок в файле 10 Qed |
| _файл целиком_ |  |  | IV.6 P4 как фильтр, стр. 120 | верно | все восемь классифицированных в файле результатов физические: Паули, щель 289/384, угол Вайнберга, группа СМ, знак Лоренца, rho = 1, D = 3, CP (строки 36–58) |
| _файл целиком_ |  |  | IV.6 P4 как фильтр, стр. 135 | верно | после шага 3 (12.11) расхождения записи файла с компилятором нет: вместо «Expected results» в комментарии Part II стоят действительные ответы компилятора, а о шести ключевых результатах в файле стоит сама команда Print Assumptions; разметка силы (FullyDerived и др.) остаётся оценкой автора — Print Assumptions показывает допущения, а не силу вывода |
| _файл целиком_ |  |  | IV.6 P4 как фильтр, стр. 149 | верно | после правок 2026-11-12 верно: сплошной прогон Print Assumptions после правок 2026-11-12 — functional_extensionality_dep: 0 (было 9 лемм в 5 файлах); модулей выбора (ClassicalChoice, Epsilon, IndefiniteDescription) и унивалентности в импортах нет |
| _файл целиком_ |  |  | IV.6 P4 как фильтр, стр. 150 | верно | исправлено 12.11 (шаг 3, слово автора): было «опертое на Print Assumptions, а не машинная проверка всего репозитория одной командой»; статус назван честно — запись в комментарии файла, проверка — прогон (tools/tom-pa-all.cjs) |
| _файл целиком_ |  |  | IV.6 P4 как фильтр, стр. 200 | верно | исправлено 12.11 (шаг 13, слово автора): пересказ приведён к шапке ProcessAxiomAudit.v — «Elements: DerivationStrength, axiom classifications; Roles: meta-level analysis, honest assessment; Rules: classify each result by derivation strength»; у ProcessDerivedVsConsistent.v шапка своя (IFStrength, DerivationRecord; Forced/Natural/Chosen) |
| _файл целиком_ |  |  | IV.6 P4 как фильтр, стр. 430 | верно | файл на месте: src/process/ProcessAxiomAudit.v, 10 Qed (после шага 3), 0 Admitted, аксиом не объявляет; все объявления замкнуты |
| `DerivationStrength` (39) | Inductive | Closed under the global context | IV.6 P4 как фильтр, стр. 108, 206, 416, 430 | верно | Inductive с пятью конструкторами (ProcessAxiomAudit.v:28–33); порядок «от сильнейшей к слабейшей» в файле отношением не задан — это чтение главы по порядку конструкторов |
| `DerivationStrength` (39) | Inductive | Closed under the global context | IV.6 P4 как фильтр, стр. 108, 206, 416, 430 | верно | все пять строк таблицы градаций совпадают с комментариями при конструкторах (ProcessAxiomAudit.v:29–33) |
| `fully_derived_strongest` (72) | Lemma | Closed under the global context | IV.6 P4 как фильтр, стр. 139 | верно | утверждение леммы — pauli_strength = FullyDerived (reflexivity): проверяет запись, порядка «сильнейшая» не доказывает; глава большего и не утверждает |
| `total_classified` (89) | Lemma | Closed under the global context | IV.6 P4 как фильтр, стр. 126 | верно | числа верны: по определениям *_strength (строки 36–58) 3 + 2 + 2 + 1 = 8; счётчики n_* вписаны в файл числами, лемма проверяет их сумму; в файле это Lemma, а не Theorem |
| `key_results_hold` (136) | Definition | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 353 | верно | исправлено 12.11 (шаг 3, слово автора): было «Его теорема axiom_minimal — формализованная документация вывода…»; теоремы-вывески axiom_minimal, l4_witness_localized, classic_is_L3 и определение uses_classic из файла удалены (утверждали «L3 влечёт L3», нигде больше не использовались); key_results_hold — конъюнкция pauli_exclusion, spectral_gap_beta_1, weinberg_physical, trace_gauge_invariant_concrete, regge_equation_uniform, sm_anomaly_cancels; команда Print Assumptions стоит в файле и при сборке отвечает «Closed under the global context» |
| `key_results_hold` (136) | Definition | Closed under the global context | IV.6 P4 как фильтр, стр. 144 | верно | исправлено 12.11 (шаг 3, слово автора): было «Его теорема axiom_minimal утверждает содержательно: ключевые результаты зависят только от classic»; теорема-вывеска удалена; key_results_hold — конъюнкция шести теорем, Print Assumptions стоит в файле и отвечает «Closed under the global context» |

---

## #712 — `src/process/ProcessBinReal.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ |  |  | IV.5 Процессный континуум, стр. 155 | верно | сомнительное (статус): неинъективность перевода в файле не доказана — шапка относит её к «честной границе (вне ядра)» (ProcessBinReal.v:21–23), доказан только образец 0,111…=1; итог главы (стр. 915–917) честно называет общую неоднозначность записи открытой, а здесь она подана как видная «прямо на переводе» |
| _файл целиком_ |  |  | IV.5 Процессный континуум, стр. 926 | верно | статус честный: совпадает с «честной границей» в шапке файла (ProcessBinReal.v:21–23) |
| _файл целиком_ |  |  | IV.6 P4 как фильтр, стр. 422 | верно | исправлено 12.11 (шаг 14, слово автора «А»): из списка открытых задач и из итога сняты два закрытых пункта — полное перечисление ℚ (Q_bijection, Countability_Q.v:759, без допущений) и точка-класс (сетоид RealPointSetoid.v с метрикой и топологией; отдельный фактортип ToS осознанно не строит, Глава 4.3); оставшиеся два по формализации открыты: мост 2^ℕ ↔ [0,1] есть только в прямую сторону (bin_to_real, process/ProcessBinReal.v), а P4 в foundation/PrinciplesFromLaws.v держится «по построению типа», без цепочки от законов |
| `bin_to_real` (90) | Definition | Closed under the global context | IV.5 Процессный континуум, стр. 148, 923 | верно | bin_to_real := bin_partial, n-я частичная сумма bit(b k)/2^(k+1) (ProcessBinReal.v:84–90); попадание в [0,1] — bin_to_real_in_interval, без допущений |
| `bin_to_real` (90) | Definition | Closed under the global context | IV.6 P4 как фильтр, стр. 376 | верно | ProcessBinReal.v: bin_to_real, bin_to_real_in_interval, bin_ones_equiv_one — без допущений, bin_to_real_is_Cauchy — на classic; обратного отображения в src нет (в журнале формализации это задача F-23) |
| `bin_to_real_in_interval` (169) | Theorem | Closed under the global context | IV.5 Процессный континуум, стр. 924 | верно | forall b, in_interval 0 1 (bin_to_real b) (ProcessBinReal.v:169); без допущений; в файле 15 Qed, как и в его шапке |
| `bin_to_real_is_Cauchy` (176) | Theorem | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P | IV.5 Процессный континуум, стр. 924 | верно | Print Assumptions: Classical_Prop.classic — через monotone_bounded_Cauchy (ProcessBinReal.v:176–181; ProcessArithmetic.v:311) |
| `bin_ones_equiv_one` (188) | Theorem | Closed under the global context | IV.5 Процессный континуум, стр. 153, 926 | верно | bin_to_real all_ones ~~ const_process 1 (ProcessBinReal.v:188, в файле объявлена как Theorem); без допущений |

---

## #717 — `src/process/ProcessBounds.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ |  |  | IV.2 RealProcess как тип, стр. 1106 | верно | Действительный счёт: 11 Qed, 0 Admitted, 0 Axiom; все 11 — «Closed under the global context» (шапка файла в двух местах называет 11 и 14). |
| `has_process_mass_gap` (39) | Record | Closed under the global context | IV.2 RealProcess как тип, стр. 804, 809, 814, 1106 | верно | ProcessBounds.v:39–50: PMG1 (0 < delta <= R n), PMG2 (\|R m - R n\| <= C * r^min(m,n), 0 < r < 1), PMG3 (monotone_decreasing R). |
| `has_process_mass_gap` (39) | Record | не применимо (часть имени) | IV.2 RealProcess как тип, стр. 804, 809, 814, 1106 | верно | исправлено 12.11 (шаг 7, слово автора): было «Имя `mass_gap`» — часть имени; структура в файле называется has_process_mass_gap (ProcessBounds.v:39); оговорка «не физический массовый зазор» — чтение главы |
| `pmg_implies_cauchy` (74) | Theorem | Closed under the global context | IV.2 RealProcess как тип, стр. 817 | верно | ProcessBounds.v:74: has_process_mass_gap R -> is_Cauchy R; допущений нет. |
| `pathological_no_pmg` (209) | Theorem | Closed under the global context | IV.2 RealProcess как тип, стр. 825 | верно | ProcessBounds.v:209: has_process_mass_gap (const_process 0) -> False; допущений нет. |
| `vanishing_no_pmg` (217) | Lemma | Closed under the global context | IV.2 RealProcess как тип, стр. 826 | верно | ProcessBounds.v:217: условие в Rocq — значения процесса с некоторого шага меньше любого eps > 0 (монотонность не требуется); пересказ «убывающего к нулю» чуть уже, по смыслу верен; допущений нет. |

---

## #718 — `src/process/ProcessBridge.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ |  |  | IV.3 Точка как класс эквивалентности процессов, стр. 269 | верно | Шапка ProcessBridge.v, строка 16: «These are the same mathematical object.» |
| _файл целиком_ |  | Closed under the global context (все 10 лемм файла) | IV.3 Точка как класс эквивалентности процессов, стр. 955 | верно | Действительный счёт: 10 Qed, 0 Admitted, объявлений Axiom / Parameter нет; Print Assumptions для всех 10 лемм файла — Closed under the global context. |
| _файл целиком_ |  |  | IV.3 Точка как класс эквивалентности процессов, стр. 957 | верно | Обе шапки содержат строки Elements / Roles / Rules (ProcessCore.v:2–4, ProcessBridge.v:2–4). |
| _файл целиком_ | файл |  | IV.4 Несчётность процессов, стр. 676 | верно | упоминание файла; проверено существование |
| `cauchyseq_to_process` (35) | Definition | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 281 | верно | ProcessBridge.v:35: fun n => cs_seq cs n; блок кода (стр. 275) совпадает. |
| `process_to_cauchyseq` (39) | Definition | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 281 | верно | ProcessBridge.v:39: mkCauchy R H — принимает процесс вместе с доказательством is_Cauchy; блок кода (стр. 277) совпадает. |
| `cauchy_equiv_to_process_equiv` (66) | Lemma | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 296 | верно | ProcessBridge.v:66; блок кода (стр. 288) совпадает с исходником. |
| `cauchy_equiv_to_process_equiv` (66) | Lemma | Closed under the global context | IV.4 Несчётность процессов, стр. 675 | верно | Верно: леммы cauchy_equiv_to_process_equiv и process_equiv_to_cauchy_equiv (process/ProcessBridge.v:66, :78), обе без допущений; номер параграфа 3.3.1 на странице Главы 4.3 не проставлен (заголовки без номеров) — не проверялся. |
| `process_equiv_to_cauchy_equiv` (78) | Lemma | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 297 | верно | ProcessBridge.v:78; вместе с леммой :66 — равносильность в обе стороны, вывод главы обоснован. |
| `roundtrip_process_equiv` (101) | Lemma | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 301 | верно | ProcessBridge.v:101: process_equiv (cauchyseq_to_process (process_to_cauchyseq R H)) R — возврат к эквивалентному объекту. |
| `roundtrip_cauchyseq_equiv` (120) | Lemma | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 302 | верно | ProcessBridge.v:120: cauchy_equiv cs (process_to_cauchyseq (cauchyseq_to_process cs) (cauchyseq_is_cauchy cs)). |

---

## #719 — `src/process/ProcessBW.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ |  |  | IV.1 P4 бесконечность как процесс, стр. 360 | верно | исправлено 12.11 (шаг 3, слово автора): было «зависят только от classic, и лишь изредка — от L4, причём L4 локализован в одном файле, посвящённом вариационному принципу»; сплошной прогон Print Assumptions после правок 2026-11-12, src/process: 4429 теорем и лемм, 4376 без допущений, 48 на classic (19 файлов), из них 7 ещё и на L4_witness — все в ProcessBW.v (process_BW и шесть лемм вокруг) |

---

## #734 — `src/process/ProcessCore.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| `Q` | внешнее | не применимо (тип стандартной библиотеки) | IV.2 RealProcess как тип, стр. 141, 147 | верно | Сомнительное место, не расхождение: `Q` и `nat` — типы стандартной библиотеки Rocq (Stdlib.QArith.QArith_base.Q, Corelib.Init.Datatypes.nat; ProcessCore.v:24 их импортирует), в файлах формализации они не строятся; «построенные в предыдущих частях тома» верно для изложения, не для кода. |
| _файл целиком_ |  |  | IV.2 RealProcess как тип, стр. 508 | верно | Три рода конструкции названы верно (ProcessCore.v:34, CauchyReal.v:48, ProcessGeneral.v:50); наблюдение: читатель встретит в src ещё локальные копии RealProcess (10 объявлений) и is_Cauchy (9). |
| _файл целиком_ |  |  | IV.2 RealProcess как тип, стр. 907 | верно | Шапки: ProcessCore.v:4 «Rules: every mathematical object is a finite process at each stage (P4)»; ProcessArithmetic.v:4 «Rules: each operation preserves the Cauchy condition». |
| _файл целиком_ |  |  | IV.3 Точка как класс эквивалентности процессов, стр. 777 | верно | Шапка ProcessCore.v, строка 4: «Rules: every mathematical object is a finite process at each stage (P4)». Попутно: шапка называет 25 Qed, действительный счёт 19 (в этой главе число не приводится). |
| _файл целиком_ | файл |  | IV.4 Несчётность процессов, стр. 578, 598, 612 | верно | упоминание файла; проверено существование |
| `ProcessCore` | модуль |  | IV.4 Несчётность процессов, стр. 581, 638, 907 | верно | имя модуля; файл существует |
| _файл целиком_ |  |  | IV.6 P4 как фильтр, стр. 268 | верно | все 27 объявлений ProcessCore.v (19 Qed) — «Closed under the global context» |
| `RealProcess` (34) | Definition | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 1203, 1215, 1219, 1225, 1313 | верно | Definition RealProcess := nat -> Q (ProcessCore.v:34); то же определение повторено ещё в девяти файлах |
| `RealProcess` (34) | Definition | Closed under the global context | IV.2 RealProcess как тип, стр. 77, 80, 88, 96, 97, 99, 115, 121 | верно | Определение и блок кода (стр. 84) совпадают с ProcessCore.v:34; наблюдение: в src ещё 9 локальных копий того же определения (Archimedean_ERR, EVT_idx, HeineBorel_ERR, ShrinkingIntervals_ERR и др.). |
| `RealProcess` (34) | Definition | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 11, 64, 126, 232, 237, 242, 267, 270 | верно | Definition RealProcess := nat -> Q (ProcessCore.v:34). |
| `RealProcess` (34) | Definition | Closed under the global context | IV.5 Процессный континуум, стр. 90, 127 | верно | Definition RealProcess := nat -> Q (ProcessCore.v:34); то же определение повторено ещё в девяти файлах |
| `RealProcess` (34) | Definition | Closed under the global context | IV.6 P4 как фильтр, стр. 268, 345 | верно | сомнительное: Definition RealProcess := nat -> Q (ProcessCore.v:34) — тип всех процессов, без условия Коши; условие задаёт отдельный предикат is_Cauchy (строка 68), упакованная форма — CauchySeq (CauchyReal.v:48); в сводной строке это сокращение, Глава 4.2 различие проводит |
| `const_process` (37) | Definition | Closed under the global context | IV.2 RealProcess как тип, стр. 944, 1102 | верно | Блок кода (стр. 106) совпадает с ProcessCore.v:37. |
| `is_Cauchy` (68) | Definition | Closed under the global context | IV.2 RealProcess как тип, стр. 254, 267, 518, 542, 576, 589, 1066, 1102 | верно | ProcessCore.v:68; наблюдение к словам «двумя предикатами в двух файлах» (стр. 264): в src 9 объявлений is_Cauchy, среди них запись со строгими неравенствами в ShrinkingIntervals_ERR.v:163 (её называет Глава 4.4). |
| `is_Cauchy` (68) | Definition | Closed under the global context | IV.4 Несчётность процессов, стр. 561, 568, 604 | верно | Верно: ShrinkingIntervals_ERR.v:163–166 — (m > N), (n > N); process/ProcessCore.v:68–71 — (N <= m), (N <= n). |
| `is_Cauchy` (68) | Definition | Closed under the global context | IV.6 P4 как фильтр, стр. 268 | верно | упоминание имени (Definition); проверено существование; объявлений с таким именем 9 (файл назван в главе) |
| `const_is_Cauchy` (78) | Lemma | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 701 | верно | ProcessCore.v:78: forall q, is_Cauchy (const_process q). |
| `process_equiv` (170) | Definition | Closed under the global context | IV.2 RealProcess как тип, стр. 1102 | верно | Шапка ProcessCore.v:3: «SINGLE source of truth for process definitions»; четыре имени объявлены в файле (:34, :68, :37, :170); наблюдение: шапка называет 25 Qed, действительных 19 (глава числа не приводит). |
| `process_equiv` (170) | Definition | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 243, 245, 258, 260, 299, 309, 699, 720 | верно | Блок кода (стр. 249–252) совпадает с ProcessCore.v:170; определение то же, что у cauchy_equiv, для голых процессов. |
| `process_equiv` (170) | Definition | Closed under the global context | IV.4 Несчётность процессов, стр. 214, 613, 616, 664, 671, 675, 680, 690 | верно | упоминание имени (Definition); проверено существование; объявлений с таким именем 3 (файл назван в главе) |
| `process_equiv` (170) | Definition | Closed under the global context | IV.5 Процессный континуум, стр. 185 | верно | ProcessCore.v:170: для всякого eps разность членов меньше eps начиная с некоторого N; «общий предел» — пересказ, предел в определении не назван |
| `process_equiv` (170) | Definition | Closed under the global context | IV.6 P4 как фильтр, стр. 268, 346 | верно | Equivalence для process_equiv и cauchy_equiv зарегистрированы в RealPointSetoid.v:52, 61; без допущений |
| `equiv_cauchy_l` (210) | Lemma | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 702 | верно | ProcessCore.v:210: R1 ~~ R2 -> is_Cauchy R1 -> is_Cauchy R2. |

---

## #749 — `src/process/ProcessDerivedVsConsistent.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ |  |  | IV.6 P4 как фильтр, стр. 185 | верно | 4 из 12 — треть; число совпадает с файлом |
| _файл целиком_ |  |  | IV.6 P4 как фильтр, стр. 415 | верно | для шкал силы верно; для оси цены таблица в Rocq есть — settheory/ChoicePriceMap.v (см. запись строки 242) |
| `IFStrength` (33) | Inductive | Closed under the global context | IV.6 P4 как фильтр, стр. 161, 207, 416, 431 | верно | совпадает с Inductive IFStrength и комментариями при конструкторах (ProcessDerivedVsConsistent.v:33–36) |
| `DerivationRecord` (39) | Record | Closed under the global context | IV.6 P4 как фильтр, стр. 431 | верно | упоминание имени (Record); проверено существование |
| `all_derivations` (184) | Definition | Closed under the global context | IV.6 P4 как фильтр, стр. 431 | верно | все три имени объявлены в файле (строки 33, 39, 184); в списке 12 записей; файл — 20 Qed, все 38 объявлений замкнуты |
| `derivation_count_forced` (198) | Lemma | Closed under the global context | IV.6 P4 как фильтр, стр. 179 | верно | count_forced = 4 вычисляется фильтром по списку all_derivations из 12 записей (E/R/R, метрика, Эйнштейн, CP); без допущений |
| `derivation_count_natural` (203) | Lemma | Closed under the global context | IV.6 P4 как фильтр, стр. 180 | верно | count_natural = 5 (Паули, калибровка, Лоренц, СМ, D = 3); без допущений |
| `derivation_count_chosen` (208) | Lemma | Closed under the global context | IV.6 P4 как фильтр, стр. 180 | верно | count_chosen = 3 (щель, Вайнберг, натяжение струны); сумма 4 + 5 + 3 = 12 — лемма derivation_total |

---

## #796 — `src/process/ProcessFourPrinciples.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ |  |  | IV.1 P4 бесконечность как процесс, стр. 125 | верно | P1_formalized … P4_formalized — ProcessFourPrinciples.v:52–64; строка комментария о P4 — :16 (в файле стрелка «→», в главе «->») |
| _файл целиком_ |  |  | IV.1 P4 бесконечность как процесс, стр. 1200 | верно | двенадцать конструкторов ProcessInstance (:110–122), twelve_instances (:131) |
| _файл целиком_ |  |  | IV.1 P4 бесконечность как процесс, стр. 1370 | верно | исправлено 12.11 (шаг 2, слово автора): было «наследует единственную логическую аксиому classic»; все объявления ProcessFourPrinciples.v — Closed under the global context; число 25 Qed верно |
| _файл целиком_ | файл |  | IV.2 RealProcess как тип, стр. 371, 516 | верно | упоминание файла; проверено существование |
| `P4_formalized` (65) | Definition | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 143, 155, 167, 173, 255, 268, 276, 372 | верно | исправлено 12.11 правкой формализации (шаг 1, слово автора «А»): второй пункт предиката теперь is_Cauchy (process_mul R1 R2) — замкнутость относительно умножения (ProcessFourPrinciples.v; лемма mul_preserves_Cauchy, CauchyProcessBridge.v:74); слова главы верны как есть. Было: пункт о паре процессов (process_product). |
| `P4_formalized` (65) | Definition | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 143, 155, 167, 173, 255, 268, 276, 372 | верно | блок кода совпадает с исходником (ProcessFourPrinciples.v:64), комментарии внутри определения опущены |
| `P4_formalized` (65) | Definition | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 143, 155, 167, 173, 255, 268, 276, 372 | верно | исправлено 12.11 правкой формализации (шаг 1, слово автора «А»): второй пункт предиката теперь is_Cauchy (process_mul R1 R2) — замкнутость относительно умножения (ProcessFourPrinciples.v; лемма mul_preserves_Cauchy, CauchyProcessBridge.v:74); слова главы верны как есть. Было: пункт о паре процессов (process_product). |
| `P4_formalized` (65) | Definition | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 143, 155, 167, 173, 255, 268, 276, 372 | верно | исправлено 12.11 правкой формализации (шаг 1, слово автора «А»): второй пункт предиката теперь is_Cauchy (process_mul R1 R2) — замкнутость относительно умножения (ProcessFourPrinciples.v; лемма mul_preserves_Cauchy, CauchyProcessBridge.v:74); слова главы верны как есть. Было: пункт о паре процессов (process_product). |
| `P4_formalized` (65) | Definition | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 143, 155, 167, 173, 255, 268, 276, 372 | верно | исправлено 12.11 правкой формализации (шаг 1, слово автора «А»): второй пункт предиката теперь is_Cauchy (process_mul R1 R2) — замкнутость относительно умножения (ProcessFourPrinciples.v; лемма mul_preserves_Cauchy, CauchyProcessBridge.v:74); слова главы верны как есть. Было: пункт о паре процессов (process_product). |
| `P4_formalized` (65) | Definition | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 143, 155, 167, 173, 255, 268, 276, 372 | верно | исправлено 12.11 правкой формализации (шаг 1, слово автора «А»): второй пункт предиката теперь is_Cauchy (process_mul R1 R2) — замкнутость относительно умножения (ProcessFourPrinciples.v; лемма mul_preserves_Cauchy, CauchyProcessBridge.v:74); слова главы верны как есть. Было: пункт о паре процессов (process_product). |
| `P4_formalized` (65) | Definition | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 143, 155, 167, 173, 255, 268, 276, 372 | верно | исправлено 12.11 правкой формализации (шаг 1, слово автора «А»): второй пункт предиката теперь is_Cauchy (process_mul R1 R2) — замкнутость относительно умножения (ProcessFourPrinciples.v; лемма mul_preserves_Cauchy, CauchyProcessBridge.v:74); слова главы верны как есть. Было: пункт о паре процессов (process_product). |
| `P4_formalized` (65) | Definition | Closed under the global context | IV.2 RealProcess как тип, стр. 370, 374, 378, 392 | верно | ProcessFourPrinciples.v:64 — три конъюнкта именно таковы; третий записан через process_sum (ProcessLimitColimit.v:278, поточечная сумма). |
| `P4_formalized` (65) | Definition | Closed under the global context | IV.6 P4 как фильтр, стр. 380 | верно | P4_formalized — самостоятельный предикат (ProcessFourPrinciples.v:64); теорема с именем P4_from_L5 есть (foundation/PrinciplesFromLaws.v:191), но L5 в её посылках нет, и файл сам пишет «not derived as a theorem» (строки 188–189) |
| `P4_holds_formalized` (101) | Theorem | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 155, 259, 373 | верно | Theorem P4_holds_formalized : P4_formalized (:97); свидетель const_process 0 — :100 |
| `P4_holds_formalized` (101) | Theorem | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 155, 259, 373 | верно | исправлено 12.11 (шаг 2, слово автора): было «доказательство опирается лишь на classic и процессную арифметику»; Print Assumptions P4_holds_formalized — Closed under the global context |
| `ProcessInstance` (113) | Inductive | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 192, 198, 207, 1371 | верно | Inductive ProcessInstance, 12 конструкторов (:110–122); перечисленные роды процессов соответствуют комментариям конструкторов |
| `all_instances` (128) | Definition | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 1371 | верно | упоминание имени (Definition); проверено существование |
| `twelve_instances` (134) | Lemma | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 200, 1371 | верно | length all_instances = 12 (:131) |
| `all_instances_nodup` (147) | Lemma | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 201, 1371 | верно | NoDup all_instances (:144) |
| `P4_independent` (185) | Theorem | Closed under the global context | IV.1 P4 бесконечность как процесс, стр. 422 | верно | forall L : Level, exists R : RealProcess, is_Cauchy R (:182); уровень L в заключении не участвует — свидетель тот же const_process 0 |

---

## #852 — `src/process/ProcessIVT.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| `process_IVT` (128) | Theorem | Closed under the global context | V.3 Непрерывность, стр. 680, 687, 1127, 1134 | верно | исправлено 12.11; сверена цена; формулировка — при аудите части |

---

## #872 — `src/process/ProcessLimitColimit.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| `process_product` (38) | Definition | Closed under the global context | IV.2 RealProcess как тип, стр. 379 | верно | ProcessLimitColimit.v:38, :42: пара процессов и первая проекция, не арифметическое умножение — оговорка главы верна. |
| `process_fst` (42) | Definition | Closed under the global context | IV.2 RealProcess как тип, стр. 379 | верно | упоминание имени (Definition); проверено существование |

---

## #888 — `src/process/ProcessNinePoint.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ | файл |  | IV.2 RealProcess как тип, стр. 1039 | верно | упоминание файла; проверено существование |
| _файл целиком_ | файл |  | IV.3 Точка как класс эквивалентности процессов, стр. 669, 674, 948 | верно | упоминание файла; проверено существование |
| `pow10` (42) | Fixpoint | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 688 | верно | упоминание имени (Fixpoint); проверено существование; объявлений с таким именем 2 (файл назван в главе) |
| `ten_pow` (48) | Definition | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 688 | верно | ProcessNinePoint.v:47 (ten_pow) и :41 (pow10 над positive). Проверено компилятором: `10 ^ (S n)` над Q с показателем nat не проходит проверку типов, `10 ^ Z.of_nat (S n)` проходит. |
| `pow10_ge` (57) | Lemma | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 712 | верно | ProcessNinePoint.v:56: Z.of_nat (S m) <= Z.pos (pow10 m). |
| `nine_raw` (66) | Definition | Closed under the global context | IV.2 RealProcess как тип, стр. 1047 | верно | упоминание имени (Definition); проверено существование |
| `nine_raw` (66) | Definition | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 618, 696, 698, 705 | верно | ProcessNinePoint.v:65: fun n => 1 - 1 / ten_pow (S n); блок кода (стр. 682) совпадает. |
| `nine_raw_lt_one` (72) | Lemma | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 621, 692 | верно | ProcessNinePoint.v:71: forall n, nine_raw n < 1 — формулировка совпадает; в файле объявление названо Lemma (шапка файла тоже зовёт её теоремой). |
| `nine_equiv_one` (84) | Theorem | Closed under the global context | IV.2 RealProcess как тип, стр. 1049 | верно | nine_equiv_one : nine_raw ~~ const_process 1 (ProcessNinePoint.v:84), первая линия; Closed under the global context |
| `nine_equiv_one` (84) | Theorem | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 675, 771, 948 | верно | ProcessNinePoint.v:83; Print Assumptions: Closed under the global context. |
| `nine_equiv_one` (84) | Theorem | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 675, 771, 948 | верно | Блок кода (стр. 716) совпадает с ProcessNinePoint.v:83: nine_raw ~~ const_process 1; знак ~~ здесь — process_equiv (Notation, ProcessCore.v:175). |
| `nine_equiv_one` (84) | Theorem | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 675, 771, 948 | верно | ProcessNinePoint.v:83; Print Assumptions: Closed under the global context. |
| `nine_raw_is_Cauchy` (114) | Theorem | Closed under the global context | IV.2 RealProcess как тип, стр. 1048 | верно | Theorem nine_raw_is_Cauchy : is_Cauchy nine_raw (ProcessNinePoint.v:114); Closed under the global context |
| `nine_raw_is_Cauchy` (114) | Theorem | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 704, 729 | верно | ProcessNinePoint.v:113; доказательство: equiv_cauchy_l (const_process 1) nine_raw, process_equiv_sym от nine_equiv_one, const_is_Cauchy — ход описан верно. |
| `nine_raw_0` (122) | Example | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 686 | верно | Example nine_raw_0 : nine_raw 0%nat == 9 # 10 (ProcessNinePoint.v:121). |
| `nine_process` (135) | Definition | Closed under the global context | IV.2 RealProcess как тип, стр. 1042 | верно | исправлено 12.11 (шаг 8, слово автора «А»): имя теперь есть в формализации (ProcessNinePoint.v), блок страницы совпадает с исходником |
| `one_process` (138) | Definition | Closed under the global context | IV.2 RealProcess как тип, стр. 1043 | верно | исправлено 12.11 (шаг 8, слово автора «А»): определение добавлено в ProcessNinePoint.v; блок страницы совпадает с исходником |
| `nine_process_equiv_one` (150) | Theorem | Closed under the global context | IV.2 RealProcess как тип, стр. 1036 | верно | исправлено 12.11 (шаг 8, слово автора «А»): схема стала кодом — в ProcessNinePoint.v добавлены nine_process, one_process, nine_process_lt_one_stagewise и Theorem nine_process_equiv_one : cauchy_equiv nine_process one_process (доказательство — теорема первой линии nine_equiv_one, линии совпадают по CauchyProcessBridge); Closed under the global context |
| `nine_process_equiv_one` (150) | Theorem | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 728 | верно | исправлено 12.11 (шаг 8, слово автора «А»): было «доступен через `nine_raw_is_Cauchy` и мост»; перенос выполнен — Theorem nine_process_equiv_one : cauchy_equiv nine_process one_process; Closed under the global context |

---

## #897 — `src/process/ProcessOpenQuestions.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ |  |  | IV.6 P4 как фильтр, стр. 364 | верно | шапка файла: «What Remains After 10000 Qed … Honest catalogue of what is NOT derived»; теоремы not_derived_* и future_* — о физике; в шапке «~50 Qed», действительных 36 (глава числа не называет) |

---

## #1006 — `src/process/ProcessUncountable.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ | файл |  | IV.3 Точка как класс эквивалентности процессов, стр. 893 | верно | упоминание файла; проверено существование |
| _файл целиком_ |  |  | IV.4 Несчётность процессов, стр. 130 | верно | Пересказ заголовочного комментария process/ProcessUncountable.v:13–14 («no enumeration process captures all Cauchy processes — a statement about processes, not about a set»); условие регулярности оговорено в сноске 1. |
| _файл целиком_ |  |  | IV.4 Несчётность процессов, стр. 738 | верно | Совпадает с шапкой process/ProcessUncountable.v:2–4 (Elements: nested intervals avoiding each enumerated process; Roles: diagonal process differs from every enumerated one; Rules: at step n, avoid E(n) by choosing the other third). |
| _файл целиком_ |  |  | IV.4 Несчётность процессов, стр. 761 | верно | В шапке роль названа «diagonal process differs from every enumerated one» (process/ProcessUncountable.v:3); слово «соперник» — слово главы, в файле его нет. |
| _файл целиком_ |  |  | IV.4 Несчётность процессов, стр. 930 | верно | Сноска 1 верна: файл лежит в src/process/, цитируемая мысль — строки 13–14 заголовочного комментария. |
| _файл целиком_ |  |  | IV.4 Несчётность процессов, стр. 932 | верно | Сноска 3 верна: разметка Elements / Roles / Rules стоит в шапке process/ProcessUncountable.v:2–4 и повторена в строках 16–19. |
| `si_cauchy_compat` (58) | Lemma | Closed under the global context | IV.4 Несчётность процессов, стр. 603, 908 | верно | Формулировка совпадает: forall R, ShrinkingIntervals_ERR.is_Cauchy R <-> ProcessCore.is_Cauchy R (process/ProcessUncountable.v:58). |
| `not_equiv_implies_not_process_equiv` (69) | Lemma | Closed under the global context | IV.4 Несчётность процессов, стр. 614, 909 | верно | Формулировка совпадает: ShrinkingIntervals_ERR.not_equiv R1 R2 -> ~ ProcessCore.process_equiv R1 R2 (process/ProcessUncountable.v:69). |
| `not_equiv_implies_not_process_equiv` (69) | Lemma | Closed under the global context | IV.4 Несчётность процессов, стр. 614, 909 | верно | Статус честен: поиск по src не нашёл леммы вида ~ process_equiv -> not_equiv; not_equiv используется только в ShrinkingIntervals_ERR.v, process/ProcessUncountable.v и устаревшем DiagonalArgument_ERR.v. |
| `process_uncountable` (88) | Theorem | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 895 | верно | исправлено 12.11 (шаг 10, слово автора): добавлено условие теоремы — process_uncountable (ProcessUncountable.v:88) доказана при valid_regular_enumeration E: каждый член перечисления есть регулярный процесс Коши со значениями в [0,1] (ShrinkingIntervals_ERR.v:1089); было «для всякого перечисления процессов» |
| `process_uncountable` (88) | Theorem | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 897 | верно | исправлено 12.11 (шаг 10, слово автора): вывод приведён к доказанному — регулярные перечисления процессов отрезка [0,1]; было «никакое перечисление представителей» |
| `process_uncountable` (88) | Theorem | Closed under the global context | IV.4 Несчётность процессов, стр. 810 | верно | Верно: process/ProcessUncountable.v:97 — destruct (unit_interval_uncountable_trisect_v2 E Hvalid). |
| `process_uncountable` (88) | Theorem | Closed under the global context | IV.4 Несчётность процессов, стр. 810 | верно | исправлено 12.11 (шаг 10, слово автора): блок кода приведён дословно, с приставками модулей (process/ProcessUncountable.v:88–94); было без приставок |
| `process_uncountable` (88) | Theorem | Closed under the global context | IV.4 Несчётность процессов, стр. 810 | верно | Ход доказательства описан верно (process/ProcessUncountable.v:96–101): первый конъюнкт — si_cauchy_to_process, второй переносится как есть, третий — not_equiv_implies_not_process_equiv. |
| `process_uncountable` (88) | Theorem | Closed under the global context | IV.4 Несчётность процессов, стр. 810 | верно | Исправлено 12.11; совпадает с Print Assumptions: Closed under the global context (и для process_uncountable, и для главной теоремы). |
| `process_uncountable` (88) | Theorem | Closed under the global context | IV.4 Несчётность процессов, стр. 810 | верно | Исправлено 12.11; совпадает с Print Assumptions обеих теорем. |
| `process_uncountable` (88) | Theorem | Closed under the global context | IV.4 Несчётность процессов, стр. 810 | верно | Верно: вывод process_uncountable — ~ ProcessCore.process_equiv D (E n) (process/ProcessUncountable.v:94); обратной леммы в src нет. |
| `process_uncountable` (88) | Theorem | Closed under the global context | IV.6 P4 как фильтр, стр. 347 | верно | forall E, valid_regular_enumeration E -> exists D, … forall n, ~ process_equiv D (E n); «Closed under the global context» |
| `diagonal_convergence_rate` (132) | Definition | Closed under the global context | IV.4 Несчётность процессов, стр. 457 | верно | Верно и сказано осторожно: это константа 1 # 3 (process/ProcessUncountable.v:132); теоремой с диагональным процессом она не связана — лемма diagonal_rate_valid (:134) проверяет лишь 0 < 1/3 < 1. |

---

## #1035 — `src/ProcessContinuumHypothesis.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ |  |  | IV.5 Процессный континуум, стр. 79 | верно | Theorem process_continuum_hypothesis (ProcessContinuumHypothesis.v:619); в шапке файла «41 Qed, 0 Admitted» — действительный счёт тот же (41) |
| _файл целиком_ |  |  | IV.5 Процессный континуум, стр. 412 | верно | статус честный: поиск по трём опорным файлам (closure, topolog, limit) пуст; замкнутость задана только через дерево |
| _файл целиком_ |  |  | IV.5 Процессный континуум, стр. 628 | верно | статус честный: леммы вида has_perfect_subset C -> ~ is_enumerable C нет ни в трёх опорных файлах, ни в остальном src (поиск по has_perfect_subset: только применения дихотомии в physics/ и zeta/) |
| _файл целиком_ |  |  | IV.5 Процессный континуум, стр. 715 | верно | точный перевод шапки: Elements / Roles / Rules (ProcessContinuumHypothesis.v:11–13) |
| _файл целиком_ |  |  | IV.5 Процессный континуум, стр. 823 | верно | From Stdlib Require Import Cantor (стр. 28); Cantor.of_nat, Cantor.to_nat, Cantor.cancel_of_to в countable_union_from_fam (стр. 57–68) — эта лемма без допущений |
| `is_closed` (44) | Definition | Closed under the global context | IV.5 Процессный континуум, стр. 404 | верно | блок кода (стр. 399) совпадает с ProcessContinuumHypothesis.v:43 |
| `countable_union_enum` (71) | Lemma | Axioms: ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.5 Процессный континуум, стр. 732, 848 | верно | forall F, (forall n, is_enumerable (F n)) -> is_enumerable (fun p => exists n, F n p) (ProcessContinuumHypothesis.v:70); применена в no_split_implies_enum (стр. 478) |
| `countable_union_enum` (71) | Lemma | Axioms: ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.5 Процессный континуум, стр. 732, 848 | верно | Print Assumptions countable_union_enum: только ToS_Axioms.L4_witness — совпадает |
| `countable_union_enum` (71) | Lemma | Axioms: ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.5 Процессный континуум, стр. 732, 848 | верно | исправлено 12.11 (шаг 12, слово автора «А»): было «место это поучительное… в одном месте»; мест два — countable_union_enum (:70–78, L4_witness применён напрямую) и pick_dir (:272–275, через L3_informative); Print Assumptions pick_dir: Classical_Prop.classic и ToS_Axioms.L4_witness; countable_union_enum: только L4_witness |
| `countable_union_enum` (71) | Lemma | Axioms: ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.5 Процессный континуум, стр. 732, 848 | верно | apply L4_witness к (HF n) — из exists f в {f \| …} (ProcessContinuumHypothesis.v:76–78); Print Assumptions: только L4_witness |
| `countable_union_enum` (71) | Lemma | Axioms: ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.6 P4 как фильтр, стр. 324 | верно | исправлено 12.11 (шаг 12, слово автора «А»): добавлено второе место; countable_union_enum применяет L4_witness к каждому F n (:76–78), Print Assumptions — только L4_witness; pick_dir — classic + L4_witness через L3_informative |
| `pick_dir` (273) | Definition | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.5 Процессный континуум, стр. 578, 834, 842 | верно | главная цепь chain строится из pick_dir (ProcessContinuumHypothesis.v:272–281); цена здесь не названа, а уже у pick_dir в допущениях classic и L4_witness — см. запись к стр. 818 |
| `pick_dir` (273) | Definition | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.5 Процессный континуум, стр. 578, 834, 842 | верно | исправлено 12.11 (шаг 12, слово автора «А») — абзац добавлен: pick_dir T sigma := if L3_informative (perf_subtree T (sigma ++ [false])) then false else true; perf_subtree T s := T s /\ ~ is_enumerable (paths_extending T s); L3_informative : forall P, {P} + {~P} (ToS_Axioms.v:119) стоит на classic + L4_witness; Print Assumptions pick_dir: Classical_Prop.classic и ToS_Axioms.L4_witness; countable_union_enum: только L4_witness |
| `pick_dir` (273) | Definition | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.6 P4 как фильтр, стр. 325 | верно | упоминание имени (Definition); проверено существование |
| `chain_followers_eq` (374) | Lemma | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.5 Процессный континуум, стр. 582 | верно | Lemma chain_followers_eq: два пути через sigma, следующие цепи, равны по bp_eq (ProcessContinuumHypothesis.v:373) |
| `path_classification` (408) | Lemma | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.5 Процессный континуум, стр. 583 | верно | path_classification: путь либо следует цепи, либо лежит в классе k-го отклонения (ProcessContinuumHypothesis.v:407–414); перечислимость каждого класса — chain_other_enum (стр. 310) |
| `no_split_implies_enum` (466) | Lemma | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.5 Процессный континуум, стр. 595 | верно | точная форма: для узла ядра sigma, если ни один узел главной цепи не имеет обоих потомков в ядре, пути через sigma перечислимы (ProcessContinuumHypothesis.v:465–470); пересказ главы — честное изложение идеи; в файле лемма работает внутри доказательства от противного (стр. 535–552) |
| `perf_subtree_has_splitting` (521) | Lemma | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.5 Процессный континуум, стр. 597 | верно | точная форма: всякий узел ядра (узел дерева с неперечислимым множеством путей, perf_subtree, стр. 202) имеет продолжение, оба потомка которого лежат в ядре (ProcessContinuumHypothesis.v:520–525) |
| `process_continuum_hypothesis` (620) | Theorem | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.4 Несчётность процессов, стр. 824 | верно | Исправлено 12.11; верно: Print Assumptions называет classic и вместе с ним L4_witness — здесь упомянут только L3, L4 назван в Главе 4.5 и в Главе 4.6. |
| `process_continuum_hypothesis` (620) | Theorem | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.5 Процессный континуум, стр. 637, 646, 652, 727 | верно | блок кода (стр. 533) совпадает с ProcessContinuumHypothesis.v:619; оба условия (замкнутость, бинарная модель) названы; цена названа главой ниже (стр. 733, 812) |
| `process_continuum_hypothesis` (620) | Theorem | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.5 Процессный континуум, стр. 637, 646, 652, 727 | верно | исправлено 12.11 (шаг 13, слово автора): имя было разорвано переносом строки и на странице читалось с пробелом; теперь на одной строке (ProcessContinuumHypothesis.v:619) |
| `process_continuum_hypothesis` (620) | Theorem | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.5 Процессный континуум, стр. 637, 646, 652, 727 | верно | статус честный: утверждение Rocq — дихотомия для замкнутых совокупностей в 2^N; о мощностях в нём речи нет |
| `process_continuum_hypothesis` (620) | Theorem | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.5 Процессный континуум, стр. 637, 646, 652, 727 | верно | совпадает с шапкой файла: «PROCESS CONTINUUM HYPOTHESIS (Cantor-Bendixson)» (ProcessContinuumHypothesis.v:3–5) |
| `process_continuum_hypothesis` (620) | Theorem | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.5 Процессный континуум, стр. 637, 646, 652, 727 | верно | число и имена верны: Print Assumptions даёт Classical_Prop.classic и ToS_Axioms.L4_witness; роль L4 описана неполно — см. запись к стр. 818 |
| `process_continuum_hypothesis` (620) | Theorem | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.5 Процессный континуум, стр. 637, 646, 652, 727 | верно | совпадает с Print Assumptions главной теоремы |
| `process_continuum_hypothesis` (620) | Theorem | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.5 Процессный континуум, стр. 637, 646, 652, 727 | верно | сверено 12.11 («Верно») и повторно: Print Assumptions — Classical_Prop.classic и ToS_Axioms.L4_witness |
| `process_continuum_hypothesis` (620) | Theorem | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.5 Процессный континуум, стр. 637, 646, 652, 727 | верно | в выводе Print Assumptions только classic и L4_witness; оговорка главы о сходстве L4_witness с выбором (стр. 837–845) честна |
| `process_continuum_hypothesis` (620) | Theorem | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.5 Процессный континуум, стр. 637, 646, 652, 727 | верно | в выводе Print Assumptions такой аксиомы нет; оговорка о типах nat и nat -> bool сделана |
| `process_continuum_hypothesis` (620) | Theorem | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.5 Процессный континуум, стр. 637, 646, 652, 727 | верно | команда Print Assumptions process_continuum_hypothesis стоит в файле (ProcessContinuumHypothesis.v:703); вывод совпадает |
| `process_continuum_hypothesis` (620) | Theorem | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.5 Процессный континуум, стр. 637, 646, 652, 727 | верно | исправлено 12.11 (шаг 12, слово автора «А»): добавлено второе место L4 — выбор направления главной цепи (pick_dir через L3_informative); Print Assumptions process_continuum_hypothesis: classic + L4_witness |
| `process_continuum_hypothesis` (620) | Theorem | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.6 P4 как фильтр, стр. 269 | верно | исправлено 12.11 (шаг 12, слово автора «А»): цена совпадает (classic + L4_witness); названы оба места L4 — countable_union_enum и pick_dir (через L3_informative) |
| `process_continuum_hypothesis` (620) | Theorem | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.6 P4 как фильтр, стр. 276 | верно | исправлено 12.11; Print Assumptions: Classical_Prop.classic и ToS_Axioms.L4_witness |
| `process_continuum_hypothesis` (620) | Theorem | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.6 P4 как фильтр, стр. 348 | верно | точная форма: is_closed C -> is_enumerable C \/ has_perfect_subset C — «перечислима либо содержит совершенное подмножество»; в строке таблицы сокращено |
| `process_continuum_hypothesis` (620) | Theorem | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | X.2 Счётность конструктивна; несчётность — правило о процессах, стр. 173 | верно | исправлено 12.11; сверена цена; формулировка — при аудите части |
| `process_continuum_hypothesis` (620) | Theorem | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | XV.3 Одна диагональ halting, Райс, Кантор, Колмогоров, стр. 173 | верно | сверена цена; формулировка — при аудите части |
| `process_continuum_hypothesis` (620) | Theorem | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | XV.7 Синтез одна диагональ, один дискриминант, стр. 43 | верно | исправлено 12.11; сверена цена; формулировка — при аудите части |
| `process_continuum_hypothesis` (620) | Theorem | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | XX.1 Граница финитизации, стр. 163 | верно | исправлено 12.11; сверена цена; формулировка — при аудите части |
| `process_continuum_hypothesis` (620) | Theorem | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | Формализация, стр. 100 | верно | сверена цена; формулировка — при аудите части |
| `no_intermediate_process_type` (642) | Theorem | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.5 Процессный континуум, стр. 614, 665, 730 | верно | утверждение дословно то же; доказательство — exact process_continuum_hypothesis (ProcessContinuumHypothesis.v:641–645) |
| `no_intermediate_process_type` (642) | Theorem | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.5 Процессный континуум, стр. 614, 665, 730 | верно | исправлено 12.11 (шаг 13, слово автора): было «Имя файла `no_intermediate_process_ type`»; это второе имя теоремы (ProcessContinuumHypothesis.v:642), файла с таким именем нет; имя теперь стоит на одной строке |
| `PCH_structural_dichotomy` (648) | Theorem | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.5 Процессный континуум, стр. 622 | верно | is_closed C -> ~ is_enumerable C -> has_perfect_subset C (ProcessContinuumHypothesis.v:647); выведена из главной теоремы |
| `full_has_perfect` (676) | Theorem | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.5 Процессный континуум, стр. 607 | верно | формулировка верна; цена в главе не названа, по компилятору — classic и L4_witness: теорема выведена из самой дихотомии (PCH_structural_dichotomy + неперечислимость, стр. 675–680), а не предъявлением свидетеля; прямой свидетель mem := fun _ => True дал бы 0 допущений — кандидат в бэклог формализации |
| `empty_closed_enum` (683) | Lemma | Closed under the global context | IV.5 Процессный континуум, стр. 605 | верно | is_closed (fun _ => False) /\ is_enumerable (fun _ => False) (ProcessContinuumHypothesis.v:682); без допущений |

---

## #1036 — `src/ProcessDiagonal.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ |  |  | IV.5 Процессный континуум, стр. 78 | верно | flip, diagonal, diagonal_differs, cantor_for_processes (ProcessDiagonal.v:38–122); файл импортирует ProcessTypes (стр. 31) |
| `flip` (38) | Definition | Closed under the global context | IV.5 Процессный континуум, стр. 237, 264, 268, 285, 292 | верно | блок кода (стр. 233) совпадает с ProcessDiagonal.v:38 |
| `diagonal` (41) | Definition | Closed under the global context | IV.5 Процессный континуум, стр. 283, 310 | верно | блок кода (стр. 241) совпадает с ProcessDiagonal.v:41: fun n => flip (f n n) |
| `flip_neq` (53) | Lemma | Closed under the global context | IV.5 Процессный континуум, стр. 286 | верно | Lemma flip_neq : forall b, flip b <> b (ProcessDiagonal.v:53); применена в diagonal_differs (стр. 90) |
| `diagonal_differs` (85) | Lemma | Closed under the global context | IV.5 Процессный континуум, стр. 274, 290, 299, 874 | верно | forall f n, ~ bp_eq (diagonal f) (f n) (ProcessDiagonal.v:85); ход доказательства в главе совпадает с файлом: подстановка шага n и flip_neq (стр. 86–91) |
| `diagonal_differs` (85) | Lemma | Closed under the global context | IV.5 Процессный континуум, стр. 274, 290, 299, 874 | верно | Print Assumptions: Closed under the global context; команда действительно стоит в файле (ProcessDiagonal.v:94) |
| `diagonal_differs` (85) | Lemma | Closed under the global context | IV.5 Процессный континуум, стр. 274, 290, 299, 874 | верно | Closed under the global context |
| `diagonal_differs` (85) | Lemma | Closed under the global context | X.2 Счётность конструктивна; несчётность — правило о процессах, стр. 91, 105, 133, 156, 173, 175, 176 | верно | сверена цена; формулировка — при аудите части |
| `binary_processes_not_enumerable` (108) | Theorem | Closed under the global context | IV.5 Процессный континуум, стр. 319 | верно | блок кода (стр. 314) совпадает с ProcessDiagonal.v:108; без допущений (сверено и 12.11) |
| `binary_processes_not_enumerable` (108) | Theorem | Closed under the global context | IV.5 Процессный континуум, стр. 327 | верно | исправлено 12.11 (шаг 13, слово автора): было «проще и конструктивнее» — остаток контраста, снятого 12.11; binary_processes_not_enumerable (ProcessDiagonal.v:108) и unit_interval_uncountable_trisect_v2 (ShrinkingIntervals_ERR.v:3569) обе «Closed under the global context» |
| `binary_processes_not_enumerable` (108) | Theorem | Closed under the global context | X.2 Счётность конструктивна; несчётность — правило о процессах, стр. 104, 176 | верно | сверена цена; формулировка — при аудите части |
| `binary_processes_not_enumerable` (108) | Theorem | Closed under the global context | XV.3 Одна диагональ halting, Райс, Кантор, Колмогоров, стр. 173 | верно | исправлено 12.11; сверена цена; формулировка — при аудите части |
| `binary_processes_not_enumerable` (108) | Theorem | Closed under the global context | Формализация, стр. 92 | верно | сверена цена; формулировка — при аудите части |
| `cantor_for_processes` (118) | Theorem | Closed under the global context | IV.5 Процессный континуум, стр. 308 | верно | блок кода (стр. 303) совпадает с ProcessDiagonal.v:118; свидетель в доказательстве — exists (diagonal f) (стр. 121); без допущений |
| `cantor_for_processes` (118) | Theorem | Closed under the global context | X.2 Счётность конструктивна; несчётность — правило о процессах, стр. 104, 176 | верно | сверена цена; формулировка — при аудите части |
| `bp_eq_not_enum_witness` (208) | Lemma | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P | IV.5 Процессный континуум, стр. 872 | верно | число верно: Print Assumptions по всем объявлениям — в ProcessDiagonal.v classic только у bp_eq_not_enum_witness (стр. 208), остальные 21 замкнуты; в ProcessTypes.v classic только у not_enum_union (стр. 398), остальные 46 замкнуты |

---

## #1037 — `src/ProcessGeneral.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ |  |  | IV.2 RealProcess как тип, стр. 533 | верно | Шапка ProcessGeneral.v:6–11: «CauchyReal.v instantiates it for Q. This file provides the GENERAL theory over arbitrary types. GenProcess A := nat -> A». |
| _файл целиком_ |  |  | IV.2 RealProcess как тип, стр. 546 | верно | Расположение файлов верно. |
| _файл целиком_ |  |  | IV.2 RealProcess как тип, стр. 1103 | верно | Действительный счёт: 16 Qed, 0 Admitted, 0 Axiom; все 16 лемм — «Closed under the global context». |
| _файл целиком_ | файл |  | IV.3 Точка как класс эквивалентности процессов, стр. 261 | верно | упоминание файла; проверено существование |
| `GenProcess` (50) | Definition | Closed under the global context | IV.2 RealProcess как тип, стр. 532, 570, 626, 894 | верно | Совпадает с ProcessGeneral.v:50. |
| `observe` (53) | Definition | Closed under the global context | IV.2 RealProcess как тип, стр. 172 | верно | Блок кода (стр. 163) совпадает с ProcessGeneral.v:53. |
| `prefix` (56) | Fixpoint | Closed under the global context | IV.2 RealProcess как тип, стр. 173, 174 | верно | Блок кода (стр. 165) совпадает с ProcessGeneral.v:56. |
| `prefix_length` (83) | Lemma | Closed under the global context | IV.2 RealProcess как тип, стр. 177 | верно | ProcessGeneral.v:83: length (prefix p n) = n; допущений нет. |
| `prefix_nth` (93) | Lemma | Closed under the global context | IV.2 RealProcess как тип, стр. 179 | верно | ProcessGeneral.v:93: при k < n nth k (prefix p n) d = p k; условие k < n в главе подразумевается. |
| `process_equiv` (122) | Definition | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 243, 245, 258, 260, 299, 309, 699, 720 | верно | ProcessGeneral.v:122: process_equiv {A} (eq_A) p1 p2 := forall n, eq_A (p1 n) (p2 n) — параметр eq_A, согласие на каждом шаге; описание точное. |
| `is_cauchy_gen` (190) | Definition | Closed under the global context | IV.2 RealProcess как тип, стр. 544, 557, 575 | верно | ProcessGeneral.v:190: параметр dist : A -> A -> Q произволен. |
| `Qdist` (217) | Definition | Closed under the global context | IV.2 RealProcess как тип, стр. 556, 566 | верно | ProcessGeneral.v:217: Qdist x y := Qabs (x - y). |
| `cauchy_Q_equiv` (220) | Lemma | Closed under the global context | IV.2 RealProcess как тип, стр. 558, 1070 | верно | ProcessGeneral.v:220: is_cauchy a <-> is_cauchy_gen Qdist a; блок кода (стр. 561) совпадает; допущений нет. |
| `cauchy_seq_is_gen_process` (228) | Lemma | Closed under the global context | IV.2 RealProcess как тип, стр. 569 | верно | ProcessGeneral.v:228: forall cs, is_cauchy_gen Qdist (cs_seq cs); допущений нет. |

---

## #1038 — `src/ProcessTypes.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ |  |  | IV.5 Процессный континуум, стр. 77 | верно | BinProcess, PrunedTree, BinCollection объявлены в файле (ProcessTypes.v:34, 67, 51) |
| _файл целиком_ |  |  | IV.5 Процессный континуум, стр. 879 | верно | совпадает с шапкой файла «29 Qed, 0 Admitted, 0 axioms (except classic for 1 lemma)» (ProcessTypes.v:14); действительный счёт Qed — 29 |
| `BinProcess` (34) | Definition | Closed under the global context | IV.5 Процессный континуум, стр. 723 | верно | блок кода совпадает с ProcessTypes.v:34 |
| `bp_eq` (37) | Definition | Closed under the global context | IV.5 Процессный континуум, стр. 175, 191, 214, 281 | верно | блок кода совпадает с ProcessTypes.v:37; пересказ «совпадают на каждом шаге» точен |
| `BinCollection` (51) | Definition | Closed under the global context | IV.5 Процессный континуум, стр. 196, 548, 861 | верно | блок кода совпадает с ProcessTypes.v:51 |
| `is_enumerable` (54) | Definition | Closed under the global context | IV.5 Процессный континуум, стр. 212 | верно | блок кода (стр. 207) совпадает с ProcessTypes.v:54; пересказ точен: exists f, forall p, C p -> exists n, bp_eq (f n) p |
| `PrunedTree` (67) | Definition | Closed under the global context | IV.5 Процессный континуум, стр. 378, 479, 731 | верно | блок кода (стр. 345) совпадает с ProcessTypes.v:67; «P4-рефакторинг» — слова шапки файла (стр. 15) |
| `is_tree` (70) | Definition | Closed under the global context | IV.5 Процессный континуум, стр. 363, 379, 382 | верно | блок кода (стр. 366) совпадает с ProcessTypes.v:70: T [] = true и замкнутость по removelast; требования «нет тупиков» в определении нет — оговорка главы верна |
| `has_left` (74) | Definition | Closed under the global context | IV.5 Процессный континуум, стр. 437 | верно | has_left T sigma := T (sigma ++ [false]) = true (ProcessTypes.v:74) |
| `has_right` (78) | Definition | Closed under the global context | IV.5 Процессный континуум, стр. 438 | верно | has_right T sigma := T (sigma ++ [true]) = true (ProcessTypes.v:78) |
| `is_splitting` (82) | Definition | Closed under the global context | IV.5 Процессный континуум, стр. 439 | верно | блок кода (стр. 443) совпадает с ProcessTypes.v:82 |
| `is_path` (86) | Definition | Closed under the global context | IV.5 Процессный континуум, стр. 391 | верно | is_path T p := forall n, T (bp_prefix p n) = true; bp_prefix p n := map p (seq 0 n) (ProcessTypes.v:86, 40) |
| `is_perfect` (90) | Definition | Closed under the global context | IV.5 Процессный континуум, стр. 384 | верно | блок кода (стр. 457) совпадает с ProcessTypes.v:90; одноимённое определение есть и в settheory/CantorBendixsonFull.v:52 — глава говорит о первом |
| `has_perfect_subset` (99) | Definition | Closed under the global context | IV.5 Процессный континуум, стр. 471, 482 | верно | четыре конъюнкта определения переданы точно: корень, замкнутость по removelast, продолжение до узла с обоими потомками, пути в C (ProcessTypes.v:99–109) |
| `has_perfect_subset` (99) | Definition | Closed under the global context | IV.5 Процессный континуум, стр. 471, 482 | верно | exists (mem : list bool -> Prop) (ProcessTypes.v:100); ядро perf_subtree : list bool -> Prop (ProcessContinuumHypothesis.v:202); статус «разрешимо исходное дерево, ядро — нет» честный |
| `has_perfect_subset` (99) | Definition | Closed under the global context | IV.6 P4 как фильтр, стр. 303 | верно | has_perfect_subset: exists (mem : list bool -> Prop), … (ProcessTypes.v:99); perf_subtree T : list bool -> Prop (ProcessContinuumHypothesis.v:202) |
| `tree_mem_dec` (279) | Lemma | Closed under the global context | IV.5 Процессный континуум, стр. 356 | верно | Closed under the global context; доказательство — destruct (T sigma) (ProcessTypes.v:279–283); «другие» — has_left_dec, has_right_dec, bool_eq_dec, bp_eq_dec_at_n (стр. 264–299), тоже замкнуты |
| `is_splitting_dec` (301) | Lemma | Closed under the global context | IV.5 Процессный континуум, стр. 356 | верно | Closed under the global context (ProcessTypes.v:301) |
| `not_enum_union` (398) | Lemma | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P | IV.5 Процессный континуум, стр. 877 | верно | Print Assumptions: Classical_Prop.classic; в доказательстве classic (is_enumerable A) и classic (is_enumerable B) (ProcessTypes.v:403–404); импорт ToS_Axioms — стр. 25 |

---

## #1047 — `src/RealField.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ | файл |  | IV.2 RealProcess как тип, стр. 327 | верно | упоминание файла; проверено существование |
| _файл целиком_ |  |  | IV.3 Точка как класс эквивалентности процессов, стр. 565 | верно | Законы коммутативного кольца с точностью до ~~ доказаны: cauchy_add_comm / _assoc / _zero_r / _neg_r (CauchyReal.v:336–370), cauchy_mul_comm / _assoc / _one_l / _one_r, cauchy_distrib_l / _r (RealField.v:240–291); все — Closed under the global context. |
| `cauchy_mul` (172) | Definition | Closed under the global context | IV.2 RealProcess как тип, стр. 327, 593, 928, 1081 | верно | RealField.v:172; законы: коммутативность :240, ассоциативность :250, единица :261, дистрибутивность :280, обратный для положительных :396; все 17 лемм файла без допущений. |
| `cauchy_mul` (172) | Definition | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 569 | верно | RealField.v:172; cauchy_mul_comm (:240), cauchy_mul_assoc (:250), cauchy_mul_one_r / _one_l (:261, :271), cauchy_distrib_l / _r (:280, :291) — все четыре названных закона есть. |
| `cauchy_mul_compat` (181) | Lemma | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 572 | верно | RealField.v:181: a ~~ a' -> b ~~ b' -> cauchy_mul a b ~~ cauchy_mul a' b'. |
| `cauchy_inv_is_cauchy` (333) | Lemma | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 578 | верно | RealField.v:333 — лемма о свойстве Коши у обратной последовательности при положительном зазоре q < a_n; сам обратный — cauchy_inv_pos (:390). Уточнение: в RealField.v закрыта положительная сторона, общий случай «отделён от нуля» — в RealFieldApart.v (сноска 2). |

---

## #1868 — `src/RealFieldApart.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ |  | Closed under the global context (все 8 утверждений файла) | IV.3 Точка как класс эквивалентности процессов, стр. 956 | верно | исправлено 12.11 (шаг 9, слово автора «А»): было 6; после шага 9 в RealFieldApart.v 8 Qed, 0 Admitted; Print Assumptions для всех восьми — Closed under the global context. |
| `apart0` (59) | Definition | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 956 | верно | RealFieldApart.v:56: exists q > 0, exists N, forall n >= N, q < \|x_n\| — предъявленный рациональный зазор. |
| `apart_has_inverse` (103) | Theorem | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 956 | верно | apart0 x -> exists y, cauchy_equiv (cauchy_mul x y) cauchy_one (RealFieldApart.v:103); Closed under the global context |
| `inverse_implies_apart` (129) | Theorem | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 956 | верно | исправлено 12.11 (шаг 9, слово автора «А»): теорема добавлена шагом 9; forall x y, cauchy_equiv (cauchy_mul x y) cauchy_one -> apart0 x; Closed under the global context |
| `invertible_iff_apart` (156) | Theorem | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 956 | верно | исправлено 12.11 (шаг 9, слово автора «А») — правка формализации: в RealFieldApart.v доказана обратная сторона, inverse_implies_apart : cauchy_equiv (cauchy_mul x y) cauchy_one -> apart0 x (зазор 1/(2B) из границы обратного, cauchy_bounded), и invertible_iff_apart : apart0 x <-> exists y, cauchy_equiv (cauchy_mul x y) cauchy_one; Closed under the global context |
| `apartness_field` (188) | Theorem | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 956 | верно | RealFieldApart.v — конъюнкция трёх: апартный в конце концов одного знака (apart0_sign); апартность равносильна обратимости (после шага 9 второй член — invertible_iff_apart, было: только apart_has_inverse); ~ apart0 0. |

---

## #1049 — `src/RealPointSetoid.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ |  | Closed under the global context (все 7 утверждений файла) | IV.3 Точка как класс эквивалентности процессов, стр. 76 | верно | Сверено с файлом: Instance cauchy_equiv_Equivalence (RealPointSetoid.v:52), Definition RealPoint := CauchySeq (:74), Proper-экземпляры cauchy_add_Proper, cauchy_mul_Proper, cauchy_neg_Proper (:81, :85, :89); статус «формализован» честен. |
| _файл целиком_ |  | Closed under the global context (все 7 утверждений файла) | IV.3 Точка как класс эквивалентности процессов, стр. 413 | верно | Print Assumptions для cauchy_equiv_Equivalence, process_equiv_Equivalence, cauchy_add_Proper, cauchy_mul_Proper, cauchy_neg_Proper и двух примеров файла — Closed under the global context. |
| _файл целиком_ |  |  | IV.4 Несчётность процессов, стр. 687 | верно | Статус честен: RealPointSetoid.v:71–74 — «NOT a reified quotient object», RealPoint := CauchySeq; класс задан отношением, а не отдельным типом. |
| `cauchy_equiv_Equivalence` (52) | Instance | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 397 | верно | Instance cauchy_equiv_Equivalence (RealPointSetoid.v:52) собран ровно из cauchy_equiv_refl / _sym / _trans. |
| `cauchy_equiv_Equivalence` (52) | Instance | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 933 | верно | Итог повторяет § 3.3 и § 3.4.3: три леммы CauchyReal.v:67–91 и Instance RealPointSetoid.v:52; всё Closed under the global context. |
| `cauchy_add_Proper` (81) | Instance | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 402 | верно | RealPointSetoid.v:81: Proper (cauchy_equiv ==> cauchy_equiv ==> cauchy_equiv) cauchy_add. |
| `cauchy_mul_Proper` (85) | Instance | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 402, 572, 767, 937 | верно | RealPointSetoid.v:85: Proper (cauchy_equiv ==> cauchy_equiv ==> cauchy_equiv) cauchy_mul; доказан через cauchy_mul_compat. |

---

## #1050 — `src/RealPointTopology.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ | файл |  | IV.3 Точка как класс эквивалентности процессов, стр. 554 | верно | упоминание файла; проверено существование |
| `cauchy_le_compat` (43) | Lemma | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 553, 559, 568, 768, 795, 938, 946 | верно | RealPointTopology.v:43: a ~~ a' -> b ~~ b' -> cauchy_le a b -> cauchy_le a' b' — формулировка главы совпадает с утверждением. |
| `cauchy_le_Proper` (61) | Instance | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 554 | верно | Instance cauchy_le_Proper: Proper (cauchy_equiv ==> cauchy_equiv ==> iff) cauchy_le (RealPointTopology.v:61) — «в обе стороны» = iff; статус «теперь доказана» честен. |

---

## #1059 — `src/settheory/CantorBendixsonFull.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| `S_finite_scattered` (344) | Lemma | Closed under the global context | X.6 Синтез Части X что доказуемо без выбора, и карта границ, стр. 56 | верно | речь о производной множества в CantorBendixsonFull.v (не о процессной континуум-гипотезе главы IV.5); `CB_omega_finite_empty`, `CB_omega_accumulation_in_parent` — тоже без допущений |

---

## #1062 — `src/settheory/ChoicePriceMap.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ |  |  | IV.6 P4 как фильтр, стр. 244 | верно | для шкал силы (DerivationStrength, IFStrength) верно; для оси аксиомной цены такая таблица в Rocq теперь есть — settheory/ChoicePriceMap.v (июнь 2026, исправлена в октябре): RCountabilityQ, RDiagonal, RShrinkingIntervals — PZero, RContinuumHypothesis — PL3_L4; строки таблицы главы с ней согласуются; упоминать ли её здесь — решение автора |
| _файл целиком_ |  |  | IV.6 P4 как фильтр, стр. 315 | верно | модули выбора стандартной библиотеки (ClassicalChoice, Epsilon, IndefiniteDescription) вне комментариев не встречаются ни в одном файле src; о силе L4 — следующие записи |
| `l4_statement_gives_functional_choice` (164) | Lemma | Closed under the global context | IV.6 P4 как фильтр, стр. 328 | верно | техническая сила подтверждена машинно: из утверждения L4_witness следует функциональный выбор по произвольному семейству (ChoicePriceMap.v:164, без допущений), вместе с classic — эпсилон Гильберта; слово главы «choice-подобный» этому отвечает |

---

## #1064 — `src/settheory/HigmanLemma.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ |  |  | X.6 Синтез Части X что доказуемо без выбора, и карта границ, стр. 57 | не проверено | 12.11 не проверялось; сводная страница «Формализация» для `higman_unit` называет «нет», для `dickson_pair` — исключённое третье: сверить при аудите Части X |

---

## #1065 — `src/settheory/KruskalFull.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| `depth1_wqo` (129) | Lemma | Closed under the global context | Формализация, стр. 95 | верно | сверена цена; формулировка — при аудите части |
| `L5_from_kruskal` (166) | Theorem | Closed under the global context | Формализация, стр. 95 | верно | сверена цена; формулировка — при аудите части |

---

## #1066 — `src/settheory/KruskalTree.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| `kruskal_chains` (265) | Lemma | Closed under the global context | X.6 Синтез Части X что доказуемо без выбора, и карта границ, стр. 56 | верно | исправлено 12.11 (перенесено из яруса classic); `kruskal_forks` (KruskalTree.v:276) — тоже без допущений |
| `kruskal_chains` (265) | Lemma | Closed under the global context | Формализация, стр. 95 | верно | сверена цена; формулировка — при аудите части |
| `kruskal_forks` (276) | Lemma | Closed under the global context | Формализация, стр. 95 | верно | сверена цена; формулировка — при аудите части |

---

## #1068 — `src/ShrinkingIntervals_ERR.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ |  |  | IV.4 Несчётность процессов, стр. 64 | верно | Верно: diagonal_trisect_v2 (ShrinkingIntervals_ERR.v:2987) и unit_interval_uncountable_trisect_v2 (:3569); process_uncountable — process/ProcessUncountable.v:88, выводится из главной теоремы (:97). |
| _файл целиком_ |  |  | IV.4 Несчётность процессов, стр. 813 | верно | Исправлено 12.11; верно: импорт ToS_Axioms и Classical_Pred_Type (ShrinkingIntervals_ERR.v:72–73), заметка — :76–85; ни classic, ни леммы Classical_Pred_Type не применяются ни в одном доказательстве файла (поиск по тексту: слово встречается только в комментариях :78, :83, :3621). |
| _файл целиком_ |  |  | IV.4 Несчётность процессов, стр. 844 | верно | Исправлено 12.11; число и факт верны: три команды — для shrinking_interval_Cauchy, bisect_width_n (ShrinkingIntervals_ERR.v:3588–3589) и главной теоремы (:3632); все три дают Closed under the global context. |
| _файл целиком_ |  |  | IV.4 Несчётность процессов, стр. 868 | верно | Исправлено 12.11; совпадает с Print Assumptions главной теоремы. |
| _файл целиком_ |  |  | IV.4 Несчётность процессов, стр. 931 | верно | Сноска 2 верна: комментарии со старым множителем 12 — ShrinkingIntervals_ERR.v:282, 2817, 2827, 2831, 3270, 3599–3600; действующие определения — 48 (:2835) и 24 (:2841). |
| _файл целиком_ | файл |  | IV.6 P4 как фильтр, стр. 268 | верно | упоминание файла; проверено существование |
| `RealProcess` (159) | Definition | Closed under the global context | IV.4 Несчётность процессов, стр. 186, 674 | верно | Верно: Definition RealProcess := nat -> Q (ShrinkingIntervals_ERR.v:159); то же определение стоит в ядре process/ProcessCore.v:34 (всего 10 одноимённых объявлений в src). |
| `is_Regular_Cauchy` (180) | Definition | Closed under the global context | IV.4 Несчётность процессов, стр. 246 | верно | Блок кода (стр. 290) совпадает с ShrinkingIntervals_ERR.v:180; оценка стоит для m, n > 0, как и в блоке. |
| `trisect_delta_bound` (289) | Lemma | Closed under the global context | IV.4 Несчётность процессов, стр. 448 | верно | Формулировка совпадает: forall n, 2 * (1 / (24 * 3^n)) < (1 / 3^n) / 3 (ShrinkingIntervals_ERR.v:289) — для всех n, как и сказано. |
| `Archimedean_pow3` (327) | Theorem | Closed under the global context | IV.4 Несчётность процессов, стр. 481 | верно | Имя и файл верны: forall eps > 0, exists N, 1 / 3^N < eps (ShrinkingIntervals_ERR.v:327); в файле объявлена словом Theorem, не Lemma. |
| `Regular_implies_Cauchy` (471) | Lemma | Closed under the global context | IV.4 Несчётность процессов, стр. 320 | верно | Формулировка совпадает: forall R, is_Regular_Cauchy R -> is_Cauchy R (ShrinkingIntervals_ERR.v:471). |
| `shrinking_interval_Cauchy` (559) | Theorem | Closed under the global context | III.4 От позиции к процессу, стр. 738, 832, 1059, 1060 | верно | исправлено 12.11; сверена цена; формулировка — при аудите части; одноимённая теорема есть и в Archimedean_ERR.v:158, тоже без допущений |
| `Enumeration` (1080) | Definition | Closed under the global context | IV.4 Несчётность процессов, стр. 54, 188 | верно | Блок кода (стр. 171) совпадает с ShrinkingIntervals_ERR.v:1080; одноимённое определение есть ещё в устаревшем DiagonalArgument_ERR.v. |
| `valid_enumeration` (1083) | Definition | Closed under the global context | IV.4 Несчётность процессов, стр. 237 | верно | Блок кода (стр. 233) совпадает с ShrinkingIntervals_ERR.v:1083. |
| `valid_regular_enumeration` (1089) | Definition | Closed under the global context | IV.4 Несчётность процессов, стр. 752, 930 | верно | Блок кода (стр. 241) совпадает с ShrinkingIntervals_ERR.v:1089. |
| `valid_regular_enumeration` (1089) | Definition | Closed under the global context | IV.4 Несчётность процессов, стр. 752, 930 | верно | исправлено 12.11 (шаг 10, слово автора): было `valid_regular` — такого имени нет; определение — valid_regular_enumeration (ShrinkingIntervals_ERR.v:1089) |
| `valid_regular_implies_valid` (1094) | Lemma | Closed under the global context | IV.4 Несчётность процессов, стр. 249 | верно | Формулировка совпадает: valid_regular_enumeration E -> valid_enumeration E (ShrinkingIntervals_ERR.v:1094). |
| `not_equiv` (1109) | Definition | Closed under the global context | IV.4 Несчётность процессов, стр. 506, 521, 532, 611, 615, 649, 656, 661 | верно | Пересказ совпадает с определением; блок кода (стр. 509) совпадает с ShrinkingIntervals_ERR.v:1109. |
| `avoid_E` (1287) | Definition | Closed under the global context | IV.4 Несчётность процессов, стр. 380 | верно | упоминание имени (Definition); проверено существование |
| `diagonal_intervals` (1300) | Definition | Closed under the global context | IV.4 Несчётность процессов, стр. 381 | верно | Верно: раздел 10 файла помечен «SUPERSEDED: This section uses BISECTION which has edge cases» (ShrinkingIntervals_ERR.v:1243); avoid_E — :1287, diagonal_intervals — :1300. |
| `TrisectChoice` (2184) | Inductive | Closed under the global context | IV.4 Несчётность процессов, стр. 402 | верно | Число верно: тип TrisectChoice из трёх конструкторов (ShrinkingIntervals_ERR.v:2184) и три операции trisect_left, trisect_middle, trisect_right (:2187–2195); блок кода совпадает. |
| `smart_trisect_choice` (2562) | Definition | Closed under the global context | IV.4 Несчётность процессов, стр. 418 | верно | Верно: определение (ShrinkingIntervals_ERR.v:2562) ветвится по conf_below / conf_above, которые решаются через Qlt_le_dec (:2554–2559); функция возвращает только левую или правую треть. |
| `trisect_ref` (2835) | Definition | Closed under the global context | IV.4 Несчётность процессов, стр. 341, 931 | верно | Верно: trisect_ref n := 48 * 3^n (ShrinkingIntervals_ERR.v:2835); шаг trisect_iter_v2 берёт приближение E n (trisect_ref n) (:2882–2892). |
| `trisect_delta` (2841) | Definition | Closed under the global context | IV.4 Несчётность процессов, стр. 931 | верно | Числа верны: trisect_ref n := 48 * 3^n (ShrinkingIntervals_ERR.v:2835), trisect_delta n := 1 / (24 * 3^n) (:2841), ширина после n шагов равна 1/3^n — лемма trisect_iter_v2_width (:2895). |
| `diagonal_trisect_v2` (2987) | Definition | Closed under the global context | IV.4 Несчётность процессов, стр. 470, 557 | верно | Совпадает с определением: полусумма концов состояния trisect_iter_v2 E [0,1] n (ShrinkingIntervals_ERR.v:2987); шаг строится по E n (trisect_ref n) и trisect_delta n, как описано в абзаце. |
| `diagonal_trisect_v2_is_Cauchy` (3334) | Lemma | Closed under the global context | IV.4 Несчётность процессов, стр. 478 | верно | Формулировка: forall E, is_Cauchy (diagonal_trisect_v2 E) — без условий на E; ход доказательства описан верно: Archimedean_pow3 и trisect_iter_v2_width (ShrinkingIntervals_ERR.v:3334–3382). |
| `diagonal_trisect_v2_in_unit` (3385) | Lemma | Closed under the global context | IV.4 Несчётность процессов, стр. 491 | верно | Формулировка совпадает: forall E n, 0 <= diagonal_trisect_v2 E n <= 1 (ShrinkingIntervals_ERR.v:3385). |
| `diagonal_trisect_v2_differs_from_E_n` (3423) | Lemma | Closed under the global context | IV.4 Несчётность процессов, стр. 504 | верно | Формулировка: forall E n, valid_regular_enumeration E -> not_equiv (diagonal_trisect_v2 E) (E n) (ShrinkingIntervals_ERR.v:3423) — условие регулярности стоит в самой лемме, глава называет его в § 4.4. |
| `diagonal_trisect_v2_differs_from_E_n` (3423) | Lemma | Closed under the global context | IV.4 Несчётность процессов, стр. 504 | верно | По существу верно: зазор положителен по лемме regular_excluded_by_trisection_v2 (:3272); в доказательстве порогом взята половина зазора (exists (gap / 2), :3452 и :3512), а расхождение на поздних шагах не меньше всего зазора — различие техническое. |
| `unit_interval_uncountable_trisect_v2` (3569) | Theorem | Closed under the global context | III.4 От позиции к процессу, стр. 1060 | верно | исправлено 12.11; сверена цена; формулировка — при аудите части |
| `unit_interval_uncountable_trisect_v2` (3569) | Theorem | Closed under the global context | IV.4 Несчётность процессов, стр. 591, 809 | верно | Словесная формулировка совпадает с теоремой: условие valid_regular_enumeration E; вывод — is_Cauchy D, 0 <= D m <= 1, not_equiv D (E n) для всех n (ShrinkingIntervals_ERR.v:3569). |
| `unit_interval_uncountable_trisect_v2` (3569) | Theorem | Closed under the global context | IV.4 Несчётность процессов, стр. 591, 809 | верно | Статус честен: теорем несчётности с условием valid_enumeration в src нет; устаревший DiagonalArgument_ERR.v (цифровая диагональ) доказывает лишь сходимость диагонали и её нахождение в отрезке, но не отличие от членов перечисления. |
| `unit_interval_uncountable_trisect_v2` (3569) | Theorem | Closed under the global context | IV.4 Несчётность процессов, стр. 591, 809 | верно | Дословное чтение совпадает; блок кода (стр. 544–551) совпадает с ShrinkingIntervals_ERR.v:3569; свидетель в доказательстве — diagonal_trisect_v2 E (:3577). |
| `unit_interval_uncountable_trisect_v2` (3569) | Theorem | Closed under the global context | IV.4 Несчётность процессов, стр. 591, 809 | верно | Статус честен: в выводе теоремы только is_Cauchy D, границы отрезка и not_equiv; is_Regular_Cauchy D не заявлено. |
| `unit_interval_uncountable_trisect_v2` (3569) | Theorem | Closed under the global context | IV.4 Несчётность процессов, стр. 591, 809 | верно | Исправлено 12.11; совпадает с Print Assumptions: Closed under the global context. |
| `unit_interval_uncountable_trisect_v2` (3569) | Theorem | Closed under the global context | IV.4 Несчётность процессов, стр. 591, 809 | верно | исправлено 12.11 (шаг 10, слово автора): добавлено слово «регулярный» — теорема доказана для valid_regular_enumeration; ниже в том же разборе глава сама пишет «любой регулярный процесс-нумератор» |
| `unit_interval_uncountable_trisect_v2` (3569) | Theorem | Closed under the global context | IV.4 Несчётность процессов, стр. 591, 809 | верно | Исправлено 12.11; подтверждено повторно на полной сборке 12.11: обе теоремы — Closed under the global context. |
| `unit_interval_uncountable_trisect_v2` (3569) | Theorem | Closed under the global context | IV.4 Несчётность процессов, стр. 591, 809 | верно | Совпадает с Print Assumptions (допущений нет вовсе); выбор трети — вычислимая функция smart_trisect_choice. |
| `unit_interval_uncountable_trisect_v2` (3569) | Theorem | Closed under the global context | IV.4 Несчётность процессов, стр. 591, 809 | верно | Итоговая формулировка совпадает с теоремой: условие регулярности названо, вывод — not_equiv. |
| `unit_interval_uncountable_trisect_v2` (3569) | Theorem | Closed under the global context | IV.5 Процессный континуум, стр. 323 | верно | пересказ итога Главы 4.4: условие valid_regular_enumeration названо словом «регулярное»; вывод — существование процесса D в [0,1], не эквивалентного ни одному E n (ShrinkingIntervals_ERR.v:3569) |
| `unit_interval_uncountable_trisect_v2` (3569) | Theorem | Closed under the global context | IV.5 Процессный континуум, стр. 323 | верно | исправлено 12.11 (было: «там трисекционная диагональ опиралась на классическую логику»); Print Assumptions: Closed under the global context |
| `unit_interval_uncountable_trisect_v2` (3569) | Theorem | Closed under the global context | IV.5 Процессный континуум, стр. 323 | верно | верно: та — о процессах Коши (RealProcess) при valid_regular_enumeration, эта — о BinProcess без условий; две разные теоремы в двух файлах |
| `unit_interval_uncountable_trisect_v2` (3569) | Theorem | Closed under the global context | IV.6 P4 как фильтр, стр. 13 | верно | условие «регулярного перечисления» названо, как в теореме (valid_regular_enumeration E); то же в строках 48–50 |
| `unit_interval_uncountable_trisect_v2` (3569) | Theorem | Closed under the global context | IV.6 P4 как фильтр, стр. 268 | верно | исправлено 12.11 (перенесено из строки «L3»); Print Assumptions: «Closed under the global context»; условие регулярности названо |
| `unit_interval_uncountable_trisect_v2` (3569) | Theorem | Closed under the global context | IV.6 P4 как фильтр, стр. 419 | верно | исправлено 12.11 (шаг 13, слово автора): было «два результата Части IV — на L3 и на L3+L4» — место, пропущенное при правке 12.11; unit_interval_uncountable_trisect_v2 и process_uncountable — «Closed under the global context»; на classic + L4_witness в Части IV один результат — process_continuum_hypothesis |
| `unit_interval_uncountable_trisect_v2` (3569) | Theorem | Closed under the global context | X.2 Счётность конструктивна; несчётность — правило о процессах, стр. 157, 173, 177 | верно | исправлено 12.11; сверена цена; формулировка — при аудите части |
| `unit_interval_uncountable_trisect_v2` (3569) | Theorem | Closed under the global context | X.6 Синтез Части X что доказуемо без выбора, и карта границ, стр. 56 | верно | исправлено 12.11 (перенесено из яруса classic); сверена цена; формулировка — при аудите части |
| `unit_interval_uncountable_trisect_v2` (3569) | Theorem | Closed under the global context | XV.3 Одна диагональ halting, Райс, Кантор, Колмогоров, стр. 173 | верно | исправлено 12.11; сверена цена; формулировка — при аудите части |
| `unit_interval_uncountable_trisect_v2` (3569) | Theorem | Closed under the global context | XV.7 Синтез одна диагональ, один дискриминант, стр. 46 | верно | исправлено 12.11; сверена цена; формулировка — при аудите части |
| `unit_interval_uncountable_trisect_v2` (3569) | Theorem | Closed under the global context | XX.1 Граница финитизации, стр. 164 | верно | исправлено 12.11; сверена цена; формулировка — при аудите части |
| `unit_interval_uncountable_trisect_v2` (3569) | Theorem | Closed under the global context | XX.6 Что доказано, что наблюдение, что горизонт, стр. 40 | верно | исправлено 12.11; сверена цена; формулировка — при аудите части |
| `unit_interval_uncountable_trisect_v2` (3569) | Theorem | Closed under the global context | Направления/Математика/index, стр. 96 | верно | сверена цена; формулировка — при аудите части |
| `unit_interval_uncountable_trisect_v2` (3569) | Theorem | Closed under the global context | Формализация, стр. 91, 134 | верно | сверена цена; формулировка — при аудите части |

---

## #1610 — `src/stdlib/RefinementSqrt.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ |  |  | IV.2 RealProcess как тип, стр. 249 | верно | Статус честный: RefinementSqrt.v содержит newton_0…2, cf_0…2, differ_at_2, newton_better_at_2; теоремы is_Cauchy для ньютонова или цепно-дробного процесса в src нет (foundation/ContinuumLimitIsReal.v:27 сам оговаривает, что полное эпсилон-N не выведено). |

---

## #1789 — `src/TheoryOfSystems_Core_ERR.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| `System` (203) | Record | Closed under the global context | IV.3 Точка как класс эквивалентности процессов, стр. 783 | верно | Record System (L : Level) — TheoryOfSystems_Core_ERR.v:203; глава честно называет E/R/R-разбор содержательным чтением, а не объектом формализации. |
| `System` (203) | Record | Closed under the global context | IV.4 Несчётность процессов, стр. 744 | верно | упоминание имени (Record); проверено существование |

---

## #1793 — `src/ToS_Axioms.v`

| имя (строка файла) | вид | допущения | где в томе | вердикт | пометка |
|---|---|---|---|---|---|
| _файл целиком_ |  |  | IV.1 P4 бесконечность как процесс, стр. 293 | верно | объявлена в файле одна аксиома — L4_witness (ToS_Axioms.v:105); classic реэкспортирована из стандартной библиотеки (:31), что глава оговаривает следующей фразой |
| `classic` | внешнее | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P | IV.1 P4 бесконечность как процесс, стр. 298, 309, 312, 360, 361, 362, 365, 1106 | верно | ToS_Axioms.v:31 — Require Export Coq.Logic.Classical_Prop; в выводе Print Assumptions аксиома значится как Classical_Prop.classic |
| _файл целиком_ |  |  | IV.1 P4 бесконечность как процесс, стр. 1347 | верно | после правок 2026-11-12 функциональной экстенсиональности в допущениях нет (прогон: 0); аксиом бесконечности и выбора в формализации нет; «мета-аудит» (ProcessAxiomAudit.v) записывает это комментарием, а проверяет сплошной прогон Print Assumptions |
| _файл целиком_ |  |  | IV.1 P4 бесконечность как процесс, стр. 1372 | верно | три леммы: L3_informative (Defined, :119), L4_definite (:135), NNPP_from_L3 (:147) — 2 Qed и 1 Defined; шапка файла озаглавлена «ToS AXIOMS — The Formal Laws of Logic» |
| `classic` | внешнее | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P | IV.4 Несчётность процессов, стр. 756, 816, 913 | верно | Имя стандартной библиотеки: Classical_Prop.classic, переэкспортируется ToS_Axioms.v:31; одноимённые аксиомы в src (foundation/Distinction.v:36, EVT_idx.v:338, settheory/BorelDeterminacy.v:21) к теоремам главы отношения не имеют. |
| `classic` | внешнее | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P | IV.5 Процессный континуум, стр. 733, 815, 839 | верно | в допущениях стоит Classical_Prop.classic стандартной библиотеки, которую ToS_Axioms.v:31 реэкспортирует (Require Export Coq.Logic.Classical_Prop); одноимённые локальные Axiom classic (EVT_idx.v:338, foundation/Distinction.v:36, settheory/BorelDeterminacy.v:21) здесь не участвуют |
| _файл целиком_ | файл |  | IV.5 Процессный континуум, стр. 839 | верно | упоминание файла; проверено существование |
| `classic` | внешнее | аксиома стандартной библиотеки: Classical_Prop.classic : forall P : Prop, P \/ ~ P | IV.6 P4 как фильтр, стр. 147 | верно | classic в формализации — аксиома стандартной библиотеки Classical_Prop.classic, которую ToS_Axioms.v переэкспортирует (строка 31); одноимённые аксиомы объявлены ещё в foundation/Distinction.v:36, EVT_idx.v:338, settheory/BorelDeterminacy.v:21; исправлено 12.11 (шаг 3, слово автора): было «зависят только от classic — то есть от L3» |
| _файл целиком_ |  |  | IV.6 P4 как фильтр, стр. 147 | верно | исправлено 12.11 (шаг 3, слово автора): было «локализован и появляется лишь в отдельных файлах (лемма l4_witness_localized)»; лемма-вывеска удалена; сплошной прогон Print Assumptions после правок 2026-11-12: от ToS_Axioms.L4_witness зависят объявления девяти файлов помимо ToS_Axioms.v — ProcessContinuumHypothesis.v, SchroederBernstein_ERR.v, analysis/BolzanoWeierstrass.v, process/ProcessBW.v, physics/SpectralDichotomy.v, physics/MeasurementProcess.v, physics/Entanglement.v, settheory/CardinalityWithoutChoice.v, zeta/ZeroStructure.v; напрямую аксиома применена в ProcessContinuumHypothesis.v:78 и в двух леммах ToS_Axioms.v, остальные наследуют |
| `L4_witness` (105) | Axiom | Axioms: ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.1 P4 бесконечность как процесс, стр. 301, 317, 328, 332, 339, 360 | верно | Axiom L4_witness : forall (A : Type) (P : A -> Prop), (exists x, P x) -> {x : A \| P x} (:105) |
| `L4_witness` (105) | Axiom | Axioms: ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.1 P4 бесконечность как процесс, стр. 301, 317, 328, 332, 339, 360 | верно | форма (exists x, P x) -> {x : A \| P x} соответствует описанию |
| `L4_witness` (105) | Axiom | Axioms: ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.5 Процессный континуум, стр. 734, 816, 829, 840, 847 | верно | Axiom L4_witness : (exists x, P x) -> {x : A \| P x} (ToS_Axioms.v:105); в опорном файле применена явно в countable_union_enum (ProcessContinuumHypothesis.v:78) |
| `L4_witness` (105) | Axiom | Axioms: ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.6 P4 как фильтр, стр. 147, 320 | верно | Axiom L4_witness : (exists x, P x) -> {x : A \| P x} (ToS_Axioms.v:105) — пересказ точен |
| `L4_witness` (105) | Axiom | Axioms: ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.6 P4 как фильтр, стр. 147, 320 | верно | согласуется со строками 310–326 и с ChoicePriceMap.v (из утверждения L4_witness следует функциональный выбор) |
| `L3_informative` (119) | Lemma | Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A \| P x} | IV.5 Процессный континуум, стр. 839 | верно | исправлено 12.11 (шаг 12) — фраза добавлена: Lemma L3_informative : forall P : Prop, {P} + {~P} (ToS_Axioms.v:119); Print Assumptions: Classical_Prop.classic и ToS_Axioms.L4_witness |

