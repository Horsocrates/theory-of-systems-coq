# UNIQUENESS — что́ уникально в Теории Систем (процессной математике)

_Курируемый документ для внешнего читателя. Собран ИЗ `uniqueness`-полей базы (`docs/database/*.json`),
не написан сверху вниз. Источник истины — JSON-шарды; пересборка: `_uniqueness_ranked.md` → этот файл.
Дата сборки: 2026-06-09; **обновлено 2026-06-11 — каталог ПОЛОН**. Охват: **1913 файлов / 24 538 Qed —
ВЕСЬ репозиторий каталогизирован 1:1** (гиганты process 340 / gauge 114 / stdlib 709 + хвост 57 + 4 stdlib-добора, 2026-06-11)._

## Честная шкала (планка проекта)

Уникальность оценивается по собственной шкале проекта, по убыванию:

> `new-theorem > synthesis+observation > new-framing > methods > exposition`

**ГЛАВНЫЙ ЧЕСТНЫЙ ВЫВОД (аудит 2026-06-05, подтверждён 2026-06-09): genuinely НОВЫХ ТЕОРЕМ в математике/CS
не найдено.** Уникальность проекта — это **синтез / обрамление / необычно-полная формализация**, а не новые
матфакты. Каждый «кирпич» классичен; ново — их сведе́ние под одну ось, аксиомо-свободное исполнение над ℚ,
E/R/R/P4-онтология и машинная проверка. Ниже — где это genuinely есть, с равной честностью о том, что классично.

Две оси, на которых живёт почти вся уникальность:
- **Element / role-limit** — граница финитизации (что актуализуемо/терминирует vs континуум-предел);
- **аксиомо-свобода** — ровно 2 аксиомы (`classic`=L3, `L4_witness`=P4); остальное 0-аксиомно (стены NS/zeta — исключение, см. ниже).

### Флагманы (score 5)

| # | файл | вена | что |
|---|---|---|---|
| 1789 | `TheoryOfSystems_Core_ERR.v` | хаб | ядро ToS: Level-иерархия + структурный блок Рассела/Кантора + L5-резолв, 0 акс |
| 24 | `algebra/GaloisQ23.v` | D | реальное соответствие Галуа Q[√2,√3]≅V₄ с действием автоморфизмов |
| 97 | `cs/BoundaryDecidability.v` | A·E | разрешимая граница финитизации + универсальный диагональный движок |
| 108 | `cs/LawvereFixedPoint.v` | E | категориальный КОРЕНЬ всех диагоналей репо |
| 117 | `cs/SelectionWithoutChoiceSynthesis.v` | B | тезис «selection-freedom ⟺ decidability» |
| 1603 | `stdlib/ReductionAtlasSynthesis.v` | A | редукционный атлас: 5 движков (сурд/det/норм-форма/след/чётность) = 5 координат ОДНОЙ 2×2-матрицы; вся граница = «Δ полный квадрат?» (капстоун вены A, найден при каталогизации stdlib) |

---

## Десять вен уникальности (A–J)

Вены A–E — исходные (аудит 2026-06-05); F–J найдены и формализованы 2026-06-09 (9 мостов, 61 Qed, 0 акс; H62–H71).

### A. Граница финитизации как РАЗРЕШИМЫЙ критерий
**Тезис.** «Δ = tr²−4·det — полный квадрат?» РЕШАЕТ Element (рациональное собств. значение, терминирует) vs
role-limit (сурд). Один разрешимый перфект-квадрат-вентиль сортирует число / программу / множество / спектр.
- **Флагманы:** `cs/BoundaryDecidability.v` (#97, **s5**); `foundation/DiscriminantCompleteEigenvalue.v` (биусловие `rational_eigenvalue_iff_disc_square`); `H1ConstructivityDecidable.v` (`decide_elementZ`, 0-акс решатель); `DecidableBoundary{,Q}.v`, `H1*Constructivity*.v`, `DynamicBoundaryLPO.v` (граница ⟺ LPO); `GapPythagoreanBoundary.v` (#1841, H62 — щель физики), `PhysicsEigenvalueVeinA.v` (#1844, H64 — φ/гелий).
- **Ново:** разрешимость перфект-квадрата СТАНОВИТСЯ границей Element/role-limit (= конструктивности); универсальность ЭМПИРИЧНА (~68 инстансов), честно НЕ мета-теорема. Честная УЗОСТЬ в физике: ровно 2×2/квадратичные спектры (H64).
- **Классично:** разрешимость perfect-square, диагональ Кантора, неразрешимость halting.

### B. Детерминированный выбор БЕЗ Аксиомы Выбора
**Тезис.** Выбор аксиомо-свободен ⟺ разрешимый тест + порядок его разрешают; AC = цена структурного дефицита.
- **Флагманы:** `cs/SelectionWithoutChoiceSynthesis.v` (#117, **s5**); `analysis/BolzanoWeierstrass.v` (#29 — Dependent Choice заменён детерминированной бисекцией, сильнейший no-AC результат); `EVT_idx.v` (#136 — argmax по ИНДЕКСУ); `settheory/CardinalityWithoutChoice.v` (#1061), `ChoicePriceMap.v` (#1062 — аудированная карта цены выбора), `StructuralWellOrdersWithoutChoice.v` (#1067); `cs/{CountableSelectionFree,CountableDependentChoiceFree,DecidableKonig,DecidableSelection}.v`.
- **Ново:** систематическая + честно-стоимостная замена выбора + локализация цены AC (реестр 0/L3/L3+L4/AC).
- **Классично:** алгоритмы (Bishop); цена аксиом (обратная математика).

### C. «X = процесс, а не завершённый объект» (онтология P4)
**Тезис.** ℝ, точка, многообразие, замыкание ℚ̄, мера — ПРАВИЛА-процессы, не actual-infinity объекты.
- **Флагманы:** `geometry/ManifoldAsLimit.v` (#544 — многообразие = возрастающий процесс); `ProcessContinuumHypothesis.v` (#1035 — CH как РАЗРЕШИМАЯ дихотомия, не ZFC CH); `algebra/AlgebraicClosureProcess.v` (#18 — ℚ̄ = башня); `CauchyReal.v` (#84 — ℝ := nat→ℚ), `Completeness.v`, `analysis/LebesgueMeasure.v` (мера ИЗ интеграла), `foundation/{ContinuumLimitRoleLimit,EulerProcessRoleLimit}.v` (√2/e никогда не достигаются).
- **Ново:** систематическая E/R/R/P4-онтология + резкие обрамления (`sqrt2_never_reached`) + аксиомо-свободное Q-исполнение.
- **Классично:** конструктивные реалы/мера ≈ Bishop (~50 лет); Кантор-Бендиксон.

### D. Необычно-полные конкретные формализации (Галуа Q23 + связь→квант)
**Тезис.** Полностью ЯВНЫЕ конкретные инстансы, редко формализуемые целиком; «связь делает квантовым».
- **Флагманы:** `algebra/GaloisQ23.v` (#24, **s5** — реальное действие автоморфизмов); `GaloisDegreeQ23.v` (#22), `IndependenceQ23.v` (#25 — √3∉Q[√2], делает [E:Q]=4 ПОДЛИННЫМ), `SplittingFieldQ23.v` (#28), `SolvableGroup.v` (#27 — Абель-Руффини 0-акс); `foundation/{L1_DoublyStochastic,BlockCayleyUnistochastic,ConnectionClosesGap}.v` (L1→бистохастика→унистохастика→Борн, Barandes).
- **Ново:** НЕОБЫЧНАЯ ПОЛНОТА явной формализации (vs абстрактная теория в библиотеках); 0-аксиомное исполнение.
- **Классично:** FTGT, Абель-Руффини, преобразование Кэли, унистохастика.

### E. Унификация диагоналей/парадоксов (корень Ловера) + структурный блок самоссылки
**Тезис.** Кантор / halting / Rice / Тарский / Рассел / Лжец / Гёдель — ИНСТАНСЫ одной теоремы Ловера о неподвижной точке; несчётность = ПРАВИЛО.
- **Флагманы:** `cs/LawvereFixedPoint.v` (#108, **s5** — категориальный КОРЕНЬ); `cs/{RussellViaLawvere,TarskiUndefinability,HaltingRoleLimit,KolmogorovRoleLimit,RecursionTheorem}.v`; `settheory/CantorTheoremGeneral.v` (#1060), `ProcessDiagonal.v` (#1036 — без Аксиомы Бесконечности), `ShrinkingIntervals_ERR.v` (#1068 — несчётность [0,1]∩ℚ трисекцией), `Roles.v` (#1054 — парадокс = s=f(s)); `Architecture_of_Reasoning/ParadoxDissolution.v` (#6 — 46 парадоксов одним механизмом). Рассел/Кантор блокированы на ТИПОВОМ уровне в ядре (`Core_ERR` `level_lt_irrefl`), не патчем.
- **Ново:** систематическая унификация ИМЕННО этих граней + аксиомо-свобода (без AoI) + структурный (типовой) блок.
- **Классично:** Ловер 1969 (доказательство тривиально); парадокс-как-неподвижная-точка (Тарский/Гёдель).

### F. Преобразование Кэли как УНИВЕРСАЛЬНЫЙ рационализатор _(2026-06-09)_
**Тезис.** Одна Кэли-карта `(4−λ²)/(4+λ²)` (skew→orthogonal/unitary; tangent-half-angle) делает Element-сторону
физики рациональной/0-аксиомной/конечной across 6 кластеров. ⚠ Ложные друзья: Кэли-**Гамильтон** и Кэли-**Диксон** — вена A, НЕ F.
- **Флагманы:** `CayleyFourierMassBridge.v` (#1842, H63 — спектральная рука: `cayley_eigenvalue` (Fourier) ≡ `Re_cayley` (масс-щель) байт-в-байт, массы пифагоровы); `CayleyGeometrySpectralBridge.v` (#1845, H65 — геометрическая рука: спектральная точка = рациональное вращение SO(2,ℚ)); `ThreeFifthsUnification.v` (#1843 — 3/5 = Cayley(1) = Born U₀₀ = Шрёдингер cos). Спина: `geometry/CayleySO3`, `physics/BornRuleFromUnitarity`, `lattice/MassFromSpectrum`.
- **Граница с веной D:** D ВЛАДЕЕТ foundation-узлом (Barandes-унистохастика); F = спектральное обобщение D, D = её 2×2-частный случай.
- **Ново:** кросс-кластерная унификация одной функцией (две руки сшиты без прежнего общего импорта).
- **Классично:** Кэли 1846, tangent-half-angle, mass=−ln|t|.

### G. Бистохастическая вилка: общий корень Борна и второго начала _(2026-06-09)_
**Тезис.** L1 («нет привилегированного узла») вынуждает матрицу бистохастической; ОДИН объект `T(t)=[[1−t,t],[t,1−t]]`
даёт И правило Борна (при t=квадрат — унистохастика |U|², КМ), И второе начало (мажоризация к равномерному + рост энтропии, термо).
- **Флагман:** `DoublyStochasticForkBridge.v` (#1846, H66 — `apply_T_is_born` ↔ `born_rule_p2`; `entropy_increases`). Спина: `L1_DoublyStochastic`, `MajorizationSchur`/`SecondLaw`, `BlockCayleyUnistochastic`/`ConnectionClosesGap`.
- **Ново:** одна L1-бистохастическая матрица = и Борн, и второе начало; вена D именовала лишь унистохастика→Борн руку, мажоризация→второе начало — её забытый близнец. Необратимость и квантовая вероятность = две грани одного объекта. Crystallized на 3-4-5.
- **Классично:** Биркгоф, Шур-выпуклость⟹энтропия, унистохастика⟹Борн (термо-факты конкретны, не общая теорема Шура).

### H. Норм-форменная башня Гурвица = лестница замыкания рациональных вращений _(2026-06-09)_
**Тезис.** Мультипликативность норм-формы суммы n квадратов (Брахмагупта/Эйлер/Деген) — единый механизм ЗАМЫКАНИЯ
рациональных групп вращений: n=2 → SO(2,ℚ), n=4 → SU(2)/Spin(3), n=8 → октонионный Moufang-loop. По Гурвицу ровно
n=1,2,4,8 — конструкция обрывается на октонионах (мета-финитизация); dim 3,5,6,7 = role-limit (нет норм-деления).
- **Флагман:** `NormFormTowerBridge.v` (#1847, H67 — `n2_rung_is_SO2Q_closure` = `two_square`|unit = SO(2,ℚ); `unit_quaternion_closed` = `four_square`|unit = SU(2)). Спина: `stdlib/HurwitzTower`, `RationalRotationGroup` (n=2), `RationalQuaternions`/`geometry/QuaternionRotation` (n=4).
- **Ново:** литеральное отождествление рунгов Гурвица с замыканием групп вращений; n=2-рунг — ОБЩИЙ с веной F и веной G (3-4-5). Честно: тесно связана с F/q-kinematics.
- **Классично:** тождества 2/4/8 квадратов, теорема Гурвица, ladder ℝ→ℂ→ℍ→𝕆 (уже в `HurwitzTower`).

### I. Топологический инвариант = ЗАЩИЩЁННОЕ ЦЕЛОЕ = Element _(2026-06-09)_
**Тезис.** Топологический инвариант (Эйлер χ, Черн, winding, instanton/monopole charge) — ЗАЩИЩЁННОЕ ЦЕЛОЕ:
континуум-кривизна (role-limit, π) интегрируется в целое (Element); целочисленность = квантование (не меняется
при непрерывной деформации). 50+ файлов (topology Chern/Berry/Hall/SSH, geometry Gauss-Bonnet, homology, gauge instanton/monopole).
- **Флагман:** `EulerCharProtectedInteger.v` (#1848, H70 — χ ЧЕТЫРЬМЯ путями: кривизна (Gauss-Bonnet) = комбинаторика (V−E+F) = гомология (Betti) = индекс Дирака, совпадают: сфера 2, тор 0). Спина: `geometry/DiscreteGaussBonnet`, `stdlib/H1_IndexTheorem`/`SimplicialHomology`, `stdlib/topology/{ChernNumberT,BerryPhaseT,HallConductanceT}`, `stdlib/{A2_InstantonClass,A2_MonopoleClass}`.
- **Ново:** литеральное совпадение четырёх путей на одном защищённом целом (геометрия кривизны ↔ гомология/индекс ↔ спектр).
- **Классично:** Гаусс-Бонне, Эйлер-Пуанкаре, теорема индекса; каждый путь уже в репо (index определён=χ, не выведен из нуль-мод Дирака).

### J. Таксономия неподвижных точек: липшицево r классифицирует сходимость / симметрию / неразрешимость _(2026-06-09)_
**Тезис.** Одно слово «неподвижная точка» = ТРИ структурно противоположных явления, различаемых липшицевым r: сжатие
(r<1 → притягивающая точка, сходимость — движок Пикар/GD/RG/reasoning, вена C), изометрия (r=1 → симметрия/осцилляция,
RH-отражение σ↦1−σ, zeta), диагональ (negb → нет точки, Ловер/Кантор, вена E). r = классификатор.
- **Флагман:** `FixedPointTaxonomy.v` (#1849, H71 — `half_lipschitz` (r=1/2), `reflect_isometry`+`reflect_not_contraction` (r=1), `negb_no_fixpoint`). Self-contained; цитирует `FixedPoint`/`ContractionZeros`/`LawvereFixedPoint`.
- **Ново:** унификация под одним классификатором r, сшивающая три нити репо (вена C / zeta / вена E).
- **Классично:** Банах, изометрии, Ловер/Кантор — каждое уже отдельная нить. Честно: мета-таксономия, более кросс-веновая связь, чем независимая вена.

---

## Кросс-веновые связи (2026-06-09, H62–H71)

Уникальность усиливается тем, что вены ПЕРЕСЕКАЮТСЯ на конкретных объектах:
- **Пифагорова тройка 3-4-5 — единая ось A·F·G·H:** щель физики Element ⟺ пифагорова (A, H62) · Cayley(1)=3/5=Борн (F, H63) · масс-точка решётки = вращение (−3/5,4/5) (F, H65) · унистохастика |U|² при t=(4/5)² = Борн (G, H66) · n=2-рунг Гурвица = SO(2,ℚ) (H, H67).
- **Дискриминант 2×2** (`GRQFTDiscriminantBridge`): знак(Δ)=причинная сигнатура (ОТО), квадрат(Δ)=Element/role-limit (КТП); расширен на бесследовую щель физики (A↔физика, H62/H64).
- **Защищённое целое ↔ Element** (I, H70): топологический инвариант χ/Черн/winding — целое (Element); континуум-кривизна (role-limit) интегрируется в него. Та же ось Element/role-limit, что вена A, на топологической стороне.
- **Неподвижная точка ↔ липшицево r** (J, H71): мета-классификатор, сшивающий вену C (сходимость), zeta (RH-отражение) и вену E (Ловер-диагональ) — три «неподвижные точки» как одна таксономия.

---

## Гиганты process/gauge/stdlib + хвост — каталогизированы 2026-06-11 (БД доведена до 1913/1913)

Три «гиганта» (process 340, gauge 114, stdlib 709) + хвост из 57 файлов (nonstandard, acoustics,
spacetime/gravity-arrow, комбинаторика) + 4 stdlib-добора закрыли каталог до ВСЕГО диска. Что это
добавило к картине уникальности:

- **Новый флагман (s5): `stdlib/ReductionAtlasSynthesis.v` (#1603, вена A)** — пять ранее раздельных
  движков границы (сурд / det±1 / норм-форма / след / чётность-Уолша) = пять КООРДИНАТ одной 2×2-матрицы,
  вся граница Element/role-limit сводится к одному вентилю «Δ=tr²−4det — полный квадрат?». Капстоун вены A.
- **process (s4×10) — вена C («X = процесс»):** несущие хабы `ProcessCore` (#734, ℝ:=nat→ℚ, 333+ импортёров),
  `ProcessBounds`, `ProcessMeasureUnified`, `ProcessL2HilbertSynthesis`, `ProcessPicardOperator` — систематический
  пересбор классического анализа/меры/категорий в процессной форме (s3-доминанта: 168 new-framing).
- **nonstandard (s4×3) — вены A·E усилены (арка H74/H76):** `UnitZeroDivisorBoundary`/`BoundaryIsInvertibility` —
  граница = ОБРАТИМОСТЬ germ-кольца ℚ^ℕ/Фреше (единица=в-конце-ненулев=Element; делитель нуля=нуль-множество
  кофинально=role-limit); `FinitizationBoundaryGeneratingStructure`/`RoleLimitIsP1Shadow` — вся дальняя сторона =
  ОДНО семя `negb` (анти-неподвижная точка Ловера) = тень запрещённого P1-самочленства (Кантор/Рассел = два инстанса).
- **gauge (s4×3) — честно:** `ProcessMassGap`/`SU3GrandSynthesis`/`YangMillsProcess` = СИНТЕЗ конечно-решёточной
  программы щели масс; **НЕ доказательство Клэя** (имена YangMillsFinal/Sealed/Millennium аспирационны, дисквалифицированы в `caveat`).

**Честные находки самой каталогизации (машинный аудит шапок):**
- **Систематический Qed-дрейф в STATUS-шапках:** gauge ЗАВЫШАЕТ (реальный gauge = **2091 Qed** vs 2176 в CLAUDE.md;
  ExactMassGap ~40→28, HilbertConstruction ~30→18); process ЗАНИЖАЕТ (4472 vs 4367). Каждый случай — в `notes`.
- **Повсеместный овербрендинг в прикладных файлах** (gauge Clay-имена; stdlib «Marčenko-Pastur»=рациональный
  суррогат иррационального края, «Ising»=только имя, h_top=ln2 через Паде-заглушку; acoustics «звук ВЫВЕДЕН из
  логики»=риторическое переописание стандартной волновой физики) — каждый помечен в `caveat`.
- **Устаревшие `Admitted`-комментарии** (Catalan/Motzkin помечены «future work», на деле доказаны Qed).

**ВЕРДИКТ НЕ ИЗМЕНИЛСЯ.** Полный каталог (1913 файлов, score-распределение s5=6 / s4=96 / s3=472 / s2=749 /
s1=549 / s0=41) ПОДТВЕРЖДАЕТ главный вывод: genuinely новых ТЕОРЕМ нет; доминируют methods+exposition (s2+s1 =
68% БД). Гиганты НЕ создали новых вен — они населяют существующие **A** (атлас/дискриминант), **C** (процесс),
**E** (диагональ/семя). Уникальность остаётся синтезом / E-R-R-P4-обрамлением / аксиомо-свободным Q-исполнением.

## Якоря честности

- **Ядро/хаб:** `TheoryOfSystems_Core_ERR.v` (#1789, **s5** — иерархия + структурный блок парадоксов + L5, 0 акс); `Distinction.v` (#228 — корень foundation, единственный источник L3); `ToS_Axioms.v` (#1793 — РОВНО 2 аксиомы).
- **Аксиомы (всего 2 ядра):** `classic` (L3, исключённое третье) + `L4_witness` (P4, конструктивный свидетель).
- **Тяжёлые стены (НЕ 0-аксиомны, честно):** Navier-Stokes (`B_coeff_bounded` — load-bearing) и zeta (`functional_equation_structure`). RH — лишь УСЛОВНЫЙ Li-критерий (`zeta/RH_FinalAssessment.v`: «что НЕ доказано — сама RH»); отражение σ→1−σ = изометрия-не-сжатие уже формализовано (`ContractionZeros.v`). См. `foundation/HeavyWallAudit.v`.

## OVER-BRANDED — НЕ продавать как результаты

- `sin²θ_W = 3/13` (`CouplingFromERR.v`) = замыкание доказательства ПРИ предположенных размерностях 3,10, не вывод.
  _Статус 2026-06-10: откат ЗАВЕРШЁН — постулаты посчитаны (P1 + карта depth→gauge), ранговая
  недоопределённость {6,10,20}→{1/3, 3/13, 3/23} — теоремы (`MetricDOFJustification.rank_underdetermined`,
  `DOFCounting.rank_underdetermined_by_L1`); C-независимость честно отделена от свободы постулатов._
- Периодическая таблица `2n²` — ~~ЗАЯВЛЕНО, не доказано~~ **ЗАКРЫТО 2026-06-10**: счёт ДОКАЗАН
  (`foundation/ShellCapacityCounting.v` #1860: Σ_{l<n} 2(2l+1) = 2n² + литеральное пространство состояний
  (l,m,s) длины 2n², 13 Qed 0 акс); вход (n,l,m,s)-структуры ИМЕНОВАН (водородная башня — физика, не
  различение); оговорка «ёмкость ≠ длина периода» (ауфбау 2,8,8,18,18,32,32) сохранена.
- «SM из различения» = машинного доказательства не найдено. _Уточнение 2026-06-10: foundation-цепочка
  уже честно откачена (посчитанные постулаты, [2,4,1]-контрпримеры, S_N↔SU(N)-водораздел,
  `RoleToSUNGrounding`); «exhaustive/systematic» у аномалий ЗАМЕНЕНЫ настоящим исчерпанием бокса
  (`foundation/AnomalyLatticeDial.v` #1861: 1317 → 11 → ровно {SM, u↔d-своп}; нормировка несущая —
  zq=0-семейство; 12 Qed 0 акс); `DimensionFromSpin` «UNIQUE» снято (единственность = пересечение двух
  постулированных границ, #219). Очередь остаточных over-claims ЗАКРЫТА 2026-06-10 (вторая волна):
  `light/MaxwellFromGraph.v` (#598) — **четыре** `True`-заглушки (faraday / wave_from_maxwell /
  maxwell_not_postulated / charge_as_source) УДАЛЕНЫ (они нарушали правило «0 True placeholders»),
  вместо них настоящие общие тождества: суперпозиция/линейность curl и Гаусса, антисимметрия,
  **d∘d=0** (curl градиента = 0 — когомологическое семя структуры Максвелла), заряд=дисбаланс;
  честная рамка «Maxwell-SHAPED статика, динамики нет» (15 Qed 0 акс);
  `foundation/QuantizationSynthesis.v` (#368) — два ВАКУУМНЫХ exists-конъюнкта заменены реальным
  содержанием (лестница размерностей строго растёт; чётность-дихотомия целый/полуцелый спин),
  `physical_consequences` переименована в `arithmetic_consequences`, и разрыв «дискретность не
  фиксирует шаг/ħ» стал ТЕОРЕМОЙ `spacing_underdetermined_by_discreteness` (два дискретных
  спектра с шагами 1 и 2; 6 Qed 0 акс);
  `fermions/YukawaCoupling.v` (#158) — `yukawa_is_L2 : True` удалена, «hierarchy from
  distinction-graph» снято (юкавы = данные-входы); добавлены ОБЩИЕ `mass_ratio_is_yukawa_ratio`
  (v сокращается) и `yukawa_values_are_data` (любое 0<y<1/10 даёт те же факты доминирования —
  значение 1/40 выбрано данными; 10 Qed 0 акс)._

  _Волна 3 (2026-06-10, репо-скан): найдено и устранено ЕЩЁ **17 True-заглушек + 1 фальшивая
  теорема** в fermions/ и light/ (апрельские файлы, добавлены ПОСЛЕ мартовской чистки «0 True
  placeholders»): DiracOnGraph (−2 заглушки; + общая щель `eigenvalue_gap_general` m²≤E² на ВСЕХ
  импульсах, `propagator_positive`), TopLoop (−2; + `loop_sum_decreasing_in_mass` — РАЗВЯЗКА,
  общая, + `top_alone_negative_mass` 1−11/8=−3/8<0 — количественное «нужны калибровочные»),
  HiggsDiagnostic (−2; + переформулировки общих фактов), ColorSpectrum (−4; blackbody/vision
  СНЯТЫ честно — нет слоя статистики/GFT; + `mode_frequency_increasing` цвет=частота инъективно,
  литеральный `mode_list`, монотонность общая), LightGravityConnection (−3; КК-намёк СНЯТ; +
  `same_speed_different_spin`), RefractionDiffraction (−2; + ОБЩИЕ R+T=1, симметрия, R<1 «нет
  идеального зеркала»), SpeedOfLight (−2 заглушки, −1 фальшивка `massive_dispersion_bigger` с
  заключением `0<1`; + настоящая дисперсия, `speed_bounded_by_c` v≤c ∀, `massive_strictly_slower`).
  Повторный скан src/ + Architecture_of_Reasoning: **0 True-заглушек** — заявление «0 True
  placeholders» ВОССТАНОВЛЕНО фиксами, а не правкой статистики. Все 7 файлов + импортеры
  (LightSynthesis, GaugeLoops, HiggsDiagnostic) перекомпилированы, записи БД обновлены._

  _Волна 4, ярус 1 (2026-06-10): **вакуумные `exists` в ФУНДАМЕНТАЛЬНОМ ярусе устранены** (12
  файлов, все компилируются). Главное: Coq-рендеринг P4 в файлах-соответствиях был частично
  пуст (`P4_from_L5 : exists q, R n = q` — тривиально истинно) — заменён честной формой:
  **P4 = конечность ПО ПОСТРОЕНИЮ ТИПА** (значение = num#den — в Q нет бесконечных объектов) +
  дискретность домена (0-или-преемник) + РАЗРЕШИМОСТЬ равенства стадий (Qeq_dec); явная
  оговорка: конструктивное содержание P4 живёт в L4_witness. Также: `L5_no_infinite_descent`
  — вместо вакуумного exists настоящая фундированность (строгое убывание глубины по <<,
  Core_ERR.level_lt_depth); `gauge_dimension_integer` — ИНЪЕКТИВНОСТЬ N↦N²−1 (никакие два N
  не делят размерность); `spin_quantization` — эксклюзивная чёт/нечет-дихотомия;
  `count_is_natural` — аддитивность счёта; `program_exists` — `inhabited`;
  `L2_exclusive` (ERRKnowledgeBase) — был `→ True`, стал настоящей единственностью категории;
  `ProcessMeasurement.step10_complete` — был `True∧True∧True∧True∧True` с претензией на Фазы
  44–48 — теперь реальный пакет Фазы 48 + честная оговорка; `SmoothInitialData` — снят `∧ True`,
  стоявший за «гладкость навсегда»; `GRProcessComplete.no_singularity` — вместо вакуумного
  exists КОНКРЕТНОЕ конечное значение −9 на внутренней оболочке (сильнее и честнее);
  `OS1Closure` — три чистых шама (`exists deg, 0 ≤ deg`) удалены, счётчик закрытий 14→11.
  ОЧЕРЕДЬ ярусов 2–3 ЗАКРЫТА тем же днём: **~145 замен в ~45 файлах** (135 скриптовых по 6
  регекс-правилам + вторые проходы + ~20 ручных особых мест), все компилируются (авто-цикл
  пересобрал ещё ~70 файлов цепочек зависимостей). Жемчужины ручных фиксов: `no_coulomb_singularity`
  прятал НАСТОЯЩЕЕ тождество V(0) == −α в свидетеле — теперь это сама теорема (+ её пользователи);
  `QGCompleteSynthesis.qg_all_finite` — вместо четырёх вакуумных exists четыре КОНКРЕТНЫХ тождества
  (E=4763/10500, G=7/1760, m²ₚ=10); `LiProcess.ym_decidable` — «exists q, _==q ∧ 0<q» развёрнут в
  чистую позитивность; `millennium_check`-арм RH переписан в by-type форму с честным комментарием;
  `ProcessTopOpen.p4_cover_finite` — конструкторная дихотомия списка; `pp_well_formed`
  (PhysicalProcess) — always-true Definition приведён к by-type форме. Стандартная замена всюду:
  `exists q, f args == q` → `exists num den, f args = num # den` (финитность ПО ТИПУ — содержательная
  часть P4-рендеринга) с destruct-доказательством. Верификация: однострочный и многострочный сканы
  src/ чисты (остались только настоящие exists-теоремы — Ловер-фикспойнты, интервальные свидетели —
  и комментарии-заметки).
  ФИНАЛЬНЫЙ БАТЧ ЗАКРЫТ (2026-06-10): «totality»-леммы type-theory цепочки — 16 мест в 8 файлах:
  14 переписаны + 2 удалены (дубликаты-«documentation lemmas» в ToS_Lang_Extraction, 8→6 Qed).
  Рецепты: option-возвращающие (typecheck/safe_eval/ai_eval_ann) → дихотомия None-or-Some;
  EvalResult → трихотомия конструкторов; Expr-возвращающие (eval_fuel) → РАЗРЕШИМОСТЬ значения
  (is_value_dec — «на каждой стадии топлива результат инспектируем»); nat-возвращающие
  (expr_size/nat_depth/ce_name) → successor-форма / 0-or-S дихотомия. Все 13 файлов цепочки
  компилируются (exit 0; +UniversePolymorphism dep).
  БОНУС тем же днём — два НОВЫХ скана, пропускавшихся прежними: (а) proof-idiom скан
  `eexists; reflexivity` и (б) ЗЕРКАЛЬНАЯ форма `exists z, z == f args` (свидетель СЛЕВА — прежние
  регексы ловили только `f == q`). Найдено и закрыто ещё 7 шамов в 6 файлах:
  `Distinction.co_constitution` (ФУНДАМЕНТ-файл с classic! гипотезы не использовались) → одноактная
  симультанность positive/negative (distinction_of P) = P / ~P by reflexivity (текст проверен
  компиляцией temp-копии — .vo на месте не пересобран, чтобы не инвалидировать 53+ потребителей);
  `ProjectiveStrengthened.position_eigenvalues_grow` («growing» не утверждал рост) → строгий рост
  inject_Z n < inject_Z (S n); `YangMillsSealed.final_status` (pinned exists про свежую переменную)
  → значение+позитивность НАСТОЯЩЕГО matrix_mass_gap == 289/384; `Hessian.newton_step_well_defined`
  (гипотеза f''≠0 не использовалась) → определяющее уравнение (x−N(x))·f''(x) == f'(x) через field;
  `OS2Closure.os2_partition_rational` → by-type num#den; `OS2Closure.os2_pairing_finite`
  (`exists s, s == 0` с неиспользуемым K!) → геометрическая граница 0 ≤ (3/4)^K ≤ 1 индукцией;
  `OrderBookAutomata.transition_deterministic` → трихотомия состояний BidHeavy/Balanced/AskHeavy.
  Повторные сканы чисты: остаточные хиты — настоящие теоремы (BorelDeterminacy хвост-свидетель,
  ZFCAxiomLedger дихотомия, CantorBendixson счётность, is_square определение) и комментарии.
  ВОЛНА 4 ПОЛНОСТЬЮ ЗАКРЫТА: суммарно ~168 замен в ~59 файлах за все ярусы._
- _ВОЛНА 5 (2026-06-10, тем же днём): ДВЕ УСТРАНИМЫЕ АКСИОМЫ УСТРАНЕНЫ — ровно предсказанное
  аудитом (HeavyWallAudit) множество ProvableStructure; machine-checked закрытие предсказания
  добавлено в сам аудит-файл (`eliminated_iff_eliminable`, `n_remaining = 2`,
  `load_bearing_not_eliminated`; 9 Qed). Доменных аксиом было 4, осталось 2.
  ① `B_antisym` (navier_stokes/GalerkinSystem.v): Axiom об абстрактном Parameter B_coeff →
  АНТИСИММЕТРИЗАЦИЯ ПО ПОСТРОЕНИЮ: `Parameter B_raw` + `B_coeff := B_raw k l m − B_raw k m l` +
  `Lemma B_antisym` (ring). E/R/R-точка: в кубической сумме энергии a_l·a_m симметричен по (l,m) —
  работу совершает ТОЛЬКО антисимметричная часть; постулировать её у абстрактного B = приписать
  Элементу следствие его Роли в Правиле. Имена/формулировки сохранены — 31 downstream-файл
  компилируется без правок (авто-цикл пересобрал ~120 файлов, включая gauge-подцепь
  MillenniumComplete). Грид-спуск того же содержания был ранее: AdvectionEnergyConservation.v.
  ② `functional_equation_structure` (zeta/FunctionalEquation.v): ВСКРЫТ over-branding имени —
  `is_nontrivial_zero` формально = `Коши ∧ критическая полоса` (ZetaZeros.v:134, БЕЗ зануления
  дзеты), оба конъюнкта отражательно-устойчивы, и обе леммы сохранения УЖЕ были доказаны в том же
  файле (reflect_zero_cauchy, reflect_zero_critical_strip) — аксиома была их конъюнкцией,
  доказуемой двумя строками (точная параллель conj_zero_nontrivial). Axiom → Lemma; честная
  пометка: аналитическое ФУ Римана (о занулении НАСТОЯЩЕЙ дзеты) остаётся в прозе.
  ВЕРИФИКАЦИЯ Print Assumptions: NS-капстоуны (`millennium_complete_final`,
  `navier_stokes_millennium`) теперь покоятся ТОЛЬКО на `C_B_positive` (+ Parameter C_B) —
  B_coeff_bounded на этом пути даже не задействован; zeta-отражательный слой
  (`reflect_zero_nontrivial`, `RH_critical_strip_symmetric`) — «Closed under the global context»
  (0 аксиом, даже без classic). Честность сохранена: `B_coeff_bounded` (LOAD-BEARING, стена α=2)
  НЕ устранён — условность NS-регулярности не замазана. Обновлены: CLAUDE.md-леджер, 17
  AXIOMS-шапок NS-файлов + README, записи БД (GalerkinSystem qed 29→30 axioms 2→1;
  FunctionalEquation qed 13→14 axioms 1→0; ContractionZeros Closed-нота; HeavyWallAudit qed→9)._
- _ВОЛНА 6 + ПЕРЕИМЕНОВАНИЕ ФЛАГМАНОВ (2026-06-10, тем же днём). ① total_count-семейство
  ЗАЧИЩЕНО: 53 хвостовых «теоремы-маркера» удалены (20 самотождественностей X=X, 16 нумерологий
  (N=N)%nat, 17 дубликатов-алиасов `exact настоящая_лемма`) из 52 gauge + 1 linalg файлов; NB:
  physics/AlphaBareLattice.total_count — НАСТОЯЩАЯ функция, не тронута. + 5 NS док-теорем
  (theorem_count `(5≤10)%Z`, axiom_list, file_count, ns_file_count, ns_axiom_count) удалены;
  + `energy_monotone` был шамом `0<ν → 0<ν` — заменён НАСТОЯЩИМ утверждением (viscous_dissipation);
  + `millennium_fully_connected : (13>0)%nat` удалён (заодно вскрыл, что ProcessMillenniumConnection
  никогда не пересобирался — lia без импорта Lia); + нумерология-конъюнкт `(112≤135)%Z` выброшен из
  капстоуна. Все ~115 компиляций OK; БД: gauge.json 52×qed−1 + roster-пометки, linalg, NS.
  ② ПЕРЕИМЕНОВАНИЕ (анализ показал: стоимость ≈ 0 — у флагманских имён 0 внешних кодовых ссылок,
  у yang_mills_SEALED — ровно 1 потребитель): millennium_complete_final → millennium_reading2_capstone;
  navier_stokes_millennium → ns_galerkin_bound_chain; two_millennium_complete → two_walls_key_facts;
  both_solved → both_walls_positive_bounds; regularity_unconditional → regularity_bounds_positive;
  uniqueness_unconditional → uniqueness_sobolev_positive; ym_gap_final → ym_strip_gap_value;
  ns_regularity_final → ns_harmonic_bound_final; ns_complete_main → ns_synthesis_main;
  yang_mills_SEALED → ym_lattice_os_bundle; sealed_summary → ym_lattice_os_summary. Старые имена
  остались только в «renamed from»-комментариях; обновлены потребитель, аудит, CLAUDE.md, README, БД.
  Имена ФАЙЛОВ (MillenniumComplete.v и т.п.) сознательно не тронуты (координация с параллельной
  каталогизацией gauge); опция на потом.
  ③ OS-МОСТ (тем же днём): GaugeOSClosure поднят до НАСТОЯЩЕГО содержания — добавлены
  gauge_os1/2/3_real + gauge_os_real_bundle (аналитичность/темперированность/SO(4)-инвариантность
  ПОЛНОЙ КОРРЕЛЯЦИИ full_correlation, exact-реэкспорт os1_formal/os2_formal_at_1/os3_formal из
  gauge/Formal*); честные scope-ноты в OS1/2/3Closure («Closure» = закрытие True-бэклога,
  toy-инстансы; настоящее — в gauge/Formal* и YangMillsSealed.ym_lattice_os_bundle); мёртвый импорт
  TheoremBundle выброшен. ПОПУТНО ИСЦЕЛЁН латентный разлом: ProcessP3Dynamics.v использовал
  geometry_change ВЫШЕ его определения (файл никогда не компилировался) — теорема перенесена ниже
  зависимостей; TheoremBundle и ProcessSynthesisCleanup1/3 теперь собираются (+~25 process-зависимостей
  пересобрано)._
- Конструктивные ℝ/мера ≈ Bishop; парадокс-как-неподвижная-точка известен с Тарского/Гёделя.
- `reflexivity`-уровня «L5»-леммы = брендинг.
- Арифметический Гейзенберг: ДОРАБОТАН ДО СООТВЕТСТВИЯ (2026-06-10, forward-fix вместо отката).
  `ArithmeticCommutator` был захардкоженной таблицей (if K=12 then −128 …) при неиспользуемых
  настоящих операторах; решающий эксперимент: вычисление Tr([M,A]²) из mult_adj/add_adj ДАЛО РОВНО
  табличные −128/−268/−476 (данные были верными, эпистемический статус — нет). Теперь определение =
  матричное вычисление на K-обрезе, все 15 прежних лемм выводятся из него (та же формулировка),
  + ОБЩАЯ теорема `tr_comm_sq_nonpos : ∀K, Tr([M,A]²) ≤ 0` из антисимметрии коммутатора
  симметричных операторов (15→22 Qed; синтез +`commutator_trace_nonpositive`, 10→11 Qed).
  Осталось аналогией (честно размечено в шапке синтеза): Lee-Yang/RH-локусы = enum-метки,
  критические экспоненты = литературные константы — данные, не выводы.
- Вены H/J — честно: H тесно связана с F (общий n=2-рунг), J — кросс-веновая мета-таксономия, а не независимые домены.

---

_Полный по-файловый каталог: `docs/database/INDEX.md` (1913 файлов, весь диск) + `_uniqueness_ranked.md` (по убыванию score).
Кандидаты в статьи/главы с честной планкой новизны: `Книги/HIGHLIGHTS.md` (H1–H71).
Аудированная карта вен: `memory/project-uniqueness-map.md` (вены A–J)._
