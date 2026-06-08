# Database - cluster `geometry`

_Generated from `geometry.json` by `generate.ps1` - do not edit by hand; edit the JSON._

**7 files / 85 Qed.** Score distribution: s5=0 / s4=1 / s3=4 / s2=2 / s1=0 / s0=0

---

## #540 - `src/geometry/CayleySO3.v` - score 3 (new-framing)

**The Cayley transform to SO(3) over Q: rational rotation matrices**

- **Topic.** 3x3 matrices over Q, the Cayley numerator cay_num(x,y,z), proven orthogonal-when-scaled and det-1-when-scaled by ring; the 90-degree-x rotation as a scaled Cayley image; rot90x orthogonal with det 1.
- **Role.** Vein D-flavour: rational rotations of SO(3) via Cayley. Self-contained (QArith).
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ 3x3-матрицы M3 над Q; параметры x,y,z. _Roles:_ ортогональная матрица = поворот (роль SO(3)); Cayley-числитель как рациональный генератор. _Rules:_ cay_num через (x,y,z); ортогональность/детерминант через ring при масштабе. _P4:_ рациональные повороты SO(3) — Element (точная Q-арифметика, ring); иррациональные углы — role-limit (вне образа Cayley).
- **Classical counterpart.** The Cayley transform (skew-symmetric -> orthogonal) and rational parametrization of rotations are classical; NEW: only the explicit Q-arithmetic instance (scaled orthogonality/det proven by ring) tying rational data to SO(3) rotations.
- **Tags.** cayley, SO3, rational-rotation, geometry, new-framing

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `M3/Meq/Mtrans/Mmul/Mscale/Mid/Mdet/orthogonal` | Definition | 3x3 матрицы над Q и операции |
| `cay_num` | Definition | числитель преобразования Кэли (x,y,z) |
| `cay_orthogonal_scaled` | Theorem | ★ Cayley-образ ортогонален (при масштабе) |
| `cay_det_scaled` | Theorem | детерминант Cayley-образа (при масштабе) |
| `cay_identity` | Theorem | cay_num 0 0 0 = Mid |
| `rot90x/cay_num_90x` | Definition/Theorem | поворот на 90° как масштабированный Cayley-образ |
| `rot90x_orthogonal/rot90x_det` | Theorem | rot90x ортогонален, det=1 |

**Key lemmas (deep):**

- **`cay_orthogonal_scaled`** - Преобразование Кэли из рациональных (x,y,z) даёт ортогональную матрицу (при явном масштабе) — доказано ring над Q. Element-сторона: рациональные повороты SO(3) точны и вычислимы, без вещественных углов. _(cayley, SO3, rational, orthogonal)_
- **`rot90x_det`** - Поворот на 90° имеет det=1 (собственная ортогональность) — конкретное свидетельство, что Cayley-параметризация попадает именно в SO(3), а не в O(3) с отражениями. _(determinant, rotation)_

**Uniqueness - score 3 (new-framing).** Рациональные повороты SO(3) через преобразование Кэли над Q (ортогональность/det через ring) — Element-сторона группы вращений без вещественных углов.
> _Caveat:_ Преобразование Кэли и рациональная параметризация вращений классичны; вклад — явный Q-инстанс, перекликается с RationalSO3/q-kinematics.

---

## #541 - `src/geometry/DiscreteGaussBonnet.v` - score 3 (new-framing)

**Discrete Gauss-Bonnet: total angular defect = 4 (= 2*chi) for all Platonic solids, exactly over Q**

- **Topic.** Vertex angular defects (in pi units) for the five Platonic solids all sum to exactly 4 = 2*chi, the Euler characteristic V-E+F=2, the general discrete Gauss-Bonnet relation, and the defect sum is exactly rational.
- **Role.** Vein D-flavour: chi as a protected integer; exact rational curvature. Self-contained (QArith/ZArith).
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith ZArith
- **E/R/R.** _Elements:_ углы граней (рациональные доли pi); вершины/рёбра/грани (V,E,F). _Roles:_ дефект вершины = дискретная кривизна; эйлерова характеристика chi как защищённое целое. _Rules:_ total_defect = V·(2 − m·a); сумма дефектов = 2·chi; euler = V−E+F. _P4:_ суммарный дефект ТОЧНО рационален (=4) для каждого платонова тела (Element); chi — защищённое целое, не приближение.
- **Classical counterpart.** Descartes' angular-defect theorem / discrete Gauss-Bonnet (total defect = 2*pi*chi) and the Platonic Euler characteristic chi=2 are classical; NEW is only the exact RATIONAL formalization (defects in units of pi sum to 4 = 2*chi for every Platonic solid) with chi a protected integer.
- **Tags.** gauss-bonnet, euler-characteristic, platonic-solids, rational-curvature, new-framing

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `tri_angle/sq_angle/pent_angle` | Definition | углы правильных граней в долях pi (1/3,1/2,3/5) |
| `vertex_defect_pi/total_defect_pi/euler` | Definition | дефект вершины, суммарный дефект, V−E+F |
| `tetra_defect/cube_defect/octa_defect/dodeca_defect/icosa_defect` | Theorem | ★ суммарный дефект = 4 для всех 5 тел |
| `platonic_euler` | Theorem | chi=2 для платоновых тел |
| `gauss_bonnet_general` | Theorem | ★ общее дискретное Гаусса-Бонне (дефект ↔ chi) |
| `gauss_bonnet_tetra` | Theorem | Гаусс-Бонне для тетраэдра |
| `defect_sum_is_rational` | Theorem | суммарный дефект = 4/1 (точно рационален) |

**Key lemmas (deep):**

- **`gauss_bonnet_general`** - Дискретная теорема Гаусса-Бонне: суммарный угловой дефект = 2·chi, точно над Q. Кривизна сосредоточена в вершинах как РАЦИОНАЛЬНЫЙ дефект, а эйлерова характеристика — защищённое целое (топологический инвариант). Element-сторона кривизны без вещественной геометрии. _(gauss-bonnet, euler-characteristic, rational-curvature)_
- **`dodeca_defect`** - Додекаэдр: 20 вершин × дефект(3 пятиугольника) = 4 точно — даже для пятиугольных граней (угол 3/5·pi) сумма рациональна и равна 2·chi. Демонстрирует, что топологический инвариант не зависит от иррациональностей конкретных углов. _(dodecahedron, exact, defect)_

**Uniqueness - score 3 (new-framing).** Дискретная Гаусса-Бонне точно над Q: суммарный угловой дефект = 4 = 2·chi для всех платоновых тел, chi — защищённое целое; кривизна как рациональный вершинный дефект.
> _Caveat:_ Теорема Декарта/дискретная Гаусса-Бонне и chi=2 классичны; вклад — точная рациональная формализация (chi как защищённое целое), не новый результат.

---

## #542 - `src/geometry/DiscreteGeodesic.v` - score 2 (methods)

**Discrete geodesics: straight is shortest in the L1 metric over Q**

- **Topic.** L1 distance d1 on Q-points, polyline length plen, the triangle inequality, straight-is-geodesic and straight-is-shortest, geodesic insertion, and concrete examples (a midpoint refinement preserves length; a detour is strictly longer).
- **Role.** Discrete metric geometry over Q. Self-contained (QArith/Qabs).
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs
- **E/R/R.** _Elements:_ точки Q×Q; ломаные (списки точек); L1-расстояние d1. _Roles:_ геодезическая = кратчайший путь (роль); длина ломаной plen как мера. _Rules:_ d1 неотрицательна/симметрична, треугольное неравенство; прямая = кратчайшая. _P4:_ конечные ломаные полностью вычислимы (Element); кратчайшесть = теорема о длине, не предельный объект.
- **Classical counterpart.** Geodesics as shortest paths and the triangle inequality are classical; NEW: only a discrete L1-metric formalization where 'straight is shortest' is a polyline-length theorem over Q, with concrete detour examples.
- **Tags.** geodesic, L1-metric, discrete-geometry, methods

**Lemmas (8):**

| name | kind | role |
|---|---|---|
| `Point/d1/plen/pend` | Definition/Fixpoint | точки, L1-метрика, длина ломаной, конец |
| `qabs_sub_triangle/qabs_sub_sym` | Lemma | свойства \|a−b\| |
| `d1_nonneg/d1_sym/d1_self_zero` | Lemma | метрические аксиомы d1 |
| `d1_triangle` | Theorem | треугольное неравенство для d1 |
| `plen_app/plen_ge` | Lemma/Theorem | длина ломаной аддитивна и ≥ прямого расстояния |
| `straight_is_geodesic/straight_is_shortest` | Theorem | ★ прямая — кратчайшая ломаная |
| `geodesic_insert` | Theorem | вставка точки на отрезке не меняет длину |
| `straight_refinement_concrete/detour_strictly_longer` | Theorem | конкретные примеры (рефайнмент vs обход) |

**Key lemmas (deep):**

- **`straight_is_shortest`** - Прямая ломаная — кратчайшая (через многократное треугольное неравенство): геодезическая определяется как минимум длины, доказанный над Q. Element-сторона метрической геометрии — никаких вещественных кривых, только конечные ломаные. _(geodesic, shortest-path, L1)_
- **`detour_strictly_longer`** - Конкретный обход (через точку Up) СТРОГО длиннее прямого — свидетельство, что неравенство строгое для невырожденных путей. Делает «кратчайшесть» содержательной, а не тавтологией. _(detour, strict, concrete)_

**Uniqueness - score 2 (methods).** Дискретные геодезические над Q в L1-метрике: «прямая — кратчайшая» как теорема о длине ломаной + конкретные примеры обходов.
> _Caveat:_ Геодезические и треугольное неравенство классичны; вклад — дискретная Q-формализация, перекликается с процессным подходом к геометрии.

---

## #543 - `src/geometry/LieAlgebraSO3.v` - score 2 (methods)

**The Lie algebra so(3) over Q: bracket, structure constants, Jacobi**

- **Topic.** 3-vectors over Q, the cross-product bracket, the structure relations [e1,e2]=e3 (cyclic), bracket self-zero, antisymmetry, bilinearity, the Jacobi identity, and so(3) non-abelian.
- **Role.** Concrete Lie algebra over Q (the infinitesimal SO(3)). Self-contained (QArith).
- **Counts.** Qed 14 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ 3-векторы V3 над Q; базис e1,e2,e3. _Roles:_ скобка = роль-коммутатор (инфинитезимальная симметрия); структурные константы как роли. _Rules:_ bracket = векторное произведение; [e1,e2]=e3 циклически; антисимметрия; Якоби. _P4:_ конечная алгебра Ли над Q, всё через ring (Element); so(3) неабелева = источник неабелевости SO(3).
- **Classical counterpart.** The Lie algebra so(3) with its bracket, structure constants epsilon_ijk, antisymmetry and the Jacobi identity is classical; NEW: only the explicit Q-vector formalization (bracket bilinear, antisymmetric, Jacobi by ring) of so(3).
- **Tags.** lie-algebra, so3, jacobi, rational, methods

**Lemmas (9):**

| name | kind | role |
|---|---|---|
| `V3/Veq/Vadd/Vscale/Vneg/Vzero/bracket` | Definition | 3-векторы над Q и скобка (cross) |
| `e1/e2/e3` | Definition | базисные векторы |
| `Veq_refl/sym/trans` | Lemma | Veq — эквивалентность |
| `bracket_e1_e2/e2_e3/e3_e1` | Theorem | ★ структурные соотношения [e_i,e_j]=e_k (циклически) |
| `bracket_self_zero/bracket_antisym` | Theorem | [a,a]=0, антисимметрия |
| `bracket_add_l/scale_l/add_r/scale_r` | Theorem | билинейность скобки |
| `jacobi` | Theorem | ★ тождество Якоби |
| `so3_nonabelian` | Theorem | ★ so(3) неабелева |
| `structure_constant_123` | Definition | структурная константа [e1,e2]=e3 |

**Key lemmas (deep):**

- **`jacobi`** - Тождество Якоби для скобки (векторного произведения) над Q, доказано ring — превращает (V3,bracket) в настоящую алгебру Ли so(3). Element-сторона: инфинитезимальная группа вращений полностью рациональна и вычислима. _(jacobi, lie-algebra, so3)_
- **`so3_nonabelian`** - so(3) неабелева ([e1,e2]≠[e2,e1]) — инфинитезимальный источник неабелевости SO(3)/SU(2). Перекликается с GaloisGroup.s3_non_commutative и нитью неабелевых симметрий. _(non-abelian, so3)_

**Uniqueness - score 2 (methods).** Алгебра Ли so(3) над Q явно: скобка-cross, структурные константы [e_i,e_j]=e_k, билинейность, Якоби (через ring), неабелевость.
> _Caveat:_ so(3) и её соотношения учебная классика; вклад — явная рациональная формализация, не новая алгебра.

---

## #544 - `src/geometry/ManifoldAsLimit.v` - score 4 (synthesis+observation)

**Manifold as a PROCESS: inscribed polygon refinement with no maximal stage (vein C)**

- **Topic.** Inscribed polygons on the unit circle (square, dodecagon via 3-4-5 points), shoelace areas, refinement strictly grows the area while staying below the circumscribed bound, a half-power approximation sequence, no maximal stage, and 'manifold is a process'.
- **Role.** Vein C flagship (X = process) for geometry. Book Part XII flagship 'manifold = process'. Self-contained (QArith).
- **Counts.** Qed 14 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith List
- **E/R/R.** _Elements:_ вписанные многоугольники (списки Q-точек на окружности); площади shoelace. _Roles:_ многообразие = role-limit процесса рефайнмента; стадия n = вписанный многоугольник. _Rules:_ shoelace-площадь; рефайнмент строго растит площадь; ограничен описанной. _P4:_ многообразие ЕСТЬ строго возрастающий ограниченный процесс рефайнмента (no_maximal_stage), не завершённый предел-объект — вена C; каждая стадия актуальна (Element).
- **Classical counterpart.** Approximating a curved region by inscribed polygons and the area-as-limit construction are classical (Archimedes / exhaustion); NEW is only the P4 reframing: the manifold IS the strictly-increasing bounded refinement PROCESS (no maximal stage), not a completed limit object — vein C.
- **Tags.** manifold, process-ontology, vein-C, exhaustion, P4, no-maximum

**Lemmas (10):**

| name | kind | role |
|---|---|---|
| `Pt/on_circle/cross/sl/shoelace` | Definition/Fixpoint | точки, окружность, формула площади (шнуровка) |
| `q35/q45/square_pts/dodeca_pts` | Definition | 3-4-5 точки; квадрат и 12-угольник на окружности |
| `square_on_circle/dodeca_on_circle` | Theorem | вершины лежат на окружности |
| `square_area/dodeca_area` | Theorem | площади = 2 и 74/25 (точно над Q) |
| `dodeca_more_vertices/refinement_grows_area/dodeca_below_circumscribed` | Theorem | ★ рефайнмент строго растит площадь, оставаясь ниже описанной |
| `half_pow/half_pow_pos/approx` | Fixpoint/Definition | аппроксимационная последовательность 4−2·2^{−n} |
| `approx_0_is_square_area/approx_strict_incr/approx_bounded` | Theorem | приближения строго растут, ограничены 4 |
| `StrictlyIncreasing/BoundedBy` | Definition | строгий рост и ограниченность последовательности |
| `no_maximal_stage` | Theorem | ★ нет максимальной стадии рефайнмента |
| `area_process_is_a_process/manifold_is_a_process` | Theorem | ★ площадь/многообразие = процесс |

**Key lemmas (deep):**

- **`manifold_is_a_process`** - Флагман вены C для геометрии: многообразие (область, ограниченная кривой) ЕСТЬ строго возрастающий ограниченный процесс вписанных рефайнментов — no_maximal_stage гарантирует, что нет завершающей стадии. То, что классика называет «площадью как пределом», расщепляется на правило-рефайнмент (P4-актуальное) + платонистский предел-объект (отброшен). Книжный флагман Части XII «многообразие=процесс». _(manifold, process, vein-C, no-maximum)_
- **`refinement_grows_area`** - Рефайнмент квадрат→12-угольник СТРОГО растит площадь (2 < 74/25), оставаясь ниже описанной границы — конкретное свидетельство монотонно-ограниченного процесса. Площадь приближается, но стадия её не «достигает» (как 0.999…→1 точкой-равенством). _(refinement, monotone-bounded, exhaustion)_

**Uniqueness - score 4 (synthesis+observation).** Многообразие как строго возрастающий ограниченный процесс рефайнмента (вписанные многоугольники, no_maximal_stage) над Q — вена C: многообразие ЕСТЬ процесс, не завершённый предел-объект. Книжный флагман Части XII.
> _Caveat:_ Исчерпание Архимеда и площадь-как-предел классичны; уникальность — в P4-переобрамлении (правило вместо завершённого объекта) + аксиомо-свободном Q-исполнении, не в новой геометрии.

---

## #545 - `src/geometry/QuaternionRotation.v` - score 3 (new-framing)

**Quaternion rotations over Q: multiplicative norm, double cover SU(2)->SO(3)**

- **Topic.** Quaternions H over Q with multiplication, conjugate, norm; i^2=j^2=k^2=-1, ij=k, non-commutativity, norm multiplicative, the conjugation action preserves the pure part and the norm (rotation), the double cover q and -q act identically, and a concrete order-3 rational rotation (qhalf).
- **Role.** Vein D-flavour: rational quaternion rotation group (Spin(3)). Self-contained (QArith).
- **Counts.** Qed 24 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ кватернионы H над Q; чистые кватернионы (векторы); единичные кватернионы. _Roles:_ единичный кватернион = поворот SO(3) (через сопряжение); норма как роль-инвариант. _Rules:_ Hmul ассоциативна; норма мультипликативна (Эйлер 4 квадрата); сопряжение сохраняет норму/чистоту; q и −q дают тот же поворот. _P4:_ рациональные кватернион-повороты = Element (точная Q-арифметика, норм-форма); иррациональные углы (напр. порядок 5) = role-limit (связь с RationalQuaternions/q-kinematics).
- **Classical counterpart.** Quaternions, the multiplicative norm (Euler four-square), the conjugation action on pure quaternions, and the double cover SU(2)->SO(3) are classical; NEW: only the explicit Q-arithmetic formalization (associativity, norm multiplicative, double cover, an order-3 rational rotation) over Q.
- **Tags.** quaternions, SO3, double-cover, norm-form, rational-rotation, new-framing

**Lemmas (13):**

| name | kind | role |
|---|---|---|
| `H/Heq/Hadd/Hneg/Hzero/Hone/Hmul/Hconj/Hnorm2/pureH` | Definition | кватернионы над Q и операции |
| `qi/qj/qk` | Definition | мнимые единицы |
| `Heq_refl/sym/trans` | Lemma | Heq — эквивалентность |
| `Hnorm2_mult` | Theorem | ★ норма мультипликативна (Эйлер 4 квадрата) |
| `Hnorm2_conj/Hconj_mul/Hmul_conj_eq_norm` | Theorem | свойства сопряжения и нормы |
| `Hmul_assoc/Hmul_one_l/one_r` | Theorem | ассоциативность, единица |
| `qi_squared/qj_squared/qk_squared` | Theorem | i²=j²=k²=−1 |
| `qij/qjk/qki` | Theorem | ij=k, jk=i, ki=j |
| `quaternion_not_commutative` | Theorem | ★ некоммутативность (ij≠ji) |
| `conjugate_action/conjugate_action_pure` | Definition/Theorem | сопряжение действует на чистой части |
| `rotation_scales_norm/rotation_preserves_norm` | Theorem | поворот сохраняет норму |
| `double_cover` | Theorem | ★ q и −q дают один поворот (двойное накрытие) |
| `qhalf/qhalf_unit/qhalf_cube/rotation_order3` | Definition/Theorem | ★ конкретный поворот порядка 3 |

**Key lemmas (deep):**

- **`double_cover`** - Двойное накрытие SU(2)→SO(3): кватернионы q и −q задают ОДИН и тот же поворот через сопряжение — формализовано над Q. Element-сторона: рациональная Spin(3)-группа, точная арифметика, никаких вещественных углов. _(double-cover, SU2-SO3, spin)_
- **`Hnorm2_mult`** - Норма мультипликативна (тождество Эйлера о 4 квадратах) — превращает единичные кватернионы в ГРУППУ относительно умножения (норм-форма). Тот же норм-форменный Element-механизм, что в q-kinematics (RationalQuaternions/Hurwitz). _(norm-form, euler-four-square, group)_
- **`rotation_order3`** - Конкретный рациональный поворот порядка 3 (qhalf=(½,½,½,½)) — ④-разрешённый порядок (∈{1,2,3,4,6}). Иррациональные порядки (5/икосаэдр) — role-limit (√5), как в кристаллографическом ограничении. _(order-3, rational-rotation, crystallographic)_

**Uniqueness - score 3 (new-framing).** Рациональные кватернион-повороты SO(3) над Q: мультипликативная норма (Эйлер 4 квадрата) = групповая замкнутость, двойное накрытие SU(2)→SO(3), конкретный поворот порядка 3 — Element-сторона Spin(3).
> _Caveat:_ Кватернионы, норм-форма и двойное накрытие классичны; вклад — явная Q-формализация, тесно связан с норм-форменной нитью q-kinematics.

---

## #546 - `src/geometry/RationalSO3.v` - score 3 (new-framing)

**Rational SO(3): rotation matrices from circle points; a cyclic order-3 rotation**

- **Topic.** 3x3 matrices over Q; rot_z(c,s) from a rational circle point (c^2+s^2=1) is orthogonal with det 1; the coordinate-cycling matrix cyc is orthogonal, det 1, and order 3.
- **Role.** Vein B/D-flavour: rational rotations of SO(3). Self-contained (QArith).
- **Counts.** Qed 5 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ 3x3-матрицы над Q; рациональные точки окружности (c,s). _Roles:_ поворот z как роль SO(3); cyc как конечный поворот порядка 3. _Rules:_ on_circle c s = c²+s²=1; rot_z ортогонален/det=1; cyc³=Mid. _P4:_ рациональные повороты (из пифагоровых троек) = Element; конечный порядок 3 вычислим; иррациональные углы — role-limit.
- **Classical counterpart.** Rational rotation matrices (from rational circle points = Pythagorean triples) and finite-order rotations are classical; NEW: only the explicit Q-instance (rot_z orthogonal/det-1 from a circle point, a cyclic order-3 rotation) tying rational data to SO(3).
- **Tags.** SO3, rational-rotation, pythagorean, finite-order, new-framing

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `M3/Meq/Mtrans/Mmul/Mid/Mdet/orthogonal` | Definition | матрицы над Q и операции |
| `on_circle/rot_z` | Definition | точка окружности; поворот вокруг z |
| `rot_z_orthogonal` | Theorem | ★ rot_z ортогонален при c²+s²=1 |
| `rot_z_det` | Theorem | det(rot_z)=1 |
| `cyc` | Definition | циклическая перестановка координат |
| `cyc_orthogonal/cyc_det` | Theorem | cyc ортогонален, det=1 |
| `cyc_order3` | Theorem | ★ cyc³=Mid (порядок 3) |

**Key lemmas (deep):**

- **`rot_z_orthogonal`** - Поворот rot_z(c,s) из РАЦИОНАЛЬНОЙ точки окружности (c²+s²=1, т.е. пифагорова тройка) ортогонален с det=1 — Element-сторона SO(3): рациональные повороты точны без вещественных углов. Прямая связь с пифагоровыми тройками / RationalRotationGroup из q-kinematics. _(rational-rotation, SO3, pythagorean)_
- **`cyc_order3`** - Циклическая перестановка координат — поворот порядка 3 (cyc³=Mid), ④-разрешённый порядок. Конкретный конечный элемент SO(3,ℚ), вычислимый точно. _(order-3, finite-order)_

**Uniqueness - score 3 (new-framing).** Рациональные повороты SO(3) из точек окружности (пифагоровых троек): rot_z ортогонален/det=1, циклический поворот порядка 3 — Element-сторона группы вращений над Q.
> _Caveat:_ Рациональные матрицы вращений и конечные порядки классичны; вклад — явный Q-инстанс, связан с q-kinematics (RationalRotationGroup/④).

