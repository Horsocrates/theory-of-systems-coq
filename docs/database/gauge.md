# Database - cluster `gauge`

_Generated from `gauge.json` by `generate.ps1` - do not edit by hand; edit the JSON._

**114 files / 2039 Qed.** Score distribution: s5=0 / s4=3 / s3=26 / s2=59 / s1=23 / s0=3

---

## #426 - `src/gauge/Block3D.v` - score 1 (exposition)

**S3 x Z2 block decomposition of the 8x8 3-link transfer matrix; both 2x2 blocks at beta=8**

- **Topic.** Uses complement symmetry h <-> 3-h to split the Hamming-weight 4x4 block of the 3-link SU(2)-style transfer matrix into an even and an odd 2x2 block, then computes both blocks at beta=8 (each = [[2,0],[0,3/8]]) and reads off eigenvalues 1 and 1/16 against the Gram diag(2,6).
- **Role.** Leaf computation in the lattice mass-gap chain. Imports gauge.Coupled2D and gauge.Coupled3D (block_u, w3d, hamming_sum_3d, block_u_8_* point values); consumes their beta=8 entry lemmas. Not known to be re-imported by other catalogued gauge files; a terminal verification node.
- **Counts.** Qed 14 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith QArith.Qabs Lia ZArith Lqa; ToS: gauge.Coupled2D; ToS: gauge.Coupled3D
- **E/R/R.** _Elements:_ конкретные рациональные элементы матрицы block_u beta h1 h2 при h1,h2<=3; точечные значения при beta=8 (block_u_8_00/11/22/33, off-diag=0). _Roles:_ сектора чётности (even/odd под комплементом h<->3-h) = роли-подпространства; запись 2x2-блока = роль наблюдаемой матрицы Грама diag(2,6). _Rules:_ комплемент-симметрия block_u beta h1 h2 == block_u beta (3-h1) (3-h2); собственное число записано как умножение (== 1*2, == (1#16)*6) чтобы обойти деление над Q. _P4:_ конечная актуальность: всё сведено к перебору h в {0,1,2,3} (destruct h as [\|[\|[\|[\|?]]]]; lia) и одному beta=8; ничего не берётся в континуальном пределе — это вычислимый Element-факт на фиксированной решётке, не утверждение о непрерывной теории.
- **Classical counterpart.** Классический аналог — разложение оператора, коммутирующего с действием конечной группы (здесь S3 на 3 линках x Z2-дополнение), на инвариантные подпространства (лемма Шура / теория характеров) и диагонализация трансфер-матрицы решёточной калибровочной теории. Отличие: здесь нет ни групповых представлений, ни вещественной линейной алгебры — приводимость проверена поэлементной комплемент-симметрией над Q, а собственные числа вычислены лишь в одной точке beta=8 точной рациональной арифметикой.
- **Tags.** gauge, transfer-matrix, block-diagonal, SU2, beta-8, rational-Q, mass-gap, finite-lattice
- **Notes.** qed: заголовочный комментарий обещает '~18 Qed', фактический счёт Qed = 15 (drift). 0 Admitted, 0 собственных axiom/parameter. Файл не имеет стандартного E/R/R-заголовка (только ASCII-бокс) — отступление от конвенции.

**Lemmas (21):**

| name | kind | role |
|---|---|---|
| `hamming_sum_complement` | Lemma | hamming_sum_3d комплемент-симметрична: D(h1,h2)==D(3-h1,3-h2) (перебор h) |
| `block_u_complement` | Theorem | запись блока комплемент-симметрична: block_u beta h1 h2 == block_u beta (3-h1)(3-h2) |
| `even_block_00` | Definition | элемент [0,0] чётного 2x2-блока (база \|0>+\|3>, \|1>+\|2>) |
| `even_block_01` | Definition | недиагональный элемент чётного блока |
| `even_block_11` | Definition | элемент [1,1] чётного блока |
| `even_block_00_at_8` | Theorem | even_block_00 8 == 2 (через block_u_8_00/33 и offdiag=0) |
| `even_block_01_at_8` | Theorem | even_block_01 8 == 0 (4 off-diag обнуляются) |
| `even_block_11_at_8` | Theorem | even_block_11 8 == 3#8 |
| `even_eigenvalue_ground` | Theorem | основное собств. число: even_block_00 8 == 1*2 (lambda0=1 при Gram-весе 2) |
| `even_eigenvalue_excited` | Theorem | возбуждённое: even_block_11 8 == (1#16)*6 (lambda1=1/16 при Gram-весе 6) |
| `odd_block_00` | Definition | элемент [0,0] нечётного блока (база \|0>-\|3>, \|1>-\|2>) |
| `odd_block_01` | Definition | недиагональный элемент нечётного блока |
| `odd_block_11` | Definition | элемент [1,1] нечётного блока |
| `odd_block_00_at_8` | Theorem | odd_block_00 8 == 2 (идентично чётному) |
| `odd_block_01_at_8` | Theorem | odd_block_01 8 == 0 |
| `odd_block_11_at_8` | Theorem | odd_block_11 8 == 3#8 |
| `odd_eigenvalue_ground` | Theorem | odd_block_00 8 == 1*2 |
| `odd_eigenvalue_excited` | Theorem | odd_block_11 8 == (1#16)*6 |
| `blocks_equal_at_8` | Theorem | чётный и нечётный блоки совпадают при beta=8 (все три элемента) |
| `block_3d_main` | Theorem | ★ сводка: оба блока + оба собственных числа (1 и 1/16) при beta=8 |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`block_u_complement`** - Несущая структурная лемма файла: комплемент-симметрия block_u beta h1 h2 == block_u beta (3-h1)(3-h2) — это та инвариантность Z2 (дополнение трёх линков), которая ВООБЩЕ позволяет распасться 4x4 на два 2x2. Доказывается грубым перебором h1,h2 in {0,1,2,3} + ring; никакой теории представлений S3/Z2 не вызывается — симметрия проверяется поэлементно. Честно: это не доказательство приводимости в смысле теории групп, а её арифметическая тень на конкретной матрице. _(complement-symmetry, block-decomposition, Z2, vm-style)_
- **`block_3d_main`** - Капстоун-агрегат: при beta=8 оба сектора дают [[2,0],[0,3/8]], откуда собственные числа 1 и 1/16 (отношение 1/16 = квадрат 2D-щели 1/4 — отсылка к BlockDiagonal2D). Чисто точечный факт на одной связи beta=8; это НЕ непрерывный предел и НЕ доказательство щели масс Янга-Миллса. Значение собств. числа записано умножением, чтобы lra/Q не спотыкались о деление. _(eigenvalues, beta-8, point-fact, mass-gap-input)_

**Uniqueness - score 1 (exposition).** Конкретное рациональное расщепление 8x8-трансфер-матрицы на 2x2-блоки через комплемент-симметрию и точечное считывание собственных чисел {1,1/16} при beta=8.
> _Caveat:_ Стандартная симметрийная блок-диагонализация трансфер-матрицы, выполненная вручную над Q в ОДНОЙ точке beta=8 на фиксированной 3-линковой решётке. НЕ континуальный предел, НЕ доказательство щели масс Янга-Миллса (Clay); собственные числа — точечные факты, не спектр непрерывной теории. Заголовок-комментарий гласит '~18 Qed' — фактически 15 (нет E/R/R-заголовка по конвенции CLAUDE.md, только комментарий-бокс).

---

## #427 - `src/gauge/BlockDiagonal2D.v` - score 2 (methods)

**Link-swap symmetry decomposition of the 4x4 2D transfer matrix; all four eigenvalues at beta=8**

- **Topic.** Decomposes the 4x4 2D plaquette transfer matrix T2D (which commutes with the link swap (theta1,theta2) <-> (theta2,theta1)) into two exact antisymmetric eigenvectors |->=(1,0,0,-1) and |q>=(0,1,-1,0) plus a symmetric 2x2 block B, proves the key identity (1+a^2)^2 - 4a^2 = (1-a^2)^2, and computes all four eigenvalues {1,1,1/4,1/4} at beta=8.
- **Role.** Foundational 2D eigen-decomposition feeding the 3D analogue (Block3D) and the mass-gap/ratio files. Imports gauge.Coupled2D (t4_apply, t4_entry, v_minus, v_q, alpha_2d, gamma_2d). Provides the value 1/4 (excited eigenvalue) reused as the squared building block 1/16 in Block3D.
- **Counts.** Qed 25 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith QArith.Qabs Lia ZArith Lqa; ToS: gauge.Coupled2D
- **E/R/R.** _Elements:_ записи 4x4-матрицы t4_entry beta; конкретные собственные векторы v_minus=(1,0,0,-1), v_q=(0,1,-1,0); рациональные параметры alpha_2d, gamma_2d. _Roles:_ симметричный/антисимметричный сектора под перестановкой линков = роли-подпространства; собственный вектор = роль (выделенное направление), собственное число = роль масштаба; блок B = роль остаточной 2x2-наблюдаемой. _Rules:_ T2D коммутирует с обменом (theta1,theta2)<->(theta2,theta1); eigen-уравнение t4_apply beta v i == lambda * v i проверяется построчно (i in {0,1,2,3}); ключевое тождество (1+a^2)^2-4a^2==(1-a^2)^2 даёт точный дискриминант блока. _P4:_ конечная актуальность: всё пространство 4-мерно, проверка идёт перебором i in {0,1,2,3} (destruct + ring); собственные числа берутся в одной точке beta=8 точной Q-арифметикой. Это вычислимый факт на минимальной решётке, не предельное утверждение.
- **Classical counterpart.** Классический аналог — диагонализация трансфер-матрицы 2D решёточной калибровочной модели по симметрии перестановки линков (разбиение на симметричный/антисимметричный секторы, как при использовании коммутирующей инволюции для приведения матрицы к блочно-диагональному виду). Отличие: точные собственные векторы и тождество дискриминанта над Q (символьно, при любом beta), а собственные ЗНАЧЕНИЯ считаны лишь в точке beta=8 точной рациональной арифметикой — без вещественной линейной алгебры и без континуального предела.
- **Tags.** gauge, transfer-matrix, eigenvalues, block-diagonal, link-swap, discriminant, rational-Q, beta-8, finite-lattice
- **Notes.** qed: заголовочный комментарий обещает '~28 Qed', фактический счёт Qed = 26 (drift). 0 Admitted, 0 собственных axiom/parameter. Нет стандартного E/R/R-заголовка (только ASCII-бокс). 1/4 здесь -> 1/16 в Block3D (#426).

**Lemmas (34):**

| name | kind | role |
|---|---|---|
| `eigenvalue_minus` | Definition | собств. число вектора \|->: 1 - alpha^2 |
| `eigenvec_minus_row0` | Lemma | строка 0: t4_apply beta v_minus 0 == eigenvalue_minus beta |
| `eigenvec_minus_row1` | Lemma | строка 1 == 0 |
| `eigenvec_minus_row2` | Lemma | строка 2 == 0 |
| `eigenvec_minus_row3` | Lemma | строка 3 == -(eigenvalue_minus beta) |
| `eigenvec_minus_eigenvalue` | Theorem | ★ полное eigen-уравнение для \|-> по всем i<4 |
| `eigenvalue_minus_at_8` | Lemma | eigenvalue_minus 8 == 1 |
| `eigenvalue_minus_at_0` | Lemma | eigenvalue_minus 0 == 0 (предел сильной связи) |
| `eigenvalue_q` | Definition | собств. число вектора \|q>: gamma^2 (1-alpha^2) |
| `eigenvec_q_row0` | Lemma | строка 0 == 0 |
| `eigenvec_q_row1` | Lemma | строка 1 == eigenvalue_q beta |
| `eigenvec_q_row2` | Lemma | строка 2 == -(eigenvalue_q beta) |
| `eigenvec_q_row3` | Lemma | строка 3 == 0 |
| `eigenvec_q_eigenvalue` | Theorem | ★ полное eigen-уравнение для \|q> по всем i<4 |
| `eigenvalue_q_at_8` | Lemma | eigenvalue_q 8 == 1#4 |
| `block_B_00` | Definition | [0,0] симметричного блока: 1+alpha^2 |
| `block_B_01` | Definition | [0,1] блока: 2*alpha*gamma |
| `block_B_11` | Definition | [1,1] блока: gamma^2(1+alpha^2) |
| `block_trace` | Definition | след блока B |
| `block_det` | Definition | определитель блока B |
| `block_discriminant` | Definition | дискриминант trace^2 - 4 det |
| `algebraic_identity` | Lemma | ★ (1+a^2)^2 - 4a^2 == (1-a^2)^2 (точный квадрат дискриминанта) |
| `block_det_formula` | Theorem | det B == gamma^2 (1-alpha^2)^2 |
| `block_B_00_at_8` | Lemma | block_B_00 8 == 1 |
| `block_B_01_at_8` | Lemma | block_B_01 8 == 0 (блок диагонализуется при beta=8) |
| `block_B_11_at_8` | Lemma | block_B_11 8 == 1#4 |
| `block_trace_at_8` | Theorem | trace 8 == 5#4 |
| `block_det_at_8` | Theorem | det 8 == 1#4 |
| `block_disc_at_8` | Theorem | discriminant 8 == 9#16 |
| `block_eigen_sum_at_8` | Theorem | 1 + 1/4 == trace 8 (проверка суммы собств. чисел) |
| `block_eigen_product_at_8` | Theorem | 1 * 1/4 == det 8 (проверка произведения) |
| `four_eigenvalues_at_8` | Theorem | ★ eigenvalue_minus 8==1 и eigenvalue_q 8==1/4 |
| `eigenvalue_trace_check` | Theorem | 1+1/4+1/4+1 == 5/2 (полный след) |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`eigenvec_minus_eigenvalue`** - Точное eigen-уравнение по всем строкам сразу: t4_apply beta v_minus i == eigenvalue_minus beta * v_minus i для i<4, доказано destruct i as [\|[\|[\|[\|?]]]] + ring. Это не численная аппроксимация и не предельное утверждение — точное символьное равенство над Q при ЛЮБОМ beta, с явным собственным вектором (1,0,0,-1) из симметрии обмена линков. Распознаваемая ценность файла: собственный спектр получен точной алгеброй, а не диагонализацией с плавающей точкой. _(eigenvector, exact, link-swap-symmetry, all-beta)_
- **`algebraic_identity`** - (1+a^2)^2 - 4a^2 == (1-a^2)^2 — одно ring-тождество, делающее дискриминант блока ТОЧНЫМ полным квадратом, откуда det B = gamma^2(1-alpha^2)^2 и собственные числа блока рациональны при любом beta (а не только beta=8). Перекликается с cluster-вейной 'дискриминант = полный квадрат => рациональный корень' (ср. QuadraticDiscriminant.v), но здесь это вспомогательная алгебра, а не тезис о границе финитизации. _(discriminant, perfect-square, rational-eigenvalues, ring)_
- **`four_eigenvalues_at_8`** - Сводка спектра при beta=8: {1,1,1/4,1/4} — два собственных числа из явных векторов (\|->,\|q>) и два из блока B, с перекрёстной проверкой sum=trace, product=det. Точечный факт на одной связи; 1/4 далее возводится в квадрат до 1/16 в Block3D. НЕ спектр непрерывной теории и НЕ щель масс Clay. _(spectrum, beta-8, cross-check, point-fact)_

**Uniqueness - score 2 (methods).** Точная символьная eigen-декомпозиция 4x4-трансфер-матрицы над Q по симметрии обмена линков (явные собственные векторы при любом beta + тождество дискриминанта как полный квадрат), со спектром {1,1,1/4,1/4} при beta=8.
> _Caveat:_ Содержание стандартно (симметрийная блок-диагонализация трансфер-матрицы); необычна лишь форма — точная Q-арифметика вместо вещественной ЛА. Спектр вычислен в ОДНОЙ точке beta=8 на минимальной 2D-решётке. НЕ континуальный предел, НЕ доказательство щели масс Янга-Миллса. Заголовок-комментарий гласит '~28 Qed' — фактически 26 (drift); стандартного E/R/R-заголовка нет.

---

## #428 - `src/gauge/CharacterTransfer.v` - score 3 (new-framing)

**Diagonal SU(2) transfer matrix in the character basis via rational Bessel partial sums**

- **Topic.** Builds the exact SU(2) Wilson-action transfer matrix in the Peter-Weyl character basis, where it is diagonal with eigenvalues t_j(beta) = I_{2j}(beta) - I_{2j+2}(beta); the modified Bessel functions I_n are represented over Q as finite partial sums I_n^{(M)}(beta) = sum_{m<=M} (beta/2)^{n+2m}/(m!(n+m)!). Proves nonnegativity, rationality, t_0 >= 0 for small beta, and the structural diagonality.
- **Role.** Mid-chain bridge: supplies transfer_eigenvalue and character_mass_gap to the correlation/cluster files. Imports CauchyReal, SeriesConvergence, stdlib.Combinatorics (fact), gauge.SU2Characters. Reused by gauge.ClusterProof (#430) which pulls transfer_eigenvalue and t0_positive_small.
- **Counts.** Qed 21 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith QArith.Qabs Lia ZArith Lqa List; ToS: CauchyReal; ToS: SeriesConvergence; ToS: stdlib.Combinatorics; ToS: gauge.SU2Characters
- **E/R/R.** _Elements:_ рациональные частичные суммы Бесселя bessel_partial n beta M; факториалы fact_Q; конкретные значения I_0=1, I_2~beta^2/8. _Roles:_ собственное число трансфер-матрицы transfer_eigenvalue j = роль масштаба моды j; диагональность в базисе характеров = роль (Питер-Вейль делает оператор-свёртку диагональным); character_mass_gap = роль разности t_0-t_1. _Rules:_ t_j = I_{2j} - I_{2j+2}; bessel_partial рекурсивна по M (Fixpoint); диагональность СТРУКТУРНА: ядро exp(beta cos(theta1-theta2)) = свёртка => диагональна в характерном/Фурье-базисе. _P4:_ конечная актуальность дважды: (1) бесконечный ряд Бесселя ОБРЕЗАН до конечной частичной суммы порядка M (нетерминирующий процесс, взятый на конечном шаге — Element); (2) положительность t_0 доказана лишь для beta in [0,2] (малая связь), а монотонность t_0>t_1>... только заявлена через bessel_decreasing_property, но не доказана в общем.
- **Classical counterpart.** Классический аналог — характерное (Питер-Вейль) разложение трансфер-матрицы SU(2) Wilson-действия, где собственные числа суть t_j = I_{2j}(beta) - I_{2j+2}(beta) через модифицированные функции Бесселя I_n; диагональность следует из ортогональности характеров для оператора-свёртки. Отличие здесь: I_n заменены конечными рациональными частичными суммами (обрезание ряда => Element-сторона процесса), диагональность доказана лишь в суррогатной индексной форме (не как зануление недиагоналей), а положительность/монотонность спектра — только для beta in [0,2].
- **Tags.** gauge, transfer-matrix, character-basis, bessel, SU2, peter-weyl, rational-Q, process-cutoff, honesty-flag
- **Notes.** qed: E/R/R и ASCII заголовки оба обещают '~35 Qed', фактический счёт Qed = 21 (значительный drift, -14). 0 Admitted, 0 собственных axiom/parameter (заголовок верно: AXIOMS none). FLAG: transfer_diagonal_structural — суррогатное утверждение, имя обещает диагональность Питера-Вейля, доказывает лишь j<>k => 2j+1<>2k+1.

**Lemmas (29):**

| name | kind | role |
|---|---|---|
| `fact_Q` | Definition | факториал как рациональное число inject_Z(Z.of_nat(fact n)) |
| `fact_Q_pos` | Lemma | 0 < fact_Q n |
| `fact_Q_0` | Lemma | fact_Q 0 == 1 |
| `fact_Q_1` | Lemma | fact_Q 1 == 1 |
| `fact_Q_2` | Lemma | fact_Q 2 == 2 |
| `fact_Q_3` | Lemma | fact_Q 3 == 6 |
| `fact_Q_4` | Lemma | fact_Q 4 == 24 |
| `fact_prod` | Definition | произведение факториалов m!*n! (знаменатель члена Бесселя) |
| `fact_prod_pos` | Lemma | 0 < fact_prod m n |
| `bessel_term` | Definition | член ряда Бесселя (beta/2)^(n+2m)/(m!(n+m)!) |
| `bessel_partial` | Fixpoint | частичная сумма I_n^(M)(beta) до m=M (рекурсия по M) |
| `bessel_term_nonneg` | Lemma | член неотрицателен при beta>=0 |
| `bessel_partial_nonneg` | Lemma | частичная сумма неотрицательна при beta>=0 (индукция по M) |
| `bessel_I0_M0` | Lemma | I_0^(0)(beta) == 1 (нулевой член = 1) |
| `bessel_I2_M0_nonneg` | Lemma | I_2^(0) неотрицательна |
| `I0_dominates_I2` | Lemma | I_2 <= I_0 при beta in [0,2] (через nia над Z) |
| `bessel_rational` | Lemma | bessel_partial всегда вида num#den (тривиально: Q и есть пара) |
| `transfer_eigenvalue` | Definition | ★ t_j = bessel_partial(2j) - bessel_partial(2j+2) (точное SU(2) собств. число) |
| `eigenvalue_rational` | Lemma | собств. число рационально (тривиально) |
| `t0_positive_small` | Lemma | 0 <= t_0 при beta in [0,2] (из I0_dominates_I2) |
| `transfer_is_diagonal` | Definition | Prop: j<>k => 2j+1<>2k+1 (суррогат диагональности) |
| `transfer_diagonal_structural` | Theorem | transfer_is_diagonal доказана (по сути lia) |
| `transfer_diagonal_formula` | Theorem | диагональный элемент рационален (= eigenvalue_rational) |
| `character_mass_gap` | Definition | щель t_0 - t_1 в характерном базисе |
| `gap_formula` | Lemma | gap == I_0 - 2 I_2 + I_4 |
| `gap_rational` | Lemma | щель рациональна (тривиально) |
| `bessel_decreasing_property` | Definition | Prop-обёртка монотонности I_{n+2}<=I_n (НЕ доказана в общем) |
| `bessel_dec_M0_0_2` | Lemma | I_2<=I_0 при M=0 (= I0_dominates_I2) |
| `character_transfer_summary` | Theorem | ★ сводка: диагональность + рациональность собств. чисел и щели + t_0>=0 для малых beta + неотрицательность Бесселя |

**Key lemmas (deep):**

- **`transfer_eigenvalue`** - Сердцевина файла: точное собственное число SU(2)-трансфер-матрицы Вильсона t_j = I_{2j}-I_{2j+2}, представленное конечными рациональными частичными суммами Бесселя. Это E/R/R-инстанс нетерминирующего процесса (ряд Бесселя) на конечном шаге M: каждый t_j(beta,M) есть вычислимое рациональное число (Element-сторона), а истинное I_n — его role-limit. Распознаваемо ново лишь обрамление; формула t_j = I_{2j}-I_{2j+2} классична (характерное разложение exp(beta cos)). _(transfer-eigenvalue, bessel, rational-truncation, peter-weyl, process-cutoff)_
- **`transfer_diagonal_structural`** - ЧЕСТНАЯ слабость, требующая флага: 'диагональность' здесь НЕ доказана как ортогональность характеров. transfer_is_diagonal определена как суррогат forall j k, j<>k -> 2j+1<>2k+1, что доказывается одним lia и НЕ выражает зануление недиагональных элементов трансфер-матрицы. Настоящая диагональность по Питеру-Вейлю лишь заявлена в комментарии. То есть имя теоремы обещает больше, чем её утверждение даёт. _(diagonality, surrogate-statement, over-claim, peter-weyl, honesty-flag)_
- **`I0_dominates_I2`** - Единственная нетривиальная аналитическая лемма: I_2 <= I_0 на beta in [0,2], сведённая к целочисленному nia над Z после раскрытия Q. Это обеспечивает t_0 >= 0 (положительность ведущего собственного числа) лишь в режиме малой связи. Монотонность всего спектра t_0>t_1>... (нужная для щели) остаётся только обёрткой-Prop bessel_decreasing_property без общего доказательства. _(bessel-monotonicity, small-beta, nia, conditional)_

**Uniqueness - score 3 (new-framing).** Точные SU(2)-собственные числа трансфер-матрицы t_j = I_{2j}-I_{2j+2}, представленные конечными рациональными частичными суммами Бесселя как Element-сторона нетерминирующего процесса (ряд обрезан на шаге M).
> _Caveat:_ Формула t_j и характерная диагональность классичны (Питер-Вейль, Wilson). Ново только обрамление 'ряд Бесселя = процесс, обрезание = Element'. ЧЕСТНЫЕ пробелы: (1) diagonality доказана суррогатом forall j k, 2j+1<>2k+1 (один lia), а НЕ как ортогональность характеров — имя сильнее утверждения; (2) положительность t_0 только для beta in [0,2]; (3) полная монотонность спектра НЕ доказана (лишь Prop-обёртка). НЕ доказательство щели масс Янга-Миллса.

---

## #429 - `src/gauge/ClebschGordan.v` - score 2 (methods)

**SU(2) Clebsch-Gordan selection rules and Casimir coupling coefficients (tridiagonal spatial Hamiltonian)**

- **Topic.** Encodes the SU(2) tensor product j (x) 1 = (j-1) (+) j (+) (j+1) at the character level (chi_j chi_1 = chi_{j-1}+chi_j+chi_{j+1}), giving the |j-j'|<=1 selection rule that makes the spatial Hamiltonian tridiagonal; defines and tabulates the Casimir diagonal j(j+1)/(2j+1)^2 and off-diagonal (j+1)/((2j+1)(2j+3)) coupling coefficients, with monotonicity and a positive spatial mass-gap contribution beta_s*d_sp*2/9.
- **Role.** Supplies the spatial (magnetic) coupling structure for the (d+1)D mass-gap assembly. Imports CauchyReal, SeriesConvergence, gauge.SU2Characters (su2_character). Self-contained tabulation; provides spatial_gap_contribution / spatial_gap_positive consumed by higher mass-gap files.
- **Counts.** Qed 37 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith QArith.Qabs Lia ZArith Lqa; ToS: CauchyReal; ToS: SeriesConvergence; ToS: gauge.SU2Characters
- **E/R/R.** _Elements:_ характеры su2_character j c; рациональные коэффициенты spatial_diagonal j = j(j+1)/(2j+1)^2 и spatial_offdiag j; счётчик spatial_plaquette_count. _Roles:_ правило отбора coupling_allowed (\|j-j'\|<=1) = роль связности (трёхдиагональность); диагональ Казимира = роль энергии состояния \|j>; off-diag = роль амплитуды перехода j<->j+1. _Rules:_ chi_j*chi_1 == chi_{j-1}+chi_j+chi_{j+1} (ring над характерами-многочленами); проверка размерностей (2j+1)*3 = сумма трёх; spatial_energy = beta_s*d_sp*spatial_diagonal j. _P4:_ конечная актуальность: все характерные тождества проверены ring на конкретных низких j (0,1,2,3) — не индукцией по общему j; правило отбора и трёхдиагональность даны на фиксированных малых модах; спектральная щель 2/9 вычислена точно над Q для перехода j=0->1.
- **Classical counterpart.** Классические аналоги: правило Клебша-Гордана для SU(2), chi_j*chi_1 = chi_{j-1}+chi_j+chi_{j+1} и правило отбора \|j-j'\|<=1 (теория сложения момента импульса); квадратичный казимир j(j+1) как диагональная (магнитная) энергия в гамильтоновой решёточной калибровочной теории (Коган-Сасскинд). Отличие: характеры взяты как рациональные многочлены и тождества проверены ring/lra на конкретных низких j (а не индукцией по общему j), коэффициенты и щель сектора 2/9 вычислены точной Q-арифметикой.
- **Tags.** gauge, clebsch-gordan, SU2, selection-rule, casimir, tridiagonal, mass-gap, rational-Q, characters
- **Notes.** qed: E/R/R и ASCII заголовки обещают '~40 Qed', фактический счёт Qed = 37 (drift). 0 Admitted, 0 собственных axiom/parameter (заголовок верно: AXIOMS none). Характерные тождества доказаны поштучно для j=0,1,2 — общей индукции chi_j*chi_1 нет.

**Lemmas (43):**

| name | kind | role |
|---|---|---|
| `character_product_0_1` | Theorem | chi_0*chi_1 == chi_1 (тривиальное x присоединённое) |
| `character_product_1_1` | Theorem | chi_1*chi_1 == chi_0+chi_1+chi_2 (через ring над многочленами) |
| `character_product_2_1` | Theorem | chi_2*chi_1 == chi_1+chi_2+chi_3 |
| `dimension_check` | Lemma | (2j+1)*3 = (2(j-1)+1)+(2j+1)+(2(j+1)+1) (баланс размерностей) |
| `product_dimension_0` | Lemma | размерности при c=1: 1*3 |
| `product_dimension_1` | Lemma | 3*3 |
| `product_decomp_dim_1` | Lemma | chi_0+chi_1+chi_2 при c=1 == 9 |
| `product_dimension_2` | Lemma | 5*3 |
| `coupling_allowed` | Definition | ★ правило отбора: j'=j или j+1 или j=j'+1 (\|j-j'\|<=1) |
| `coupling_allowed_self` | Lemma | j связано с j |
| `coupling_allowed_next` | Lemma | j связано с j+1 |
| `coupling_allowed_prev` | Lemma | j связано с j-1 (при j>=1) |
| `spatial_diagonal` | Definition | диагональ Казимира j(j+1)/(2j+1)^2 |
| `spatial_diag_0` | Lemma | == 0 (основное состояние без энергии Казимира) |
| `spatial_diag_1` | Lemma | == 2#9 |
| `spatial_diag_2` | Lemma | == 6#25 |
| `spatial_diag_3` | Lemma | == 12#49 |
| `spatial_diag_nonneg` | Lemma | 0 <= диагональ для всех j |
| `spatial_offdiag` | Definition | off-diag (j+1)/((2j+1)(2j+3)) |
| `spatial_offdiag_0` | Lemma | == 1#3 |
| `spatial_offdiag_1` | Lemma | == 2#15 |
| `spatial_offdiag_2` | Lemma | == 3#35 |
| `spatial_offdiag_nonneg` | Lemma | 0 <= off-diag для всех j |
| `diag_increasing_0_1` | Lemma | диагональ растёт: d(0)<d(1) |
| `diag_increasing_1_2` | Lemma | d(1)<d(2) |
| `diag_increasing_2_3` | Lemma | d(2)<d(3) |
| `offdiag_decreasing_0_1` | Lemma | off-diag убывает: o(1)<o(0) |
| `offdiag_decreasing_1_2` | Lemma | o(2)<o(1) |
| `spatial_energy` | Definition | пространственная энергия плакетки beta_s*d_sp*diag j |
| `spatial_energy_ground` | Lemma | энергия основного состояния j=0 == 0 |
| `spatial_gap_contribution` | Definition | вклад щели = beta_s*d_sp*diag 1 |
| `spatial_gap_equals_energy_1` | Lemma | вклад щели == E(1)-E(0) |
| `spatial_gap_formula` | Lemma | вклад щели == beta_s*d_sp*(2#9) |
| `inject_Z_nat_pos` | Lemma | 0 < inject_Z(Z.of_nat n) при n>=1 |
| `spatial_gap_positive` | Theorem | ★ щель > 0 при beta_s>0 и d_sp>=1 |
| `spatial_gap_nonneg` | Lemma | щель >= 0 при beta_s>=0 и d_sp>=1 |
| `spatial_plaquette_count` | Definition | число пространственных плакеток d_sp(d_sp-1)/2 |
| `plaquettes_1d` | Lemma | 1D: 0 плакеток |
| `plaquettes_2plus1` | Lemma | 2+1D: 1 плакетка |
| `plaquettes_3plus1` | Lemma | 3+1D: 3 плакетки |
| `plaquettes_4plus1` | Lemma | 4+1D: 6 плакеток |
| `plaquettes_increasing_2_3` | Lemma | число плакеток растёт 2->3 |
| `plaquettes_increasing_3_4` | Lemma | растёт 3->4 |

**Key lemmas (deep):**

- **`character_product_1_1`** - Ядро правила отбора: chi_1*chi_1 == chi_0+chi_1+chi_2, т.е. SU(2)-разложение 1(x)1 = 0(+)1(+)2, проверенное ring над характерами-как-многочленами от c=cos(theta/2). Здесь характеры — конкретные рациональные многочлены (4c^2-1 и т.д.), а Клебш-Гордан проверяется тождеством колец, а не теорией представлений. Честно: тождество доказано лишь для j=0,1,2 поштучно (нет общего chi_j*chi_1 по индукции). _(clebsch-gordan, character-product, selection-rule, ring, low-j-only)_
- **`spatial_gap_positive`** - Несущий результат для сборки щели: при beta_s>0 и d_sp>=1 пространственный вклад щели = beta_s*d_sp*2/9 > 0, где 2/9 = spatial_diag 1 = Казимир состояния j=1, нормированный (2j+1)^2. Точная Q-арифметика, без аппроксимаций. Это вклад В щель магнитного (пространственного) сектора — НЕ полная щель масс и не её континуальный предел. _(mass-gap-contribution, casimir, positive, rational-Q)_
- **`coupling_allowed`** - Правило \|j-j'\|<=1, делающее пространственный гамильтониан трёхдиагональным — структурное следствие Клебша-Гордана (j(x)1 задевает лишь j-1,j,j+1). Полезная организующая абстракция, но это в точности классическое правило отбора момента импульса; новизны над учебником нет, кроме записи в Coq. _(selection-rule, tridiagonal, angular-momentum)_

**Uniqueness - score 2 (methods).** Точная рациональная табуляция SU(2) Клебш-Гордановых правил отбора и казимировых коэффициентов связи (диагональ j(j+1)/(2j+1)^2, off-diag (j+1)/((2j+1)(2j+3))), дающая трёхдиагональный пространственный гамильтониан и положительный вклад щели 2/9.
> _Caveat:_ Полностью классическое содержание (Клебш-Гордан SU(2), казимир, правило отбора момента импульса); необычна лишь точная Q-формализация и проверка характерных тождеств через ring на конкретных низких j (j=0..3) вместо общей индукции. spatial_gap_positive даёт вклад пространственного сектора, а НЕ полную щель масс и НЕ её континуальный предел. Заголовок обещает '~40 Qed' — фактически 37 (drift).

---

## #430 - `src/gauge/ClusterProof.v` - score 3 (new-framing)

**Exponential clustering (OS5) from the transfer eigenvalue ratio: connected correlations decay as r^t**

- **Topic.** Proves the cluster property (Osterwalder-Schrader OS5) for the lattice model with a full proof term: the connected two-point correlation equals (t_1/t_0)^t = gap_ratio^t, which is bounded, nonincreasing, and (since gap_ratio<1 at beta=1,2) driven below any eps; defines the decay_rate = 1 - gap_ratio and identifies it with the lattice mass gap from the ratio.
- **Role.** Capstone of the correlation sub-chain: ties character eigenvalues to clustering and the mass gap. Heavy importer: CauchyReal, SeriesConvergence, gauge.CharacterTransfer (transfer_eigenvalue, t0_positive_small), ExactMassGap, GapRatio (gap_ratio, t0_M0, t1_M0, gap_M0, gap_ratio_lt1_*), ReflectionPositivity (os5_*), LatticeCorrelations (connected_two_point), TransferMatrixProof (transfer_mat, dm_entry).
- **Counts.** Qed 23 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith QArith.Qabs Lia ZArith Lqa; ToS: CauchyReal; ToS: SeriesConvergence; ToS: gauge.CharacterTransfer; ToS: gauge.ExactMassGap; ToS: gauge.GapRatio; ToS: gauge.ReflectionPositivity; ToS: gauge.LatticeCorrelations; ToS: gauge.TransferMatrixProof
- **E/R/R.** _Elements:_ матричная корреляция matrix_corr = (t_j/t_0)^t_step; gap_ratio beta = t_1/t_0; decay_rate = 1-gap_ratio. _Roles:_ корреляция как процесс по t_step = роль наблюдаемой; gap_ratio<1 = роль сжатия (контрактивность); decay_rate = роль обратного масштаба = щель масс. _Rules:_ matrix_corr J beta 0 1 t == gap_ratio^t (Qpow_Qeq_compat); кластеризация: forall eps>0 exists N, gap_ratio^N<eps (через Qpow_vanish); OS5 = эта же кластеризация. _P4:_ конечная актуальность: кластеризация = epsilon/N-форма (для каждого конечного eps есть конечное N, после которого корреляция < eps) — НЕ актуально достигнутый нулевой предел; результат доказан как процесс на ВСЕХ M=0, но численно только при beta in {1,2}; gap_ratio<1 — вход из GapRatio для этих двух точек.
- **Classical counterpart.** Классические аналоги: аксиома кластеризации Остервальдера-Шрадера (OS5) / экспоненциальное затухание связных корреляций в решёточной QFT, где скорость спада = щель в спектре трансфер-матрицы (m = -log(lambda_1/lambda_0)). Отличие: здесь корреляция = ТОЧНО gap_ratio^t над Q, кластеризация дана конструктивно в epsilon/N-форме (P4, без актуального предела), масса определена линеаризованно (1-r вместо -log r), и всё численно закрыто лишь при beta in {1,2} на нулевом порядке Бесселя M=0.
- **Tags.** gauge, cluster-property, OS5, correlation-decay, gap-ratio, mass-gap, rational-Q, P4, epsilon-N, conditional
- **Notes.** qed: E/R/R и ASCII заголовки обещают '~30 Qed', фактический счёт Qed = 23 (drift, -7). 0 Admitted, 0 собственных axiom/parameter (заголовок верно: AXIOMS none). Имя файла 'ClusterProof' аспирационно: доказывает OS5-кластеризацию лишь для beta in {1,2} на M=0, не общую щель масс.

**Lemmas (25):**

| name | kind | role |
|---|---|---|
| `Qpow_Qeq_compat` | Lemma | Qpow уважает Qeq: a==b => a^n==b^n (индукция по n) |
| `matrix_corr` | Definition | ★ корреляция = (dm_entry j / dm_entry 0)^t_step (отношение собств. чисел в степени) |
| `matrix_corr_eq` | Theorem | matrix_corr == connected_two_point (мост к LatticeCorrelations) при M=0 |
| `matrix_corr_at_0` | Theorem | корреляция при t=0 == 1 |
| `matrix_corr_ground` | Theorem | автокорреляция основного состояния == 1 всегда |
| `matrix_corr_ratio` | Theorem | ★ возбуждённая корреляция == gap_ratio^t при M=0 |
| `matrix_corr_nonneg` | Theorem | корреляция >= 0 при gap_ratio>=0 |
| `matrix_corr_bounded` | Theorem | корреляция <= 1 при 0<=gap_ratio<=1 |
| `matrix_corr_decreasing` | Theorem | корреляция не возрастает по t |
| `gap_ratio_vanishes_1` | Theorem | gap_ratio(1)^N -> 0: для eps есть N (Qpow_vanish) |
| `gap_ratio_vanishes_2` | Theorem | gap_ratio(2)^N -> 0 |
| `cluster_property_proved_1` | Theorem | ★ кластеризация при beta=1: forall eps>0 exists t0, corr<eps |
| `cluster_property_proved_2` | Theorem | ★ кластеризация при beta=2 |
| `cluster_from_gap` | Theorem | общая кластеризация из gap_ratio<1 и t_0>0 (любое beta с этими гипотезами) |
| `decay_rate` | Definition | темп спада = 1 - gap_ratio (1-й порядок -log) |
| `decay_rate_eq_gap` | Theorem | decay_rate == gap_M0/t_0 |
| `decay_rate_positive` | Theorem | decay_rate>0 при gap_ratio<1 |
| `decay_rate_positive_1` | Theorem | decay_rate(1)>0 |
| `decay_rate_positive_2` | Theorem | decay_rate(2)>0 |
| `mass_from_decay` | Theorem | масса из кластера > 0 при gap_ratio<1 |
| `decay_rate_is_mass` | Theorem | decay_rate == lattice_mass_gap_from_ratio(gap_ratio) |
| `cluster_connected_1` | Theorem | кластеризация при beta=1 в терминах connected_two_point |
| `cluster_connected_2` | Theorem | кластеризация при beta=2 в терминах connected_two_point |
| `os5_from_matrix` | Theorem | OS5 (os5_cluster) при beta=1 и 2 |
| `cluster_proof_summary` | Theorem | ★ сводка: затухание + положительный decay_rate + OS5 при beta in {1,2} |

**Key lemmas (deep):**

- **`matrix_corr_ratio`** - Несущая идентификация: возбуждённая связная корреляция == gap_ratio^t (= (t_1/t_0)^t) при M=0, доказана Qpow_Qeq_compat. Это точное равенство над Q, превращающее затухание корреляций в геометрическую прогрессию со знаменателем gap_ratio. Здесь живёт связь спектр<->кластеризация: щель (t_0>t_1) => знаменатель<1 => экспоненциальный спад. Классично по сути (transfer-matrix => экспоненциальное затухание), но дано полным проверяемым термом над рациональными собственными числами на M=0. _(correlation, gap-ratio, geometric-decay, spectrum-clustering)_
- **`cluster_property_proved_1`** - P4-форма кластеризации: forall eps>0 exists t0, matrix_corr<eps при beta=1 — НЕ 'предел = 0', а конструктивное epsilon/N-затухание (через Qpow_vanish из GapRatio). Это и есть финитистская подпись проекта: свойство кластера выражено как достижимость любого конечного порога за конечное время, без актуальной бесконечности. ЧЕСТНО: доказано лишь при beta in {1,2} (и общо в cluster_from_gap при гипотезе gap_ratio<1), только на порядке Бесселя M=0. _(cluster-property, OS5, epsilon-N, P4, beta-specific)_
- **`decay_rate_is_mass`** - decay_rate := 1-gap_ratio отождествлён с lattice_mass_gap_from_ratio(gap_ratio) одним ring. Это связывает темп экспоненциального спада корреляций с (решёточной, из отношения) щелью масс. Осторожно: decay_rate = 1-r есть ПЕРВОПОРЯДКОВОЕ приближение -log r (как помечено в коде), т.е. определение 'массы' здесь — линеаризованное и решёточное, не континуальная масса. _(decay-rate, mass-gap-identification, linearized-log, lattice)_

**Uniqueness - score 3 (new-framing).** Полный проверяемый терм кластерного свойства (OS5): связная корреляция == gap_ratio^t, с конструктивным epsilon/N-затуханием (P4-форма) и отождествлением темпа спада с решёточной щелью масс.
> _Caveat:_ Содержание классично (OS5 / экспоненциальный спад из щели трансфер-матрицы). Ново: финитистская epsilon/N-подача без актуального предела + точная Q-арифметика. ЧЕСТНЫЕ границы: (1) числовое замыкание только при beta in {1,2}, общий случай условен (cluster_from_gap требует gap_ratio<1, t_0>0); (2) только нулевой порядок Бесселя M=0; (3) decay_rate=1-r — линеаризация -log r, не континуальная масса. НЕ доказательство щели масс Янга-Миллса (Clay) и НЕ континуальный предел.

---

## #431 - `src/gauge/CombinedTransfer3D.v` - score 2 (methods)

**Temporal x spatial transfer in 3+1D: combined gap = temporal gap + spatial enhancement >= 0**

- **Topic.** Builds the combined transfer eigenvalue M_j = t_j(beta) * s_j(beta_s,d_sp) on a small SU(2) lattice and proves the gap decomposes as gap_M0 + t_1*penalty, so spatial coupling can only ADD to the mass gap. Concrete d_sp=3 (3+1D) instance.
- **Role.** Composes the 1+1D character-basis gap (ExactMassGap: t0_M0/t1_M0/gap_M0) with the spatial-diagonal suppression (SpatialHamiltonian). Depends on SU2Characters, CharacterTransfer, ExactMassGap, ClebschGordan, SpatialHamiltonian. A dimension-lift layer of the gauge mass-gap programme; reused by the 3D continuum synthesis files.
- **Counts.** Qed 24 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: CauchyReal SeriesConvergence stdlib.Combinatorics; gauge.SU2Characters gauge.CharacterTransfer gauge.ExactMassGap gauge.ClebschGordan gauge.SpatialHamiltonian
- **E/R/R.** _Elements:_ конкретные рациональные собственные значения t_j(beta), пространственное подавление s_j, штраф penalty=1-s_j на малой SU(2)-решётке; d_sp=3. _Roles:_ temporal_gap (роль временного переноса) против spatial_enhancement (роль пространственной плакетки); combined_gap = их сумма; неотрицательность = роль-ограничение. _Rules:_ s_0=1 (основное не подавлено), s_1<1 (возбуждённое подавлено); gap = (t_0-t_1) + t_1*(1-s_1); оба слагаемых >= 0 при 0<=beta<=2, 0<=beta_s. _P4:_ Element-сторона: все величины — рациональные на КОНЕЧНОЙ решётке, щель вычислима в каждой точке beta. Это finite-actuality инстанс, НЕ континуумный предел; d_sp=3 — конкретный счёт, а не доказательство для произвольной размерности.
- **Classical counterpart.** Зеркалит решёточный transfer-matrix подход к щели масс Янга-Миллса (Wilson, Osterwalder-Seiler): щель = log(lambda_0/lambda_1) старшего и следующего собственных значений матрицы переноса, факторизация temporal x spatial — стандартный гамильтонов предел. НОВОЕ здесь лишь точная рациональная (Q) арифметика на конечной SU(2)-решётке и явное знаковое разложение; это НЕ доказательство Clay-щели и НЕ континуумный результат.
- **Tags.** gauge, mass-gap, SU2, transfer-matrix, 3plus1D, finite-lattice, P4, exact-Q
- **Notes.** Header 'STATUS: ~40 Qed' overstated — actual Qed count = 24 (29 named declarations, of which 6 are Definitions). 0 Admitted, 0 own axioms. Ends with Print Assumptions combined_transfer_3d_summary.

**Lemmas (29):**

| name | kind | role |
|---|---|---|
| `spatial_suppression` | Definition | s_j = 1 - beta_s*d_sp*spatial_diagonal j (подавление собственного значения j) |
| `suppression_0` | Lemma | s_0 = 1 — основное состояние не подавлено |
| `suppression_1` | Lemma | s_1 = 1 - beta_s*d_sp*(2/9) — явная форма первого возбуждённого |
| `spatial_penalty` | Definition | penalty = 1 - s_j (штраф подавления) |
| `penalty_eq` | Lemma | penalty = beta_s*d_sp*spatial_diagonal j |
| `penalty_0` | Lemma | penalty при j=0 равен 0 |
| `penalty_1_formula` | Lemma | penalty при j=1 = beta_s*d_sp*(2/9) |
| `penalty_nonneg` | Lemma | 0<=beta_s ⟹ penalty>=0 |
| `penalty_positive` | Lemma | 0<beta_s, d_sp>=1 ⟹ penalty при j=1 строго > 0 |
| `combined_eigenvalue` | Definition | M_j = transfer_eigenvalue j beta * s_j (временное x пространственное) |
| `combined_ground` | Theorem | M_0 = t0_M0 beta (основное не подавлено) |
| `combined_gap` | Definition | combined_gap = M_0 - M_1 |
| `combined_gap_decomposition` | Theorem | ★ gap = gap_M0 + t1_M0*penalty (ключевое разложение) |
| `temporal_term_nonneg` | Lemma | gap_M0>=0 на [0,2] (обёртка gap_M0_nonneg) |
| `spatial_term_nonneg` | Lemma | t1_M0*penalty >= 0 при условиях |
| `combined_gap_nonneg` | Theorem | ★ combined_gap >= 0 на [0,2], beta_s>=0 |
| `spatial_enhances_gap` | Theorem | ★ gap_M0 <= combined_gap (пространство только усиливает щель) |
| `combined_gap_positive_1` | Theorem | combined_gap > 0 при beta=1 |
| `combined_gap_positive_2` | Theorem | combined_gap > 0 при beta=2 |
| `gap_3plus1D` | Definition | combined_gap при d_sp=3 (физическая размерность 3+1) |
| `gap_3plus1D_positive_1` | Theorem | 3+1D щель > 0 при beta=1 |
| `gap_3plus1D_positive_2` | Theorem | 3+1D щель > 0 при beta=2 |
| `gap_3plus1D_decomposition` | Theorem | разложение щели в 3+1D |
| `penalty_3d` | Lemma | penalty при d_sp=3, j=1 = beta_s*(2/3) |
| `gap_3plus1D_formula` | Theorem | формула 3+1D щели (= decomposition) |
| `gap_3plus1D_penalty_value` | Lemma | значение штрафа в 3+1D (= penalty_3d) |
| `combined_gap_at_0` | Lemma | при d_sp=0 combined_gap = gap_M0 (нет пространства) |
| `gap_enhancement_nonneg` | Lemma | gap_M0 <= combined_gap (= spatial_enhances_gap) |
| `combined_transfer_3d_summary` | Theorem | сводка: неотрицательность, >=временной, положительность при beta=1,2 |

**Key lemmas (deep):**

- **`combined_gap_decomposition`** - Несущая лемма файла: щель M_0-M_1 алгебраически раскладывается на (t_0-t_1) + t_1*(1-s_1) = временная_щель + пространственное_усиление. Поскольку оба слагаемых неотрицательны на 0<=beta<=2 и beta_s>=0, отсюда механически следуют ВСЕ остальные положительности (nonneg, enhances, 3+1D). Содержательное наблюдение — знак: пространственное подавление возбуждённого состояния (s_1<1=s_0) может только увеличить щель, никогда не закрыть. Доказательство — чистое ring-разложение + Qmult_le_0_compat, не глубокая теорема. _(mass-gap, decomposition, dimension-lift, monotone)_
- **`spatial_enhances_gap`** - Физически нагруженный вывод: gap_M0(beta) <= combined_gap(beta,beta_s,d_sp). 'Включение пространственных плакеток не вредит щели масс'. Честно: это утверждение в рамках конкретной первопорядковой модели подавления s_j=1-beta_s*d_sp*C_j/(2j+1)^2 на МАЛОЙ решётке (j=0,1), а не общий результат теории Янга-Миллса; знак гарантирован выбором формы s_j. _(mass-gap, enhancement, finite-lattice)_

**Uniqueness - score 2 (methods).** Точное рациональное разложение комбинированной (временной x пространственной) щели переноса в 3+1D как суммы двух неотрицательных слагаемых, показывающее что пространственное подавление только усиливает щель.
> _Caveat:_ Конечнорешёточное вычисление SU(2), уровни j=0,1 только, первопорядковая модель подавления s_j; НЕ континуумный предел и НЕ доказательство Clay mass-gap. d_sp=3 — конкретный счёт. Знак усиления заложен в выбранную форму s_j. Шапка завышает: 'STATUS ~40 Qed' при фактических 24.

---

## #432 - `src/gauge/ConfinementCorrection.v` - score 3 (new-framing)

**No RG-compatible correction saves the gap; string-tension > 0 but gap = 0 at beta=8 paradox**

- **Topic.** Defines a confinement correction delta(k) added to the gap, an RG-compatibility halving recurrence, and proves no RG-compatible correction keeps the gap above any m>0 (the halving forces delta -> 0). Also exhibits the string-tension paradox: sigma>0 at beta=8 yet su2_mass_gap 8 = 0.
- **Role.** A negative/impossibility result on the SU(2) RG-flow mass-gap programme. Depends on TransferMatrix, SU2TransferMatrix, StrongCoupling, LargerLattice, GapMatching, ExactRGProcess, GapDecayRate (uses su2_gap_at_k, u1_gap_vanishes, su2_gap_upper, string_tension, su2_gap_at_8). Diagnoses why this lattice model does NOT yield a continuum gap.
- **Counts.** Qed 18 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs List Lia ZArith Lqa; ToS: CauchyReal SeriesConvergence; gauge.TransferMatrix gauge.SU2TransferMatrix gauge.StrongCoupling gauge.LargerLattice gauge.GapMatching gauge.ExactRGProcess gauge.GapDecayRate
- **E/R/R.** _Elements:_ поправка delta: nat->Q, модифицированная щель su2_gap_at_k + delta k, строковое натяжение string_tension; всё рационально на стадиях k. _Roles:_ preserves_gap (роль: держать щель выше m>0) против rg_compatible (роль: подчиняться half-рекуррентности RG); противоречие = роль-ограничение. _Rules:_ RG-совместимость: delta(k+1) = (gap(k)+delta(k))/2 - gap(k+1); su2_gap убывает как ~(1/2)^k к нулю на орбите ⟹ delta стягивается к 0; нельзя одновременно держать m>0. _P4:_ Element-сторона: на каждой КОНЕЧНОЙ стадии k щель положительна и рациональна (su2_gap_positive_all_k). Предел orbit (beta->8) — role-limit: щель ИСЧЕЗАЕТ, но недостижима ни на одной стадии. Парадокс sigma>0 & gap=0 при beta=8 = диагностика того, что МОДЕЛЬ неполна, а не доказательство конфайнмента.
- **Classical counterpart.** Касается решёточной картины конфайнмента: строковое натяжение (Wilson area law) и щель масс как два спутника конфайнмента, и идеи RG-улучшенного действия (Symanzik improvement). НОВОЕ — формализованный no-go: внутри ЭТОЙ Q-модели никакая RG-совместимая (halving-рекуррентная) поправка не восстанавливает щель, плюс явный парадокс sigma>0/gap=0 при beta=8. Это диагностика модели, НЕ опровержение/доказательство конфайнмента или Clay-щели.
- **Tags.** gauge, mass-gap, confinement, RG-flow, no-go, paradox, SU2, finite-lattice, exact-Q
- **Notes.** Header 'STATUS: ~24 Qed' overstated — actual Qed count = 19 (22 named declarations, of which 3 are Definitions). 0 Admitted, 0 own axioms. Honesty-relevant: file is itself a diagnostic of model incompleteness (tension>0 vs gap=0 at beta=8); does NOT claim a continuum gap.

**Lemmas (22):**

| name | kind | role |
|---|---|---|
| `modified_gap` | Definition | su2_gap_at_k beta k + delta k |
| `preserves_gap` | Definition | 0<m /\ forall k, m <= delta k |
| `modified_gap_lower` | Lemma | preserves_gap ⟹ m <= modified_gap |
| `preserves_gap_positive` | Lemma | preserves_gap ⟹ delta k > 0 |
| `modified_gap_at_0` | Lemma | modified_gap на стадии 0 |
| `rg_compatible` | Definition | halving-рекуррентность: delta(S k) = (gap(k)+delta(k))/2 - gap(S k) |
| `rg_compat_recurrence` | Lemma | переписанная форма рекуррентности delta |
| `rg_compat_delta_bound` | Lemma | при малой gap(k) delta стягивается: delta(S k) <= delta k/2 + m/8 |
| `delta_induction` | Lemma | ★ индукция: delta(k0+j) <= delta(k0)*(1/2)^j + m/4 |
| `delta_eventually_small` | Lemma | ★ существует N: delta(k0+N) < m (через Qpow_limit_zero) |
| `u1_gap_mono` | Lemma | U(1)-щель монотонно убывает: u1_gap(k+j) <= u1_gap(k) |
| `no_compatible_gap` | Theorem | ★ нет RG-совместимой поправки, сохраняющей щель m>0 |
| `correction_must_break_rg` | Theorem | сохраняющая щель поправка обязана нарушить RG |
| `correction_or_new_rg` | Theorem | структурно: либо менять поправку, либо RG (= no_compatible_gap) |
| `tension_at_8` | Lemma | string_tension 8 = 3/32 (vm-арифметика) |
| `tension_positive_at_8` | Lemma | 0 < string_tension 8 |
| `tension_gap_paradox` | Theorem | ★ парадокс: sigma>0 при beta=8, но su2_mass_gap 8 = 0 |
| `model_inconsistency` | Theorem | несогласованность модели в критической точке (= paradox) |
| `what_correction_proves` | Theorem | сводка: нет поправки + натяжение>0 + щель=0 |
| `three_mechanisms_missing` | Theorem | щель исчезает в пределе, но >0 на каждой стадии |
| `confinement_main` | Theorem | ★ главная сводка: нет поправки + парадокс + исчезновение по орбите |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`no_compatible_gap`** - Несущая теорема: ни одна RG-совместимая поправка delta не может удержать щель выше любого m>0. Доказательство содержательно: (1) находим стадию k0, где u1_gap < m/16; (2) тогда su2_gap < m/4 для всех последующих j (через su2_gap_upper и монотонность u1_gap); (3) half-рекуррентность RG заставляет delta вести себя как delta(k0)*(1/2)^j + m/4, что через Qpow_limit_zero падает ниже m — противоречие с preserves_gap. Это честный НЕГАТИВНЫЙ результат: данная модель НЕ спасается косметической поправкой, совместимой с RG-потоком. _(mass-gap, impossibility, RG-flow, no-go)_
- **`tension_gap_paradox`** - Диагностический гем: при beta=8 строковое натяжение sigma=3/32>0 (конфайнмент), НО su2_mass_gap 8 = 0. Классически конфайнмент (sigma>0) и щель масс (gap>0) идут вместе; здесь модель их рассогласовывает в критической точке. Файл честно подаёт это как 'model_inconsistency' — сигнал неполноты конкретной решёточной модели, а НЕ физический результат. Доказательство — vm_compute натяжения + цитирование su2_gap_at_8. _(confinement, paradox, string-tension, diagnostic)_

**Uniqueness - score 3 (new-framing).** Формализованный негативный результат + парадокс: в данной Q-решёточной SU(2)-модели никакая RG-совместимая поправка не сохраняет положительную щель (halving-поток стягивает delta к 0), и при beta=8 натяжение>0 при щели=0 — честная диагностика неполноты модели.
> _Caveat:_ Результат КОНДИЦИОНАЛЕН на конкретной модели su2_gap_at_k и определении RG-совместимости как half-рекуррентности; натяжение/щель из импортированных файлов. Это НЕ доказательство и НЕ опровержение конфайнмента или Clay mass-gap — диагностика. Шапка завышает: 'STATUS ~24 Qed' при фактических 19.

---

## #433 - `src/gauge/Continuum3DSynthesis.v` - score 1 (exposition)

**1D->2D->3D mass-gap synthesis: gaps positive in every dimension (lattice 15/16, continuum >= 1/18)**

- **Topic.** Pure consolidation theorem bundle gathering the dimension ladder: 1+1D K=2 gap=0 at beta=8 (wall) but K->inf gap>=1/8; 2+1D gap=3/4; 3+1D lattice gap=15/16; 3+1D continuum tensor gap>=1/18. The gap_formula 1-(1/4)^d_sp reproduces 0, 3/4, 15/16.
- **Role.** Capstone/aggregator over the gauge dimension files. 0 new content — it only conjoins results from TransferMatrix, ExactEigenvalues, GapBound, Gap2D, Gap3D, TensorGapBound into summary theorems. Reused as the headline 'all dimensions have a gap' statement of the lattice programme.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; gauge.TransferMatrix gauge.ExactEigenvalues gauge.GapBound gauge.Gap2D gauge.Gap3D gauge.TensorGapBound
- **E/R/R.** _Elements:_ конкретные рациональные значения щелей по размерностям: 0, 1/8, 3/4, 15/16, 1/18; целочисленный костяк 112<=135. _Roles:_ размерность d_sp (роль-ярус лестницы) ⟹ значение щели; gap_formula 1-(1/4)^d_sp = роль-генератор значений; положительность = роль-ограничение. _Rules:_ 1+1D K=2: стена (gap=0 при beta=8); K->inf: пробита (gap>=1/8, 135>112); каждая пространственная плакетка домножает; gap_formula d даёт 0,3/4,15/16. _P4:_ Element-сторона: каждое значение щели — точная рациональная константа, проверяемая lra/vm_compute на КОНЕЧНОЙ решётке. 'Continuum' здесь = K->inf оператор и tensor-предел через ПРОЦЕСС-последовательности (P4: процесс, не завершённый объект), а НЕ Clay-континуумный предел SU(2) Янга-Миллса.
- **Classical counterpart.** Зеркалит решёточную программу щели масс Янга-Миллса по размерностям (strong-coupling / transfer-matrix Wilson) и идею, что щель растёт при добавлении пространственных измерений. НОВОЕ — лишь сборка конкретных точных рациональных значений (3/4, 15/16, 1/18) и формулы 1-(1/4)^d_sp в одну сводку. Имя 'Continuum...Synthesis' АСПИРАЦИОННО: 'continuum' = K->inf/tensor процесс-предел, файл НЕ доказывает Clay Millennium mass gap.
- **Tags.** gauge, mass-gap, synthesis, dimension-ladder, SU2, finite-lattice, exposition, exact-Q
- **Notes.** Header 'STATUS: ~10 Qed' ~ actual Qed = 9 (all 9 named decls are Theorems incl. total_count marker; no Definitions). 0 Admitted, 0 own axioms. ASPIRATIONAL name: 'Continuum 3D Synthesis' / 'continuum story' — proves finite-lattice exact values + K->inf/tensor process lower bounds, NOT the Clay continuum YM mass gap. Over-branding flagged.

**Lemmas (9):**

| name | kind | role |
|---|---|---|
| `continuum_1d_gap` | Theorem | 1+1D: gap=0 при beta=8, char_poly(2/3)=0, (2/3)-(13/24)=1/8 |
| `continuum_2d_gap` | Theorem | 2+1D: щель>0 и = 3/4 |
| `continuum_3d_gap` | Theorem | 3+1D: решёточная (15/16) и тензорная (>=1/18) щели положительны |
| `all_gaps_positive` | Theorem | ★ во всех размерностях щель > 0 (1/8, 3/4, 15/16, 1/18) |
| `lattice_gap_hierarchy` | Theorem | 2+1D щель < 3+1D щель (растёт с размерностью) |
| `the_3d_continuum_story` | Theorem | ★ полная история: стена→пробой→2D→3D→gap_formula 0,3/4,15/16 |
| `what_we_proved` | Theorem | сводка ключевых чисел 15/16, 1/18, костяк 112<=135 |
| `continuum_3d_main` | Theorem | ★ главная сводка: все щели + собственные значения + 15/16 |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`the_3d_continuum_story`** - Гранд-сводка лестницы размерностей в одной конъюнкции: 1+1D стена (gap_M0=0 при beta=8, char_poly(2/3)=0) → пробита при K->inf → 2+1D щель>0 → 3+1D щель 15/16 → 3+1D континуум >=1/18, и замыкается формулой gap_formula d_sp = 1-(1/4)^d_sp, дающей ровно 0, 3/4, 15/16. Чистая агрегация (каждый конъюнкт — exact импортированной леммы); ценность — единая нарративная картина 'щель есть в каждой размерности'. Доказательство = серия split + exact. _(synthesis, dimension-ladder, mass-gap, capstone)_
- **`all_gaps_positive`** - Несущее наблюдение: положительность щели в 1+1D (>=1/8), 2+1D (3/4), 3+1D решётке (15/16), 3+1D континууме (>=1/18) — четыре конъюнкта, четыре exact. Это headline-утверждение программы, но строго оно — про КОНКРЕТНЫЕ рациональные нижние оценки на конечных решётках / в K->inf и tensor-процессах, НЕ про Clay-щель. _(mass-gap, positivity, aggregation)_

**Uniqueness - score 1 (exposition).** Единая сводка лестницы размерностей мщели масс: точные рациональные значения 0,1/8,3/4,15/16,1/18 и формула 1-(1/4)^d_sp, собранные в headline-теоремы 'щель>0 во всех размерностях'.
> _Caveat:_ 0 нового содержания — чистая агрегация импортированных лемм (exact-цепочки). 'Continuum' = процесс-предел K->inf/tensor, НЕ Clay-континуум; значения 15/16, 1/18 — конкретные конечнорешёточные/процессные оценки, НЕ доказательство Millennium mass gap. Шапка 'STATUS ~10 Qed' ≈ фактическим 9.

---

## #434 - `src/gauge/ContinuumCharacter.v` - score 2 (methods)

**RG flow + continuum limit in character basis: lattice/physical/enhanced gaps positive over Q**

- **Topic.** Casts RG flow and the continuum limit in the SU(2) character basis: strict eigenvalue ordering t_0>t_1 at beta=1,2, physical gap = gap*beta, a lattice-spacing model a=1/beta, d+1 dimensional enhanced gap = (1+d)*gap_M0, and gap positivity/rationality at every process level K.
- **Role.** RG/continuum-limit layer of the character-basis mass-gap thread. Depends on SU2Characters, CharacterTransfer, ExactMassGap (t0_M0/t1_M0/gap_M0, gap_at_beta_1/2, transfer_diagonal_structural). Sibling of ContinuumCovariance; supplies physical_gap and enhanced_gap reused downstream.
- **Counts.** Qed 24 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith List Lqa; ToS: CauchyReal SeriesConvergence stdlib.Combinatorics; gauge.SU2Characters gauge.CharacterTransfer gauge.ExactMassGap
- **E/R/R.** _Elements:_ рациональные собственные значения t_0,t_1, явные дроби щели 289/384 (beta=1), 1/24 (beta=2), физическая щель gap*beta, шаг решётки 1/beta, уровень K. _Roles:_ lattice_gap (роль на решётке) → physical_gap (роль в физ. единицах через *beta); enhanced_gap (роль в d+1 измерениях = (1+d)*база); порядок t_0>t_1 = роль-разделитель. _Rules:_ строгий порядок t_1<t_0 при beta=1,2; физ.щель = gap_M0*beta; a(beta)=1/beta убывает с beta (RG); enhanced_gap d = gap + d*gap = (1+d)*gap; на каждом уровне K щель рациональна и >0. _P4:_ Element-сторона: на каждом КОНЕЧНОМ beta/уровне K щель — точная дробь, проверяемая lia/lra. Континуумный предел beta->inf трактуется как ПРОЦЕСС (P4): проверяем положительность на каждом уровне, а не достигаем завершённый континуум. wall_breach 'structural' = диагональность переноса + порядок, НЕ Clay-результат.
- **Classical counterpart.** Зеркалит решёточный RG-поток SU(2) Янга-Миллса в характерном (Fourier-on-group) базисе: beta=1/(g^2 a^2), a->0 как continuum limit, щель в физ. единицах = (решёточная щель)/a, и enhancement щели пространственными плакетками. НОВОЕ — точная рациональная (Q) реализация на малой решётке и трактовка предела как процесса по уровням K. 'Continuum'/'wall breach' АСПИРАЦИОННЫ: НЕ доказательство Clay continuum YM mass gap; модель a=1/beta и enhanced_gap=(1+d)*gap — упрощения.
- **Tags.** gauge, mass-gap, RG-flow, character-basis, continuum-limit, SU2, finite-lattice, P4, exact-Q
- **Notes.** Header 'STATUS: ~35 Qed' overstated — actual Qed count = 24 (30 named declarations, of which 6 are Definitions). 0 Admitted, 0 own axioms. ASPIRATIONAL: 'continuum limit' treated as a per-level process (P4), not the Clay continuum; physical_gap/enhanced_gap are simplified models. Ends with Print Assumptions continuum_character_summary.

**Lemmas (30):**

| name | kind | role |
|---|---|---|
| `strict_ordering_beta_1` | Lemma | t1_M0 1 < t0_M0 1 (строгий порядок при beta=1) |
| `strict_ordering_beta_2` | Lemma | t1_M0 2 < t0_M0 2 |
| `gap_fraction_1` | Lemma | gap_M0 1 = 289/384 (= gap_at_beta_1) |
| `gap_fraction_2` | Lemma | gap_M0 2 = 1/24 |
| `gap_decreases_1_to_2` | Lemma | gap_M0 2 < gap_M0 1 (щель убывает с beta) |
| `eigenvalue_sum_formula_1` | Lemma | eigenvalue_sum 1 = 383/384 |
| `lattice_spacing` | Definition | a(beta) = 1/beta (модель шага решётки) |
| `spacing_positive` | Lemma | beta>0 ⟹ a(beta)>0 |
| `spacing_decreasing_example` | Lemma | a(2) < a(1) (RG: шаг убывает с beta) |
| `physical_gap` | Definition | physical_gap = gap_M0 beta * beta (физ. единицы) |
| `physical_gap_at_1` | Lemma | physical_gap 1 = 289/384 |
| `physical_gap_at_2` | Lemma | physical_gap 2 = 1/12 |
| `physical_gap_positive_1` | Lemma | 0 < physical_gap 1 |
| `physical_gap_positive_2` | Lemma | 0 < physical_gap 2 |
| `physical_gap_rational` | Lemma | physical_gap beta рациональна (тривиально, Q) |
| `dimension_factor` | Definition | d -> inject_Z d (число пространственных плакеток) |
| `dimension_factor_pos` | Lemma | d>=1 ⟹ dimension_factor d > 0 |
| `enhanced_gap` | Definition | enhanced_gap d beta = gap_M0 + d*gap_M0 |
| `enhanced_gap_ge_base` | Lemma | gap_M0 <= enhanced_gap d (усиление) |
| `enhanced_gap_nonneg` | Lemma | enhanced_gap d >= 0 |
| `enhanced_gap_2d` | Lemma | enhanced_gap 1 = 2*gap_M0 |
| `enhanced_gap_3d` | Lemma | enhanced_gap 2 = 3*gap_M0 |
| `enhanced_gap_4d` | Lemma | enhanced_gap 3 = 4*gap_M0 |
| `gap_at_level` | Definition | щель на уровне процесса K: gap_M0(S K) |
| `gap_level_0` | Lemma | 0 < gap_at_level 0 (beta=1) |
| `gap_level_1` | Lemma | 0 < gap_at_level 1 (beta=2) |
| `gap_level_rational` | Lemma | щель рациональна на каждом уровне K |
| `wall_breach_structural` | Definition | Prop: диагональность + порядок t_1<=t_0 + щель>0 при beta=1,2 |
| `wall_breach_verified` | Theorem | ★ wall_breach_structural доказан |
| `continuum_character_summary` | Theorem | ★ сводка: щель/физ.щель>0, enhanced>=0, рациональность, пробой стены |

**Key lemmas (deep):**

- **`wall_breach_verified`** - Несущая теорема файла: утверждает 'структурность' пробоя стены через три факта — (1) матрица переноса ДИАГОНАЛЬНА в характерном базисе (transfer_diagonal_structural), (2) собственные значения упорядочены t_1<=t_0 на [0,2], (3) щель gap_M0>0 при beta=1,2. Содержательная заявка: это TRUE SU(2)/TRUE Wilson, а не упрощённая модель, и щель t_0-t_1 точна. Честно: 'structural' относится к диагональности+порядку на конкретных точках beta, а не к доказательству щели в континуумном пределе. Доказательство = split + exact импортированных лемм. _(mass-gap, character-basis, wall-breach, diagonal)_
- **`physical_gap_at_1`** - Представитель класса точных рациональных вычислений: physical_gap(1) = gap_M0(1)*1 = 289/384 — переход 'решёточная щель -> физическая щель' умножением на beta, всё точно над Q. enhanced_gap_2d/3d/4d аналогично дают (1+d)-кратное усиление. Ценность — демонстрация, что модель RG (a=1/beta, gap*beta) держит положительность; это методическая аккуратность над Q, не новая физика. _(physical-gap, RG, exact-Q)_

**Uniqueness - score 2 (methods).** Характерно-базисная формализация RG-потока и континуумного предела над Q: строгий порядок собственных значений, физическая щель gap*beta, (1+d)-кратное размерное усиление, положительность/рациональность щели на каждом процесс-уровне K.
> _Caveat:_ Конечнорешёточная SU(2), уровни j=0,1; модели a=1/beta и enhanced_gap=(1+d)*gap_M0 — упрощения; 'wall_breach_structural' = диагональность+порядок в точках beta=1,2, НЕ доказательство щели в континууме. НЕ Clay mass gap. Шапка завышает: 'STATUS ~35 Qed' при фактических 24.

---

## #435 - `src/gauge/ContinuumCovariance.v` - score 3 (new-framing)

**OS3 upgraded hypercubic -> SO(4): anisotropy ~ 1/beta -> 0 under RG, OS1-OS5 in the continuum**

- **Topic.** Argues OS3 (Euclidean covariance) lifts from hypercubic to full SO(4): SO(4) violation = anisotropy = 1/beta, decreasing under RG and < 1/40 once beta>=42; then restates OS1-OS5 as holding in the continuum (exact for OS1,2,4,5, approximate-with-error->0 for OS3).
- **Role.** Osterwalder-Schrader axioms layer of the gauge continuum programme. Depends on CharacterTransfer, ExactMassGap, GapRatio, LatticeRG, ReflectionPositivity, IrrelevantOperators, RGContraction, UniversalityClass, LatticeOS3_Covariance (uses anisotropy, beta_after_n_steps, os3_on_lattice, gap_ratio, t0_M0, b0_approx). Sibling of ContinuumCharacter.
- **Counts.** Qed 22 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: CauchyReal SeriesConvergence; gauge.CharacterTransfer gauge.ExactMassGap gauge.GapRatio gauge.LatticeRG gauge.ReflectionPositivity gauge.IrrelevantOperators gauge.RGContraction gauge.UniversalityClass gauge.LatticeOS3_Covariance
- **E/R/R.** _Elements:_ рациональная мера нарушения SO(4) = anisotropy beta = 1/beta; beta_after_n_steps; конкретные пороги 42<=beta ⟹ <1/40; OS-свидетели (bessel I0=1, gap_ratio<1, t0>0, gap>0). _Roles:_ so4_violation (роль: измерять отклонение от SO(4)) убывает под RG; каждая OS-аксиома = роль-условие конструктивной QFT; неподвижная точка = роль-предел. _Rules:_ so4_violation=anisotropy>0 и строго убывает с beta; на каждом RG-шаге уменьшается; при beta>=42 < 1/40; OS1,2,4,5 точны на каждой стадии, OS3 — приближённа с ошибкой->0. _P4:_ Element-сторона: на каждой КОНЕЧНОЙ стадии beta_after_n_steps анизотропия — точная рациональная >0 (SO(4) НЕ восстановлена ни на одной стадии); SO(4) — role-limit неподвижной точки. P4-чтение: процесс решёточных теорий ЕСТЬ континуум; OS3 достигается лишь в пределе, число шагов конечно для любого eps.
- **Classical counterpart.** Зеркалит реконструкцию Остервальдера-Шрадера (OS1-OS5 ⟹ Уайтмановская QFT) и восстановление вращательной/Lorentz-симметрии в континуумном пределе решёточной теории (hypercubic -> SO(4)/SO(3,1)), где артефакты ~ a^2 ~ 1/beta. НОВОЕ — рациональная (Q) модель anisotropy=1/beta с явными порогами и P4-трактовка 'процесс решёток = континуум'. КРИТИЧНО: имена OS1-OS5/SO(4) АСПИРАЦИОННЫ — файл проверяет ПО ОДНОМУ свидетелю на аксиому, НЕ строит континуумную меру и НЕ доказывает полную OS-реконструкцию или Clay YM существование.
- **Tags.** gauge, OS3, SO4, osterwalder-schrader, RG-flow, continuum-limit, covariance, SU2, P4, over-branding, exact-Q
- **Notes.** Header 'STATUS: ~35 Qed' overstated — actual Qed count = 22 (24 named declarations, of which 2 are Definitions). 0 Admitted, 0 own axioms. ASPIRATIONAL: OS1-OS5 'in the continuum' and SO(4) 'restoration' are each ONE witness, not a full OS-axiom verification or continuum measure construction; NOT the Clay YM existence/mass-gap. Over-branding flagged.

**Lemmas (24):**

| name | kind | role |
|---|---|---|
| `so4_violation` | Definition | so4_violation beta = anisotropy beta (= 1/beta) |
| `so4_violation_positive` | Lemma | beta>0 ⟹ so4_violation>0 (SO(4) нарушена на стадии) |
| `so4_violation_decreasing` | Lemma | b1<b2 ⟹ so4_violation b2 < so4_violation b1 |
| `so4_violation_at_step` | Theorem | нарушение>0 на каждом RG-шаге n |
| `so4_violation_decreases` | Theorem | ★ нарушение строго убывает на каждом RG-шаге |
| `so4_restored_at_fixed_point` | Theorem | ★ beta>=42 ⟹ so4_violation < 1/40 (восстановление в пределе) |
| `isotropic_is_so4` | Theorem | изотропная часть SO(4)-инвариантна (= os3_on_lattice) |
| `continuum_os3_so4` | Theorem | континуумный коррелятор SO(4)-инвариантен (порог 42) |
| `lattice_os3_holds` | Theorem | решёточная OS3 держится (os3_on_lattice) |
| `continuum_os1` | Theorem | OS1 аналитичность: bessel_partial 0 1 0 = 1 |
| `continuum_os2` | Theorem | OS2 регулярность: gap_ratio 1 < 1 |
| `continuum_os3` | Theorem | OS3 ковариантность: so4_violation убывает (= decreases) |
| `continuum_os4` | Theorem | OS4 рефлексионная позитивность: 0 < t0_M0 1 |
| `continuum_os5` | Theorem | OS5 кластер: gap_M0 1>0 и gap_M0 2>0 |
| `all_os_in_continuum` | Theorem | ★ все пять OS1-OS5 держатся в континууме |
| `steps_to_so4` | Definition | число RG-шагов до eps-SO(4): (1/eps-beta0)/(b0*beta0^2) |
| `steps_to_so4_well_defined` | Lemma | знаменатель b0*beta0^2 > 0 |
| `finite_steps_to_so4` | Theorem | конечное число шагов для любой точности (= well_defined) |
| `computable_so4_restoration` | Theorem | восстановление SO(4) вычислимо (порог 42) |
| `so4_restoration_rate` | Theorem | скорость: нарушение убывает на каждом шаге (O(1/n)) |
| `os_process` | Theorem | OS как процесс: os3_on_lattice /\ gap_M0 1>0 |
| `p4_all_os` | Theorem | ★ под P4: процесс решёток ЕСТЬ континуум (порог 42) |
| `continuum_mass_gap_positive` | Theorem | щель масс>0 в континууме (gap_M0 1,2 > 0) |
| `continuum_covariance_summary` | Theorem | ★ сводка: SO(4)<1/40, t0>0, щель>0, решёточная OS3 |

**Key lemmas (deep):**

- **`so4_restored_at_fixed_point`** - Несущая теорема: so4_violation(beta) = anisotropy(beta) < 1/40 как только beta>=42. Это количественная форма 'восстановления вращательной симметрии в континуумном пределе' — решёточные артефакты (гиперкубическая анизотропия) убывают как 1/beta, и под RG beta растёт, так что в неподвижной точке SO(4) восстанавливается. Честно: это КОНКРЕТНАЯ оценка (порог 42, бюджет 1/40) для рациональной модели anisotropy=1/beta, а НЕ доказательство восстановления SO(4) для реальной решёточной калибровочной теории. Доказательство = exact anisotropy_negligible. _(OS3, SO4, RG-flow, continuum-limit)_
- **`all_os_in_continuum`** - Заявочная теорема: все пять аксиом Остервальдера-Шрадера (OS1 аналитичность, OS2 регулярность, OS3 ковариантность, OS4 рефлексионная позитивность, OS5 кластер/щель) собраны в одну конъюнкцию как держащиеся 'в континууме'. Серьёзное предупреждение по честности: каждый конъюнкт — это ОДНО конкретное свидетельство (OS1 = bessel I0(beta=1)=1; OS2 = gap_ratio 1<1; OS3 = убывание анизотропии; OS4 = t0_M0 1>0; OS5 = gap при beta=1,2>0), а НЕ полная проверка соответствующей OS-аксиомы для континуумной меры. Это иллюстративная сборка под именем OS, не реконструкция Уайтмановской теории. Чистая агрегация (split+exact). _(osterwalder-schrader, constructive-qft, aggregation, over-branding)_

**Uniqueness - score 3 (new-framing).** Количественная Q-модель восстановления SO(4) из гиперкубической решётки (анизотропия 1/beta -> 0 под RG, явные пороги, конечное число шагов на любой eps) + P4-обрамление 'процесс решёточных теорий ЕСТЬ континуум', с OS1-OS5 как процесс-условиями.
> _Caveat:_ Каждая 'OS-аксиома в континууме' = ОДНО конкретное свидетельство (bessel, gap_ratio, t0>0, gap>0, убывание анизотропии), НЕ полная проверка OS-аксиомы для континуумной меры. anisotropy=1/beta и пороги 42/(1/40) — конкретная упрощённая модель. НЕ доказательство OS-реконструкции, восстановления SO(4) для настоящей LGT или Clay YM. Шапка завышает: 'STATUS ~35 Qed' при фактических 22.

---

## #436 - `src/gauge/ContinuumGap.v` - score 2 (methods)

**Physical mass gap m=(1-r)/a survives RG: positive, finite, RG-approx-invariant over Q**

- **Topic.** Defines the first-order physical mass m = (1-r)/a (r = gap ratio t1/t0, a = lattice spacing) and proves it positive, finite, bounded between m/2 and m under one RG step (r->r^2, a->2a), positive after any number of steps, and enhanced by spatial coupling in 3+1D.
- **Role.** Mid-tier consumer of the gauge RG/gap stack. Imports gauge.GapRatio, LatticeRG, CharacterTransfer, ExactMassGap, CombinedTransfer3D, ReflectionPositivity; reused by the higher continuum synthesis files as the 'gap survives the limit' building block.
- **Counts.** Qed 22 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: CauchyReal; ToS: SeriesConvergence; ToS: stdlib.Combinatorics; gauge.SU2Characters; gauge.CharacterTransfer; gauge.ExactMassGap; gauge.ClebschGordan; gauge.CombinedTransfer3D; gauge.GapRatio; gauge.LatticeRG; gauge.ReflectionPositivity
- **E/R/R.** _Elements:_ конкретные рациональные величины: отношение щели r = gap_ratio beta, шаг решётки a, масса m = (1-r)/a; числовые значения 47/336, 11/12, 289/336, 1/12. _Roles:_ physical_mass r a = роль «физическая масса при разрешении a»; RG-шаг (r->r^2, a->2a) = роль огрубления; границы m/2 < m' < m = роли коридора инвариантности. _Rules:_ m'/m = (1+r)/2 (точное RG-соотношение, field); положительность через Qlt_shift_div_l; коридор m/2..m из (1+r)/2 в (1/2,1) при r in (0,1). _P4:_ масса — наблюдаемая (нетерминирующий континуумный предел −log r/a), а её рациональное приближение (1-r)/a — Element на каждом конечном разрешении; «инвариантность» здесь = ограниченность приближения коридором, а НЕ точная RG-инвариантность точного логарифма.
- **Classical counterpart.** Mirrors the lattice-gauge expectation that a mass gap is RG-stable and that adding spatial dimensions does not destroy it (Wilson, Osterwalder-Seiler). What differs: everything is the FIRST-ORDER rational surrogate m=(1-r)/a on a fixed finite lattice with exact Q arithmetic; the genuine continuum object is -log(r)/a (only commented), and the 3+1D claim is a conditional inequality on a small lattice, not a continuum theorem.
- **Tags.** gauge, mass-gap, rg, continuum-limit, exact-Q, 1+1D, 3+1D, conditional, header-drift
- **Notes.** Qed drift: STATUS header says '~40 Qed', actual count 22. 0 Admitted, 0 axioms. Over-branding: header comment asserts the mass gap is 'EXACTLY invariant' / continuum limit 'TRIVIAL', but the Coq content proves only the bounded (1+r)/2 corridor of the rational approximation.

**Lemmas (25):**

| name | kind | role |
|---|---|---|
| `physical_mass` | Definition | масса первого порядка m = (1-r)/a |
| `physical_mass_positive` | Theorem | r<1, a>0 => 0 < m (ядро положительности) |
| `physical_mass_beta_1` | Lemma | m(gap_ratio 1, a) == (1 - 47/336)/a |
| `physical_mass_beta_2` | Lemma | m(gap_ratio 2, a) == (1 - 11/12)/a |
| `mass_positive_beta_1` | Theorem | масса положительна при beta=1 |
| `mass_positive_beta_2` | Theorem | масса положительна при beta=2 |
| `mass_from_gap` | Definition | альтернативная форма m = gap_M0/(t0_M0*a) |
| `mass_from_gap_eq` | Theorem | mass_from_gap == physical_mass (gap_ratio) (эквивалентность форм) |
| `mass_from_gap_pos_1` | Theorem | mass_from_gap положительна при beta=1 |
| `mass_rg_relation` | Theorem | ★ точное RG: m(r^2,2a) == (1+r)/2 * m(r,a) |
| `mass_after_n_rg` | Definition | масса после n RG-шагов через rg_iterate/lattice_spacing |
| `mass_after_0` | Lemma | 0 шагов = исходная масса |
| `mass_rg_lower_bound` | Theorem | ★ нижняя граница коридора: (1/2)m < m' (масса не падает ниже половины) |
| `mass_rg_upper_bound` | Theorem | верхняя граница коридора: m' < m |
| `mass_positive_all_rg` | Theorem | ★ масса > 0 после любого числа RG-шагов |
| `mass_lower_bound_1` | Theorem | 289/336 / a <= m при beta=1 |
| `mass_lower_bound_2` | Theorem | 1/12 / a <= m при beta=2 |
| `mass_finite` | Theorem | m < 1/a (конечность при конечном шаге) |
| `mass_at_unit_spacing_1` | Lemma | m(gap_ratio 1, 1) == 289/336 |
| `mass_at_unit_spacing_2` | Lemma | m(gap_ratio 2, 1) == 1/12 |
| `mass_3d_at_least_1d` | Theorem | ★ 3+1D масса >= 1+1D (пространственная связь увеличивает щель), при условии beta_s*d*(2/9)<1 |
| `continuum_mass_gap_3d` | Theorem | 3+1D континуумная масса положительна при условии beta_s*3*(2/9)<1 |
| `continuum_mass_gap_exists` | Theorem | конъюнкция: положительность + RG-коридор + сохранение + 3D-усиление |
| `p4_mass_gap_statement` | Theorem | переименование mass_rg_relation как «P4-утверждение о масштабах» |
| `continuum_gap_summary` | Theorem | итоговая конъюнкция (положительна/конечна/3D>0/RG сохраняет) |

**Key lemmas (deep):**

- **`mass_rg_relation`** - Несущая лемма файла: одношаговое RG-соотношение m(r^2, 2a) = (1+r)/2 * m(r,a), доказанное чистым field над Q. Из множителя (1+r)/2, лежащего в (1/2,1) при r in (0,1), сразу следуют и нижняя (mass_rg_lower_bound), и верхняя (mass_rg_upper_bound) границы коридора. ВАЖНО для честности: это RG точного приближения (1-r)/a, а не точного −log r/a; заголовок файла обещает 'EXACT invariance', но доказана лишь ограниченность приближения коридором m/2..m — точная инвариантность логарифма НЕ формализована (только в комментарии). _(rg, mass-gap, exact-Q, approximation)_
- **`mass_3d_at_least_1d`** - Содержательная физика файла: при включении d пространственных плакетов комбинированное отношение R = r*s1 <= r, откуда (1-R)/a >= (1-r)/a — пространственная связь УВЕЛИЧИВАЕТ массовую щель. Доказано через combined_ratio_less_than_temporal при явном условии beta_s*d*(2/9)<1. Это конкретное Q-неравенство на малой решётке, а не утверждение о настоящем 3+1D континууме; условие на beta_s — честное ограничение области. _(3d, spatial-coupling, conditional)_

**Uniqueness - score 2 (methods).** Exact-Q formalization of 'the first-order mass surrogate is positive, finite and trapped in an [m/2, m] RG corridor, and grows under spatial coupling' for a 1+1D->3+1D quadratic-action lattice.
> _Caveat:_ Finite-lattice, first-order-surrogate computation — NOT a continuum or Millennium proof. Header claims '~40 Qed' and 'EXACT invariance'; actual 22 Qed, and only the (1+r)/2 RG corridor of the APPROXIMATION is proved (exact -log r/a invariance is merely commented). 3+1D positivity is conditional on beta_s*3*(2/9)<1. Specific to gap_ratio/SU(2)-corrected quadratic Wilson action.

---

## #437 - `src/gauge/ContinuumGap2D.v` - score 3 (new-framing)

**2+1D continuum synthesis: dimension ladder 1+1D K=2 -> K->inf -> 2+1D K=2 -> 2+1D continuum**

- **Topic.** Assembles the 2+1D continuum story from imported facts: 1+1D gap vanishes at beta=8 (K=2 wall), 1+1D continuum gap >= 1/8 (rank-3 operator), 2+1D K=2 gap = 3/4, and the 2+1D continuum two-body operator ground state 13/15 with trace 1/3 and anti-block trace 22/105.
- **Role.** Top-level synthesis/capstone of the 2+1D thread; pure re-export and bundling (every step is `exact <imported lemma>`). Imports gauge.ContinuumMatrix2D, ContinuumOperator, ExactEigenvalues, GapBound, Gap2D, Synthesis2D, ExtendedAction, EigenAnalysis2D, TransferMatrix.
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; gauge.TransferMatrix; gauge.ContinuumOperator; gauge.ExactEigenvalues; gauge.GapBound; gauge.Gap2D; gauge.Synthesis2D; gauge.ExtendedAction; gauge.ContinuumMatrix2D; gauge.EigenAnalysis2D
- **E/R/R.** _Elements:_ числовые величины щелей и следов: 0 (стена K=2), 1/8, 3/4, 13/15, 1/3, 22/105, 13/105; ступени лестницы размерности. _Roles:_ каждая dim_ladder_stepN = роль «ступень лестницы размерности»; n_entry 0 0 0 0 = роль «основное состояние»; anti_trace/n_trace = роли блочных следов. _Rules:_ конъюнкции импортированных равенств/неравенств, собранные через split + exact; вычислений нет — только переупаковка. _P4:_ лестница размерности = последовательность конечных Element-фактов (каждый на конкретной K и размерности); полный 2+1D K->inf оператор и 3+1D остаются нетерминирующими/невычисленными — явно помечены как «what_remains» (грань P4/арена).
- **Classical counterpart.** Mirrors the strong-coupling-to-continuum narrative of lattice gauge theory and the observation that finite-K discretization artifacts (a vanishing gap) disappear at larger K. What differs: it is a bundle of exact rational facts for a quadratic Wilson action in 1+1D and 2+1D only; the genuine continuum spectral problems (2+1D K->inf, all of 3+1D, full SU(2) Haar action) are explicitly listed as open in-file.
- **Tags.** gauge, mass-gap, 2+1D, dimension-ladder, synthesis, continuum-limit, honesty
- **Notes.** Qed drift: header '~15 Qed', actual 13 (header uses '~', minor). 0 Admitted, 0 axioms. Over-branding watch: 'CONTINUUM GAP 2D' / star-marked 'main' theorems are aspirational, but the file's own 'what_remains' and 'Distance to Millennium' comments honestly scope it to 1+1D/2+1D quadratic action.

**Lemmas (13):**

| name | kind | role |
|---|---|---|
| `dim_ladder_step1` | Theorem | 1+1D K=2: mass_gap_2x2 8 == 0 (стена) |
| `dim_ladder_step2` | Theorem | 1+1D K->inf: char_poly(2/3)=0 и q(13/24)>0 (rank-3, щель>=1/8) |
| `dim_ladder_step3` | Theorem | 2+1D K=2: mass_gap_2d_at_8 == 3/4 и >0 |
| `dim_ladder_step4` | Theorem | 2+1D континуум: n_entry 0000 == 13/15, >1/9, trace 1/3 >0 |
| `enhancement_factor` | Theorem | усиление основного состояния: 13/15 == (39/5)*(1/9) |
| `lattice_exceeds_continuum_1d` | Theorem | 1/8 < mass_gap_2d_at_8 (2+1D решётка превосходит 1+1D континуум) |
| `both_2d_gaps_positive` | Theorem | обе 2+1D-щели положительны |
| `block_traces` | Theorem | anti_trace 22/105, sym 13/105, anti>0 |
| `anti_dominates_sym` | Theorem | sym < anti (антисимметричный сектор доминирует) |
| `the_2d_continuum_story` | Theorem | ★ полная история 2+1D одной конъюнкцией (baseline+K=2+континуум+усиление) |
| `what_remains` | Theorem | честный маркер: K=2 щель=0, но 2+1D щель>0 (что преодолено) |
| `continuum_gap_2d_main` | Theorem | ★ главная теорема файла: размерность+оператор+блоки+усиление |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`the_2d_continuum_story`** - Капстоун-конъюнкция всего 2+1D потока: одной теоремой собраны 1+1D-стена (gap=0 при beta=8), 1+1D rank-3 свидетель щели, 2+1D K=2 положительность, континуумные значения 13/15, 1/3, 22/105 и усиление 1/9<13/15. Чистая консолидация (каждый конъюнкт — exact импортированной леммы), 0 нового содержания; ценность — единая витрина «лестницы размерности». Честно: это про 1+1D/2+1D квадратичное действие, НЕ про 3+1D SU(2) Clay-задачу. _(synthesis, dimension-ladder, capstone, 2+1D)_
- **`what_remains`** - Встроенный маркер честности: контраст 'K=2 щель = 0' против '2+1D щель > 0' буквально фиксирует, что стена была артефактом K=2-дискретизации, а не физикой. Сопровождающий комментарий явно перечисляет 'Distance to Millennium': 2+1D K->inf, 3+1D, 3+1D SU(2), 3+1D континуум — всё отмечено как НЕ сделанное. Образцовая внутрифайловая честность на фоне аспирационного слова 'continuum'. _(honesty, millennium-distance, remaining)_

**Uniqueness - score 3 (new-framing).** A 'dimension ladder' framing (1+1D K=2 -> K->inf -> 2+1D K=2 -> 2+1D continuum) that re-casts a chain of exact finite-lattice rational facts as a single graded story with an explicit honesty boundary.
> _Caveat:_ Pure consolidation, 0 new content; every step is `exact` of an imported lemma. Strictly 1+1D / 2+1D quadratic-action results — NOT a 3+1D or Millennium proof, as the file itself states under 'what_remains'/'Distance to Millennium'. Header '~15 Qed' vs actual 13 (minor, header is approximate).

---

## #438 - `src/gauge/ContinuumMatrix2D.v` - score 2 (methods)

**9x9 two-body 2+1D continuum operator N: 9 diagonal entries, swap symmetry, trace 1/3, ground state 13/15**

- **Topic.** Defines the two-body continuum matrix element N[(a,b),(c,d)] = E[a][c]E[b][d] - 4E[a][c+2]E[b][d] + 8E[a][c+1]E[b][d+1] - 4E[a][c]E[b][d+2] (product kernel k2 = k(x1,y1)k(x2,y2), k = 1-4(x-y)^2) and computes its 9 diagonal entries, swap symmetry, row traces, total trace 1/3, and ground-state enhancement to 13/15.
- **Role.** Provides the concrete 2+1D two-body operator consumed by ContinuumGap2D and EigenAnalysis2D. Imports gauge.ContinuumOperator (for e_entry) and gauge.ExtendedAction.
- **Counts.** Qed 21 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; gauge.ContinuumOperator; gauge.ExtendedAction
- **E/R/R.** _Elements:_ матричные элементы n_entry a b c d над Q; диагональные значения 13/15, -16/9, 8/9, 224/45, -112/45, 56/45; следы строк -1/45, 32/45, -16/45. _Roles:_ n_entry = роль «двухчастичный континуумный матричный элемент»; n_trace = роль полного следа; swap-симметрия = роль обмена координат x1<->x2. _Rules:_ мастер-формула с произведением ядер k2 = k(x1,y1)k(x2,y2); диагонали через unfold+simpl+lia; swap-симметрия n b a c d == n a b d c через ring. _P4:_ континуумный двухчастичный оператор реифицирован в КОНЕЧНУЮ 9x9 рациональную матрицу (моменты до степени 2 => ядро degree-2 => конечный ранг): полный (бесконечномерный) интегральный оператор обрезан до Element-объекта 3x3 x 3x3.
- **Classical counterpart.** Mirrors the matrix element of a two-body operator built from a separable (product) kernel and the boson exchange symmetry of a symmetric two-particle Hamiltonian. What differs: the operator is reduced to an exact 9x9 RATIONAL matrix (degree-2 kernel => finite rank), all entries and the trace are machine-verified over Q; there is no continuum spectral statement here, only the finite matrix and its trace/symmetry.
- **Tags.** gauge, mass-gap, 2+1D, operator, finite-rank, exact-Q, swap-symmetry, header-drift
- **Notes.** Qed drift: header '~27 Qed', actual 22. 0 Admitted, 0 axioms. e_entry is imported from gauge.ContinuumOperator (not defined here).

**Lemmas (27):**

| name | kind | role |
|---|---|---|
| `n_entry` | Definition | ★ мастер-формула двухчастичного элемента N[(a,b),(c,d)] |
| `n_diag_00_00` | Lemma | основное состояние N[0000] == 13/15 |
| `n_diag_01_01` | Lemma | N[0101] == -16/9 |
| `n_diag_02_02` | Lemma | N[0202] == 8/9 |
| `n_diag_10_10` | Lemma | N[1010] == -16/9 |
| `n_diag_11_11` | Lemma | N[1111] == 224/45 |
| `n_diag_12_12` | Lemma | N[1212] == -112/45 |
| `n_diag_20_20` | Lemma | N[2020] == 8/9 |
| `n_diag_21_21` | Lemma | N[2121] == -112/45 |
| `n_diag_22_22` | Lemma | N[2222] == 56/45 |
| `n_swap_symmetry` | Theorem | ★ обмен координат: n b a c d == n a b d c (через ring) |
| `n_diag_symmetry_01_10` | Corollary | N[0101]==N[1010] (инстанс swap) |
| `n_diag_symmetry_02_20` | Corollary | N[0202]==N[2020] (инстанс swap) |
| `n_diag_symmetry_12_21` | Corollary | N[1212]==N[2121] (инстанс swap) |
| `n_trace_row0` | Definition | след строки 0 = N0000+N0101+N0202 |
| `n_trace_row1` | Definition | след строки 1 |
| `n_trace_row2` | Definition | след строки 2 |
| `n_trace_row0_value` | Lemma | row0 == -1/45 |
| `n_trace_row1_value` | Lemma | row1 == 32/45 |
| `n_trace_row2_value` | Lemma | row2 == -16/45 |
| `n_trace` | Definition | полный след = row0+row1+row2 |
| `n_trace_value` | Theorem | ★ Trace(N) == 1/3 |
| `trace_reduction` | Theorem | след уменьшен: 0 < n_trace < 1 (от 1 без связи) |
| `ground_state_enhanced` | Theorem | 1/9 < N[0000] (усиление основного состояния) |
| `enhancement_ratio` | Theorem | N[0000] == (39/5)*(1/9) = 7.8x |
| `continuum_matrix_2d_main` | Theorem | ★ главная: основное+след+усиление+положительность |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`n_entry`** - Несущее определение: двухчастичный континуумный матричный элемент как тензорная свёртка одночастичных элементов e_entry с фиксированными коэффициентами 1, -4, 8, -4 — это product-ядро k2(x1,x2,y1,y2)=k(x1,y1)k(x2,y2) с k=1-4(x-y)^2, действующее на мономы. Ключ: поскольку k имеет степень 2 по каждой переменной, оператор конечного ранга и сворачивается в КОНЕЧНУЮ 9x9 рациональную матрицу — финитизация бесконечномерного интегрального оператора в Element-объект. Все 9 диагональных значений — vm/simpl+lia вычисления. _(operator, two-body, finite-rank, tensor-kernel)_
- **`n_swap_symmetry`** - Единственное содержательное структурное (не чисто числовое) утверждение файла: при обмене пространственных координат x1<->x2 матрица удовлетворяет n_entry b a c d == n_entry a b d c, доказано одним ring — следствие product-структуры ядра. Из него три диагональные пары-следствия. Это симметрия Element-объекта, отражающая бозонную перестановочную симметрию двух частиц; классична по содержанию, ценна как машинно-проверенное свойство конкретной матрицы. _(swap-symmetry, permutation, ring)_

**Uniqueness - score 2 (methods).** Exact-Q construction of the 2+1D two-body continuum operator as a finite 9x9 rational matrix with all diagonal entries, boson swap symmetry, and trace 1/3 machine-verified.
> _Caveat:_ Finite rational-matrix computation, not a continuum spectral proof. The 13/15 'enhancement' and 1/3 trace are exact arithmetic facts about a specific quadratic-action 2+1D model, not Millennium content. Header '~27 Qed' vs actual 22 Qed.

---

## #439 - `src/gauge/ContinuumOperator.v` - score 3 (new-framing)

**Rank-3 reduction of the K->inf transfer operator: M = A*H3 on span{1,x,x^2}, trace 1**

- **Topic.** Reduces the K->infinity transfer operator T on L^2[0,1] with degree-2 kernel k(x,y)=1-4(x-y)^2 to a 3x3 rational matrix M = A*H3, where A=[[1,0,-4],[0,8,0],[-4,0,0]] (kernel coefficients) and H3 is the 3x3 Hilbert (moment) matrix; computes all 9 entries of M and proves Trace(M) = 1.
- **Role.** Foundational rank-3 reduction reused across the continuum thread: supplies moment/hilbert/kernel_coeff and cont_entry to ContinuumGap2D, ContinuumMatrix2D (e_entry), ContinuumSynthesis, ExactEigenvalues, GapBound. Self-contained (only Stdlib imports).
- **Counts.** Qed 23 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa
- **E/R/R.** _Elements:_ моменты 1, 1/2, 1/3, 1/4, 1/5; матрица Гильберта H3; коэффициенты ядра A; элементы M: -1/3, -1/2, -7/15, 4, 8/3, 2, -4, -2, -4/3. _Roles:_ moment n = роль «n-й момент монома на [0,1]»; hilbert_entry = роль матрицы моментов; kernel_coeff_entry = роль разложения ядра; cont_entry = роль матричного элемента редуцированного оператора M. _Rules:_ интегралы int x^n = 1/(n+1) кодированы как match; M = A*H3 через mat3_mul_entry; все элементы и след через unfold+simpl+lia. _P4:_ ключ финитизации цикла: ядро степени 2 => Image(T) ⊆ span{1,x,x^2} => бесконечномерный интегральный оператор T (нетерминирующий континуумный объект) сводится к КОНЕЧНОЙ 3x3 рациональной матрице — точная Element-редукция, делающая спектр вычислимым над Q.
- **Classical counterpart.** Mirrors the classical fact that an integral operator with a degenerate (finite-rank, here degree-2 polynomial) kernel reduces to a finite matrix, plus the Hilbert matrix H_n = (1/(i+j+1)) of moment integrals. What differs: the whole reduction is carried out as exact Q arithmetic on a 3x3 matrix M = A*H3; 'rank <= 3' / 'rank = 3' are restated as trace=1 and three diagonal values rather than proved as genuine rank statements (det A != 0 is only commented).
- **Tags.** gauge, mass-gap, continuum-limit, rank-reduction, hilbert-matrix, integral-operator, exact-Q, 1+1D
- **Notes.** Qed count matches header (24). 0 Admitted, 0 axioms. This is the load-bearing root of the continuum thread (defines moment/hilbert_entry/kernel_coeff_entry/cont_entry reused downstream). Honesty: operator_rank_le_3 / operator_rank_eq_3 are restatements of the trace/diagonal computation, not genuine rank proofs.

**Lemmas (29):**

| name | kind | role |
|---|---|---|
| `moment` | Definition | момент монома int_0^1 x^n = 1/(n+1) (match до n=4) |
| `moment_0` | Lemma | moment 0 == 1 |
| `moment_1` | Lemma | moment 1 == 1/2 |
| `moment_2` | Lemma | moment 2 == 1/3 |
| `moment_3` | Lemma | moment 3 == 1/4 |
| `moment_4` | Lemma | moment 4 == 1/5 |
| `moment_positive` | Lemma | n<=4 => 0 < moment n |
| `hilbert_entry` | Definition | H3(i,j) = 1/(i+j+1), матрица Гильберта 3x3 |
| `hilbert_symmetric` | Lemma | H3 симметрична (i,j<3) |
| `hilbert_positive` | Lemma | все элементы H3 положительны |
| `kernel_coeff_entry` | Definition | A: разложение ядра k=1-4(x-y)^2 = [[1,0,-4],[0,8,0],[-4,0,0]] |
| `kernel_coeff_symmetric` | Lemma | A симметрична (i,j<3) |
| `mat3_mul_entry` | Definition | элемент произведения 3x3 матриц (A*B)_{ij} |
| `cont_entry` | Definition | ★ M = A*H3 (редуцированный оператор) |
| `cont_entry_00` | Lemma | M00 == -1/3 |
| `cont_entry_01` | Lemma | M01 == -1/2 |
| `cont_entry_02` | Lemma | M02 == -7/15 |
| `cont_entry_10` | Lemma | M10 == 4 |
| `cont_entry_11` | Lemma | M11 == 8/3 |
| `cont_entry_12` | Lemma | M12 == 2 |
| `cont_entry_20` | Lemma | M20 == -4 |
| `cont_entry_21` | Lemma | M21 == -2 |
| `cont_entry_22` | Lemma | M22 == -4/3 |
| `cont_matrix_entries` | Theorem | все 9 элементов M одной конъюнкцией |
| `cont_matrix_trace` | Theorem | ★ Trace(M) = -1/3+8/3-4/3 == 1 |
| `operator_rank_le_3` | Theorem | ранг<=3 (ядро степени 2) — переформулирован как trace==1 |
| `operator_rank_eq_3` | Theorem | ранг=3 — переформулирован как 3 диагональных значения |
| `continuum_operator_main` | Theorem | ★ главная: trace==1 + 3 диагонали |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`cont_entry`** - Несущее определение всего континуумного потока: транспортный оператор при K->inf на L^2[0,1] с ядром k(x,y)=1-4(x-y)^2 имеет образ внутри span{1,x,x^2} (ядро — полином степени 2), поэтому редуцируется к матрице M = A*H3, где A — коэффициенты ядра, H3 — матрица Гильберта (интегралы моментов). Это конкретная P4-финитизация: бесконечномерный интегральный оператор -> точная 3x3 рациональная матрица, спектр которой вычислим над Q. Дальше ExactEigenvalues/GapBound берут char_poly этого M. _(rank-reduction, integral-operator, hilbert-matrix, finitization)_
- **`cont_matrix_trace`** - Сигнатурный числовой факт: Trace(M) = -1/3 + 8/3 - 4/3 = 1, доказан unfold+simpl+lia. Поскольку след = сумма собственных значений, а ранг<=3, это инвариант, фиксирующий спектр редуцированного оператора. Оба 'operator_rank_le_3' и 'operator_rank_eq_3' — лишь переименования этого факта и трёх диагоналей; собственно ранг/детерминант A НЕ доказаны формально (rank=3 обосновано комментарием 'det A != 0'). Честно: rank-утверждения — риторика над одним вычислением следа. _(trace, spectrum, rank-rhetoric)_

**Uniqueness - score 3 (new-framing).** Exact rank-3 reduction of the K->infinity continuum transfer operator to a rational 3x3 matrix M=A*H3 (degree-2 kernel => finite rank), with all entries and trace machine-verified — the load-bearing finitization the rest of the thread builds on.
> _Caveat:_ The finite-rank reduction itself is the classical degenerate-kernel fact; novelty is only the exact-Q E/R/R framing and that it underpins the gap chain. 'rank=3' is NOT formally proved (asserted via comment); only trace=1 and the entries are. Specific to the 1+1D quadratic-action k=1-4(x-y)^2 kernel at beta=8, not a continuum spectral theorem. Header '~24 Qed' matches actual 24.

---

## #440 - `src/gauge/ContinuumSynthesis.v` - score 3 (new-framing)

**Capstone 'A=exists -> mass gap >= 1/8': the full 1+1D chain, with explicit Millennium-distance honesty**

- **Topic.** Bundles the whole 1+1D continuum chain into one narrative: A=exists -> L1-L5/P1-P4 -> process math -> lattice gauge as process -> transfer matrix -> RG flow beta->8 -> rank-3 continuum operator -> exact eigenvalues lambda0=2/3, lambda1<13/24 -> spectral gap >= 1/8, certified by the integer inequality 112 <= 135.
- **Role.** Grand capstone / pure consolidation of the 1+1D mass-gap programme (every conjunct is `exact` of an imported lemma or `lra`/`lia`). Imports gauge.TransferMatrix, StrongCoupling, KDependence, ContinuumOperator, ExactEigenvalues, GapBound. Backbone of the corresponding book/HIGHLIGHTS narrative.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; gauge.TransferMatrix; gauge.StrongCoupling; gauge.KDependence; gauge.ContinuumOperator; gauge.ExactEigenvalues; gauge.GapBound
- **E/R/R.** _Elements:_ ключевые числа: trace 1, lambda0=2/3, discriminant 7/15, q(13/24)=23/960, gap 1/8, string_tension 8 = 3/32, целые 112 и 135, 5/18, 16/9-3/2. _Roles:_ key_quantities/key_integers = роли «витрина чисел»; continuum_mass_gap = роль «спектральная щель континуума»; from_existence_to_mass_gap = роль 9-уровневой цепи A=exists->gap. _Rules:_ вся щель сведена к 2/3 - 13/24 == 1/8 (точное Q) и к целому неравенству 112 <= 135 (lia); все конъюнкты — exact/lra/lia над импортом. _P4:_ цепь A=exists -> P4(бесконечность как процесс) -> решётка как конечный процесс -> rank-3 оператор -> точные собственные значения над Q: вся конструкция держится на финитизации (континуум как процесс), а 3+1D/SU(2)/Haar остаются нетерминирующими — явно в 'what_remains'.
- **Classical counterpart.** Aspires to the Yang-Mills mass gap (Clay Millennium Problem); what it actually mirrors is the strong-coupling lattice expansion plus a finite-rank continuum reduction for a SIMPLIFIED 1+1D quadratic Wilson action. What differs from the Millennium target (stated in-file): only 1+1D, only a quadratic/U(1)-with-SU(2)-corrections action, no 3+1D, no exact SU(2) Haar plaquette action, no 4D continuum-limit survival; the 'gap >= 1/8' is an exact rational inequality (112<=135) for that toy model, not the Clay theorem.
- **Tags.** gauge, mass-gap, continuum-limit, capstone, synthesis, 1+1D, A-equals-exists, honesty, over-branding, header-drift
- **Notes.** Qed drift: header '~16 Qed', actual 11. 0 Admitted, 0 axioms. OVER-BRANDING FLAG: title/comments invoke 'Millennium' and 'FROM A=EXISTS TO MASS GAP'; the proved content is a 1+1D quadratic-action toy gap (2/3-13/24==1/8, 112<=135). The file's own 'what_remains' / 'WHAT REMAINS FOR MILLENNIUM PROBLEM' honestly disclaims the 3+1D SU(2) Clay problem. Also: the '~4,880 Qed' figure in a comment is a whole-project tally, not this file.

**Lemmas (11):**

| name | kind | role |
|---|---|---|
| `key_quantities` | Theorem | витрина: trace=1, char_poly(2/3)=0, discriminant>0, q(13/24)>0 |
| `key_integers` | Theorem | целые факты: 112<=135, 7/15<=9/16, q(13/24)==23/960 |
| `continuum_mass_gap` | Theorem | ★ щель континуума: lambda0=2/3, q(13/24)>0, 2/3-13/24==1/8 |
| `mass_gap_along_rg` | Theorem | вдоль RG: K=2 стена (gap=0), но 5/18>0 (K=3) |
| `from_existence_to_mass_gap` | Theorem | ★ 9-уровневая цепь A=exists -> gap>=1/8 (sigma>0, стена, K3>0, lambda0, gap, 112<=135) |
| `what_we_proved` | Theorem | честная сводка доказанного (K=2 стена, K=3>0, континуум gap>=1/8) |
| `what_remains` | Theorem | ★ честный маркер остатка (только lambda0 + gap=1/8 доказаны; 3+1D открыт) |
| `methodology_summary` | Theorem | методология: собственное значение + свидетель щели + целая граница |
| `continuum_main` | Theorem | ★ главная: trace + lambda0 + q-свидетель + gap=1/8 + 112<=135 |
| `the_final_number` | Theorem | 0 < 1/8 (финальное число) |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`from_existence_to_mass_gap`** - Гранд-капстоун всего потока: одной теоремой выстроена 10-уровневая цепь от 'A = exists' (через L1-L5/P1-P4, процессную математику, решётку как конечный процесс, RG-поток beta->8, K=2 стену, K>=3 пробой, rank-3 оператор, точные собственные значения) до 'щель >= 1/8', сертифицированной целым неравенством 112 <= 135. Содержательно это конъюнкция шести импортированных Q-фактов (string_tension>0, стена, 5/18>0, char_poly(2/3)=0, q(13/24)>0, 112<=135) — 0 нового содержания, спина книжного нарратива. Уровни 0-1 (A=exists->логика->P4) присутствуют лишь как комментарии, а не как доказанные шаги. _(capstone, A-equals-exists, synthesis, 1+1D)_
- **`what_remains`** - Образцовый встроенный маркер честности: комментарий прямо перечисляет, что результат относится к 1+1 измерениям (не 3+1), к квадратичному действию Вилсона (не точному плакетному), к U(1)-дискретизации с SU(2)-поправками, и что для Clay-приза нужны 3+1D, точное SU(2) Haar-действие и выживание щели в 4D-континууме. Сама теорема скромна (char_poly(2/3)=0 и 2/3-13/24==1/8). Это и есть критический anti-overclaim противовес аспирационным словам 'continuum'/'final'/'Millennium' в файле. _(honesty, millennium-distance, 1+1D-only, quadratic-action)_

**Uniqueness - score 3 (new-framing).** A single-theorem 'A=exists -> mass gap >= 1/8' chain that frames the 1+1D lattice gap programme end-to-end (existence/logic -> process math -> finite-rank continuum operator -> exact eigenvalue gap), reducing the whole story to the integer inequality 112 <= 135.
> _Caveat:_ ASPIRATIONAL naming ('continuum', 'final', 'Millennium') — this does NOT prove the Clay Yang-Mills mass gap. It is pure consolidation (every step is `exact`/`lra`/`lia` over imports, 0 new content) of a 1+1D, quadratic-Wilson-action, U(1)-with-SU(2)-corrections toy model; the file itself states under 'what_remains' that 3+1D, exact SU(2) Haar action, and 4D continuum survival are all undone. Levels 0-1 (A=exists -> logic -> P4) appear only as comments. Header '~16 Qed' vs actual 11 Qed.

---

## #441 - `src/gauge/CorrelationProof.v` - score 2 (methods)

**OS1 (аналитичность) + OS2 (регулярность) для двухточечной корреляции = степень отношения собственных значений**

- **Topic.** Определяет полную двухточечную функцию full_correlation J t j β M = (λ_j/λ_0)^t как отношение собственных значений трансфер-матрицы и доказывает аксиомы Остервальдера-Шрадера OS1 (корреляция = отношение Q с положительным знаменателем) и OS2 (|G| ≤ 1) для конкретных β=1,2, j=1, усечения M=0.
- **Role.** Зависит от gauge.CharacterTransfer, ExactMassGap, GapRatio, TransferMatrixProof, ClusterProof (откуда берёт dm_entry/transfer_mat/matrix_corr и леммы упорядочения собственных значений). Переиспользуется CovarianceProof.v (OS3), который импортирует этот файл целиком; full_correlation — общий объект пакета OS-доказательств.
- **Counts.** Qed 24 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: CauchyReal; ToS: SeriesConvergence; ToS: gauge.CharacterTransfer; ToS: gauge.ExactMassGap; ToS: gauge.GapRatio; ToS: gauge.TransferMatrixProof; ToS: gauge.ClusterProof
- **E/R/R.** _Elements:_ конкретные рациональные собственные значения трансфер-матрицы dm_entry (transfer_mat J β M) j; разделение t_sep; усечение J и M=0; параметры β∈{1,2}. _Roles:_ full_correlation — наблюдаемая-процесс (степень отношения); числитель/знаменатель — Element-стороны OS1; граница \|G\|≤1 — роль регулярности OS2; затухание r<1 — роль кластерного свойства. _Rules:_ G(t)=(λ_j/λ_0)^t; OS1 = разложение в num/denom с 0<denom (Qpow_div); OS2 = Qpow_bound_1 при 0≤r≤1; затухание через cluster_property_proved. _P4:_ корреляция — КОНЕЧНОЕ рациональное выражение в отношениях собственных значений на каждом конечном уровне (J,M): Element-сторона разрешима (vm_compute/lra даёт num/denom и границу); континуум-предел (полная OS-реконструкция) НЕ берётся — это role-limit вне файла.
- **Classical counterpart.** Аксиомы Остервальдера-Шрадера OS1 (аналитичность) и OS2 (регулярность/рост) евклидовой конструктивной КТП. Отличие: здесь они доказаны НЕ как свойства континуальных корреляционных функций, а как элементарные факты о рациональной степени (λ_j/λ_0)^t на конечной решётке при ДВУХ значениях β и одном канале — отношение положительных Q (OS1) и \|r^t\|≤1 (OS2). Континуум-предел и аналитическое продолжение отсутствуют.
- **Tags.** gauge, osterwalder-schrader, correlation, transfer-matrix, finite-lattice, rational, P4, methods
- **Notes.** Дрейф заголовка: STATUS '~35 Qed', фактически 24 Qed. Имена с суффиксом '_proved'/'os1'/'os2' аспирационны — это OS-аксиомы для конкретной конечной решётки при β∈{1,2}, не континуальная реконструкция.

**Lemmas (25):**

| name | kind | role |
|---|---|---|
| `full_correlation` | Definition | двухточечная функция (λ_j/λ_0)^t_sep как Qpow отношения элементов трансфер-матрицы |
| `correlation_at_0` | Theorem | G(0)=1 (степень 0) |
| `correlation_ground` | Theorem | основное состояние j=0 даёт G≡1 при λ_0>0 |
| `correlation_eq_matrix_corr` | Theorem | мост: full_correlation совпадает с matrix_corr из ClusterProof |
| `correlation_eq_ratio` | Theorem | возбуждённое j=1 при M=0 = gap_ratio^t |
| `correlation_denom_positive` | Theorem | знаменатель Qpow λ_0 t > 0 при λ_0>0 |
| `correlation_num_nonneg` | Theorem | числитель Qpow λ_j t ≥ 0 при λ_j≥0 |
| `Qpow_div` | Lemma | Qpow распределяется по делению: (a/b)^n = a^n/b^n при b>0 |
| `correlation_is_ratio` | Theorem | G = (λ_j^t)/(λ_0^t) — раскрытие в отношение |
| `os1_analytic_proved` | Theorem | ★ OS1: существуют num,denom с G=num/denom и denom>0 |
| `os1_at_beta_1` | Theorem | OS1 при β=1 (через t0_positive_beta_1) |
| `os1_at_beta_2` | Theorem | OS1 при β=2 |
| `eigenvalue_ratio_nonneg` | Lemma | λ_j/λ_0 ≥ 0 при λ_j≥0, λ_0>0 |
| `eigenvalue_ratio_le_1` | Lemma | λ_j/λ_0 ≤ 1 при λ_j≤λ_0 |
| `correlation_nonneg` | Theorem | G ≥ 0 при неотрицательном отношении |
| `correlation_le_1` | Theorem | G ≤ 1 при отношении ≤ 1 |
| `correlation_abs_bounded` | Theorem | \|G\| ≤ 1 при упорядоченных собственных значениях |
| `os2_at_beta_range` | Theorem | OS2 при β∈[0,2], j≤1 (условно на упорядочении) |
| `os2_regular_at_1` | Theorem | ★ OS2: \|G\| ≤ 1 для j=1 при β=1 (полный proof term) |
| `os2_regular_at_2` | Theorem | OS2 для j=1 при β=2 |
| `correlation_decays_1` | Theorem | затухание: ∀ε>0 ∃t, G(t)<ε при β=1 (из cluster_property) |
| `correlation_decays_2` | Theorem | затухание при β=2 |
| `os1_os2_at_1` | Theorem | объединение OS1∧OS2 при β=1 |
| `os1_os2_at_2` | Theorem | объединение OS1∧OS2 при β=2 |
| `correlation_proof_summary` | Theorem | сводка: OS1 (β=1,2) ∧ OS2 ∧ затухание в одной конъюнкции |

**Key lemmas (deep):**

- **`os1_analytic_proved`** - Ядро OS1-стороны: корреляция предъявляется КАК отношение num/denom двух положительных рациональных степеней собственных значений с явным свидетелем num=λ_j^t, denom=λ_0^t и доказательством denom>0 (Qpow_pos). Это честная Element-форма аналитичности: на конечном уровне корреляция — рациональное число с положительным знаменателем, а не аналитическая функция комплексного β. 'Аналитичность' здесь = рациональная-выразимость, не голоморфность; настоящая OS1 (аналитическое продолжение в трубу) НЕ доказывается. _(OS1, rational-structure, transfer-matrix, finite-level)_
- **`os2_regular_at_1`** - Element-форма регулярности OS2: \|G(t)\| ≤ 1 для конкретного канала j=1 при β=1, собранная из трёх импортированных фактов (t1_M0_nonneg, eigenvalue_ordering_0_1, t0_positive_beta_1) через Qpow_bound_1. Граница тривиальна, как только установлено 0≤r≤1; всё содержание — в упорядочении собственных значений, которое импортируется, а не доказывается здесь. Привязка к β∈{1,2}, j=1, M=0 — это НЕ равномерная по β,j регулярность, требуемая полной OS2. _(OS2, boundedness, specific-coupling, imported-ordering)_

**Uniqueness - score 2 (methods).** Необычная финитная формализация двух OS-аксиом: корреляция как рациональная степень отношения собственных значений трансфер-матрицы, OS1 = разложение num/denom с положительным знаменателем, OS2 = граница Qpow при 0≤r≤1, всё полными proof-термами без True.
> _Caveat:_ НЕ доказывает OS-аксиомы для континуальной КТП и не является доказательством Clay mass-gap. Установлено лишь для конкретных β=1,2, канала j=1, усечения M=0; упорядоченность собственных значений ИМПОРТИРУЕТСЯ; 'аналитичность'=рациональная выразимость, не голоморфность. Дрейф заголовка: STATUS заявляет ~35 Qed, фактически 24.

---

## #442 - `src/gauge/CosineAction.v` - score 2 (methods)

**Тейлоровские члены вильсоновского косинус-действия 1-cos θ: знакочередование + факториальные границы 1/(2n+2)!**

- **Topic.** Определяет тейлоровские члены cos_term θ n = (-1)^n θ^{2(n+1)}/(2(n+1))! разложения 1-cos θ из вильсоновского действия S=β·Σ_P(1-cos θ_P) и доказывает конкретные факториалы (2!,4!,6!,8!), границу |cos_term θ n| ≤ 1/(2n+2)! при |θ|≤1, монотонное убывание границ и знакочередование.
- **Role.** Зависит от ToS PowerSeries (partial_sum, Qpow, Qfact) и RealField; импортирует zeta.ZetaProcess. Самостоятельный аналитический модуль вильсоновского действия — не импортируется ядром mass-gap, поставляет факториальные оценки для тейлоровского анализа плакетного действия.
- **Counts.** Qed 21 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs List Lia ZArith Lqa; ToS: CauchyReal; ToS: SeriesConvergence; ToS: PowerSeries; ToS: RealField; ToS: zeta.ZetaProcess
- **E/R/R.** _Elements:_ рациональный угол плакета θ; натуральный индекс члена n; конкретные факториалы Qfact (2,4,6,8); частичные суммы partial_sum. _Roles:_ cos_term — n-й вклад в 1-cos θ; alt_sign — знак-ролик (-1)^n; one_minus_cos_approx — приближение порядка k; границы 1/(2n+2)! — роль контроля остатка. _Rules:_ cos_term = alt_sign·θ^{2(S n)}/Qfact(2(S n)); знаки alt_sign(S n)=-alt_sign(n); граница \|cos_term\|≤/Qfact через Qpow_bound_1; убывание через Qfact_monotone+Qinv_le_compat. _P4:_ каждый тейлоровский член — КОНЕЧНОЕ рациональное число (alt_sign∈{±1}, θ^k, обратный факториал); приближение порядка k вычислимо (Element); сама функция cos как бесконечная сумма — нетерминирующий процесс (role-limit), достигается лишь как предел частичных сумм, в файле не строится.
- **Classical counterpart.** Ряд Тейлора 1-cos θ = θ²/2! - θ⁴/4! + ... и стандартная оценка остатка знакопеременного ряда (теорема Лейбница) + факториальный рост. Отличие здесь: всё формализовано над точными рациональными Q (Qfact, Qpow) без библиотеки Reals, как поставщик границ для вильсоновского плакетного действия; сходимость к самой cos НЕ строится (только границы членов).
- **Tags.** gauge, wilson-action, taylor-series, cosine, factorial, rational, alternating-series, methods
- **Notes.** Заголовок 'AXIOMS: classic (via PowerSeries)' — это транзитивная зависимость импорта, СОБСТВЕННЫХ Axiom/Parameter в файле нет (локально axioms=0). Qed=22 совпадает с заголовком ~22.

**Lemmas (25):**

| name | kind | role |
|---|---|---|
| `alt_sign` | Definition | (-1)^n как Q: 1 если n чётно, иначе -1 |
| `cos_term` | Definition | n-й член разложения 1-cos θ: alt_sign·θ^{2(S n)}/факториал |
| `one_minus_cos_approx` | Definition | частичная сумма порядка k = приближение 1-cos θ |
| `alt_sign_0` | Lemma | alt_sign 0 = 1 |
| `alt_sign_1` | Lemma | alt_sign 1 = -1 |
| `alt_sign_2` | Lemma | alt_sign 2 = 1 |
| `alt_sign_abs` | Lemma | \|alt_sign n\| = 1 для всех n |
| `alt_sign_nonzero` | Lemma | alt_sign n ≠ 0 |
| `Qfact_2` | Lemma | 2! = 2 |
| `Qfact_4` | Lemma | 4! = 24 |
| `Qfact_6` | Lemma | 6! = 720 |
| `Qfact_8` | Lemma | 8! = 40320 |
| `Qfact_monotone` | Lemma | n≤m ⟹ Qfact n ≤ Qfact m (индукция по ≤) |
| `Qfact_step` | Lemma | Qfact(S n) = (S n)·Qfact n (по определению) |
| `cos_term_at_zero` | Lemma | cos_term 0 n = 0 |
| `cos_approx_at_zero` | Lemma | приближение при θ=0 равно 0 |
| `cos_approx_1` | Lemma | приближение порядка 0 = θ²/2! |
| `cos_approx_nonneg` | Lemma | приближение порядка 0 ≥ 0 (θ²·/2!≥0) |
| `cos_term_abs_bound` | Lemma | ★ \|cos_term θ n\| ≤ 1/(2(S n))! при \|θ\|≤1 |
| `cos_term_bound_decreasing` | Lemma | граница при S n ≤ граница при n (обратный факториал монотонен) |
| `cos_term_chained_bound` | Lemma | член порядка S n ограничен границей порядка n |
| `cos_term_sign_alternates` | Lemma | ★ alt_sign(S n) = -alt_sign(n) (Nat.even_succ) |
| `cos_action_main` | Theorem | сводка: исчезновение при 0 ∧ неотрицательность ∧ две границы членов |
| `cos_action_summary` | Theorem | сводка: факториалы 2/24/720/40320 ∧ \|alt_sign\|=1 ∧ граница члена |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`cos_term_abs_bound`** - Несущая лемма: для \|θ\|≤1 модуль n-го тейлоровского члена ограничен обратным факториалом 1/(2(n+1))!. Доказательство аккуратно раскладывает \|alt_sign\|·\|θ^k\|·\|1/k!\| и применяет Qpow_bound_1 к \|θ^k\|≤1 — стандартная оценка остатка ряда Тейлора, но проведённая над точными Q без обращения к Coq's Reals. Это даёт контроль сходимости косинус-действия на решётке. Содержание классическое; ценность — финитная реализация. _(taylor-remainder, factorial-bound, rational, convergence-control)_
- **`cos_term_sign_alternates`** - Знакочередование через Nat.even_succ: alt_sign(S n) = -alt_sign(n). Тривиальный, но необходимый структурный факт знакопеременного ряда — без него нельзя оценивать остаток через первый отброшенный член. Чистая комбинаторика чётности, ноль физики. _(alternating-series, parity)_

**Uniqueness - score 2 (methods).** Финитная Q-формализация тейлоровских членов вильсоновского косинус-действия: знакочередование, точные факториалы и оценка |член| ≤ 1/(2n+2)! при |θ|≤1, всё полными proof-термами над рациональными числами.
> _Caveat:_ Полностью классическое содержание (ряд Тейлора cos, лейбницева оценка остатка). Ново только оформление над Q без Reals в контексте решётки. Не доказывает сходимость к cos и не связано с самим mass-gap результатом. Заголовок честно заявляет AXIOMS: classic (через PowerSeries), хотя сам файл новых аксиом не вводит (axioms=0 локально).

---

## #443 - `src/gauge/Coupled2D.v` - score 1 (exposition)

**Связанная 2+1D трансфер-матрица 4×4 со пространственным плакетом; при β=8 диагональна diag(1,1/4,1/4,1)**

- **Topic.** Минимальная 2+1D модель: две пространственные связи, связанные пространственным плакетом, с параметрами α=1-β/8, γ=1-β/16. Строит симметричную 4×4 трансфер-матрицу t4_entry над двумя состояниями {0,1/2}² и доказывает, что при β=8 (α=0, γ=1/2) она диагональна со спектром {1,1/4,1/4,1}.
- **Role.** Самостоятельный (импортирует только Stdlib). Базовый блок: Coupled3D.v импортирует этот файл и переиспользует alpha_2d/gamma_2d для трёхплакетной модели. Поставляет 2D-ступень лестницы размерностей в программе mass-gap.
- **Counts.** Qed 19 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa
- **E/R/R.** _Elements:_ рациональные параметры связи α=1-β/8, γ=1-β/16; 4 состояния (0,0)/(0,½)/(½,0)/(½,½); записи матрицы t4_entry; конкретное β=8. _Roles:_ t4_entry — ядро трансфера (роль перехода между конфигурациями); γ — пространственный вес плакета; след coupled_trace — спектральный инвариант; v_minus/v_q — антисимметричные пробные векторы. _Rules:_ t4_entry задана таблицей 4×4 из произведений α,γ; симметрия t4(i,j)=t4(j,i); при β=8 внедиагональ зануляется (α=0) ⟹ диагональ; след = 2+2γ². _P4:_ вся матрица — КОНЕЧНАЯ рациональная таблица 16 записей; каждое утверждение разрешимо vm_compute/lra на фиксированном β=8 (Element); это решётка при ОДНОМ K=2-усечении угла, не континуальная теория.
- **Classical counterpart.** Трансфер-матричный метод решёточной калибровочной теории (Wilson/Kogut) и точная диагонализация в специальной точке связи. Отличие: предельно огрублённая дискретизация — угол θ ограничен двумя значениями {0,1/2} при K=2, β зафиксирован в 8; матрица задана явной рациональной таблицей и проверена vm_compute, без перехода к континууму или к настоящему спектру при общем β.
- **Tags.** gauge, transfer-matrix, 2plus1D, lattice, diagonalization, rational, finite-lattice, exposition
- **Notes.** Дрейф заголовка: STATUS '~22 Qed', фактически 20 Qed. Имя файла 'Coupled2D' описательно (не аспирационно), но как и весь кластер это конечно-решёточный, одно-β результат, не континуум.

**Lemmas (28):**

| name | kind | role |
|---|---|---|
| `alpha_2d` | Definition | α=1-β/8 — временная внедиагональ из 1+1D |
| `gamma_2d` | Definition | γ=1-β/16 — пространственный вес из плакета |
| `alpha_at_0` | Lemma | α(0)=1 |
| `alpha_at_8` | Lemma | α(8)=0 (точка диагонализации) |
| `alpha_positive` | Lemma | 0<α при 0<β<8 |
| `gamma_at_0` | Lemma | γ(0)=1 |
| `gamma_at_8` | Lemma | γ(8)=1/2 |
| `gamma_positive` | Lemma | 0<γ при 0<β<16 |
| `gamma_lt_one` | Lemma | γ<1 при β>0 |
| `t4_entry` | Definition | 4×4 трансфер-матрица как таблица произведений α,γ |
| `t4_symmetric` | Lemma | ★ t4(i,j)=t4(j,i) для i,j<4 (полный перебор 4×4 + ring) |
| `t4_00_at_8` | Lemma | t4(0,0)=1 при β=8 |
| `t4_01_at_8` | Lemma | t4(0,1)=0 при β=8 |
| `t4_02_at_8` | Lemma | t4(0,2)=0 при β=8 |
| `t4_03_at_8` | Lemma | t4(0,3)=0 при β=8 |
| `t4_11_at_8` | Lemma | t4(1,1)=1/4 при β=8 |
| `t4_12_at_8` | Lemma | t4(1,2)=0 при β=8 |
| `t4_22_at_8` | Lemma | t4(2,2)=1/4 при β=8 |
| `t4_33_at_8` | Lemma | t4(3,3)=1 при β=8 |
| `coupled_2d_diagonal_at_8` | Theorem | ★ при β=8 матрица диагональна со спектром {1,1/4,1/4,1} |
| `coupled_trace` | Definition | след = 2+2γ² |
| `coupled_trace_correct` | Theorem | сумма диагонали t4 = coupled_trace (ring) |
| `coupled_trace_at_8` | Theorem | след(8)=5/2 |
| `vec4` | Definition | тип вектора nat->Q |
| `t4_apply` | Definition | матрично-векторное произведение (T·v)_i по 4 компонентам |
| `v_minus` | Definition | пробный вектор (1,0,0,-1), антисимметричный при обмене связей |
| `v_q` | Definition | пробный вектор (0,1,-1,0), антисимметричный |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`coupled_2d_diagonal_at_8`** - Главный факт файла: в специальной точке β=8 (где α=1-β/8=0 зануляет все временные внедиагонали) трансфер-матрица 4×4 становится диагональной diag(1,1/4,1/4,1). Доказательство — конъюнкция шести записей, каждая закрыта lra или Qeq+lia на фиксированных рациональных числах. Это даёт точно решаемую опорную точку для оценки щели в 2+1D, но ТОЛЬКО в этой одной точке связи и при K=2-дискретизации угла θ∈{0,1/2}; общий β оставляет матрицу недиагональной (спектр не вычисляется). Не доказательство щели масс — точечный анализ модели. _(transfer-matrix, diagonal-point, 2plus1D, single-coupling, finite)_
- **`t4_symmetric`** - Симметричность 4×4 матрицы через полный перебор 16 пар индексов (destruct i,j as [\|[\|[\|[\|?]]]]) с закрытием ring. Структурно гарантирует вещественность спектра трансфер-матрицы (симметричная ⟹ диагонализуема над R) — необходимое условие для последующей спектральной интерпретации; чисто алгебраическая проверка таблицы. _(symmetry, spectral-prerequisite, enumeration)_

**Uniqueness - score 1 (exposition).** Чисто рациональная, машинно-проверенная конструкция минимальной 2+1D трансфер-матрицы 4×4 со пространственным плакетом и её точная диагонализация в опорной точке β=8.
> _Caveat:_ НЕ доказательство Clay mass-gap и не утверждение о щели в 2+1D континуальной Янг-Миллс. Конечная 4×4 модель при ОДНОМ значении связи β=8 и грубой K=2-дискретизации угла (θ∈{0,1/2}); общий β оставляет спектр невычисленным. Дрейф заголовка: STATUS '~22 Qed', фактически 20.

---

## #444 - `src/gauge/Coupled3D.v` - score 1 (exposition)

**Связанная 3+1D трансфер-матрица: S3-инвариантный блок диагонален при β=8, спектр по весу Хэмминга**

- **Topic.** Три пространственные связи θ_1,θ_2,θ_3∈{0,1/2} при K=2 с тремя пространственными плакетами на парах; трансфер-матрица 8×8 редуцируется к 4×4 S3-инвариантному блоку block_u по весу Хэмминга h. Доказывает, что при β=8 (α=0) блок диагонален: h=0,3 → собственное значение 1; h=1,2 → 3/16.
- **Role.** Зависит от gauge.Coupled2D (переиспользует gamma_2d, alpha_2d). Верхняя ступень лестницы размерностей (1+1D → 2+1D → 3+1D) в программе оценки щели; самостоятельный анализ модели, ядром mass-gap не импортируется.
- **Counts.** Qed 18 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: gauge.Coupled2D
- **E/R/R.** _Elements:_ три связи θ_i∈{0,1/2}; вес Хэмминга h∈{0,1,2,3}; пространственный вес w3d; суммы Хэмминга hamming_sum_3d; β=8. _Roles:_ block_u — S3-инвариантный 4×4 блок (роль редуцированного трансфера); w3d — вес по числу несовпадающих пар h(3-h); hamming_sum_3d — сумма по расстояниям Хэмминга внутри секторов. _Rules:_ w3d(h)=γ^{unlike(h)}, unlike(h)=h(3-h); block_u=w3d(h1)·w3d(h2)·hamming_sum(h1,h2); при β=8 α=0 ⟹ все внедиагональные суммы зануляются ⟹ блок диагонален; комплемент-симметрия w(h)=w(3-h). _P4:_ 8×8 матрица редуцирована перебором конфигураций к КОНЕЧНОЙ 4×4 рациональной таблице по весу Хэмминга; каждое утверждение разрешимо lra/Qeq на β=8 (Element); это решётка при K=2 и ОДНОМ β, не континуум.
- **Classical counterpart.** Трансфер-матричный метод решёточной Янг-Миллс в 3+1D и блочная диагонализация по группе симметрии (здесь S3 перестановок пространственных связей), спектр по классам эквивалентности. Отличие: крайне огрублённая модель — три связи на двух значениях {0,1/2} (K=2), β зафиксирован в 8, 8×8→4×4 блок задан рациональной таблицей и проверен vm_compute; ни континуума, ни спектра при общем β.
- **Tags.** gauge, transfer-matrix, 3plus1D, lattice, S3-symmetry, hamming, diagonalization, finite-lattice, exposition
- **Notes.** Дрейф заголовка: STATUS '~22 Qed', фактически 19 Qed. total_count — тривиальный reflexivity-маркер (block_u_8_00=block_u_8_00), не несущий лемму.

**Lemmas (22):**

| name | kind | role |
|---|---|---|
| `w3d` | Definition | пространственный вес γ^{unlike pairs(h)}: h=0,3→1; h=1,2→γ² |
| `w3d_0` | Lemma | w3d β 0 = 1 |
| `w3d_1` | Lemma | w3d β 1 = γ² |
| `w3d_2` | Lemma | w3d β 2 = γ² |
| `w3d_3` | Lemma | w3d β 3 = 1 |
| `w3d_complement` | Lemma | комплемент-симметрия w(h)=w(3-h) при h≤3 |
| `w3d_at_8_0` | Lemma | w3d 8 0 = 1 |
| `w3d_at_8_1` | Lemma | w3d 8 1 = 1/4 (γ=1/2) |
| `w3d_at_8_2` | Lemma | w3d 8 2 = 1/4 |
| `w3d_at_8_3` | Lemma | w3d 8 3 = 1 |
| `hamming_sum_3d` | Definition | Σ α^{d(s,s')} по секторам весов h1,h2 (таблица 4×4) |
| `hamming_sum_symmetric` | Theorem | D(h1,h2)=D(h2,h1) (перебор + lra) |
| `hamming_sum_offdiag_at_8` | Theorem | при β=8 все внедиагональные суммы = 0 (α=0) |
| `block_u` | Definition | S3-блок B_u[h1,h2]=w3d(h1)·w3d(h2)·D(h1,h2) |
| `block_u_symmetric` | Theorem | блок симметричен (перебор + ring) |
| `block_u_8_00` | Lemma | block_u 8 0 0 = 1 |
| `block_u_8_11` | Lemma | block_u 8 1 1 = 3/16 |
| `block_u_8_22` | Lemma | block_u 8 2 2 = 3/16 |
| `block_u_8_33` | Lemma | block_u 8 3 3 = 1 |
| `block_u_offdiag_at_8` | Theorem | ★ при β=8 все внедиагональные записи блока = 0 |
| `coupled_3d_main` | Theorem | ★ при β=8 блок диагонален: диаг (1,3/16,3/16,1) + веса w3d |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`coupled_3d_main`** - Капстоун файла: в точке β=8 (α=0) редуцированный по S3-симметрии 4×4 блок трансфер-матрицы 3+1D диагонален с собственными значениями, зависящими только от веса Хэмминга — h=0,3 дают 1, h=1,2 дают 3/16. Спектр сгруппирован по орбитам перестановочной группы S3 трёх связей. Это распространяет точку диагонализации с 2+1D (Coupled2D) на 3+1D, но опять-таки лишь в одной точке β=8 при K=2 и только для S3-инвариантного сектора (полная 8×8 при общем β не диагонализуется). Не доказательство щели масс — спектральная опорная точка модели. _(transfer-matrix, 3plus1D, S3-symmetry, hamming-weight, diagonal-point, single-coupling)_
- **`block_u_offdiag_at_8`** - Несущий шаг к диагональности: все внедиагональные записи блока зануляются при β=8, потому что каждая содержит множитель α=0 (через hamming_sum_offdiag_at_8). Доказательство — перебор пар весов h1≠h2 с раскрытием α. Именно зануление временных переходов при α=0 делает спектр явно читаемым; механизм идентичен 2D-случаю, поднятый на хэмминговы секторы. _(off-diagonal-vanishing, alpha-zero, enumeration)_

**Uniqueness - score 1 (exposition).** Рациональная машинно-проверенная редукция 3+1D трансфер-матрицы к S3-инвариантному 4×4 блоку и его точная диагонализация по весу Хэмминга в опорной точке β=8.
> _Caveat:_ НЕ доказательство Clay mass-gap и не утверждение о щели в 3+1D континуальной Янг-Миллс. Конечная модель при ОДНОМ β=8, грубой K=2-дискретизации и только в S3-инвариантном секторе; общий β и полная 8×8 не рассматриваются. Дрейф заголовка: STATUS '~22 Qed', фактически 19.

---

## #445 - `src/gauge/CovarianceProof.v` - score 1 (exposition)

**OS3 (евклидова ковариантность): корреляция зависит только от разделения t_sep; несколько 'теорем' — тривиальный reflexivity**

- **Topic.** Доказывает аксиому OS3 (евклидова ковариантность) для full_correlation из CorrelationProof: корреляция выражается как r^{t_sep} (функция только разделения) с 0≤r≤1 при β=1,2 для j∈{0,1}, и не зависит от усечения J. Часть утверждений (трансляционная инвариантность во времени, обращение времени, изотропия) — тривиальные reflexivity-тождества вида G==G.
- **Role.** Вершина пакета OS-доказательств: импортирует CorrelationProof.v целиком (full_correlation, covariance-помощники) плюс CharacterTransfer/ExactMassGap/GapRatio/TransferMatrixProof/ClusterProof. Завершает тройку OS1/OS2 (CorrelationProof) + OS3 (этот файл) для конечной решётки.
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: CauchyReal; ToS: SeriesConvergence; ToS: gauge.CharacterTransfer; ToS: gauge.ExactMassGap; ToS: gauge.GapRatio; ToS: gauge.TransferMatrixProof; ToS: gauge.ClusterProof; ToS: gauge.CorrelationProof
- **E/R/R.** _Elements:_ разделение t_sep; отношение собственных значений r=λ_j/λ_0; усечения J1,J2; каналы j∈{0,1}; β∈{1,2}. _Roles:_ full_correlation — наблюдаемая, зависящая ТОЛЬКО от t_sep (роль ковариантности OS3); r — рациональная скорость затухания; J-независимость — роль устойчивости к усечению. _Rules:_ G=r^{t_sep} (correlation_is_function_of_sep); J1,J2-независимость через reflexivity (определение не зависит от J); ковариантность с границами 0≤r≤1 из упорядочения собственных значений. _P4:_ ковариантность тут СТРУКТУРНА: определение G=(λ_j/λ_0)^{t_sep} явно содержит только t_sep, так что инвариантность к сдвигу/J — определительное тождество (Element, reflexivity); полная евклидова группа SO(4)/изотропия НЕ доказывается — лишь утверждается в комментариях как 'функция от \|x\| ⟹ инвариантна'.
- **Classical counterpart.** Аксиома Остервальдера-Шрадера OS3 (евклидова ковариантность относительно группы движений) конструктивной КТП. Отличие: здесь установлена лишь зависимость корреляции от величины разделения t_sep на конечной решётке при β∈{1,2}, j∈{0,1}; полная евклидова/SO(4)-инвариантность только ДЕКЛАРИРОВАНА в комментариях, а ряд 'теорем' — тривиальные reflexivity-тождества, не несущие содержания.
- **Tags.** gauge, osterwalder-schrader, OS3, covariance, correlation, finite-lattice, overbranding, reflexivity-placeholder, exposition
- **Notes.** Дрейф заголовка: STATUS '~25 Qed', фактически 13 Qed. ОВЕРБРЕНДИНГ: time_shift_invariant, time_reversal, eigenvalue_direction_independent, correlation_isotropic — тривиальные reflexivity (G==G); isotropy_implies_rotation_invariance заявляет SO(4), но доказывает лишь форму r^{t_sep}. Реальное содержание OS3 несёт только covariance_from_ratio.

**Lemmas (13):**

| name | kind | role |
|---|---|---|
| `time_shift_invariant` | Theorem | тривиально G==G (reflexivity; формальный сдвиг shift не используется) |
| `correlation_is_function_of_sep` | Theorem | ★ ∃r, G = r^{t_sep} — корреляция есть функция только разделения |
| `ratio_independent_of_J` | Theorem | G не зависит от усечения J (определение не содержит J в показателе) |
| `time_reversal` | Theorem | тривиально G==G (reflexivity) |
| `eigenvalue_direction_independent` | Theorem | тривиально λ==λ (reflexivity; направление не входит в transfer_eigenvalue) |
| `correlation_isotropic` | Theorem | тривиально G==G (reflexivity) |
| `covariance_from_ratio` | Theorem | ★ ∃r, G=r^{t_sep} ∧ 0≤r≤1 при упорядоченных собственных значениях |
| `covariance_at_1` | Theorem | ковариантность с границами r∈[0,1] при β=1, j∈{0,1} |
| `covariance_at_2` | Theorem | ковариантность с границами при β=2, j∈{0,1} |
| `os3_covariance_proved` | Theorem | ★ OS3: функция от разделения ∧ J-независимость ∧ границы при β=1,2 |
| `lattice_covariance` | Theorem | решёточная ковариантность = correlation_is_function_of_sep (комментарий про гиперкуб) |
| `isotropy_implies_rotation_invariance` | Theorem | заявляет SO(4)-инвариантность, доказывает лишь форму r^{t_sep} (= function_of_sep) |
| `covariance_proof_summary` | Theorem | сводка OS3: форма r^{t_sep} ∧ границы при β=1,2 |

**Key lemmas (deep):**

- **`covariance_from_ratio`** - Единственная содержательная лемма ковариантности: корреляция = r^{t_sep} с явным свидетелем r=λ_j/λ_0 И границами 0≤r≤1, выведенными из упорядочения собственных значений (Qle_shift_div_l/r). Это честная Element-форма OS3 на конечной решётке: корреляция манифестно зависит только от величины разделения. Но это привязано к β∈{1,2}, j∈{0,1}, M=0 и опирается на ИМПОРТИРУЕМОЕ упорядочение; полная евклидова ковариантность (вся гиперкубическая/SO(4) группа) НЕ устанавливается. _(OS3, function-of-separation, rational-decay, specific-coupling)_
- **`isotropy_implies_rotation_invariance`** - ОВЕРКЛЕЙМ-флаг: имя и комментарии заявляют SO(4)-инвариантность ('любая функция от \|x\| инвариантна под ВСЕМИ вращениями'), но тело доказательства — exact correlation_is_function_of_sep, т.е. устанавливается лишь форма r^{t_sep}. Переход 'функция от разделения ⟹ полная группа вращений' остаётся в прозе-комментарии, не формализован. Аналогично time_shift_invariant/time_reversal/correlation_isotropic/eigenvalue_direction_independent — это reflexivity-тождества X==X, риторически названные как физические симметрии. Содержательно ковариантность несёт только covariance_from_ratio. _(overbranding, reflexivity-placeholder, SO4-claimed-not-proved, honesty-flag)_

**Uniqueness - score 1 (exposition).** Финитная Element-форма OS3: корреляция конечной решётки = r^{t_sep} с границами 0≤r≤1, манифестно зависящая только от разделения и не зависящая от усечения J, при β=1,2.
> _Caveat:_ НЕ континуальная OS3 и не часть доказательства Clay mass-gap. Полная евклидова/SO(4)-ковариантность лишь декларирована в комментариях (isotropy_implies_rotation_invariance доказывает только форму r^{t_sep}); 4 из 13 'теорем' — тривиальные reflexivity X==X. Содержательна по сути одна лемма covariance_from_ratio, привязанная к β∈{1,2}, j∈{0,1}, M=0 с импортируемым упорядочением. Дрейф заголовка: STATUS '~25 Qed', фактически 13.

---

## #446 - `src/gauge/DimensionLadder.v` - score 2 (methods)

**Dimension ladder 1D→2D→3D: lattice mass-gap values 0, 3/4, 15/16 and the formula 1−γ^(2·d_sp)**

- **Topic.** Pure synthesis file gathering the K=2 (single-link truncation) transfer-matrix mass-gap values across spatial dimension: 1+1D gap=0 at β=8, 2+1D gap=3/4, 3+1D gap=15/16, plus the closed form gap=1−γ^(2·d_sp). No new computation — re-exports results from Coupled2D/3D, Gap2D/3D, GapBound, ContinuumGap2D.
- **Role.** Top of the K=2 dimension-ladder stack; depends on gauge.Coupled2D, gauge.Coupled3D, gauge.Block3D, gauge.Gap3D, gauge.Gap2D, gauge.TransferMatrix, gauge.GapBound, gauge.ContinuumGap2D. Terminal narrative node — nothing in the catalogued set imports it.
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; gauge.Coupled2D; gauge.Coupled3D; gauge.Block3D; gauge.Gap3D; gauge.Gap2D; gauge.TransferMatrix; gauge.GapBound; gauge.ContinuumGap2D
- **E/R/R.** _Elements:_ конкретные рациональные значения щели mass_gap_2x2 8, mass_gap_2d_at_8=3/4, mass_gap_3d_at_8=15/16; веса w3d 8 0/1; gap_formula d. _Roles:_ пространственная размерность d_sp = роль-параметр лестницы; щель = роль-наблюдаемая (расстояние основной↔возбуждённый); конфайнмент = роль возбуждения. _Rules:_ gap = 1 − γ^(2·d_sp): каждое пространственное измерение добавляет плакетный штраф γ²; строгое возрастание щели с размерностью. _P4:_ всё — конкретные Q-значения при фиксированном β=8 и K=2 (одна ссылка/плакет): Element-сторона (терминирующее vm_compute/lra). Континуальный предел K→∞ и большая решётка N_sp→∞ НЕ достигнуты — это role-limit, честно вынесенный в 'WHAT REMAINS'.
- **Classical counterpart.** Mirrors strong-coupling lattice gauge theory (Wilson 1974) and Osterwalder–Seiler / Hamiltonian K=2 character expansion: a positive mass gap on a finite lattice at fixed coupling. WHAT DIFFERS: exact rational arithmetic (no floating point), a single-link/single-plaquette truncation K=2 at β=8 only, and the slogan formula 1−γ^(2·d_sp) as a finite-lattice pattern — NOT a continuum-limit theorem; the continuum SU(2) Yang–Mills mass gap (Clay problem) is explicitly left open.
- **Tags.** gauge, mass-gap, lattice, dimension-ladder, K=2, exact-Q, synthesis, over-branded-name
- **Notes.** Header STATUS says '~13 Qed' and total_count asserts 13=13; ACTUAL Qed count = 10. Title-level over-branding ('THE COMPLETE RESULT', 'COMPLETE YANG-MILLS DIMENSION STORY') — file verifies finite K=2/β=8 rational facts only; the comment block itself lists the Millennium Problem under 'WHAT REMAINS'.

**Lemmas (10):**

| name | kind | role |
|---|---|---|
| `complete_dimension_comparison` | Theorem | ★ сводка: 1+1D щель=0, 1+1D-континуум 112≤135, 2+1D и 3+1D щель>0, строгий порядок 2D<3D |
| `dimension_values` | Theorem | точные значения mass_gap_2d_at_8=3/4 и mass_gap_3d_at_8=15/16 |
| `confinement_mechanism` | Theorem | механизм: w3d 8 0=1 (основное без штрафа), w3d 8 1=1/4 (возбуждённое со штрафом), щель=15/16 |
| `spatial_coupling_enhances` | Theorem | gap_formula 0/1/2/3 = 0, 3/4, 15/16, 63/64 — щель растёт с числом пространственных измерений |
| `from_existence_to_3d_gap` | Theorem | нарратив 'A=exists → 3+1D щель': целочисленная граница 112≤135 + 2D/3D значения + позитивность |
| `gap_3d_exceeds_1d_continuum` | Theorem | 1/8 < mass_gap_3d_at_8 (3+1D решёточная щель превосходит 1+1D-континуумную оценку 1/8) |
| `dimension_ladder_main` | Theorem | ★ главная сборка лестницы: щель=0/>0/>0, порядок, формула 0,3/4,15/16, превосходство над 1/8 |
| `mass_gap_because_space_exists` | Theorem | 0 < mass_gap_3d_at_8 (щель существует, потому что есть пространство) — псевдоним gap_3d_positive |
| `what_remains` | Theorem | mass_gap_2d_at_8 < mass_gap_3d_at_8 — то, что 'остаётся для Millennium' (на деле лишь строгое неравенство) |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`spatial_coupling_enhances`** - Несущая наблюдательная теорема файла: щель как функция числа пространственных измерений считается замкнутой формулой gap_formula d = 1−(1/4)^d, давая 0, 3/4, 15/16, 63/64. Это аккуратная упаковка паттерна '1 − γ^(2·d_sp)': каждое пространственное измерение умножает вес возбуждённого состояния на γ²=1/4, поэтому щель приближается к 1. Всё доказано делегированием gap_formula_0..3 (lra на Q). Честно: это арифметика конкретных дробей при β=8/K=2, НЕ теорема о континуальной SU(2)-теории. _(dimension-ladder, confinement, K=2, exact-Q)_
- **`dimension_ladder_main`** - Капстоун-сборка: одна конъюнкция, повторяющая щель=0 (1+1D wall), позитивность 2D/3D, строгий порядок 2D<3D, формулу-лестницу и превосходство 3+1D над 1+1D-континуумной 1/8. Чистая ре-экспозиция уже доказанного в Coupled2D/3D/Gap2D/3D — ценность нарративная (нить 'A=exists → mass gap'), не математическая. Комментарий 'WHAT REMAINS: 3+1D K→∞, true SU(2) Haar, N_sp→∞, the Millennium Problem' сам честно фиксирует, что Clay-проблема НЕ закрыта. _(synthesis, narrative, honest-gap, millennium-not-proved)_

**Uniqueness - score 2 (methods).** Аккуратная exact-Q упаковка решёточной щели как функции пространственной размерности с замкнутой формулой gap=1−γ^(2·d_sp) при K=2, β=8.
> _Caveat:_ Конечно-решёточная (K=2, одна ссылка/плакет, β=8) арифметика, НЕ континуальное доказательство. Названия 'COMPLETE'/'Yang-Mills story'/'what_remains' аспирационны: Clay-проблема явно открыта в самом файле. Все 10 лемм — ре-экспорт уже доказанного. Header '~13 Qed' завышен (факт 10).

---

## #447 - `src/gauge/DomainWalls.v` - score 2 (methods)

**Domain-wall combinatorics on binary strings: why the strip gap 3/4 is N-independent (min nonzero wall count = 1)**

- **Topic.** Self-contained combinatorics of binary strings {0,1}^N: domain-wall count d(s)=#adjacent unlike pairs, complement/Hamming/alternating constructions, and the eigenvalue weight (1/4)^d at β=8. The load-bearing fact is the trivial dichotomy 'd∈ℕ, so min nonzero d=1', which makes the strip mass gap 1−1/4=3/4 independent of N.
- **Role.** Standalone leaf: imports only Stdlib (QArith, Lqa, List) — no ToS gauge deps. Supplies the combinatorial justification (min-wall=1) behind the 2+1D strip gap used elsewhere in the ladder; nothing in the catalogued set imports it.
- **Counts.** Qed 37 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa List
- **E/R/R.** _Elements:_ бинарные строки bstring=list bool; конкретные строки [false;true] и т.п.; домен-стены d(s); вес quarter_power n=(1/4)^n. _Roles:_ число доменных стен d = роль-наблюдаемая (заряд возбуждения); униформная/чередующаяся/одно-граничная строка = роли-конфигурации; собственное значение = роль-вес состояния. _Rules:_ d(s)∈ℕ ⟹ либо 0, либо ≥1 (дихотомия); комплемент сохраняет d; чередующаяся достигает максимума n−1; вес монотонно убывает по d. _P4:_ сама дихотомия 'd — натуральное число, значит min ненулевое = 1' (walls_dichotomy, доказывается одним lia) — конечно-актуальная Element-сторона: вот почему щель 3/4 НЕ зависит от длины N. Континуум здесь не при чём — это комбинаторика конечных строк.
- **Classical counterpart.** Mirrors the 1D Ising domain-wall / kink picture (Peierls argument) and the transfer-matrix spectral gap of the 1D Ising strip. WHAT DIFFERS: framed entirely as finite binary-string combinatorics with the gap=3/4 traced to the trivial integrality of the wall count (min nonzero=1) at the single coupling β=8 — a finite-N statement, not a thermodynamic-limit or continuum result; no actual statistical-mechanics partition sum is taken.
- **Tags.** gauge, domain-walls, ising, combinatorics, strip, exact-Q, N-independence, self-contained
- **Notes.** Header STATUS says '~42 Qed'; ACTUAL = 37 (the file's own SUMMARY footer correctly states 'TOTAL: 37 Qed', so the header line is the stale one). 0 ToS imports — fully Stdlib-self-contained leaf.

**Lemmas (46):**

| name | kind | role |
|---|---|---|
| `bstring` | Definition | тип строки = list bool |
| `bdiff` | Definition | индикатор x≠y: 0 если равны, 1 если различны |
| `domain_walls` | Fixpoint | число соседних различных пар в строке |
| `all_same` | Fixpoint | униформная строка из n копий b |
| `all_same_length` | Lemma | длина all_same b n = n |
| `bdiff_sym` | Lemma | bdiff симметричен |
| `bdiff_same` | Lemma | bdiff x x = 0 |
| `bdiff_negb` | Lemma | bdiff x (negb x) = 1 |
| `domain_walls_all_false` | Lemma | униформная false-строка имеет 0 стен |
| `domain_walls_all_true` | Lemma | униформная true-строка имеет 0 стен |
| `complement` | Fixpoint | побитовая инверсия строки |
| `complement_length` | Lemma | комплемент сохраняет длину |
| `bdiff_negb_negb` | Lemma | bdiff (negb x) (negb y) = bdiff x y |
| `complement_preserves_walls` | Theorem | комплемент сохраняет число доменных стен |
| `complement_involutive` | Lemma | комплемент инволютивен |
| `one_boundary` | Definition | строка с одной границей в позиции k: k копий start, потом n−k копий negb start |
| `one_boundary_length` | Lemma | длина one_boundary = n при k≤n |
| `dw_app_uniform` | Lemma | стены конкатенации униформ-разного-значения = 1 (несущий счётный факт) |
| `one_boundary_walls` | Lemma | строка с одной границей имеет ровно 1 стену (1≤k<n) |
| `dw_2_00` | Lemma | конкретно: domain_walls [false;false]=0 |
| `dw_2_01` | Lemma | конкретно: [false;true]=1 |
| `dw_2_10` | Lemma | конкретно: [true;false]=1 |
| `dw_2_11` | Lemma | конкретно: [true;true]=0 |
| `dw_3_001` | Lemma | конкретно: [false;false;true]=1 |
| `dw_3_010` | Lemma | конкретно: [false;true;false]=2 |
| `dw_3_101` | Lemma | конкретно: [true;false;true]=2 |
| `alternating` | Fixpoint | чередующаяся строка start, negb start, ... |
| `alternating_length` | Lemma | длина alternating = n |
| `alternating_walls` | Lemma | чередующаяся строка имеет n−1 стен (максимум) |
| `walls_dichotomy` | Theorem | ★ d(s)=0 ИЛИ 1≤d(s) — тривиальная ℕ-дихотомия, ВСЯ причина N-независимости щели |
| `min_nonzero_walls` | Theorem | d(s)≠0 ⟹ 1≤d(s) (минимальное ненулевое = 1) |
| `hamming_dist` | Fixpoint | расстояние Хэмминга: число позиций различия |
| `hamming_dist_sym` | Lemma | Хэмминг симметричен |
| `hamming_dist_zero` | Lemma | hamming_dist s s = 0 |
| `hamming_dist_complement` | Lemma | hamming_dist s (complement s) = length s |
| `quarter_power` | Fixpoint | (1/4)^n — собственное значение состояния с n стенами при β=8 |
| `qp_0` | Lemma | (1/4)^0 = 1 |
| `qp_1` | Lemma | (1/4)^1 = 1/4 |
| `qp_2` | Lemma | (1/4)^2 = 1/16 |
| `qp_3` | Lemma | (1/4)^3 = 1/64 |
| `qp_positive` | Lemma | (1/4)^n > 0 для всех n |
| `qp_le_one` | Lemma | (1/4)^n ≤ 1 |
| `qp_monotone` | Lemma | m≤n ⟹ (1/4)^n ≤ (1/4)^m (вес монотонно убывает по числу стен) |
| `domain_walls_main` | Theorem | сводка: 0 стен у униформ-100, 1 у [f;t], 2 у [f;t;f] |
| `one_boundary_main` | Theorem | конструкция одной границы даёт ровно 1 стену для обоих start (n≥2) |
| `alternating_max` | Theorem | чередующаяся строка даёт максимум n−1 стен |

**Key lemmas (deep):**

- **`walls_dichotomy`** - Идейное ядро всего файла, доказывается ОДНИМ lia: число доменных стен — натуральное, значит либо 0, либо ≥1. Эта банальность — точная причина, по которой щель полосы 1−(1/4)^d при минимальном ненулевом d=1 равна 1−1/4=3/4 и НЕ зависит от длины N: нет промежуточных значений между 'без стены' и 'одна стена'. Файл сам честно помечает: 'This trivial fact is the ENTIRE reason the gap is N-independent.' Ценность — изоляция этого Element-наблюдения, а не глубина доказательства. _(dichotomy, N-independence, nat-floor, P4)_
- **`qp_monotone`** - Связывает комбинаторику с физикой: вес состояния (1/4)^d монотонно убывает по числу доменных стен, так что больше стен ⟹ меньше вес ⟹ выше энергия. Вместе с min-ненулевым-d=1 это даёт фиксированный зазор между основным (d=0, вес 1) и первым возбуждённым (d=1, вес 1/4). Стандартная монотонность геометрической прогрессии на Q, доказанная индукцией; здесь служит мостом dichotomy→gap. _(eigenvalue, monotone, geometric, gap-bridge)_
- **`complement_preserves_walls`** - Структурная симметрия: глобальная инверсия всех битов сохраняет число доменных стен (через bdiff_negb_negb). Это Z₂-симметрия конфигурационного пространства полосы — основное и возбуждённые состояния приходят инвариантными парами. Чисто комбинаторно, но фиксирует, что 'заряд' d определён на классах по комплементу. _(symmetry, Z2, involution, combinatorics)_

**Uniqueness - score 2 (methods).** Изоляция тривиального ℕ-факта (min ненулевое число доменных стен = 1) как точной причины N-независимости решёточной щели 3/4, с полной комбинаторикой строк (комплемент, Хэмминг, чередование) и весом (1/4)^d.
> _Caveat:_ Стандартная Ising-доменно-стенная картина; всё классично (кинки Пайерлса, расстояние Хэмминга, геометрическая прогрессия). Ново лишь обрамление 'дихотомия ⟹ щель'. Конечно-N, один β=8; НЕ термодинамический предел и НЕ континуум. Header '~42 Qed' завышен — факт 37 (совпадает с собственным TOTAL файла).

---

## #448 - `src/gauge/EigenAnalysis2D.v` - score 2 (methods)

**2D continuum operator: symmetric/antisymmetric block split under x1↔x2, anti-trace 22/105, sym-trace 13/105**

- **Topic.** Decomposes the 2D continuum operator N (from ContinuumMatrix2D) into symmetric (6×6) and antisymmetric (3×3) blocks under the x1↔x2 swap. Defines anti_entry(a,b,c,d)=n(a,b,c,d)−n(a,b,d,c), computes the three antisymmetric diagonal entries, and gets anti-block trace = 22/105, sym-block trace = total−anti = 13/105 (both positive).
- **Role.** Block-analysis layer of the 2D continuum mass-gap branch; imports gauge.ContinuumOperator, gauge.ExtendedAction, gauge.ContinuumMatrix2D (relies on n_entry, e_entry, n_trace, n_trace_value, trace_reduction). Leaf — not imported by the other catalogued files.
- **Counts.** Qed 15 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; gauge.ContinuumOperator; gauge.ExtendedAction; gauge.ContinuumMatrix2D
- **E/R/R.** _Elements:_ матричные элементы n_entry a b c d; антисимметричная комбинация anti_entry; конкретные дроби −58/45, 32/315, 22/105, 13/105. _Roles:_ симметричный/антисимметричный блок = роли-секторы относительно обмена x1↔x2; след блока = роль-инвариант; антисимметричная мода = роль-вектор состояния. _Rules:_ anti_entry(a,b,c,d)=n(a,b,c,d)−n(a,b,d,c) обнуляется на c=c и антисимметрична по (c,d); след_симм = след_полный − след_анти. _P4:_ все элементы и следы — конкретные рациональные числа, вычисленные unfold+simpl+lia (терминирует): Element-сторона. 'Continuum' в имени — это конечная 3×3/6×6 проекция оператора на низкие моды, а НЕ настоящий континуальный предел; собственные значения здесь не извлекаются (только следы).
- **Classical counterpart.** Mirrors symmetry-adapted block-diagonalisation of an operator by irreducible representations of S₂ (the swap group), a standard representation-theory tool; the bound 'ground state 13/15 > 1/9' in the header echoes a coupling-enhancement statement. WHAT DIFFERS: applied to a finite low-mode (3×3 / 6×6) rational truncation of a 'continuum' operator with exact Q entries, extracting only block traces (not eigenvalues) — a finite-dimensional diagnostic, not a continuum spectral theorem.
- **Tags.** gauge, continuum-operator, block-decomposition, S2-symmetry, trace, exact-Q, 2D, spectral-diagnostic
- **Notes.** Header STATUS says '~18 Qed'; ACTUAL = 16. Only block TRACES are computed (no eigenvalue extraction). 'Continuum' refers to a finite low-mode rational truncation, not a continuum limit.

**Lemmas (18):**

| name | kind | role |
|---|---|---|
| `anti_entry` | Definition | антисимметричная под x1↔x2 комбинация n(a,b,c,d)−n(a,b,d,c) |
| `anti_entry_sym_vanishes` | Lemma | anti_entry a b c c = 0 (обнуляется на симметричных индексах) |
| `anti_entry_antisym_cd` | Lemma | anti_entry антисимметрична по (c,d) |
| `n_offdiag_10_01` | Lemma | n_entry 1 0 0 1 = −58/45 |
| `n_offdiag_01_10` | Lemma | n_entry 0 1 1 0 = −58/45 |
| `n_offdiag_20_02` | Lemma | n_entry 2 0 0 2 = 32/315 |
| `n_offdiag_02_20` | Lemma | n_entry 0 2 2 0 = 32/315 |
| `n_offdiag_21_12` | Lemma | n_entry 2 1 1 2 = −12/5 |
| `n_offdiag_12_21` | Lemma | n_entry 1 2 2 1 = −12/5 |
| `anti_diag_10` | Lemma | anti_entry 1 0 1 0 = −22/45 |
| `anti_diag_20` | Lemma | anti_entry 2 0 2 0 = 248/315 |
| `anti_diag_21` | Lemma | anti_entry 2 1 2 1 = −4/45 |
| `anti_trace` | Definition | след антисимметричного блока = сумма трёх диагональных anti_entry |
| `anti_trace_value` | Theorem | ★ anti_trace = 22/105 |
| `sym_trace_value` | Theorem | ★ n_trace − anti_trace = 13/105 (след симметричного блока) |
| `anti_trace_positive` | Theorem | 0 < anti_trace |
| `eigen_analysis_2d_main` | Theorem | сводка: anti=22/105, sym=13/105, оба следа положительны |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`sym_trace_value`** - Несущий результат: след симметричного блока получается вычитанием уже вычисленного anti_trace=22/105 из полного n_trace (импортированного n_trace_value), давая 13/105. Это аккуратное использование инвариантности следа относительно блочной декомпозиции по неприводимым представлениям S₂ (обмен x1↔x2): tr(N)=tr(N_sym)+tr(N_anti). Честно: извлекаются только СЛЕДЫ блоков, не собственные значения, поэтому щель отсюда напрямую не следует — это промежуточный спектральный диагностик. _(block-decomposition, S2-symmetry, trace, exact-Q)_
- **`anti_trace_value`** - Якорная вычислительная теорема: складывает три антисимметричных диагональных элемента −22/45 + 248/315 − 4/45 = 22/105. Каждый диагональный элемент сам доказан unfold+simpl+lia из определений n_entry/e_entry. Демонстрирует, что проекция на 3 антисимметричные моды (\|01⟩−\|10⟩, \|02⟩−\|20⟩, \|12⟩−\|21⟩) даёт положительный след — необходимое (не достаточное) условие положительной щели в этом секторе. _(antisymmetric, trace, computation, spectral-diagnostic)_

**Uniqueness - score 2 (methods).** Симметрийно-адаптированное расщепление конечной рациональной 2D-матрицы на симм/антисимм блоки относительно x1↔x2 с точными следами 22/105 и 13/105.
> _Caveat:_ Стандартная блок-диагонализация по неприводимым представлениям S₂; всё классично. Конечная низкомодовая проекция, НЕ континуальный спектр (несмотря на 'Continuum' в импортах); извлекаются только следы, не собственные значения, поэтому щель отсюда не выводится. Header '~18 Qed' завышен (факт 16).

---

## #449 - `src/gauge/ExactEigenvalues.v` - score 3 (new-framing)

**Characteristic polynomial of the 3×3 continuum operator: λ³−λ²+(2/15)λ+8/135, root λ0=2/3, discriminant 7/15>0**

- **Topic.** Computes the exact characteristic data of the 3×3 continuum operator M (from ContinuumOperator): principal minors (4/9, −64/45, 10/9), cofactor sum 2/15, determinant −8/135, char poly p(λ)=λ³−λ²+(2/15)λ+8/135, verifies λ0=2/3 is a root, factors out the quadratic q(λ)=λ²−λ/3−4/45 with discriminant 7/15>0 (two real roots, opposite signs).
- **Role.** Eigenvalue-analysis layer of the 3×3 continuum branch; imports gauge.ContinuumOperator (uses cont_entry, mat3_mul_entry, kernel_coeff_entry, hilbert_entry, cont_matrix_trace). Leaf — supplies spectral data, not imported by the other catalogued files.
- **Counts.** Qed 22 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; gauge.ContinuumOperator
- **E/R/R.** _Elements:_ элементы матрицы cont_entry i j; главные миноры; коэффициенты char_poly; корень λ0=2/3; дискриминант 7/15. _Roles:_ характеристический многочлен = роль-инвариант спектра; корень λ0 = роль-собственное-значение; дискриминант = роль-индикатор вещественности/кратности корней. _Rules:_ p(λ)=λ³−tr·λ²+(Σкофакторов)·λ−det; λ0=2/3 — корень (135-кратно: 40−60+12+8=0); деление на (λ−2/3) даёт квадратичный фактор; Δ=(1/3)²+4·(4/45)=7/15. _P4:_ весь спектральный анализ — точная рациональная арифметика (unfold/simpl/lia, vm-терминирует): Element-сторона. Сам дискриминант Δ=7/15 НЕ полный квадрат рациональным образом ⟹ два оставшихся собственных значения иррациональны — role-limit-грань (квадратичная иррациональность), как в дискриминантной нити репо (vein A).
- **Classical counterpart.** Mirrors the standard characteristic-polynomial / Cayley–Hamilton spectral computation for a 3×3 matrix (trace, sum of principal 2×2 minors, determinant as poly coefficients) plus the rational-root test and quadratic discriminant. WHAT DIFFERS: done in exact rational arithmetic on a finite 'continuum'-operator truncation, surfacing one rational eigenvalue 2/3 and two irrational ones (disc 7/15 not a perfect square) — an instance of the repo's discriminant Element/role-limit dial, not a generic numerical eigensolver.
- **Tags.** gauge, eigenvalues, char-poly, discriminant, vein-A, exact-Q, 3x3, rational-root, spectral
- **Notes.** Header STATUS says '~25 Qed'; ACTUAL = 23. Bumped to score 3 (not 2) only because the non-square discriminant 7/15 is a clean instance of the repo's discriminant Element/role-limit dial on a concrete gauge operator — otherwise standard linear algebra.

**Lemmas (27):**

| name | kind | role |
|---|---|---|
| `minor_00` | Lemma | главный минор M00 = 4/9 |
| `minor_11` | Lemma | главный минор M11 = −64/45 |
| `minor_22` | Lemma | главный минор M22 = 10/9 |
| `cofactor_sum_value` | Theorem | сумма кофакторов 4/9−64/45+10/9 = 2/15 (коэффициент при λ) |
| `cofactor_sum_positive` | Lemma | 0 < 2/15 |
| `det_value` | Theorem | det(M) = −8/135 (разложение по строке 0) |
| `det_negative` | Lemma | −8/135 < 0 |
| `char_poly` | Definition | p(λ)=λ³−λ²+(2/15)λ+8/135 |
| `char_poly_int` | Definition | целочисленная форма 135·p(λ)=135λ³−135λ²+18λ+8 |
| `char_poly_at_0` | Lemma | p(0)=8/135>0 |
| `char_poly_at_1` | Lemma | p(1)=26/135 |
| `two_thirds_squared` | Lemma | (2/3)²=4/9 |
| `two_thirds_cubed` | Lemma | (2/3)³=8/27 |
| `lambda_0_is_root` | Theorem | ★ p(2/3)=0 (λ0=2/3 — корень) |
| `lambda_0_is_root_int` | Theorem | целочисленная проверка: 135·p(2/3)=40−60+12+8=0 |
| `quadratic_factor` | Definition | q(λ)=λ²−(1/3)λ−4/45 (фактор после деления на λ−2/3) |
| `quadratic_at_0` | Lemma | q(0)=−4/45<0 |
| `quadratic_at_0_negative` | Lemma | q(0)<0 |
| `quadratic_at_2_3` | Lemma | q(2/3)=2/15≠0 (2/3 не кратный корень) |
| `quadratic_at_2_3_positive` | Lemma | 0 < q(2/3) |
| `quad_discriminant` | Definition | Δ = 7/15 |
| `discriminant_value` | Theorem | (1/3)²+4·(4/45)=7/15 (дискриминант квадратичного фактора) |
| `discriminant_positive` | Lemma | 0 < 7/15 (два вещественных корня) |
| `roots_opposite_sign` | Theorem | произведение оставшихся корней −4/45<0 (разные знаки) |
| `roots_sum` | Theorem | сумма оставшихся корней 1/3 (как 0<1/3) |
| `eigenvalues_main` | Theorem | ★ сводка: след=1, кофакторы=2/15, λ0=2/3 корень, Δ=7/15>0 |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`lambda_0_is_root`** - Якорь файла: λ0=2/3 — точный рациональный корень характеристического многочлена p(λ)=λ³−λ²+(2/15)λ+8/135, проверяемый 40−60+12+8=0 над общим знаменателем 135. Это единственное РАЦИОНАЛЬНОЕ собственное значение оператора; дублируется в целочисленной форме (lambda_0_is_root_int) для устойчивого vm-вычисления. Стандартная rational-root проверка кубики; ценность — точное (не приближённое) спектральное значение в рамке exact-Q. _(eigenvalue, rational-root, char-poly, exact-Q)_
- **`discriminant_value`** - Дискриминант квадратичного фактора q(λ)=λ²−λ/3−4/45 равен Δ=(1/3)²+4·(4/45)=7/15>0: два оставшихся собственных значения вещественны и (через roots_opposite_sign, произведение −4/45<0) имеют разные знаки. Поскольку 7/15 не является квадратом рационального, эти два корня ИРРАЦИОНАЛЬНЫ — это прямая инстанция дискриминантной грани Element/role-limit (vein A репо: рациональный корень ⟺ дискриминант — полный квадрат). Связывает конкретный gauge-спектр с центральной нитью проекта. _(discriminant, vein-A, irrational-eigenvalue, real-roots)_

**Uniqueness - score 3 (new-framing).** Точный рациональный спектральный анализ 3×3 gauge-оператора (корень 2/3, дискриминант 7/15), где не-квадратность дискриминанта прямо инстанцирует дискриминантную грань Element/role-limit (vein A) на конкретном физическом операторе.
> _Caveat:_ Сама математика классична (характеристический многочлен, rational-root тест, дискриминант квадратичного). Конечная низкомодовая проекция, НЕ континуальный оператор; два иррациональных корня лишь характеризуются (знак/вещественность), их значения не извлекаются. Header '~25 Qed' завышен (факт 23). Связь с vein A — наблюдение, не новая теорема.

---

## #450 - `src/gauge/ExactMassGap.v` - score 3 (new-framing)

**Mass gap via M=0 character expansion: Δ(β)=I0−2·I2+I4 ≥ 0 on β∈[0,2], = 289/384 at β=1, 1/24 at β=2**

- **Topic.** Proves a positive transfer-matrix mass gap Δ(β)=t0−t1=(I0−I2)−(I2−I4)=I0−2·I2+I4 ≥ 0 for β∈[0,2] at character-expansion truncation order M=0, via Bessel-term dominance I0≥I2≥I4. Computes exact values: Δ(1)=289/384, Δ(2)=1/24, and the eigenvalues t0,t1 at β=1,2.
- **Role.** Gap-positivity layer over the SU(2) character expansion; imports CauchyReal, SeriesConvergence, stdlib.Combinatorics, gauge.SU2Characters, gauge.CharacterTransfer (uses bessel_partial, transfer_eigenvalue, character_mass_gap, I0_dominates_I2, t0_positive_small). Has the standard E/R/R header and a closing Print Assumptions. Leaf among the catalogued set.
- **Counts.** Qed 28 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa List; CauchyReal; SeriesConvergence; stdlib.Combinatorics; gauge.SU2Characters; gauge.CharacterTransfer
- **E/R/R.** _Elements:_ частичные суммы Бесселя bessel_partial n β 0; собственные значения трансфера t0_M0/t1_M0; щель gap_M0 β; конкретные дроби 289/384, 1/24. _Roles:_ t0/t1 = роли-собственные-значения (основное/первое возбуждённое); щель Δ = роль-наблюдаемая; функция Бесселя I_n = роль-вклад характера спина j. _Rules:_ цепь доминирования I0≥I2≥I4 (на β≤2); Δ=t0−t1=I0−2I2+I4; ключевая структурная лемма a+d≤c+b ⟹ a−b≤c−d переносит 2I2≤I0+I4 в упорядочивание собственных значений. _P4:_ ВСЁ ограничено усечением M=0 (нулевой порядок ряда Бесселя) И диапазоном β∈[0,2]: конечно-актуальная Element-сторона (терминирующие nia/lia на Q). Полный ряд (M→∞), произвольное β и континуальный предел НЕ покрыты — это role-limit; файл честно держит 0 аксиом (Print Assumptions в конце).
- **Classical counterpart.** Mirrors the strong-coupling SU(2) character (heat-kernel) expansion of lattice gauge theory, where transfer-matrix eigenvalues are ratios of modified Bessel functions I_n(β) and the mass gap is their leading difference (Wilson / Drouffe–Zuber). WHAT DIFFERS: truncated to character order M=0 and restricted to β∈[0,2], with exact rational Bessel partial sums and the gap proven positive by integer (nia) Bessel-dominance — a finite, conditional positivity statement, not the all-orders / continuum SU(2) mass gap (Clay problem).
- **Tags.** gauge, mass-gap, SU2, character-expansion, bessel, exact-Q, transfer-matrix, 0-axioms, M=0-truncation, over-branded-name
- **Notes.** Header STATUS says '~40 Qed' (twice); ACTUAL = 28 — the largest header drift in this batch. File ends with 'Print Assumptions exact_mass_gap_summary' confirming 0 axioms. Result is explicitly conditional on character-order M=0 and β∈[0,2]; name 'EXACT MASS GAP' is aspirational — not the continuum SU(2) Clay problem.

**Lemmas (35):**

| name | kind | role |
|---|---|---|
| `bessel_ratio_M0` | Definition | отношение соседних бесселевых членов I_{n+2}/I_n при M=0 |
| `bessel_I0_positive` | Lemma | I0(β)>0 при M=0 |
| `I2_over_I0_bound` | Lemma | I2 ≤ I0 для β∈[0,2] (= I0_dominates_I2) |
| `bessel_I4_M0_nonneg` | Lemma | I4 ≥ 0 при β≥0 |
| `I2_dominates_I4` | Lemma | I4 ≤ I2 для β∈[0,2] (ручной Z-вывод через nia) |
| `I4_le_I0` | Lemma | I4 ≤ I0 (транзитивность цепи доминирования) |
| `t0_M0` | Definition | t0 = transfer_eigenvalue 0 β 0 (основное собственное значение) |
| `t1_M0` | Definition | t1 = transfer_eigenvalue 1 β 0 (первое возбуждённое) |
| `gap_M0` | Definition | щель = t0 − t1 |
| `gap_M0_eq` | Lemma | gap_M0 = character_mass_gap β 0 (согласование с импортом) |
| `t0_M0_nonneg` | Lemma | 0 ≤ t0 на β∈[0,2] |
| `t1_M0_nonneg` | Lemma | 0 ≤ t1 на β∈[0,2] |
| `two_I2_le_I0` | Lemma | 2·I2 ≤ I0 (усиленная доминантность, несущая для упорядочивания) |
| `I0_plus_I4_ge_two_I2` | Lemma | 2·I2 ≤ I0 + I4 (ключевое неравенство выпуклости) |
| `Qle_minus_equiv` | Lemma | структурная: a+d≤c+b ⟹ a−b≤c−d в Q (перенос в разности) |
| `eigenvalue_ordering_0_1` | Theorem | ★ t1 ≤ t0 на β∈[0,2] (упорядочивание собственных значений ⟹ щель≥0) |
| `gap_M0_nonneg` | Lemma | 0 ≤ gap_M0 на β∈[0,2] |
| `gap_M0_rational` | Lemma | gap_M0 β — рациональное число (num#den) |
| `gap_at_beta_1` | Lemma | Δ(1)=289/384 |
| `gap_at_beta_1_positive` | Lemma | 0 < Δ(1) |
| `gap_at_beta_2` | Lemma | Δ(2)=1/24 |
| `gap_at_beta_2_positive` | Lemma | 0 < Δ(2) |
| `t0_at_beta_1` | Lemma | t0(1)=7/8 |
| `t1_at_beta_1` | Lemma | t1(1)=47/384 |
| `t0_at_beta_2` | Lemma | t0(2)=1/2 |
| `t1_at_beta_2` | Lemma | t1(2)=11/24 |
| `relative_gap` | Definition | относительная щель = gap_M0/t0_M0 |
| `gap_decomposition` | Lemma | gap_M0 = t0 − t1 (разложение) |
| `gap_positive_from_ordering` | Lemma | t1 ≤ t0 (псевдоним eigenvalue_ordering_0_1) |
| `eigenvalue_sum` | Definition | сумма собственных значений t0 + t1 |
| `eigenvalue_sum_nonneg` | Lemma | 0 ≤ t0 + t1 на β∈[0,2] |
| `eigenvalue_sum_rational` | Lemma | t0 + t1 рационально |
| `partition_approx` | Definition | приближение статсуммы Z ≈ t0 + 3·t1 |
| `partition_approx_nonneg` | Lemma | 0 ≤ partition_approx на β∈[0,2] |
| `exact_mass_gap_summary` | Theorem | ★ сводка: щель≥0 на [0,2], >0 при β=1,2, упорядочивание t1≤t0, оба t≥0 |

**Key lemmas (deep):**

- **`eigenvalue_ordering_0_1`** - Несущая теорема положительности щели: t1≤t0 на β∈[0,2], то есть основное собственное значение трансфер-матрицы превосходит первое возбуждённое, откуда Δ=t0−t1≥0. Доказательство сводит упорядочивание к неравенству выпуклости 2·I2≤I0+I4 (I0_plus_I4_ge_two_I2) через чисто алгебраическую лемму Qle_minus_equiv (a+d≤c+b ⟹ a−b≤c−d над Q). Это и есть содержательное ядро: позитивность щели = доминирование/выпуклость бесселевых членов, а не просто подстановка чисел. ВАЖНО: справедливо лишь при усечении M=0 и β≤2. _(mass-gap, eigenvalue-ordering, bessel-dominance, convexity)_
- **`I2_dominates_I4`** - Базовое звено цепи доминирования I0≥I2≥I4, доказанное вручную спуском к целочисленным неравенствам Z (destruct β, Z.mul_le_mono + nia) — без lra, поскольку отношение I4/I2=(β/2)²/12≤1/12 требует нелинейного рассуждения над Q. Эта аккуратная Z-арифметика типична для gauge-кластера и показывает, что доминантность Бесселя при M=0 — терминирующий конечный факт (Element-сторона), а не аналитическая оценка полного ряда. _(bessel, domination, nia, Z-arithmetic, M=0)_
- **`exact_mass_gap_summary`** - Капстоун-конъюнкция: щель неотрицательна на всём [0,2], строго положительна в двух точках β=1 (289/384) и β=2 (1/24), собственные значения упорядочены и неотрицательны. Завершается Print Assumptions — файл честно демонстрирует 0 аксиом. Однако имя 'EXACT MASS GAP' аспирационно: это положительность щели для SU(2) при НУЛЕВОМ порядке характерного разложения (M=0) и только β∈[0,2], НЕ полный ряд, НЕ континуум, НЕ Clay-проблема. _(synthesis, 0-axioms, honest-truncation, millennium-not-proved)_

**Uniqueness - score 3 (new-framing).** Машинно-проверенная положительность SU(2) щели масс Δ=I0−2I2+I4≥0 как exact-Q бесселева доминантность/выпуклость при усечении M=0, с явными значениями 289/384, 1/24 и 0 аксиом.
> _Caveat:_ Классическая картина (характерное разложение, бесселевы собственные значения трансфера). КРИТИЧНО: только нулевой порядок M=0 И только β∈[0,2]; НЕ полный ряд, НЕ континуальный предел, НЕ Clay Millennium mass gap. Имя 'EXACT MASS GAP' аспирационно. Header '~40 Qed' сильно завышен — факт 28.

---

## #451 - `src/gauge/ExactRGProcess.v` - score 2 (methods)

**Exact RG orbit k |-> exact_rg(K,k,beta) is Q-Cauchy (bounded+increasing, MCT); three methods collapse to one**

- **Topic.** Shows the exact-rational renormalization-group orbit of the 2x2 mass-gap inverse is increasing in k and bounded above by 8, hence Cauchy by the monotone convergence theorem; offers a geometric-contraction route (Method B) and a telescoping route (Method C) that both reduce to the unconditional MCT result.
- **Role.** Convergence wrapper of the gauge RG layer: imports CauchyReal, FixedPoint, MonotoneConvergence and the gauge files TransferMatrix, LargerLattice, GapMatching (which supply exact_rg, exact_rg_orbit, gap_lower_N, gap_inverse, mass_gap_2x2 and the monotonicity/range lemmas). Consumes those to certify the orbit as a real process; a downstream synthesis sink rather than a source.
- **Counts.** Qed 17 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs List Lia ZArith Lqa; ToS: CauchyReal; ToS: FixedPoint; ToS: MonotoneConvergence; ToS: gauge.TransferMatrix; ToS: gauge.LargerLattice; ToS: gauge.GapMatching
- **E/R/R.** _Elements:_ точечные значения орбиты exact_rg_orbit K beta k в Q на стадии k; обратная щель gap_inverse v = 8-4v; стадийная щель gap_lower_N K (2^k) beta. _Roles:_ k-стадия = индекс процесса (L5-порядок приближений); орбита = процесс nat->Q; 8 = верхняя роль-граница (стенка деконфайнмента); коэффициент 4 = липшицев множитель gap_inverse. _Rules:_ монотонность (exact_rg_increasing) + ограниченность (<8) => Cauchy (q_inc_bounded_cauchy/MCT); gap_inverse липшицев с константой 4 (gap_inverse_lipschitz); RG-сдвиг = 4*сдвиг-щели. _P4:_ процесс конечно-актуален: каждая стадия k даёт точное рациональное значение (Element, вычислимо), предел НЕ достигается как завершённый объект — он живёт как Cauchy-процесс (role-limit). Methods B/C формально условны, но сводятся к безусловному MCT: дополнительные гипотезы не несут собственной работы (P4: 'могло бы быть иначе' — нет, A уже всё закрывает).
- **Classical counterpart.** Monotone Convergence Theorem (bounded monotone sequence converges) and the contraction-mapping / telescoping convergence criteria are classical real analysis; NEW here is only the casting of an exact-rational RG orbit on the mass-gap inverse as a Q-Cauchy PROCESS (nat->Q), with convergence carried by the bounded-increasing argument rather than a continuum limit.
- **Tags.** rg-flow, mass-gap, cauchy, MCT, process, exact-Q, monotone
- **Notes.** STATUS header says '~25 Qed'; actual Qed terminators = 18 (drift, fewer). 0 own axioms; classic enters only transitively via MonotoneConvergence. 'Three methods' B/C are non-independent (discard their hypotheses, call Method A).

**Lemmas (19):**

| name | kind | role |
|---|---|---|
| `exact_rg_orbit_increasing` | Lemma | орбита возрастает: exact_rg_orbit K beta k <= ... (S k), для 0<beta<8 |
| `exact_rg_orbit_bounded` | Lemma | орбита ограничена сверху восьмёркой (через exact_rg_lt_8) |
| `exact_rg_orbit_cauchy` | Theorem | ★ орбита Cauchy безусловно через MCT (q_inc_bounded_cauchy с границей 8) |
| `exact_rg_orbit_pos` | Lemma | орбита положительна на каждой стадии |
| `exact_rg_orbit_in_range` | Lemma | орбита остаётся в (0,8) |
| `exact_rg_orbit_at_0` | Lemma | стадия 0 орбиты == beta (exact_rg_0) |
| `gap_contracts` | Definition | условие Method B: щель сжимается геометрически с константой c<1 |
| `gap_inverse_lipschitz` | Lemma | ★ \|gap_inverse v1 - gap_inverse v2\| == 4*\|v1-v2\| (точный липшиц, константа 4) |
| `rg_contracts_if_gap_contracts` | Lemma | если щель сжимается, RG-сдвиги сжимаются с константой 4c |
| `cauchy_from_contraction` | Theorem | Method B: сжатие => Cauchy (на деле игнорирует гипотезу, вызывает MCT) |
| `rg_shift_from_gap` | Lemma | RG-сдвиг == 4 * сдвиг щели (применение gap_inverse_lipschitz) |
| `cauchy_from_telescoping` | Theorem | Method C: телескопирование => Cauchy (тоже сводится к MCT) |
| `three_methods_cauchy` | Theorem | все три метода дают Cauchy (B/C используют A как fallback) |
| `unconditional_cauchy` | Theorem | ★ главный результат: безусловная Cauchy-сходимость орбиты |
| `unconditional_boundedness` | Theorem | exact_rg в (0,8) на каждой стадии (exact_rg_range) |
| `unconditional_gap_positive` | Theorem | щель gap_lower_N K (2^k) beta положительна на каждой стадии |
| `exact_rg_main` | Theorem | сводный: Cauchy + диапазон (0,8) + возрастание + положительность щели |
| `what_exact_rg_proves` | Theorem | процесс корректно определён (num#den) + Cauchy + сохранение щели (gap_matching_preserves_gap) |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`exact_rg_orbit_cauchy`** - Несущая теорема файла: точная орбита RG на обратной щели Cauchy БЕЗУСЛОВНО, потому что она монотонно возрастает и ограничена 8 — чистый монотонный аргумент сходимости (q_inc_bounded_cauchy = MCT над Q-процессами). Это типичный ход gauge-кластера: вместо континуумного предела доказывается, что последовательность точных рациональных стадий есть Cauchy-процесс. Сама сходимость классична (теорема о монотонной ограниченной последовательности); ново только то, что носителем выступает RG-поток масс-щели, выраженный в точной Q-арифметике. _(MCT, cauchy, rg-flow, process)_
- **`gap_inverse_lipschitz`** - Единственная нетривиальная аналитическая лемма: преобразование gap_inverse v = 8 - 4v липшицево с ТОЧНОЙ константой 4 (равенство, не оценка). Это рабочая лошадка обоих условных методов (B даёт 4c, C даёт RG-сдвиг = 4*сдвиг-щели). Тривиально (аффинная функция), но честно вынесено как именованный факт; всё 'сжатие' свелось бы к нему, если бы Methods B/C не были замкнуты через A. _(lipschitz, affine, exact-constant)_
- **`three_methods_cauchy`** - Показательный для честности файла: 'три метода' (безусловный MCT, геометрическое сжатие, телескопирование) ЗАЯВЛЕНЫ как три, но Methods B и C в доказательстве просто отбрасывают свою гипотезу (intros ... _) и зовут exact_rg_orbit_cauchy. То есть содержательно метод один (MCT); B/C — риторическая упаковка, а не независимые маршруты сходимости. Это надо фиксировать в caveat. _(synthesis, redundancy, honesty)_

**Uniqueness - score 2 (methods).** Точная (Q-арифметика) RG-орбита обратной масс-щели предъявлена как монотонно возрастающий ограниченный Cauchy-процесс nat->Q; сходимость несёт MCT над процессами, а не континуумный предел.
> _Caveat:_ Сходимость классична (монотонная ограниченная последовательность). НЕ континуумное доказательство щели масс и НЕ Clay-результат — лишь свойства конкретной рациональной RG-орбиты при 0<beta<8. 'Три метода' вводят в заблуждение: Methods B/C отбрасывают свои гипотезы и сводятся к Method A (MCT), так что независимый маршрут один. Опирается на монотонность/диапазон из импортируемых gauge-файлов (TransferMatrix/LargerLattice/GapMatching), не доказывая их здесь.

---

## #452 - `src/gauge/ExtendedAction.v` - score 1 (exposition)

**Extended action matrix E (3x5): exact-Q coefficients of T1(x^n) in {1,x,x^2} for n=0..4**

- **Topic.** Tabulates, as exact rationals, the coefficients E[i][n] = [x^i] T1(x^n) of the degree-4-truncated continuum transfer operator T1 with kernel k(x,y)=1-4(x-y)^2, checks each of the 15 entries, verifies columns 0-2 agree with ContinuumOperator.v, and checks the five column integrals are positive.
- **Role.** Pure data/verification layer of the continuum-operator branch: imports only gauge.ContinuumOperator (for cont_entry and the matrix helpers). Defines e_entry and col_integral; reused by ExtendedAction7.v (#453), which extends the same matrix to columns 5-6.
- **Counts.** Qed 25 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: gauge.ContinuumOperator
- **E/R/R.** _Elements:_ точные рациональные числа E[i][n] = коэффициент при x^i в T1(x^n); конкретные дроби -1/3, 8/3, -4/5, ...; столбцовые интегралы col_integral n. _Roles:_ i = строка (степень выходного монома 0..2), n = столбец (степень входного монома 0..4); матрица E = таблица действия оператора T1 на базис мономов; rank-3 структура (только {1,x,x^2} на выходе). _Rules:_ E[0][n]=1/(n+1)-4/(n+3), E[1][n]=8/(n+2), E[2][n]=-4/(n+1) — выписаны как замкнутые рациональные формулы; столбцовый интеграл = E0 + E1/2 + E2/3. _P4:_ конечная актуальность в чистом виде: каждая запись — завершённое рациональное число, проверяемое vm_compute/lra; никакого предела или процесса. Оператор T1 имеет конечный ранг 3, поэтому вся бесконечная башня мономов сворачивается в 3x(n+1) таблицу — финитизация по построению, без role-limit.
- **Classical counterpart.** Computing the moments of a fixed integral kernel T1 f(x) = int_0^1 (1-4(x-y)^2) f(y) dy against monomials x^n is elementary calculus (Beta-function / 1/(n+k) rationals); NEW is nothing mathematical, only the packaging as an exact-Q 3x5 coefficient matrix feeding the lattice continuum-operator construction.
- **Tags.** continuum-operator, exact-Q, matrix, kernel-moments, data, rank-3
- **Notes.** STATUS header says '~31 Qed'; actual Qed terminators = 26 (drift, fewer). 0 own axioms. Most proofs are one-line 'unfold e_entry. lra. Qed.' entry-checks.

**Lemmas (28):**

| name | kind | role |
|---|---|---|
| `e_entry` | Definition | матрица E[i][n] (3x5) как match по i,n, возвращающий точную дробь; иначе 0 |
| `e_entry_00` | Lemma | E[0][0] == -1/3 (1/1-4/3) |
| `e_entry_01` | Lemma | E[0][1] == -1/2 |
| `e_entry_02` | Lemma | E[0][2] == -7/15 |
| `e_entry_03` | Lemma | E[0][3] == -5/12 |
| `e_entry_04` | Lemma | E[0][4] == -13/35 |
| `e_entry_10` | Lemma | E[1][0] == 4 (8/2) |
| `e_entry_11` | Lemma | E[1][1] == 8/3 |
| `e_entry_12` | Lemma | E[1][2] == 2 |
| `e_entry_13` | Lemma | E[1][3] == 8/5 |
| `e_entry_14` | Lemma | E[1][4] == 4/3 |
| `e_entry_20` | Lemma | E[2][0] == -4 |
| `e_entry_21` | Lemma | E[2][1] == -2 |
| `e_entry_22` | Lemma | E[2][2] == -4/3 |
| `e_entry_23` | Lemma | E[2][3] == -1 |
| `e_entry_24` | Lemma | E[2][4] == -4/5 |
| `e_matches_cont_col0` | Theorem | столбец 0 матрицы E совпадает с cont_entry из ContinuumOperator.v |
| `e_matches_cont_col1` | Theorem | столбец 1 совпадает с cont_entry |
| `e_matches_cont_col2` | Theorem | столбец 2 совпадает с cont_entry (согласованность 1D) |
| `col_integral` | Definition | столбцовый интеграл int_0^1 T1(x^n) = E0 + E1*(1/2) + E2*(1/3) |
| `col_integral_0` | Lemma | col_integral 0 == 1/3 |
| `col_integral_1` | Lemma | col_integral 1 == 1/6 |
| `col_integral_2` | Lemma | col_integral 2 == 4/45 |
| `col_integral_3` | Lemma | col_integral 3 == 1/20 |
| `col_integral_4` | Lemma | col_integral 4 == 1/35 |
| `col_integral_positive` | Lemma | ★ все столбцовые интегралы (n<=4) положительны (разбор случаев + lra) |
| `extended_action_main` | Theorem | сводный: 1D-согласованность + новые столбцы 3,4 + положительность интегралов 3,4 |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`e_matches_cont_col0`** - Единственная содержательная проверка файла: первые три столбца независимо выписанной матрицы E совпадают с 3x3-матрицей cont_entry из ContinuumOperator.v (через unfold всех вспомогательных определений + lia на Qeq). Это страховка согласованности: расширение до 5 столбцов не противоречит уже построенному 1D-оператору. Остальное — пословная табличная верификация дробей. _(consistency, continuum-operator, cross-check)_
- **`col_integral_positive`** - Чуть более общая лемма, чем точечные: для всех n<=4 столбцовый интеграл положителен, доказано конечным разбором destruct n + lra. Эти интегралы = int_0^1 T1(x^n) dx и их положительность нужна как нормировочная санитарная проверка ядра T1. По сути всё ещё конечная проверка пяти чисел, обёрнутая в forall. _(positivity, normalization, finite-case)_

**Uniqueness - score 1 (exposition).** Точно-рациональная 3x5-таблица коэффициентов конечно-рангового континуум-оператора T1 на мономах, сверенная со смежным 1D-файлом и с положительными столбцовыми интегралами.
> _Caveat:_ Чистая экспозиция/данные: моменты фиксированного полиномиального ядра против мономов — элементарное исчисление (рациональные 1/(n+k)). Никакой новизны, ни щели масс, ни континуумного предела — лишь табуляция и согласованность. Ранг-3 структура (T1(x^n) в span{1,x,x^2}) заявлена, но используется/докажется в ExtendedAction7.v, не здесь.

---

## #453 - `src/gauge/ExtendedAction7.v` - score 1 (exposition)

**Extended action E columns 5-6: T1 has rank 3 for all n, enabling 3+1D tensor eigenvalues (claim)**

- **Topic.** Extends the exact-Q matrix E[i][n] to n=5,6 (falling back to ExtendedAction.e_entry for n<=4), verifies the six new entries and two column integrals, and argues that since T1(x^n) always lies in span{1,x,x^2}, the operator has rank 3 and T1(x)T1(x)T1 on V27 has product eigenvalues.
- **Role.** Thin extension of #452: imports only gauge.ExtendedAction (reuses e_entry). Defines e_entry_ext and col_integral_ext. Terminal leaf of the continuum-operator data branch; the rank-3 / 3+1D-eigenvalue consequence is asserted in prose, not formalized here.
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: gauge.ExtendedAction
- **E/R/R.** _Elements:_ точные дроби E[i][n] для n=5,6 (-1/3, 8/7, -2/3, -19/63, 1, -4/7); столбцовые интегралы col_integral_ext 5 = 1/63, 6 = 1/126. _Roles:_ n=5,6 = новые столбцы той же таблицы действия T1; i=0..2 = три выходных монома; e_entry_ext = расширение e_entry с откатом на старую матрицу при n<=4. _Rules:_ те же формулы E[0][n]=1/(n+1)-4/(n+3), E[1][n]=8/(n+2), E[2][n]=-4/(n+1); ключевое утверждение: ранг T1 = 3 для ВСЕХ n (выход всегда в span{1,x,x^2}). _P4:_ финитизация по построению: бесконечная башня мономов x^n сворачивается оператором конечного ранга 3 в трёхмерный образ — конкретное проявление 'бесконечный вход / конечный актуальный выход' (P4). Спектр T1(x)T1(x)T1 на 27-мерном V27 = произведения трёх 1D собственных значений — но это утверждается в комментарии, формального доказательства тензорного спектра в файле нет.
- **Classical counterpart.** Same elementary kernel-moment computation as ExtendedAction.v, plus the standard fact that a finite-rank operator's tensor power has eigenvalues that are products of the factor eigenvalues; NEW is nothing mathematical — only extending the exact-Q coefficient table to columns 5-6 and stating the rank-3 / 3+1D tensor consequence as a comment-level claim.
- **Tags.** continuum-operator, exact-Q, matrix, kernel-moments, data, rank-3, tensor-product
- **Notes.** STATUS header '~12 Qed' matches actual 12 Qed terminators (no drift). 0 own axioms. The rank-3 and 3+1D tensor-eigenvalue statements are docstring-only, not formalized.

**Lemmas (14):**

| name | kind | role |
|---|---|---|
| `e_entry_ext` | Definition | расширение E на столбцы 5,6 (match по n); n<=4 -> откат на e_entry |
| `e_ext_05` | Lemma | E[0][5] == -1/3 |
| `e_ext_15` | Lemma | E[1][5] == 8/7 |
| `e_ext_25` | Lemma | E[2][5] == -2/3 |
| `e_ext_06` | Lemma | E[0][6] == -19/63 |
| `e_ext_16` | Lemma | E[1][6] == 1 |
| `e_ext_26` | Lemma | E[2][6] == -4/7 |
| `col_integral_ext` | Definition | столбцовый интеграл E0 + E1*(1/2) + E2*(1/3) для расширенной матрицы |
| `col_integral_ext_5` | Lemma | col_integral_ext 5 == 1/63 |
| `col_integral_ext_6` | Lemma | col_integral_ext 6 == 1/126 |
| `col_integral_5_positive` | Lemma | col_integral_ext 5 > 0 |
| `col_integral_6_positive` | Lemma | col_integral_ext 6 > 0 |
| `extended_action_7_main` | Theorem | ★ сводный: шесть записей столбцов 5,6 + положительность двух интегралов (носитель утверждения о ранге 3) |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`extended_action_7_main`** - Сводная теорема файла, но её содержание = шесть проверок дробей + две положительности интегралов; КЛЮЧЕВОЙ вывод ('T1 имеет ранг 3, значит T1^{tensor 3} на V27 имеет собственные значения = произведения 1D') живёт только в docstring и НЕ доказан. То есть файл предъявляет данные, согласные с ранг-3 гипотезой, но не формализует ни сам ранг как теорему, ни тензорный спектр. Это надо честно отметить. _(data, rank-3-claim, informal-consequence)_
- **`e_entry_ext`** - Определение с откатом: для n=5,6 даёт явные дроби, для n<=4 делегирует e_entry из ExtendedAction.v. Аккуратная инкрементальная упаковка (не дублирует старую матрицу), но математически — продолжение той же элементарной таблицы моментов ядра ещё на два столбца. _(extension, fallback, kernel-moments)_

**Uniqueness - score 1 (exposition).** Два дополнительных столбца точно-рациональной таблицы конечно-рангового оператора T1, поддерживающие (но не доказывающие) утверждение о ранге 3 и тензорном спектре для 3+1D.
> _Caveat:_ Экспозиция/данные, ещё тоньше #452 (12 Qed, в основном проверки записей). Ранг-3 и продуктовый спектр T1(x)T1(x)T1 на V27 ЗАЯВЛЕНЫ в комментарии, формально НЕ доказаны. Не щель масс и не континуумный результат. Опирается на e_entry из ExtendedAction.v.

---

## #454 - `src/gauge/ExtendedInterval.v` - score 2 (methods)

**Every orbit of the quadratic RG map f(b)=4b/(1+b) converges for all b>0 (trichotomy at b*=3); gap stays positive**

- **Topic.** Proves that for any b>0 the orbit of rg_map_quadratic converges (Cauchy): below 3 it increases and is bounded by 4, at 3 it is constant at the fixed point, above 3 it decreases and is bounded below by 3; consequently every iterate (n>=1) stays in (0,8) so the SU(2) mass gap is positive ('confinement, no deconfinement').
- **Role.** Convergence + confinement layer of the nonlinear-RG branch: imports CauchyReal, SeriesConvergence, FixedPoint, MonotoneConvergence, RealField and gauge files RGFlow, SU2TransferMatrix, NonlinearRG (which supply rg_map_quadratic, iterate, su2_mass_gap and the f-difference lemmas). A consumer/synthesis file certifying orbit convergence and gap positivity.
- **Counts.** Qed 27 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs List Lia ZArith Lqa; ToS: CauchyReal; ToS: SeriesConvergence; ToS: FixedPoint; ToS: MonotoneConvergence; ToS: RealField; ToS: gauge.RGFlow; ToS: gauge.SU2TransferMatrix; ToS: gauge.NonlinearRG
- **E/R/R.** _Elements:_ точечные значения iterate rg_map_quadratic beta n в Q; неподвижная точка b*=3; масс-щель su2_mass_gap значения. _Roles:_ n = индекс процесса; b*=3 = аттрактор/разделитель трихотомии; 4 = верхняя роль-граница для b<3, 3 = нижняя для b>3, 8 = стенка деконфайнмента; орбита = процесс nat->Q. _Rules:_ f(b)-b == b(3-b)/(1+b) задаёт знак движения (rg_quad_minus_beta); b<3 => возрастание+ограничение => Cauchy (MCT), b>3 => убывание+ограничение снизу => Cauchy, b=3 => постоянная; f(b)<4<8 => положительная щель. _P4:_ конечная актуальность: каждая итерация — точное рациональное значение (Element), предел орбиты = аттрактор-процесс, не завершённый объект (role-limit, кроме b=3, где он достигается за конечное число шагов как точка). 'Нет деконфайнмента' = роль-граница 8 не пересекается ни одной актуальной стадией. Использует classic транзитивно (через MonotoneConvergence) — единственный неконструктивный вход.
- **Classical counterpart.** Convergence of the orbit of the Mobius map f(b)=4b/(1+b) by trichotomy around its fixed point b*=3 (increasing-bounded below 3, constant at 3, decreasing-bounded above 3) is a standard 1D discrete-dynamics / MCT exercise; NEW is only casting each orbit as a Q-Cauchy process and tying f<8 to lattice 'confinement' / positive SU(2) mass gap.
- **Tags.** rg-flow, mass-gap, cauchy, MCT, fixed-point, mobius, confinement, su2, process
- **Notes.** STATUS header says '~30 Qed' (and SUMMARY footer says '~27'); actual Qed terminators = 28. AXIOMS header honestly notes classic via MonotoneConvergence; 0 own axiom declarations. orbit_step_lt_4 and orbit_in_bounds are present but not used by the main chain.

**Lemmas (28):**

| name | kind | role |
|---|---|---|
| `rg_pushes_up` | Lemma | b<3 => b < f(b) (знак b(3-b)/(1+b)>0) |
| `rg_pushes_up_le` | Lemma | b<=3 => b <= f(b) (с равенством в b=3) |
| `rg_pushes_down` | Lemma | b>3 => f(b) < b |
| `rg_pushes_down_le` | Lemma | b>=3 => f(b) <= b |
| `rg_below_3_stays` | Lemma | b<3 => f(b)<3 (инвариантность интервала (0,3)) |
| `rg_above_3_stays` | Lemma | b>3 => f(b)>3 (через rg_quad_diff, монотонность f) |
| `orbit_below_3` | Lemma | орбита из b<3 остаётся в (0,3) (индукция) |
| `orbit_above_3` | Lemma | орбита из b>3 остаётся >3 (индукция) |
| `orbit_inc_below` | Lemma | орбита возрастает при b<3 |
| `orbit_dec_above` | Lemma | орбита убывает при b>3 |
| `orbit_pos` | Lemma | все итерации положительны (rg_quad_pos) |
| `orbit_lt_4_from_1` | Lemma | итерации n>=1 строго меньше 4 |
| `orbit_step_lt_4` | Lemma | f(b)<4 для всех b>0 (= rg_quad_lt_4) |
| `orbit_in_bounds` | Lemma | итерации n>=1 в (0,4) |
| `orbit_cauchy_below` | Lemma | b<3: орбита Cauchy (возрастает+ограничена 4, q_inc_bounded_cauchy) |
| `orbit_cauchy_above` | Lemma | b>3: орбита Cauchy (убывает+ограничена снизу 3, q_dec_bounded_cauchy) |
| `orbit_cauchy_at_3` | Lemma | b=3: постоянная орбита Cauchy (iterate_at_fp) |
| `orbit_cauchy_all` | Theorem | ★ все орбиты для b>0 Cauchy (трихотомия по b vs 3) |
| `orbit_in_gap_range` | Lemma | итерации n>=1 в (0,8) |
| `orbit_gap_positive` | Theorem | ★ масс-щель положительна на каждой итерации n>=1 (su2_mass_gap_positive) |
| `orbit_gap_positive_0` | Lemma | щель положительна на итерации 0 при b<8 |
| `rg_prevents_deconfinement` | Lemma | f(b)<8 для всех b>0 (RG не выводит за стенку) |
| `confinement_via_rg` | Theorem | итерации n>=1 строго меньше 8 (нет деконфайнмента) |
| `double_iterate` | Lemma | f^2(b) == 16b/(1+5b) (явная двойная итерация, field) |
| `mass_gap_all_beta` | Lemma | щель положительна для всех b в (0,8) (= su2_mass_gap_positive) |
| `extended_main` | Theorem | сводный: все орбиты сходятся + щель>0 (n>=1) + нет деконфайнмента |
| `what_step9_proves` | Theorem | сводный: возрастание(b<3)+убывание(b>3)+сходимость+щель>0 |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`orbit_cauchy_all`** - Главная теорема: для ЛЮБОГО b>0 орбита Мёбиус-отображения f(b)=4b/(1+b) есть Cauchy-процесс. Доказательство — трихотомия по b относительно неподвижной точки 3: ниже 3 орбита возрастает и ограничена 4 (MCT), выше 3 убывает и ограничена снизу 3 (MCT), в самой 3 постоянна. Содержательно это стандартная одномерная дискретная динамика сжатия к аттрактору; ценность gauge-кластера — что орбита взята как точный Q-процесс, а не вещественная последовательность, и предел трактуется как процесс (P4). Случай b=beta==3 аккуратно закрыт леммой iterate_qeq о совместимости итерации с Qeq. _(MCT, trichotomy, fixed-point, mobius, process)_
- **`orbit_gap_positive`** - Физическая обёртка сходимости: поскольку каждая итерация (n>=1) лежит в (0,4) подавно в (0,8), SU(2) масс-щель su2_mass_gap положительна на всей орбите — формулируется как 'конфайнмент, нет деконфайнмента'. Это перенос аналитического факта (диапазон (0,8)) на щель через su2_mass_gap_positive из SU2TransferMatrix.v. Сам факт положительности щели на интервале импортирован, не доказан здесь; новое — что он держится вдоль всей RG-орбиты. _(mass-gap, confinement, positivity, su2)_
- **`double_iterate`** - Единственная чисто алгебраическая лемма: f^2(b)==16b/(1+5b), получена field с явной выпиской ненулевых знаменателей. Полезный конкретный факт о композиции (показывает, что итерации Мёбиуса остаются Мёбиус-дробями с растущими коэффициентами), хотя в основной цепочке сходимости не используется. _(mobius, composition, exact-Q)_

**Uniqueness - score 2 (methods).** Полная трихотомическая сходимость орбит Мёбиус-RG-отображения f(b)=4b/(1+b) для всех b>0 как Q-Cauchy-процессов, с переносом на положительность SU(2) масс-щели вдоль орбиты ('нет деконфайнмента').
> _Caveat:_ Динамика классическая: сходимость орбиты к неподвижной точке Мёбиус-отображения трихотомией вокруг b*=3 — стандартное упражнение MCT/одномерной динамики. НЕ континуумное доказательство щели масс и НЕ Clay-результат: это свойства конкретного рационального RG-отображения и конкретной SU(2)-2x2-щели. Положительность щели на (0,8) импортирована из SU2TransferMatrix.v. classic входит транзитивно через MonotoneConvergence.

---

## #455 - `src/gauge/FormalAnalytic.v` - score 1 (exposition)

**Lattice surrogate of OS1: 'analytic' := pointwise representable as num/denom with denom>0; correlations satisfy it (trivially)**

- **Topic.** Defines a lattice analogue of OS1 analyticity (is_lattice_analytic f := forall beta>0, exists num denom, f beta == num/denom /\ 0<denom), shows it is closed under sums/products and holds for constants, transfer eigenvalues, the mass gap and full correlations, then labels the correlation case 'OS1 formal'.
- **Role.** OS1-branch capstone-by-labeling: imports CauchyReal, SeriesConvergence and gauge files CharacterTransfer, ExactMassGap, GapRatio, TransferMatrixProof, CorrelationProof (for transfer_eigenvalue, matrix_mass_gap, gap_ratio, full_correlation and t0 positivity). Ends with Print Assumptions analyticity_summary. A terminal verification/branding file.
- **Counts.** Qed 15 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: CauchyReal; ToS: SeriesConvergence; ToS: gauge.CharacterTransfer; ToS: gauge.ExactMassGap; ToS: gauge.GapRatio; ToS: gauge.TransferMatrixProof; ToS: gauge.CorrelationProof
- **E/R/R.** _Elements:_ функции f:Q->Q (собственные значения, щель, корреляции) и для каждого beta>0 пара (num,denom) с denom>0; конкретные gap_ratio 1, gap_ratio 2. _Roles:_ is_lattice_analytic = предикат-роль 'аналитичность на решётке'; num/denom = представление значения; denom>0 = роль 'нет полюса'; OS1 = имя-роль для случая корреляций. _Rules:_ f аналитична <=> forall beta>0 exists num denom, f beta == num/denom /\ 0<denom; замкнутость относительно + и * (общий знаменатель df*dg>0); любое значение тривиально пишется как x/1. _P4:_ P4-разбор вскрывает безфорсовость: 'аналитичность' определена так слабо, что ЛЮБОЕ значение x удовлетворяет ей через x/1 (denom=1>0) — предикат не различает аналитические и неаналитические функции на (0,inf), а лишь утверждает, что Q есть поле дробей. Содержательная решёточная аналитичность (num,denom — ПОЛИНОМЫ от beta) заявлена в комментариях, но в коде НЕ кодирована: num,denom — произвольные Q, зависящие от beta. Поэтому 'OS1 доказан' — переименование тривиальности, а не выполнение аксиомы.
- **Classical counterpart.** Osterwalder-Schrader axiom OS1 (analyticity of Schwinger functions) and the fact that rational functions with non-vanishing denominator are analytic/meromorphic-without-poles are classical; NEW here is only the lattice surrogate definition 'lattice-analytic on (0,inf) := for every beta>0, f(beta)=num/denom with denom>0' and the trivial observation that everything in sight (eigenvalues, gap, correlations) satisfies it.
- **Tags.** os1, analyticity, lattice, correlations, mass-gap, over-branding, vacuous-predicate, exact-Q
- **Notes.** STATUS header says '~25 Qed'; actual Qed terminators = 15 (drift, fewer). 0 own axioms; file ends with 'Print Assumptions analyticity_summary'. OVER-BRANDING flagged: is_lattice_analytic is satisfied by every f via x/1 (denom=1), so 'OS1 formal' is a renaming, not the OS1 axiom; the polynomial-ratio content is docstring-only.

**Lemmas (18):**

| name | kind | role |
|---|---|---|
| `is_lattice_analytic` | Definition | ★ предикат: forall beta>0, exists num denom, f beta == num/denom /\ 0<denom |
| `is_rational_function` | Definition | дословно тот же предикат (синоним is_lattice_analytic) |
| `rational_is_analytic` | Theorem | rational => analytic (тождественно, exact H) |
| `constant_analytic` | Theorem | константа c аналитична (c/1) |
| `product_analytic` | Theorem | произведение аналитических аналитично (nf*ng / df*dg) |
| `sum_analytic` | Theorem | сумма аналитических аналитична (общий знаменатель) |
| `eigenvalue_is_analytic` | Theorem | собственное значение transfer_eigenvalue j beta M аналитично (через x/1) |
| `gap_ratio_analytic_1` | Theorem | gap_ratio 1 = num/denom с denom>0 (t0_positive_beta_1) |
| `gap_ratio_analytic_2` | Theorem | gap_ratio 2 = num/denom с denom>0 (t0_positive_beta_2) |
| `mass_gap_analytic` | Theorem | matrix_mass_gap J beta 0 аналитична (через x/1) |
| `correlation_is_analytic` | Theorem | ★ full_correlation как функция beta аналитична (через x/1) |
| `os1_formal` | Theorem | ★ 'OS1 формально': корреляции решёточно-аналитичны (= correlation_is_analytic) |
| `os1_formal_at_1` | Theorem | OS1 при beta=1 (специализация) |
| `os1_formal_at_2` | Theorem | OS1 при beta=2 (специализация) |
| `is_continuable` | Definition | 'продолжаемость' := та же решёточная аналитичность |
| `correlations_continuable` | Theorem | корреляции продолжаемы (= correlation_is_analytic) |
| `continuation_preserves_structure` | Theorem | продолжение сохраняет структуру щели (= mass_gap_analytic) |
| `analyticity_summary` | Theorem | сводный: собств.значения + gap_ratio 1 + корреляции + щель — все аналитичны |

**Key lemmas (deep):**

- **`is_lattice_analytic`** - Несущее (и проблемное) определение всего файла. Заявлено как решёточный аналог OS1: 'f(beta)=num/denom с положительным знаменателем, нет полюсов'. Но num,denom здесь — ПРОИЗВОЛЬНЫЕ рациональные, зависящие от beta, а не полиномы фиксированной степени. Поэтому предикат выполняется для ВСЯКОЙ f:Q->Q тривиально (x = x/1, denom=1>0) — он не несёт никакой аналитической информации, лишь повторяет, что Q — поле. Содержательная версия (num,denom полиномиальны) описана в комментарии, но не закодирована. Это центральная честностная проблема файла. _(os1, definition, vacuous, over-branding)_
- **`os1_formal`** - 'OS1 FORMAL: корреляции решёточно-аналитичны' — звучит как выполнение аксиомы Остервальдера-Шрадера OS1. Фактически доказательство = correlation_is_analytic, где корреляция представлена как full_correlation/1 (denom=1). То есть OS1 'доказана' переименованием тождества x=x/1. Реальная аналитичность корреляции (она есть Qpow рациональной дроби) НЕ извлечена. Сильный кандидат на флаг over-branding: имя OS1/'formal' аспирационно. _(os1, correlation, renaming, over-branding)_
- **`product_analytic`** - Единственные две леммы с реальным содержанием (product_analytic, sum_analytic): замкнутость предиката относительно умножения и сложения через общий знаменатель df*dg>0 (Qmult_lt_0_compat) и field. Это настоящие, хоть и элементарные, факты о дробях; они были бы осмысленны, если бы базовый предикат не был вырожденным. В текущем виде — корректная алгебра над пустым по сути предикатом. _(closure, field, honest-fragment)_

**Uniqueness - score 1 (exposition).** Решёточный суррогат аксиомы OS1 (аналитичность = поточечная представимость num/denom с denom>0), замкнутый относительно +/*, и применённый к собственным значениям, щели масс и корреляциям.
> _Caveat:_ OVER-BRANDING: определение is_lattice_analytic вырождено — num,denom произвольны, так что ЛЮБАЯ f:Q->Q удовлетворяет ему тривиально через x/1; предикат не различает аналитичность, а лишь констатирует, что Q — поле. 'os1_formal'/'OS1 FORMAL' — переименование тождества, а НЕ выполнение аксиомы Остервальдера-Шрадера. Содержательная (полиномиальная) аналитичность заявлена только в комментариях. Реально нетривиальны лишь sum/product-замкнутость (элементарная алгебра дробей). Не континуумная аналитичность и не Clay-результат.

---

## #456 - `src/gauge/FormalSO4.v` - score 1 (exposition)

**OS3 (SO(4)-инвариантность) как тривиальность: функция расстояния автоматически изометрична**

- **Topic.** Определяет is_SO4_invariant f := forall d1 d2, d1=d2 -> f d1 == f d2 и доказывает, что ВСЯКАЯ функция nat->Q ей удовлетворяет; затем переносит это на корреляции full_correlation как формальную проверку аксиомы Остервальдера-Шрадера OS3.
- **Role.** Лист программы доказательства mass-gap (Остервальдер-Шрадер). Зависит от gauge.CharacterTransfer, ExactMassGap, GapRatio, TransferMatrixProof, CorrelationProof, CovarianceProof. Парный с FormalTempered (OS2). Дальше почти не переиспользуется — терминальный «отчёт по OS3».
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: CauchyReal; ToS: SeriesConvergence; ToS: gauge.CharacterTransfer; ToS: gauge.ExactMassGap; ToS: gauge.GapRatio; ToS: gauge.TransferMatrixProof; ToS: gauge.CorrelationProof; ToS: gauge.CovarianceProof
- **E/R/R.** _Elements:_ корреляции full_correlation J t j beta M как функции расстояния-разделения t : nat; степенной свидетель Qpow r t. _Roles:_ is_SO4_invariant / depends_only_on_distance — предикаты-роли «быть изометрически инвариантным» / «зависеть только от расстояния»; t играет роль \|x\| (модуля разделения). _Rules:_ f изометрична <-> (d1=d2 -> f d1 == f d2); функция от \|x\| инвариантна автоматически; G(t) == r^t (степенной закон из transfer-матрицы). _P4:_ Element-сторона тривиальна по построению: решётка дискретна, t — это УЖЕ скаляр-расстояние (конечный nat), поэтому никакого вращения переносить не нужно — непрерывная группа SO(4) свёрнута до рефлексивности равенства nat. Честно: это не действие группы, а наблюдение, что параметризация по скаляру делает инвариантность бессодержательной.
- **Classical counterpart.** Аксиома Остервальдера-Шрадера OS3 (евклидова/вращательная инвариантность, SO(d)) из конструктивной QFT и теорема о том, что радиальные функции инвариантны относительно O(n). Отличие здесь: НЕ доказано действие группы SO(4) на полевых конфигурациях и инвариантность относительно него; вместо этого решёточная корреляция параметризована скаляром-расстоянием, и «инвариантность» вырождается в рефлексивность равенства nat — формальная галочка, а не реконструкция OS3.
- **Tags.** gauge, mass-gap, osterwalder-schrader, OS3, SO4, over-branding, trivial, lattice, plumbing
- **Notes.** Header STATUS заявляет «~15 Qed» — фактически 9 Qed (приблизительная оценка автора, дрейф ~15->9). 0 Admitted, 0 axioms (Print Assumptions so4_summary в конце). Несколько теорем (distance_implies_SO4, os3_full_argument) игнорируют свои гипотезы через _ и закрываются apply SO4_invariant_trivial — подтверждает тривиальность содержания.

**Lemmas (11):**

| name | kind | role |
|---|---|---|
| `is_SO4_invariant` | Definition | предикат: f d1 == f d2 когда d1=d2 (изометрическая инвариантность как функция расстояния) |
| `SO4_invariant_trivial` | Lemma | ★ ВСЯКАЯ f : nat->Q тривиально SO(4)-инвариантна (через rewrite Heq) |
| `depends_only_on_distance` | Definition | f факторизуется через \|.\|: exists g, forall t, f t == g t |
| `any_function_of_distance` | Lemma | всякая f от nat зависит только от расстояния (свидетель g:=f) |
| `distance_implies_SO4` | Theorem | зависимость от расстояния => SO(4)-инвариантность (сводится к SO4_invariant_trivial) |
| `correlation_SO4` | Theorem | корреляция при фикс. параметрах SO(4)-инвариантна как функция t |
| `os3_formal` | Theorem | ★ OS3 FORMAL: корреляции SO(4)-инвариантны (= correlation_SO4) |
| `os3_with_witness` | Theorem | OS3 + свидетель ковариантности G(t) == r^t с r = dm_entry j / dm_entry 0 |
| `os3_full_argument` | Theorem | полный аргумент OS3 шаги 1-4 (но при гипотезе игнорируемой через _) |
| `wilson_action_isotropic` | Theorem | изотропия действия Вильсона как рефлексивность собственного значения (transfer_eigenvalue j beta M == себе) |
| `so4_summary` | Theorem | сводка: все корреляции инвариантны + факторизуются через расстояние + имеют степенной свидетель |

**Key lemmas (deep):**

- **`SO4_invariant_trivial`** - Несущая лемма и одновременно источник over-branding: всё содержание «SO(4)-инвариантности» сведено к forall f, d1=d2 -> f d1 == f d2, что доказывается одним rewrite Heq для ЛЮБОЙ функции nat->Q. Это не теорема о группе вращений SO(4) и не действие группы — это наблюдение, что при параметризации корреляции единственным скаляром-расстоянием t инвариантность относительно изометрий становится бессодержательной (рефлексивность равенства nat). Честная ценность мизерна; имя os3_formal обещает аксиому Остервальдера-Шрадера, файл доказывает тавтологию. _(over-branding, trivial, OS3, isometry, plumbing)_
- **`os3_with_witness`** - Единственная лемма с реальным содержанием сверх тривиальности: предъявляет степенной свидетель G(t) == Qpow r t с r = (j-я диагональ transfer-матрицы)/(0-я диагональ) — то есть переносит результат CovarianceProof (G_j(t)=r_j^t из диагонализации transfer-матрицы) в формат OS3. Само равенство закрывается unfold full_correlation; reflexivity, так что вся работа сделана в импортируемых файлах. Это плита-переходник, а не новый факт. _(transfer-matrix, power-law, witness, bridge)_

**Uniqueness - score 1 (exposition).** Формальная запись «OS3 (SO(4)-инвариантность)» для решёточных корреляций как функций скаляра-расстояния, со степенным свидетелем из transfer-матрицы.
> _Caveat:_ OVER-BRANDED. SO4_invariant_trivial показывает, что вся «SO(4)-инвариантность» тут = forall f, d1=d2 -> f d1==f d2 (тривиально для любой nat->Q); это НЕ действие группы вращений и НЕ восстановление аксиомы OS Остервальдера-Шрадера. Решёточный, не континуумный; реальное содержание (G=r^t) импортировано из CovarianceProof. Header «~15 Qed» — фактически 9.

---

## #457 - `src/gauge/FormalTempered.v` - score 2 (methods)

**OS2 (умеренность) на решётке: |G|<=1 ограничено, связные корреляции — Шварц (экспоненциальный спад)**

- **Topic.** Определяет is_tempered (ограниченность |f|<=C) и is_schwartz_lattice (|f t|<=r^t, 0<r<1) и доказывает: основная корреляция ограничена 1, возбуждённая — Шварц с r=gap_ratio, откуда умеренна; формальная проверка аксиомы Остервальдера-Шрадера OS2.
- **Role.** Лист программы Остервальдера-Шрадера (OS2), парный с FormalSO4 (OS3). Зависит от gauge.CharacterTransfer, ExactMassGap, GapRatio, TransferMatrixProof, ClusterProof, CorrelationProof. Терминальный «отчёт по OS2».
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: CauchyReal; ToS: SeriesConvergence; ToS: gauge.CharacterTransfer; ToS: gauge.ExactMassGap; ToS: gauge.GapRatio; ToS: gauge.TransferMatrixProof; ToS: gauge.ClusterProof; ToS: gauge.CorrelationProof
- **E/R/R.** _Elements:_ решёточные функции f : nat->Q (корреляции full_correlation); константа C>0; коэффициент спада r in (0,1); степень Qpow r t. _Roles:_ is_tempered / is_schwartz_lattice — роли классов роста (умеренный=ограниченный / Шварц=экспоненциально спадающий); gap_ratio играет роль коэффициента спада. _Rules:_ ограничено => умеренно (полиномиальный рост степени 0); Шварц => умеренно (r^t<=1 при 0<r<1 через Qpow_bound_1); G_0(t)=1, G_1(t)=gap_ratio^t. _P4:_ Element-сторона: на дискретной решётке «умеренность» = простая ограниченность \|G\|<=1 (конечно-актуальный факт, проверяемый на каждом t), а не распределение умеренного роста на R^d. Спад до 0 формулируется как достижимость (forall eps, exists t0, \|f t0\|<eps) — это потенциальный, не завершённый предел: процесс приближается к 0, не достигая. Честно: ограничено СИЛЬНЕЕ умеренного, поэтому OS2 здесь — с запасом, но в решёточной, не континуумной постановке.
- **Classical counterpart.** Аксиома Остервальдера-Шрадера OS2 (умеренность: швингеровские функции суть распределения умеренного роста) и характеризация Шварца через экспоненциальный спад; кластерное свойство QFT (спад связных функций <=> щель масс). Отличие: доказана решёточная ограниченность \|G\|<=1 и экспоненциальный спад gap_ratio^t для конкретного beta=1, а НЕ умеренность континуумных распределений; это с-запасом проверка на дискретной решётке, опирающаяся на импортированную диагонализацию transfer-матрицы.
- **Tags.** gauge, mass-gap, osterwalder-schrader, OS2, tempered, schwartz, cluster-property, over-branding, lattice
- **Notes.** Header STATUS заявляет «~20 Qed» — фактически 11 Qed (дрейф ~20->11). 0 Admitted, 0 axioms (Print Assumptions tempered_summary). Бренд «OS2 formal» аспирационен: умеренность здесь = решёточная ограниченность, не континуумная аксиома OS.

**Lemmas (13):**

| name | kind | role |
|---|---|---|
| `is_tempered` | Definition | f умеренна: exists C>0, forall t, Qabs (f t) <= C (ограниченность) |
| `bounded_is_tempered` | Lemma | ограниченность => умеренность (свидетель C:=C) |
| `is_schwartz_lattice` | Definition | f есть Шварц: exists r, 0<r<1 /\ forall t, Qabs (f t) <= Qpow r t |
| `schwartz_is_tempered` | Lemma | ★ Шварц => умеренна (через r^t<=1, Qpow_bound_1) |
| `constant_tempered` | Lemma | константа умеренна (граница \|c\|) |
| `ground_correlation_tempered_1` | Theorem | основная корреляция G_0 ограничена 1 при beta=1 (через correlation_le_1 + correlation_nonneg) |
| `excited_correlation_schwartz_1` | Theorem | ★ возбуждённая G_1 = gap_ratio^t есть Шварц при beta=1 (через correlation_eq_ratio) |
| `excited_correlation_tempered_1` | Theorem | возбуждённая умеренна через Шварц (beta=1) |
| `os2_formal_at_1` | Theorem | OS2 для j in {0,1} при beta=1 (разбор случаев) |
| `os2_formal` | Theorem | ★ OS2 FORMAL для общего j: \|G\|<=1 => умеренна (correlation_abs_bounded) |
| `os2_stronger_than_needed_1` | Theorem | связные корреляции — Шварц, сильнее умеренности (= excited_correlation_schwartz_1) |
| `schwartz_implies_decay` | Theorem | Шварц => спад к 0: forall eps>0, exists t0, \|f t0\|<eps (Qpow_vanish) |
| `tempered_summary` | Theorem | сводка: G_0 ограничена / G_1 Шварц / G_1 умеренна |

**Key lemmas (deep):**

- **`excited_correlation_schwartz_1`** - Содержательное ядро файла: возбуждённая корреляция G_1(t) ТОЧНО равна gap_ratio^t (через correlation_eq_ratio из transfer-матрицы), а 0<gap_ratio<1 (mass gap положителен), поэтому она экспоненциально спадает = Шварц. Это решёточная форма кластерного свойства (экспоненциальный спад связных корреляций <=> щель масс) и единственное место, где OS2 опирается на реальную физику (gap_ratio_lt1_beta_1). Само неравенство, однако, импортирует всю работу из GapRatio/CorrelationProof; здесь только переупаковка в формат Шварца. _(schwartz, exponential-decay, mass-gap, cluster-property, transfer-matrix)_
- **`os2_formal`** - Несущая «галочка OS2» для общего j: умеренность выводится из \|G\|<=1 (correlation_abs_bounded) одним exists 1 + apply. Подчёркивает честный, но скромный смысл файла: на решётке OS2 (умеренность) — это просто равномерная ограниченность корреляций единицей, что СИЛЬНЕЕ умеренного роста, но в дискретной постановке и без реконструкции континуумного распределения умеренного роста. _(OS2, boundedness, tempered, bridge)_

**Uniqueness - score 2 (methods).** Решёточная формализация OS2: умеренность=ограниченность |G|<=1, плюс усиление до Шварца (экспоненциальный спад gap_ratio^t) для связных корреляций, связывающее спад со щелью масс.
> _Caveat:_ OVER-BRANDED именем «OS2 formal»: доказывает решёточную ограниченность/спад для конкретного beta=1, НЕ умеренность континуумных распределений Остервальдера-Шрадера. Кластерное свойство и спад<=>щель классичны; содержание (G=gap_ratio^t) импортировано из GapRatio/CorrelationProof. Header «~20 Qed» — фактически 11.

---

## #458 - `src/gauge/Gap2D.v` - score 3 (new-framing)

**Щель масс 2+1D = 3/4 при beta=8: пространственная плакетка создаёт щель там, где 1+1D даёт 0**

- **Topic.** Доказывает на конкретной transfer-матрице, что в 2+1D при beta=8 щель = 1-1/4 = 3/4 > 0 (тогда как 1+1D даёт 0), и что щель антисимметричного сектора gap_antisymmetric(beta) = (1-alpha^2)(1-gamma^2) > 0 для всех 0<beta<8.
- **Role.** Узел dimension-ladder программы mass-gap. Зависит от gauge.Coupled2D, BlockDiagonal2D, TransferMatrix (mass_gap_2x2, eigenvalue_minus, gamma_2d, alpha_2d). Переиспользуется Gap3D (mass_gap_2d_at_8, gap_2d_positive) для строгого порядка щелей по размерности.
- **Counts.** Qed 17 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: gauge.Coupled2D; ToS: gauge.BlockDiagonal2D; ToS: gauge.TransferMatrix
- **E/R/R.** _Elements:_ собственные значения transfer-матрицы (eigenvalue_minus, eigenvalue_q); параметры решётки alpha_2d, gamma_2d; конкретные значения beta in {1,7,8}; щель mass_gap_2d_at_8 = 3#4. _Roles:_ gap_antisymmetric — роль «щель антисимметричного сектора»; beta=8 играет роль критической связи (континуумная точка RG-орбиты); пространственная плакетка — роль источника щели. _Rules:_ щель = lambda_max - lambda_next = (1-alpha^2)(1-gamma^2); eigenvalue_minus=(beta/8)(2-beta/8); 1-gamma^2=(beta/16)(2-beta/16); произведение положительных положительно. _P4:_ Чисто Element-вычисление: каждое утверждение — точная рациональная арифметика на КОНКРЕТНОЙ малой (блочной) transfer-матрице при конкретных beta, закрываемая lra/ring/vm_compute-стилем. «Континуумный предел» beta_k->8 и щель->3/4 заявлены в комментариях как RG-орбита, но формально проверены лишь финитно (точка beta=8 и положительность на интервале), без построения процесса-последовательности и без доказательства, что это и есть континуумная YM-щель.
- **Classical counterpart.** Гипотеза о щели масс в Yang-Mills (Clay Millennium) и решёточное наблюдение, что 1+1D калибровочная теория тривиальна (нет поперечных глюонов), а d>=3 даёт щель/конфайнмент. Отличие: здесь точное Q-вычисление на КОНКРЕТНОЙ блок-диагональной transfer-матрице при beta=8 (и положительность на (0,8)) для специфической решёточной модели — это НЕ доказательство континуумной YM-щели и не Millennium; «RG-орбита beta->8» лишь прокомментирована, не построена как процесс.
- **Tags.** gauge, mass-gap, lattice, transfer-matrix, dimension-ladder, 2+1D, exact-rational, vm_compute, finite-lattice
- **Notes.** Header STATUS заявляет «~20 Qed» — фактически 18 Qed (близко, дрейф ~20->18). 0 Admitted, 0 axioms. total_count — reflexivity-маркер конца (не содержательная лемма). Local Lemma Qmult_pos локальна для файла.

**Lemmas (20):**

| name | kind | role |
|---|---|---|
| `mass_gap_2d_at_8` | Definition | константа щели 2+1D при beta=8 := 3#4 |
| `gap_2d_value` | Theorem | 1 - 1/4 == 3/4 (значение щели как разность собственных значений) |
| `gap_2d_positive` | Theorem | 0 < 3/4 (положительность щели) |
| `dimension_upgrade` | Theorem | ★ ключевое сравнение: 1+1D щель = 0, 2+1D щель = 3/4 > 0 |
| `gap_antisymmetric` | Definition | щель антисимм. сектора beta := eigenvalue_minus*(1-gamma^2) |
| `gap_anti_formula` | Lemma | gap_antisymmetric == eigenvalue_minus - eigenvalue_q (через ring) |
| `gap_anti_at_8` | Lemma | gap_antisymmetric 8 == 3/4 (vm_compute-арифметика) |
| `one_minus_sq_factor` | Lemma | 1-(1-x)^2 == x(2-x) (тождество ring) |
| `eigenvalue_minus_factored` | Lemma | eigenvalue_minus == (beta/8)(2-beta/8) |
| `one_minus_gamma_sq_factored` | Lemma | 1-gamma^2 == (beta/16)(2-beta/16) |
| `Qmult_pos` | Local Lemma | произведение положительных положительно (хелпер) |
| `gap_2d_positive_all_beta` | Theorem | ★ щель > 0 для всех 0<beta<8 (произведение двух положительных факторов) |
| `spatial_coupling_enhances_gap` | Theorem | 2+1D щель (3/4) > 1+1D континуумной щели (1/8) |
| `gap_anatomy` | Theorem | щель == 1-gamma^2 при beta=8 (т.к. eigenvalue_minus=1) |
| `gap_anti_positive_at_1` | Lemma | 0 < gap_antisymmetric 1 (инстанс при beta=1) |
| `gap_less_at_1` | Lemma | gap_antisymmetric 1 < 3/4 (щель растёт с beta) |
| `gap_2d_survives_rg` | Theorem | щель в пределе beta=8 = 3/4 > 0 (выживает RG) |
| `gap_continuity_at_8` | Theorem | 0 < gap_antisymmetric 7 (непрерывность около 8) |
| `gap_2d_main` | Theorem | ★ сводка: 1+1D=0, 2+1D=3/4, >0 на (0,8), 3/4>1/8 |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`gap_2d_positive_all_beta`** - Главный нетривиальный результат файла: щель антисимметричного сектора положительна на ВСЁМ интервале связи 0<beta<8, а не только в точке beta=8. Доказательство честное и аккуратное: факторизует eigenvalue_minus=(beta/8)(2-beta/8) и 1-gamma^2=(beta/16)(2-beta/16), показывает положительность каждого фактора через Qmult_pos+lra и берёт произведение. Это реальное физическое наблюдение (пространственная плакетка раскрывает щель), но строго о конкретной модели блок-диагональной transfer-матрицы 2+1D, НЕ о континуумной SU(N) YM. _(mass-gap, all-beta, factorization, antisymmetric-sector, honest)_
- **`dimension_upgrade`** - Концептуальное ядро: контраст 1+1D (щель=0 при beta=8, через gap_vanishes_at_8) против 2+1D (щель=3/4>0). Это формальное подтверждение, что добавление пространственного измерения (лишней плакетки) КАЧЕСТВЕННО меняет спектр — щель рождается из размерности. Содержательное наблюдение dimension-ladder, но это сравнение двух явно вычисленных малых решёточных моделей, а не теорема о размерностной зависимости континуумной щели. _(dimension-ladder, comparison, spatial-plaquette, synthesis-lite)_

**Uniqueness - score 3 (new-framing).** Размерностная лестница щели как точные рациональные факты: 1+1D=0, 2+1D=3/4 при beta=8, со строгой положительностью на всём интервале 0<beta<8 и анатомией щели = (1-alpha^2)(1-gamma^2).
> _Caveat:_ Конечно-решёточное Q-вычисление на конкретной блок-диагональной transfer-матрице 2+1D, НЕ континуумный YM и НЕ Clay Millennium. Значение 3/4 и «выживание RG» привязаны к точке beta=8 и модели; континуумный предел прокомментирован, но формально не построен как процесс-последовательность. Header «~20 Qed» — фактически 18.

---

## #459 - `src/gauge/Gap3D.v` - score 3 (new-framing)

**Щель масс 3+1D = 15/16 при beta=8 и лестница размерности gap = 1-(1/4)^d_sp**

- **Topic.** Доказывает на конкретной блок-матрице, что в 3+1D при beta=8 щель = 1-1/16 = 15/16, выстраивает лестницу размерности 0->0, 1->3/4, 2->15/16, 3->63/64 и фиксирует замкнутую формулу gap_formula(d_sp) = 1-(1/4)^d_sp при gamma=1/2.
- **Role.** Вершина dimension-ladder программы mass-gap. Зависит от gauge.Coupled2D, Coupled3D, Block3D, Gap2D, TransferMatrix (even_block_00/11, w3d, mass_gap_2x2, mass_gap_2d_at_8). Терминальный — задаёт формулу щели по числу пространственных измерений.
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: gauge.Coupled2D; ToS: gauge.Coupled3D; ToS: gauge.Block3D; ToS: gauge.Gap2D; ToS: gauge.TransferMatrix
- **E/R/R.** _Elements:_ блоки even_block_00=2, even_block_11=6/16 при beta=8; веса конфайнмента w3d 8 0=1, w3d 8 1=1/4; число пространственных измерений d_sp : nat; щель mass_gap_3d_at_8 = 15#16. _Roles:_ gap_formula / gamma_sq_power — роль «щель как функция размерности» / «(1/4)^d_sp»; d_sp играет роль уровня лестницы; основное состояние (вес 1) vs возбуждённое (штраф 1/4) — роль конфайнмента. _Rules:_ щель = 1 - (1/4)^d_sp (при gamma=1/2); gamma_sq_power(S m)=(1/4)*gamma_sq_power m; собственные значения 1 (основное) и 1/16 (возбуждённое) из чётного блока. _P4:_ Element-вычисление на дискретной решётке: лестница построена как ОТДЕЛЬНЫЕ точные значения при d_sp=0,1,2,3 (gap_formula_0..3 через vm_compute/lia), а не как доказанная по индукции общая закономерность 1-(1/4)^d_sp для произвольного d_sp. Замкнутая формула определена (Fixpoint gamma_sq_power), но согласие с щелью доказано лишь для конечного набора уровней; континуумная интерпретация и произвольная размерность — за границей формализации.
- **Classical counterpart.** Гипотеза щели масс Yang-Mills (Clay) и общее ожидание, что щель/конфайнмент усиливаются с размерностью; геометрическая прогрессия штрафов площади в strong-coupling разложении. Отличие: точные Q-значения щели для d_sp=0,1,2,3 на конкретных блок-матрицах + замкнутая формула 1-(1/4)^d_sp, проверенная на этих уровнях, а НЕ доказанная индуктивно для всех d_sp и НЕ континуумный YM/Millennium.
- **Tags.** gauge, mass-gap, lattice, transfer-matrix, dimension-ladder, 3+1D, confinement, exact-rational, finite-lattice
- **Notes.** Header STATUS заявляет «~15 Qed» — фактически 14 Qed (дрейф минимальный ~15->14). 0 Admitted, 0 axioms. total_count — reflexivity-маркер конца. gap_formula_matches охватывает d_sp=0,1,2 (не 3); согласие формулы с щелью доказано только финитно, не индукцией.

**Lemmas (17):**

| name | kind | role |
|---|---|---|
| `mass_gap_3d_at_8` | Definition | константа щели 3+1D при beta=8 := 15#16 |
| `gap_3d_value` | Theorem | 1 - 1/16 == 15/16 (значение щели) |
| `gap_3d_positive` | Theorem | 0 < 15/16 (положительность) |
| `gap_from_eigenvalues` | Theorem | ★ щель из собственных значений чётного блока: ground=1*2, excited=(1/16)*6, gap=15/16 |
| `dimension_ladder_at_8` | Theorem | ★ лестница: 1+1D=0, 2+1D=3/4>0, 3+1D=15/16>0 |
| `gap_increases_with_dimension` | Theorem | строгий порядок 3/4 < 15/16 |
| `gap_3d_exceeds_all` | Theorem | 3+1D щель превосходит обе младшие (0 и 3/4) |
| `gamma_sq_power` | Fixpoint | (1/4)^d_sp рекурсивно (gamma=1/2 => gamma^2=1/4) |
| `gap_formula` | Definition | щель := 1 - (1/4)^d_sp |
| `gap_formula_0` | Theorem | gap_formula 0 == 0 |
| `gap_formula_1` | Theorem | gap_formula 1 == 3/4 |
| `gap_formula_2` | Theorem | gap_formula 2 == 15/16 |
| `gap_formula_3` | Theorem | gap_formula 3 == 63/64 |
| `gap_formula_matches` | Theorem | ★ формула согласована с вычисленными щелями (d_sp=0,1,2) |
| `confinement_weights` | Theorem | веса конфайнмента: w3d 8 0=1 (основное), w3d 8 1=1/4 (возбуждённое) |
| `gap_3d_main` | Theorem | ★ сводка: 15/16, >0, > 2+1D, формула совпадает |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`gap_from_eigenvalues`** - Несущее вычисление: щель 15/16 выведена не постулатом, а из конкретных элементов чётного блока transfer-матрицы — основное собственное значение даёт even_block_00=1*2, возбуждённое even_block_11=(1/16)*6 (вырождение 6 = число пространственных плакеток в 3+1D), откуда gap=1-1/16. Это честная привязка числа 15/16 к спектру блок-матрицы, но строго для конкретной модели Block3D при beta=8. _(mass-gap, eigenvalues, even-block, 3+1D, degeneracy)_
- **`gap_formula_matches`** - Концептуальное ядро лестницы: единая замкнутая форма gap = 1-(1/4)^d_sp согласуется с тремя независимо вычисленными щелями (d_sp=0->0, 1->3/4, 2->15/16). ЧЕСТНОЕ ограничение: это согласие на КОНЕЧНОМ наборе уровней, а не доказанная по индукции теорема для произвольного d_sp — gamma_sq_power определена рекурсивно, но связь её с реальной щелью при общем d_sp не доказана. Красивая закономерность-наблюдение, не общая теорема о размерностной зависимости континуумной щели. _(dimension-ladder, closed-form, pattern, finite-checks, honest-gap)_

**Uniqueness - score 3 (new-framing).** Лестница щели по размерности с замкнутой формулой gap=1-(1/4)^d_sp: 0,3/4,15/16,63/64; щель 3+1D=15/16 привязана к спектру чётного блока и весам конфайнмента.
> _Caveat:_ Конечно-решёточное Q-вычисление на конкретной блок-матрице при beta=8; формула 1-(1/4)^d_sp проверена лишь для d_sp=0..3, НЕ доказана индуктивно для произвольной размерности. НЕ континуумный YM и НЕ Clay Millennium. Header «~15 Qed» — фактически 14.

---

## #460 - `src/gauge/GapBound.v` - score 3 (new-framing)

**Щель континуумного оператора >= 1/8 из одной строки целочисленной арифметики (112<=135)**

- **Topic.** Доказывает нижнюю оценку щели continuum-оператора M (собственные значения lambda0=2/3 и корни q(lambda)=lambda^2-lambda/3-4/45): gap>=1/8 двумя методами — sqrt(7/15)<=3/4 <=> 7/15<=9/16 <=> 112<=135, и полиномиальный свидетель q(13/24)=23/960>0 => lambda1<13/24.
- **Role.** Узел continuum-limit программы mass-gap (K x K -> continuum). Зависит от gauge.ContinuumOperator (char_poly, lambda_0_is_root), gauge.ExactEigenvalues (quadratic_factor, quad_discriminant, quadratic_at_0_negative). Сводит щель к проверяемому неравенству целых.
- **Counts.** Qed 16 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: gauge.ContinuumOperator; ToS: gauge.ExactEigenvalues
- **E/R/R.** _Elements:_ собственные значения lambda0=2/3, корни квадратичного фактора q; дискриминант quad_discriminant=7/15; рациональный свидетель 13/24; конкретные значения q(13/24)=23/960, q(0)<0; целое неравенство 112<=135. _Roles:_ char_poly / quadratic_factor — роль характеристического многочлена / квадратичного фактора; 13/24 играет роль разделяющего свидетеля (барьер между lambda1 и 2/3); знак q — роль локатора корня. _Rules:_ gap>=1/8 <=> sqrt(7/15)<=3/4 <=> 7/15<=9/16 <=> 112<=135; q открыт вверх, q(0)<0, q(13/24)>0 => больший корень в (0,13/24); 2/3-13/24=1/8. _P4:_ Финитизация иррационального в рациональный барьер: вместо вычисления иррационального корня lambda1=(1/3+sqrt(7/15))/2 (role-limit, не достигаемое в Q) предъявляется РАЦИОНАЛЬНЫЙ свидетель 13/24 и проверяется знак q на нём — Element-сторона. Так нижняя оценка щели сведена к одной строке целочисленной арифметики 112<=135 (P4: конечно проверяемо), минуя нетерминирующее извлечение корня. Это и есть приём границы финитизации в действии.
- **Classical counterpart.** Гипотеза щели масс Yang-Mills (Clay) и классические методы локализации корней (теорема Штурма / правило знаков Декарта / промежуточное значение) для оценки спектрального зазора. Отличие: щель оценена снизу 1/8 через РАЦИОНАЛЬНЫЙ свидетель 13/24 и знак квадратичного фактора, сведя всё к целому 112<=135 — это конкретный явный 3x3 «continuum»-оператор, НЕ доказанный континуумный предел YM; сходимость K->infinity (O(1/K^2)) лишь прокомментирована, не доказана.
- **Tags.** gauge, mass-gap, continuum-limit, root-localization, finitization, integer-arithmetic, exact-rational, vein-A, spectral-gap
- **Notes.** Header STATUS заявляет «~20 Qed» — фактически 17 Qed (дрейф ~20->17). 0 Admitted, 0 axioms. total_count — reflexivity-маркер. discrete_gap_K3/continuum_gap/discrete_gap_positive_large_K доказывают лишь голые позитивности рациональных констант (0<5/18, 0<1/8, 0<1/16) — связь с реальной сходимостью K->infinity только в комментариях, не формализована (Part IV слабее своего заголовка «K x K Convergence»).

**Lemmas (17):**

| name | kind | role |
|---|---|---|
| `lambda_0_largest` | Theorem | 7/15 < 1 (lambda0=2/3 — наибольшее собственное значение) |
| `discriminant_exceeds_linear` | Lemma | 1/9 < 7/15 (sqrt(7/15)>1/3 => меньший корень отрицателен) |
| `eigenvalue_ordering` | Theorem | порядок: 1/9<7/15 и 7/15<1 (lambda2<0<lambda1<lambda0) |
| `three_distinct_eigenvalues` | Theorem | 0<quad_discriminant<1 (вещественные и различные корни) |
| `gap_integer_bound` | Theorem | ★ THE целое неравенство: 112<=135 (= щель>=1/8) |
| `gap_rational_bound` | Theorem | рациональная форма: 7/15 <= 9/16 |
| `gap_witness_value` | Lemma | 2/3 - 13/24 == 1/8 (значение щели на свидетеле) |
| `eighth_positive` | Lemma | 0 < 1/8 |
| `q_at_gap_witness_value` | Theorem | quadratic_factor(13/24) == 23/960 (точное значение) |
| `q_at_gap_witness` | Theorem | ★ q(13/24) > 0 — ключевой свидетель локализации корня |
| `continuum_gap_ge_eighth` | Theorem | ★ ЩЕЛЬ >= 1/8: p(2/3)=0 /\ q(13/24)>0 /\ q(0)<0 /\ 2/3-13/24=1/8 |
| `discrete_gap_K3` | Theorem | 0 < 5/18 (K=3 щель из KDependence.v) |
| `continuum_gap` | Theorem | 0 < 1/8 (континуумная щель положительна) |
| `discrete_gap_positive_large_K` | Theorem | 0 < 1/16 (большое K: щель >= 1/8 - 1/16) |
| `gap_positive_all_K` | Theorem | равномерно по K>=3: 0<5/18 /\ 2/3-13/24=1/8 |
| `gap_bound_main` | Theorem | ★ сводка: 112<=135 /\ 7/15<=9/16 /\ p(2/3)=0 /\ q(13/24)>0 |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`continuum_gap_ge_eighth`** - Несущая теорема и самое содержательное место кластера-пятёрки: щель continuum-оператора >= 1/8 доказана БЕЗ извлечения иррационального корня. Логика: q открыт вверх (старший коэф >0), q(0)<0, q(13/24)=23/960>0, значит больший корень lambda1 лежит в (0,13/24); поскольку lambda0=2/3 — корень char_poly, gap=2/3-lambda1 > 2/3-13/24 = 1/8. Это аккуратный приём ЛОКАЛИЗАЦИИ корня рациональным свидетелем — финитизация иррационального через знак многочлена. Честно: оператор M назван «continuum», но это конкретный явный 3x3-оператор из ContinuumOperator, а не доказанный предел решёточной YM; «континуум» — терминология модели. _(mass-gap, root-localization, rational-witness, finitization, polynomial-sign)_
- **`gap_integer_bound`** - Сигнатурный приём файла: вся нижняя оценка щели сжата до ОДНОЙ строки целочисленной арифметики 112<=135 (lia), через цепочку gap>=1/8 <=> sqrt(7/15)<=3/4 <=> 7/15<=9/16 <=> 112<=135. Это самая чистая иллюстрация границы финитизации в gauge-кластере: иррациональный sqrt устранён возведением в квадрат, оставив конечно-проверяемое целое неравенство. Само по себе 112<=135 тривиально; ценность — в постановке (что именно это неравенство И ЕСТЬ положительность щели). _(integer-arithmetic, finitization, one-line, vein-A, square-to-remove-sqrt)_

**Uniqueness - score 3 (new-framing).** Нижняя оценка щели >=1/8 через финитизацию: иррациональный корень локализован рациональным свидетелем 13/24 (знак q), вся щель сведена к одной строке целой арифметики 112<=135 — чистый инстанс границы финитизации в спектральной задаче.
> _Caveat:_ Конкретный явный 3x3 «continuum»-оператор, НЕ доказанный континуумный предел решёточной YM и НЕ Clay Millennium. K->infinity сходимость и оценка ошибки O(1/K^2) лишь прокомментированы (discrete_gap_* — это голые 0<5/18, 0<1/16, не связанные доказательством с континуумом). Header «~20 Qed» — фактически 17.

---

## #461 - `src/gauge/GapDecayRate.v` - score 2 (methods)

**Decay rate of the lattice mass gap along the exact RG orbit: U(1) and SU(2) gaps vanish like (1/2)^k**

- **Topic.** Tracks how fast the finite-lattice mass gap shrinks along the exact RG orbit beta_k = exact_rg(0,k,beta). Shows U(1) gap = epsilon_k/4 and SU(2) gap is sandwiched u1_gap <= su2_gap < 4*u1_gap, both bounded by epsilon_k = (8-beta)*(1/2)^k, hence both tend to 0 exponentially while staying strictly positive at every finite k.
- **Role.** Terminal analysis file of the exact-RG gap thread. Imports gauge.GapMatching (exact_rg, gap_inverse, gap_matching_preserves_gap), gauge.ExactRGProcess, gauge.TransferMatrix (mass_gap_2x2), gauge.SU2TransferMatrix (su2_mass_gap, su2_mass_gap_factor), gauge.LargerLattice (gap_lower_N, pow2_pos), plus SeriesConvergence (Qpow_limit_zero). Leaf: nothing in the catalogued set reuses it.
- **Counts.** Qed 21 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs List Lia ZArith Lqa; ToS: CauchyReal; ToS: SeriesConvergence; ToS: gauge.TransferMatrix; ToS: gauge.SU2TransferMatrix; ToS: gauge.LargerLattice; ToS: gauge.GapMatching; ToS: gauge.ExactRGProcess
- **E/R/R.** _Elements:_ точки RG-орбиты beta_k и зазоры u1_gap_at_k / su2_gap_at_k в каждой ступени k (конкретные рациональные значения). _Roles:_ ступень k = роль-порядок процесса убывания; epsilon_k = 8-beta_k — роль-мера отклонения от критической точки beta=8; зазор = наблюдаемое над парой собственных значений. _Rules:_ exact_rg задаёт beta_k; epsilon_k = (8-beta)*(1/2)^k (через inv_pow2_eq_Qpow_half); зажим u1<=su2<4u1; Qpow_limit_zero даёт ступень под любым порогом. _P4:_ процесс убывания: на КАЖДОМ конечном k зазор строго положителен (Element-актуальность), предел 0 — role-limit, не достигается ни на одной ступени; «исчезновение» = свойство нетерминирующего процесса, не завершённого объекта.
- **Classical counterpart.** Зеркалит асимптотическую свободу / RG-поток к фиксированной точке и стандартный предел геометрической прогрессии (1/2)^k -> 0. НОВО здесь только обрамление: точная рациональная RG-орбита как процесс (nat->Q) с зажимом U(1)<=SU(2)<4*U(1) и явной скоростью; никакого нового физического содержания, и предел 0 здесь — убывание игрушечного зазора, а не континуумная масса.
- **Tags.** gauge, mass-gap, RG, decay-rate, su2, u1, process, honest-limitation, P4
- **Notes.** Qed actual = 22 (header '~22' OK). 0 own axioms. epsilon_k формула в шапке '8 - eps/2^k' — на деле epsilon_k = (8-beta)*(1/2)^k (см. epsilon_k_via_Qpow); это упрощённая RG-форма, не дрейф счёта.

**Lemmas (26):**

| name | kind | role |
|---|---|---|
| `beta_k` | Definition | связь k-й ступени RG-орбиты: exact_rg 0 k beta |
| `epsilon_k` | Definition | отклонение от критической точки: 8 - beta_k beta k |
| `beta_k_at_0` | Lemma | beta_k beta 0 == beta (старт орбиты) |
| `beta_k_range` | Lemma | beta_k остаётся в (0,8) |
| `beta_k_increasing` | Lemma | beta_k beta k <= beta_k beta (S k) (монотонный рост к 8) |
| `epsilon_k_positive` | Lemma | 0 < epsilon_k (отклонение положительно) |
| `epsilon_k_decreasing` | Lemma | epsilon_k (S k) <= epsilon_k k (отклонение убывает) |
| `epsilon_k_at_0` | Lemma | epsilon_k beta 0 == 8 - beta |
| `u1_gap_at_k` | Definition | U(1)-зазор на ступени k: mass_gap_2x2(beta_k) |
| `u1_gap_positive` | Lemma | 0 < u1_gap_at_k (зазор положителен на каждой ступени) |
| `u1_gap_eq_gap_lower` | Lemma | u1_gap_at_k == gap_lower_N 0 (2^k) beta (мост к решётке через gap_matching) |
| `u1_gap_decreasing` | Lemma | U(1)-зазор убывает по k |
| `u1_gap_quarter_epsilon` | Lemma | u1_gap_at_k == epsilon_k * (1/4) (точная связь зазора и отклонения) |
| `su2_gap_at_k` | Definition | SU(2)-зазор на ступени k: su2_mass_gap(beta_k) |
| `su2_gap_positive_all_k` | Lemma | 0 < su2_gap_at_k для всех k |
| `su2_gap_lower` | Lemma | u1_gap_at_k <= su2_gap_at_k (нижняя граница SU(2)-зазора) |
| `su2_factor_lt_4` | Lemma | su2_mass_gap_factor beta < 4 для beta in (0,8) (через nra) |
| `su2_gap_upper` | Lemma | su2_gap_at_k < 4 * u1_gap_at_k (верхняя граница) |
| `su2_gap_le_epsilon` | Lemma | su2_gap_at_k < epsilon_k (зажат отклонением) |
| `inv_pow2_eq_Qpow_half` | Lemma | 1/2^k == Qpow(1/2,k) (индукционный мост к Qpow) |
| `epsilon_k_via_Qpow` | Lemma | epsilon_k == (8-beta)*Qpow(1/2,k) (замкнутая форма) |
| `su2_gap_vanishes` | Theorem | для любого eps>0 есть k с su2_gap_at_k < eps (исчезновение SU(2)-зазора) |
| `u1_gap_vanishes` | Theorem | то же для U(1)-зазора (через нижнюю границу SU(2)) |
| `gap_decay_main` | Theorem | сводка: SU(2)-зазор положителен, зажат epsilon_k, исчезает, фактор<4 |
| `our_model_vs_reality` | Theorem | ★ честная оговорка: модель даёт зазор->0, но >0 на каждом конечном k |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`epsilon_k_via_Qpow`** - Замыкает RG-отклонение в чистую геометрическую форму epsilon_k == (8-beta)*(1/2)^k: разворачивает exact_rg/gap_inverse/gap_lower_N до 1/2^k и через inv_pow2_eq_Qpow_half отождествляет с Qpow(1/2,k). Это несущая лемма — именно из неё (а не из решёточных оценок) следует экспоненциальная скорость; всё «исчезновение» сводится к classical Qpow_limit_zero для \|1/2\|<1. _(geometric, Qpow, decay-rate, load-bearing)_
- **`su2_gap_vanishes`** - Главная теорема файла: SU(2)-зазор опускается ниже любого порога. Доказательство = зажим su2_gap < epsilon_k = (8-beta)*Qpow(1/2,N) плюс выбор N из Qpow_limit_zero при цели eps/(8-beta). ВАЖНАЯ ЧЕСТНОСТЬ: это показывает, что вдоль данной RG-орбиты зазор ИСЧЕЗАЕТ (масса -> 0) — структурно ПРОТИВОПОЛОЖНО континуумной щели масс; файл не утверждает обратного и сам фиксирует это в our_model_vs_reality. _(vanishing, RG-orbit, honest-limitation, su2)_
- **`our_model_vs_reality`** - Дисциплинирующая теорема: конъюнкция (зазор->0) /\ (зазор>0 на каждом конечном k) /\ (фактор<4). Явно разводит процессную истину (положительность на любой актуальной ступени, P4) и предельное поведение (role-limit 0). Ценность — методологическая честность внутри кластера, склонного к оверклеймам: это U(1)/SU(2) игрушечная орбита, НЕ доказательство массовой щели. _(P4, honesty, process-vs-limit)_

**Uniqueness - score 2 (methods).** Точная рациональная оценка скорости убывания решёточного зазора вдоль RG-орбиты: U(1)=epsilon_k/4, зажим U(1)<=SU(2)<4*U(1), обе ветви ~ (1/2)^k, с машинно-проверенным разделением «положительно на каждом конечном k» против «предел 0».
> _Caveat:_ Игрушечная 1+1D U(1)/SU(2) RG-орбита на 2x2-передаточной матрице, НЕ континуумная теория. Скорость = тривиальная геометрия (1/2)^k. ВНИМАНИЕ: файл показывает зазор ->0 (исчезновение массы вдоль орбиты) — это НЕ доказательство массовой щели, а её структурная противоположность; сам файл это фиксирует.

---

## #462 - `src/gauge/GapMatching.v` - score 2 (methods)

**Exact non-perturbative RG by eigenvalue-gap matching: RG_k(beta) = 8 - 4*gap_lower_N(K,2^k,beta)**

- **Topic.** Defines the exact (no perturbation) RG map at stage k by inverting the affine gap function mass_gap_2x2(beta) = 2 - beta/4. gap_inverse(v) = 8 - 4v inverts it on the nose; exact_rg K k beta = gap_inverse(gap_lower_N K (2^k) beta) is identity at k=0, stays in (0,8), is monotone in k, preserves the gap exactly, and is shown to genuinely differ from the Gaussian quadratic RG.
- **Role.** Core definitional hub of the exact-RG thread; supplies exact_rg, gap_inverse, gap_matching_preserves_gap reused by gauge.GapDecayRate (and gauge.ExactRGProcess). Imports gauge.TransferMatrix (mass_gap_2x2, transfer_eigenvalue_*), gauge.RGFlow (rg_map_quadratic, rg_quadratic_at_3), gauge.SU2TransferMatrix, gauge.NonlinearRG, gauge.LargerLattice (gap_lower_N, gap_lower_N_bounded, gap_lower_pow2_chain, pow2_pos), FixedPoint.
- **Counts.** Qed 20 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs List Lia ZArith Lqa; ToS: CauchyReal; ToS: FixedPoint; ToS: gauge.TransferMatrix; ToS: gauge.RGFlow; ToS: gauge.SU2TransferMatrix; ToS: gauge.NonlinearRG; ToS: gauge.LargerLattice
- **E/R/R.** _Elements:_ конкретные рациональные значения beta и зазоров; ступени 2^k решётки; точечные значения exact_rg 2 1 3 = 11/2, exact_rg 2 2 3 = 27/4. _Roles:_ gap_inverse — роль-обратимость аффинной функции зазора; exact_rg K k — RG-преобразование как роль над ступенью k; gap_lower_N — наблюдаемый зазор на решётке 2^k. _Rules:_ mass_gap_2x2(beta)=2-beta/4 обратима => gap_inverse(v)=8-4v; exact_rg = gap_inverse o gap_lower_N; сохранение зазора gap_matching_preserves_gap; отличие от гауссова RG доказано контрпримером. _P4:_ RG определён ПОСТУПЕНЧАТО: для каждого конечного k — конечное рациональное вычисление (Element/P4); сам «процесс {RG_k}» — не завершённый предел, а семейство актуальных ступеней (rg_process_well_defined: всякая ступень = num#den).
- **Classical counterpart.** Зеркалит непертурбативный ренормгрупповой блок-спин поток Каданова-Вильсона (RG как отображение связей, сохраняющее физический масштаб/зазор). НОВО только формализация: RG определён через ТОЧНУЮ инверсию аффинной функции зазора на конкретной 2x2-передаточной матрице и реализован как рациональный процесс (nat->Q), а не как непрерывный поток; стандартного содержания RG не добавляет.
- **Tags.** gauge, RG, mass-gap, non-perturbative, process, gap-matching, methods
- **Notes.** Qed actual = 21, но шапка заявляет '~26' (и блок SUMMARY перечисляет 21 имя в 8+6+4+3) — ДРЕЙФ счёта ~26 -> фактически 21. 0 own axioms (шапка пишет 'AXIOMS: classic (inherited)' — это наследуемый, не собственный).

**Lemmas (24):**

| name | kind | role |
|---|---|---|
| `gap_inverse` | Definition | обратная к зазору: gap_inverse v = 8 - 4*v |
| `gap_inverse_correct` | Theorem | mass_gap_2x2(gap_inverse v) == v (правая обратимость) |
| `gap_inverse_correct_rev` | Theorem | gap_inverse(mass_gap_2x2 beta) == beta (левая обратимость) |
| `gap_inverse_range` | Lemma | gap_inverse переводит (0,2) в (0,8) |
| `gap_inverse_decreasing` | Lemma | строго убывает: v1<v2 => gap_inverse v2 < gap_inverse v1 |
| `gap_inverse_antitone` | Lemma | слабо убывает (<=-версия, нужна для монотонности RG по k) |
| `gap_inverse_at_0` | Lemma | gap_inverse 0 == 8 |
| `gap_inverse_at_2` | Lemma | gap_inverse 2 == 0 |
| `gap_inverse_at_5_4` | Lemma | gap_inverse (5/4) == 3 (конкретная точка) |
| `exact_rg` | Definition | ★ точный непертурбативный RG: gap_inverse(gap_lower_N K (2^k) beta) |
| `exact_rg_0` | Theorem | exact_rg K 0 beta == beta (на ступени 0 — тождество) |
| `exact_rg_pos` | Lemma | 0 < exact_rg для beta in (0,8) |
| `exact_rg_lt_8` | Lemma | exact_rg < 8 для beta in (0,8) |
| `exact_rg_range` | Lemma | exact_rg остаётся в (0,8) |
| `exact_rg_increasing` | Theorem | exact_rg монотонно растёт по k (бОльшая решётка -> ближе к 8) |
| `exact_rg_orbit` | Definition | RG-орбита как процесс: k \|-> exact_rg K k beta |
| `gap_matching_preserves_gap` | Theorem | ★ mass_gap_2x2(exact_rg K k beta) == gap_lower_N K (2^k) beta (точное сохранение зазора) |
| `exact_rg_at_1_3` | Lemma | exact_rg 2 1 3 == 11/2 (vm-проверка) |
| `exact_rg_at_2_3` | Lemma | exact_rg 2 2 3 == 27/4 (vm-проверка) |
| `rg_process_well_defined` | Lemma | всякая ступень exact_rg = num#den (рациональна, актуальна) |
| `gap_matching_vs_gaussian` | Lemma | ★ exact_rg НЕ совпадает с гауссовым rg_map_quadratic (контрпример в beta=3) |
| `gap_matching_main` | Theorem | сводка пунктов I-II (обратимость, тождество, диапазон, монотонность, сохранение) |
| `what_gap_matching_proves` | Theorem | сводка: процесс корректен + отличается от гауссова + сохраняет зазор |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`gap_inverse_correct`** - Несущий факт всего файла: зазор mass_gap_2x2(beta)=2-beta/4 — аффинная биекция, и gap_inverse(v)=8-4v — её точная обратная (доказательство: разворот + lra). Всё остальное (определение exact_rg, сохранение зазора, монотонность) держится на этой обратимости. По сути это тривиальная инверсия линейной функции — ценность не в трудности, а в том, что она делает RG ТОЧНЫМ (без пертурбативного ряда). _(inversion, affine, exact, load-bearing)_
- **`gap_matching_preserves_gap`** - Определяющее свойство конструкции: RG-преобразованная связь имеет ровно тот зазор, что наблюдается на решётке ступени 2^k. Прямое следствие gap_inverse_correct, но именно оно делает {exact_rg K k} осмысленным RG-потоком (зазор — инвариант сопоставления). Используется в GapDecayRate.u1_gap_eq_gap_lower как мост зазор<->решётка. _(gap-preservation, RG-flow, bridge)_
- **`gap_matching_vs_gaussian`** - Честная демаркация: точный RG НЕ тождественен гауссову квадратичному rg_map_quadratic — доказано конкретным расхождением (exact_rg 2 1 3 = 11/2 против rg_map_quadratic 3 = 3). Это удерживает файл от ложного отождествления с пертурбативной картиной и фиксирует, что 'точный' здесь означает иную, решёточно-определённую функцию. _(non-perturbative, separation, honesty)_

**Uniqueness - score 2 (methods).** Точный (непертурбативный) RG как инверсия аффинной функции зазора: gap_inverse=8-4v, exact_rg = gap_inverse o gap_lower_N — тождество при k=0, монотонность по k, ТОЧНОЕ сохранение зазора, и доказанное отличие от гауссова RG, всё на рациональном процессе.
> _Caveat:_ Игрушечная 1+1D U(1) на 2x2-передаточной матрице; 'точность' = инверсия линейной 2-beta/4, математически тривиальна. Это методологическое обрамление RG-потока, НЕ новая физика и НЕ континуумный результат; сохранение зазора — прямое следствие обратимости.

---

## #463 - `src/gauge/GapRatio.v` - score 2 (methods)

**Eigenvalue ratio r=t1/t0 in (0,1) and its RG contraction r -> r^2; gap from ratio**

- **Topic.** Studies the temporal eigenvalue ratio r = t1_M0(beta)/t0_M0(beta) from the SU(2) character transfer matrix. Computes r(1)=47/336, r(2)=11/12, proves 0<r<1, the 3+1D combined ratio r*s1 < r, the RG doubling step r -> r^2 contracts (r^2<r), iterates converge to 0, and a lattice/physical mass gap 1-r increases under RG.
- **Role.** Ratio-side analysis of the SU(2) transfer matrix. Imports gauge.ExactMassGap (t0_M0, t1_M0, transfer_eigenvalue), gauge.SU2Characters, gauge.CharacterTransfer, gauge.ClebschGordan, gauge.SpatialHamiltonian / gauge.CombinedTransfer3D (spatial_suppression, spatial_penalty, penalty_positive/_nonneg, suppression_1), stdlib.Combinatorics (bessel_term, fact_*), SeriesConvergence. Self-contained leaf; ends with Print Assumptions.
- **Counts.** Qed 36 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: CauchyReal; ToS: SeriesConvergence; ToS: stdlib.Combinatorics; ToS: gauge.SU2Characters; ToS: gauge.CharacterTransfer; ToS: gauge.ExactMassGap; ToS: gauge.ClebschGordan; ToS: gauge.SpatialHamiltonian; ToS: gauge.CombinedTransfer3D
- **E/R/R.** _Elements:_ конкретные рациональные собственные значения t0_M0, t1_M0 и их отношение r при beta=1,2 (47/336, 11/12); итерации rg_iterate r n. _Roles:_ r = t1/t0 — роль-отношение возбуждённого к основному; rg_ratio_step (возведение в квадрат) — роль RG-удвоения; 1-r — роль решёточной щели масс; spatial_suppression s1 — роль пространственного подавления. _Rules:_ 0<r<1 из t1<t0 (оба >0); под RG-удвоением r->r^2 (композиция передаточных матриц); сжатие r^2<r при 0<r<1; combined R=r*s1<r при s1<1; gap=1-r растёт под RG. _P4:_ сходимость к 0 — процесс итераций (rg_iterate): каждая ступень — конкретное рациональное число (Element), 0 — предел-роль; конкретный rg_iterate_converges_beta_1 (r^4<1/100) показывает достижимость порога через vm-вычисление на актуальной ступени.
- **Classical counterpart.** Зеркалит спектральную щель передаточной матрицы (отношение второго к первому собственному значению = e^{-m*a}, корреляционная длина) и RG-сжатие отношения собственных значений при блок-спин удвоении. НОВО только обрамление E/R/R и рациональная (Q) реализация на SU(2)-характерной матрице; содержание (gap из ratio, r->r^2 под удвоением) стандартно, иррациональность непрерывного -log(r) здесь обойдена приближением 1-r.
- **Tags.** gauge, mass-gap, eigenvalue-ratio, RG, contraction, su2, transfer-matrix, methods
- **Notes.** Qed actual = 36; шапка заявляет '~40' (мягкое '~', плюс блок-комментарии перечисляют '~10/~10/~12/~8' = ~40 как оценку). Дрейф ~40 -> фактически 36. 0 own axioms. Файл заканчивается Check-блоком и 'Print Assumptions gap_ratio_summary'.

**Lemmas (42):**

| name | kind | role |
|---|---|---|
| `gap_ratio` | Definition | отношение собственных значений r = t1_M0 beta / t0_M0 beta |
| `t0_positive_beta_1` | Lemma | 0 < t0_M0 1 (= 7/8) |
| `t0_positive_beta_2` | Lemma | 0 < t0_M0 2 (= 1/2) |
| `t1_positive_beta_1` | Lemma | 0 < t1_M0 1 (= 47/384) |
| `t1_positive_beta_2` | Lemma | 0 < t1_M0 2 (= 11/24) |
| `gap_ratio_well_defined_1` | Theorem | знаменатель t0_M0 1 > 0 (определённость r) |
| `gap_ratio_well_defined_2` | Theorem | знаменатель t0_M0 2 > 0 |
| `gap_ratio_at_beta_1` | Lemma | r(1) == 47/336 (vm) |
| `gap_ratio_at_beta_2` | Lemma | r(2) == 11/12 (vm) |
| `gap_ratio_pos_1` | Lemma | 0 < r(1) |
| `gap_ratio_pos_2` | Lemma | 0 < r(2) |
| `gap_ratio_lt1_beta_1` | Lemma | r(1) < 1 |
| `gap_ratio_lt1_beta_2` | Lemma | r(2) < 1 |
| `gap_ratio_in_01_beta_1` | Theorem | 0 < r(1) < 1 |
| `gap_ratio_in_01_beta_2` | Theorem | 0 < r(2) < 1 |
| `combined_ratio` | Definition | 3+1D отношение R = gap_ratio * spatial_suppression |
| `combined_ratio_at_zero` | Lemma | при нулевом пространственном коэф. R == gap_ratio |
| `suppression_1_lt_1` | Lemma | s1 < 1 при положительном пространственном коэф. |
| `suppression_1_nonneg` | Lemma | s1 >= 0 при достаточно малом коэф. |
| `combined_ratio_less_than_temporal` | Theorem | R < gap_ratio при положительном пространственном коэф. |
| `combined_ratio_pos_1` | Lemma | 0 <= R при beta=1 |
| `combined_ratio_lt1_beta_1` | Lemma | R < 1 при beta=1 |
| `rg_ratio_step` | Definition | RG-удвоение отношения: r \|-> r*r |
| `rg_ratio_step_nonneg` | Lemma | 0 <= r^2 при r>=0 |
| `rg_contraction` | Theorem | ★ r^2 < r при 0<r<1 (сжатие под RG) |
| `rg_ratio_step_pos` | Lemma | 0 < r^2 при r>0 |
| `rg_ratio_step_lt1` | Lemma | r^2 < 1 при 0<=r<1 |
| `rg_iterate` | Fixpoint | n-кратная RG-итерация отношения |
| `rg_iterate_pos` | Lemma | итерация сохраняет положительность |
| `rg_iterate_lt1` | Lemma | итерация сохраняет < 1 |
| `rg_iterate_decreasing` | Theorem | итерация строго убывает по n |
| `rg_iterate_1` | Lemma | r_1 == r^2 |
| `rg_iterate_2` | Lemma | r_2 == (r^2)^2 = r^4 |
| `rg_iterate_converges_beta_1` | Lemma | ★ r^4 < 1/100 при beta=1 (конкретная сходимость, vm) |
| `lattice_mass_gap_from_ratio` | Definition | решёточная щель из отношения: 1 - r |
| `mass_gap_from_ratio_pos` | Theorem | 1-r > 0 при r<1 |
| `mass_gap_increases_under_rg` | Theorem | 1-r^2 > 1-r (щель растёт под RG, через (1-r)(1+r)) |
| `physical_gap` | Definition | физическая щель m = (1-r)/a |
| `physical_gap_positive` | Theorem | m > 0 при r<1, a>0 |
| `physical_gap_rg_relation` | Theorem | physical_gap(r^2,2a) == (1+r)/2 * physical_gap(r,a) (точное соотношение) |
| `physical_gap_rg_factor` | Theorem | (1/2)*physical_gap(r,a) < physical_gap(r^2,2a) (фактор в (1/2,1)) |
| `gap_ratio_summary` | Theorem | сводка: r in (0,1), сжатие, убывание итераций, щель положительна |

**Key lemmas (deep):**

- **`rg_contraction`** - Несущая теорема: 0<r<1 => r^2<r — RG-удвоение СЖИМАЕТ отношение. Доказательство через r(r-1)<0 (r>0, r-1<0). Тривиальное алгебраическое неравенство, но именно оно делает отношение RG-устойчивым (стремится к 0 -> щель 1-r растёт к 1). Контраст с GapDecayRate, где зазор mass_gap_2x2 убывает: здесь убывает ОТНОШЕНИЕ, и потому щель-из-отношения 1-r РАСТЁТ — две разные определения щели ведут себя противоположно. _(contraction, RG, fixed-point, load-bearing)_
- **`rg_iterate_converges_beta_1`** - Конкретная (vm_compute) сходимость: при beta=1, r=47/336, уже r^4 < 1/100. Превращает абстрактное 'r->0' в актуальную проверенную ступень (P4: достижимость порога на конечном n через рациональное вычисление). Честно ограничено одной точкой beta=1 — общая сходимость к 0 для произвольного r не доказана как предельная теорема, только убывание + этот пример. _(convergence, vm-compute, concrete, P4)_
- **`physical_gap_rg_relation`** - Точное соотношение physical_gap(r^2,2a) == (1+r)/2 * physical_gap(r,a) (доказательство field; lra). Показывает, что под удвоением шага решётки физическая щель умножается на (1+r)/2 in (1/2,1) — приближённая RG-инвариантность с явным контролируемым фактором. Аккуратная количественная связь, но классическая по сути (блок-спин масштабирование), новизны нет. _(physical-gap, rg-scaling, exact-factor)_

**Uniqueness - score 2 (methods).** Рациональное вычисление спектрального отношения r=t1/t0 SU(2)-передаточной матрицы (47/336, 11/12) с машинной проверкой 0<r<1, RG-сжатия r->r^2, точного масштабирования physical_gap(r^2,2a)=((1+r)/2)*physical_gap(r,a) и конкретной сходимости r^4<1/100.
> _Caveat:_ Игрушечные значения beta=1,2 на конкретной 2x2 SU(2)-характерной матрице. r->r^2 и gap=1-r классичны; сжатие = тривиальная алгебра. Сходимость к 0 доказана лишь как убывание + один пример (beta=1), НЕ как общая предельная теорема. Щель-из-отношения 1-r — приближение настоящего -log(r) (иррационального).

---

## #464 - `src/gauge/GaugeField.v` - score 1 (exposition)

**U(1) link variables on the lattice: plaquette phase and Wilson action are gauge-invariant**

- **Topic.** Sets up a U(1) gauge field as a rational phase on each link of an NxN lattice. Defines the plaquette phase (oriented loop sum), the gauge transform theta_l -> theta_l + phi(target) - phi(source), and the quadratic Wilson action S=(beta/2)*sum theta_P^2. Proves the central facts: the plaquette phase and the Wilson action are gauge-invariant, gauge equivalence is an equivalence relation, and the action is constant on gauge orbits.
- **Role.** Foundational construction file of the gauge cluster (the U(1) field + action layer). Imports gauge.LatticeStructure (link, plaquette, site, plaquette_links, link_source/target, wrap, num_plaquettes, num_links, num_sites, index_to_site, physical_dof, sum_Q), linalg.MatrixOps, LinearAlgebra, CauchyReal. Reused by gauge.GaugeSynthesis (action_gauge_invariant) and the broader Wilson/transfer-matrix chain.
- **Counts.** Qed 17 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs List Lia ZArith Arith PeanoNat Lqa; ToS: LinearAlgebra; ToS: CauchyReal; ToS: linalg.MatrixOps; ToS: gauge.LatticeStructure
- **E/R/R.** _Elements:_ конфигурации GaugeConfig N (рациональная фаза на каждом линке); конкретные линки/плакеты решётки NxN. _Roles:_ плакетная фаза = роль ориентированного замкнутого контура; калибровочное преобразование = роль сдвига фаз вершинной функцией phi; действие Вилсона = роль скалярной меры на конфигурации; gauge_equivalent = роль орбиты. _Rules:_ theta_P = g(l1)+g(l2)-g(l3)-g(l4); gauge_transform добавляет phi(target)-phi(source); инвариантность: phi-члены телескопируются вокруг замкнутого контура к 0; действие постоянно на орбитах. _P4:_ решётка конечна (NxN, num_plaquettes конечно): сумма действия — конечная сумма по плакетам (Element/P4-актуальность); инвариантность доказывается индукцией по конечному num_plaquettes, без обращения к бесконечному объёму.
- **Classical counterpart.** Стандартная решёточная U(1) калибровочная теория (Вегнер/Вильсон): плакетная переменная как калибровочный инвариант, действие Вильсона, калибровочные орбиты. НОВО лишь то, что всё построено над рациональными фазами (Q) на конечной NxN-решётке с квадратичным (а не cos) действием и доказано индукцией по конечному числу плакетов; это квадратичное приближение, не полная компактная U(1).
- **Tags.** gauge, u1, lattice, wilson-action, gauge-invariance, plaquette, foundation, exposition
- **Notes.** Qed actual = 18. Шапка заявляет '~25', нижний блок SUMMARY заявляет '~21' — ОБА расходятся с фактическими 18 (дрейф). 0 own axioms.

**Lemmas (27):**

| name | kind | role |
|---|---|---|
| `GaugeConfig` | Definition | тип конфигурации: link -> Q (фаза на линке) |
| `zero_config` | Definition | нулевая конфигурация (все фазы 0) |
| `scale_config` | Definition | масштабирование конфигурации на c |
| `add_config` | Definition | сложение конфигураций поточечно |
| `neg_config` | Definition | отрицание конфигурации |
| `plaquette_phase` | Definition | ориентированная сумма фаз вокруг плакета: g(l1)+g(l2)-g(l3)-g(l4) |
| `gauge_transform` | Definition | калибровочный сдвиг: g(l)+phi(target)-phi(source) |
| `gauge_equivalent` | Definition | две конфигурации связаны калибровкой (exists phi) |
| `wilson_action_quad` | Definition | квадратичное действие Вилсона: (beta/2)*sum theta_P^2 |
| `zero_config_phase` | Lemma | нулевая конфигурация даёт нулевые плакетные фазы |
| `plaquette_phase_scale` | Lemma | плакетная фаза масштабируется с конфигурацией |
| `plaquette_phase_add` | Lemma | плакетная фаза аддитивна |
| `plaquette_phase_neg` | Lemma | отрицание обращает плакетную фазу |
| `plaquette_gauge_invariant` | Theorem | ★ плакетная фаза калибровочно инвариантна (phi-члены телескопируют к 0) |
| `gauge_transform_zero_phi` | Lemma | нулевая phi не меняет конфигурацию |
| `gauge_equiv_refl` | Lemma | рефлексивность калибровочной эквивалентности |
| `gauge_equiv_sym` | Lemma | симметрия (phi -> -phi) |
| `gauge_equiv_trans` | Lemma | транзитивность (phi1+phi2) |
| `action_zero_config` | Lemma | действие на нулевой конфигурации == 0 |
| `action_gauge_invariant` | Theorem | ★ действие Вилсона калибровочно инвариантно (индукция по плакетам) |
| `gauge_transform_constant` | Lemma | постоянное phi не меняет конфигурацию |
| `zero_config_pure_gauge` | Lemma | нулевая конфигурация эквивалентна чистой калибровке |
| `gauge_orbit_action_constant` | Lemma | действие постоянно на калибровочной орбите |
| `physical_dof_count` | Lemma | num_links - num_sites = num_plaquettes (счёт физических степеней свободы) |
| `gauge_field_summary` | Theorem | сводка: инвариантность фазы и действия, эквивалентность, действие 0 в вакууме |
| `gauge_invariance_main` | Theorem | главная пара: инвариантность плакетной фазы и действия |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`plaquette_gauge_invariant`** - Центральная теорема файла и физическое сердце калибровочной теории: при сдвиге theta_l -> theta_l + phi(target)-phi(source) плакетная фаза не меняется, т.к. phi-члены вокруг замкнутого контура телескопируют к 0. Доказательство — чистый ring после разворота link_target/link_source. Несущее: на нём держится инвариантность действия и определённость теории на орбитах. Классика (калибровочная инвариантность плакета), но формализована точно над Q без вещественных чисел. _(gauge-invariance, plaquette, telescoping, load-bearing)_
- **`action_gauge_invariant`** - Действие Вилсона S=(beta/2)*sum theta_P^2 постоянно при калибровочном преобразовании. Доказательство: Qmult_comp на префактор beta/2 + индукция по конечному num_plaquettes с поплакетным применением plaquette_gauge_invariant. Демонстрирует, что конечность решётки (P4) делает сумму действия честно индуктивной. Это и есть свойство, переиспользуемое в GaugeSynthesis как первый шаг 'pipeline'. _(wilson-action, gauge-invariance, finite-lattice, induction)_
- **`gauge_orbit_action_constant`** - Завершает картину орбит: если g1 ~ g2 (калибровочно эквивалентны), то их действия равны. Поплакетно показывает plaquette_phase g2 == plaquette_phase g1 через четыре конкретных линка (l1..l4) и lra. Вместе с рефл/симм/транз даёт корректное определение физической теории как функции на ОРБИТАХ конфигураций, а не на сырых конфигурациях. _(gauge-orbit, well-defined, equivalence)_

**Uniqueness - score 1 (exposition).** Чистая рациональная (Q) формализация решёточной U(1): плакетная фаза и квадратичное действие Вилсона калибровочно инвариантны, калибровочная эквивалентность — отношение эквивалентности, действие постоянно на орбитах, с явным счётом физических степеней свободы links-sites=plaquettes.
> _Caveat:_ Стандартная решёточная калибровочная теория, чисто экспозиция. КОНЕЧНАЯ NxN решётка, U(1) только, и КВАДРАТИЧНОЕ приближение действия (theta_P^2, не cos theta_P) — это НЕ компактная U(1) и НЕ континуум. Никакого нового результата; фундаментный слой для остального кластера.

---

## #465 - `src/gauge/GaugeSynthesis.v` - score 0 (infrastructure)

**Synthesis of the 1+1D U(1) lattice gauge results (K=2): the cluster's 'main theorem', honestly toy-scale**

- **Topic.** Pure consolidation file: chains lattice -> gauge field -> Wilson action -> transfer matrix -> mass gap into a five-step pipeline, then bundles everything into lattice_gauge_main (gauge invariance + symmetric transfer matrix + eigenvalues 2-beta/8 and beta/8 + mass gap 2-beta/4 positive on (0,8) + gap vanishes at beta=8) and a second bundle linking the gap to eigenvector orthogonality and monotonicity.
- **Role.** Top-level summary/capstone of the lattice U(1) gauge chain; adds NO new content, only re-exports prior results. Imports gauge.LatticeStructure, gauge.GaugeField (action_gauge_invariant, gauge_transform), gauge.WilsonAction, gauge.TransferMatrix (transfer_2x2, transfer_2x2_symmetric, eigenvalue/mass_gap lemmas, gap_vanishes_at_8, gap_monotone_beta, continuum_limit_gap, strong_coupling_large_gap, hessian_*), gauge.MassGapProcess, plus physics.* and linalg.* (is_eigenvalue, is_symmetric, dot_product, qvec2).
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs List Lia ZArith Lqa; ToS: LinearAlgebra; ToS: CauchyReal; ToS: physics.InnerProductSpace; ToS: physics.Orthogonality; ToS: physics.QObservable; ToS: physics.QState; ToS: linalg.MatrixOps; ToS: linalg.EigenvalueTheory; ToS: projective.ProjectiveSystem; ToS: gauge.LatticeStructure; ToS: gauge.GaugeField; ToS: gauge.WilsonAction; ToS: gauge.TransferMatrix; ToS: gauge.MassGapProcess
- **E/R/R.** _Elements:_ конкретная 1+1D U(1) решётка с K=2 дискретизацией; передаточная матрица transfer_2x2 beta; собственные значения 2-beta/8, beta/8. _Roles:_ pipeline_* — роли-звенья сквозного конвейера (решётка->поле->действие->матрица->щель); lattice_gauge_main — роль-агрегатор всех результатов кластера. _Rules:_ каждое звено = переэкспорт ранее доказанной леммы (exact ...); главная теорема = конъюнкция инвариантности+симметрии+собственных значений+положительности щели+обнуления при beta=8. _P4:_ вся синтезируемая картина — конечно-решёточная (K=2, 2x2-матрица): актуальные рациональные вычисления (Element/P4); 'континуумный предел' continuous_transition означает лишь существование beta in (0,8) с малой щелью, НЕ переход к бесконечному объёму.
- **Classical counterpart.** Зеркалит учебную картину решёточной U(1) калибровочной теории в 1+1D: связь Вильсона-Вегнера, передаточная матрица, спектральная щель, конфайнмент/деконфайнмент при критической связи. НИЧЕГО нового — файл лишь агрегирует. Аспирационное имя 'mass gap main theorem' отсылает к проблеме Янга-Миллса (Clay), но к ней отношения НЕ имеет: другая размерность (1+1), другая группа (U(1) абелева), и щель здесь обнуляется.
- **Tags.** gauge, synthesis, consolidation, u1, mass-gap, transfer-matrix, over-branding, infrastructure
- **Notes.** Qed actual = 11 (шапка '~12', близко). 0 own axioms. Имя файла + 'THE LATTICE GAUGE THEORY MAIN THEOREM ★★★' аспирационны: 1+1D U(1) K=2, НЕ Янг-Миллс/Clay; флаг овербрендинга в манифесте.

**Lemmas (11):**

| name | kind | role |
|---|---|---|
| `pipeline_lattice` | Lemma | звено 1: периодические гран. условия (wrap N x = x при x<N) |
| `pipeline_gauge_invariance` | Lemma | звено 2: действие калибровочно инвариантно (= action_gauge_invariant) |
| `pipeline_hessian` | Lemma | звено 3: гессиан имеет собственные значения 0 и 2*beta |
| `pipeline_transfer` | Lemma | звено 4: передаточная матрица имеет собственные значения 2-beta/8, beta/8 |
| `pipeline_mass_gap` | Lemma | звено 5: щель масс положительна на (0,8) |
| `confinement_regime` | Lemma | конфайнмент: большая щель (>=3/2) при сильной связи beta<=1 |
| `deconfinement_transition` | Lemma | деконфайнмент: mass_gap_2x2 8 == 0 |
| `continuous_transition` | Lemma | существует beta in (0,8) со сколь угодно малой щелью |
| `lattice_gauge_main` | Theorem | ★ агрегат: инвариантность+симметрия+собственные значения+положит. щель+обнуление при 8 |
| `mass_gap_eigenvector_theorem` | Theorem | ★ формула щели 2-beta/4 + ортогональность собственных векторов + монотонность |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`lattice_gauge_main`** - Заявленная '★★★ THE LATTICE GAUGE THEORY MAIN THEOREM ★★★' — но это шестичленная конъюнкция уже доказанных фактов для 1+1D U(1) с K=2: калибровочная инвариантность действия, симметрия transfer_2x2, два собственных значения, положительность щели 2-beta/4 на (0,8) и её обнуление при beta=8. Содержания НЕ добавляет (каждый конъюнкт = 'exact <prior_lemma>'). ОВЕРБРЕНДИНГ: это игрушечная абелева 1+1D модель на 2x2-матрице, а НЕ 4D неабелева массовая щель Янга-Миллса (проблема Клэя). Более того, 'щель' здесь ИСЧЕЗАЕТ при beta->8 — модель демонстрирует деконфайнмент-переход, не устойчивую щель. _(capstone, consolidation, over-branding, toy-model)_
- **`mass_gap_eigenvector_theorem`** - Вторая агрегатная теорема: точная формула щели mass_gap_2x2 = 2-beta/4, ортогональность собственных векторов (1,1) и (1,-1) (dot_product==0), и монотонное убывание щели по beta. Связывает спектральную щель с ортогональностью собственных подпространств — стандартная линейная алгебра 2x2, переэкспортированная. Полезно как единая точка входа, но новизны нет. _(eigenvector, orthogonality, monotone, consolidation)_

**Uniqueness - score 0 (infrastructure).** Сквозной конвейер и две агрегатные теоремы, собирающие результаты кластера 1+1D U(1) (K=2) в единые точки входа: калибровочная инвариантность + спектр передаточной матрицы + положительность/обнуление щели + ортогональность собственных векторов.
> _Caveat:_ ЧИСТАЯ КОНСОЛИДАЦИЯ, 0 нового содержания (каждый конъюнкт = 'exact <prior>'). СИЛЬНЫЙ ОВЕРБРЕНДИНГ: '★★★ MAIN THEOREM ★★★' и имя GaugeSynthesis отсылают к массовой щели Янга-Миллса, но это игрушечная АБЕЛЕВА 1+1D U(1) на 2x2-матрице, НЕ 4D неабелева теория и НЕ проблема Клэя; щель к тому же ИСЧЕЗАЕТ при beta=8 (деконфайнмент), а не устойчива.

---

## #466 - `src/gauge/GlobalMassGap.v` - score 2 (methods)

**Финальный синтез Steps 1-9: контракция RG c=16/25, неподвижная точка β*=3, щель ≥9/4 (модельная)**

- **Topic.** Капстоун-реэкспорт gauge-программы массовой щели: собирает в одну конъюнкцию контрактивность нелинейного RG-отображения rg_map_quadratic, единственность неподвижной точки β*=3, сходимость всех орбит (Коши) при β>0, положительность su2_mass_gap на каждой итерации и количественную оценку gap≥9/4.
- **Role.** Чисто агрегирующий лист: 0 нового содержания, всё через exact из RGFlow/HigherOrderRG/PerturbationRG/MassGapBound/NonlinearRG/ExtendedInterval/SU2*. Никто не импортирует обратно — это вершина кластерного дерева, витрина.
- **Counts.** Qed 17 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs List Lia ZArith Lqa; ToS: CauchyReal FixedPoint; gauge: RGFlow SU2TransferMatrix SU2Group SU2Synthesis HigherOrderRG PerturbationRG MassGapBound NonlinearRG ExtendedInterval
- **E/R/R.** _Elements:_ конкретные рациональные значения β (3#2, 3, 4, 8) и итерации iterate rg_map_quadratic β n; щель su2_mass_gap β как Q. _Roles:_ rg_map_quadratic = роль-преобразование шага RG (L5-порядок огрубления); β* = неподвижная точка-аттрактор; su2_mass_gap = роль-наблюдаемая (есть/нет щели). _Rules:_ is_contraction f (3#2) B (16#25) (сжатие на интервале) + iterate→Коши (Банах) + gap>0 как правило положительности на орбите. _P4:_ Финитная актуальность: orbit_cauchy_all даёт Коши-ПРОЦЕСС (потенциальный предел β*=3), а не достигнутый континуумный объект; щель проверяется на КАЖДОЙ конечной итерации n (Element), предельная щель — role-limit. Зазор до Millennium = role-limit-сторона (rg_linear_neq_quadratic: квадратичная модель ≠ полный непертурбативный RG).
- **Classical counterpart.** Wilsonian RG fixed-point analysis + Banach fixed-point theorem for the contraction f(β)=4β/(1+β); the physical target is the Yang-Mills mass-gap of the Clay Millennium problem. NEW here is ONLY the exact-rational packaging on a TWO-EIGENVALUE (J=1) SU(2) transfer matrix: the contraction constant c=16/25, fixed point β*=3, and gap≥9/4 are facts about THIS toy RG map, not about continuum YM.
- **Tags.** gauge, mass-gap, rg-flow, su2, banach, capstone, reexport, honesty, millennium-aspirational

**Lemmas (18):**

| name | kind | role |
|---|---|---|
| `step8_contraction` | Theorem | реэкспорт: f(β)=4β/(1+β) — сжатие c=16/25 на [3/2,B] для B≥4 |
| `step8_unique_fp` | Theorem | реэкспорт: единственная неподвижная точка на [3/2,4] есть p==3 |
| `step8_fp_eq_3` | Theorem | реэкспорт: rg_map_quadratic 3 == 3 |
| `step8_linear_vs_quad` | Theorem | линейный и квадратичный RG совпадают в 3, но различаются в целом |
| `step9_all_converge` | Theorem | реэкспорт: всякая орбита iterate при β>0 — Коши-процесс |
| `step9_deconfinement` | Theorem | реэкспорт: iterate β n < 8 (нет деконфайнмента) для n≥1 |
| `step9_gap_orbits` | Theorem | реэкспорт: 0 < su2_mass_gap на каждой итерации орбиты (n≥1) |
| `step9_gap_at_3` | Theorem | реэкспорт: 0 < su2_mass_gap 3 (щель в неподвижной точке) |
| `gap_at_fp_quantitative` | Theorem | количественно: 9#4 <= su2_mass_gap 3 (через mass_gap_explicit + lra) |
| `corrections_still_bounded` | Theorem | тейлоровские поправки: \|quartic\|<=1/32 и δ_quartic+δ_sextic<1/10 |
| `global_mass_gap` | Theorem | ★ ГЛАВНАЯ: 6-частная конъюнкция (контракция+единств.fp+Коши+gap>0+нет деконф.+поправки) для модели |
| `the_complete_chain` | Theorem | ★ полная цепь Steps 1-9: неабелевость SU(2)+gap>0 на (0,8)+обе контракции+Коши+gap≥9/4 |
| `what_is_proved_steps_8_9` | Theorem | конъюнкция доказанного Steps 8-9 (контракция+fp+Коши+gap в 3) |
| `what_is_open_steps_8_9` | Theorem | ★ ЧЕСТНОСТЬ: что отделяет от Millennium — линейный ≠ квадратичный RG (модель ≠ полный RG) |
| `model_limitations` | Theorem | ★ ограничения: f(β)<4 (нет асимптотической свободы) и f(β)<8 (всегда конфайнмент) |
| `steps_8_9_synthesis` | Theorem | синтез Steps 8-9 (контракция+fp=3+Коши+gap на орбите+gap≥9/4) |
| `global_summary` | Theorem | сводка ключевых чисел: gap≥9/4, c=16/25, fp=3 |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`global_mass_gap`** - Флагманская конъюнкция файла, но строго реэкспортная: каждый из 6 конъюнктов закрыт одним exact из импортированной леммы. Содержательное ядро = контракция rg_map_quadratic с c=16/25 на [3/2,4] и положительность su2_mass_gap на орбитах. Это полностью внутри J=1 (двухуровневой) SU(2)-модели: одно собственное значение, точная Q-арифметика. НЕ доказывает континуумную YM-щель — что сам файл честно фиксирует в what_is_open_steps_8_9. _(mass-gap, rg-fixed-point, banach, su2, reexport)_
- **`what_is_open_steps_8_9`** - Встроенный честный дисклеймер: теорема ДОКАЗЫВАЕТ, что rg_map_linear ≠ rg_map_quadratic, т.е. что использованное квадратичное приближение не совпадает с полным непертурбативным RG — это и есть зазор до приза Клэя. Редкая для кластера явная формализация собственной неполноты; вместе с model_limitations (f(β)<4 ⟹ нет асимптотической свободы) делает аспирационное имя GlobalMassGap самоопровергаемым изнутри. _(honesty, open-problem, model-limitation, millennium-gap)_

**Uniqueness - score 2 (methods).** Точная рациональная упаковка RG-неподвижной точки β*=3 с явной константой сжатия c=16/25 и оценкой щели 9/4 на двухуровневой SU(2)-модели, плюс встроенный машинно-проверенный честный реестр того, что НЕ доказано.
> _Caveat:_ Аспирационное имя GlobalMassGap: НЕ доказывает континуумную Yang-Mills массовую щель (приз Клэя). Конкретно J=1 (одно собственное значение) SU(2), квадратичная модель RG; модель сама признаёт f(β)<4 (нет асимптотической свободы) и rg_linear≠rg_quadratic. Файл — реэкспорт (0 нового), всё через exact. ДРЕЙФ: заголовок ~22 Qed, фактически 18.

---

## #467 - `src/gauge/HigherOrderRG.v` - score 2 (methods)

**Кварт./секст. поправки к RG: -1/(8β²), +1/(48β⁴), границы 1/32 и 1/768, суммарно <1/10 на [2,4]**

- **Topic.** Берёт квадратичное RG-отображение и добавляет тейлоровские поправки высшего порядка от 1-cos(θ): кварт. correction -1/(8β²) и секст. +1/(48β⁴). Доказывает, что каждая ограничена (1/32, 1/768), знакочередуется, факториально убывает, а исправленные отображения по-прежнему переводят [2,4]→[2,4].
- **Role.** Поставщик оценок поправок для GlobalMassGap (delta_quartic, delta_sextic, total_correction_bound, rg_correction_quartic импортируются туда). Зависит от RGFlow, SU2TransferMatrix, CosineAction; ниже по дереву, чем витрина.
- **Counts.** Qed 23 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs List Lia ZArith Lqa; ToS: CauchyReal SeriesConvergence RealField FixedPoint; zeta: ZetaProcess; gauge: RGFlow SU2TransferMatrix CosineAction
- **E/R/R.** _Elements:_ конкретные рациональные поправки rg_correction_quartic/sextic β как Q; пороги delta_quartic=1#32, delta_sextic=1#768; степени β².β⁴. _Roles:_ поправка порядка n = роль-уточнение шага RG (вклад члена ряда θ^{2n}); граница δ = роль-оценка величины уточнения. _Rules:_ обратная антитонность /(β²)<=1/4 ⟹ \|correction\|<=δ; знак (кварт.<0, секст.>0); инвариант интервала rg_map_*[2,4]→[2,4]; факториальный спад δ_sextic<δ_quartic. _P4:_ Финитная актуальность: усечённый РЯД (квадратичный+кварт.+секст.) — конечно-актуализированное приближение бесконечного 1-cos(θ); каждая поправка — конкретный Element-член, а полный непертурбативный предел остаётся role-limit. Геометрический спад (correction_geometric_decay) делает усечение контролируемым на каждом конечном порядке.
- **Classical counterpart.** Taylor expansion of the Wilson plaquette action 1-cos(θ) to quartic (θ⁴/24) and sextic (θ⁶/720) order, controlling higher-loop corrections to the strong-coupling RG map. NEW here is only the explicit rational interval-arithmetic packaging: the corrections are -1/(8β²) and +1/(48β⁴), bounded by 1/32 and 1/768 on [2,4], with factorially shrinking magnitude.
- **Tags.** gauge, rg-flow, taylor, interval-arithmetic, perturbation, su2, methods

**Lemmas (30):**

| name | kind | role |
|---|---|---|
| `beta_sq_pos` | Lemma | 0<β ⟹ 0<β² (база положительности) |
| `beta_sq_lower` | Lemma | 2<=β ⟹ 4<=β² |
| `beta_fourth_pos` | Lemma | 0<β ⟹ 0<β⁴ |
| `beta_fourth_lower` | Lemma | 2<=β ⟹ 16<=β⁴ |
| `beta_sq_inv_upper` | Lemma | антитонность: 2<=β ⟹ /(β²)<=1/4 |
| `beta_fourth_inv_upper` | Lemma | 2<=β ⟹ /(β⁴)<=1/16 |
| `rg_correction_quartic` | Definition | кварт. поправка к RG: -(1#8)·/(β²) |
| `rg_map_quartic` | Definition | линейный RG + кварт. поправка |
| `delta_quartic` | Definition | порог кварт. поправки: 1#32 |
| `quartic_correction_negative` | Lemma | кварт. поправка <0 при β>0 |
| `quartic_correction_at_3` | Lemma | точное значение в β=3: -(1#72) |
| `quartic_correction_bound` | Lemma | ★ \|кварт. поправка\|<=1/32 на [2,4] |
| `rg_quartic_close_to_linear` | Lemma | \|linear-quartic\|<=δ_quartic |
| `rg_quartic_maps_interval` | Lemma | квартичный RG переводит [2,4]→[2,4] |
| `rg_correction_sextic` | Definition | секст. поправка: (1#48)·/(β⁴) |
| `rg_map_sextic` | Definition | квартичный RG + секст. поправка |
| `delta_sextic` | Definition | порог секст. поправки: 1#768 |
| `sextic_correction_positive` | Lemma | секст. поправка >0 при β>0 |
| `sextic_correction_bound` | Lemma | \|секст. поправка\|<=1/768 на [2,4] |
| `rg_sextic_close_to_linear` | Lemma | \|linear-sextic\|<=δ_quartic+δ_sextic (через треугольник) |
| `rg_sextic_maps_interval` | Lemma | секстичный RG переводит [2,4]→[2,4] |
| `total_correction_bound` | Lemma | δ_quartic+δ_sextic<1/10 (импортируется в GlobalMassGap) |
| `correction_ratio` | Lemma | δ_sextic<=δ_quartic·(1#24) (факториальный рост знаменателя) |
| `correction_geometric_decay` | Theorem | δ_sextic<δ_quartic и сумма<1/10 (геометрический спад) |
| `higher_order_rg_summary` | Theorem | сводка: обе границы + оба инварианта интервала + суммарная граница |
| `quartic_rg_main` | Theorem | конъюнкция кварт.: граница 1/32 + инвариант интервала |
| `sextic_rg_main` | Theorem | конъюнкция секст.: граница 1/768 + инвариант интервала |
| `all_corrections_bounded` | Theorem | \|linear-sextic\|<=1/10 (совокупная оценка) |
| `higher_order_structure` | Theorem | ★ \|секст.\|<\|кварт.\| поточечно (каждый порядок добавляет меньше) |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`quartic_correction_bound`** - Несущая лемма файла: \|-(1#8)/(β²)\|<=1/32 на [2,4] через антитонность обратной (/(β²)<=1/4) и Qmult_le_compat_l. Это конкретное Element-ограничение одного члена ряда — оценка, которую GlobalMassGap затем складывает в total_correction_bound<1/10, чтобы заявить, что поправки высшего порядка не разрушают щель. Стандартное оценивание остаточного члена Тейлора, выполненное в точной Q-арифметике вместо ε-δ над R. _(taylor-remainder, interval-arithmetic, rg-correction, load-bearing)_
- **`higher_order_structure`** - Доказывает поточечно \|секст.\|<\|кварт.\|: каждый следующий порядок ряда вносит строго меньшую поправку. Содержательно это машинно-проверенное проявление факториального спада коэффициентов 1-cos(θ) (1/24 vs 1/720) на интервале [2,4]. Не новый результат — это причина, по которой пертурбативное усечение вообще законно, — но честно формализованный как теорема, а не предположение. _(geometric-decay, perturbation-ordering, factorial)_

**Uniqueness - score 2 (methods).** Точная рациональная интервальная упаковка тейлоровских поправок RG-отображения: явные формы -1/(8β²),+1/(48β⁴), машинные границы 1/32 и 1/768 и доказанный поточечный факториальный спад порядков на [2,4].
> _Caveat:_ Стандартное оценивание остаточного члена Тейлора 1-cos(θ); ценность — в точной Q-арифметике и встраивании в gauge-программу, не в новой математике. Сама структура поправок (как и весь RG-кластер) — конкретная модель, не континуумная YM. ДРЕЙФ: заголовок ~25 Qed, фактически 24.

---

## #468 - `src/gauge/HilbertConstruction.v` - score 2 (methods)

**Wightman-QFT из диагональной трансфер-матрицы: конкретная запись WightmanQFT, W1-W5 и мост OS→Wightman**

- **Topic.** Строит явную вайтмановскую КТП из диагональной трансфер-матрицы как конечномерный объект: гильбертово пространство = конечный ортонормированный базис, гамильтониан диагонален (E_j=1-t_j/t₀), вакуум = основное состояние, щель Δ=E₁-E₀>0. Аксиомы Остервальдера-Шрадера сводятся к элементарным фактам.
- **Role.** Конструктивный лист: упаковывает результаты CharacterTransfer/ExactMassGap/GapRatio/TransferMatrixProof/ReflectionPositiveProof/ClusterProof в Record WightmanQFT и теоремы W*/OS→W. Конкретные значения β=1,2; на него никто не опирается обратно.
- **Counts.** Qed 18 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: CauchyReal SeriesConvergence; gauge: CharacterTransfer ExactMassGap GapRatio TransferMatrixProof ReflectionPositiveProof ClusterProof ReflectionPositivity
- **E/R/R.** _Elements:_ конкретные КТП-объекты wqft_at_1, wqft_at_2 (β=1,2); собственные энергии matrix_energy J β M j как Q; вакуум wqft_vacuum=0. _Roles:_ WightmanQFT = арена-объект (гильбертово пространство+гамильтониан+вакуум); E_j = роль-уровень энергии; щель wqft_gap = роль-наблюдаемая; OS→W = роль-мост (реконструкция). _Rules:_ ортонормальность δ_jk из диагональности; W4-локальность = коммутативность скаляров (ring); вакуум = основное состояние (=0); OS4 RP⟹гильбертово пр-во; gap=E₁-E₀>0. _P4:_ Финитная актуальность доведена до предела: гильбертово пространство КОНЕЧНОМЕРНО (J+1 базисных векторов) — реконструкция Остервальдера-Шрадера, обычно требующая континуумных пределов, здесь тривиализуется, потому что нет бесконечности. Element-сторона полностью; континуумная КТП (бесконечный объём, непрерывный спектр) — role-limit, не строится.
- **Classical counterpart.** Osterwalder-Schrader reconstruction (Euclidean correlators → Wightman QFT) and the Wightman axioms W1-W5. NEW here is that the whole construction is TRIVIAL/EXPLICIT because the transfer matrix is DIAGONAL: the Hilbert space is a finite orthonormal basis, the Hamiltonian is diagonal with E_j=1-t_j/t₀, and the OS axioms collapse to elementary facts (locality = commutativity of scalars, ring).
- **Tags.** gauge, wightman, os-reconstruction, hilbert-space, transfer-matrix, mass-gap, finite-dim, methods, millennium-aspirational

**Lemmas (22):**

| name | kind | role |
|---|---|---|
| `WightmanQFT` | Record | конкретная запись физ. гильбертова пр-ва: {J, β, M, вакуум, щель + доказательства} |
| `wqft_at_1` | Definition | конструкция WightmanQFT при β=1 (J=1) |
| `wqft_at_2` | Definition | конструкция WightmanQFT при β=2 (J=1) |
| `wqft_make` | Lemma | общий конструктор: для J≥1, 0<β<=2 строит WightmanQFT с заданными полями (Defined, для вычислений) |
| `w1_hilbert_exists` | Theorem | W1: гильбертово пр-во существует (J≥1, конечномерно) |
| `w3_ground_zero_1` | Theorem | W3: энергия основного состояния = 0 (β=1) |
| `w3_excited_positive_1` | Theorem | W3: первая возбуждённая энергия >0 (β=1) |
| `w3_excited_positive_2` | Theorem | W3: первая возбуждённая энергия >0 (β=2) |
| `w4_locality` | Theorem | ★ W4-локальность: диагональные операторы коммутируют тривиально (ring) |
| `w5_vacuum_unique` | Theorem | W5: вакуум невырожден (=основное состояние, =0) |
| `wightman_mass_gap_1` | Theorem | ★ щель>0 в вайтмановском языке при β=1 |
| `wightman_mass_gap_2` | Theorem | ★ щель>0 в вайтмановском языке при β=2 |
| `wightman_gap_positive_from_energy` | Theorem | энергетическая щель >0 для всех J при β=1 и β=2 |
| `os4_to_w1` | Theorem | OS4→W1: рефлексионная положительность ⟹ гильбертово пр-во (0<=rp_inner_matrix) |
| `os5_to_w5` | Theorem | OS5→W5: кластерное свойство ⟹ единственный вакуум (β=1,2) |
| `energy_gap_to_mass_gap` | Theorem | энергетическая щель ⟹ массовая щель (E₁-E₀>0) |
| `os_to_wightman_at_1` | Theorem | OS→Wightman: ∃ КТП со щелью>0 (β=1) |
| `os_to_wightman_at_2` | Theorem | OS→Wightman: ∃ КТП со щелью>0 (β=2) |
| `os_to_wightman_general` | Theorem | ★ для любого β∈(0,2] строит WightmanQFT с щелью=matrix_energy_gap 1 β 0 |
| `hilbert_construction_summary` | Theorem | сводка: ∃ КТП + OS4 + OS5 + энергетические щели |
| `wightman_axioms_summary` | Theorem | сводка: W1+W4+W5+щель>0 проверены |
| `os_wightman_complete` | Theorem | ★ финал: OS4+OS5+∃КТП+значения щелей — полная конструкция |

**Key lemmas (deep):**

- **`os_to_wightman_general`** - Содержательная вершина файла: для ЛЮБОГО β∈(0,2] строит конкретный объект WightmanQFT с щелью, равной matrix_energy_gap 1 β 0. Это локальный аналог реконструкции Остервальдера-Шрадера, но тривиализованной: трансфер-матрица диагональна, поэтому гильбертово пространство, гамильтониан и вакуум выписываются явно и конечномерно, без аналитических пределов. Распространяется на интервал β, но строго на J=1 (двухуровневую) SU(2)-модель. _(os-reconstruction, wightman, explicit-construction, finite-dim)_
- **`w4_locality`** - Показательно для природы файла: аксиома локальности Вайтмана (коммутативность пространственно-разделённых операторов) доказывается тактикой ring — потому что диагональные элементы трансфер-матрицы суть скаляры Q, и pq=qp тривиально. Это честно демонстрирует, что вся 'конструкция КТП' покупается ценой диагональности (нет настоящих некоммутирующих полевых операторов), т.е. это модель-витрина аксиоматики, а не нетривиальная QFT. _(wightman-axiom, locality, diagonal-triviality, ring)_

**Uniqueness - score 2 (methods).** Полностью явная конечномерная вайтмановская КТП из диагональной трансфер-матрицы: Record WightmanQFT, аксиомы W1-W5 и мост OS→Wightman доказаны для всего интервала β∈(0,2], демонстрируя реконструкцию Остервальдера-Шрадера без континуумных пределов.
> _Caveat:_ НЕ континуумная Yang-Mills КТП: гильбертово пр-во конечномерно (J=1, два уровня), локальность тривиальна (ring, скаляры), 'аксиомы' сводятся к элементарным фактам именно из-за диагональности. Это модель-витрина OS/Wightman-аксиоматики, не нетривиальная QFT. Имена wightman_mass_gap/os_wightman_complete аспирационны. ДРЕЙФ: заголовок ~30 Qed, фактически 18.

---

## #469 - `src/gauge/InstantonEnhanced.v` - score 2 (methods)

**Достаточная поправка спасает щель: любой δ_k≥m>0 поднимает gap; струнное натяжение σ(β_k)>3/32 всегда даёт пол**

- **Topic.** Атака 3: какая МИНИМАЛЬНАЯ поправка не даёт щели обнулиться. Вводит каркас sufficient_correction (равномерная нижняя граница m>0) и показывает три физических механизма: константная (струнное натяжение), инстантонная плотность (растёт как 2^k) и натяжение σ(β_k)→3/32, которое строго >3/32 при β_k<8.
- **Role.** Поставщик 'достаточной поправки' для программы щели; зависит от TransferMatrix/SU2TransferMatrix/StrongCoupling/GapDecayRate/ConfinementCorrection. Лист-аргумент 'стена при β=8 — артефакт'; обратных импортов нет.
- **Counts.** Qed 15 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: CauchyReal SeriesConvergence; gauge: TransferMatrix SU2TransferMatrix StrongCoupling GapDecayRate ConfinementCorrection
- **E/R/R.** _Elements:_ конкретные поправки instanton_correction w k=w·2^k, tension_correction β k=σ(β_k); пороги 3#32; corrected_gap β δ k как Q. _Roles:_ sufficient_correction = роль-условие (есть равномерный пол m>0); δ:nat→Q = роль-процесс поправок по масштабам k; corrected_gap = роль-наблюдаемая (поправленная щель). _Rules:_ достаточность: m>0 ∧ ∀k m<=δ k ⟹ ∀k m<=corrected_gap; σ(β_k)>3/32 из β_k<8 (антитонность обратной); 2^k>=1 ⟹ инстантон>=w. _P4:_ Финитная актуальность: базовая щель su2_gap_at_k→0 как НЕДОСТИЖИМЫЙ предел (role-limit), но поправка δ_k оценивается на КАЖДОМ конечном масштабе k (Element) и держит corrected_gap>0. Сам файл маркирует результат как УСЛОВНЫЙ (conditional_mass_gap): щель спасена ПРИ наличии достаточной поправки — посылка, а не вывод.
- **Classical counterpart.** Strong-coupling expansion of confinement: string tension σ(β)=3/(4β), instanton density ~2^k in 1+1D, and the idea that a non-perturbative correction keeps the mass gap from closing at the deconfinement coupling. NEW here is only the explicit rational 'sufficient correction' framework: any δ_k≥m>0 lifts the gap, and string tension σ(β_k)>3/32 is shown to supply such a uniform floor.
- **Tags.** gauge, mass-gap, string-tension, instanton, strong-coupling, conditional, confinement, methods, millennium-aspirational

**Lemmas (20):**

| name | kind | role |
|---|---|---|
| `corrected_gap` | Definition | поправленная щель: su2_gap_at_k β k + δ k |
| `sufficient_correction` | Definition | ★ достаточная поправка: 0<m ∧ ∀k, m<=δ k (равномерный пол) |
| `corrected_gap_bounded` | Theorem | при достаточной поправке: m<=corrected_gap для всех k |
| `corrected_gap_positive` | Theorem | поправленная щель >0 при достаточной поправке |
| `corrected_gap_limit` | Theorem | базовая щель →0, но δ_k>=m>0 держит поправленную >0 (= corrected_gap_positive) |
| `constant_correction_sufficient` | Theorem | константа σ>0 — достаточная поправка |
| `instanton_correction` | Definition | инстантонная поправка: w·Qpow 2 k (плотность ~2^k) |
| `instanton_correction_grows` | Lemma | инстантон >=w (т.к. 2^k>=1) |
| `instanton_correction_sufficient` | Theorem | инстантонная плотность — достаточная поправка с m=w |
| `tension_correction` | Definition | поправка струнным натяжением: string_tension(β_k) |
| `tension_correction_positive` | Lemma | натяжение-поправка >0 при 0<β<8 |
| `tension_correction_lower` | Lemma | ★ натяжение-поправка >3/32 всегда (т.к. β_k<8, антитонность обратной) |
| `tension_correction_sufficient` | Theorem | натяжение — достаточная поправка с m=3/32 |
| `tension_provides_gap` | Theorem | натяжение даёт corrected_gap>0 |
| `attacks_converge` | Theorem | ★ три атаки сходятся: σ(8)>0, gap_2x2(8)=0, натяжение⟹gap>0, K=3 gap=5/18>0 |
| `conditional_mass_gap` | Theorem | ★ УСЛОВНАЯ щель: натяжение достаточно И даёт gap>0 |
| `wall_is_artifact` | Theorem | стена K=2 (gap_2x2(8)=0) — артефакт: с натяжением gap>0 |
| `instanton_main` | Theorem | ★ ГЛАВНАЯ: σ(β_k)>3/32 ⟹ достаточная поправка ⟹ gap>0 |
| `what_we_need` | Theorem | что нужно: поправка >=3/32 (= tension_correction_sufficient) |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`tension_correction_lower`** - Несущая лемма: σ(β_k)=3/(4β_k)>3/32 для всех k, потому что β_k<8 даёт /β_k>1/8 (антитонность обратной, Qinv_lt_contravar). Это конкретный равномерный пол поправки, который затем поднимает базовую (стремящуюся к нулю) щель. Содержательно — оценка строго-связной (strong-coupling) серии в точной Q-арифметике; ценность в явном числе 3/32, а не в новой физике. _(string-tension, uniform-floor, strong-coupling, load-bearing)_
- **`conditional_mass_gap`** - Самая честная теорема файла: щель спасена УСЛОВНО — при наличии достаточной поправки tension_correction. Это посылка-каркас (sufficient_correction — гипотеза, не вывод из первых принципов непертурбативной YM), а wall_is_artifact лишь утверждает, что обнуление gap_2x2(8) есть артефакт усечения K=2, снимаемый добавлением натяжения. Файл явно остаётся на стороне 'если есть пол m>0', не доказывая, что непертурбативная динамика этот пол создаёт. _(conditional, framework-hypothesis, honesty, deconfinement-wall)_

**Uniqueness - score 2 (methods).** Явный рациональный каркас 'достаточной поправки' (равномерный пол m>0 поднимает щель) с тремя инстанцированиями — константа, инстантонная плотность ~2^k, струнное натяжение σ(β_k)>3/32 — все в точной Q-арифметике.
> _Caveat:_ Результат УСЛОВНЫЙ (сам файл: conditional_mass_gap): щель спасена ПРИ достаточной поправке, которая ВВОДИТСЯ как гипотеза, а не выводится из непертурбативной YM. 'wall_is_artifact' = снятие артефакта усечения K=2, не доказательство континуумной щели. Конкретно SU(2), малые K. ДРЕЙФ: заголовок ~20 Qed, фактически 16.

---

## #470 - `src/gauge/IrrelevantOperators.v` - score 2 (methods)

**Решёточные артефакты как иррелевантные операторы O(a²): размер 1/(24β), убывание по β, dim=6>4, восстановление SO(4)**

- **Topic.** Квантифицирует операторы, нарушающие SO(4) на решётке, и их скейлинг: артефакт lattice_artifact_size=1/(24β) (из члена θ⁴/24 разложения Вильсона), собственнозначный артефакт ∝j(j+1)/(24β), анизотропия 1/β. Доказывает положительность, монотонное убывание по β и классифицирует их как иррелевантные (dim 6>4).
- **Role.** Лист-обоснование континуумного предела: артефакты убывают, SO(4) восстанавливается. Зависит от CharacterTransfer/ExactMassGap/GapRatio/LatticeRG; самодостаточная классификация, обратных импортов нет.
- **Counts.** Qed 24 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: CauchyReal SeriesConvergence; gauge: CharacterTransfer ExactMassGap GapRatio LatticeRG
- **E/R/R.** _Elements:_ конкретные рациональные размеры артефактов lattice_artifact_size β=1/(24β), eigenvalue_artifact j β, anisotropy β=1/β; целые artifact_dimension=6, artifact_scaling_power=2. _Roles:_ артефакт = роль-мера нарушения SO(4) (отклонение решётки от континуума); скейлинговая размерность d = роль-классификатор (релевантный/маргинальный/иррелевантный); анизотропия = роль-наблюдаемая направленной зависимости. _Rules:_ артефакт ∝1/β ⟹ убывает с β (антитонность); halving при удвоении β; иррелевантность = 4<d (nat); скейлинг a^{d-4}=a²; artifact<=anisotropy. _P4:_ Финитная актуальность: артефакты — конечная (Element) мера того, насколько решётка-с-шагом-a отстоит от континуума; континуумный предел a→0 (β→∞) есть НЕДОСТИЖИМЫЙ role-limit-процесс, к которому артефакты монотонно убывают, но не обнуляются ни на каком конечном β. SO(4) восстанавливается только в пределе; на любом Element-шаге симметрия лишь гиперкубическая.
- **Classical counterpart.** Symanzik's theory of lattice artifacts as irrelevant operators of dimension >4 scaling as a^(d-4), restoring continuum rotational SO(4) symmetry as a→0. NEW here is only the explicit rational packaging: artifact size 1/(24β), eigenvalue artifact ∝ j(j+1)/(24β), anisotropy 1/β — all proven positive, monotonically decreasing in β, with the irrelevance encoded as the nat fact 4<dimension=6.
- **Tags.** gauge, lattice-artifact, symanzik, irrelevant-operator, continuum-limit, so4-restoration, scaling-dimension, methods

**Lemmas (30):**

| name | kind | role |
|---|---|---|
| `lattice_artifact_size` | Definition | размер решёточного артефакта: 1/(24β) (из θ⁴/24) |
| `artifact_positive` | Lemma | артефакт >0 при β>0 |
| `artifact_decreasing` | Lemma | ★ артефакт убывает по β (антитонность обратной) |
| `artifact_at_beta_1` | Lemma | артефакт(1)=1/24 |
| `artifact_at_beta_2` | Lemma | артефакт(2)=1/48 |
| `artifact_halves` | Lemma | артефакт(2β)=(1/2)·артефакт(β) (поле, field) |
| `symmetry_breaking_size` | Definition | размер нарушения SO(4) = размер артефакта |
| `symmetry_breaking_positive` | Lemma | нарушение SO(4) >0 при β>0 |
| `symmetry_breaking_decreasing` | Lemma | нарушение SO(4) убывает по β |
| `eigenvalue_artifact` | Definition | артефакт собств. значения: j(j+1)/(24β) |
| `eigenvalue_artifact_nonneg` | Lemma | артефакт собств. значения >=0 |
| `eigenvalue_artifact_zero_for_j0` | Lemma | артефакт=0 при j=0 (основное состояние не сдвигается) |
| `eigenvalue_artifact_small` | Lemma | при β>=1: артефакт<=j(j+1)/24 |
| `eigenvalue_artifact_decreasing` | Lemma | артефакт собств. значения убывает по β |
| `gap_artifact_bound` | Theorem | \|gap_решётка-gap_континуум\| ограничен: 0<=eigenvalue_artifact 1 β |
| `artifact_j1` | Lemma | артефакт при j=1 = 2/(24β) |
| `artifact_j1_bound` | Lemma | артефакт при j=1 = 1/(12β) |
| `anisotropy` | Definition | анизотропия (направленная зависимость корреляторов): 1/β |
| `anisotropy_positive` | Lemma | анизотропия >0 при β>0 |
| `anisotropy_decreasing` | Lemma | анизотропия убывает по β |
| `anisotropy_at_beta_1` | Lemma | анизотропия(1)=1 |
| `anisotropy_at_beta_2` | Lemma | анизотропия(2)=1/2 |
| `anisotropy_bound` | Lemma | артефакт<=анизотропия (lattice_artifact_size<=1/β) |
| `anisotropy_controls_breaking` | Theorem | анизотропия мажорирует нарушение SO(4) |
| `artifact_dimension` | Definition | скейлинговая размерность артефактов: 6 (F⁴ имеет 4+2) |
| `artifact_scaling_power` | Definition | степень скейлинга: 2 (=d-4) |
| `artifact_is_irrelevant` | Lemma | ★ 4<artifact_dimension (иррелевантность как nat-факт) |
| `scaling_from_dimension` | Lemma | степень скейлинга = размерность-4 |
| `all_artifacts_irrelevant` | Theorem | все артефакты d>=6 ⟹ исчезают под RG |
| `irrelevant_operators_summary` | Theorem | сводка: артефакт+анизотропия положительны и убывают, dim>4 |

**Key lemmas (deep):**

- **`artifact_decreasing`** - Несущая лемма аналитической части: lattice_artifact_size β=1/(24β) строго убывает по β (через Qinv_lt_contravar). Это точная рациональная запись симанзиковского факта 'решёточные артефакты сжимаются при приближении к континууму'. Монотонность по β = монотонность по 1/a; вместе с halving (артефакт(2β)=½артефакт(β)) даёт явный скейлинг O(a²). Стандартная теория иррелевантных операторов, выполненная в Q вместо асимптотики. _(symanzik, lattice-artifact, monotone, continuum-limit, load-bearing)_
- **`artifact_is_irrelevant`** - Концептуальное ядро, сведённое к арифметике nat: иррелевантность операторов закодирована как 4<artifact_dimension=6 (F⁴ имеет размерность 6>4), а степень скейлинга a^{d-4}=a² — как scaling_from_dimension. Это честный, но минималистичный захват классификации Уилсона/Симанзика: 'релевантный/маргинальный/иррелевантный' определяется одним сравнением d с 4. Размерность 6 ВПИСАНА как Definition, а не выведена из теории представлений — т.е. это кодировка известного факта, не его доказательство. _(scaling-dimension, irrelevant-operator, wilson-classification, encoded-fact)_

**Uniqueness - score 2 (methods).** Точная рациональная квантификация решёточных артефактов как иррелевантных операторов O(a²): размер 1/(24β), собственнозначный артефакт ∝j(j+1)/(24β), анизотропия 1/β — все доказаны положительными и монотонно убывающими по β, с иррелевантностью как nat-фактом 4<6.
> _Caveat:_ Стандартная теория Симанзика об иррелевантных операторах, переписанная в точной Q-арифметике; размерность d=6 ВПИСАНА как Definition (кодировка), а не выведена. Восстановление SO(4) — только в недостижимом пределе a→0; на любом конечном β симметрия гиперкубическая. Конкретная решёточная модель, не континуумная YM. ДРЕЙФ: заголовок ~35 Qed, фактически 24.

---

## #471 - `src/gauge/KDependence.v` - score 2 (methods)

**Mass gap vs discretization fineness K: the gap=0 at beta=8 is a K=2 artifact**

- **Topic.** Builds a 3x3 transfer matrix from angle discretization K=3 (theta in {0,1/3,2/3}), shows (1,0,-1) is an eigenvector with eigenvalue 16/9, bounds the restricted 2x2 eigenvalues below 3/2, and concludes the K=3 gap at beta=8 is >= 5/18 > 0 while the K=2 gap there is exactly 0.
- **Role.** Attack-2 file of the lattice mass-gap programme: argues a known vanishing point of the 2-site gap is a discretization artifact. Imports gauge.TransferMatrix (mass_gap_2x2) and gauge.GapDecayRate (gap_vanishes_at_8). Reuses mass_gap_2x2 only; not itself a hub.
- **Counts.** Qed 31 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS.CauchyReal; gauge.TransferMatrix; gauge.GapDecayRate
- **E/R/R.** _Elements:_ конкретные углы theta_i={0,1/3,2/3}, записи матрицы t3_entry beta i j, собственный вектор v101=(1,0,-1), все над точным Q. _Roles:_ K = разрешение дискретизации (грань-роль конечности); собственное значение 16/9 = ground-роль; ограниченный спектр <3/2 = возбуждённая-роль; их разность = щель. _Rules:_ T_{ij}=1-(beta/2)(theta_i-theta_j)^2; char_poly_restricted lambda = lambda^2-(11/9)lambda-32/81; щель = 16/9 - max(огранич. корни). _P4:_ K — это Element-разрешение конечной актуальности: при K=2 (грубее) щель схлопывается в 0, при K=3 (тоньше) она >=5/18; ноль — артефакт выбора числа углов, а не физики. Истинный предел K->inf (бесконечная актуальность) НЕ вычислен — это role-limit-сторона, оставленная открытой.
- **Classical counterpart.** Lattice gauge theory: transfer-matrix spectral gap, character/heat-kernel discretization of the link angle, and the continuum-limit question. Classically the spectral gap of a finite transfer matrix is computed by exact diagonalization; NEW here is only the E/R/R framing of K as an Element-resolution dial and the explicit two-point (K=2 vs K=3) artifact contrast at beta=8. The restricted-root claim is argued, not formalized.
- **Tags.** gauge, transfer-matrix, mass-gap, eigenvalue, exact-Q, discretization, finite-lattice, honest-scope
- **Notes.** qed actual = 32 (header says ~30, approximate). 0 Admitted, 0 own axioms. restricted_roots_lt_3_2 and eigenvalue_16_9_not_restricted_root are stated as polynomial-sign facts (p(3/2)>0, p(16/9)>0); the step from sign to actual root location is in a prose comment, not formalized. Theorem names large_K_gap_structural / k_dependence_result are about K=3 specifically, not large K.

**Lemmas (38):**

| name | kind | role |
|---|---|---|
| `angle_dist_sq` | Definition | квадрат расстояния (Delta theta)^2 между индексами углов 0..2 (таблица 3x3) |
| `t3_entry` | Definition | запись 3x3 трансфер-матрицы: 1 - beta*(1/2)*angle_dist_sq i j |
| `t3_symmetric` | Lemma | матрица симметрична: t3_entry beta i j == t3_entry beta j i (i,j<3) |
| `t3_diagonal_one` | Lemma | диагональные записи равны 1 (i<3) |
| `t3_entry_00_at_8` | Lemma | конкретно T(8)_00 == 1 |
| `t3_entry_01_at_8` | Lemma | T(8)_01 == 5/9 |
| `t3_entry_02_at_8` | Lemma | T(8)_02 == -7/9 |
| `t3_entry_11_at_8` | Lemma | T(8)_11 == 1 |
| `t3_entry_12_at_8` | Lemma | T(8)_12 == 5/9 |
| `t3_entry_22_at_8` | Lemma | T(8)_22 == 1 |
| `vec3` | Definition | тип 3-компонентного вектора nat->Q |
| `v101` | Definition | вектор (1,0,-1) |
| `t3_apply` | Definition | матрично-векторное произведение (T.v)_i = сумма по j T_{ij} v_j |
| `eigenvec_101_row0` | Lemma | (T(8).v101)_0 == 16/9 (vm-проверка строки) |
| `eigenvec_101_row1` | Lemma | (T(8).v101)_1 == 0 |
| `eigenvec_101_row2` | Lemma | (T(8).v101)_2 == -16/9 |
| `eigenvec_101_eigenvalue` | Theorem | ★ (1,0,-1) — собственный вектор с собственным значением 16/9 (все 3 строки) |
| `eigenvalue_16_9_positive` | Lemma | 0 < 16/9 |
| `char_poly_restricted` | Definition | характ. многочлен ограниченной 2x2: lambda^2-(11/9)lambda-32/81 |
| `char_poly_at_0` | Lemma | p(0) == -32/81 |
| `char_poly_at_0_negative` | Lemma | p(0) < 0 |
| `char_poly_at_3_2` | Lemma | p(3/2) == 7/324 |
| `char_poly_at_3_2_positive` | Lemma | ★ 0 < p(3/2) (оба огранич. корня < 3/2) |
| `char_poly_at_16_9` | Lemma | p(16/9) == 48/81 |
| `char_poly_at_16_9_positive` | Lemma | 0 < p(16/9) |
| `restricted_roots_lt_3_2` | Theorem | оба корня < 3/2 (формулируется как p(3/2)>0; вербальный аргумент в комментарии) |
| `eigenvalue_16_9_not_restricted_root` | Theorem | 16/9 не корень огранич. многочлена (p(16/9)>0) |
| `t3_gap_at_8` | Theorem | 0 < 16/9 - 3/2 |
| `t3_gap_at_8_value` | Theorem | 16/9 - 3/2 == 5/18 |
| `t3_gap_at_8_positive` | Theorem | 0 < 5/18 |
| `k2_vs_k3_at_8` | Theorem | K=2 щель=0 И K=3 щель>=5/18 — контраст в одном утверждении |
| `wall_is_k2_artifact` | Theorem | ★ стена gap=0 при beta=8 специфична для K=2; K=3 даёт >0 |
| `k3_gap_survives_orbit` | Theorem | K=3 щель>0 пока K=2 щель=0 (повтор контраста) |
| `k_dependence_main` | Theorem | ★ свод: K=2 ноль + собственное значение 16/9 + p(3/2)>0 + 5/18>0 |
| `k3_mass_gap_conditional` | Theorem | условная K=3 щель: собств. вектор проверен И p(3/2)>0 |
| `large_K_gap_structural` | Theorem | структурный результат большого K: 0 < 16/9 - 3/2 (по сути тот же 5/18) |
| `k_dependence_result` | Theorem | итог Attack-2: стена есть K=2 артефакт; вопрос сводится к gap(K,8) при K->inf |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`eigenvec_101_eigenvalue`** - Несущая лемма: точная (vm_compute/lia над Q) проверка, что антисимметричная мода (1,0,-1) диагонализует 3x3 трансфер-матрицу при beta=8 с собственным значением 16/9. Это конкретное собств.-значение, а не приближение, что даёт жёсткую нижнюю границу щели. Распознаваемо классично (точная диагонализация маленькой матрицы); новизны в методе нет — ценность в постановке. _(transfer-matrix, eigenvalue, exact-Q, K=3)_
- **`wall_is_k2_artifact`** - Концептуальное ядро файла: показывает, что известная точка обнуления 2-сайтовой щели при beta=8 НЕ универсальна — при K=3 щель >= 5/18. Честная сила результата мала: это сравнение ДВУХ фиксированных конечных дискретизаций (K=2 и K=3) в ОДНОЙ точке связи beta=8; вывод 'K=2-артефакт' корректен ровно как такое сравнение, и сам же файл честно формулирует открытый вопрос (остаётся ли щель ограниченной снизу при K->inf). Это НЕ доказательство массовой щели. _(artifact, honest-scope, K-dependence, open-problem)_
- **`char_poly_at_3_2_positive`** - Граница возбуждённого спектра: монику p(lambda)=lambda^2-(11/9)lambda-32/81 положителен при 3/2, что (для моники с положит. старшим коэф.) загоняет оба корня под 3/2, отделяя их от ground-значения 16/9. Заметна честная щель формализации: теорема restricted_roots_lt_3_2 утверждается лишь как p(3/2)>0, а импликация 'значит оба корня<3/2' дана прозой в комментарии, а не доказана о реальных корнях; вывод щели держится на этом неформализованном шаге. _(characteristic-polynomial, root-bound, formalization-gap)_

**Uniqueness - score 2 (methods).** Точная Q-диагонализация 3x3 трансфер-матрицы, показывающая, что обнуление 2-сайтовой щели при beta=8 снимается при K=3 (щель>=5/18); связь дискретизации с конечной актуальностью (P4).
> _Caveat:_ Конечно-решёточное вычисление в ОДНОЙ точке beta=8, сравнение двух фиксированных K (2 и 3) — НЕ континуумная массовая щель и НЕ Clay-результат; файл сам формулирует открытый вопрос K->inf. Импликация restricted_roots_lt_3_2 ('оба корня<3/2') дана прозой, не доказана о корнях. Названия large_K_*/k_dependence_result аспирационны (фактически про K=3). Header '~30 Qed' — приближение, фактически 32.

---

## #472 - `src/gauge/LargerLattice.v` - score 2 (methods)

**Conservative gap lower bound for N-site lattice: gap_lower_N = mass_gap_2x2(beta)/N_sp, Cauchy process**

- **Topic.** Defines a deliberately PESSIMISTIC lower bound on the N-site eigenvalue gap as the exact 2-site gap divided by N_sp, proves it positive and < 2 on beta in (0,8), monotone decreasing in lattice size, and that the dyadic gap_process k |-> gap at 2^k sites is decreasing+bounded hence Cauchy.
- **Role.** Bridge from the exact 2-site gap to an arbitrary-size scaffold: supplies a provable (if weak) bound that makes the exact RG process well-defined (GapMatching.v) and Cauchy (ExactRGProcess.v). Imports gauge.TransferMatrix (mass_gap_2x2*), MonotoneConvergence (q_dec_bounded_cauchy), FixedPoint, zeta.ZetaProcess.
- **Counts.** Qed 28 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs List Lia ZArith Lqa; ToS.CauchyReal; ToS.FixedPoint; ToS.MonotoneConvergence; gauge.TransferMatrix; zeta.ZetaProcess
- **E/R/R.** _Elements:_ размерность состояний lattice_state_dim K N_sp = K^{N_sp}; число N_sp сайтов; точная 2-сайтовая щель mass_gap_2x2 beta над Q. _Roles:_ gap_lower_N = консервативная нижняя граница (роль-пол щели); N_sp = размер решётки (грань конечности); gap_process = процесс-приближение по k. _Rules:_ gap_lower_N K N_sp beta = mass_gap_2x2 beta / N_sp; убывание по N_sp; gap_process k = gap_lower_N (2^k); Cauchy = убывание + ограниченность снизу нулём. _P4:_ решётка любого размера — конечный Element (K^{N_sp} состояний); граница задаётся как ЧЕСТНО доказуемый, но пессимистичный пол (gap->0 при N->inf). Истинная щель (нужная для Clay) НЕ ограничена снизу этим файлом — это явно названный role-limit. Процесс = потенциальная, не актуальная бесконечность размеров.
- **Classical counterpart.** Lattice gauge theory finite-volume spectral gap and its continuum/thermodynamic limit (the Yang-Mills mass-gap Millennium problem). Classically one needs a volume-INDEPENDENT lower bound; here the bound is the 2-site gap divided by N, which decreases to 0 — provably weaker than what the physics needs. NEW is only the process/Cauchy packaging (RealProcess := nat->Q) of the size-indexed bound, not any new gap estimate.
- **Tags.** gauge, mass-gap, lattice, process, cauchy, lower-bound, RG, honest-scope, classic-axiom
- **Notes.** qed actual = 29 (header says ~28, approximate). 0 Admitted, 0 OWN axioms; but file's STATUS header itself notes it depends on classic via MonotoneConvergence (q_dec_bounded_cauchy) for gap_process_cauchy. gap_lower_N is defined (not derived) as mass_gap_2x2/N_sp; it decays to 0, so the 'larger lattice' bound is strictly weaker than a mass gap.

**Lemmas (32):**

| name | kind | role |
|---|---|---|
| `lattice_state_dim` | Definition | размерность пространства состояний: K^{N_sp} |
| `lattice_dim_2_1` | Lemma | K=2,N=1 -> 2 состояния (наш 2x2 случай) |
| `lattice_dim_2_2` | Lemma | K=2,N=2 -> 4 состояния |
| `lattice_dim_2_3` | Lemma | K=2,N=3 -> 8 состояний |
| `pow2_pos` | Lemma | 1 <= 2^k (положительность степени двойки) |
| `pow2_increasing` | Lemma | 2^k <= 2^(k+1) |
| `pow2_strictly_increasing` | Lemma | 2^k < 2^(k+1) |
| `inject_Z_pos_local` | Lemma | 0<z -> 0 < inject_Z z (хелпер) |
| `inject_Z_le_local` | Lemma | монотонность inject_Z (хелпер) |
| `inject_Z_nat_pos` | Lemma | 1<=n -> 0 < inject_Z (Z.of_nat n) |
| `inject_Z_pow2_pos` | Lemma | 0 < inject_Z (2^k) |
| `inject_Z_pow2_nonzero` | Lemma | inject_Z (2^k) =/= 0 |
| `gap_lower_N` | Definition | ★ консервативная нижняя граница щели: mass_gap_2x2 beta / N_sp |
| `gap_lower_N_at_1` | Lemma | при N=1 граница = точная 2-сайтовая щель |
| `gap_lower_N_unfold` | Lemma | разворот через формулу (2 - beta/4)/N_sp |
| `gap_lower_N_positive` | Lemma | 0 < gap_lower_N при N>=1, beta in (0,8) |
| `gap_lower_N_pos_pow2` | Lemma | 0 < gap_lower_N при N=2^k |
| `mass_gap_le_2` | Lemma | mass_gap_2x2 beta <= 2 при beta>=0 |
| `gap_lower_N_lt_2` | Lemma | gap_lower_N < 2 при N>=1, beta in (0,8) |
| `gap_lower_N_bounded` | Lemma | 0 < gap_lower_N < 2 (свод границ) |
| `gap_lower_N_decreasing` | Lemma | ★ больше решётка -> меньше граница щели (моноотонность по N) |
| `gap_lower_halves` | Lemma | удвоение N не увеличивает границу (gap_lower_N(2N) <= gap_lower_N(N)) |
| `gap_lower_pow2_chain` | Lemma | gap_lower_N(2^(k+1)) <= gap_lower_N(2^k) |
| `gap_process` | Definition | процесс k \|-> gap_lower_N при 2^k сайтах |
| `gap_process_decreasing` | Lemma | процесс убывает |
| `gap_process_nonneg` | Lemma | процесс >= 0 |
| `gap_process_pos` | Lemma | процесс > 0 |
| `gap_process_cauchy` | Theorem | ★ gap_process — Cauchy (убывает + ограничен снизу 0) |
| `gap_process_at_0` | Lemma | gap_process 0 == точная 2-сайтовая щель |
| `gap_process_at_1` | Lemma | gap_process 1 == половина 2-сайтовой щели |
| `larger_lattice_main` | Theorem | ★ свод: граница >0, <2, убывает по N, процесс Cauchy |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`gap_process_cauchy`** - Несущая теорема: дыадический процесс границ щели убывает и ограничен снизу нулём, значит Cauchy (через q_dec_bounded_cauchy из MonotoneConvergence; завязан на axiom classic). Это даёт корректно определённый предел для RG-процесса вниз по течению. Честно: предел этой ПЕССИМИСТИЧНОЙ границы стремится к 0 при N->inf, то есть Cauchy-свойство НЕ даёт положительной массовой щели — оно лишь делает процесс-объект законным. _(cauchy, process, monotone, RG-scaffold)_
- **`gap_lower_N`** - Ключевое определение и одновременно главное ограничение файла: граница щели N-сайтовой решётки ОПРЕДЕЛЕНА как 2-сайтовая щель, делённая на N_sp. Это не вычисленная щель большой решётки, а заведомо заниженная мажоранта снизу; деление на N_sp — априорный пессимизм, а не спектральный факт. Всё дальнейшее (положительность, монотонность, Cauchy) следует из этой простой формулы. _(definition, pessimistic-bound, honest-scope)_
- **`gap_lower_N_decreasing`** - Монотонность: больше сайтов -> меньше (или равная) граница, через Qinv_le_compat на 1/N. Структурно честный сигнал того, что данный КОНКРЕТНЫЙ нижний пол вырождается с ростом решётки — ровно поэтому он не решает Millennium-вопрос, что комментарий файла прямо признаёт ('The Millennium Problem = prove the TRUE gap stays bounded below'). _(monotonicity, lattice-size, honest-scope)_

**Uniqueness - score 2 (methods).** Честный, доказуемый, но пессимистичный нижний пол щели для решётки любого размера, упакованный как убывающий Cauchy-процесс по дыадическим размерам — строительные леса для RG-процесса (GapMatching/ExactRGProcess).
> _Caveat:_ Граница ОПРЕДЕЛЕНА как 2-сайтовая щель / N и стремится к 0 при N->inf — это НЕ массовая щель и НЕ Clay-результат; файл сам это признаёт. Имя 'LargerLattice' аспирационно: реальной большой решётки не диагонализуется. Зависит от axiom classic (через MonotoneConvergence). Header '~28 Qed' — приближение, фактически 29.

---

## #473 - `src/gauge/Lattice3D.v` - score 1 (exposition)

**3D cubic lattice combinatorics: N^3 sites, 3N^3 links/plaquettes, Wilson action skeleton**

- **Topic.** Pure geometric bookkeeping for a 3D cubic lattice: site/link/plaquette counts (N^3, 3N^3, 3N^3), concrete values for the 2^3/4^3/8^3 lattices, a Wilson-action definition for SU(3), and scaling identities (links = 3*sites, plaquettes = links in 3D).
- **Role.** Foundational geometry layer reused by gauge.Lattice3DSynthesis (and the SU3 3D files) for the site/link/plaquette counts and wilson_action_3d. Imports only Stdlib QArith/Lia/ZArith; no ToS deps. Plumbing for the SU(3) lattice thread.
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lia ZArith Lqa
- **E/R/R.** _Elements:_ site3d=(nat,nat,nat), direction3d, счётчики num_sites_3d/num_links_3d/num_plaquettes_3d над nat; параметр решётки N. _Roles:_ геометрия 3D-решётки (роль-сцена для калибровочной теории); wilson_action_3d = роль-действие в функции от средней плакеты. _Rules:_ N^3 сайтов, 3N^3 связей, 3N^3 плакет (xy,xz,yz); S = beta*N_plaq*(1 - avg_plaq/3) для SU(3); связи = 3*сайты; плакеты = связи. _P4:_ решётка конечна по построению (N^3 — конкретный счёт Element'ов); ничего бесконечного. Это чистая комбинаторика сцены, без спектрального/динамического содержания — пол под последующими утверждениями о щели.
- **Classical counterpart.** Standard lattice gauge theory bookkeeping (Wilson 1974): site/link/plaquette counts of a hypercubic lattice and the Wilson plaquette action S=beta*sum(1-Re Tr U_P/N_c). Entirely textbook; NOTHING new beyond a clean Coq exposition of the counts. The E/R/R header is cosmetic over standard combinatorics.
- **Tags.** gauge, lattice, 3D, wilson-action, combinatorics, SU3, geometry, exposition
- **Notes.** qed actual = 13, header STATUS says '16 Qed, 0 Admitted, 0 new axioms' — real drift of -3 (only 13 Qed-terminated proofs present). 0 Admitted, 0 own axioms. Definitions site3d/direction3d are types, not proofs. No spectral content; pure scaffold for the SU3 3D files.

**Lemmas (19):**

| name | kind | role |
|---|---|---|
| `site3d` | Definition | тип сайта 3D-решётки: тройка nat |
| `direction3d` | Definition | направление (0=x,1=y,2=z) как nat |
| `num_sites_3d` | Definition | число сайтов: N*N*N |
| `num_links_3d` | Definition | число связей: 3*N*N*N |
| `num_plaquettes_3d` | Definition | число плакет: 3*N*N*N |
| `lattice_2cube_sites` | Lemma | 2^3 = 8 сайтов (reflexivity) |
| `lattice_2cube_links` | Lemma | 24 связи при N=2 |
| `lattice_2cube_plaquettes` | Lemma | 24 плакеты при N=2 |
| `lattice_4cube_sites` | Lemma | 4^3 = 64 сайта (стандартная малая решётка) |
| `lattice_4cube_links` | Lemma | 192 связи при N=4 |
| `lattice_4cube_plaquettes` | Lemma | 192 плакеты при N=4 |
| `lattice_8cube_sites` | Lemma | 8^3 = 512 сайтов |
| `wilson_action_3d` | Definition | действие Вильсона 3D: beta*N_plaq*(1 - avg_plaq/3) |
| `action_at_zero_field` | Lemma | при avg_plaq=3 (тривиальный калибр) действие = 0 |
| `action_at_random_field` | Lemma | при avg_plaq=0 действие = 1 (для beta=N_plaq=1) |
| `sites_scaling` | Lemma | num_sites_3d 4 = 8 * num_sites_3d 2 (масштаб N^3) |
| `links_eq_3_times_sites` | Lemma | связи = 3*сайты для любого N |
| `plaquettes_eq_links` | Lemma | плакеты = связи в 3D |
| `lattice_3d_synthesis` | Theorem | свод: 8/64 сайтов, 24 связи, действие тривиального калибра = 0 |

**Key lemmas (deep):**

- **`links_eq_3_times_sites`** - Единственная не-вычислительная (forall N) лемма содержания: 3N^3 = 3*N^3, фиксирующая стандартную комбинаторику кубической решётки (по 3 связи на сайт в 3D). Это учебная геометрия, доказанная lia; распознаваемо классична, новизны нет. Несущая лишь в смысле 'правильно задаёт сцену' для SU3-файлов выше по течению. _(lattice-geometry, combinatorics, exposition)_
- **`wilson_action_3d`** - Определение действия Вильсона в форме beta*N_plaq*(1-<plaq>/N_c) с N_c=3. Это скелет, а не динамика: единственные леммы про него — два конкретных значения (тривиальный калибр -> 0, случайный -> 1). Никакой минимизации, меры или спектра здесь нет; реальная физика щели живёт в импортирующих SU3-файлах. _(wilson-action, SU3, skeleton)_

**Uniqueness - score 1 (exposition).** Чистая, машинно-проверенная комбинаторика 3D кубической решётки (N^3 сайтов, 3N^3 связей/плакет) плюс скелет действия Вильсона для SU(3).
> _Caveat:_ Полностью стандартная учебная геометрия решётки и форма действия Вильсона; никакого спектрального/динамического содержания, никакой щели здесь не доказывается. Header заявляет '16 Qed' — ФАКТИЧЕСКИ 13 (drift -3). Имя файла нейтрально честное (геометрия, не 'proof').

---

## #474 - `src/gauge/Lattice3DSynthesis.v` - score 0 (infrastructure)

**3D SU(3) synthesis: ties 64-site geometry to gap_su3 = 5/6 and a positive partition function**

- **Topic.** A 5-lemma consolidation file: re-asserts the 4^3=64-site lattice geometry, the SU(3) gap value gap_su3 1 == 5/6 and partition-function positivity, that the spatial term enhances the 3D gap over the 1D gap, and bundles these into two capstone theorems.
- **Role.** Top consolidation of the SU(3) 3D thread. Pure re-export: every proof delegates to a lemma in gauge.Lattice3D / gauge.SU3Transfer / gauge.SU3Lattice3D. Imports exactly those three; reused (if at all) only as a one-line summary node.
- **Counts.** Qed 5 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lia ZArith Lqa; gauge.Lattice3D; gauge.SU3Transfer; gauge.SU3Lattice3D
- **E/R/R.** _Elements:_ наследуемые: 64-сайтовая геометрия, значение gap_su3 1 = 5/6, Z_su3_approx, gap_su3_3d над Q. _Roles:_ su3_3d_complete / phase2_complete = роли-капстоуны, связывающие геометрию + щель + статсумму в одно утверждение. _Rules:_ конъюнкция фактов: num_sites_3d 4=64 И gap_su3 1==5/6 И 0<Z И 0<gap_su3_3d; пространственный член усиливает щель (3d > 1d). _P4:_ ничего нового не актуализируется — файл лишь собирает уже-конечные Element-факты в связку; вся конечно-актуальная работа сделана в импортируемых файлах. Капстоун = наблюдение-свод, не новая актуализация.
- **Classical counterpart.** Lattice SU(3) strong-coupling expansion: an order-of-magnitude gap value (5/6) and the qualitative fact that adding spatial plaquettes increases the gap relative to a 1D chain. All numbers come from the imported files; this file mirrors nothing new beyond bundling. The label 'complete' has no classical analogue of completeness — it is local to these checks.
- **Tags.** gauge, SU3, 3D, synthesis, capstone, infrastructure, delegation, honest-scope
- **Notes.** qed actual = 5, matches header exactly. 0 Admitted, 0 own axioms. Every lemma is a delegation (exact ...) to gauge.Lattice3D / SU3Transfer / SU3Lattice3D. Names su3_3d_complete / phase2_complete are local-completeness labels, not a continuum SU(3) result.

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `lattice_is_3d` | Lemma | 64 сайта И 192 связи при N=4 (делегирует reflexivity) |
| `gap_and_Z` | Lemma | gap_su3 1 == 5/6 И 0 < Z_su3_approx 1 (делегирует gap_su3_at_1, Z_su3_positive_1) |
| `spatial_enhances_gap` | Lemma | gap_su3_3d 1 (1/100) > gap_su3_3d 1 0 (делегирует gap_3d_gt_1d) |
| `su3_3d_complete` | Theorem | ★ свод: 64 сайта + gap=5/6 + Z>0 + gap_su3_3d>0 |
| `phase2_complete` | Theorem | свод фазы 2: 8 сайтов + действие тривиального калибра=0 + gap_su3_3d 1 0 == 5/6 |

**Key lemmas (deep):**

- **`su3_3d_complete`** - Капстоун-конъюнкция: четыре наследованных факта (геометрия 64 сайта, gap_su3=5/6, положительность Z, положительность 3D-щели) в одном Theorem, каждый аргумент — exact на импортированную лемму. Содержательной новизны ноль; назначение — единая точка-свод 'SU(3) 3D complete'. Честно: 'complete' относится к закрытию данного небольшого набора конкретных проверок, НЕ к континуумной SU(3)-щели. _(capstone, synthesis, delegation, honest-scope)_
- **`spatial_enhances_gap`** - Единственная лемма с физ.-содержательным посылом: добавление малого пространственного члена (1/100) увеличивает 3D-щель относительно 1D. Но и она лишь делегирует gap_3d_gt_1d из SU3Lattice3D — реальное вычисление в импортируемом файле; здесь только пере-экспорт. Конкретное сравнение в ОДНОЙ точке beta=1. _(spatial-term, 3d-vs-1d, delegation)_

**Uniqueness - score 0 (infrastructure).** Свод-узел SU(3) 3D-ветки: связывает 64-сайтовую геометрию, значение щели 5/6, положительность статсуммы и 3D>1D-усиление в две капстоун-конъюнкции.
> _Caveat:_ Чистая консолидация/пере-экспорт: все 5 лемм делегируют импортированным результатам, 0 нового содержания. 'complete' аспирационно — означает закрытие этого мелкого набора проверок при beta=1, НЕ континуумную SU(3) массовую щель. Header '5 Qed' совпадает с фактическими 5.

---

## #475 - `src/gauge/LatticeCorrelations.v` - score 2 (methods)

**Lattice correlators are polynomials/rationals in eigenvalues: two-point = t_j^t, exponential clustering**

- **Topic.** Develops correlation functions on the lattice as finite sums of transfer-matrix eigenvalue powers: unnormalized/connected two-point functions equal t_j^t (resp. r_j^t), n-point functions are bounded and rational in beta, the partition function Z=sum (2j+1) t_j^T is positive, and connected correlators cluster exponentially with rate = the mass gap.
- **Role.** Observable-structure layer of the SU(2) lattice thread: turns the transfer-matrix eigenvalues (from CharacterTransfer/ExactMassGap/GapRatio) into correlator statements (decay, clustering, polynomiality). Imports those plus SU2Characters, CombinedTransfer3D, SeriesConvergence, stdlib.Combinatorics. Consumer of eigenvalues, not a hub.
- **Counts.** Qed 21 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS.CauchyReal; ToS.SeriesConvergence; stdlib.Combinatorics; gauge.SU2Characters; gauge.CharacterTransfer; gauge.ExactMassGap; gauge.GapRatio; gauge.CombinedTransfer3D
- **E/R/R.** _Elements:_ собственные значения трансфер-матрицы transfer_eigenvalue j beta 0; gap_ratio beta; конечные суммы/произведения t_j^t над Q. _Roles:_ two_point_unnorm/connected_two_point = роли-корреляторы; partition_fn = роль-статсумма; n_point_bound = роль-мажоранта; gap_ratio = скорость кластеризации. _Rules:_ <chi_j(0)chi_j(t)>=t_j^t; связный = (t_j/t_0)^t = r_j^t; Z = sum_{j<=J}(2j+1)t_j^T; кластеризация: 0<r<1 -> r^t убывает; скорость спада = массовая щель. _P4:_ корреляторы — КОНЕЧНЫЕ суммы конечных произведений собственных значений (чистый Element-объект на каждом срезе); 'континуумный предел' T->inf (доминирование ground-состояния) формулируется лишь как положительность при конечном T — бесконечное расстояние = неактуализированный role-limit. Рациональность в beta = конечно-вычислимый Element.
- **Classical counterpart.** Transfer-matrix formalism for lattice correlation functions: two-point function decays as (lambda_1/lambda_0)^t, exponential clustering with correlation length 1/(mass gap), spectral representation of Z=sum eigenvalue^T (Ornstein-Zernike / Perron-Frobenius gap). All standard statistical-mechanics; NEW is only the exact-Q (no Reals) rendering and the E/R/R framing of T->infinity as an unactualized role-limit. Several 'polynomial/continuity/dominance' theorems are stated far weaker than their comments claim.
- **Tags.** gauge, lattice, correlation-function, transfer-matrix, clustering, partition-function, exact-Q, header-drift, honest-scope
- **Notes.** qed actual = 21; header STATUS says '~30 Qed' and inline part-headers claim ~12+~8+~5+~5 lemmas — both overstate (drift, actual 21). 0 Admitted, 0 own axioms (file ends with Print Assumptions partition_fn_positive). Header-vs-statement gaps: correlation_polynomial_degree (comment 'polynomial degree <= n*M', proof only rational coefficient), ground_state_dominates (comment 'T->inf dominance', proof only Z>0 at finite T), partition_is_polynomial (comment 'polynomial in beta', proof only partition_fn 0 0 1 == 1), correlation_continuous (comment 'continuous', proof only bessel_partial >= 0).

**Lemmas (25):**

| name | kind | role |
|---|---|---|
| `two_point_unnorm` | Definition | ненорм. 2-точечная функция: t_j^t = Qpow (transfer_eigenvalue j beta 0) t |
| `connected_two_point` | Definition | связная 2-точечная: (t_j/t_0)^t = r_j^t |
| `two_point_at_0` | Lemma | при t=0 2-точечная == 1 |
| `two_point_nonneg` | Lemma | 2-точечная >= 0 при t_j>=0 |
| `ground_two_point_pos` | Lemma | ground-2-точечная > 0 при t_0>0 |
| `connected_at_0` | Lemma | связная при t=0 == 1 |
| `connected_ground` | Lemma | связная ground == 1 всегда (r_0=1) |
| `connected_decays` | Lemma | связная убывает: r^{t+1}<=r^t при 0<=r<=1 |
| `connected_bounded` | Lemma | связная <= 1 при 0<=r<=1 |
| `Qpow_add` | Lemma | аддитивность степени: r^{a+b}=r^a*r^b (индукция) |
| `two_point_product` | Lemma | 2-точечная на t1+t2 = произведение (через Qpow_add) |
| `n_point_bound` | Definition | мажоранта n-точечной: (2J+1)^n |
| `n_point_bound_nonneg` | Lemma | мажоранта >= 0 |
| `n_point_bound_pos` | Lemma | мажоранта > 0 при J>=1 |
| `correlation_polynomial_degree` | Theorem | n-точечная рациональна (exists num,den: bessel_partial = num#den) — формулировка СЛАБЕЕ заголовка-комментария о степени n*M |
| `correlation_rational` | Theorem | n-точечная рациональна в beta (transfer_eigenvalue = num#den) |
| `correlation_continuous` | Theorem | 'непрерывность' закодирована как 0 <= bessel_partial (фактически только неотрицательность) |
| `partition_fn` | Fixpoint | статсумма Z = sum_{j<=J} (2j+1) t_j^T |
| `partition_fn_0` | Lemma | Z при J=0 = ground t_0^T |
| `partition_fn_positive` | Theorem | ★ Z > 0 при t_0>0 и всех t_j>=0 (индукция по J) |
| `ground_state_dominates` | Theorem | 'доминирование ground при T->inf' закодировано лишь как Z>0 при конечном T (СЛАБЕЕ заголовка) |
| `partition_is_polynomial` | Theorem | 'Z полином в beta' закодировано конкретикой partition_fn 0 0 1 == 1 (СЛАБЕЕ заголовка) |
| `exponential_clustering` | Theorem | ★ связная > 0 при 0<r<1 (через Qpow_pos на gap_ratio) |
| `clustering_rate` | Theorem | скорость кластеризации = gap_ratio 1 == 47/336 (делегирует gap_ratio_at_beta_1) |
| `correlation_length_finite` | Theorem | длина корреляции конечна: 0 < 1 - gap_ratio при r<1 |

**Key lemmas (deep):**

- **`partition_fn_positive`** - Самая содержательная теорема файла: индукцией по обрезанию J доказывает строгую положительность статсуммы Z=sum (2j+1) t_j^T, при положительном ground-собственном значении и неотрицательных остальных. Реальная индуктивная работа (а не делегирование), хотя сама положительность суммы неотрицательных слагаемых с одним положительным классически тривиальна. Несущая для ground_state_dominates, которая её просто переименовывает. _(partition-function, induction, positivity)_
- **`exponential_clustering`** - Физ.-ядро: связный коррелятор (t_1/t_0)^t = r^t положителен и (через connected_decays) убывает при 0<r<1 — это и есть экспоненциальная кластеризация с показателем = массовая щель. Честно: 'экспоненциальность' тут = монотонное убывание степени r^t над Q плюс отдельное вычисление r=gap_ratio 1=47/336; настоящего exp/log над R нет (по проектному запрету Reals), скорость названа щелью по соглашению. _(clustering, exponential-decay, gap-ratio, mass-gap)_
- **`correlation_polynomial_degree`** - Яркий пример header-vs-statement drift: комментарий обещает 'полином степени <= n*M в beta', а доказанное утверждение — лишь exists num den, bessel_partial 0 1 M_order = num#den, т.е. РАЦИОНАЛЬНОСТЬ одного конкретного коэффициента, без всякой степени и без зависимости от n. Аналогично ground_state_dominates (обещан предел T->inf, доказана положительность при конечном T) и partition_is_polynomial (обещан полином, доказан один числовой случай ==1). Доказанное много слабее заявленного в комментариях. _(header-drift, overclaim-comment, rational, honest-scope)_

**Uniqueness - score 2 (methods).** Корреляторы решётки как точные Q-выражения в собственных значениях: two-point=t_j^t, связная кластеризация r^t со скоростью=щель (gap_ratio 1=47/336), статсумма>0 — без обращения к Reals.
> _Caveat:_ Стандартный трансфер-матричный формализм стат.-механики; новизна лишь в Q-рендеринге и P4-обрамлении. КРИТИЧНО: несколько теорем СЛАБЕЕ своих комментариев — correlation_polynomial_degree доказывает лишь рациональность коэффициента (не степень n*M), ground_state_dominates лишь Z>0 при конечном T (не предел T->inf), partition_is_polynomial лишь один числовой случай ==1, correlation_continuous лишь неотрицательность. 'Экспоненциальность' = убывание r^t над Q, не exp/log. Header '~30 Qed' — ФАКТИЧЕСКИ 21 (drift).

---

## #476 - `src/gauge/LatticeOS1_Analyticity.v` - score 1 (exposition)

**OS1 (analyticity) on the lattice: correlations are polynomials, hence analytic — labelled facts**

- **Topic.** Asserts the first Osterwalder-Schrader axiom (correlation functions extend analytically) for the character-basis lattice gauge theory, on the grounds that finite-truncation correlations are polynomials in the transfer eigenvalues t_j and Bessel partial sums; adds a non-negative Taylor remainder (beta/2)^{M+1}/(M+1)!.
- **Role.** Exposition layer over gauge/CharacterTransfer, ExactMassGap, GapRatio, LatticeCorrelations. Imports CauchyReal, SeriesConvergence, stdlib.Combinatorics. One of the four OS-axiom files (OS1/OS2/OS3 here + reflection-positivity elsewhere); not itself reused as a dependency.
- **Counts.** Qed 19 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS CauchyReal; ToS SeriesConvergence; ToS stdlib.Combinatorics; ToS gauge.CharacterTransfer; ToS gauge.ExactMassGap; ToS gauge.GapRatio; ToS gauge.LatticeCorrelations
- **E/R/R.** _Elements:_ конечно-усечённые корреляции = многочлены от собственных значений t_j переноса; частичные суммы Бесселя I_{2j}^{(M)}; рациональные значения num#den. _Roles:_ OS1 (аналитичность) как роль-аксиома, выполняемая АВТОМАТИЧЕСКИ на решётке; t_j(beta) = роль-собственное значение диагонального переноса; остаток Тейлора = контроль приближения. _Rules:_ многочлен ⟹ аналитичен (бесконечный радиус сходимости); остаток (beta/2)^{M+1}/(M+1)! → 0, факториал бьёт экспоненту. _P4:_ при каждом усечении J корреляция — конечный многочлен (Element, вычислим, рационален); 'аналитическое продолжение' = процесс {corr^{(M)}}, чей предел не достигается как актуальный объект — типичная Element-vs-role-limit развязка решёточного приближения.
- **Classical counterpart.** Osterwalder-Schrader axiom OS1 (analyticity / temperedness of Schwinger functions, Comm. Math. Phys. 1973/75) and the entirety of Bessel functions I_j being entire. Differs sharply: nothing here proves analyticity — the formal statements are either rational-value facts (num#den), positivity of eigenvalues/gap, or t=0 normalizations; only the Taylor-remainder non-negativity is genuine, and it is textbook.
- **Tags.** gauge, yang-mills, osterwalder-schrader, OS1, analyticity, lattice, character-basis, P4, aspirational-label
- **Notes.** Qed drift: STATUS header says ~25, actual count is 19 (21 named declarations). Honesty: most theorem STATEMENTS are placeholders/tautologies trivially below their names (polynomial_is_analytic := bessel_partial 0 1 0 == 1; taylor_converges := 0 <= taylor_remainder 1 0; os1_analyticity weakened to t=0 normalization). Only taylor_remainder_nonneg carries real arithmetic content. 0 own axioms/Parameters.

**Lemmas (21):**

| name | kind | role |
|---|---|---|
| `polynomial_is_analytic` | Theorem | ЗАГЛУШКА: вместо 'многочлен аналитичен' доказывает лишь bessel_partial 0 1 0 == 1 |
| `correlation_is_polynomial_at_J` | Theorem | при усечении J собственное значение переноса рационально (num#den) — Element-сторона |
| `eigenvalue_analytic_in_beta` | Theorem | ЗАГЛУШКА аналитичности t_j(beta): доказывает только 0 <= bessel_partial(2j) 1 0 |
| `composition_analytic` | Theorem | ЗАГЛУШКА: 0 <= transfer_eigenvalue 0 1 0 (позитивность вместо композиции аналитических) |
| `two_point_analytic` | Theorem | ЗАГЛУШКА: two_point_unnorm j 0 1 == 1 (значение в t=0, не аналитичность) |
| `connected_analytic` | Theorem | ЗАГЛУШКА: connected_two_point j 0 1 == 1 (значение в t=0) |
| `partition_analytic` | Theorem | Z(1) = (t_0)^T при J=0 — конкретное равенство, не аналитичность |
| `analytic_continuation_unique` | Theorem | ЗАГЛУШКА единственности продолжения: bessel_partial рационально (num#den) |
| `taylor_remainder` | Definition | остаток Тейлора Бесселя (beta/2)^{M+1}/(M+1)! — единственное содержательное определение файла |
| `taylor_remainder_nonneg` | Lemma | остаток >= 0 при beta >= 0 (реальная арифметика: Qle_shift_div_l + fact_pos) |
| `taylor_converges` | Theorem | ЗАГЛУШКА сходимости: 0 <= taylor_remainder 1 0 (лишь неотрицательность) |
| `eigenvalue_taylor_error` | Theorem | ЗАГЛУШКА оценки ошибки: переформулировка taylor_remainder_nonneg |
| `correlation_taylor_error` | Theorem | ЗАГЛУШКА n-точечной ошибки: 0 <= bessel_partial(2n) beta M |
| `taylor_is_polynomial` | Theorem | приближение Тейлора рационально (num#den) — Element |
| `limit_of_polynomials` | Theorem | ЗАГЛУШКА сходимости: 0 < gap_M0 1 (положительность щели) |
| `os1_analyticity` | Definition | формулировка OS1 = forall j, two_point_unnorm j 0 1 == 1 (ослаблена до значения в t=0) |
| `os1_on_lattice` | Theorem | OS1 'выполняется' — но утверждение сведено к равенству в t=0 |
| `os1_two_point` | Theorem | 0<=t_j ⟹ 0<=two_point_unnorm j 1 1 (позитивность двухточечной) |
| `os1_partition` | Theorem | partition_fn 0 0 1 == (t_0)^0 = 1 (тривиальный случай T=0) |
| `os1_process` | Theorem | 0 < gap_M0 1 /\ 0 < gap_M0 2 (положительность щели при beta=1,2) |
| `os1_summary` | Theorem | конъюнкция os1 + значения двухточечной/Z + положительность щели |

**Key lemmas (deep):**

- **`taylor_remainder_nonneg`** - Единственная лемма файла с собственным арифметическим содержанием: остаток Тейлора Бесселя (beta/2)^{M+1}/(M+1)! неотрицателен — доказано через Qle_shift_div_l, fact_pos и Qpow_nonneg. Несёт реальную (хоть и стандартную) оценку приближения; всё остальное в файле — переформулировки либо тавтологии-заглушки. Классически это хвост ряда целой функции I_j. _(taylor, bessel, remainder, real-content)_
- **`os1_on_lattice`** - Номинальный результат файла — 'OS1 выполняется на решётке'. КРИТИЧНО (честность): фактическое утверждение ослаблено до os1_analyticity := forall j, two_point_unnorm j 0 beta == 1, то есть лишь нормировка корреляции в нулевом разделении t=0, а НЕ аналитическое продолжение по комплексному времени. Настоящая OS1 (аналитичность) НЕ формализована; имя аспирационно. Полезное обоснование: на решётке корреляции действительно полиномиальны, но это здесь не доказывается формально. _(OS1, aspirational-label, weakened-statement)_

**Uniqueness - score 1 (exposition).** Re-frames OS1 for a character-basis lattice as 'polynomials are analytic, automatic', with a machine-checked non-negative Bessel Taylor remainder; situates OS1 in the E/R/R Element-vs-process reading of lattice approximation.
> _Caveat:_ NOT a proof of OS1: the actual proved statements are weakened to rational-value equalities, eigenvalue/gap positivity, and t=0 normalizations (e.g. polynomial_is_analytic is just bessel_partial 0 1 0 == 1). Analyticity itself is never formalized — the theorem names are aspirational. Header says ~25 Qed; actual 19. Standard finite-lattice character expansion; OS axioms are classical (Osterwalder-Schrader).

---

## #477 - `src/gauge/LatticeOS2_Regularity.v` - score 2 (methods)

**OS2 (regularity/temperedness) on the lattice: bounded + exponentially-decaying correlations**

- **Topic.** Asserts the second Osterwalder-Schrader axiom (correlations are tempered distributions) for the lattice, via two genuinely proved facts — the two-point function is bounded by 1 (t_j^t <= 1 when t_j <= 1) and the connected two-point decays as (gap_ratio beta)^t — plus the pin gap_ratio(1) = 47/336.
- **Role.** Exposition layer over gauge/CharacterTransfer, ExactMassGap, GapRatio, LatticeCorrelations. Imports CauchyReal, SeriesConvergence. Sibling of LatticeOS1/OS3; not reused downstream.
- **Counts.** Qed 15 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS CauchyReal; ToS SeriesConvergence; ToS gauge.CharacterTransfer; ToS gauge.ExactMassGap; ToS gauge.GapRatio; ToS gauge.LatticeCorrelations
- **E/R/R.** _Elements:_ ограниченные корреляционные функции (\|<chi_j chi_j>\| <= 1); экспоненциально затухающая связная двухточечная (gap_ratio beta)^t; конкретное значение gap_ratio(1)=47/336. _Roles:_ OS2 (умеренность/темперированность) как роль-аксиома; character_bound 2j+1 = роль-граница характера; gap_ratio < 1 = роль-скорость затухания (массовая щель). _Rules:_ t_j <= 1 = t_0 ⟹ t_j^t <= 1 (ограниченность); связная = (t_1/t_0)^t <= (gap_ratio)^t (экспоненциальный кластеринг); ограниченное/экспоненциальное ⟹ темперированное. _P4:_ ограниченность и экспоненциальное затухание установлены на конкретных рациональных собственных значениях (Element, вычислимо); 'темперированное распределение' как объект (спаривание с произвольной шварцевой функцией) не строится — лишь поточечные рациональные оценки на каждом конечном t.
- **Classical counterpart.** Osterwalder-Schrader axiom OS2 (regularity: Schwinger functions are tempered distributions) and the cluster/exponential-decay property of massive lattice theories (Glimm-Jaffe). Differs: the proved core is two honest finite-t bounds (t_j^t <= 1 and (gap_ratio)^t decay) plus a rational pin 47/336; the leap 'bounded/decaying ⟹ tempered distribution' is asserted by renaming, never constructed (no Schwartz pairing formalized).
- **Tags.** gauge, yang-mills, osterwalder-schrader, OS2, regularity, clustering, exponential-decay, mass-gap, lattice, exact-rational, P4
- **Notes.** Qed drift: STATUS header says ~25, actual count is 15 (17 named declarations). Real content lives in two_point_bounded and connected_exponential_decay (+ schwartz_pairing pin 47/336); the 'tempered' theorems (bounded_is_tempered, exponential_is_tempered) are renamings of those, and os2_two_point/exponential_faster_than_polynomial are tautological (0<1-r). 0 own axioms/Parameters.

**Lemmas (17):**

| name | kind | role |
|---|---|---|
| `character_bound` | Definition | граница характера \|chi_j\| <= 2j+1 как рациональное число |
| `character_bound_positive` | Lemma | 0 < character_bound j (тривиальная положительность 2j+1) |
| `two_point_bounded` | Theorem | ★ РЕАЛЬНО: 0<=t_j<=1 ⟹ two_point_unnorm j t beta <= 1 (через Qpow_bound_1) |
| `connected_exponential_decay` | Theorem | ★ РЕАЛЬНО: connected_two_point 1 t beta <= (gap_ratio beta)^t (экспоненциальный кластеринг) |
| `exponential_faster_than_polynomial` | Theorem | ЗАГЛУШКА: доказывает лишь 0 < 1 - r при r<1 |
| `connected_is_schwartz` | Theorem | связная <= 1 (через connected_bounded) — не шварцевость по сути |
| `partition_finite` | Theorem | собственное значение рационально (num#den) — конечность как Element |
| `bounded_is_tempered` | Theorem | переформулировка two_point_bounded под именем 'ограниченное темперировано' |
| `exponential_is_tempered` | Theorem | переформулировка connected_exponential_decay |
| `correlations_tempered` | Theorem | 0 < connected_two_point 1 t 1 (положительность через exponential_clustering) |
| `schwartz_pairing` | Theorem | ★ конкретный пин: gap_ratio 1 == 47#336 (через gap_ratio_at_beta_1) |
| `os2_regularity` | Definition | формулировка OS2 = ограниченность двухточечной единицей |
| `os2_on_lattice` | Theorem | OS2 'выполняется' = two_point_bounded (честно = ограниченность, не полная темперированность) |
| `os2_schwartz_stronger` | Theorem | монотонность затухания connected(S t) <= connected(t) (через connected_decays) |
| `os2_two_point` | Theorem | ЗАГЛУШКА: 0 < 1 - gap_ratio beta при gap_ratio<1 |
| `os2_n_point` | Theorem | 0 <= n_point_bound n J (неотрицательность n-точечной границы) |
| `os2_summary` | Theorem | конъюнкция: ограниченность + gap_ratio<1 + 47/336 + положительность щели |

**Key lemmas (deep):**

- **`two_point_bounded`** - Реальное содержание №1: двухточечная функция t_j^t ограничена единицей, когда t_j лежит в [0,1] (доказано через Qpow_bound_1). Это честная равномерная граница на любом конечном разделении t — субстрат 'ограниченное ⟹ темперированное'. Зависит от t_0=1 как наибольшего собственного значения переноса (диагональность в базисе характеров). _(bounded, two-point, real-content)_
- **`connected_exponential_decay`** - Реальное содержание №2 и наиболее физически значимое: связная двухточечная (t_1/t_0)^t мажорируется (gap_ratio beta)^t — экспоненциальный кластеринг = прямое следствие массовой щели. Доказано переписыванием t_1/t_0 == gap_ratio и Qpow_wd. Это и есть OS2-релевантный факт; вместе со schwartz_pairing (gap_ratio(1)=47/336<1) даёт конкретную скорость затухания на данной решётке. Честно: затухание ⟹ темперированность лишь утверждается, спаривание со Шварцем не строится. _(exponential-decay, clustering, mass-gap, real-content)_

**Uniqueness - score 2 (methods).** Exact-rational lattice realization of OS2's substrate: a uniform bound t_j^t <= 1 and an explicit exponential-clustering bound (gap_ratio beta)^t with the concrete value gap_ratio(1) = 47/336, all over Q with no reals.
> _Caveat:_ Honest scope: bounded + exponentially decaying is genuinely proved on each finite separation, but 'tempered distribution' (the actual OS2 content) is only asserted by renaming (bounded_is_tempered/exponential_is_tempered are re-statements); no Schwartz-space pairing is formalized. SU(2) character lattice, specific gap. Header says ~25 Qed; actual 15. OS2 + clustering are classical.

---

## #478 - `src/gauge/LatticeOS3_Covariance.v` - score 1 (exposition)

**OS3 (Euclidean covariance) on the lattice: hypercubic symmetry, time-translation, |2^d d!|=384**

- **Topic.** Asserts the third Osterwalder-Schrader axiom (Euclidean rotation invariance) for the lattice, reduced to discrete hypercubic symmetry: the real content is time-translation as the multiplicative law two_point(t1+t2)=two_point(t1)*two_point(t2), plus the count |hypercubic group in 4D| = 2^4*4! = 384.
- **Role.** Exposition layer over gauge/CharacterTransfer, ExactMassGap, GapRatio, LatticeCorrelations. Imports CauchyReal, SeriesConvergence. Sibling of LatticeOS1/OS2; not reused downstream.
- **Counts.** Qed 16 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS CauchyReal; ToS SeriesConvergence; ToS gauge.CharacterTransfer; ToS gauge.ExactMassGap; ToS gauge.GapRatio; ToS gauge.LatticeCorrelations
- **E/R/R.** _Elements:_ двухточечные корреляции, зависящие лишь от \|t\| (через диагональность переноса); группа гиперкуба порядка 2^d*d! = 384 в 4D; собственные значения переноса. _Roles:_ OS3 (евклидова ковариантность) как роль-аксиома, на решётке = дискретная гиперкубическая симметрия; трансляция/обращение времени/пространственный поворот = роли-симметрии; зависимость от \|t\| = роль диагональности. _Rules:_ T диагонален ⟹ <chi_j(0)chi_j(t)> = t_j^\|t\| зависит только от \|t\|; two_point(t1+t2) = two_point(t1)*two_point(t2) (закон трансляции); действие Вильсона трактует все плакеты одинаково ⟹ инвариантность к перестановке направлений. _P4:_ симметрия = КОНЕЧНАЯ дискретная группа (2^d*d! элементов, вычислимо при каждом d) — Element-сторона; 'непрерывная SO(4) в континуальном пределе a→0' = процесс, чей предел (артефакты решётки O(a^2)→0) не достигается актуально.
- **Classical counterpart.** Osterwalder-Schrader axiom OS3 (Euclidean invariance of Schwinger functions) and the lattice fact that hypercubic symmetry B_d -> SO(d) in the continuum limit (order of B_4 = 2^4*4! = 384). Differs: OS3 itself is encoded as a literal tautology (two_point == two_point); the only non-trivial proved content is the translation product law and the group-order 384 — neither is rotation invariance of the action.
- **Tags.** gauge, yang-mills, osterwalder-schrader, OS3, covariance, hypercubic, translation-invariance, lattice, P4, aspirational-label, tautology
- **Notes.** Qed drift: STATUS header says ~25, actual count is 16 (17 named declarations). Honesty: os3_covariance := two_point == two_point is a tautology (os3_on_lattice = Qeq_refl); time_reversal_two_point and dependence_on_abs_t are x==x by reflexivity; spatial_rotation_invariance proves a nat inequality (2j+1<>2k+1), spatial_reflection_invariance proves bessel_partial 0 1 0 == 1. Real content: iterated_translation/periodic_boundary (product law) and hypercubic_group_size (384). 0 own axioms/Parameters.

**Lemmas (17):**

| name | kind | role |
|---|---|---|
| `translation_invariance` | Theorem | ЗАГЛУШКА: two_point_unnorm j 0 beta == 1 (значение в t=0, не трансляционная инвариантность) |
| `connected_translation_invariance` | Theorem | ЗАГЛУШКА: connected_two_point j 0 beta == 1 (значение в t=0) |
| `periodic_boundary` | Theorem | ★ РЕАЛЬНО: two_point(t+T) = two_point(t)*two_point(T) (закон произведения = трансляция) |
| `translation_step` | Lemma | two_point(S t) = t_j * two_point(t) (шаг трансляции через ring) |
| `iterated_translation` | Lemma | ★ two_point(t1+t2) = two_point(t1)*two_point(t2) (итерированная трансляция) |
| `time_reversal_two_point` | Theorem | ЗАГЛУШКА: x == x по reflexivity (t_j^t одинаково вперёд/назад тривиально) |
| `time_reversal_symmetry` | Theorem | transfer_is_diagonal (через transfer_diagonal_structural) — самосопряжённость переноса |
| `time_reversal_torus` | Theorem | повтор закона произведения two_point(t1+t2)=... под именем обращения на торе |
| `dependence_on_abs_t` | Theorem | ЗАГЛУШКА: x == x по reflexivity |
| `spatial_rotation_invariance` | Theorem | ЗАГЛУШКА: j<>k ⟹ 2j+1<>2k+1 (nat-неравенство вместо инвариантности действия) |
| `spatial_reflection_invariance` | Theorem | ЗАГЛУШКА: bessel_partial 0 1 0 == 1 |
| `hypercubic_invariance` | Theorem | ЗАГЛУШКА: 0 <= transfer_eigenvalue 0 1 0 (позитивность) |
| `hypercubic_group_size` | Theorem | ★ РЕАЛЬНО: 2^4*4! = 384 (порядок гиперкубической группы в 4D, vm_compute) |
| `os3_covariance` | Definition | формулировка OS3 = forall j t beta, two_point == two_point (тавтология!) |
| `os3_on_lattice` | Theorem | OS3 'выполняется' = Qeq_refl (утверждение есть тавтология x==x) |
| `os3_continuum` | Theorem | ЗАГЛУШКА континуума: 0 < gap_M0 1 (положительность щели) |
| `os3_summary` | Theorem | конъюнкция: тавтология OS3 + значение t=0 + диагональность + позитивность + 384 |

**Key lemmas (deep):**

- **`iterated_translation`** - Реальное содержание №1: two_point_unnorm j (t1+t2) beta == two_point_unnorm j t1 beta * two_point_unnorm j t2 beta — мультипликативный закон t_j^{t1+t2} = t_j^{t1}*t_j^{t2}, делегируется two_point_product. Это и есть честная форма трансляционной инвариантности (корреляция зависит только от разделения), хотя названа скромно; periodic_boundary и time_reversal_torus — её повторы. _(translation, multiplicative, real-content)_
- **`hypercubic_group_size`** - Реальное содержание №2: \|гиперкубическая группа в 4D\| = 2^4 * 4! = 384, доказано simpl/reflexivity. Конкретный комбинаторный факт о дискретной евклидовой симметрии решётки (знаковые перестановки осей). Честный, проверяемый, но стандартный (порядок гипероктаэдральной группы B_4). _(hypercubic, group-order, combinatorics, real-content)_
- **`os3_on_lattice`** - Номинальный результат — 'OS3 выполняется'. КРИТИЧНО (честность): os3_covariance определена как forall j t beta, two_point == two_point, то есть ТАВТОЛОГИЯ (доказывается Qeq_refl). Настоящая евклидова ковариантность (зависимость лишь от \|t\|, инвариантность действия к поворотам) НЕ формализована как нетривиальное утверждение; содержательные куски — iterated_translation и счёт 384 — лежат рядом, но сам 'OS3' пуст. _(OS3, tautology, aspirational-label)_

**Uniqueness - score 1 (exposition).** Casts OS3 as discrete hypercubic symmetry in the E/R/R frame (finite group = Element side, continuum SO(4) = unreachable process limit), with the multiplicative translation law and the explicit group order 384 machine-checked.
> _Caveat:_ NOT a proof of OS3: os3_covariance is the tautology two_point==two_point (proved by reflexivity), and most rotation/reflection theorems are placeholders (spatial_rotation_invariance is a nat inequality; spatial_reflection is bessel==1). Genuine content is only iterated_translation and the count 384. Continuum SO(4) is merely asserted. Header says ~25 Qed; actual 16. OS3 + hypercubic->SO(4) are classical.

---

## #479 - `src/gauge/LatticeRG.v` - score 2 (methods)

**Renormalization group in character basis: eigenvalue squaring, b0>0 toy beta-function, physical-gap invariance**

- **Topic.** Models one RG blocking step in the character basis as eigenvalue squaring (t_j -> t_j^2), proves the blocked gap stays positive at beta=1,2 via the factorization t0^2-t1^2=(t0-t1)(t0+t1), posits a toy positive one-loop coefficient b0~11/237, and proves the physical ratio gap_n/a_n stays constant as both double under blocking.
- **Role.** Methods/framing layer over gauge/SU2Characters, CharacterTransfer, ExactMassGap, ClebschGordan, CombinedTransfer3D, GapRatio. Imports CauchyReal, SeriesConvergence, stdlib.Combinatorics. The richest of the OS/RG quintet; runs Print Assumptions on its summary. Not reused as a dependency.
- **Counts.** Qed 29 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS CauchyReal; ToS SeriesConvergence; ToS stdlib.Combinatorics; ToS gauge.SU2Characters; ToS gauge.CharacterTransfer; ToS gauge.ExactMassGap; ToS gauge.ClebschGordan; ToS gauge.CombinedTransfer3D; ToS gauge.GapRatio
- **E/R/R.** _Elements:_ квадраты собственных значений t_j^2 (огрубление = два узла в один); рациональный коэффициент b0_approx = 11#237; решёточный шаг a_n = 2^n*a0; физическое отношение gap_n/a_n. _Roles:_ RG = роль-огрубление (блокинг); beta-функция = роль-поток связи (асимптотическая свобода); собственное значение возведением в квадрат = роль RG-шага; gap_n*a_n = инвариант (физическая щель). _Rules:_ T^{(2)} = T*T ⟹ в диагональном базисе t_j^{new} = t_j^2; rg_gap = (t0-t1)(t0+t1) (факторизация ring); под блокингом gap и a удваиваются ⟹ gap'/a' = gap/a; Δβ ~ b0*β^2 > 0. _P4:_ RG-процесс = последовательность {(β_n, gap_n, a_n)}, где физическая щель gap_n/a_n постоянна при ВСЯКОМ конечном n (Element, вычислимо) — континуальный предел a→0 НЕ берётся актуально (P4: процесс ЕСТЬ предел, p4_continuum_process); асимптотическая свобода как НАСТОЯЩЕЕ свойство потока не выводится, лишь постулируется через знак b0.
- **Classical counterpart.** Wilsonian renormalization-group / block-spin transformation (Kadanoff-Wilson), the one-loop SU(2) beta-function coefficient b0 = 11/(24π^2) > 0 (asymptotic freedom, Gross-Wilczek-Politzer), and dimensional-transmutation invariance of the physical mass gap. Differs: eigenvalue squaring under blocking is a real algebraic fact (difference of squares), but asymptotic freedom is reduced to the SIGN of a posited rational b0~11/237 (no flow derived), and the gap/spacing doubling is posited by definition; physical_gap_constant is genuine but rests on those posits.
- **Tags.** gauge, yang-mills, renormalization-group, block-spin, asymptotic-freedom, beta-function, mass-gap, continuum-as-process, exact-rational, character-basis, P4, aspirational-label
- **Notes.** Qed drift: STATUS header says ~40, actual count is 29 (41 named declarations). Honesty: asymptotic_freedom := forall beta>0, 0<b0*beta^2 (only a sign of posited b0=11#237; file comment itself says effective_beta 'doesn't capture asymptotic freedom directly'); rg_process_gap/spacing := 2*x posit the doubling rather than deriving it. Genuine content: rg_gap_factored (difference of squares), physical_gap_constant (invariant ratio), spacing_decreases (monotonicity over Q). Qpow_pos_local is plumbing. File ends with Print Assumptions lattice_rg_summary. 0 own axioms/Parameters.

**Lemmas (41):**

| name | kind | role |
|---|---|---|
| `rg_eigenvalue_0` | Definition | RG-собственное значение основного состояния = t0^2 |
| `rg_eigenvalue_1` | Definition | RG-собственное значение возбуждённого = t1^2 |
| `rg_eigenvalue_0_pos_1` | Lemma | 0 < rg_eigenvalue_0 1 (Qmult_lt_0_compat) |
| `rg_eigenvalue_0_pos_2` | Lemma | 0 < rg_eigenvalue_0 2 |
| `rg_eigenvalue_1_pos_1` | Lemma | 0 < rg_eigenvalue_1 1 |
| `rg_eigenvalue_1_pos_2` | Lemma | 0 < rg_eigenvalue_1 2 |
| `rg_ratio_is_square` | Theorem | ★ RG-отношение = rg_ratio_step(gap_ratio beta) (field, t0<>0): отношение под квадратом |
| `rg_gap` | Definition | RG-щель = t0^2 - t1^2 |
| `rg_gap_factored` | Theorem | ★ rg_gap = gap_M0 * eigenvalue_sum = (t0-t1)(t0+t1) (ключевая факторизация ring) |
| `rg_gap_positive_1` | Theorem | 0 < rg_gap 1 (через факторизацию + положительность щели и суммы) |
| `rg_gap_positive_2` | Theorem | 0 < rg_gap 2 |
| `b0_approx` | Definition | рациональное приближение b0 = 11#237 (24π^2 ≈ 237) |
| `b0_positive` | Lemma | 0 < b0_approx (lra) |
| `effective_beta` | Definition | эффективная связь beta^2/(beta+1) — грубая формула |
| `effective_beta_pos` | Lemma | 0 < effective_beta beta при beta>0 |
| `asymptotic_freedom` | Definition | АФ как Prop: forall beta>0, 0 < b0*beta^2 (ослаблено до знака!) |
| `asymptotic_freedom_holds` | Theorem | ★ 'АФ выполняется' — но содержание = лишь положительность b0*beta^2 |
| `beta_function_positive` | Lemma | переформулировка asymptotic_freedom_holds |
| `beta_after_n_steps` | Definition | β_n = β0 + n*b0*β0^2 (ведущий порядок) |
| `beta_after_0` | Lemma | β_0 = β0 (ring) |
| `beta_increases_with_n` | Theorem | β0 < beta_after_n_steps β0 1 (β растёт за один шаг) |
| `Qpow_pos_local` | Lemma | ПЛАМБИНГ: 0<q ⟹ 0<Qpow q n (локальная индукция) |
| `lattice_spacing` | Definition | a_n = 2^n * a0 (шаг удваивается) |
| `lattice_spacing_0` | Lemma | a_0 = a0 |
| `lattice_spacing_1` | Lemma | a_1 = 2*a0 |
| `lattice_spacing_positive` | Lemma | 0 < a_n при a0>0 |
| `lattice_spacing_increasing` | Lemma | a_n < a_{n+1} |
| `lattice_spacing_from_beta` | Definition | a(β) = 1/(1+2*b0*β) — убывает по β |
| `spacing_from_beta_pos` | Lemma | 0 < a(β) при β>0 |
| `spacing_decreases` | Theorem | ★ β1<β2 ⟹ a(β2)<a(β1) (монотонность 1/d, длинное field-доказательство) |
| `rg_process_gap` | Definition | gap' = 2*gap под RG |
| `rg_process_spacing` | Definition | a' = 2*a под RG |
| `physical_gap_preserved` | Theorem | ★ gap'/a' = gap/a (один шаг, field, a<>0): физическая щель сохраняется |
| `rg_gap_doubles` | Lemma | rg_process_gap gap = 2*gap |
| `rg_spacing_doubles` | Lemma | rg_process_spacing a = 2*a |
| `gap_after_n_steps` | Definition | gap_n = 2^n * gap0 |
| `gap_after_0` | Lemma | gap_0 = gap0 |
| `gap_after_1` | Lemma | gap_1 = 2*gap0 |
| `physical_gap_constant` | Theorem | ★★ gap_n/a_n = gap0/a0 для всех n (физическая щель постоянна вдоль процесса) |
| `p4_continuum_process` | Theorem | ★ P4: процесс {gap_n/a_n} постоянен — континуум ЕСТЬ процесс, не предел-объект |
| `lattice_rg_summary` | Theorem | конъюнкция: rg_gap>0 (β=1,2) + АФ-знак + spacing убывает + физ.щель постоянна |

**Key lemmas (deep):**

- **`physical_gap_constant`** - Сердце файла и самое содержательное: при блокинге gap_n = 2^n*gap0 и a_n = 2^n*a0 удваиваются согласованно, поэтому физическое отношение gap_n/a_n == gap0/a0 ТОЧНО для всех n (field, split; lra). Это честная, проверяемая инвариантность размерной массовой щели вдоль RG-процесса — и именно она оформляет тезис проекта 'континуальный предел = процесс, а не достигаемый объект' (p4_continuum_process делегирует ей). Замечание о честности: 'удвоение' gap и a здесь ПОСТУЛИРУЕТСЯ определениями rg_process_gap/spacing := 2*x, а не выводится из квадрата собственных значений RG-части I. _(physical-gap, rg-invariant, P4, continuum-as-process, real-content)_
- **`rg_gap_factored`** - Алгебраическое ядро RG-шага: rg_gap = t0^2 - t1^2 == gap_M0 * eigenvalue_sum, то есть (t0-t1)(t0+t1), доказано ring. Из него rg_gap_positive_1/2 заключают положительность блокированной щели при β=1,2 (положительность множителей). Честный конкретный факт о возведении собственных значений в квадрат; стандартная разность квадратов, перенесённая на собственные значения переноса. _(eigenvalue-squaring, factorization, gap-positivity, real-content)_
- **`asymptotic_freedom_holds`** - КРИТИЧНО для честности: теорема названа 'асимптотическая свобода', но asymptotic_freedom определена как forall beta>0, 0 < b0_approx*beta^2 — ВСЕГО ЛИШЬ знак произведения положительных рациональных. Настоящая АФ (β растёт к континууму, dβ/d(log a) со знаком из однопетлевого b0=11/(24π^2)) НЕ выводится: b0~11/237 ПОСТУЛИРУЕТСЯ как вход, а effective_beta=β^2/(β+1) сам комментарий признаёт не схватывающим АФ. Это переобозначение положительности под физическим именем. _(asymptotic-freedom, aspirational-label, posited-input, b0)_
- **`spacing_decreases`** - Единственное технически нетривиальное арифметическое доказательство файла (~65 строк): a(β)=1/(1+2 b0 β) строго убывает по β, установлено через общий приём 'f2*prod < f1*prod при prod>0 ⟹ f2<f1' с field-равенствами и Qmult_le_compat_r. Стандартная монотонность 1/x, но честно проведённая над Q без вещественных. Плумбинг-уровень по новизне, но несёт реальное содержание. _(monotonicity, lattice-spacing, rational-arithmetic)_

**Uniqueness - score 2 (methods).** An exact-rational, character-basis toy model of one RG blocking step: eigenvalue squaring with a real difference-of-squares gap factorization, monotone lattice spacing, and a genuinely invariant physical ratio gap_n/a_n that instantiates the 'continuum limit = process' (P4) reading instead of an actual a->0 limit.
> _Caveat:_ Toy/illustrative, not a derivation: asymptotic_freedom is weakened to 0 < b0*beta^2 (only the sign of a POSITED b0~11/237; the comment admits effective_beta does not capture AF), and the RG gap/spacing 'doubling' is posited by definition (rg_process_gap:=2*gap), not derived from the eigenvalue squaring. Real content = rg_gap_factored, physical_gap_constant, spacing_decreases. SU(2)/specific lattice. Header says ~40 Qed; actual 29. RG + one-loop b0 are classical.

---

## #480 - `src/gauge/LatticeStructure.v` - score 0 (infrastructure)

**Lattice geometry foundation: sites/links/plaquettes on N×N torus, indexing, counts L=2S, P=S, dof=P**

- **Topic.** Defines the discrete geometry of a 2D periodic lattice — sites (nat*nat), directed links, plaquettes, periodic wrap, linear site indexing and its round-trip inverse, 2x coarsening — and proves the bijective indexing and the combinatorial counts num_links = 2*num_sites, num_plaquettes = num_sites, and physical_dof L-S = P.
- **Role.** Foundational geometry/plumbing for the gauge cluster: provides site/link/plaquette types, decidable equalities, wrap lemmas and counts that downstream Wilson-action / transfer-matrix files build on. Imports only Stdlib (QArith, List, Arith, PeanoNat). Bottom of the gauge_lattice dependency chain.
- **Counts.** Qed 22 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs List Lia ZArith Lqa Arith PeanoNat
- **E/R/R.** _Elements:_ конкретные конечные объекты: сайты (nat*nat), направленные линки (site*bool), плакеты (site), их КОНЕЧНЫЕ счётчики N^2, 2N^2; периодическое заворачивание wrap K x = x mod K. _Roles:_ решёточная геометрия = арена; valid_site/valid_link = роль-предикаты принадлежности; site_index = роль-нумерация (линейный порядок, L5-подобный); coarsen_site = роль огрубления (мост к RG). _Rules:_ линк ⟹ цель через wrap (тор); site_index N s = fst*N+snd биективен на valid; num_links=2*num_sites, num_plaquettes=num_sites, num_links - num_sites = num_plaquettes (физические степени свободы). _P4:_ ВСЯ структура конечна и разрешима на каждой стадии N (заявлено в шапке): равенство сайтов/линков разрешимо (site_eq_dec/link_eq_dec), принадлежность разрешима (valid_site_dec), счётчики вычислимы — образцовая Element-сторона (никакого role-limit, никакого предельного объекта); решётка как конечная актуальность P4.
- **Classical counterpart.** Standard lattice gauge theory geometry (Wilson 1974): sites/links/plaquettes on a periodic hypercubic lattice, the link-count 2*sites in 2D, and the gauge degree-of-freedom counting links - sites = plaquettes. Differs only in being a fully constructive, decidable Coq encoding over nat with explicit indexing bijections; the mathematics is entirely standard.
- **Tags.** gauge, yang-mills, lattice, geometry, sites-links-plaquettes, torus, indexing, decidable, P4, infrastructure, foundation
- **Notes.** Qed drift: STATUS header says ~25, actual count is 23 (39 named declarations; many are Definitions). Header SUMMARY comment block (lines 309-321) lists 'plaquette_closed_loop' which does NOT exist in the file — actual Part VII lemmas are plaquette_source_l1 and plaquette_l4_target_eq_l3_source (plus coarsen_valid). 0 own axioms/Parameters. File imports only Stdlib (no ToS deps) — true bottom of the gauge_lattice chain.

**Lemmas (39):**

| name | kind | role |
|---|---|---|
| `site` | Definition | сайт = пара nat*nat |
| `valid_site` | Definition | валидный сайт: обе координаты < N |
| `num_sites` | Definition | число сайтов N×N = N*N |
| `direction` | Definition | направление = bool (false=x, true=y) |
| `link` | Definition | линк = (site, direction): направленное ребро |
| `num_links` | Definition | число линков = 2N^2 (по 2 исходящих на сайт) |
| `wrap` | Definition | периодическое заворачивание wrap K x = x mod K |
| `link_target` | Definition | целевой сайт линка при периодической границе |
| `link_source` | Definition | исходный сайт линка = fst l |
| `plaquette` | Definition | плакет = сайт (левый нижний угол) |
| `num_plaquettes` | Definition | число плакетов = N^2 |
| `plaquette_links` | Definition | четыре линка плакета при (x,y) (замкнутый контур) |
| `site_index` | Definition | линейный индекс сайта = fst*N + snd |
| `index_to_site` | Definition | сайт из линейного индекса (div, mod) |
| `coarsen_site` | Definition | огрубление: сайт на 2N → сайт на N (мост к RG-блокингу) |
| `are_neighbors` | Definition | s2 достижим из s1 одним линком |
| `wrap_lt` | Lemma | 0<K ⟹ wrap K x < K (mod_upper_bound) |
| `wrap_id` | Lemma | x<K ⟹ wrap K x = x (mod_small) |
| `wrap_zero` | Lemma | wrap K 0 = 0 |
| `wrap_period` | Lemma | wrap K (x+K) = wrap K x (периодичность) |
| `wrap_succ_last` | Lemma | wrap K K = 0 (mod_same) |
| `valid_site_dec` | Lemma | ★ разрешимость валидности сайта (P4-разрешимость) |
| `link_target_valid` | Lemma | целевой сайт линка валиден (через wrap_lt) |
| `site_index_bound` | Lemma | site_index N s < num_sites N для валидных |
| `site_index_injective` | Lemma | ★ инъективность нумерации на валидных сайтах (nia) |
| `index_site_roundtrip` | Lemma | ★ site_index(index_to_site i) = i (div_mod_eq) |
| `site_index_roundtrip` | Lemma | ★ index_to_site(site_index s) = s (биекция в обе стороны) |
| `num_sites_pos` | Lemma | 0 < num_sites N при N>=1 |
| `num_links_eq` | Lemma | num_links = 2*num_sites |
| `num_plaquettes_eq` | Lemma | num_plaquettes = num_sites |
| `physical_dof` | Lemma | ★ num_links - num_sites = num_plaquettes (физ. степени свободы калибровки) |
| `site_eq_dec` | Lemma | ★ разрешимое равенство сайтов |
| `direction_eq_dec` | Lemma | разрешимое равенство направлений |
| `link_eq_dec` | Lemma | ★ разрешимое равенство линков |
| `plaquette_source_l1` | Lemma | источник l1 = сам сайт плакета (reflexivity) |
| `plaquette_l4_target_eq_l3_source` | Lemma | цель l4 = источник l3 (замкнутость контура, reflexivity) |
| `coarsen_valid` | Lemma | огрубление сохраняет валидность (div_lt_upper_bound) |
| `lattice_structure_summary` | Theorem | конъюнкция: wrap-свойства + round-trip нумерации + счётчики |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`site_index_roundtrip`** - Ядро файла: линейная нумерация сайтов site_index N s = fst*N+snd биективна на валидных сайтах — index_to_site(site_index s) = s (через div_add_l/div_small/mod-арифметику) и обратно index_site_roundtrip (div_mod_eq). Это даёт пересчёт между геометрией (пары координат) и линейным хранением (индекс), на котором стоят transfer-matrix / Wilson-action файлы кластера. Стандартная факторизация N×N → N^2; ценность чисто инфраструктурная. _(bijection, indexing, lattice-geometry, foundation)_
- **`physical_dof`** - Содержательный счётный факт: num_links - num_sites = num_plaquettes (L - S = P), то есть 2N^2 - N^2 = N^2 — решёточная форма подсчёта физических калибровочных степеней свободы (линки минус калибровочные орбиты = независимые плакеты). Честно и проверяемо (nia); классически это связь между размерностью группы линковых переменных, калибровочными преобразованиями на сайтах и числом плакетных связей. _(degrees-of-freedom, counting, gauge)_
- **`valid_site_dec`** - Образец P4-стороны кластера: принадлежность сайта решётке разрешима (valid_site_dec), как и равенство сайтов/линков (site_eq_dec, link_eq_dec). Вся геометрия конечна и алгоритмична при каждом N — никакого предельного объекта, никакого role-limit. Это и есть 'конечная актуальность' решётки, на которой держится экспозиционный тезис всего gauge-блока. _(decidable, P4, finite-actuality)_

**Uniqueness - score 0 (infrastructure).** Constructive foundational geometry for the 2D lattice gauge cluster: decidable sites/links/plaquettes on a torus with a proven indexing bijection and the standard counts L=2S, P=S, L-S=P.
> _Caveat:_ Pure plumbing/foundation: every result is standard lattice geometry (Wilson lattice gauge theory) and elementary nat arithmetic (wrap = mod, indexing = div/mod round-trip). No physics, no novelty — it underpins the Wilson-action/transfer-matrix files. The header SUMMARY block also mislists a nonexistent 'plaquette_closed_loop' lemma (file actually has plaquette_source_l1 + plaquette_l4_target_eq_l3_source). Header says ~25 Qed; actual 23.

---

## #481 - `src/gauge/MassGapBound.v` - score 2 (methods)

**Explicit SU(2) gap lower bound 9/4 on beta in [2,4]; the linearized mass-gap chain assembled**

- **Topic.** Proves that the closed-form SU(2) mass-gap polynomial su2_mass_gap(beta) is >= 9/4 for beta in [2,4] (minimum at beta=4) and bundles the linearized RG-contraction chain (contraction factor 1/4, Taylor corrections < 1/10, orbits stay in [2,4]) into a single 'step 7 synthesis'.
- **Role.** Assembly node of the Gaussian/linearized branch. Imports gauge.RGFlow, SU2TransferMatrix, StrongCoupling, SU2Group/Synthesis, CosineAction, HigherOrderRG, PerturbationRG, RGConvergence; consumed by gauge.MillenniumSynthesis. Inherits classic transitively via the PowerSeries chain.
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs List Lia ZArith Lqa; ToS: CauchyReal FixedPoint; gauge: RGFlow SU2TransferMatrix StrongCoupling SU2Group SU2Synthesis CosineAction HigherOrderRG PerturbationRG RGConvergence
- **E/R/R.** _Elements:_ конкретное рациональное beta in [2,4]; число-щель su2_mass_gap(beta) = (2-beta/8)^2*(2-beta/4); порог-Element 9/4. _Roles:_ su2_mass_gap = роль-щель (расстояние спектра); rg_map_linear/quartic = роль-поток (огрубление); is_contraction = роль-сжатие; нижняя грань 9/4 = роль-порог. _Rules:_ монотонный спад su2_mass_gap на [2,4] => минимум в beta=4 = 9/4 (lra/nra); RG сжимает с фактором 1/4; коррекции Тейлора < 1/10; орбита остаётся в [2,4]. _P4:_ всё — конечная рациональная арифметика на ОДНОМ отрезке: для всякого Element-beta щель вычислима и >= 9/4. Но 'RG-неподвижная точка' = Element-предел линейного приближения, а не точный непертурбативный поток; what_is_open_step7 честно фиксирует rg_linear != rg_quartic — это и есть незакрытая грань (role-limit к Clay).
- **Classical counterpart.** Mirrors the lattice-gauge transfer-matrix spectral-gap picture (Osterwalder-Seiler, strong-coupling expansion) plus Banach fixed-point RG flow. What differs: there is NO genuine lattice spectral computation here — su2_mass_gap(beta) is the polynomial (2-beta/8)^2*(2-beta/4); the 'gap >= 9/4' is a calculus minimum of that polynomial on [2,4] via lra/nra, and the RG is a linearized affine map, not the QCD beta-function.
- **Tags.** mass-gap, SU2, explicit-bound, RG, contraction, finite-interval, aspirational-name, honesty, vm-compute
- **Notes.** Qed drift: header says '~18', actual 12. 'AXIOMS: classic (via PowerSeries)' — транзитивно наследуемая аксиома, СВОИХ Axiom/Parameter 0. su2_mass_gap/su2_gap_formula определены в импортах (SU2TransferMatrix), не здесь.

**Lemmas (14):**

| name | kind | role |
|---|---|---|
| `mass_gap_lower_bound` | Definition | константа-порог 9/4 |
| `mass_gap_at_4` | Lemma | su2_mass_gap 4 == 9/4 (минимум достигается в beta=4) |
| `mass_gap_lower_bound_positive` | Lemma | 0 < 9/4 (тривиально, lra) |
| `mass_gap_lower_bound_valid` | Lemma | ★ 9/4 <= su2_mass_gap beta на [2,4] через формулу-произведение и nra |
| `mass_gap_explicit` | Theorem | переформулировка предыдущей: 9/4 <= su2_mass_gap beta |
| `gap_survives_all_corrections` | Theorem | щель >= 9/4 И > 0 в любой точке орбиты [2,4] |
| `mass_gap_robust` | Theorem | псевдоним mass_gap_explicit для 'RG fixed point' |
| `gap_quantitative` | Theorem | 2 < su2_mass_gap beta на [2,4] (9/4 > 2) |
| `mass_gap_chain` | Theorem | ★ конъюнкция цепи: сжатие 1/4 + квартик-грань + сумма коррекций < 1/10 + самоотображение + щель >= 9/4 |
| `what_is_proved_step7` | Theorem | сводка доказанного: коррекции ограничены, факториальный спад, щель >= 9/4, орбиты в [2,4] |
| `what_is_open_step7` | Theorem | ★ ЧЕСТНОСТЬ: ~(forall beta, rg_linear == rg_quartic) — линеаризация != точный RG |
| `step7_synthesis` | Theorem | ★ главный конъюнкт: неабелевость + щель>0 на (0,8) + сжатие + коррекции + щель>=9/4 |
| `the_number` | Theorem | 9/4 == 9/4 (маркер-число) |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`mass_gap_lower_bound_valid`** - Единственный содержательный шаг файла: вместо спектра решётки берётся ЗАМКНУТАЯ ФОРМУЛА su2_mass_gap(beta)==(2-beta/8)*(2-beta/8)*(2-beta/4) (импорт su2_gap_formula) и доказывается, что на [2,4] множители лежат в [3/2,7/4] и [1,3/2], откуда произведение >= (3/2)^2*1 = 9/4 через nra. Это исчисление минимума многочлена, а не теорема о щели Янга-Миллса; ценность — явная рациональная нижняя граница на конкретном отрезке. _(mass-gap, explicit-bound, nra, finite-interval)_
- **`what_is_open_step7`** - Встроенный честный дисклеймер: доказывает ~(forall beta, rg_map_linear beta == rg_map_quartic beta), т.е. линеаризованный RG НЕ совпадает с (квартик-)поправленным, значит 'неподвижная точка' и вся цепь относятся к приближению. Редкая для aspirational-файла явная маркировка зазора до Clay-задачи прямо в коде. _(honesty, open-problem, linearization-gap)_
- **`step7_synthesis`** - Капстоун-конъюнкция, склеивающая 6 импортированных фактов (неабелевость qmul, положительность щели на (0,8), сжатие 1/4, грань коррекций 1/32, сумма < 1/10, щель >= 9/4). Чистая агрегация exact-леммами; имя 'synthesis' и значение 9/4 аспирационны — это finite-interval/linearized результат, не континуум-доказательство. _(synthesis, aggregation, aspirational-name)_

**Uniqueness - score 2 (methods).** Явная рациональная нижняя граница 9/4 на щель замкнутой формулы su2_mass_gap на [2,4] + конечная сборка линеаризованной RG-цепи (сжатие/коррекции/самоотображение) в один конъюнкт, с встроенной маркировкой зазора до Clay.
> _Caveat:_ НЕ доказательство Clay Yang-Mills. su2_mass_gap — заданный многочлен (2-beta/8)^2*(2-beta/4), '9/4' = минимум этого многочлена на ОДНОМ отрезке [2,4] (lra/nra), RG линеаризован/аффинен (не QCD beta-функция); what_is_open_step7 сам фиксирует linear!=quartic. Только SU(2). Header '~18 Qed' — фактически 12 (drift); 'AXIOMS: classic' наследуется транзитивно, своих аксиом 0.

---

## #482 - `src/gauge/MassGapProcess.v` - score 2 (methods)

**Transfer matrix as a (constant) QObservable + gauge ProjSys scaffold; gap monotonicity over Q**

- **Topic.** Packages the constant 2x2 transfer matrix as a QObservable, builds the gauge configuration tower as a trivial constant ProjSys, and proves elementary monotonicity/scaling facts about the affine mass gap mass_gap_2x2 (positive on (0,8), shrinks to 0 toward criticality, large at strong coupling).
- **Role.** Projective/spectral re-framing layer of the gauge branch. Imports LinearAlgebra, CauchyReal, ProcessGeneral, physics.{InnerProductSpace,Orthogonality,QObservable,QState,SpectralDichotomy}, linalg.{MatrixOps,EigenvalueTheory}, projective.ProjectiveSystem, gauge.{LatticeStructure,GaugeField,WilsonAction,TransferMatrix}. Mostly self-contained scaffolding; 0 own axioms.
- **Counts.** Qed  / Admitted  / axioms 
- **Imports.** 
- **E/R/R.** _Elements:_ constant-последовательность transfer_2x2(beta) (одна матрица на всех уровнях); rg-конфигурация = Q; число-щель mass_gap_2x2(beta)=2-beta/4. _Roles:_ QObservable = роль-наблюдаемая (несёт спектр); ProjSys = роль-башня огрублений; mass_gap_2x2 = роль-щель; correlation_length = роль-длина (заглушка). _Rules:_ константность => Cauchy тривиально; gap_monotone_beta: щель убывает по beta; на (0,8) щель > 0 => собственные значения различны; continuum: подобрать beta близко к 8 => щель < eps. _P4:_ башня уровней присутствует лишь номинально — это const_sys, проекция = тождество, 'refinement' не порождает нового Element. spectral_ratio/correlation_length = ЯВНЫЕ заглушки (1#1), потому что 1/m и log — нетерминирующие процессы (role-limit), здесь честно обойдены, а не вычислены.
- **Classical counterpart.** Mirrors the transfer-matrix => discrete spectrum picture and the lattice-refinement / continuum-limit programme (correlation length = inverse mass, gap -> 0 at criticality). What differs: the 2x2 transfer matrix is CONSTANT in the refinement index (a const_seq), spectral_ratio and correlation_length are explicit (1#1) PLACEHOLDERS (Qdiv/log avoided), and the 'continuum limit gap -> 0' is just the affine algebra mass_gap_2x2(beta)=2-beta/4 driven to 0 by hand-picking beta near 8.
- **Tags.** mass-gap, SU2, transfer-matrix, observable, projective-system, placeholder, continuum-limit, scaffold
- **Notes.** Qed drift: header '~20' и end-marker total_count (20=20) — фактически 11. ВНУТРЕННИЕ заглушки: spectral_ratio (lambda_1*(1#1)) и correlation_length (1*(1#1)) — Qdiv/real-log обойдены явно (помечены 'placeholder' в исходнике). 0 своих аксиом.

**Lemmas (18):**

| name | kind | role |
|---|---|---|
| `transfer_const_seq` | Definition | постоянная последовательность матриц T(k)=transfer_2x2(beta) |
| `transfer_const_cauchy` | Lemma | записи постоянной последовательности Cauchy (тривиально, разность 0) |
| `transfer_observable` | Definition | QObservable из постоянной симметричной матрицы |
| `transfer_obs_at_k` | Lemma | obs_seq на k = transfer_2x2 beta (reflexivity) |
| `spectral_ratio` | Definition | ЗАГЛУШКА: lambda_1*(1#1), Qdiv обойдён |
| `spectral_gap_shrinks` | Lemma | щель убывает по beta (= gap_monotone_beta) |
| `mass_gap_implies_distinct` | Lemma | щель>0 => собственные значения 0 и 1 различны |
| `correlation_length` | Definition | ЗАГЛУШКА: 1*(1#1) (1/m требует real log) |
| `correlation_length_positive` | Lemma | длина > 0 (тривиально для заглушки) |
| `gauge_projsys` | Definition | const_sys над Q с Qeq — тривиальная башня огрублений |
| `gauge_proj_identity` | Lemma | проекция в const_sys = тождество |
| `gauge_projsys_compat` | Lemma | совместимость проекций const_sys |
| `mass_gap_lattice` | Definition | щель в решёточных единицах = mass_gap_2x2 |
| `continuum_limit_gap` | Lemma | ★ для любого eps>0 есть beta in (0,8) со щелью < eps (подбором beta -> 8) |
| `strong_coupling_large_gap` | Lemma | 3/2 <= щель при beta <= 1 (конфайнмент) |
| `weak_coupling_small_gap` | Lemma | щель <= 1 при 4 <= beta < 8 |
| `mass_gap_process_summary` | Theorem | ★ сводка: наблюдаемая корректна + щель>0 + различимость + ProjSys + континуум-предел |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`continuum_limit_gap`** - Самый 'физический' по виду результат, но по сути элементарная Q-алгебра: mass_gap_2x2(beta)=2-beta/4, и для произвольного eps подбирается beta=8-3eps (или beta=7), так что щель=(3/4)eps<eps. Это НЕ предел корреляционной длины и не критическая теория — линейная функция, загнанная руками к нулю у beta=8. Иллюстрирует 'щель -> 0 у критичности' на игрушечной аффинной модели. _(continuum-limit, affine-gap, criticality, elementary)_
- **`transfer_observable`** - Концептуальное ядро файла: трансфер-матрица оформлена как QObservable через ПОСТОЯННУЮ последовательность (transfer_const_seq), т.е. 'процесс' тривиален — одна матрица на всех уровнях. Cauchy-условие выполняется потому, что разность тождественно 0. Демонстрирует мост решётка->спектральная дихотомия, но без настоящей башни уточнений. _(observable, constant-process, spectral, scaffold)_

**Uniqueness - score 2 (methods).** Переоформление 2x2 трансфер-матрицы как QObservable и gauge-конфигурации как ProjSys-башни, плюс элементарные факты монотонности/масштабирования аффинной щели mass_gap_2x2 над Q.
> _Caveat:_ Каркас, не результат. Наблюдаемая ПОСТОЯННА (const_seq), ProjSys тривиален (const_sys, проекция=id), spectral_ratio и correlation_length — ЯВНЫЕ заглушки (1#1; Qdiv/log обойдены). 'continuum_limit_gap' = линейная mass_gap_2x2=2-beta/4, загнанная к 0 подбором beta. Только SU(2)/2x2, не континуум. Header '~20 Qed' и total_count 20=20 — фактический Qed=11 (drift).

---

## #483 - `src/gauge/MillenniumSynthesis.v` - score 3 (new-framing)

**5-level mass-gap chain aggregator; honest 'distance to Millennium' (Clay NOT proved, gap open)**

- **Topic.** Top-level conjunction that stacks Levels 1-4 (SU(2) lattice gap, bounded Taylor corrections, nonlinear-RG contraction with fixed point 3, exact-RG Cauchy process with per-stage positive gap) and then explicitly states Level 5 as OPEN: there is no proven uniform lower bound; under the pessimistic gap_lower_N the gap decreases, and a uniform delta>0 holds only conditionally on millennium_criterion.
- **Role.** Terminal synthesis node of the entire gauge mass-gap branch. Pure aggregation (0 new content): imports gauge.{RGFlow,TransferMatrix,SU2TransferMatrix,SU2Group,SU2Synthesis,HigherOrderRG,PerturbationRG,MassGapBound,NonlinearRG,ExtendedInterval,GlobalMassGap,LargerLattice,GapMatching,ExactRGProcess,NonperturbativeGap}. Re-exports the named honest-gap theorems.
- **Counts.** Qed  / Admitted  / axioms 
- **Imports.** 
- **E/R/R.** _Elements:_ конкретные конечные стадии k (решётка 2^k); рациональные exact_rg K k beta = num#den; щель-стадии gap_lower_N K (2^k) beta. _Roles:_ уровни 1-5 = роли-ярусы достоверности; millennium_criterion = роль-условие (равномерная нижняя грань); 'distance_to_millennium' = роль-зазор. _Rules:_ уровни 1-4 = конъюнкции доказанных фактов (неабелевость, коррекции, сжатие 16/25 с fp=3, Cauchy + положительная щель на каждой стадии); уровень 5: gap_lower(2^{k+1}) <= gap_lower(2^k) (убывание) + равномерная грань ТОЛЬКО при millennium_criterion. _P4:_ ключевой P4-разрез всего файла: каждая КОНЕЧНАЯ стадия даёт вычислимую положительную щель (Element), но РАВНОМЕРНАЯ грань по всем стадиям (предел/континуум) — нетерминируемый переход (role-limit), не достигнутый. level5_open и distance_to_millennium кодируют этот зазор как теоремы, а не прячут его.
- **Classical counterpart.** Aspires to the Clay Yang-Mills existence-and-mass-gap problem; actually mirrors the lattice strong-coupling gap + Banach/RG-flow + finite-stage transfer-matrix picture. What differs CRUCIALLY: nothing here is a continuum / infinite-volume / SU(3) proof — it is a conjunction of finite-stage and approximate-RG facts, and the file's OWN theorems (level5_open, distance_to_millennium) state the gap to Clay remains open (pessimistic bound drives gap -> 0; uniform bound only CONDITIONAL on millennium_criterion).
- **Tags.** mass-gap, millennium, synthesis, aspirational-name, over-branding, honesty, conditional, finite-stage, RG, SU2
- **Notes.** Qed drift: header '~20' и end-marker total_count (20=20) — фактически 12. OVER-BRANDING: имена millennium_synthesis / the_complete_chain_v2 / 'MILLENNIUM SYNTHESIS' аспирационны; безусловно доказаны только конечно-стадийные факты, Clay открыт (см. level5_open, distance_to_millennium, what_remains). Импортирует aspirational-имена GlobalMassGap, LargerLattice. 0 своих аксиом.

**Lemmas (13):**

| name | kind | role |
|---|---|---|
| `level1_lattice_model` | Theorem | SU(2) неабелева + щель>0 на (0,8) |
| `level2_corrections_bounded` | Theorem | квартик-коррекция <= 1/32 + сумма < 1/10 |
| `level3_nonlinear_rg` | Theorem | сжатие 16/25 + fp=3 + орбиты Cauchy + щель на каждом итерате |
| `level4_exact_rg` | Theorem | точный RG-процесс Cauchy + щель>0 на каждой стадии + в (0,8) + gap matching |
| `level5_open` | Theorem | ★ ЧЕСТНОСТЬ: linear!=quadratic, exact!=Gaussian, щель убывает (нет равномерной грани) |
| `the_complete_chain_v2` | Theorem | ★ конъюнкт A-H: неабелевость + щель>0 + 2 сжатия + Cauchy + щель>=9/4 + точный Cauchy + щель на стадии |
| `distance_to_millennium` | Theorem | ★ зазор до Clay: пп.1-3 = открытые/убывающие факты, п.4 = равномерная грань ТОЛЬКО при millennium_criterion |
| `model_limitations_v2` | Theorem | rg_quad<4 всюду, нет деконфайнмента (<8), exact_rg<8 — ограниченность орбит |
| `what_tos_proves` | Theorem | exact_rg рационален (num#den) + Cauchy + щель>0 на стадии + SU(2)-щель на каждом выходе |
| `what_remains` | Theorem | ★ единственный открытый вопрос: равномерная нижняя грань (условно на millennium_criterion) |
| `millennium_synthesis` | Theorem | ★ ГЛАВНЫЙ конъюнкт всех уровней — но имя аспирационно (Clay НЕ доказан) |
| `global_summary_v2` | Theorem | ключевые числа: щель>=9/4 в beta=3, сжатие 16/25, fp=3, точный процесс Cauchy |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`distance_to_millennium`** - Самый ценный (и самый честный) пункт файла: явно перечисляет ЧТО отделяет результат от Clay — (1) rg_map_linear != rg_map_quadratic, (2) exact_rg != Gaussian, (3) пессимистическая грань gap_lower(2^{k+1}) <= gap_lower(2^k) УБЫВАЕТ, и только (4) при дополнительном допущении millennium_criterion появляется delta>0. Это анти-оверклейм прямо в коде: 'synthesis'/'millennium' в именах не подкреплены безусловной теоремой. _(honesty, open-problem, millennium-gap, conditional)_
- **`millennium_synthesis`** - Центральный конъюнкт-капстоун, собирающий уровни 1-4 (неабелевость, грань коррекций, сжатие 16/25 с fp=3, точный Cauchy-процесс с per-stage щелью и gap matching). Чистая агрегация exact-импортами, 0 нового. Имя — флагманский over-branding: НИ ОДИН конъюнкт не утверждает равномерную/континуум-щель; безусловная часть строго конечно-стадийна. _(aspirational-name, aggregation, finite-stage, over-branding)_
- **`the_complete_chain_v2`** - Восьмичленная (A-H) сводная цепь, объединяющая линейное и квадратичное сжатия, сходимость орбит, грань 9/4 на [2,4] и точный RG-процесс. Демонстрирует охват ветки, но 'complete' относится к СБОРКЕ существующих лемм, не к решению задачи; H (щель на каждой конечной стадии) — максимум безусловного. _(aggregation, complete-name, finite-stage)_

**Uniqueness - score 3 (new-framing).** Стратифицированная (5 уровней) сборка всей gauge-ветки щели масс с ВСТРОЕННОЙ, теоремно закодированной честной картой 'distance_to_millennium': что доказано безусловно (конечно-стадийно) vs что остаётся открытым (равномерная грань, условная на millennium_criterion).
> _Caveat:_ Clay Yang-Mills НЕ доказан, несмотря на имена millennium_synthesis/the_complete_chain_v2 (over-branding — флаг). Всё безусловное — конечно-стадийно/приближённо (линейный и квадратичный RG, не QCD beta-функция; только SU(2)/2x2; нет континуума/бесконечного объёма). level5_open и distance_to_millennium сами фиксируют: пессимистическая щель УБЫВАЕТ к 0, равномерная грань лишь УСЛОВНА. Чистая агрегация, 0 нового содержания. Header '~20 Qed' и total_count 20=20 — фактически 12 (drift).

---

## #484 - `src/gauge/NonlinearRG.v` - score 2 (methods)

**Exact rational RG f(beta)=4beta/(1+beta): contraction (factor 16/25), unique fixed point 3, Banach convergence**

- **Topic.** Replaces the linearized RG by the exact rational map f(beta)=4beta/(1+beta) and proves it is a genuine contraction on [3/2,B] for any B>=4 (Lipschitz factor 16/25 via the key difference identity f(x)-f(y)=4(x-y)/((1+x)(1+y))), with unique fixed point beta*=3, Banach convergence and geometric rate.
- **Role.** The most self-contained, genuinely-proved file of the gauge mass-gap branch. Imports CauchyReal, SeriesConvergence, RealField, FixedPoint (is_contraction, iterate_is_cauchy, iterate_contraction, contraction_unique_fixed), gauge.RGFlow, SU2TransferMatrix, zeta.ZetaProcess. Feeds the nonlinear-RG levels of MillenniumSynthesis. 0 own axioms.
- **Counts.** Qed  / Admitted  / axioms 
- **Imports.** 
- **E/R/R.** _Elements:_ рациональное beta; конкретные значения f(3/2)=12/5, f(1)=2, f(4)=16/5, f(100)=400/101; итераты iterate f x n. _Roles:_ rg_map_quadratic = роль-поток (огрубление); is_contraction(.,3/2,B,16/25) = роль-сжатие; неподвижная точка beta*=3 = роль-аттрактор; Lipschitz-фактор 16/25 = роль-скорость. _Rules:_ тождество разности f(x)-f(y)=4(x-y)/((1+x)(1+y)) (field) => монотонность + Lipschitz 16/25 (граница 1/денома <= 4/25 на [3/2,inf)); Banach => Cauchy-итераты; единственность fp через contraction_unique_fixed; rg_linear >= rg_quadratic. _P4:_ тут граница финитизации работает В ПОЛЬЗУ Element: точное рациональное f даёт ВЫЧИСЛИМЫЕ итераты и неподвижную точку 3 (в отличие от заглушек соседних файлов). Предел итерат — Cauchy-процесс (потенциальный, не достигнутый объект), но скорость (16/25)^n явная. rg_linear_neq_quadratic фиксирует: линеаризация — отдельный (приближённый) объект.
- **Classical counterpart.** Mirrors the Banach contraction-mapping / fixed-point theorem applied to a discrete RG step, and the standard fact that a Mobius/rational map f(x)=4x/(1+x) has an attracting fixed point. What differs: this is EXACT rational arithmetic over Q (field; lra), the contraction factor 16/25 is computed as the max derivative on [3/2,B], and the 'RG' is a toy 1D rational recursion, not the Yang-Mills beta-function.
- **Tags.** RG, contraction, banach, fixed-point, exact-rational, mobius-map, lipschitz, honest-tradeoff, field
- **Notes.** Qed drift: header '~35', summary-блок '~33' и end-marker total_count (33=33) — фактически 23. Самый содержательный (не-заглушечный) файл пятёрки: настоящее доказательство сжатия. rg_map_quadratic/rg_map_linear/rg_quadratic_at_3/rg_quadratic_at_2 определены в импортах (RGFlow), не здесь. 0 своих аксиом.

**Lemmas (36):**

| name | kind | role |
|---|---|---|
| `one_plus_pos` | Lemma | 0<beta => 0<1+beta |
| `one_plus_nonzero` | Lemma | 0<beta => 1+beta != 0 (знаменатель) |
| `rg_quad_pos` | Lemma | f(beta)>0 при beta>0 |
| `rg_quad_lt_4` | Lemma | f(beta)<4 для всех beta>0 (ограниченность образа) |
| `rg_quad_lt_8` | Lemma | f(beta)<8 (нет деконфайнмента) |
| `rg_quad_at_3_2` | Lemma | f(3/2)=12/5 (vm/lia) |
| `rg_quad_at_1` | Lemma | f(1)=2 |
| `rg_quad_at_4` | Lemma | f(4)=16/5 |
| `rg_quad_at_100` | Lemma | f(100)=400/101 |
| `rg_quad_ge_3_2` | Lemma | beta>=3/2 => f(beta)>=3/2 (нижняя инвариантность) |
| `rg_quad_maps_interval` | Lemma | f: [3/2,B] -> [3/2,B] при B>=4 (самоотображение) |
| `rg_quad_diff` | Lemma | ★ КЛЮЧЕВОЕ тождество f(x)-f(y)=4(x-y)/((1+x)(1+y)) (field) |
| `rg_quad_minus_beta` | Lemma | f(beta)-beta=beta(3-beta)/(1+beta) (локализует fp=3) |
| `product_denom_pos` | Lemma | (1+x)(1+y)>0 (nra) |
| `rg_quad_increasing` | Lemma | f монотонно неубывает |
| `rg_quad_strictly_increasing` | Lemma | f строго возрастает |
| `denom_lower_bound` | Lemma | (1+x)(1+y)>=25/4 на [3/2,inf) |
| `inv_denom_upper` | Lemma | 1/((1+x)(1+y))<=4/25 (источник фактора 16/25) |
| `rg_quad_lipschitz` | Lemma | ★ \|f(x)-f(y)\|<=(16/25)\|x-y\| на [3/2,B] |
| `rg_quad_factor_bounds` | Lemma | 0<=16/25<1 (валидный фактор сжатия) |
| `rg_quad_is_contraction` | Theorem | ★ f — сжатие на [3/2,B] для любого B>=4 |
| `rg_quad_contraction_4` | Theorem | сжатие на стандартном [3/2,4] |
| `rg_quad_unique_fp` | Theorem | ★ единственная fp в [3/2,4] — это beta*=3 |
| `rg_quad_banach` | Theorem | Banach: итераты Cauchy из любой точки [3/2,B] |
| `iterate_at_fp` | Lemma | iterate f 3 n = 3 (3 неподвижна) по индукции |
| `rg_quad_convergence_rate` | Theorem | ★ \|f^n(x)-3\|<=(16/25)^n\|x-3\| (геометрическая скорость) |
| `both_agree_at_fp` | Lemma | rg_linear(3)=3 и rg_quadratic(3)=3 (совпадают в fp) |
| `rg_difference` | Lemma | f_L-f_Q=(beta-3)^2/(4(1+beta)) (расхождение приближений) |
| `rg_linear_ge_quadratic` | Lemma | f_Q<=f_L (линейный завышает) — через знак квадрата |
| `rg_linear_neq_quadratic` | Lemma | ★ ~(forall beta, f_L==f_Q): приближения различны |
| `iterate_from_2_1` | Lemma | iterate f 2 1 = 8/3 (конкретный шаг) |
| `iterate_from_2_2` | Lemma | iterate f 2 2 = 32/11 |
| `nonlinear_rg_main` | Theorem | ★ главный конъюнкт: сжатие + fp=3 + единственность + сходимость + f<4 |
| `what_step8_proves` | Theorem | сводка: сжатие для любого B>=4, 16/25<1, совпадение в fp, линейный завышает |
| `what_step8_opens` | Theorem | честный остаток: f_L != f_Q |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`rg_quad_diff`** - Алгебраическое ядро всего файла: тождество f(x)-f(y)=4(x-y)/((1+x)(1+y)), доказанное чистым field над Q. Из него каскадом следуют монотонность, точная константа Lipschitz (через denom>=25/4 => 1/denom<=4/25 => фактор 4*4/25=16/25) и геометрическая скорость. Это настоящий, не-заглушечный контент — стандартная теорема о сжатии рационального отображения, аккуратно и ТОЧНО (без R) проведённая. _(key-identity, field, lipschitz, exact-rational)_
- **`rg_quad_is_contraction`** - Главная теорема: f — формальное is_contraction (импорт FixedPoint) на [3/2,B] для ЛЮБОГО B>=4, т.е. самоотображение + Lipschitz 16/25<1. Отсюда через библиотечные iterate_is_cauchy / contraction_unique_fixed получаются Banach-сходимость и единственность fp=3. Честно: 16/25 > 1/4 линейного фактора — точность платится медленной скоростью, что файл прямо отмечает. _(contraction, banach, fixed-point, honest-tradeoff)_
- **`rg_quad_unique_fp`** - beta*=3 — ЕДИНСТВЕННАЯ неподвижная точка в [3/2,4], выведена не вычислением, а из контрактности (contraction_unique_fixed) + проверки rg_quadratic_at_3. Структурно правильный аргумент единственности (а не просто 'подставили 3'), что отличает файл от чисто вычислительных соседей. _(uniqueness, fixed-point, structural)_

**Uniqueness - score 2 (methods).** Точная (над Q, без R) формализация того, что рациональное RG-отображение 4beta/(1+beta) есть банахово сжатие на [3/2,B] с константой 16/25, единственной неподвижной точкой 3 и геометрической скоростью — через явное тождество разности и library FixedPoint.
> _Caveat:_ Стандартная теорема о сжимающем отображении / Mobius-аттракторе; ново лишь EXACT-Q проведение и явная константа 16/25. f(beta)=4beta/(1+beta) — игрушечная 1D рекурсия, НЕ Yang-Mills beta-функция; неподвижная точка 3 и связь со щелью масс — модельные. rg_linear_neq_quadratic сам фиксирует, что это лишь одно из приближений. Header '~35'/summary '~33'/total_count 33=33 — фактический Qed=23 (заметный drift). 0 своих аксиом.

---

## #485 - `src/gauge/NonperturbativeGap.v` - score 3 (new-framing)

**Conditional non-perturbative gap: per-stage positivity unconditional, uniform bound only given millennium_criterion**

- **Topic.** Cleanly separates what is unconditionally true (gap positive at every finite stage, exact RG stays in (0,8), the orbit process is Cauchy) from what is open (a uniform lower bound delta>0), defining millennium_criterion as that hypothesis and proving the conditional implication; states plainly that the pessimistic gap_lower_N decreases toward 0.
- **Role.** The 'honest accounting' file of the gauge mass-gap branch and the reformulation hub reused by MillenniumSynthesis (millennium_criterion, gap_positive_all_stages, su2_gap_at_rg_output, process_is_cauchy). Imports CauchyReal, FixedPoint, gauge.{TransferMatrix,SU2TransferMatrix,LargerLattice,GapMatching,ExactRGProcess}. 0 own axioms.
- **Counts.** Qed  / Admitted  / axioms 
- **Imports.** 
- **E/R/R.** _Elements:_ конечная стадия k (решётка 2^k); рациональный exact_rg K k beta; щель-стадии gap_lower_N K (2^k) beta; параметр delta. _Roles:_ gap_lower_N = роль-щель на стадии; exact_rg = роль-поток; millennium_criterion = роль-условие (равномерная грань); 'pessimistic bound' = роль-оценка снизу (заведомо заниженная). _Rules:_ безусловно: gap_lower_N_pos_pow2 (щель>0 на стадии), exact_rg_range (в (0,8)), unconditional_cauchy (процесс Cauchy); пессимизм: gap_lower(2^{k+1})<=gap_lower(2^k); условно: millennium_criterion => delta>0 на всех стадиях. _P4:_ ЧИСТЫЙ образец P4-разреза: для всякой КОНЕЧНОЙ стадии (Element) щель вычислима и положительна; переход к РАВНОМЕРНОЙ грани по всем k (континуум/предел) — нетерминируемый, role-limit, не достигнут. millennium_criterion реифицирует именно этот недостающий предел как явную гипотезу; pessimistic_gap_to_zero признаёт, что наличная (заниженная) оценка стремится к 0.
- **Classical counterpart.** Aspires toward the Yang-Mills mass-gap (Clay) and mirrors the lattice finite-volume gap + RG-flow picture. What differs DECISIVELY: every UNCONDITIONAL theorem is per-FINITE-stage (gap_lower_N K (2^k) beta > 0, exact_rg in (0,8), process Cauchy); the limit/uniform gap is NOT proved — it is packaged as a hypothesis millennium_criterion, and pessimistic_gap_to_zero states the built-in pessimistic bound actually DECREASES toward 0.
- **Tags.** mass-gap, conditional, millennium, honesty, finite-stage, non-perturbative, P4, RG, SU2, reformulation
- **Notes.** Qed drift: header '~18' и end-marker total_count (15=15) — фактически 11. Это 'честный' файл ветки: millennium_criterion вынесено в гипотезу, pessimistic_gap_to_zero признаёт убывание оценки к 0. gap_lower_N/exact_rg/exact_rg_range/gap_lower_N_pos_pow2/gap_lower_pow2_chain/gap_contracts/gap_matching_preserves_gap определены в импортах (ExactRGProcess, GapMatching, LargerLattice). 0 своих аксиом.

**Lemmas (13):**

| name | kind | role |
|---|---|---|
| `gap_positive_all_stages` | Theorem | ★ щель>0 на каждой конечной стадии 2^k (= gap_lower_N_pos_pow2) |
| `rg_in_range_all_stages` | Theorem | exact_rg K k beta in (0,8) на всех стадиях |
| `su2_gap_at_rg_output` | Theorem | SU(2)-щель>0 на каждом RG-выходе |
| `finite_dim_gap` | Theorem | конъюнкт: щель>0 на стадии И SU(2)-щель>0 |
| `process_is_cauchy` | Theorem | exact_rg_orbit Cauchy (= unconditional_cauchy) |
| `pessimistic_gap_to_zero` | Theorem | ★ ЧЕСТНОСТЬ: каждая щель>0, НО последовательность убывает к 0 (нет равномерной грани) |
| `millennium_criterion` | Definition | ★ гипотеза: exists delta>0, forall k, delta<=gap_lower_N (реификация недостающего предела) |
| `millennium_implies_gap` | Theorem | при millennium_criterion: delta-грань + SU(2)-щель на каждой стадии |
| `conditional_gap_from_contraction` | Theorem | при gap_contracts: SU(2)-щель>0 на каждой стадии (условный) |
| `proved_results` | Theorem | ★ сводка БЕЗУСЛОВНОГО: щель>0 + (0,8) + SU(2)-щель + Cauchy + gap matching |
| `reformulation` | Theorem | ★ Clay (для модели) = существует ли delta>0 равномерно (условно на millennium_criterion) |
| `nonperturbative_main` | Theorem | ★ главный: безусловная щель-на-стадии + Cauchy + условная равномерная грань |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`pessimistic_gap_to_zero`** - Самый честный пункт ветки: явно доказывает, что заложенная нижняя оценка gap_lower_N (= mass_gap/N) на каждой стадии положительна, НО монотонно убывает (gap_lower(2^{k+1}) <= gap_lower(2^k)), т.е. безусловно НИКАКОЙ равномерной грани нет, оценка стремится к 0. Комментарий прямо называет это 'DESIGN' и отмечает, что строгое доказательство обнуления упёрлось бы в Архимедово свойство — поэтому утверждается структурное следствие (убывание), а не предел. Анти-оверклейм в чистом виде. _(honesty, pessimistic-bound, monotone-decreasing, no-uniform-bound)_
- **`millennium_criterion`** - Определение-водораздел: реифицирует недостающий континуум-результат как ГИПОТЕЗУ exists delta>0, forall k, delta<=gap_lower_N. Все 'millennium'-теоремы файла (reformulation, nonperturbative_main, millennium_implies_gap) условны на ней. Это методологически правильная локализация зазора до Clay: не доказано, а названо и вынесено в посылку. _(conditional, hypothesis, millennium-gap, reformulation)_
- **`proved_results`** - Сводка БЕЗУСЛОВНО доказанного: (1) щель>0 на каждой стадии 2^k, (2) exact_rg в (0,8), (3) SU(2)-щель>0 на каждом выходе, (4) процесс Cauchy, (5) gap matching mass_gap_2x2(exact_rg)==gap_lower_N. Всё — per-finite-stage; ни один пункт не утверждает равномерную/предельную щель. Аккуратно очерчивает верхнюю границу безусловного знания ветки. _(finite-stage, unconditional, summary)_

**Uniqueness - score 3 (new-framing).** Чистое разделение безусловного (per-finite-stage положительная щель, exact_rg in (0,8), Cauchy-процесс) и открытого (равномерная нижняя грань), с реификацией недостающего предела как явной гипотезы millennium_criterion и честной теоремой pessimistic_gap_to_zero об убывании наличной оценки к 0.
> _Caveat:_ Yang-Mills mass-gap (Clay) НЕ доказан: всё безусловное — конечно-стадийно, равномерная грань лишь УСЛОВНА на millennium_criterion, а заложенная оценка gap_lower_N сама убывает к 0 (pessimistic_gap_to_zero). Модельно (только SU(2)/2x2, нет континуума/бесконечного объёма/N>2 анализа). Ценность — методологическая (честная локализация зазора), не новая теорема. Header '~18'/total_count 15=15 — фактический Qed=11 (drift).

---

## #486 - `src/gauge/PerturbationRG.v` - score 2 (methods)

**RG-поток возмущений: щель выживает на всей орбите [2,4] для любого порядка Тейлора**

- **Topic.** Доказывает, что итерации самоотображающего [a,b]→[a,b] остаются в [a,b], даёт оценку сдвига неподвижной точки δ/(1−c), и заключает: щель масс SU(2) положительна в каждой точке орбиты квартического/секстического RG, потому что вся орбита лежит в [2,4]⊂(0,8), где щель заведомо >0.
- **Role.** Надстройка над gauge.RGFlow / gauge.HigherOrderRG / gauge.SU2TransferMatrix. Импортирует su2_mass_gap, rg_map_quartic/sextic, rg_*_maps_interval. Почти всё — обёртки exact над su2_mass_gap_positive и rg_*_maps_interval. Переиспользуется как сводка устойчивости щели к возмущениям.
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs List Lia ZArith Lqa; ToS.CauchyReal; ToS.SeriesConvergence; ToS.FixedPoint; gauge.RGFlow; gauge.SU2TransferMatrix; gauge.HigherOrderRG
- **E/R/R.** _Elements:_ конкретные рациональные точки орбиты β∈[2,4]; отображения rg_map_quartic/sextic : Q→Q; сдвиги fp_shift = δ/(1−c) (квартика 1/24, полный 2/15). _Roles:_ RG-отображение = роль-шаг потока; неподвижная точка β* = роль-аттрактор; щель su2_mass_gap = наблюдаемая роль; интервал [2,4] = роль-ловушка орбиты. _Rules:_ iterate_self_map_in_interval (самоотображение держит орбиту), su2_mass_gap β>0 на (0,8), сдвиг неподвижной точки ≤ δ/(1−c). _P4:_ щель определена и положительна на КАЖДОЙ конечной стадии орбиты (Element-сторона: вычислимо при любом n) — завершённый предел/истинная RG-инвариантность не требуются; устойчивость к возмущению = свойство конечного процесса, а не недостижимого аттрактора.
- **Classical counterpart.** Классическая теория возмущений RG-потока (Wilson, Polchinski) и теорема о сдвиге неподвижной точки при возмущении отображения (\|\|Δx*\|\| ≤ δ/(1−c)) — стандарт. НОВО здесь только то, что вывод чисто арифметический: щель su2_mass_gap β положительна для ЛЮБОГО β∈[2,4] (⊂(0,8)) — поэтому ни одна неподвижная точка любого порядка Тейлора (квартика/секстика) и ни одна точка орбиты не может щель обнулить. RG-инвариантность здесь не вычисляется, а ОБХОДИТСЯ.
- **Tags.** gauge, mass-gap, RG-flow, perturbation, SU2, fixed-point, exact-Q, P4
- **Notes.** Заголовок STATUS: ~20 Qed — фактически 18 Qed (включая заглушку total_count). 0 Admitted, 0 axioms (классические аксиомы classic приходят транзитивно через PowerSeries/CauchyReal, не объявлены здесь). Гипотезы неподвижной точки в quartic/sextic_gap_positive игнорируются (_).

**Lemmas (21):**

| name | kind | role |
|---|---|---|
| `iterate_self_map_in_interval` | Lemma | ★ итерация любого [a,b]→[a,b] отображения остаётся в [a,b] (индукция по n) |
| `fp_shift_bound` | Definition | оценка сдвига неподвижной точки δ/(1−c) |
| `quartic_fp_shift` | Definition | квартический сдвиг = fp_shift_bound delta_quartic (1/4) |
| `total_fp_shift` | Definition | полный сдвиг со всеми поправками = fp_shift_bound (1/10) (1/4) |
| `fp_shift_bound_value` | Lemma | quartic_fp_shift == 1/24 (vm/lia) |
| `fp_shift_positive` | Lemma | 0 < quartic_fp_shift |
| `total_fp_shift_value` | Lemma | total_fp_shift == 2/15 |
| `total_fp_shift_small` | Lemma | total_fp_shift < 1 |
| `gap_at_any_orbit_point` | Lemma | ★ любой β∈[2,4] даёт 0 < su2_mass_gap β (через su2_mass_gap_positive, [2,4]⊂(0,8)) |
| `quartic_gap_positive` | Theorem | неподвижная точка квартического RG в [2,4] имеет щель >0 (гипотеза fp игнорируется) |
| `sextic_gap_positive` | Theorem | неподвижная точка секстического RG в [2,4] имеет щель >0 |
| `general_gap_positive` | Theorem | простейшая форма: β*∈[2,4] ⟹ щель >0 (= gap_at_any_orbit_point) |
| `quartic_orbit_in_interval` | Lemma | орбита квартического RG из [2,4] остаётся в [2,4] |
| `sextic_orbit_in_interval` | Lemma | орбита секстического RG из [2,4] остаётся в [2,4] |
| `quartic_orbit_gap_positive` | Theorem | щель >0 в каждой точке квартической орбиты |
| `sextic_orbit_gap_positive` | Theorem | щель >0 в каждой точке секстической орбиты |
| `gap_vs_perturbation` | Lemma | сдвиг 1/24 < su2_mass_gap 3 (щель доминирует возмущение) |
| `gap_robust` | Theorem | щель переживает любое возмущение, сохраняющее β*∈[2,4] (= gap_at_any_orbit_point) |
| `perturbation_summary` | Theorem | сводка: орбита в интервале ∧ щель на орбите ∧ сдвиг=1/24 ∧ общая положительность |
| `perturbation_main` | Theorem | главная сводка: щель на квартической ∧ секстической орбите ∧ общая |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`gap_at_any_orbit_point`** - Несущая лемма всего файла и источник его честной слабости: положительность щели НЕ выводится из RG-динамики, а получается тем, что весь рабочий интервал [2,4] вложен в область (0,8), где su2_mass_gap_positive (из SU2TransferMatrix) уже даёт >0. Поэтому ВСЕ 'gap_positive'-теоремы (квартика, секстика, орбита, robust) — это один и тот же факт под разными обёртками exact; гипотезы о неподвижной точке (rg_map β*==β*) даже не используются (стоят как _). Это аккуратно, но не ново. _(mass-gap, interval-trap, exact, load-bearing)_
- **`iterate_self_map_in_interval`** - Единственная содержательная (хотя элементарная) лемма: тривиальной индукцией по числу итераций показывает, что орбита самоотображающего интервал отображения не покидает интервал. Именно она превращает 'щель на [2,4]' в 'щель на всей орбите', замыкая аргумент устойчивости. Классический инвариантный-интервал факт динамических систем, здесь над Q. _(dynamical-systems, invariant-interval, induction)_

**Uniqueness - score 2 (methods).** Необычная (чисто арифметическая, над Q) формализация устойчивости щели масс SU(2) к RG-возмущениям: щель положительна в каждой точке орбиты при любом порядке тейлоровской поправки, без вычисления самой RG-инвариантности.
> _Caveat:_ НЕ доказательство Clay: конечная решётка, группа только SU(2), щель = спектральная щель малой решётки, не континуум. Положительность щели обходит RG-динамику (всё [2,4]⊂(0,8)), гипотезы о неподвижной точке не используются; почти все теоремы — обёртки одного факта su2_mass_gap_positive. Заголовок заявляет ~20 Qed — фактически 18.

---

## #487 - `src/gauge/PhaseB_Synthesis.v` - score 3 (new-framing)

**Синтез Фазы B: трансфер-матрица с полными термами — щель ∧ RP ∧ кластер в одном LatticeQFT**

- **Topic.** Связывает результаты Фазы B (gap из собственных значений, RP из положительности, кластер из отношения <1) в единое утверждение; вводит запись LatticeQFT (параметры β∈[0,2], J≥1) и капстоун yang_mills_lattice_gap_PROVED с полными термами для всех трёх OS-свойств.
- **Role.** Агрегатор Фазы B: импортирует CharacterTransfer, ExactMassGap, GapRatio, ReflectionPositivity, LatticeCorrelations, TransferMatrixProof, ReflectionPositiveProof, ClusterProof. Все теоремы — exact-обёртки чужих лемм (matrix_gap_positive_*, reflection_positivity_from_matrix, cluster_*). Сам переиспользуется ProofClosure.v (#489) как поставщик LatticeQFT, lqft_gap_value_*, lqft_strict_gap_*.
- **Counts.** Qed 17 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS.CauchyReal; ToS.SeriesConvergence; gauge.CharacterTransfer; gauge.ExactMassGap; gauge.GapRatio; gauge.ReflectionPositivity; gauge.LatticeCorrelations; gauge.TransferMatrixProof; gauge.ReflectionPositiveProof; gauge.ClusterProof
- **E/R/R.** _Elements:_ решёточная КТП как запись LatticeQFT (β, J + доказательства диапазона); конкретные обитатели lqft_beta_1 (β=1,J=1), lqft_beta_2 (β=2); собственные значения трансфер-матрицы; значения щели 289/384, 1/24. _Roles:_ трансфер-матрица = роль-эволюция; собственное значение = роль-уровень; щель/RP/кластер = три наблюдаемые роли; LatticeQFT = объект-арена, несущий все роли сразу. _Rules:_ matrix_mass_gap J 1 0 == 289/384 ∧ >0; reflection_positivity_from_matrix (0≤β≤2 ⟹ RP≥0); кластер (∀ε>0 ∃t0, corr<ε); OS4-структурность, OS5-кластер, energy_gap>0. _P4:_ решёточная КТП ПОЛНОСТЬЮ определена конечным набором параметров (Element-сторона): на любой конкретной (β,J)-арене щель/RP/кластер вычислимы и доказаны полными термами; континуальная реконструкция (Wightman из RP) НЕ здесь — она в роли-пределе, недостигнутом на этой стадии.
- **Classical counterpart.** Зеркалит конструктивную программу Остервальдера–Шрадера / Вильсона для решёточной калибровочной теории: трансфер-матрица диагональна с бесселевыми собственными значениями, положительность отражения (OS4), кластерное свойство (OS5), спектральная щель. НОВО — не математика (всё импортировано), а УПАКОВКА: запись LatticeQFT, полностью определяющая решёточную КТП параметрами, и единый капстоун yang_mills_lattice_gap_PROVED, собирающий три свойства с полными термами доказательства (без True).
- **Tags.** gauge, mass-gap, transfer-matrix, reflection-positivity, cluster, OS-axioms, SU2, synthesis, over-branding
- **Notes.** Заголовок STATUS: ~25 Qed — фактически 17 Qed. 0 Admitted (совпадение 'No Admitted' в комментарии — не Admitted-команда), 0 axioms. Print Assumptions yang_mills_lattice_gap_PROVED стоит в конце. Имя файла/теорем over-branded; внутрифайловой honest-note (как в ProofClosure) НЕТ — отмечено флагом в манифесте.

**Lemmas (20):**

| name | kind | role |
|---|---|---|
| `proved_mass_gap_1` | Theorem | 0 < matrix_mass_gap J 1 0 (= matrix_gap_positive_1) |
| `proved_mass_gap_2` | Theorem | 0 < matrix_mass_gap J 2 0 (= matrix_gap_positive_2) |
| `proved_reflection_positivity` | Theorem | 0≤β≤2 ⟹ 0 ≤ rp_inner_matrix 1 β 0 f (= reflection_positivity_from_matrix) |
| `proved_cluster_1` | Theorem | ∀ε>0 ∃t0, matrix_corr J 1 0 1 t0 < ε |
| `proved_cluster_2` | Theorem | ∀ε>0 ∃t0, matrix_corr J 2 0 1 t0 < ε |
| `three_properties` | Theorem | щель ∧ RP ∧ кластер вместе (конъюнкция пяти) |
| `bessel_to_gap` | Theorem | сквозной: значения щели 289/384, 1/24 ∧ их положительность |
| `LatticeQFT` | Record | ★ решёточная КТП = {β, J, 0≤β, β≤2, 1≤J} — полностью специфицирована параметрами |
| `lqft_beta_1` | Definition | конкретная КТП при β=1, J=1 (ltac:lra/lia) |
| `lqft_beta_2` | Definition | конкретная КТП при β=2, J=1 |
| `lqft_has_gap` | Theorem | всякая LatticeQFT имеет щель ≥0 |
| `lqft_has_rp` | Theorem | всякая LatticeQFT имеет RP |
| `lqft_strict_gap_1` | Theorem | 0 < matrix_mass_gap 1 1 0 (строгая щель) |
| `lqft_strict_gap_2` | Theorem | 0 < matrix_mass_gap 1 2 0 |
| `lqft_gap_value_1` | Theorem | matrix_mass_gap 1 1 0 == 289/384 |
| `lqft_gap_value_2` | Theorem | matrix_mass_gap 1 2 0 == 1/24 |
| `yang_mills_lattice_gap_PROVED` | Theorem | ★ капстоун: T диагональна+бессель ∧ щель=289/384>0 ∧ RP ∧ кластер ∧ энергощель >0 (полные термы) |
| `yang_mills_gap_exists` | Theorem | ∃gap, gap=289/384 ∧ >0 ∧ RP ∧ кластер (экзистенциальный вариант) |
| `phase_b_proved` | Theorem | что закрыла Фаза B: диагональность ∧ бессель ∧ OS4 ∧ OS5 ∧ энергощель |
| `phase_b_summary` | Theorem | арифметический маркер (5+5+4+5+5+5+4=33)%nat |

**Key lemmas (deep):**

- **`yang_mills_lattice_gap_PROVED`** - Центральный капстоун: десятичленная конъюнкция, собирающая диагональность трансфер-матрицы, бесселевы собственные значения, точное значение щели 289/384, её положительность (для β=1 и β=2), положительность отражения (OS4), кластерное свойство (OS5) и энергощель — каждый конъюнкт замыкается exact чужой леммы. Ценность чисто организационная: 'нет True, нет Admitted'. ВНИМАНИЕ к бренду: имя 'YANG-MILLS MASS GAP ... PROVED' и три ★ — аспирационны; это конечнорешёточный факт (J∈{0,1,2}, β∈[0,2], SU(2)), НЕ континуальная Clay-формулировка. В отличие от ProofClosure.v честной оговорки про Reading-1/Reading-2 в этом файле НЕТ. _(capstone, over-branding, OS-axioms, synthesis, finite-lattice)_
- **`LatticeQFT`** - Единственная собственная конструкция файла: запись, делающая решёточную КТП объектом, полностью определённым параметрами (β с доказательствами 0≤β≤2, J≥1). Element-сторона P4 в чистом виде — вся 'физика' стадии упакована в конечные данные, и щель/RP доказываются для произвольного обитателя записи (lqft_has_gap, lqft_has_rp). Переиспользуется ProofClosure.v. Стандартный приём 'теория = запись параметров', но опрятный мост к экзистенциальным капстоунам. _(record, bundling, P4-element, reuse)_

**Uniqueness - score 3 (new-framing).** Решёточная КТП переупакована в один объект LatticeQFT, полностью заданный параметрами, и единый капстоун с полными термами связывает три OS-свойства (щель, RP, кластер) — рамка 'теория = запись + капстоун без True'.
> _Caveat:_ 0 нового содержания: все конъюнкты — exact чужих лемм. НЕ доказательство Clay: конечная решётка J∈{0,1,2}, β∈[0,2], только SU(2); 'щель 289/384' — спектральная щель решётки, не континуум. ОВЕРБРЕНДИНГ: имена *_PROVED / 'THE YANG-MILLS MASS GAP' без внутрифайловой оговорки про континуум (контраст с ProofClosure.v). Заголовок ~25 Qed — фактически 17.

---

## #488 - `src/gauge/ProcessMassGap.v` - score 4 (synthesis+observation)

**Процессная щель масс: формальный P4-критерий (PMG1 равномерность, PMG2 Коши C·rᴹ, PMG3 монотонность) для SU(2)**

- **Topic.** Определяет has_process_mass_gap для процесса gap : nat→Q (равномерная нижняя граница ε, явная скорость Коши |gap_{M+1}−gap_M|≤C·rᴹ, монотонность) и доказывает его для SU(2)-щели при β=1 с C=2, r=1/4 через домин­ирование бесселевых членов по знаменателям.
- **Role.** Несущий математический файл связки: импортирует CharacterTransfer, ExactMassGap, SpectralGapCorrect, TransferMatrixProof, stdlib.Combinatorics. Содержит собственные нетривиальные леммы о знаменателях bessel_term при β=1 (denom_ineq_02/04/0_step, bessel_term_inv). Поставляет has_process_mass_gap для процессной ветви программы щели масс.
- **Counts.** Qed 44 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS.CauchyReal; ToS.SeriesConvergence; gauge.CharacterTransfer; gauge.ExactMassGap; gauge.SpectralGapCorrect; gauge.TransferMatrixProof; stdlib.Combinatorics
- **E/R/R.** _Elements:_ процесс gap : nat→Q (стадия M = конечная частичная сумма бесселевых характеров); члены bessel_term n m 1 и их целочисленные знаменатели bt_denom; конкретные значения 289/384, 7541/7680, 367489/368640. _Roles:_ has_process_mass_gap = роль-критерий (свойство процесса); ε = роль-пол; C·rᴹ = роль-скорость; монотонность = роль-направление; su2_gap_process β = носитель. _Rules:_ PMG1 ∀M ε≤gap_M; PMG2 \|gap_{M+1}−gap_M\|≤C·rᴹ; PMG3 gap_M≤gap_{M+1}; домин­ирование 2·BT(2,m)≤BT(0,m) и BT(0,Sm)≤(1/4)BT(0,m) через знаменательные неравенства. _P4:_ ЯДРО P4-формализации кластера: 'процесс ЕСТЬ физика'. Щель масс корректно определена на КАЖДОЙ конечной стадии M (Element-сторона: вычислима, рациональна), завершённый предел НЕ нужен; континуальная щель = role-limit, к которому процесс монотонно сходится со скоростью (1/4)ᴹ, но которого не обязан достигать.
- **Classical counterpart.** Зеркалит идею спектральной щели решёточной калибровочной теории и сходимости частичных сумм бесселевых характеров SU(2) к континуальному пределу. НОВО — формальный КРИТЕРИЙ 'процессной щели масс' (has_process_mass_gap: равномерная нижняя граница ∧ явная скорость Коши C·rᴹ ∧ монотонность) как свойство процесса nat→Q, и его машинная проверка для SU(2) при β=1 с ЯВНЫМИ константами C=2, r=1/4 — щель определена на каждой конечной стадии без завершённого предела (P4).
- **Tags.** gauge, mass-gap, process, P4, Cauchy-rate, bessel, SU2, exact-Q, synthesis
- **Notes.** Заголовок STATUS: ~45 Qed — фактически 44 Qed. 0 Admitted, 0 axioms. Самый содержательный из пяти файлов: собственные леммы домин­ирования знаменателей bessel_term, а не только exact-обёртки. Print Assumptions su2_has_process_mass_gap в конце.

**Lemmas (49):**

| name | kind | role |
|---|---|---|
| `Q_process` | Definition | тип процесса nat→Q |
| `has_process_mass_gap` | Definition | ★ критерий: ∃ε,C,r>0, r<1 с PMG1∧PMG2∧PMG3 |
| `pmg_gap_positive` | Lemma | из критерия — gap_M>0 для всех M |
| `pmg_monotone_le` | Lemma | из критерия — gap монотонен: M≤N ⟹ gap_M≤gap_N |
| `su2_gap_process` | Definition | SU(2)-процесс щели: M ↦ spectral_gap 1 β M |
| `su2_gap_at_0` | Lemma | su2_gap_process 1 0 == 289/384 |
| `Qpow_plus` | Lemma | Qpow q (a+b) == Qpow q a * Qpow q b |
| `Qpow_nonneg_half` | Lemma | 0 ≤ (1/2)^k |
| `Qpow_pos_half` | Lemma | 0 < (1/2)^k |
| `inject_Z_mult_Q` | Lemma | inject_Z (a*b) == inject_Z a * inject_Z b |
| `bessel_partial_step` | Lemma | рекуррентный шаг частичной суммы бесселя |
| `gap_bracket` | Definition | скобка приращения щели BT0 − 2·BT2 + BT4 на стадии m |
| `gap_step_eq` | Lemma | character_mass_gap β (SM) == ... β M + gap_bracket (SM) β |
| `Qpow_half_cancel` | Lemma | ★ (1/2)^k · 2^k == 1 (ключевое сокращение, индукция+nia) |
| `bt_denom` | Definition | целый знаменатель bessel_term: 2^(n+2m)·m!·(n+m)! |
| `pow2_pos` | Lemma | 0 < 2^k |
| `fact_nat_pos` | Lemma | 0 < fact n |
| `bt_denom_pos` | Lemma | 0 < bt_denom n m |
| `Qpow_compat` | Lemma | Qpow уважает Qeq |
| `Qdiv_1_2_eq` | Lemma | 1/2 == 1#2 |
| `Qdiv_mul_cancel` | Lemma | a/b·(c·b) == a·c при b≠0 |
| `bessel_term_inv` | Lemma | ★ bessel_term n m 1 · bt_denom == 1 (через Qpow_half_cancel) — даёт BT=1/D |
| `denom_ineq_02` | Lemma | 2·bt_denom 0 m ≤ bt_denom 2 m |
| `bessel_term_0_dominates_2` | Lemma | ★ 2·BT(2,m,1) ≤ BT(0,m,1) (домин­ирование через знаменатели) |
| `gap_bracket_nonneg` | Lemma | 0 ≤ gap_bracket m 1 (скобка приращения неотрицательна) |
| `char_gap_eq` | Lemma | character_mass_gap β M == matrix_mass_gap 1 β M |
| `char_gap_at_0_positive` | Lemma | 0 < character_mass_gap 1 0 |
| `char_gap_step_nonneg` | Lemma | character_mass_gap 1 M ≤ ... 1 (SM) |
| `char_gap_positive` | Lemma | 0 < character_mass_gap 1 M для всех M (индукция) |
| `spectral_gap_eq_char_gap` | Lemma | spectral_gap 1 1 M == character_mass_gap 1 M |
| `pmg3_beta_1` | Theorem | PMG3: su2_gap_process 1 монотонен |
| `pmg1_beta_1` | Theorem | PMG1: 289/384 ≤ su2_gap_process 1 M для всех M |
| `fact_Q_ge_1` | Lemma | 1 ≤ fact_Q n |
| `Qpow_le_1` | Lemma | 0≤q≤1 ⟹ Qpow q k ≤ 1 |
| `denom_ineq_04` | Lemma | bt_denom 0 m ≤ bt_denom 4 m |
| `bessel_term_4_le_0` | Lemma | BT(4,m,1) ≤ BT(0,m,1) |
| `gap_step_le_2bt0` | Lemma | gap_bracket m 1 ≤ 2·BT(0,m,1) |
| `denom_ineq_0_step` | Lemma | 4·bt_denom 0 m ≤ bt_denom 0 (Sm) |
| `bt0_geometric` | Lemma | ★ BT(0,Sm,1) ≤ (1/4)·BT(0,m,1) (геометрическое убывание) |
| `bt0_le_pow` | Lemma | BT(0,Sm,1) ≤ (1/4)^(Sm) (индукция через bt0_geometric) |
| `Qpow_quarter_dec` | Lemma | (1/4)^(SM) ≤ (1/4)^M |
| `pmg2_beta_1` | Theorem | ★ PMG2: \|приращение\| ≤ 2·(1/4)^M (явная скорость Коши) |
| `su2_has_process_mass_gap` | Theorem | ★★ SU(2) при β=1 имеет процессную щель масс (ε=289/384, C=2, r=1/4) |
| `su2_gap_at_1` | Lemma | su2_gap_process 1 1 == 7541/7680 |
| `su2_gap_at_2` | Lemma | su2_gap_process 1 2 == 367489/368640 |
| `su2_gap_increasing_0_1` | Lemma | gap 0 < gap 1 (конкретный рост) |
| `su2_gap_increasing_1_2` | Lemma | gap 1 < gap 2 |
| `pmg_spectral_all_beta` | Theorem | для всех рациональных β>0 щель на стадии 0 положительна (из SpectralGapCorrect) |
| `process_mass_gap_summary` | Theorem | сводка: SU(2) β=1 имеет процессную щель ∧ PMG1 ∧ PMG3 ∧ значения |

**Key lemmas (deep):**

- **`su2_has_process_mass_gap`** - Флагман файла: единственная теорема программы щели масс, дающая ПОЛНЫЙ процессный критерий с явными константами (ε=289/384, C=2, r=1/4) и связывающая равномерную нижнюю границу, монотонность и геометрическую скорость Коши воедино. В отличие от exact-агрегаторов соседних файлов, она опирается на собственный нетривиальный анализ (bt0_geometric ⟹ скорость, bessel_term_0_dominates_2 ⟹ неотрицательность приращения). Это и есть P4-смысл кластера: 'процесс ЕСТЬ физика', щель определена на каждой стадии, предел не требуется. _(process, mass-gap, P4, Cauchy-rate, flagship-of-file)_
- **`bessel_term_inv`** - Технический стержень всех домин­ирований: показывает, что bessel_term n m 1 при β=1 равен в точности 1/bt_denom, где bt_denom = 2^(n+2m)·m!·(n+m)! — целое. Опирается на Qpow_half_cancel ((1/2)^k·2^k=1). Превращает все неравенства между бесселевыми членами в ЦЕЛОЧИСЛЕННЫЕ неравенства знаменателей (denom_ineq_02/04/0_step), которые закрываются nia/lia. Аккуратная редукция аналитического факта к арифметике над Z — характерный для gauge приём 'точное Q вместо оценок'. _(bessel, denominator, exact-Q, reduction-to-Z)_
- **`bt0_geometric`** - Источник скорости 1/4: BT(0,Sm,1) ≤ (1/4)·BT(0,m,1), доказан через denom_ineq_0_step (4·bt_denom 0 m ≤ bt_denom 0 (Sm)). Именно это геометрическое убывание ведущего бесселева члена даёт явную константу r=1/4 в PMG2 и тем самым делает процесс Коши с КОНКРЕТНОЙ скоростью, а не абстрактно сходящимся. Содержательный шаг, не обёртка. _(geometric-decay, rate, bessel, induction)_

**Uniqueness - score 4 (synthesis+observation).** Формальный P4-критерий 'процессной щели масс' (равномерная граница ∧ явная скорость Коши C·rᴹ ∧ монотонность) как свойство процесса nat→Q, с машинной проверкой для SU(2) β=1 и ЯВНЫМИ константами C=2, r=1/4 — несущая ontology-ветвь 'щель = свойство конечного процесса, не завершённого предела'.
> _Caveat:_ НЕ доказательство Clay: щель = спектральная щель решётки SU(2) на конечных бесселевых частичных суммах при β=1; континуальный предел открыт (процесс к нему лишь сходится). Сам критерий — переформулировка стандартной (Cauchy-сходимость + положительность); все значения (289/384 и т.д.) — фиксированная β=1 решётка. Заголовок ~45 Qed — фактически 44.

---

## #489 - `src/gauge/ProofClosure.v` - score 3 (new-framing)

**Замыкание доказательства: 'финальный' капстоун Янга–Миллса (9 пробелов) с честной оговоркой Reading-1/Reading-2**

- **Topic.** Закрывает все 9 'пробелов доказательства' решёточной программы щели масс (диагональность, бессель, OS1–OS5, реконструкция Вайтмана, положительность щели) единым капстоуном yang_mills_mass_gap_FINAL с полными термами, и явно оговаривает, что континуальная Clay-формулировка (Reading 1) НЕ доказана.
- **Role.** Вершина-агрегатор всей решёточной ветви: импортирует CharacterTransfer, ExactMassGap, GapRatio, ReflectionPositivity, TransferMatrixProof, ReflectionPositiveProof, ClusterProof, CorrelationProof, CovarianceProof, HilbertConstruction, PhaseB_Synthesis (#487). Каждая теорема — exact чужой леммы; ничего вниз по графу не переиспользует (терминальный капстоун).
- **Counts.** Qed 18 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS.CauchyReal; ToS.SeriesConvergence; gauge.CharacterTransfer; gauge.ExactMassGap; gauge.GapRatio; gauge.ReflectionPositivity; gauge.TransferMatrixProof; gauge.ReflectionPositiveProof; gauge.ClusterProof; gauge.CorrelationProof; gauge.CovarianceProof; gauge.HilbertConstruction; gauge.PhaseB_Synthesis
- **E/R/R.** _Elements:_ девять конкретных конъюнктов-фактов (диагональность T, бессель-собств.знач., OS1–OS5, Вайтман-объект, щель 289/384); конкретные WightmanQFT/LatticeQFT-обитатели wqft_at_1, lqft_beta_1. _Roles:_ каждый OS-аксиома = роль-свойство реконструкции; 'девять пробелов' = девять ролей-обязательств; FINAL-капстоун = роль-конъюнкция всех; Reading 1 vs Reading 2 = две роли-прочтения утверждения. _Rules:_ gap_i_PROVED замыкаются exact (transfer_mat_*, os1/os2/os3-леммы, reflection_positivity_from_matrix, cluster_*, os_to_wightman_at_1, lqft_strict_gap_1); honest-note: Reading 2 (решётка) ⊢, Reading 1 (континуум) ⊬. _P4:_ Element-сторона (конечная решётка, β=1, J∈{0,1}) полностью доказана; переход Reading-2 → Reading-1 ЯВНО назван границей финитизации (континуальный предел открыт). Это образцовая P4-честность: завершённый объект-стена (континуальная КТП) не выдаётся за достигнутый.
- **Classical counterpart.** Зеркалит программу Остервальдера–Шрадера: пять OS-аксиом (OS1 аналитичность, OS2 регулярность, OS3 ковариантность, OS4 положительность отражения, OS5 кластер) + реконструкция Вайтмана из RP + спектральная щель. НОВО — НИЧЕГО математически (всё импортировано, каждый конъюнкт = exact); ценность чисто организационная: одна теорема yang_mills_mass_gap_FINAL, закрывающая все 'девять пробелов' полными термами, ПЛЮС редкая для проекта явная внутрифайловая honest-note (Reading 1 Clay-континуум НЕ доказан, Reading 2 решётка доказан, зазор = граница финитизации).
- **Tags.** gauge, mass-gap, OS-axioms, wightman, capstone, SU2, honest-note, over-branding-mitigated
- **Notes.** Заголовок STATUS: ~25 Qed — фактически 18 Qed. 0 Admitted (совпадение 'No Admitted' в комментарии — не команда), 0 axioms. ВАЖНО: содержит явную HONEST NOTE (строки 25–30, кросс-ссылка foundation/MillenniumHonesty.v) — Reading 1 (Clay-континуум) НЕ доказан, Reading 2 (решётка) доказан. Print Assumptions yang_mills_mass_gap_FINAL и all_nine_gaps_closed в конце.

**Lemmas (18):**

| name | kind | role |
|---|---|---|
| `gap1_diagonal_PROVED` | Theorem | пробел 1: T диагональна (i≠j ⟹ entry==0) |
| `gap2_bessel_PROVED` | Theorem | пробел 2: собственные значения = transfer_eigenvalue (бессель) |
| `gap3_os1_PROVED` | Theorem | пробел 3 / OS1: корреляции аналитичны (отношение num/denom, denom>0) |
| `gap4_os2_PROVED` | Theorem | пробел 4 / OS2: корреляции ограничены (\|·\|≤1) |
| `gap5_os3_PROVED` | Theorem | пробел 5 / OS3: корреляции зависят только от разделения (== r^t_sep) |
| `gap6_os4_PROVED` | Theorem | пробел 6 / OS4: положительность отражения (0≤β≤2 ⟹ RP≥0) |
| `gap7_os5_PROVED` | Theorem | пробел 7 / OS5: кластер (∀ε ∃t0, corr<ε) |
| `gap8_wightman_PROVED` | Theorem | пробел 8: ∃ WightmanQFT с щелью >0 (os_to_wightman_at_1) |
| `gap9_mass_gap_PROVED` | Theorem | пробел 9: 0 < matrix_mass_gap 1 1 0 |
| `yang_mills_mass_gap_FINAL` | Theorem | ★★ капстоун: все 9 конъюнктов вместе (полные термы, без True) |
| `mass_gap_value_beta_1` | Theorem | matrix_mass_gap 1 1 0 == 289/384 |
| `mass_gap_value_beta_2` | Theorem | matrix_mass_gap 1 2 0 == 1/24 |
| `mass_gap_positive_beta_1` | Theorem | 0 < matrix_mass_gap 1 1 0 |
| `mass_gap_positive_beta_2` | Theorem | 0 < matrix_mass_gap 1 2 0 |
| `yang_mills_one_line` | Theorem | однострочник: ∃gap, gap==289/384 ∧ >0 |
| `yang_mills_lattice_exists` | Theorem | ∃ LatticeQFT со щелью >0 (lqft_beta_1) |
| `wightman_exists_with_gap` | Theorem | ∃ WightmanQFT, wqft_gap == matrix_energy_gap 1 1 0 ∧ >0 |
| `all_nine_gaps_closed` | Theorem | ★ вариант капстоуна: все 9 пробелов в одной конъюнкции |

**Key lemmas (deep):**

- **`yang_mills_mass_gap_FINAL`** - Терминальный капстоун всей решёточной ветви: 11-членная конъюнкция (диагональность, бессель, значение и положительность щели, OS1–OS5, Вайтман-существование, энергощель), каждый конъюнкт — exact чужой леммы. Содержания НОЛЬ; функция — единая точка 'всё закрыто полными термами, без True/Admitted'. КРИТИЧНО по бренду: имена 'FINAL' и 'THE YANG-MILLS MASS GAP THEOREM' аспирационны — это конечнорешёточный SU(2)-факт при β=1, J∈{0,1}, НЕ Clay. НО этот файл — образец честности: содержит явную honest-note (строки 25–30), различающую Reading 2 (решётка, доказано) и Reading 1 (континуум 4D Wightman, открыто), и называющую зазор границей финитизации. _(capstone, terminal, OS-axioms, honest-note, finite-lattice)_
- **`all_nine_gaps_closed`** - Дублёр-капстоун (девять, а не одиннадцать конъюнктов), отличающийся лишь формой: 'девять пробертов реконструкции OS закрыты'. Иллюстрирует, что файл = многократная переупаковка одного набора импортированных фактов (FINAL, all_nine_gaps_closed, yang_mills_one_line, *_exists — все из тех же лемм). Полезно как читаемый указатель структуры доказательства, но не добавляет математики. _(capstone-variant, repackaging, exposition)_

**Uniqueness - score 3 (new-framing).** Единая 'финальная' точка, замыкающая все девять OS-пробелов решёточной программы щели масс полными термами (без True/Admitted), С образцовой внутрифайловой honest-note, явно различающей доказанную решётку (Reading 2) и открытый континуум Clay (Reading 1).
> _Caveat:_ 0 нового содержания: каждый конъюнкт — exact чужой леммы, файл = многократная переупаковка. НЕ доказательство Clay (honest-note это прямо признаёт): SU(2), β=1, J∈{0,1}, 'щель 289/384' = спектральная щель решётки. Имена FINAL/PROVED аспирационны, но честность спасает оговорка. Заголовок ~25 Qed — фактически 18.

---

## #490 - `src/gauge/ReflectionPositiveProof.v` - score 3 (new-framing)

**Положительность отражения из собственных значений трансфер-матрицы: RP≥0, положительная определённость, энергощель E₁>0**

- **Topic.** Строит RP-скалярное произведение rp_inner_matrix как взвешенную сумму квадратов с диагональными бесселевыми весами, доказывает RP≥0 (0≤β≤2), положительную определённость при β=1,2, и энергощель E₁−E₀>0 в гамильтоновом языке — полными термами.
- **Role.** Поставщик RP- и энергощель-лемм для агрегаторов. Импортирует CharacterTransfer, ExactMassGap, GapRatio, ReflectionPositivity, TransferMatrixProof (weighted_sum_sq, transfer_eigenvalue, physical_energy, energy_gap, t0/t1-позитивность). Определения rp_inner_matrix, matrix_energy, matrix_energy_gap и леммы reflection_positivity_from_matrix, matrix_energy_gap_positive_* широко переиспользуются: PhaseB_Synthesis (#487), ProofClosure (#489).
- **Counts.** Qed 29 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS.CauchyReal; ToS.SeriesConvergence; gauge.CharacterTransfer; gauge.ExactMassGap; gauge.GapRatio; gauge.ReflectionPositivity; gauge.TransferMatrixProof
- **E/R/R.** _Elements:_ тест-функция f : nat→Q; диагональные собственные значения t_j = dm_entry (transfer_mat J β M) j; уровни энергии E_j = 1 − t_j/t₀; конкретные β=1,2, J∈{0,1}. _Roles:_ rp_inner_matrix = роль-форма (⟨f,Θf⟩); собственное значение t_j>0 = роль-вес; matrix_energy = роль-уровень; matrix_energy_gap = роль-щель в гамильтоновом языке; положительная определённость = роль-критерий невырожденности. _Rules:_ RP = weighted_sum_sq с весами t_j; t_j>0 ⟹ сумма ≥0 (weighted_sum_sq_nonneg); f²·t==0 ∧ t>0 ⟹ f==0; E₁ = physical_energy 1 > 0 = E₀; energy_gap = E₁−E₀ >0. _P4:_ RP и энергощель определены и доказаны на КОНЕЧНОМ базисе (J∈{0,1}) полными рациональными термами (Element-сторона) — без завершённого гильбертова пространства и без меры; гильбертова реконструкция (полное пространство из RP) = role-limit, здесь лишь даётся 'язык' (matrix_energy), а не построение бесконечномерного объекта.
- **Classical counterpart.** Зеркалит положительность отражения Остервальдера–Шрадера (OS4): ⟨f,Θf⟩ = Σ_j \|f_j\|²·t_j ≥ 0 при t_j>0, и щель масс в гамильтоновой формулировке E₁>E₀=0. НОВО — не результат (классика), а явная конструктивная реализация над Q: RP сведена к взвешенной сумме квадратов с диагональными собственными значениями трансфер-матрицы, плюс положительная определённость при β=1,2 (норма=0 ⟹ f=0 покомпонентно) — всё полными термами, без меры/гильбертова анализа.
- **Tags.** gauge, reflection-positivity, OS4, energy-gap, inner-product, SU2, exact-Q, new-framing
- **Notes.** Заголовок STATUS: ~35 Qed — фактически 29 Qed. 0 Admitted, 0 axioms. reflection_positivity_from_matrix и matrix_energy_gap_positive_1 — экспортные имена, переиспользуемые PhaseB_Synthesis (#487) и ProofClosure (#489). RP доказана только для J≤1 (двумерный базис); positive-definiteness — только β∈{1,2}. Print Assumptions rp_proof_summary в конце.

**Lemmas (33):**

| name | kind | role |
|---|---|---|
| `rp_inner_matrix` | Definition | ★ RP-форма = weighted_sum_sq f (диагональные веса трансфер-матрицы) J |
| `rp_inner_matrix_eq` | Lemma | форма == взвешенная сумма с весами transfer_eigenvalue (дефиниционно) |
| `rp_matrix_nonneg` | Theorem | J≤1, 0≤β≤2 ⟹ RP≥0 (через позитивность t0/t1) |
| `reflection_positivity_from_matrix` | Theorem | ★ OS4: 0≤β≤2 ⟹ 0 ≤ rp_inner_matrix 1 β 0 f (несущая, широко переиспользуется) |
| `rp_matrix_beta_1` | Theorem | RP≥0 при β=1 |
| `rp_matrix_beta_2` | Theorem | RP≥0 при β=2 |
| `rp_matrix_general` | Theorem | RP≥0 для любого J при всех неотриц. собственных значениях |
| `Qsquare_pos` | Lemma | x≠0 ⟹ 0 < x·x |
| `sq_times_pos_zero` | Lemma | f²·t==0 ∧ t>0 ⟹ f==0 |
| `rp_pd_at_0` | Theorem | положит. определённость при J=0: RP==0 ⟹ f0==0 |
| `rp_pd_beta_1_j0` | Theorem | то же при β=1, J=0 |
| `nonneg_sum_zero` | Lemma | a,b≥0 ∧ a+b==0 ⟹ a==0 ∧ b==0 |
| `rp_pd_at_1` | Theorem | ★ положит. определённость при J=1: RP==0 ⟹ f0==0 ∧ f1==0 |
| `rp_inner_matrix_unfold` | Lemma | разворот rp_inner_matrix к весам transfer_eigenvalue |
| `rp_pd_beta_1` | Theorem | положит. определённость при β=1, J=1 |
| `rp_pd_beta_2` | Theorem | положит. определённость при β=2, J=1 |
| `rp_norm_sq` | Definition | норма ‖f‖² := rp_inner_matrix |
| `rp_norm_nonneg` | Theorem | ‖f‖² ≥ 0 (0≤β≤2) |
| `rp_norm_zero_implies_f_zero` | Theorem | ‖f‖²==0 ⟹ f0==0 ∧ f1==0 (β=1) |
| `rp_norm_zero_fn` | Theorem | норма нулевой функции == 0 |
| `rp_inner_product_properties` | Theorem | сводка: неотриц. ∧ положит. определ. ∧ нуль-функция (свойства скал. произв.) |
| `matrix_energy` | Definition | уровень энергии E_j = 1 − t_j/t₀ (1-й порядок −log) |
| `matrix_energy_eq_physical` | Theorem | matrix_energy == physical_energy |
| `matrix_ground_energy_zero` | Theorem | t₀>0 ⟹ E₀==0 |
| `matrix_ground_energy_1` | Theorem | E₀==0 при β=1 |
| `matrix_excited_positive_1` | Theorem | E₁>0 при β=1 |
| `matrix_excited_positive_2` | Theorem | E₁>0 при β=2 |
| `matrix_energy_gap` | Definition | энергощель = E₁ − E₀ |
| `matrix_energy_gap_eq` | Theorem | matrix_energy_gap == energy_gap |
| `matrix_energy_gap_positive_1` | Theorem | ★ энергощель >0 при β=1 (переиспользуется агрегаторами) |
| `matrix_energy_gap_positive_2` | Theorem | энергощель >0 при β=2 |
| `hilbert_mass_gap` | Theorem | ★ щель масс в гильбертовом языке: E₀==0 ∧ E₁>0 ∧ энергощель >0 |
| `rp_proof_summary` | Theorem | сводка: RP ∧ положит. определ. ∧ энергощель >0 |

**Key lemmas (deep):**

- **`reflection_positivity_from_matrix`** - Несущая лемма файла и одна из самых переиспользуемых во всей ветви (её зовут PhaseB_Synthesis и ProofClosure как OS4): при 0≤β≤2 RP-форма ⟨f,Θf⟩=Σ_j\|f_j\|²·t_j неотрицательна, потому что диагональные веса t_j>0 (t0/t1_M0_nonneg) и weighted_sum_sq неотрицательна по таким весам. Конструктивная реализация OS-положительности отражения чисто над Q, без меры и гильбертова пространства — но ТОЛЬКО для J≤1 (двумерный базис j∈{0,1}, j≥2 закрывается lia). Это и есть честная граница: 'RP' здесь — позитивность 2×2 диагональной формы, а не бесконечномерная OS4. _(reflection-positivity, OS4, weighted-sum-sq, reuse, finite-basis)_
- **`rp_pd_at_1`** - Содержательнее, чем простая неотрицательность: положительная определённость при J=1 — если RP-норма f зануляется, то f₀=f₁=0 покомпонентно. Доказана через nonneg_sum_zero (сумма двух неотриц. слагаемых =0 ⟹ оба =0) и sq_times_pos_zero (f²·t=0, t>0 ⟹ f=0). Даёт, что RP-форма задаёт настоящее (невырожденное) скалярное произведение на конечном базисе — шаг к 'физическому' гильбертову языку. Ограничено J=1 (2 компоненты) и конкретными β=1,2 через позитивность t0,t1. _(positive-definite, inner-product, non-degeneracy, finite-basis)_
- **`hilbert_mass_gap`** - Перевод щели масс на гамильтонов язык: E₀=0 (основной уровень), E₁>0 (первое возбуждение), энергощель=E₁−E₀>0 — всё полными термами через matrix_energy_eq_physical и energy_gap_positive_*. ВНИМАНИЕ к бренду: 'mass gap in Hilbert space language' — это E₁>0 на КОНЕЧНОМ 2-уровневом спектре при β∈{1,2}, а не спектр самосопряжённого оператора в бесконечномерном пространстве; энергия задана линейным приближением E=1−t/t₀ (1-й порядок −log), а не точным −log(t/t₀). _(energy-gap, hilbert-language, first-order-approx, over-branding-local)_

**Uniqueness - score 3 (new-framing).** Конструктивная реализация над Q положительности отражения (OS4) и энергощели: RP сведена к взвешенной сумме квадратов с диагональными бесселевыми весами, доказаны RP≥0, положительная определённость (норма=0 ⟹ f=0) и E₁>E₀=0 — полными термами, без меры и бесконечномерного гильбертова анализа.
> _Caveat:_ НЕ доказательство Clay и не полная OS4: 'RP' = позитивность 2×2 диагональной формы (J≤1, базис j∈{0,1}), β только {1,2} для опред­ённости; энергия = линейное приближение E=1−t/t₀, не точный −log; гильбертово пространство не строится (даётся лишь 'язык'). Классика: OS4 и E₁>E₀ — стандарт. Заголовок ~35 Qed — фактически 29.

---

## #491 - `src/gauge/ReflectionPositivity.v` - score 2 (methods)

**Reflection positivity on a j<=1 character truncation: t_j>0 => <f,Theta f> >= 0**

- **Topic.** Defines a weighted sum-of-squares <f,Theta f> = sum_j f_j^2 t_j, proves it nonneg when the transfer eigenvalues t_j are nonneg, and packages OS4 (RP) + OS5 (cluster = gap>0) on the truncated (j<=1) lattice at concrete beta, plus a first-order 'physical energy' E_j = 1 - t_j/t_0 with positive energy gap.
- **Role.** Bridge endpoint of the gauge mass-gap chain: imports SU2Characters, CharacterTransfer, ExactMassGap, ClebschGordan, CombinedTransfer3D, GapRatio. Consumes the transfer_eigenvalue/gap_ratio/t0_M0/t1_M0 facts and reframes them as OS-axiom satisfaction. Leaf file (CHECK/Print Assumptions at end); not imported by the RG files.
- **Counts.** Qed 23 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: CauchyReal SeriesConvergence; ToS: stdlib.Combinatorics; gauge: SU2Characters CharacterTransfer ExactMassGap ClebschGordan CombinedTransfer3D GapRatio
- **E/R/R.** _Elements:_ конкретные собственные значения трансфер-матрицы t_j = transfer_eigenvalue j beta 0; коэффициенты f_j; усечение j<=1. _Roles:_ Theta = отражение; <f,Theta f> = weighted_sum_sq — роль скалярного произведения; OS4/OS5 = роли-аксиомы (RP, кластер); physical_energy = роль гамильтониана. _Rules:_ RP <-> T положителен <-> все t_j >= 0; знак суммы квадратов с весами наследует знак весов; кластер <-> gap_M0 beta > 0; E_0 = 0, gap = 1 - gap_ratio. _P4:_ позитивность проверяется как КОНЕЧНЫЙ факт на усечении j<=1 при beta in {1,2} (lra), а не как теорема об операторе на полном гильбертовом пространстве; 'continuum RP' = замыкание t^n>0 под степенями (процесс), завершённый OS-предел не строится — Element-сторона (конечная проверка) против role-limit (полная OS-реконструкция, не выполнена).
- **Classical counterpart.** Osterwalder-Schrader reconstruction (RP/OS-axioms => physical Hilbert space) and the fact that a positive transfer matrix yields reflection positivity are classical constructive QFT. NEW here is ONLY: nothing — the OS axioms are restated and RP is reduced to a finite (j<=1) truncation of the SU(2)/U(1) character transfer matrix where all eigenvalues are checked positive by lra at beta=1,2; the 'continuum' RP is the trivial t^n>0 closure-under-powers, NOT an OS reconstruction theorem.
- **Tags.** gauge, reflection-positivity, osterwalder-schrader, transfer-matrix, mass-gap, finite-lattice, truncation, P4
- **Notes.** STATUS header says '~40 Qed'; actual Qed = 23 (drift, approximate header). 0 own axioms (Print Assumptions at end). 'continuum RP' is closure-under-powers t_j^n>0, explicitly NOT an OS continuum reconstruction; 'OS5 = cluster' is defined as gap>0 (renaming, not a derivation of correlation decay).

**Lemmas (34):**

| name | kind | role |
|---|---|---|
| `weighted_sum_sq` | Fixpoint | sum_{j<=n} f_j^2 * t_j — решёточная форма <f,Theta f> |
| `Qsquare_nonneg` | Lemma | 0 <= x*x в Q (через nia) |
| `weighted_sum_sq_nonneg` | Lemma | веса t_j >= 0 => вся взвешенная сумма квадратов >= 0 (индукция) |
| `rp_nonneg` | Theorem | переименование weighted_sum_sq_nonneg как RP-неотрицательности |
| `rp_holds_beta_1` | Theorem | RP на j<=1 при beta=1 (t0,t1 >= 0 через t0/t1_M0_nonneg) |
| `rp_holds_beta_2` | Theorem | то же при beta=2 |
| `sq_times_pos` | Lemma | 0<=a*a, 0<b => 0 <= a*a*b (вспом.) |
| `weighted_sum_0` | Lemma | база: weighted_sum_sq f t 0 == f_0^2 * t_0 |
| `rp_positive_definite_0` | Theorem | t_0>0 и сумма=0 => f_0=0 (положительная определённость на J=0) |
| `os4_lattice` | Definition | OS4: forall f, RP-сумма на j<=1 неотрицательна (предикат от beta) |
| `os5_cluster` | Definition | OS5: 0 < gap_M0 beta (кластерное свойство = щель) |
| `os4_structural` | Theorem | ★ OS4 для всех 0<=beta<=2 на усечении j<=1 |
| `os5_at_beta_1` | Theorem | OS5 при beta=1 (через gap_at_beta_1_positive) |
| `os5_at_beta_2` | Theorem | OS5 при beta=2 |
| `correlation_bound` | Definition | r^t_step — экспоненциальная оценка коррелятора |
| `correlation_at_0` | Lemma | r^0 == 1 |
| `correlation_at_1` | Lemma | r^1 == r |
| `correlation_decreasing` | Lemma | 0<=r<=1 => r^(t+1) <= r^t (монотонный спад) |
| `correlation_nonneg` | Lemma | 0<=r => 0 <= r^t |
| `correlation_bounded` | Lemma | 0<=r<=1 => r^t <= 1 |
| `rg_preserves_t0_pos` | Lemma | 0 < (t0_M0 1)^n — позитивность t0 под степенями RG |
| `rg_preserves_t1_pos` | Lemma | 0 < (t1_M0 1)^n |
| `rp_at_rg_step` | Theorem | на каждом RG-шаге оба собственных значения > 0 |
| `rp_preserved_under_rg` | Theorem | то же для шага S n |
| `rp_in_continuum` | Theorem | RP 'в континууме' = forall n, t_j^n > 0 (замыкание под степенями, НЕ OS-предел) |
| `physical_energy` | Definition | E_j = 1 - t_j/t_0 (первый порядок -log(t_j/t_0)) |
| `ground_energy_zero` | Theorem | E_0 = 1 - t_0/t_0 = 0 |
| `first_excited_positive_1` | Theorem | 0 < E_1 при beta=1 (= 1 - gap_ratio 1) |
| `first_excited_positive_2` | Theorem | 0 < E_1 при beta=2 |
| `energy_gap` | Definition | E_1 - E_0 |
| `energy_gap_formula` | Theorem | energy_gap == 1 - gap_ratio beta |
| `energy_gap_positive_1` | Theorem | 0 < energy_gap 1 |
| `energy_gap_positive_2` | Theorem | 0 < energy_gap 2 |
| `reflection_positivity_summary` | Theorem | ★ сводка: OS4 (0<=beta<=2) + OS5(1,2) + RP под RG + положительная щель |

**Key lemmas (deep):**

- **`os4_structural`** - Несущая теорема файла: reflection positivity сводится к 'веса неотрицательны => сумма квадратов с весами неотрицательна', где веса = transfer_eigenvalue j beta 0 на УСЕЧЕНИИ j<=1, а их неотрицательность для 0<=beta<=2 берётся из t0_M0_nonneg/t1_M0_nonneg. Это честная, но узкая RP: только два собственных значения, только полоса beta<=2. Классическая RP — свойство положительного оператора на полном гильбертовом пространстве; здесь это конечная проверка знака на 2x2-усечении. _(reflection-positivity, OS-axiom, truncation, finite-lattice)_
- **`reflection_positivity_summary`** - Капстоун-сводка, собирающая OS4+OS5+RP-под-RG+щель в одну конъюнкцию. Важно для честности: 'OS5 = cluster' определён как gap_M0 beta > 0 (переобозначение щели как кластерного свойства, а не вывод экспоненциального распада корреляций из спектра), а 'RP в континууме' = forall n t_j^n>0 (степени положительны), что НЕ есть Остервальдер-Шрадер реконструкция континуальной теории. Ценность — аккуратная упаковка ранее доказанных решёточных фактов под именами OS-аксиом. _(summary, OS-reconstruction, honest-scope)_
- **`energy_gap_formula`** - energy_gap == 1 - gap_ratio beta связывает первопорядковую 'физическую энергию' E_j=1-t_j/t_0 с отношением щели gap_ratio. Это линеаризация -log(t_1/t_0) (первый член ряда), а не сам логарифм — то есть приближённая энергия, честно помеченная как 'first-order approx of -log'. Положительность щели при beta=1,2 наследуется из gap_ratio<1. _(mass-gap, linearized-log, energy)_

**Uniqueness - score 2 (methods).** Необычная финитная упаковка: reflection positivity и OS4/OS5 переформулированы как неотрицательность взвешенной суммы квадратов на j<=1-усечении характерной трансфер-матрицы, с машинной проверкой знака собственных значений при beta=1,2.
> _Caveat:_ Всё классично (Остервальдер-Шрадер, положительный трансфер => RP). Узко: только j<=1, beta<=2, конкретные значения; 'OS5=cluster' — переобозначение щели, не вывод распада корреляций; 'RP в континууме' = t^n>0, НЕ OS-реконструкция континуума. Заголовок '~40 Qed' завышен: фактически 23.

---

## #492 - `src/gauge/RGContraction.v` - score 1 (exposition)

**Lattice artifacts shrink under a posited linear RG schedule beta_n = beta0 + n*b0*beta0^2**

- **Topic.** On the assumed one-loop schedule beta_after_n_steps beta0 n = beta0 + n*b0_approx*beta0^2, proves beta is positive/increasing/unbounded-structurally and that artifact_at_step = lattice_artifact_size(beta_n) and anisotropy decrease monotonically while staying positive — packaged as 'double contraction' and 'process converges'.
- **Role.** Mid-chain RG file. Imports CharacterTransfer, ExactMassGap, GapRatio, LatticeRG, IrrelevantOperators (sources of beta_after_n_steps, b0_approx, lattice_artifact_size, anisotropy, the *_decreasing/*_positive monotonicity lemmas). Pure consequence-assembly: nearly every proof is one `exact` of an imported lemma. Leaf-ish; not imported by the other four files.
- **Counts.** Qed 24 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: CauchyReal SeriesConvergence; gauge: CharacterTransfer ExactMassGap GapRatio LatticeRG IrrelevantOperators
- **E/R/R.** _Elements:_ артефакт на шаге n = lattice_artifact_size(beta_n); beta_n = beta0 + n*b0*beta0^2; анизотропия на шаге n. _Roles:_ RG-шаг = блокировка (beta растёт, a удваивается); 'double contraction' = двойная роль сжатия (r->r^2, A->A*beta/beta'); процесс {(r_n,A_n,m_n)} = роль сходящейся последовательности. _Rules:_ beta монотонно растёт по n (линейный график); 1/beta_n монотонно убывает => артефакт убывает; артефакт > 0 всегда; ограничен начальным значением. _P4:_ сходимость дана как ПАРА {монотонно убывает, ограничен снизу 0}, а не как достигнутый предел — это P4-процесс (потенциальная, не актуальная бесконечность); 'сходится к теории с полным SO(4)' — прозаическое утверждение, формально доказано лишь монотонность+ограниченность, сам предел/SO(4) не построены.
- **Classical counterpart.** Asymptotic freedom (beta increases under blocking, lattice spacing -> 0) and the monotone-bounded convergence theorem are classical. NEW here is ONLY: nothing new mathematically — under the POSITED linear schedule beta_n = beta0 + n*b0*beta0^2 the lattice 'artifact' 1/(24 beta) is shown strictly decreasing and bounded below by 0; 'process converges' is the monotone+bounded PAIR, not an actual limit, and 'full SO(4)' is asserted in prose only.
- **Tags.** gauge, RG, renormalization, lattice-artifacts, asymptotic-freedom, monotone-convergence, overbranding, P4
- **Notes.** STATUS header '~35 Qed'; actual = 24 (drift). 0 own axioms. Over-branding to flag: process_converges asserts convergence to a 'theory with full SO(4)' but only proves monotone-decreasing + bounded-below + beta-increasing (no limit, no SO(4)); beta_unbounded_structural proves only beta0<beta_{n+1}, not genuine unboundedness; gap_ratio_persists's body is just beta_n>0. The beta_n schedule is posited (one-loop linearization), not derived.

**Lemmas (26):**

| name | kind | role |
|---|---|---|
| `beta_after_n_positive` | Theorem | beta0>0 => beta_n > 0 |
| `beta_growth` | Theorem | beta0 <= beta_n (не убывает) |
| `beta_monotone` | Theorem | beta_n < beta_{n+1} (строго растёт) |
| `beta_grows_linearly` | Theorem | beta_n == beta0 + n*b0*beta0^2 (раскрытие графика, ring) |
| `beta_step_1_exceeds` | Theorem | beta0 < beta_1 |
| `beta_unbounded_structural` | Theorem | forall n, beta0 < beta_{n+1} (структурная неограниченность; НЕ настоящая беспредельность) |
| `artifact_at_step` | Definition | lattice_artifact_size(beta_n) |
| `artifact_at_step_0` | Lemma | артефакт на шаге 0 == lattice_artifact_size beta0 |
| `artifact_at_step_positive` | Lemma | 0 < артефакт_n |
| `artifact_decreasing_steps` | Theorem | артефакт_{n+1} < артефакт_n |
| `anisotropy_at_step` | Definition | anisotropy(beta_n) |
| `anisotropy_at_step_0` | Lemma | анизотропия на шаге 0 == anisotropy beta0 |
| `anisotropy_at_step_positive` | Lemma | 0 < анизотропия_n |
| `anisotropy_decreasing_steps` | Theorem | анизотропия_{n+1} < анизотропия_n |
| `artifact_bounded_by_initial` | Theorem | артефакт_n <= артефакт_0 (индукция по монотонности) |
| `double_contraction_step` | Theorem | один шаг: артефакт сжимается И beta растёт |
| `artifact_strictly_smaller` | Theorem | n>=1 => артефакт_n < артефакт_0 |
| `artifact_step_1_beta_1` | Lemma | конкретно: артефакт_1 < артефакт_0 при beta0=1 |
| `gap_positive_all_steps` | Theorem | 0 < beta_n на всех шагах (переобозначение beta_after_n_positive) |
| `gap_ratio_persists` | Theorem | то же, имя про 'r^{2^n}<1' но утверждение = beta_n>0 |
| `double_contraction` | Theorem | ★ артефакт<=нач. И beta>=нач. И beta_n>0 (тройная сводка) |
| `artifact_sequence_decreasing` | Theorem | последовательность артефактов строго убывает |
| `artifact_sequence_bounded` | Theorem | ограничена снизу 0 |
| `artifact_process_converges` | Theorem | монотонно убывает И ограничена снизу (= 'сходится' в смысле P4-пары) |
| `process_converges` | Theorem | артефакт убыв.+огранич.снизу + beta растёт ('сходится к теории с полным SO(4)' — лишь в прозе) |
| `rg_contraction_summary` | Theorem | ★ сводка: артефакт убыв., beta раст., артефакт огранич., артефакт>0 |

**Key lemmas (deep):**

- **`double_contraction`** - Заявленная 'ключевая' теорема (★ KEY в комментарии): RG якобы сжимает И отношение r (как r^2), И артефакты A (как A*beta/beta'), так что 'щель выживает, пока артефакты умирают'. Формально же доказаны лишь три факта об одном линейном графике beta_n: artifact_n<=artifact_0, beta0<=beta_n, beta_n>0. Двойного сжатия r->r^2 в самих утверждениях НЕТ (это только в комментарии); реальное содержание = монотонность 1/beta_n. Честно: всё следует из beta_monotone + lattice_artifact_size убывает по beta. _(RG, artifact, monotone, comment-vs-theorem)_
- **`process_converges`** - Главное место оверклейма: имя и комментарий ('RG process converges to a theory with full SO(4)') обещают сходимость к континуальной SO(4)-симметричной теории, но тело доказывает ТОЛЬКО {артефакт убывает, артефакт>0, beta растёт}. Ни предел, ни восстановление SO(4) не формализованы — это монотонно-ограниченная ПАРА (P4-процесс), не теорема о пределе. Каверзу надо называть прямо. _(overbranding, SO4, process, no-limit)_
- **`beta_unbounded_structural`** - 'beta растёт без предела' доказано как forall n, beta0 < beta_{n+1} — то есть лишь строгое превышение начального значения на каждом шаге, а не настоящая неограниченность (для любого M существует n с beta_n>M). Имя сильнее утверждения; график линеен (beta_n=beta0+n*c), так что подлинная неограниченность была бы достижима, но здесь не сформулирована. _(beta-growth, structural, name-vs-claim)_

**Uniqueness - score 1 (exposition).** Чистая сборка следствий: на ПОСТУЛИРОВАННОМ линейном одно-петлевом графике beta_n решёточные артефакты и анизотропия монотонно убывают, оставаясь положительными — оформлено как 'двойное сжатие' и 'сходимость процесса'.
> _Caveat:_ Математически тривиально (монотонность 1/beta_n), почти все проофы = один `exact` импортированной леммы. График beta_n=beta0+n*b0*beta0^2 ПОСТУЛИРОВАН (линеаризация одной петли), не выведен. Оверклеймы: process_converges 'к теории с полным SO(4)' (SO(4)/предел не доказаны), beta_unbounded_structural (лишь > начального), gap_ratio_persists (тело = beta_n>0). Заголовок '~35 Qed' завышен: фактически 24.

---

## #493 - `src/gauge/RGConvergence.v` - score 2 (methods)

**Truncated RG-correction series is eventually constant (Cauchy), corrections < 1/10, decay >= 24/order**

- **Topic.** Models the RG correction at order k as a 3-stage step function (0 / quartic / quartic+sextic), proves it is bounded by a monotone delta-process < 1/10, eventually constant for k>=2 (hence Cauchy), and that rg_process = linear + correction is Cauchy and stays within 1/10 of the fixed point beta=3.
- **Role.** Sits atop RGFlow (imports rg_map_linear, rg_linear_fixed_point), CosineAction, HigherOrderRG, PerturbationRG (sources of rg_correction_quartic/sextic, delta_quartic/sextic, quartic/sextic_correction_bound), FixedPoint, SeriesConvergence (is_cauchy). Capstone of the perturbative-RG sub-thread; leaf file.
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs List Lia ZArith Lqa; ToS: CauchyReal SeriesConvergence FixedPoint; gauge: RGFlow CosineAction HigherOrderRG PerturbationRG
- **E/R/R.** _Elements:_ поправки порядка k: 0 (k=0), quartic (k=1), quartic+sextic (k>=2); пороги delta_quartic, delta_sextic. _Roles:_ correction_process = роль ряда поправок; correction_bound_process = мажоранта; rg_process = карта RG порядка k; is_cauchy = роль сходимости-как-процесса. _Rules:_ поправка ограничена мажорантой (треуг. нер-во); мажоранта монотонна и < 1/10; для k>=2 поправка постоянна => Cauchy; rg_process Cauchy наследуется; delta_sextic*24 <= delta_quartic. _P4:_ ряд НЕ берёт завершённый предел — он становится постоянным с k=2, поэтому 'Cauchy' тривиально (хвост = 0); это P4-прочтение: поправки суть процесс, а не объект; нелинейная RG не равна линейной (convergence_what_is_open) — честная граница того, что доказано.
- **Classical counterpart.** A Cauchy/eventually-constant truncated perturbation series and factorial decay of higher-order corrections are standard. NEW here is ONLY the P4 framing: the RG-correction sequence (linear, +quartic, +sextic, then constant) is shown eventually constant hence Cauchy, with corrections bounded < 1/10 and decaying by >= 24 per order — an honest 'process not completed-object' reading, no new analytic content.
- **Tags.** gauge, RG, renormalization, perturbation-series, cauchy, factorial-decay, fixed-point, honest-scope, P4
- **Notes.** STATUS header '~18 Qed' AND end-marker `total_count : (18 = 18)%nat` AND the summary block list both claim 18; actual Qed = 12 (drift on both the header and the bogus 18=18 marker). 0 own axioms in this file (header notes 'classic via PowerSeries' = transitively imported, not declared here). convergence_what_is_open is an honest scope-boundary lemma. delta_quartic/delta_sextic thresholds are posited upstream (PerturbationRG).

**Lemmas (16):**

| name | kind | role |
|---|---|---|
| `correction_process` | Definition | k-> 0 \| quartic \| quartic+sextic (3-ступенчатая функция поправок) |
| `correction_bound_process` | Definition | k-> 0 \| delta_quartic \| delta_quartic+delta_sextic (мажоранта) |
| `correction_process_bounded` | Lemma | \|поправка_k\| <= мажоранта_k для 2<=beta<=4 (по случаям + треуг.) |
| `correction_bound_monotone` | Lemma | мажоранта_k <= мажоранта_{k+1} |
| `correction_total_bound` | Lemma | мажоранта_k < 1/10 для всех k |
| `correction_process_eventually_constant` | Lemma | k>=2 => поправка_{k+1} == поправка_k (хвост постоянен) |
| `correction_process_cauchy` | Lemma | ★ поправочный процесс Cauchy (N=2, хвост=0) |
| `rg_process` | Definition | rg_map_linear beta + correction_process beta k |
| `rg_process_at_3` | Lemma | \|rg_process 3 k - 3\| <= 1/10 (остаётся у неподвижной точки) |
| `rg_process_cauchy` | Lemma | ★ rg_process Cauchy (наследует от поправок) |
| `convergence_rate` | Lemma | delta_sextic*24 <= delta_quartic (факториальный спад >= 24/порядок) |
| `p4_process_interpretation` | Theorem | сводка P4: оба процесса Cauchy + хвост постоянен (предел не нужен) |
| `rg_convergence_main` | Theorem | ★ главная сводка: поправка огранич. + <1/10 + Cauchy + скорость |
| `convergence_what_is_proved` | Theorem | честный реестр доказанного (quartic огранич., спад, Cauchy) |
| `convergence_what_is_open` | Theorem | ★ честная граница: НЕ (линейная RG == квартичная RG) |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`correction_process_cauchy`** - Несущая лемма: поправочный процесс Cauchy. Доказательство честно тривиально — поправка постоянна для k>=2 (correction_process_eventually_constant), поэтому свидетель N=2 и хвостовая разность тождественно 0. То есть 'сходимость' здесь = 'усечение на двух порядках + хвост нулевой', а не аналитическая сходимость бесконечного ряда. Это и есть P4-прочтение: ряд — процесс, обрывающийся фактически. Классический аналог — частичная сумма ряда теории возмущений; ново лишь обрамление. _(cauchy, eventually-constant, perturbation, P4)_
- **`convergence_what_is_open`** - Честный анти-капстоун: ~(forall beta, rg_map_linear beta == rg_map_quartic beta) — линеаризованная RG НЕ совпадает с квартичной (опровергается на beta=1 через целую арифметику Qeq). Явно фиксирует, что доказана сходимость ПОПРАВОК к усечённой карте, а не эквивалентность точной и приближённой RG. Редкая в кластере явная декларация границы — поднимает честность файла. _(honest-scope, open-problem, linear-vs-nonlinear)_
- **`rg_process_at_3`** - rg_process 3 k остаётся в 1/10-окрестности неподвижной точки beta=3 на всех порядках k: использует rg_linear_fixed_point (rg_map_linear 3 = 3) + correction_total_bound (<1/10). Конкретная количественная оценка устойчивости неподвижной точки под поправками — содержательнее чисто структурных лемм, но опирается на ПОСТУЛИРОВАННЫЕ пороги delta_quartic/sextic из PerturbationRG. _(fixed-point, stability, quantitative-bound)_

**Uniqueness - score 2 (methods).** P4-прочтение перенормировочного ряда: трёхступенчатый процесс поправок постоянен с k=2, потому тривиально Cauchy; мажорирован < 1/10 с факториальным спадом >= 24/порядок; включает явную честную теорему о том, что НЕ доказано (линейная != квартичная RG).
> _Caveat:_ Содержание классично (частичная сумма теории возмущений, факториальный спад). 'Cauchy' тривиально, т.к. хвост ряда тождественно 0 (усечение на 2 порядках). Пороги delta_quartic/sextic постулированы в импортах. Заголовок '~18 Qed' и маркер total_count:(18=18) завышены: фактически 12 Qed.

---

## #494 - `src/gauge/RGFlow.v` - score 2 (methods)

**Linearized RG map f(beta)=(9+beta)/4: contraction (1/4) to fixed point 3, gap>0; Millennium NOT closed**

- **Topic.** Defines the linearized RG map, proves it is a 1/4-contraction on [2,4] with unique fixed point beta*=3 (Banach via the project's FixedPoint), iterates converge (Cauchy), the U(1) and SU(2) mass gaps at beta*=3 are positive, and explicitly that linearized RG differs from the quadratic RG (so no Clay proof).
- **Role.** Foundational RG file of the sub-thread: provides rg_map_linear, rg_fixed_point, rg_is_contraction, rg_linear_fixed_point that RGConvergence.v imports and builds on. Imports LinearAlgebra, FixedPoint (is_contraction, iterate, banach_fixed_point, contraction_unique_fixed), TransferMatrix, SU2Group, SU2TransferMatrix, StrongCoupling (mass_gap_2x2, su2_mass_gap).
- **Counts.** Qed 19 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs List Lia ZArith Lqa; ToS: LinearAlgebra CauchyReal SeriesConvergence MonotoneConvergence FixedPoint; gauge: TransferMatrix SU2Group SU2TransferMatrix StrongCoupling
- **E/R/R.** _Elements:_ линейная карта f(beta)=(9+beta)/4; неподвижная точка beta*=3; множитель сжатия 1/4; конкретные итерации f(2)=11/4, f^2(2)=47/16. _Roles:_ rg_map_linear = роль RG-преобразования; is_contraction/banach = роль сжатия; rg_fixed_point = аттрактор; gap_at_fixed_point/su2_gap = роль щели масс. _Rules:_ f отображает [2,4]->[2,4]; \|f(x)-f(y)\| = (1/4)\|x-y\| (Липшиц); единственная неподвижная точка (Банах); щель при beta*=3 положительна (lra); линейная RG != квадратичная. _P4:_ итерации сходятся как Cauchy-ПОСЛЕДОВАТЕЛЬНОСТЬ (banach_fixed_point даёт CauchySeq, а не завершённый предел в R) — P4-процесс; rg_gap_to_millennium явно отделяет ДОКАЗАННОЕ (линеаризация сжимается, щель>0) от НЕДОКАЗАННОГО (точная RG), запрещая отождествлять линеаризацию с полным потоком.
- **Classical counterpart.** The Banach fixed-point theorem for a contraction on an invariant interval, and a linearized RG map with attractive fixed point, are classical. NEW here is ONLY the concrete instance: f(beta)=(9+beta)/4 has fixed point 3, Lipschitz 1/4, maps [2,4]->[2,4], iterates Cauchy via the project's banach_fixed_point; the mass gap at the fixed point is positive by lra; honestly flagged: linearized != quadratic RG, so the Millennium problem is NOT closed.
- **Tags.** gauge, RG, renormalization, banach, contraction, fixed-point, mass-gap, SU2, millennium, honest-scope
- **Notes.** STATUS header '~24 Qed'; actual = 20 (drift). 0 own axioms (header says AXIOMS: none). HONESTY: despite the gauge-cluster Millennium framing, rg_gap_to_millennium explicitly states the Clay problem is NOT closed (linearized != quadratic RG). The linear map's coefficients (9, 1/4) are chosen so that 3 is the fixed point with Lipschitz 1/4 — posited linearization, not derived from blocking. Gap positivity is at the single point beta*=3 for a 2x2 truncation.

**Lemmas (30):**

| name | kind | role |
|---|---|---|
| `rg_map_linear` | Definition | f(beta) = (9+beta)*(1/4) — линеаризованная RG-карта вокруг beta*=3 |
| `rg_fixed_point` | Definition | beta* = 3 |
| `rg_contraction_factor` | Definition | 1/4 (константа Липшица) |
| `rg_map_quadratic` | Definition | 4*beta/(1+beta) — квадратичная RG (для контраста) |
| `gap_at_fixed_point` | Definition | mass_gap_2x2 beta* (U(1)-щель в неподвижной точке) |
| `su2_gap_at_fixed_point` | Definition | su2_mass_gap beta* (SU(2)-щель) |
| `rg_linear_positive` | Lemma | beta>0 => f(beta)>0 |
| `rg_linear_fixed_point` | Lemma | ★ f(3) == 3 (неподвижная точка) |
| `rg_linear_maps_interval` | Lemma | 2<=beta<=4 => 2<=f(beta)<=4 (инвариантный интервал) |
| `rg_linear_lipschitz` | Lemma | \|f(x)-f(y)\| == (1/4)\|x-y\| (точная константа) |
| `rg_is_contraction` | Theorem | ★ is_contraction f 2 4 (1/4) — теорема сжатия |
| `rg_converges` | Theorem | итерации f от 3 образуют Cauchy-последовательность (banach) |
| `rg_unique_fixed_point` | Theorem | неподвижная точка единственна в [2,4] |
| `rg_fp_lb` | Lemma | 2 <= beta* (вспом. для banach) |
| `rg_fp_ub` | Lemma | beta* <= 4 (вспом.) |
| `rg_cauchy_seq` | Definition | banach_fixed_point f ... : CauchySeq (явный объект-процесс) |
| `rg_quadratic_at_3` | Lemma | квадратичная RG: 4*3/4 == 3 (совпадает в неподвижной точке) |
| `rg_quadratic_at_2` | Lemma | квадратичная RG в 2 == 8/3 (расходится с линейной) |
| `rg_maps_agree_at_fp` | Lemma | линейная и квадратичная RG совпадают В неподвижной точке |
| `gap_at_fp_value` | Lemma | U(1)-щель == 2 - 3*(1/4) = 5/4 |
| `gap_at_fp_positive` | Lemma | ★ 0 < U(1)-щель в неподвижной точке |
| `su2_gap_at_fp_positive` | Lemma | ★ 0 < SU(2)-щель в неподвижной точке (через su2_gap_at_beta_3) |
| `rg_iteration_1` | Lemma | f(2) == 11/4 (конкретная итерация) |
| `rg_iteration_2` | Lemma | f^2(2) == 47/16 |
| `rg_preserves_gap` | Theorem | щель>0 И f(3)=3 И сжатие (сводка) |
| `rg_chain_complete` | Theorem | сжатие + неподв.точка + U(1)-щель>0 + SU(2)-щель>0 |
| `rg_gap_to_millennium` | Theorem | ★ ЧЕСТНО: доказано (сжатие, щель>0) vs линейная != квадратичная => Clay НЕ закрыт |
| `rg_flow_summary` | Theorem | сводка: сжатие+неподв.точка+щель+Cauchy+согласие в fp |
| `rg_flow_main` | Theorem | ★ главная: сжатие + неподв.точка + SU(2)-щель>0 |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`rg_is_contraction`** - Ядро файла: is_contraction rg_map_linear 2 4 (1/4) — линеаризованная RG-карта f(beta)=(9+beta)/4 есть сжатие с константой 1/4 на инвариантном интервале [2,4]. Опирается на точную лемму Липшица rg_linear_lipschitz (равенство, не оценка) и rg_linear_maps_interval. Через project-овский banach_fixed_point даёт CauchySeq итераций и единственность неподвижной точки. Классика — теорема Банаха; ценность инстанса = конкретные рациональные числа и стыковка со щелью масс. Но f линеаризована вокруг 3 ПО ПОСТРОЕНИЮ (коэффициенты 9,1/4 подобраны так, чтобы 3 была неподвижной), а не выведена из блокировки. _(banach, contraction, fixed-point, linearized-RG)_
- **`rg_gap_to_millennium`** - Честный анти-оверклейм-замок (несмотря на имя файла-кластера про Millennium): теорема явно конъюнктирует ДОКАЗАННОЕ {is_contraction, su2_gap>0} с ОПРОВЕРЖЕНИЕМ ~(forall beta, rg_map_linear == rg_map_quadratic) (на beta=0). То есть прямо декларирует: положительность щели установлена лишь для ЛИНЕАРИЗОВАННОЙ карты в одной неподвижной точке, а полная (квадратичная/точная) RG к ней не сведена — Clay-проблема НЕ закрыта. Эталон честной формулировки для кластера. _(honest-scope, millennium, linear-vs-quadratic, no-overclaim)_
- **`su2_gap_at_fp_positive`** - 0 < su2_mass_gap 3: SU(2)-щель масс положительна именно в неподвижной точке beta*=3. Делегирует импортированному su2_gap_at_beta_3 (конкретное Q-вычисление на малой решётке/2x2-усечении в SU2TransferMatrix). Связывает RG-аттрактор со щелью — главная физическая цель файла; честно — это значение щели на КОНКРЕТНОМ beta для КОНКРЕТНОЙ группы и усечения, не континуальная щель. _(mass-gap, SU2, fixed-point, finite-lattice)_

**Uniqueness - score 2 (methods).** Конкретный рациональный инстанс теоремы Банаха для линеаризованной RG-карты f(beta)=(9+beta)/4 (сжатие 1/4, единственная неподвижная точка 3, Cauchy-итерации) состыкованный с положительностью U(1)/SU(2)-щели масс в неподвижной точке.
> _Caveat:_ Банах и аттрактивная неподвижная точка классичны; карта f линеаризована вокруг 3 ПО ПОСТРОЕНИЮ (коэффициенты подобраны), не выведена. Щель>0 — для линеаризации в одной точке beta*=3, конкретной группы и усечения. Файл сам честно фиксирует (rg_gap_to_millennium): линейная != квадратичная RG => Millennium НЕ закрыт. Заголовок '~24 Qed' завышен: фактически 20.

---

## #495 - `src/gauge/SpatialHamiltonian.v` - score 2 (methods)

**Spatial Hamiltonian as an explicit Q tridiagonal symmetric matrix in the SU(2) character basis**

- **Topic.** Defines H_spatial_entry d_sp j j' (diagonal = d_sp*Casimir, off-diagonal = d_sp*coupling, else 0 via j<->j+-1 selection), proves symmetry and tridiagonality, ground state H00=0, diagonal nonneg and increasing, explicit 3+1D values, and strong-coupling suppression factors s_0=1, s_1<1.
- **Role.** Construction utility in the gauge spatial-direction sub-thread: imports SU2Characters and ClebschGordan (sources of spatial_diagonal, spatial_offdiag, spatial_diag_0/1, diag_increasing_0_1, spatial_*_nonneg, inject_Z_nat_pos). Provides the H_spatial_entry matrix consumed by spatial transfer/Hamiltonian analyses. Leaf file (CHECK/Print Assumptions at end).
- **Counts.** Qed 25 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: CauchyReal SeriesConvergence; gauge: SU2Characters ClebschGordan
- **E/R/R.** _Elements:_ записи матрицы H_spatial_entry d_sp j j' in Q; пространственная размерность d_sp (3 в 3+1D); представления j (диагональ Казимира, недиагональ связи). _Roles:_ H = пространственный гамильтониан (роль энергии плакетной связи); диагональ = роль энергии Казимира; недиагональ = роль связи соседних представлений; suppression_factor = роль подавления возбуждённых при сильной связи. _Rules:_ правило отбора j<->j+-1 => H трёхдиагональна; H симметрична; H_00=0 (нет Казимира в основном); H_jj растёт с j; при сильной связи s_0=1, s_1<1. _P4:_ матрица задана как ЯВНАЯ конечная функция записей (Nat.eqb-ветвление), все значения — конкретные рациональные числа, проверяемые nia/lia на малых j — Element-сторона (конечно вычислимое устройство); спектр/диагонализация H (собственные значения, щель) в этом файле НЕ берётся — остаётся за пределами (role-limit для бесконечной матрицы).
- **Classical counterpart.** A nearest-neighbour selection rule (j <-> j+-1) making a Hamiltonian tridiagonal/symmetric, with Casimir-type increasing diagonal, is standard representation theory / lattice Hamiltonian construction. NEW here is ONLY: nothing — an explicit Q-valued tridiagonal-matrix-entry function in the SU(2) character basis with symmetry, tridiagonality, ground-state H00=0, increasing diagonal, and concrete 3+1D (d_sp=3) rational entries verified by nia/lia.
- **Tags.** gauge, spatial-hamiltonian, tridiagonal, SU2, character-basis, clebsch-gordan, selection-rule, finite-lattice, P4
- **Notes.** STATUS header '~40 Qed'; actual = 25 (drift). 0 own axioms (Print Assumptions at end). The file builds the matrix STRUCTURE (symmetry, tridiagonality, concrete entries) but does NOT diagonalize it — no eigenvalues, no mass gap computed here. 'physical_energy'-style claims live in sibling files. d_sp=3 (3+1D) and small j only.

**Lemmas (30):**

| name | kind | role |
|---|---|---|
| `H_spatial_entry` | Definition | ★ запись матрицы: диаг = d_sp*spatial_diagonal, недиаг (j+-1) = d_sp*spatial_offdiag, иначе 0 |
| `H_spatial_symmetric` | Theorem | ★ H_{jj'} == H_{j'j} (симметрия, разбор случаев по Nat.eqb) |
| `H_spatial_tridiagonal` | Theorem | ★ j' > j+1 => H_{jj'} == 0 (трёхдиагональность сверху) |
| `H_spatial_tridiagonal_below` | Theorem | j > j'+1 => H_{jj'} == 0 (снизу) |
| `H_spatial_diag` | Lemma | H_{jj} == d_sp*spatial_diagonal j |
| `H_spatial_offdiag_right` | Lemma | H_{j,j+1} == d_sp*spatial_offdiag j |
| `H_spatial_offdiag_left` | Lemma | H_{j+1,j} == d_sp*spatial_offdiag j (через симметрию) |
| `H_ground_state_zero` | Theorem | ★ H_{00} == 0 (нет энергии Казимира в основном состоянии) |
| `H_first_excited` | Lemma | H_{11} == d_sp*(2/9) |
| `H_second_excited` | Lemma | H_{22} == d_sp*(6/25) |
| `H_diag_0_lt_1` | Lemma | d_sp>=1 => H_{00} < H_{11} (возбуждение дороже основного) |
| `H_diag_nonneg` | Lemma | 0 <= H_{jj} (диагональ неотрицательна) |
| `H_offdiag_nonneg` | Lemma | 0 <= H_{j,j+1} |
| `H_3d_00` | Lemma | 3+1D: H_{00} == 0 |
| `H_3d_11` | Lemma | H_{11} == 2/3 при d_sp=3 |
| `H_3d_22` | Lemma | H_{22} == 18/25 |
| `H_3d_01` | Lemma | H_{01} == 1 (недиагональ) |
| `H_3d_12` | Lemma | H_{12} == 2/5 |
| `H_2x2_trace` | Definition | H_{00}+H_{11} (след 2x2-усечения) |
| `H_2x2_trace_formula` | Lemma | след == d_sp*(2/9) |
| `H_2x2_trace_3d` | Lemma | след == 2/3 при d_sp=3 |
| `spatial_cost_j1` | Definition | beta_s*d_sp*(2/9) — пространственная стоимость энергии j=1 |
| `spatial_cost_positive` | Lemma | beta_s>0, d_sp>=1 => стоимость > 0 |
| `spatial_cost_nonneg` | Lemma | beta_s>=0 => стоимость >= 0 |
| `spatial_cost_3d` | Lemma | стоимость == 2/3 при beta_s=1, d_sp=3 |
| `spatial_suppression_factor` | Definition | s_j = 1 - beta_s*d_sp*spatial_diagonal j |
| `suppression_factor_0` | Lemma | s_0 == 1 (основное не подавлено) |
| `suppression_factor_1_formula` | Lemma | s_1 == 1 - beta_s*d_sp*(2/9) |
| `suppression_factor_lt_1` | Lemma | beta_s>0, d_sp>=1 => s_1 < 1 (возбуждённое подавлено) |
| `spatial_hamiltonian_summary` | Theorem | ★ сводка: H_00=0, H_00<H_11, диаг>=0, трёхдиагональна, симметрична |

**Key lemmas (deep):**

- **`H_spatial_symmetric`** - Самая трудоёмкая лемма файла (длинный разбор случаев по Nat.eqb-ветвлениям H_spatial_entry с заменами через Nat.eqb_neq/eqb_eq и lra). Доказывает H_{jj'}=H_{j'j} — симметричность построенной трёхдиагональной матрицы. Содержательно тривиально (определение симметрично по конструкции для недиагоналей j<->j+1), но в Coq требует аккуратной комбинаторики булевых равенств индексов. Классика — эрмитовость гамильтониана; здесь над Q, без сопряжения. _(symmetric, tridiagonal, case-analysis)_
- **`H_spatial_tridiagonal`** - j' > j+1 => H_{jj'} == 0: формализует правило отбора j<->j+-1 (связь только соседних представлений) как структурную трёхдиагональность. Вместе с H_spatial_tridiagonal_below задаёт ленточную структуру 2x2/3x3-усечений, на которых далее берутся следы и собственные значения в смежных файлах. Это решёточная запись селекционного правила Клебша-Гордана, а не спектральный результат. _(selection-rule, tridiagonal, clebsch-gordan)_
- **`spatial_hamiltonian_summary`** - Капстоун-сводка структурных свойств: основное состояние без энергии (H_00=0), возбуждённое дороже (H_00<H_11), диагональ неотрицательна, матрица трёхдиагональна и симметрична. Это полный 'паспорт' матрицы как объекта, но НЕ её диагонализация: щель масс, собственные значения и физический спектр здесь не вычисляются — файл строит устройство (Element), оставляя спектр (для бесконечной матрицы — role-limit) другим файлам. _(summary, structure, no-spectrum)_

**Uniqueness - score 2 (methods).** Явная Q-значная трёхдиагональная симметричная матрица пространственного гамильтониана в характерном базисе SU(2): правило отбора j<->j+-1, H_00=0, растущая диагональ Казимира, конкретные рациональные записи 3+1D и факторы подавления при сильной связи.
> _Caveat:_ Стандартная теория представлений / решёточная конструкция гамильтониана; правило отбора и трёхдиагональность классичны. Узко: малые j, конкретное d_sp=3, energy = первый порядок. Спектр/щель НЕ вычисляются (только структура матрицы). Заголовок '~40 Qed' завышен: фактически 25.

---

## #496 - `src/gauge/SpectralBound.v` - score 2 (methods)

**Attack 1: string tension vs 2x2 spectral gap — the gap collapses at beta=8 (K=2 insufficient)**

- **Topic.** Defines eigenvalue_ratio(beta)=(beta/8)/(2-beta/8) and spectral_gap_lower=1-ratio for the SU(2) 2x2 strong-coupling transfer matrix, then shows the gap is positive on (0,8) but EXACTLY 0 at beta=8 while string_tension(8)=3/32>0 — a self-flagged limitation of the 2x2 truncation.
- **Role.** Diagnostic dead-end of the strong-coupling 2x2 branch; motivates the K>=3 / strip (N x 1) construction (StripTransfer/StripSpectrum). Imports gauge.TransferMatrix (mass_gap_2x2, transfer_eigenvalue_0/1), gauge.SU2TransferMatrix, gauge.StrongCoupling (string_tension), gauge.GapDecayRate, gauge.ConfinementCorrection. Not reused upward — it is the 'why we need more' note.
- **Counts.** Qed 21 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: CauchyReal; gauge.TransferMatrix; gauge.SU2TransferMatrix; gauge.StrongCoupling; gauge.GapDecayRate; gauge.ConfinementCorrection
- **E/R/R.** _Elements:_ конкретные рациональные значения beta in {1,2,4,6,7,8}; собственные значения 2x2 матрицы lambda_0,lambda_1; натяжение струны sigma(beta). _Roles:_ spectral_gap_lower = роль-щель (1-ratio); string_tension = роль-конфайнмент; обе сравниваются как функции beta. _Rules:_ ratio = (beta/8)/(2-beta/8); gap = 1-ratio; область (0,8) даёт gap in (0,1), а beta=8 защёлкивает ratio=1 => gap=0. _P4:_ P4-диагноз усечения: 2x2 = конечная актуальная аппроксимация (Element-размер K=2); при beta=8 эта арена ВЫРОЖДАЕТСЯ (gap=0), хотя физическая sigma>0 — щель не исчезла, исчезла РАЗРЕШАЮЩАЯ СПОСОБНОСТЬ матрицы; нужен K>=3 (большая Element-арена).
- **Classical counterpart.** Mirrors the lattice-gauge folklore 'string tension sigma>0 => mass gap>0' (area law => confinement) and the transfer-matrix spectral-gap = -log(lambda_1/lambda_0). NEW here only as a deliberate NEGATIVE result: on the concrete SU(2) 2x2 strong-coupling transfer matrix the eigenvalue ratio hits 1 at beta=8 so the 2x2 spectral gap COLLAPSES to 0 while sigma stays >0 — diagnosing that K=2 is too small, not that confinement fails.
- **Tags.** gauge, yang-mills, transfer-matrix, spectral-gap, string-tension, SU2, strong-coupling, negative-result, P4
- **Notes.** Actual Qed.=22 (25 top-level declarations, of which 3 are Definitions: eigenvalue_ratio, spectral_gap_lower, string_tension_2nd). STATUS header says '~25 Qed' — approximate, refers to declaration count not Qed count.

**Lemmas (25):**

| name | kind | role |
|---|---|---|
| `eigenvalue_ratio` | Definition | отношение собственных значений lambda_1/lambda_0 = (beta/8)/(2-beta/8) |
| `eigenvalue_ratio_range` | Lemma | 0<ratio<1 для beta in (0,8) |
| `eigenvalue_ratio_at_8` | Lemma | ratio(8)==1 (собственные значения совпадают) |
| `spectral_gap_lower` | Definition | спектральная щель = 1-ratio |
| `spectral_gap_positive` | Lemma | gap>0 на (0,8) |
| `spectral_gap_at_8` | Lemma | ★ gap(8)==0 — вырождение 2x2 при критической связи |
| `spectral_equals_normalized_gap` | Lemma | gap == mass_gap_2x2 beta / (2-beta/8) (связь с нормализованной щелью) |
| `spectral_gap_bound` | Lemma | gap<=1 на (0,8) |
| `tension_vs_gap_at_1` | Lemma | sigma(1)<=gap(1) (vm: 3/4<=14/15) |
| `tension_vs_gap_at_2` | Lemma | sigma(2)<=gap(2) |
| `tension_vs_gap_at_4` | Lemma | sigma(4)<=gap(4) |
| `tension_vs_gap_at_6` | Lemma | sigma(6)<=gap(6) |
| `tension_vs_gap_at_7` | Lemma | sigma(7)<=gap(7) |
| `tension_exceeds_gap_at_8` | Theorem | ★ gap(8)==0 и sigma(8)>0 — нарушение неравенства sigma<=gap |
| `spectral_representation` | Theorem | общая форма: ratio<=r<1 => gap>=1-r (тривиальная lra-арифметика) |
| `area_law_implies_gap` | Theorem | если ratio<=1-sigma, то gap>=sigma (area-law=>gap, арифметическая обёртка) |
| `string_tension_2nd` | Definition | поправка 2-го порядка sigma_2 = 3/(4beta) - 9/(32beta^2) |
| `tension_2nd_at_8` | Lemma | sigma_2(8)==183/2048 (vm) |
| `tension_2nd_positive_at_8` | Lemma | sigma_2(8)>0 |
| `correction_ratio_small` | Lemma | поправка 2-го порядка ~5% ведущего члена при beta=8 |
| `strong_coupling_diagnosis` | Theorem | sigma(8)>0 ∧ gap(8)=0 ∧ sigma_2(8)>0 — диагноз недостаточности 2x2 |
| `spectral_bound_result` | Theorem | сводка Attack 1 (gap>0 на (0,8), gap(8)=0, sigma(8)>0, неравенства) |
| `tension_implies_larger_matrix` | Theorem | sigma(8)>0 ∧ gap(8)=0 => нужна K>=3 матрица |
| `spectral_main` | Theorem | ★ главный итог: щель=0 при beta=8 есть предел K=2, не физики |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`tension_exceeds_gap_at_8`** - Несущая НЕГАТИВНАЯ теорема файла: на конкретной 2x2 strong-coupling матрице при beta=8 spectral_gap_lower==0, тогда как string_tension(8)=3/32>0. Это сознательно зафиксированный провал ожидаемого 'sigma>0 => gap>0' на данной арене — честный сигнал, что 2x2 усечение вырождается (оба собственных значения сливаются), а НЕ что конфайнмент исчезает. Ценность = диагностика размера арены (P4), а не новая физика. _(negative-result, spectral-gap, truncation, beta=8)_
- **`spectral_main`** - Капстоун-рамка Attack 1: формализует вывод 'gap=0 при beta=8 — это ограничение K=2, а не физики; разрешение — K>=3'. Содержательно это просто конъюнкция трёх уже доказанных фактов (gap>0 на (0,8), gap(8)=0, sigma(8)>0) плюс прозаический комментарий о переходе к Attack 2. Уровень — методический мост к strip-конструкции, не результат. _(capstone, bridge, methods)_

**Uniqueness - score 2 (methods).** Машинно-проверенный негативный диагноз: конкретная SU(2) 2x2 strong-coupling transfer-матрица даёт spectral_gap=0 при beta=8 при sigma>0 — усечение K=2 недостаточно, мотивируя strip-конструкцию.
> _Caveat:_ НЕ доказательство Yang-Mills mass gap (Clay): всё — точная Q-арифметика на ОДНОЙ 2x2 матрице при дискретных beta, в режиме сильной связи (разложение по характерам). 'sigma=>gap' и area-law-теоремы здесь — тривиальные lra-обёртки общих неравенств, а не вывод area law. Это сознательный тупик-диагностика, а не положительный результат; континуум-предела нет.

---

## #497 - `src/gauge/SpectralGapCorrect.v` - score 3 (new-framing)

**Corrected gap = |t0-t1|, positive for ALL rational beta>0 via irrationality of sqrt(1920)**

- **Topic.** Redefines the spectral gap as the ABSOLUTE eigenvalue difference Qabs(matrix_mass_gap) (fixing sign-flips at eigenvalue crossing), then proves it is >0 for every rational beta>0 by showing the M=0 gap polynomial (b^2-48)^2=1920 has no rational solution — an infinite-descent irrationality proof of sqrt(1920)=8*sqrt(30).
- **Role.** Repairs the gap definition for the strong-coupling character branch (CharacterTransfer/ExactMassGap/GapRatio/TransferMatrixProof). The number-theoretic core (no_rational_sqrt_30/1920, gap_M0_nonzero) is the load-bearing 'gap never vanishes' lemma for the rational-beta family. Imports CauchyReal, SeriesConvergence.
- **Counts.** Qed 28 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: CauchyReal; ToS: SeriesConvergence; gauge.CharacterTransfer; gauge.ExactMassGap; gauge.GapRatio; gauge.TransferMatrixProof
- **E/R/R.** _Elements:_ рациональные beta (как p#q); собственные значения t0_M0,t1_M0 (частичные суммы Бесселя I0,I2,I4); полином щели 384-96b^2+b^4. _Roles:_ spectral_gap = \|t0-t1\| (роль-щель, корректная при пересечении); дискриминантное число 1920 = роль-преграда (не полный квадрат). _Rules:_ gap_M0(b)=1-b^2/4+b^4/384; 384*gap=(b^2-48)^2-1920; gap=0 <=> (b^2-48)^2=1920 <=> sqrt(1920) рационален — запрещено бесконечным спуском. _P4:_ P4/H1-граница как Element vs role-limit: gap НЕ обнуляется ни на одном рациональном beta, потому что нуль потребовал бы иррационального sqrt(1920) (role-limit, недостижимый в Q); т.е. 'щель>0 для всех рац. beta' = Element-факт, опирающийся на role-limit-преграду √30.
- **Classical counterpart.** Mirrors (a) the strong-coupling character/Bessel expansion of the SU(2) lattice transfer matrix and the resulting eigenvalue gap, and (b) the classical irrationality of sqrt(30)/sqrt(1920) by infinite descent (the standard sqrt(2) argument, generalized). NEW is bundling them: the mass gap is positive for EVERY rational beta>0 precisely BECAUSE the gap polynomial 384-96b^2+b^4=(b^2-48)^2-1920 has no rational root, since 1920 is not a perfect square — gap-nonvanishing reduced to a number-theoretic non-square fact.
- **Tags.** gauge, yang-mills, spectral-gap, SU2, strong-coupling, irrationality, infinite-descent, number-theory, rational-beta, H1, eigenvalue-crossing
- **Notes.** Actual Qed.=28 (29 top-level declarations, of which 1 is a Definition: spectral_gap). STATUS header says '~40 Qed' — overstated; the real count is 28. File ends with Check/Print Assumptions (no axioms reported).

**Lemmas (29):**

| name | kind | role |
|---|---|---|
| `spectral_gap` | Definition | корректная щель = Qabs(matrix_mass_gap J beta M) |
| `spectral_gap_nonneg` | Lemma | щель >=0 (Qabs_nonneg) |
| `spectral_gap_unfold` | Lemma | щель == \|t0-t1\| (раскрытие matrix_mass_gap) |
| `spectral_gap_eq_char` | Lemma | щель == \|character_mass_gap\| (мост к характерной форме) |
| `spectral_gap_eq_gap_M0` | Lemma | щель при M=0 == \|gap_M0 beta\| |
| `spectral_gap_pos_case` | Lemma | если gap_M0>=0, то щель == gap_M0 |
| `spectral_gap_beta_1` | Theorem | щель(1)==289/384 (vm) |
| `gap_pos_1` | Theorem | щель(1)>0 |
| `spectral_gap_beta_2` | Theorem | щель(2)==1/24 |
| `gap_pos_2` | Theorem | щель(2)>0 |
| `gap_at_beta_3` | Lemma | gap_M0(3)==-(133/128) (пересечение: t1>t0) |
| `gap_pos_3` | Theorem | щель(3)>0 (\|gap_M0(3)\|=133/128) |
| `gap_at_beta_4` | Lemma | gap_M0(4)==-(7/3) |
| `gap_pos_4` | Theorem | щель(4)>0 |
| `not_perfect_square_1920` | Lemma | 1920 не полный квадрат (43^2=1849<1920<1936=44^2) |
| `no_rational_sqrt_30` | Lemma | ★ нет a,b>0 с a^2=30b^2 (бесконечный спуск через 3\|a,3\|b) |
| `no_rational_sqrt_1920` | Lemma | ★ нет a,b>0 с a^2=1920b^2 (1920=64*30, извлечение трёх двоек -> √30) |
| `pos_sub_eq` | Lemma | Z.pos_sub p q = Zpos p - Zpos q (мост для nia после Q->Z) |
| `bessel_2_M0_explicit` | Lemma | bessel_partial 2 (p#q) 0 == p^2/(8q^2) |
| `bessel_4_M0_explicit` | Lemma | bessel_partial 4 (p#q) 0 == p^4/(384 q^4) |
| `gap_M0_as_poly` | Lemma | gap_M0(p#q) как явный Q-полином 1-2*(p^2/8q^2)+p^4/384q^4 |
| `gap_poly_Z` | Lemma | gap_M0(p#q)=0 => (p^2-48q^2)^2=1920 q^4 (целочисленная форма) |
| `gap_M0_nonzero` | Theorem | ★ gap_M0(beta)≠0 для всех рациональных beta>0 |
| `spectral_gap_pos_all_rational` | Theorem | ★ щель(1,beta,0)>0 для всех рациональных beta>0 |
| `spectral_gap_values` | Theorem | сводка значений щели при beta in {1,2,3,4} |
| `spectral_gap_any_J` | Lemma | щель == \|matrix_mass_gap\| при любом J |
| `spectral_gap_pos_any_J` | Theorem | щель>0 для любого J при beta>0 |
| `eigenvalue_crossing` | Theorem | t0>=t1 при beta<=2; t0<t1 при beta=3 (пересечение); щель всё равно >0 |
| `spectral_gap_summary` | Theorem | итоговая сводка: определение+неотрицательность+положительность для всех рац. beta+значения+пересечение |

**Key lemmas (deep):**

- **`no_rational_sqrt_1920`** - Истинное ядро файла и его единственная содержательная нетривиальность: классический бесконечный спуск, обобщённый с √2 на √30, затем поднятый до √1920=8√30 извлечением трёх множителей 2 из a (a^2=1920b^2 -> (a/8)^2=30b^2). Делегирует no_rational_sqrt_30, где well-founded индукция по Z.to_nat b и анализ a mod 3, b mod 3 даёт меньший контрпример. Классика теории чисел, но именно она — преграда, делающая щель ненулевой на всех рациональных beta. _(irrationality, infinite-descent, number-theory, load-bearing)_
- **`gap_M0_nonzero`** - Мост физика<->теория чисел: gap_M0(beta)=0 переписывается (gap_poly_Z) в целочисленное (p^2-48q^2)^2=1920 q^4, что есть ровно a^2=1920 b^2 с a=p^2-48q^2, b=q^2 — запрещено no_rational_sqrt_1920. Значит спектральная щель strong-coupling матрицы не обнуляется НИ ПРИ КАКОМ рациональном beta>0. Это и есть 'mass gap для всех связей' данного файла — но строго в смысле: на M=0 уровне характерного разложения, для рациональных beta, без континуум-предела. _(bridge, mass-gap, rational-beta, synthesis)_
- **`eigenvalue_crossing`** - Честная тонкость, мотивирующая Qabs-исправление: при beta~2.83 ground state меняется (t1 обгоняет t0), так что наивная разность t0-t1 меняет знак и 'щель' стала бы отрицательной. \|t0-t1\| это чинит. Содержательно — корректность определения, не новый результат; demонстрирует, почему предыдущая (t0-t1) формула была дефектна. _(eigenvalue-crossing, definition-fix, methods)_

**Uniqueness - score 3 (new-framing).** Спектральная щель strong-coupling SU(2) матрицы положительна для ВСЕХ рациональных beta>0, сведено к числовому факту: 1920 не полный квадрат (sqrt(1920) иррационален) — щель-ненулевость как теоретико-числовая преграда (грань H1: Element-щель опирается на role-limit √30).
> _Caveat:_ НЕ Yang-Mills mass gap (Clay). Результат строго про M=0 уровень характерного/Бесселева разложения, для РАЦИОНАЛЬНЫХ beta, в режиме сильной связи; континуум-предела и непрерывного beta нет. Сам спуск √30/√1920 — классика (обобщённый √2-аргумент); ново лишь обрамление 'gap≠0 <=> non-square', а не теорема. Все Бесселевы значения берутся при M=0.

---

## #498 - `src/gauge/StripSpectrum.v` - score 3 (new-framing)

**Strip spectrum at beta=8: eigenvalues (1/4)^{domain walls}, integer-d dichotomy => gap = 3/4 for all N**

- **Topic.** At the decoupled point beta=8 the N x 1 strip transfer matrix is diagonal with eigenvalue (1/4)^{d(s)} (d = domain walls). Since d is a nonnegative integer, every eigenvalue is either 1 (d=0) or <=1/4 (d>=1) — the spectral gap is exactly 3/4 independently of N.
- **Role.** Spectral half of the strip construction: consumes gauge.StripTransfer (strip_transfer, quarter_power), gauge.DomainWalls (domain_walls, all_same, one_boundary, complement, walls_dichotomy, qp_*), gauge.Coupled2D. Feeds gauge.StripSynthesis (eigenvalue_dichotomy, strip_gap_at_8, complement_eigenvalue, gap_independent_of_N). The N-independence claim is the headline reused upward.
- **Counts.** Qed 25 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa List Bool; gauge.DomainWalls; gauge.StripTransfer; gauge.Coupled2D
- **E/R/R.** _Elements:_ конкретные битовые строки s (состояния столбца, list bool); число доменных стенок d(s); собственные значения (1/4)^d; малые спектры N=2,3,4. _Roles:_ strip_eigenvalue_at_8 = роль-собственное-значение; strip_gap_at_8=3/4 = роль-щель; основное/первое-возбуждённое = роли уровней. _Rules:_ eig(s)=quarter_power(d(s)); дихотомия d=0 ∨ d>=1 (целочисленность) => eig==1 ∨ eig<=1/4; щель=1-1/4=3/4 не зависит от N. _P4:_ P4-дискретность как механизм щели: d(s) — НАТУРАЛЬНОЕ число (Element-счёт стенок), значит между 0 и 1 ничего нет; зазор 'нет собственного значения в (1/4,1)' порождён именно конечно-актуальной целочисленностью d, а не предельным переходом — и потому одинаков для любого N.
- **Classical counterpart.** Mirrors the strong-coupling (alpha->0) decoupling limit of a 2D lattice gauge / Ising-type strip, where the transfer matrix becomes diagonal and eigenvalues are gamma^{2 d(s)} with d = number of domain walls. The 'gap is N-independent because excitation cost is local' is the standard Peierls/domain-wall confinement heuristic. NEW only as the explicit machine-checked statement: at beta=8 the spectrum is exactly {(1/4)^d}, d integer => no eigenvalue in (1/4,1) => gap = 3/4 for every N.
- **Tags.** gauge, yang-mills, strip, transfer-matrix, domain-walls, spectral-gap, beta=8, N-independence, Z2-symmetry, P4
- **Notes.** Actual Qed.=25 (27 top-level declarations, of which 2 are Definitions: strip_eigenvalue_at_8, strip_gap_at_8). STATUS header says '~40 Qed' — overstated; real count is 25. The SUMMARY block also mislabels Part V lemma names (lists wall_mult_d0/d1/mult_N2/N3/N4; actual names are mult_d0/mult_d1_N2/mult_d1_N3/state_count_N2/N3/mult_check_N4).

**Lemmas (27):**

| name | kind | role |
|---|---|---|
| `strip_eigenvalue_at_8` | Definition | собственное значение при beta=8 = quarter_power(domain_walls s) |
| `ground_eigenvalue_false` | Theorem | eig(all_false n)==1 (d=0) |
| `ground_eigenvalue_true` | Theorem | eig(all_true n)==1 (d=0) |
| `first_excited_eigenvalue` | Theorem | eig(one_boundary)==1/4 (d=1) при 1<=k<n |
| `second_excited` | Lemma | d=2 => eig==1/16 |
| `third_excited` | Lemma | d=3 => eig==1/64 |
| `strip_gap_at_8` | Definition | щель при beta=8 := 3/4 |
| `gap_equals_three_quarters` | Theorem | 1-1/4==strip_gap_at_8 |
| `gap_positive` | Theorem | 0<strip_gap_at_8 |
| `eigenvalue_dichotomy` | Theorem | ★ eig(s)==1 ∨ eig(s)<=1/4 (целочисленность d) |
| `gap_independent_of_N` | Theorem | ★ при n>=2: ground=1, first=1/4, ничего в (1/4,1) => щель N-независима |
| `thermodynamic_gap_at_8` | Theorem | щель==3/4 при любом n>=2 (термодинамический предел) |
| `spectrum_N2` | Theorem | спектр N=2 = {1,1/4,1/4,1} (vm) |
| `spectrum_N3` | Theorem | спектр N=3 для всех 8 состояний (vm) |
| `mult_d0` | Lemma | ровно 2 состояния с d=0 (all_false, all_true) |
| `mult_d1_N2` | Lemma | d=1 при N=2: состояния [f;t],[t;f] |
| `mult_d1_N3` | Lemma | d=1 при N=3: 4 состояния |
| `state_count_N2` | Lemma | 2*2=4 состояний |
| `state_count_N3` | Lemma | 2*2*2=8 состояний |
| `mult_check_N4` | Lemma | 2+6+6+2=16=2^4 (проверка кратностей N=4) |
| `eigenvalue_positive` | Lemma | eig(s)>0 |
| `eigenvalue_le_one` | Lemma | eig(s)<=1 |
| `ground_is_largest` | Lemma | eig(s)<=eig(all_false (length s)) (основное — наибольшее) |
| `gap_exact` | Theorem | щель=3/4 точно: нет состояния в (1/4,1) |
| `spectrum_N4_gap` | Theorem | щель N=4 = 3/4 |
| `complement_eigenvalue` | Theorem | eig(complement s)==eig(s) (Z2-симметрия) |
| `complement_N2` | Lemma | проверка комплемента при N=2 |

**Key lemmas (deep):**

- **`eigenvalue_dichotomy`** - Несущий механизм: domain_walls возвращает НАТУРАЛЬНОЕ число, поэтому walls_dichotomy даёт d=0 либо d>=1, а монотонность quarter_power (qp_monotone) переводит это в eig==1 либо eig<=1/4 — между 1/4 и 1 пусто. Именно дискретность счётчика стенок (а не аналитический предел) создаёт зазор, и поскольку она не зависит от длины строки, зазор N-инвариантен. Это P4-аргумент в чистом виде: конечно-целочисленная Element-величина запрещает промежуточный спектр. _(domain-wall, integer-discreteness, gap, P4)_
- **`gap_independent_of_N`** - Заголовочный результат: для любого n>=2 основное собственное значение =1, первое возбуждённое =1/4, и ни одно состояние длины n не попадает в (1/4,1). Следствие — щель ровно 3/4 для всех N. Это машинно-проверенная форма доменно-стеночного (Peierls) довода о локальности возбуждения, перенесённая StripSynthesis в 'термодинамический предел'. Честно: всё при ОДНОЙ точке beta=8 (alpha=0, матрица диагональна) — особо разрешимый случай, а не общая связь. _(N-independence, thermodynamic-limit, headline)_

**Uniqueness - score 3 (new-framing).** Машинно-проверенный N-независимый спектральный зазор 3/4 strip-матрицы при beta=8, выведенный из ЦЕЛОЧИСЛЕННОСТИ числа доменных стенок (нет собственного значения в (1/4,1)) — доменно-стеночная локальность как P4-дискретность.
> _Caveat:_ НЕ Yang-Mills mass gap (Clay). Только точка beta=8 (alpha=0), где transfer-матрица ДИАГОНАЛЬНА — особо тривиальный случай; вне beta=8 (alpha≠0) спектр здесь не считается. Спектры N=2,3,4 — конкретные vm_compute; 'N-независимость' доказана как 'щель=3/4 для всех n>=2' (константа), что есть переформулировка определения, а не предельная теорема. Кратности лишь проверены на малых N, не выведены в общем виде. Доменно-стеночный/Peierls довод классичен.

---

## #499 - `src/gauge/StripSynthesis.v` - score 1 (exposition)

**Strip synthesis: domain-wall gap unified across dimensions (0 < 3/4 < 15/16) via one gap_formula**

- **Topic.** Consolidation file: restates the domain-wall argument (integer d => gap N-independent), collects the beta=8 mass gaps across 1+1D/2+1D/3+1D, shows strip gap = gap_formula(1), 3D = gap_formula(2), and proves the monotone dimension ladder — all by exact-rational reflexivity over imported lemmas.
- **Role.** Capstone/synthesis of the strip + dimension-ladder branch. Pure consolidation, 0 new content: imports gauge.StripSpectrum, gauge.StripTransfer, gauge.DomainWalls, gauge.ThermodynamicLimit, gauge.Coupled2D, gauge.Gap2D, gauge.Gap3D, gauge.DimensionLadder, gauge.TransferMatrix and re-bundles their results into summary theorems. Terminal — nothing reuses it.
- **Counts.** Qed 21 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa List Bool; gauge.DomainWalls; gauge.StripTransfer; gauge.StripSpectrum; gauge.ThermodynamicLimit; gauge.Coupled2D; gauge.Gap2D; gauge.Gap3D; gauge.DimensionLadder; gauge.TransferMatrix
- **E/R/R.** _Elements:_ значения щели при beta=8 в разных размерностях: 0 (1+1D), 3/4 (2+1D), 15/16 (3+1D), 63/64 (d=3); стоимость доменной стенки domain_wall_cost(beta). _Roles:_ gap_formula(d) = роль-объединитель размерностей; монотонная лестница = роль-упорядочение; gershgorin_gap = роль-оценка (совпадает с точной при beta=8). _Rules:_ gap_formula: 0->0,1->3/4,2->15/16,3->63/64; strip_gap=gap_formula(1), 3D=gap_formula(2); монотонность 0<3/4<15/16<63/64. _P4:_ P4-консолидация: все размерностные щели — конечные рациональные Element-значения при ОДНОЙ точке beta=8; синтез лишь связывает уже вычисленные арены одной формулой, новой актуальности (вычисления) не порождая.
- **Classical counterpart.** Mirrors the textbook picture that the strong-coupling lattice mass gap grows with spatial dimension (more neighbors => larger plaquette/wall cost) and the Peierls domain-wall argument for confinement. NEW only as a bookkeeping unification: it gathers the project's own beta=8 gap values 0 (1+1D), 3/4 (2+1D), 15/16 (3+1D) under one gap_formula(d)=1-(1/4)^{...} pattern and proves the monotone ladder — a consolidation of imported facts, zero new mathematics.
- **Tags.** gauge, yang-mills, strip, synthesis, domain-walls, dimension-ladder, spectral-gap, beta=8, consolidation, exposition
- **Notes.** Actual Qed.=21 (= 21 top-level declarations, all are Theorem/Lemma; no Definitions). STATUS header says '~30 Qed' — overstated; real count is 21.

**Lemmas (21):**

| name | kind | role |
|---|---|---|
| `domain_wall_argument` | Theorem | доменно-стеночный довод в одном утверждении (дихотомия d, дихотомия eig, щель 3/4, щель>0) |
| `locality_of_excitations` | Theorem | локальность: wall_cost(8)=3/4, N-независимость, минимум возбуждения = 1 стенка |
| `all_gaps_summary` | Theorem | ★ сводка щелей: 1+1D=0, 2+1D=3/4 (двумя путями), 3+1D=15/16 |
| `strip_matches_gap2d` | Theorem | strip_gap_at_8 == mass_gap_2d_at_8 (два определения 2+1D совпадают) |
| `strip_exceeds_1d` | Theorem | mass_gap_2x2(8)=0 < strip_gap_at_8 |
| `gap_3d_exceeds_strip` | Theorem | strip_gap_at_8 < mass_gap_3d_at_8 |
| `gap_monotonicity` | Theorem | 1+1D < 2+1D < 3+1D |
| `gap_formula_check` | Theorem | gap_formula 0/1/2/3 == 0,3/4,15/16,63/64 |
| `strip_gap_is_formula_1` | Theorem | strip_gap_at_8 == gap_formula 1 |
| `gap_3d_is_formula_2` | Theorem | mass_gap_3d_at_8 == gap_formula 2 |
| `gap_formula_positive_1` | Lemma | 0 < gap_formula 1 |
| `gap_formula_positive_2` | Lemma | 0 < gap_formula 2 |
| `gap_formula_positive_3` | Lemma | 0 < gap_formula 3 |
| `gap_formula_monotone` | Theorem | gap_formula строго растёт по размерности 0<1<2<3 |
| `thermodynamic_limit_strip` | Theorem | щель>0, N-независима, Peierls-оценка>0 |
| `wall_cost_range` | Theorem | domain_wall_cost(2,4,8)=15/64,7/16,3/4, все >0 |
| `all_dimensions_gapped` | Theorem | все размерности имеют щель>0 при beta=8 |
| `gershgorin_recovers_exact` | Theorem | при beta=8 Gershgorin-оценка == точная wall_cost (alpha=0) |
| `diagonal_structure` | Theorem | при beta=8 off-diagonal=0 и alpha_2d(8)=0 (матрица диагональна) |
| `gap_complement_invariant` | Theorem | комплемент сохраняет eig, стенки и transfer-матрицу (Z2) |
| `strip_geometry_main` | Theorem | ★ ГЛАВНЫЙ синтез: щель=3/4 для всех N, =Gap2D, лестница 0<3/4<15/16, =gap_formula(1,2), все>0 |

**Key lemmas (deep):**

- **`strip_geometry_main`** - Капстоун-конъюнкция всей strip-ветки: щель=3/4 для всех N, совпадает с Gap2D, упорядочена в лестницу 0<3/4<15/16, отождествлена с gap_formula(1)/(2), и все щели положительны. Содержательно — чистая сборка уже доказанных в импортируемых файлах фактов через reflexivity/lra над точными Q; новой математики ноль. Ценность чисто организационная (спина соответствующей главы), уровень — синтез-как-бухгалтерия, не теорема. _(capstone, synthesis, consolidation, dimension-ladder)_
- **`all_gaps_summary`** - Сводит четыре числа в одну таблицу: 1+1D gap=0 (gap_vanishes_at_8), 2+1D=3/4 (двумя независимыми путями: strip-спектр и Gap2D), 3+1D=15/16. Это наблюдение 'размерность поднимает щель' в виде точных рациональных значений при beta=8. Честно: все четыре — конкретные вычисления при ОДНОЙ связи; растущая лестница иллюстративна, не выведена как функция непрерывной размерности или beta. _(summary, dimension-comparison, exact-rational)_

**Uniqueness - score 1 (exposition).** Сводит доменно-стеночные mass-gap-значения при beta=8 по размерностям (0, 3/4, 15/16, 63/64) под один gap_formula(d) и доказывает монотонную лестницу — единое экспозиционное полотно strip+dimension ветки.
> _Caveat:_ НЕ Yang-Mills mass gap (Clay) и НЕ доказательство роста щели с размерностью в общем виде. Чистая консолидация, 0 нового содержания: все теоремы — reflexivity/lra над фактами из импортируемых файлов, при ОДНОЙ точке beta=8 (alpha=0, диагональная матрица). 'Лестница размерностей' — четыре конкретных рациональных значения, не функция непрерывной размерности; gap_formula лишь подогнана под них. Доменно-стеночный/Peierls/Gershgorin аппарат классичен.

---

## #500 - `src/gauge/StripTransfer.v` - score 2 (methods)

**N x 1 strip transfer matrix over Q: T = w(s)*alpha^{Hamming}*w(s'); diagonal at beta=8**

- **Topic.** Builds the N x 1 strip transfer matrix entry strip_transfer(beta,s,s') = strip_weight(s) * alpha_pow(Hamming(s,s')) * strip_weight(s') with strip_weight = gamma^{domain walls}, and proves that at beta=8 (alpha=0) the off-diagonal entries vanish (Hamming>=1 between distinct equal-length strings) so the matrix is diagonal, with full complement (Z2) symmetry.
- **Role.** Foundational plumbing for the strip branch: defines strip_weight, gamma_pow, alpha_pow, strip_transfer consumed by gauge.StripSpectrum (eigenvalues) and gauge.StripSynthesis (diagonal_structure, complement). Imports gauge.DomainWalls (domain_walls, hamming_dist, complement, gamma_2d, alpha_2d, gamma_at_8, alpha_at_8), gauge.Coupled2D.
- **Counts.** Qed 33 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa List Bool; gauge.DomainWalls; gauge.Coupled2D
- **E/R/R.** _Elements:_ битовые строки-состояния s,s' (list bool); веса strip_weight(s)=gamma^{d(s)}; расстояние Хэмминга; конкретные матричные элементы N=1,2. _Roles:_ strip_transfer = роль-матричный-элемент (пространственный вес x временная связь^Hamming x вес); off-diagonal = роль-связь; diagonal = роль-вырождение при beta=8. _Rules:_ T(s,s')=w(s)*alpha^{Hamming(s,s')}*w(s'); при beta=8 alpha=0 => alpha^{n>=1}=0 => off-diagonal=0; комплемент сохраняет стенки и Хэмминг => T инвариантна. _P4:_ P4-плита: матрица определена на КОНЕЧНОМ множестве битовых строк фиксированной длины (Element-арена 2^N x 2^N); при beta=8 связь обнуляется и арена распадается на диагональ — конечно-актуальный объект, на котором StripSpectrum затем считает спектр.
- **Classical counterpart.** Mirrors the construction of a 2D classical-spin / lattice-gauge column transfer matrix T(s,s') = w(s) * (temporal coupling)^{Hamming distance} * w(s') with spatial weight w(s)=gamma^{domain walls}, and its decoupling (alpha->0) limit where T becomes diagonal. Standard statistical-mechanics transfer-matrix machinery; NEW only as the explicit ToS encoding over Q with bit-string states and the machine-checked diagonalization-at-beta=8 plus complement (Z2) symmetry.
- **Tags.** gauge, yang-mills, strip, transfer-matrix, domain-walls, hamming, beta=8, diagonalization, Z2-symmetry, infrastructure, P4
- **Notes.** Actual Qed.=33 (36 top-level declarations: 2 Fixpoints gamma_pow/alpha_pow + 2 Definitions strip_weight/strip_transfer are non-Qed; remaining proofs total 33 by grep). STATUS header says '~38 Qed' — overstated; real count is 33. Admitted=0 BUT the SUMMARY comment says '0 Admitted (1 Admitted pending reversal symmetry)': the general reversal symmetry is genuinely NOT proved — only the concrete cases rev_walls_2 (N=2) and rev_walls_3 (N=3) are.

**Lemmas (36):**

| name | kind | role |
|---|---|---|
| `gamma_pow` | Fixpoint | степень gamma_2d(beta)^n (пространственный вес) |
| `strip_weight` | Definition | вес состояния w(s)=gamma_pow(beta, domain_walls s) |
| `gamma_pow_0` | Lemma | gamma_pow beta 0 == 1 |
| `gamma_pow_1` | Lemma | gamma_pow beta 1 == gamma_2d beta |
| `gamma_pow_at_8_0` | Lemma | gamma_pow 8 0 == 1 |
| `gamma_pow_at_8_1` | Lemma | gamma_pow 8 1 == 1/2 |
| `gamma_pow_at_8_2` | Lemma | gamma_pow 8 2 == 1/4 |
| `strip_weight_ground` | Lemma | w(all_false n)==1 (d=0) |
| `strip_weight_ground_true` | Lemma | w(all_true n)==1 (d=0) |
| `strip_weight_d1` | Lemma | d=1 => w==gamma_2d beta |
| `strip_weight_at_8_d0` | Lemma | beta=8, d=0 => w==1 |
| `strip_weight_at_8_d1` | Lemma | beta=8, d=1 => w==1/2 |
| `strip_weight_at_8_d2` | Lemma | beta=8, d=2 => w==1/4 |
| `alpha_pow` | Fixpoint | степень alpha_2d(beta)^n (временная связь) |
| `alpha_pow_0` | Lemma | alpha_pow beta 0 == 1 |
| `alpha_pow_at_8_0` | Lemma | alpha_pow 8 0 == 1 |
| `alpha_at_8_zero` | Lemma | alpha_2d 8 == 0 (re-export alpha_at_8) |
| `alpha_pow_at_8_pos` | Lemma | ★ beta=8, n>=1 => alpha_pow==0 (обнуление связи) |
| `strip_transfer` | Definition | ★ элемент матрицы = w(s)*alpha^{Hamming(s,s')}*w(s') |
| `hamming_pos_neq` | Lemma | ★ s≠s' равной длины => Hamming>=1 (индукция по строкам) |
| `strip_diagonal_at_8` | Theorem | ★ beta=8: off-diagonal элемент == 0 (матрица диагональна) |
| `strip_diag_at_8` | Theorem | диагональный элемент T(s,s)==w(s)^2 (Hamming=0) |
| `strip_n1_same` | Theorem | N=1: T([b],[b])==1 |
| `strip_n1_diff` | Theorem | N=1: T([b],[negb b])==alpha_2d beta |
| `strip_n2_00_00` | Lemma | N=2: T(00,00)==1 |
| `strip_n2_00_01` | Lemma | N=2: T(00,01)==alpha*gamma |
| `strip_n2_00_10` | Lemma | N=2: T(00,10)==alpha*gamma |
| `strip_n2_00_11` | Lemma | N=2: T(00,11)==alpha^2 |
| `strip_n2_at_8` | Theorem | N=2 при beta=8 диагональна: {1,0,0,0} в строке 0 |
| `hamming_complement` | Lemma | Hamming(compl s, compl s')==Hamming(s,s') |
| `strip_complement_sym` | Theorem | ★ T(compl s, compl s')==T(s,s') (Z2-симметрия) |
| `rev_walls_2` | Lemma | разворот сохраняет стенки — ТОЛЬКО конкретный случай N=2 |
| `rev_walls_3` | Lemma | разворот сохраняет стенки — ТОЛЬКО конкретный случай N=3 |
| `gamma_pow_nonneg` | Lemma | gamma_pow>=0 для beta in (0,16) |
| `strip_weight_nonneg` | Lemma | w(s)>=0 для beta in (0,16) |
| `strip_transfer_at_8_nonneg` | Lemma | T(s,s)>=0 при beta=8 |

**Key lemmas (deep):**

- **`strip_diagonal_at_8`** - Несущая теорема файла: при beta=8 любой ВНЕдиагональный элемент равен 0. Опирается на hamming_pos_neq (различные строки равной длины отличаются хотя бы в одной позиции => Hamming>=1) и alpha_pow_at_8_pos (alpha=0 при beta=8 => alpha^{>=1}=0). Так конечная 2^N x 2^N матрица распадается в диагональ — ровно тот факт, который StripSpectrum использует, чтобы прочитать собственные значения прямо с диагонали. Классическая декуплировка transfer-матрицы при alpha->0, аккуратно проведённая над Q на битовых строках. _(diagonalization, transfer-matrix, beta=8, load-bearing)_
- **`hamming_pos_neq`** - Структурная лемма, делающая диагонализацию строгой: индукцией по двум строкам равной длины показывает, что неравные строки имеют Hamming>=1 (аккуратный разбор bdiff/eqb по позициям). Без неё 'off-diagonal' было бы определено нечётко. Чистая комбинаторика списков, но именно она превращает alpha=0 в зануление ВСЕХ внедиагональных элементов. _(hamming, list-induction, combinatorics)_
- **`strip_complement_sym`** - Z2 (глобальный flip) симметрия матрицы: T(compl s, compl s')==T(s,s'), т.к. комплемент сохраняет и число доменных стенок (complement_preserves_walls), и расстояние Хэмминга (hamming_complement). Содержательно — корректная, но стандартная симметрия Изинг-подобной модели; StripSynthesis поднимает её в gap_complement_invariant. _(Z2-symmetry, complement, invariance)_

**Uniqueness - score 2 (methods).** Точное Q-кодирование N x 1 strip transfer-матрицы на битовых строках с машинно-проверенной диагонализацией при beta=8 (off-diagonal=0 через Hamming>=1 и alpha=0) и Z2-симметрией комплемента — плита под спектральный расчёт StripSpectrum.
> _Caveat:_ НЕ Yang-Mills mass gap (Clay). Это инфраструктура statistical-mechanics transfer-матрицы (классическая конструкция w*alpha^Hamming*w и её alpha->0 декуплировка), просто аккуратно проведённая над Q. Диагонализация доказана ТОЛЬКО при beta=8; вне этой точки спектр не извлекается. Заголовочный комментарий обещает '~38 Qed, 0 Admitted (1 Admitted pending reversal symmetry)' — реальных Admitted 0, НО общая reversal-симметрия НЕ доказана: rev_walls_2/rev_walls_3 закрывают лишь конкретные N=2/N=3. N=1,2 элементы — vm_compute.

---

## #501 - `src/gauge/StrongCoupling.v` - score 2 (methods)

**Strong-coupling SU(2): string tension σ=3/(4β)>0, Wilson area law, and the honest σ→0 limitation**

- **Topic.** At small β (strong coupling) SU(2) confines: defines string tension σ=3/(4β), proves it positive, bounds the Wilson loop by (1-σ)^Area with exponential decay, and PROVES that σ vanishes as β→∞ — so strong coupling alone cannot yield a continuum gap.
- **Role.** Strong-coupling layer of the SU(2) mass-gap stack. Imports gauge.SU2Group/SU2Lattice/SU2TransferMatrix/TransferMatrix and reuses su2_mass_gap, su2_strong_coupling_gap, su2_mass_gap_positive, su2_continuum_limit from SU2TransferMatrix. Reused by gauge.SU2Synthesis (string_tension_verified, strong_coupling_main).
- **Counts.** Qed 20 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs List Lia ZArith Lqa; ToS: LinearAlgebra CauchyReal SeriesConvergence MonotoneConvergence; gauge: LatticeStructure GaugeField SU2Group SU2Lattice SU2TransferMatrix TransferMatrix
- **E/R/R.** _Elements:_ конкретное число β (обратная связь), рациональное σ=3/(4β), степени Qpow r^area (площадь петли Вильсона как nat). _Roles:_ σ = роль «натяжение струны» (мера конфайнмента); su2_mass_gap β = роль-щель; (1-σ)^A = роль-оценка петли. _Rules:_ σ положительно при β>0; петля убывает с площадью при 0≤r≤1; правило масштаба σ(cβ)=σ(β)/c; стена-ограничение: σ→0 при β→∞. _P4:_ Element-сторона честна: при каждом КОНКРЕТНОМ β<8 щель вычислима и положительна (vm_compute-факты gap_positive_at_1/2/4), но континуум β→∞ — НЕ достижимая точка (σ→0), поэтому сильная связь сама по себе не доказывает континуальную щель — это явный role-limit, заявленный теоремой strong_coupling_limitation.
- **Classical counterpart.** Wilson's strong-coupling (high-temperature) expansion of lattice gauge theory: confinement with area-law Wilson loop and string tension σ~ -log(1/(4β)) at leading order (Wilson 1974). What differs here: σ fixed at the leading rational σ=3/(4β) over Q (no series resummation), the area law is a Qpow monotonicity bound rather than an analytic estimate, and the σ→0 weak-coupling breakdown is PROVED as an explicit theorem (strong_coupling_limitation) rather than discussed.
- **Tags.** gauge, su2, yang-mills, confinement, wilson-loop, string-tension, strong-coupling, honest-limitation, rational-lattice
- **Notes.** Header STATUS says '~22 Qed'; actual Qed count = 21 (end-marker total_count asserts 22=22, off by one). 0 Admitted, 0 own axioms. Depends on su2_mass_gap / su2_continuum_limit defined in gauge/SU2TransferMatrix.v (not catalogued here).

**Lemmas (23):**

| name | kind | role |
|---|---|---|
| `string_tension` | Definition | натяжение струны σ(β)=3·(1/4)·/β |
| `string_tension_positive` | Lemma | β>0 ⟹ σ(β)>0 (конфайнмент при сильной связи) |
| `string_tension_at_1` | Lemma | σ(1)=3/4 (конкретное значение) |
| `string_tension_at_2` | Lemma | σ(2)=3/8 |
| `string_tension_at_4` | Lemma | σ(4)=3/16 |
| `string_tension_scale` | Lemma | σ(c·β)=σ(β)·/c для c,β>0 (масштабирование) |
| `su2_confinement_strong` | Theorem | 0<β≤1 ⟹ σ>0 ∧ щель≥3 (конфайнмент + щель) |
| `gap_exceeds_tension_at_1` | Lemma | σ(1)=3/4 < gap(1)=1575/256 (щель доминирует натяжение) |
| `gap_positive_at_1` | Lemma | 0<su2_mass_gap 1 (делегат к su2_mass_gap_positive) |
| `gap_positive_at_2` | Lemma | 0<su2_mass_gap 2 |
| `gap_positive_at_4` | Lemma | 0<su2_mass_gap 4 |
| `wilson_loop_bound` | Definition | оценка петли Вильсона = Qpow r area |
| `wilson_loop_at_1` | Lemma | при r=1/4, area=1 оценка =1/4 |
| `wilson_loop_nonneg` | Lemma | 0≤r ⟹ оценка ≥0 |
| `wilson_loop_decay` | Lemma | 0≤r≤1 ⟹ оценка убывает с ростом площади |
| `wilson_loop_area_law` | Lemma | ★ закон площади: 0≤r≤1 ⟹ оценка ≤1 (экспоненциальное затухание) |
| `wilson_loop_vanish` | Lemma | 0<r<1 ⟹ для любого eps найдётся N с оценкой <eps |
| `string_tension_vanishes` | Theorem | ★ σ исчезает: для любого eps>0 есть β>0 с σ(β)<eps (β=1/eps) |
| `strong_coupling_limitation` | Theorem | ★ ЧЕСТНАЯ стена: σ исчезает, НО щель>0 при каждом β<8 — сильной связи мало для континуума |
| `gap_at_rg_fixed_point` | Lemma | 0<su2_mass_gap 3 (щель на RG-неподвижной точке β=3) |
| `strong_coupling_summary` | Theorem | сводка: σ>0 ∧ щель≥3 при β≤1 ∧ закон площади ∧ «континуум-предел» |
| `strong_coupling_main` | Theorem | главная: σ>0 для всех β>0 ∧ щель>0 при β<8 |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`strong_coupling_limitation`** - Самая ценная теорема файла, потому что она ОТРИЦАЕТ собственную ветку: σ(β)=3/(4β) исчезает при β→∞ (string_tension_vanishes), значит положительность натяжения при каждом конечном β НЕ переносится на континуум. Конъюнкт «щель>0 при каждом β<8» вычислителен (su2_mass_gap_positive на конкретной решётке), а не континуальный предел. Это образцовая P4-честность: разрешено говорить о каждом Element-β, запрещено реифицировать недостижимый β→∞ в доказательство щели. Классический аналог — сильно-связное разложение Вильсона/Оско (область конфайнмента), хорошо известное; ново лишь рациональная Q-форма + явная теорема-ограничение. _(confinement, strong-coupling, honest-limitation, P4, role-limit)_
- **`string_tension_vanishes`** - Конструктивный свидетель β=1/eps даёт σ=3·eps/4<eps: это машинная форма факта «при слабой связи струна растворяется». Здесь и лежит точка, где сильно-связный конфайнмент перестаёт быть инструментом для континуальной щели — мост к необходимости RG-потока (RGFlow.v). Полностью классично по содержанию; формализация — Q-арифметика + Qinv_involutive. _(limit, weak-coupling, witness)_

**Uniqueness - score 2 (methods).** Рациональная (Q) формализация сильно-связного конфайнмента SU(2): положительное натяжение, закон площади петли Вильсона как Qpow-монотонность, и — главное — машинно-доказанная честная стена σ→0, отделяющая конечно-β конфайнмент от континуальной щели.
> _Caveat:_ Содержание полностью классично (разложение Вильсона по сильной связи, закон площади). НЕ доказывает Clay-щель: σ=3/(4β) — лишь ведущий рациональный порядок, σ→0 при β→∞; «континуум-предел» в strong_coupling_summary — это лишь существование β<8 с малой щелью на ФИКСИРОВАННОЙ малой решётке (через SU2TransferMatrix), а не континуальный предел. Заголовок «~22 Qed» завышен: фактически 21.

---

## #502 - `src/gauge/SU2Characters.v` - score 2 (methods)

**SU(2) characters via Chebyshev U_n over Q; integer-coeff irreps, structural Haar orthogonality**

- **Topic.** Exact representation theory of SU(2) over Q: Chebyshev polynomials of the second kind U_n give the characters χ_j=U_{2j} (in c=cosθ), with χ_j(1)=2j+1 (dimension) and χ_j(0)=(-1)^j. Orthogonality is rendered STRUCTURALLY (different j give different frequency 2j+1) rather than as an actual integral.
- **Role.** Representation-theory leaf of the gauge cluster. Self-contained (only imports CauchyReal, SeriesConvergence); no other catalogued gauge file imports it. Provides the character/orthogonality vocabulary used informally by the character-expansion / heat-kernel narrative.
- **Counts.** Qed 38 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: CauchyReal SeriesConvergence
- **E/R/R.** _Elements:_ конкретный рациональный c=cosθ, многочлены Чебышёва U_n(c) с ЦЕЛЫМИ коэффициентами, рациональные моменты ∫c^k(1-c²). _Roles:_ χ_j = роль «характер неприводимого представления спина j»; χ_j(1)=2j+1 = роль-размерность; haar_norm = роль-нормировка. _Rules:_ рекуррента U_{n+2}=2c·U_{n+1}-U_n; χ_j=U_{2j}; ортогональность кодируется как j≠k ⟹ 2j+1≠2k+1; чётные моменты 4/((k+1)(k+3)), нечётные =0. _P4:_ Element-сторона представлена честно (характеры — многочлены с целыми коэффициентами, всё вычислимо над Q), но НАСТОЯЩАЯ ортогональность (интеграл по мере Хаара) НЕ построена: она заменена арифметическим прокси «разные частоты», т.е. интегральная роль-сторона остаётся вне Q-формализации.
- **Classical counterpart.** Classical SU(2) character theory: χ_j(θ)=sin((2j+1)θ)/sinθ = U_{2j}(cosθ) (Chebyshev 2nd kind), dim=2j+1, and Peter-Weyl/Weyl orthogonality ∫_0^π χ_j χ_k (2/π)sin²θ dθ = δ_{jk}. What differs here: characters are exact Q-polynomials (integer coefficients) with no transcendental θ; orthogonality is NOT integrated — it is replaced by the arithmetic proxy '2j+1 ≠ 2k+1', and haar_norm is a rational stand-in 1/(2j+1) for π/2, so the actual Haar integral and Peter-Weyl completeness are not formalized.
- **Tags.** gauge, su2, characters, chebyshev, representation-theory, haar, orthogonality-proxy, exact-Q
- **Notes.** Header STATUS says '~40 Qed'; actual Qed count = 38. 0 Admitted, 0 own axioms. Honesty flag: lemmas named cross_integral_zero / self_integral_positive do NOT compute integrals — they are arithmetic frequency/positivity proxies for unformalized Haar integrals; haar_norm is a rational stand-in for π/2.

**Lemmas (44):**

| name | kind | role |
|---|---|---|
| `chebyshev_U` | Fixpoint | многочлены Чебышёва 2-го рода U_n(c): U_0=1, U_1=2c, U_{n+2}=2c·U_{n+1}-U_n |
| `U_0` | Lemma | U_0(c)=1 |
| `U_1` | Lemma | U_1(c)=2c |
| `U_2` | Lemma | U_2(c)=4c²-1 |
| `U_3` | Lemma | U_3(c)=8c³-4c |
| `U_4` | Lemma | U_4(c)=16c⁴-12c²+1 |
| `chebyshev_recurrence` | Theorem | рекуррентное соотношение U_{n+2}=2c·U_{n+1}-U_n (общее n) |
| `U_at_1_0` | Lemma | U_0(1)=1 |
| `U_at_1_1` | Lemma | U_1(1)=2 |
| `U_at_1_2` | Lemma | U_2(1)=3 |
| `U_at_1_3` | Lemma | U_3(1)=4 |
| `U_at_1_4` | Lemma | U_4(1)=5 (U_n(1)=n+1) |
| `U_at_0_0` | Lemma | U_0(0)=1 |
| `U_at_0_1` | Lemma | U_1(0)=0 |
| `U_at_0_2` | Lemma | U_2(0)=-1 |
| `U_at_0_3` | Lemma | U_3(0)=0 |
| `U_at_0_4` | Lemma | U_4(0)=1 |
| `su2_character` | Definition | характер SU(2) спина j: χ_j(c)=U_{2j}(c) |
| `chi_0` | Lemma | χ_0(c)=1 |
| `chi_1` | Lemma | χ_1(c)=4c²-1 |
| `chi_2` | Lemma | χ_2(c)=16c⁴-12c²+1 |
| `chi_at_1_0` | Lemma | χ_0(1)=1 (размерность 1) |
| `chi_at_1_1` | Lemma | χ_1(1)=3 (размерность 3) |
| `chi_at_1_2` | Lemma | χ_2(1)=5 (размерность 2j+1=5) |
| `character_rational` | Lemma | χ_j(c) рационально для рационального c (это num#den) |
| `chi_at_0_0` | Lemma | χ_0(0)=1 |
| `chi_at_0_1` | Lemma | χ_1(0)=-1 |
| `chi_at_0_2` | Lemma | χ_2(0)=1 (χ_j(0)=(-1)^j) |
| `orthogonal_reps` | Definition | ортогональность представлений: j≠k ⟹ 2j+1≠2k+1 (прокси) |
| `orthogonal_reps_holds` | Theorem | j≠k ⟹ orthogonal_reps j k (через lia) |
| `haar_norm` | Definition | нормировка Хаара (рац. прокси) =1/(2j+1) |
| `haar_norm_pos` | Lemma | haar_norm j>0 (положительность нормы) |
| `self_integral_positive` | Lemma | интеграл j=k положителен (=haar_norm_pos) |
| `cross_integral_zero` | Theorem | ★ кросс-интеграл j≠k обнуляется (структурно: 2j+1≠2k+1) |
| `character_expansion_exists` | Definition | Питер-Вейль: коэффициенты разложения вычислимы (каждый haar_norm рационален) |
| `character_expansion_computable` | Theorem | character_expansion_exists выполнено |
| `weighted_moment` | Definition | взвешенный момент ∫c^k(1-c²): чётный 4/((k+1)(k+3)), нечётный 0 |
| `wm_0` | Lemma | момент(0)=4/3 |
| `wm_2` | Lemma | момент(2)=4/15 |
| `wm_4` | Lemma | момент(4)=4/35 |
| `wm_odd` | Lemma | момент(2k+1)=0 (нечётные обнуляются) |
| `inject_Z_of_nat_pos` | Lemma | 1≤n ⟹ inject_Z(Z.of_nat n)>0 (вспомогательная) |
| `wm_nonneg` | Lemma | момент(k)≥0 для всех k |
| `su2_characters_summary` | Theorem | сводка: характеры вычислимы ∧ ортогональность ∧ норма>0 ∧ моменты≥0 ∧ разложение вычислимо |

**Key lemmas (deep):**

- **`chebyshev_recurrence`** - Несущая лемма: рекуррента U_{n+2}=2c·U_{n+1}-U_n определяет ВСЕ характеры χ_j=U_{2j} как многочлены с целыми коэффициентами над Q. Это и есть Element-сторона теории представлений SU(2): неприводимые характеры вычислимы точной рациональной арифметикой, χ_j(1)=2j+1 (размерность), χ_j(0)=(-1)^j. Классика (характеры SU(2) суть многочлены Чебышёва 2-го рода); ценность файла — что вся таблица характеров живёт над Q без аппроксимаций. _(chebyshev, representation-theory, exact-Q, dimension)_
- **`cross_integral_zero`** - Здесь — самая слабая (и честно слабая) точка файла: «ортогональность характеров» сведена к арифметическому факту j≠k ⟹ 2j+1≠2k+1 (доказательство — одна lia), а НЕ к интегралу ∫χ_j·χ_k·dμ=δ_{jk}. Комментарии явно выводят тригонометрию sin(aθ)sin(bθ), но мера Хаара и интеграл не формализованы. Это типичный «structural proxy»: настоящая ортогональность (роль-сторона, требующая интеграла/предела) вынесена за скобки, заменена счётом частот. Отметить как лёгкое over-stating в самих именах cross_integral_zero / self_integral_positive — они называются интегралами, но интегралов не содержат. _(orthogonality, proxy, haar, over-stated-name)_

**Uniqueness - score 2 (methods).** Точная Q-формализация таблицы характеров SU(2) через многочлены Чебышёва 2-го рода (целые коэффициенты, размерность 2j+1, значения в c=0,1), плюс рациональные взвешенные моменты ∫c^k(1-c²).
> _Caveat:_ Содержание — классическая теория представлений SU(2) (характеры = Чебышёв U_n). Ортогональность НЕ доказана как интеграл: cross_integral_zero/self_integral_positive — арифметические прокси (j≠k⟹2j+1≠2k+1; норма =1/(2j+1) вместо π/2), мера Хаара и Питер-Вейль не формализованы — имена «integral» завышены. Заголовок «~40 Qed» завышен: фактически 38.

---

## #503 - `src/gauge/SU2Group.v` - score 2 (methods)

**SU(2) as unit quaternions over Q: associativity, Euler four-square norm, non-commutativity, cyclic trace**

- **Topic.** Builds SU(2)≅unit quaternions as a Q⁴ Record with quaternion product, and proves the group structure: associativity, identity, conjugate-inverse, the Euler four-square identity |pq|²=|p|²|q|², closure of units, genuine non-commutativity (ij=k≠-k=ji), and the cyclic trace tr(pq)=tr(qp).
- **Role.** Group-theory foundation of the entire SU(2) gauge stack. Pure rational arithmetic, no ToS imports. Reused by gauge.SU2Lattice (Quaternion, qmul, qconj, qnorm_sq, is_unit, unit_closed, qmul_noncommutative, trace_cyclic), SU2TransferMatrix, StrongCoupling, SU2Synthesis.
- **Counts.** Qed 29 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs List Lia ZArith Lqa
- **E/R/R.** _Elements:_ кватернион = запись mkQ4 из четырёх рациональных компонент (q0,q1,q2,q3)∈Q⁴; единица qid; образующие i,j,k. _Roles:_ qmul = роль группового умножения (некоммутативного!); qconj = роль обращения для единичных; qnorm_sq = роль нормы; qtrace=2q0 = роль следа (калибровочно-инвариантный). _Rules:_ формула произведения кватернионов; \|q\|²=Σqᵢ²; ассоциативность (ring); \|pq\|²=\|p\|²\|q\|² (Эйлер 4 квадрата); единичные замкнуты; tr(pq)=tr(qp). _P4:_ Чисто Element-объект: каждый кватернион — конкретная четвёрка рациональных чисел, все групповые тождества — финитные ring-проверки; единичность is_unit q == 1 берётся как равенство-условие (а не точка на сфере), поэтому реальная компактная группа SU(2) (континуум) НЕ строится — формализована лишь её рациональная алгебраическая оболочка.
- **Classical counterpart.** Classical SU(2)≅Sp(1)=unit quaternions (Hamilton 1843): quaternion algebra, multiplicative norm = Euler's four-square identity (Euler 1748), non-commutativity ij=-ji=k, and cyclicity of the matrix trace. What differs here: everything is over Q (components in Q⁴, no completeness), 'is_unit' is the algebraic equation \|q\|²==1 rather than a point of the real 3-sphere, so this formalizes the rational quaternion *-algebra and its unit-group laws, not the compact Lie group SU(2) as a topological/continuum object.
- **Tags.** gauge, su2, quaternion, non-abelian, euler-four-square, trace-cyclic, group-theory, exact-Q, foundation
- **Notes.** Header STATUS says '~30 Qed'; actual Qed count = 30 (matches). 0 Admitted, 0 own axioms. Foundational file for the SU(2) gauge cluster — defines Quaternion and all its operations reused downstream.

**Lemmas (45):**

| name | kind | role |
|---|---|---|
| `Quaternion` | Record | тип кватерниона: {q0;q1;q2;q3}∈Q⁴ |
| `qeq` | Definition | покомпонентное равенство кватернионов |
| `qmul` | Definition | умножение кватернионов (формула Гамильтона) |
| `qid` | Definition | единица mkQ4 1 0 0 0 |
| `qconj` | Definition | сопряжение q̄=(q0,-q1,-q2,-q3) |
| `qnorm_sq` | Definition | квадрат нормы \|q\|²=q0²+q1²+q2²+q3² |
| `qadd` | Definition | сложение кватернионов |
| `qscale` | Definition | скалярное умножение |
| `qneg` | Definition | отрицание |
| `qtrace` | Definition | след как 2×2-матрицы: tr(q)=2q0 |
| `is_unit` | Definition | единичный кватернион: \|q\|²==1 |
| `near_id` | Definition | околоединичная параметризация mkQ4 1 (eps·a1) (eps·a2) (eps·a3) |
| `qeq_refl` | Lemma | рефлексивность qeq |
| `qeq_sym` | Lemma | симметричность qeq |
| `qeq_trans` | Lemma | транзитивность qeq |
| `qmul_id_l` | Lemma | левая единица qid·q=q |
| `qmul_id_r` | Lemma | правая единица q·qid=q |
| `qmul_assoc` | Theorem | ★ ассоциативность (главная групповая аксиома, ring) |
| `qmul_conj_r` | Lemma | q·q̄=\|q\|²·1 (обращение справа) |
| `qmul_conj_l` | Lemma | q̄·q=\|q\|²·1 (обращение слева) |
| `qconj_involutive` | Lemma | сопряжение инволютивно |
| `qnorm_sq_nonneg` | Lemma | \|q\|²≥0 (сумма квадратов) |
| `qnorm_mul` | Theorem | ★ тождество Эйлера 4 квадратов \|pq\|²=\|p\|²·\|q\|² (ring) |
| `unit_closed` | Theorem | ★ произведение единичных единично (замкнутость группы) |
| `qid_is_unit` | Lemma | единица единична |
| `qconj_is_unit` | Lemma | сопряжённый единичного единичен |
| `qnorm_sq_conj` | Lemma | \|q̄\|²=\|q\|² |
| `qi` | Definition | образующая i=(0,1,0,0) |
| `qj` | Definition | образующая j=(0,0,1,0) |
| `qk` | Definition | образующая k=(0,0,0,1) |
| `qmul_ij` | Lemma | i·j=k |
| `qmul_ji` | Lemma | j·i=-k |
| `qmul_noncommutative` | Theorem | ★ SU(2) некоммутативна: ∃p,q. pq≠qp (свидетели i,j) |
| `trace_cyclic` | Theorem | ★ цикличность следа tr(pq)=tr(qp) (ключ к калибр. инвариантности) |
| `qtrace_id` | Lemma | tr(qid)=2 |
| `qtrace_conj` | Lemma | tr(q̄)=tr(q) |
| `q0_id` | Lemma | q0(qid)=1 |
| `qadd_comm` | Lemma | сложение коммутативно |
| `qscale_zero` | Lemma | 0·q=ноль-кватернион |
| `qscale_one` | Lemma | 1·q=q |
| `near_id_at_zero` | Lemma | near_id 0 = qid |
| `near_id_norm_sq` | Lemma | \|near_id eps a\|²=1+eps²(a1²+a2²+a3²) |
| `q0_unit_sq_bound` | Lemma | единичный ⟹ q0²≤1 |
| `su2_group_summary` | Theorem | сводка групповых свойств (ассоц., единица, обращение, норма, некоммут., след, замкнутость) |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`qnorm_mul`** - Тождество Эйлера четырёх квадратов \|pq\|²=\|p\|²·\|q\|², доказанное одним ring над Q. Это математическое сердце SU(2): оно делает норму мультипликативной, откуда мгновенно следует замкнутость единичных кватернионов (unit_closed) — групповое свойство SU(2). Тождество классическое (Эйлер 1748, основа теоремы Лагранжа о 4 квадратах; ровно та же норм-форма, что в репозитории встречается в HurwitzTower/RationalQuaternions). Здесь оно играет роль E/R/R-правила: норма = роль, согласованная с умножением. _(euler-four-square, norm-multiplicative, group-closure)_
- **`qmul_noncommutative`** - Подлинная (не прокси) некоммутативность: ij=k, ji=-k, и q3-компоненты +1 vs -1 дают противоречие через lra. Это структурный водораздел gauge-программы — именно неабелевость отличает SU(2) от U(1) (повторяется в SU2Lattice как su2_three_generators). Классика теории кватернионов Гамильтона; ценность — что она зафиксирована как конкретный машинный факт, опирающий весь неабелев Wilson-каркас. _(non-abelian, quaternion, su2-vs-u1)_
- **`trace_cyclic`** - Цикличность следа tr(pq)=tr(qp) (через qtrace=2q0, ring). Это правило, обеспечивающее калибровочную инвариантность действия Вильсона: q0 плакетки инвариантен относительно сопряжения Ω·X·Ω⁻¹ (используется в SU2Lattice.q0_conjugation_unit). Классический факт линейной алгебры; здесь — несущий мост между алгеброй кватернионов и калибровочной инвариантностью решёточного действия. _(trace, cyclic, gauge-invariance, bridge)_

**Uniqueness - score 2 (methods).** Чистая рациональная (Q⁴) реализация SU(2) как единичных кватернионов с полным набором групповых тождеств машинной проверки: ассоциативность, мультипликативность нормы (Эйлер 4 квадрата), некоммутативность (i·j=k≠j·i), цикличность следа — несущее основание всего SU(2)-стека.
> _Caveat:_ Содержание классическое (алгебра кватернионов Гамильтона, тождество Эйлера 4 квадратов). Не строит компактную группу SU(2) как континуальный объект: is_unit — алгебраическое уравнение |q|²==1, а не точка 3-сферы; формализована рациональная *-алгебра и её групповые законы, не топология/мера. Та же норм-форма, что и в HurwitzTower/RationalQuaternions цикла finitization. Заголовок и фактический счёт совпадают (30 Qed).

---

## #504 - `src/gauge/SU2Lattice.v` - score 2 (methods)

**Non-abelian SU(2) gauge field on the lattice: quaternion plaquette, Wilson action, q0-level gauge invariance**

- **Topic.** Puts a quaternion on each link, defines the ordered plaquette product U_P=U1·U2·conj(U3)·conj(U4) and the Wilson action S=β·Σ(1-q0(U_P)). Proves vacuum action 0, reflexive gauge equivalence, plaquette contribution ≥0, and the key gauge invariance at q0 level: q0(A·B·conj(A))=q0(B) for unit A.
- **Role.** Lattice layer of the SU(2) gauge stack. Imports gauge.LatticeStructure/GaugeField and gauge.SU2Group (Quaternion, qmul, qconj, is_unit, trace). Reused by gauge.SU2TransferMatrix and SU2Synthesis (q0_conjugation_unit appears in gauge_theory_structure).
- **Counts.** Qed 19 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs List Lia ZArith Lqa; ToS: LinearAlgebra CauchyReal; linalg: MatrixOps; gauge: LatticeStructure GaugeField SU2Group
- **E/R/R.** _Elements:_ конфигурация = функция link→Quaternion; плакетка = упорядоченное произведение 4 кватернионов; действие = рациональное число β·Σ(1-q0). _Roles:_ su2_plaquette = роль «локальная кривизна петли»; su2_wilson_action = роль действия; su2_gauge_transform = роль калибровочного преобразования Ω·g·Ω̄; q0 = роль (1/2)следа. _Rules:_ плакетка = U1·U2·U3̄·U4̄ (ПРОИЗВЕДЕНИЕ, не сумма — отличие от U(1)); действие масштабируется по β; калибр. инвариантность q0 через цикличность следа. _P4:_ Element-сторона: на конкретной конфигурации (нулевой/единичной) действие и плакетки вычислимы (vm_compute-подобные ring-факты); полная калибровочная инвариантность по ЗАМКНУТОЙ петле (телескопирование Ω) заявлена в комментарии, но доказан лишь ЛОКАЛЬНЫЙ шаг q0(A·B·Ā)=q0(B) — полное телескопирование по решётке не формализовано (P4: глобальная сумма по плакеткам не свёрнута).
- **Classical counterpart.** Classical lattice gauge theory (Wilson 1974): non-abelian gauge field assigns a group element to each link, the plaquette is the ordered product around an elementary square, the Wilson action is S=β Σ_P (1 - (1/N) Re tr U_P), and gauge invariance follows from trace cyclicity under U_l → Ω_s U_l Ω_t†. What differs here: the group is the rational unit-quaternion stand-in for SU(2), q0 plays the role of (1/2)tr, and gauge invariance is proved only LOCALLY (q0(A·B·Ā)=q0(B)) — the closed-loop telescoping of Ω-factors and the full action invariance are described in comments but not formalized; the lattice/plaquette geometry is delegated to gauge.LatticeStructure.
- **Tags.** gauge, su2, lattice, wilson-action, plaquette, non-abelian, gauge-invariance, quaternion, exact-Q
- **Notes.** Header STATUS says '~22 Qed'; actual Qed count = 20 (end-marker total_count asserts 22=22, off by two). 0 Admitted, 0 own axioms. Gauge invariance is local-only; full closed-loop invariance left as commentary.

**Lemmas (26):**

| name | kind | role |
|---|---|---|
| `SU2Config` | Definition | SU(2)-конфигурация: link→Quaternion |
| `su2_zero_config` | Definition | тривиальная конфигурация fun _ => qid |
| `su2_plaquette` | Definition | плакетка U_P=U1·U2·conj(U3)·conj(U4) |
| `su2_wilson_action` | Definition | действие Вильсона S=β·Σ_P(1-q0(U_P)) |
| `su2_gauge_transform` | Definition | калибр. преобразование g'(l)=Ω(s)·g(l)·conj(Ω(t)) |
| `su2_gauge_equivalent` | Definition | калибр. эквивалентность через ∃Ω |
| `su2_zero_plaquette` | Lemma | плакетка нулевой конфигурации = qid |
| `su2_action_at_vacuum` | Lemma | действие вакуума (нулевая конфиг.) =0 |
| `su2_gauge_transform_id` | Lemma | калибр. преобразование единицей = тождество |
| `su2_plaquette_at_id` | Lemma | q0 плакетки единичной конфиг. =1 |
| `su2_action_id_config` | Lemma | действие единичной конфиг. =0 (повтор) |
| `q0_cyclic` | Lemma | q0(pq)=q0(qp) — цикличность следа на уровне q0 |
| `q0_conjugation_unit` | Lemma | ★ для единичного A: q0(A·B·conj(A))=q0(B) (калибр. инвариантность) |
| `su2_gauge_equiv_refl` | Lemma | калибр. эквивалентность рефлексивна |
| `su2_action_scale_beta` | Lemma | S(c·β)=c·S(β) (масштаб по β) |
| `su2_three_generators` | Lemma | ★ SU(2) имеет 3 различных образующих i,j,k (vs 1 у U(1)) |
| `su2_dim` | Lemma | dim SU(2)=3 (заглушка 3=3) |
| `u1_dim` | Lemma | dim U(1)=1 (заглушка 1=1) |
| `su2_vs_u1` | Lemma | 1<3 (SU(2) строго богаче U(1)) |
| `q0_unit_bound` | Lemma | единичный ⟹ q0≤1 |
| `q0_unit_bound_neg` | Lemma | единичный ⟹ -1≤q0 |
| `plaq_contribution_nonneg` | Lemma | единичный ⟹ 1-q0≥0 (вклад плакетки неотрицателен) |
| `su2_config_ext` | Lemma | экстенсиональное равенство SU2Config (тривиальная переформулировка) |
| `su2_lattice_summary` | Theorem | сводка: вакуум-действие 0, эквив. рефлексивна, 3 образующих, q0 цикличен |
| `su2_gauge_invariance_main` | Theorem | ★ главная: калибр. инвариантность q0 (=q0_conjugation_unit) |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`q0_conjugation_unit`** - Несущая лемма файла: для единичного A выполняется q0(A·B·conj(A))=q0(B). Доказательство = цикличность (q0_cyclic) + подстановка \|A\|²=1 в развёрнутую формулу (один большой ring + rewrite). Это локальный носитель калибровочной инвариантности действия Вильсона: q0 плакетки не меняется при сопряжении Ω. Честно: это ЛОКАЛЬНЫЙ факт; полная инвариантность по замкнутой петле (телескопирование Ω(s1)·…·Ω(s1)⁻¹) лишь описана в комментарии, не доказана. Классический факт (калибр. инвариантность через цикличность следа), формализован рационально. _(gauge-invariance, trace-cyclic, wilson-action, local-only)_
- **`su2_three_generators`** - Машинная фиксация неабелевой размерности: i,j,k попарно различны (3 образующих) против 1 у U(1) — структурный водораздел между неабелевой SU(2) и абелевой U(1)-теорией. Опирается на qmul-некоммутативность из SU2Group. su2_dim/u1_dim/su2_vs_u1 — заглушки (3=3, 1=1, 1<3), несущая нагрузка — именно различимость образующих. Классика; ценность — что плакетка-как-ПРОИЗВЕДЕНИЕ (а не сумма U(1)) явно зафиксирована. _(non-abelian, generators, su2-vs-u1, dimension)_

**Uniqueness - score 2 (methods).** Рациональная решёточная реализация НЕабелева SU(2)-поля: плакетка как упорядоченное ПРОИЗВЕДЕНИЕ кватернионов (ключевое отличие от суммы U(1)), действие Вильсона S=β·Σ(1-q0), нулевое вакуум-действие и локальная калибровочная инвариантность q0 через цикличность следа.
> _Caveat:_ Содержание классическое (решёточная калибровочная теория Вильсона). Калибровочная инвариантность доказана лишь ЛОКАЛЬНО (q0(A·B·Ā)=q0(B)); телескопирование по замкнутой петле и инвариантность полного действия — только в комментариях, не формализованы. su2_dim/u1_dim — заглушки-тавтологии; геометрия плакеток вынесена в LatticeStructure. Заголовок «~22 Qed» завышен: фактически 20.

---

## #505 - `src/gauge/SU2Synthesis.v` - score 1 (exposition)

**SU(2) mass-gap synthesis: bundles non-abelian + finite-β gap + RG contraction; honestly marks the Millennium gap**

- **Topic.** Consolidation file gathering the SU(2) gauge results into combined theorems (yang_mills_progress, su2_synthesis_main): non-abelian, mass gap >0 for 0<β<8, RG linear map a contraction with fixed point β*=3, gap positive at the fixed point. Crucially also proves millennium_gap: the linearized RG ≠ the quadratic RG, explicitly stating what separates this from the Clay Prize.
- **Role.** Top capstone of the SU(2) gauge stack; pure re-export (0 new content). Imports the whole stack: gauge.SU2Group, SU2Lattice, SU2TransferMatrix, StrongCoupling, RGFlow, TransferMatrix + ToS.FixedPoint. Terminal — nothing in the catalogued gauge set imports it.
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs List Lia ZArith Lqa; ToS: LinearAlgebra CauchyReal FixedPoint; gauge: LatticeStructure GaugeField TransferMatrix SU2Group SU2Lattice SU2TransferMatrix StrongCoupling RGFlow
- **E/R/R.** _Elements:_ конкретные β∈(0,8) на фиксированной малой решётке; рациональная RG-карта rg_map_linear; неподвижная точка β*=3. _Roles:_ su2_mass_gap = роль-щель; is_contraction rg_map_linear = роль-сжатие (Банах); rg_fixed_point=3 = роль-аттрактор; «yang_mills_progress» = роль-сводка верифицированного. _Rules:_ все конъюнкты — переэкспорт ранее доказанного (qmul_noncommutative, su2_mass_gap_positive, su2_gap_vs_u1, rg_is_contraction, …); millennium_gap = правило-различение линейной и квадратичной RG. _P4:_ Образцовая P4-честность В САМОМ файле: millennium_gap доказывает, что линеаризованная RG ≠ настоящая (квадратичная) RG, т.е. явно отделяет верифицированное Element-содержание (щель при каждом β<8 на конечной решётке) от недостижимой континуальной задачи Clay; what_is_proved/millennium_gap фиксируют границу «что доказано / что открыто».
- **Classical counterpart.** Mirrors the strategy of the Yang-Mills existence-and-mass-gap problem (Jaffe-Witten Clay Millennium problem): a positive spectral gap surviving the continuum limit via renormalization-group flow to a fixed point. What differs — and is stated outright in the file: only a FINITE-β (0<β<8) gap on a fixed small lattice (transfer-matrix eigenvalue, gauge group = rational unit quaternions ≈ SU(2)), a LINEARIZED toy RG map shown to be a Banach contraction to β*=3, and millennium_gap PROVES this linear RG ≠ the true quadratic RG — so the continuum YM mass gap is explicitly NOT established.
- **Tags.** gauge, su2, yang-mills, mass-gap, synthesis, rg-flow, millennium, honest-limitation, aspirational-name, re-export
- **Notes.** Header STATUS says '~15 Qed'; actual Qed count = 13 (end-marker total_count, off by two). 0 Admitted, 0 own axioms. Over-branding: theorem names yang_mills_progress / su2_synthesis_main and the 'SU(2) SYNTHESIS' framing are aspirational — the file does NOT prove the Clay Yang-Mills mass gap; it re-exports finite-β lattice facts + a linearized toy RG, and millennium_gap honestly proves the linear RG differs from the true quadratic RG. Depends on su2_mass_gap/su2_gap_vs_u1/SU2TransferMatrix and rg_* from RGFlow (not catalogued here).

**Lemmas (13):**

| name | kind | role |
|---|---|---|
| `su2_is_nonabelian` | Theorem | SU(2) неабелева (=qmul_noncommutative) |
| `su2_mass_gap_exists` | Theorem | щель >0 при 0<β<8 (=su2_mass_gap_positive) |
| `su2_stronger_confinement` | Theorem | щель SU(2) > щели U(1) при β<8 (=su2_gap_vs_u1) |
| `string_tension_verified` | Theorem | натяжение струны >0 (=string_tension_positive) |
| `rg_contraction_verified` | Theorem | RG-карта — сжатие на [2,4] с коэф. 1/4 (=rg_is_contraction) |
| `rg_fixed_point_verified` | Theorem | f(3)=3 неподвижная точка (=rg_linear_fixed_point) |
| `gap_at_fp_verified` | Theorem | щель в неподвижной точке >0 (=su2_gap_at_fp_positive) |
| `yang_mills_progress` | Theorem | ★ сводка 6 верифицированных шагов (неабел.+щель+конфайн.+натяж.+сжатие+щель в т.) |
| `what_is_proved` | Theorem | что доказано: дискр. щель + сжатие + неподв. точка + сходимость итераций |
| `millennium_gap` | Theorem | ★ ЧЕСТНАЯ граница: линейная RG ≠ квадратичная RG (rg_map_linear≠rg_map_quadratic при β=0) |
| `gauge_theory_structure` | Theorem | структура: калибр. инвариантность + неабел. + замкнутость группы |
| `su2_synthesis_main` | Theorem | ★ главная сводка SU(2): неабел.+щель+сжатие/неподв.точка+щель в точке |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`millennium_gap`** - Самая важная теорема файла именно потому, что она ОТРИЦАЕТ полноту результата: ~(forall β, rg_map_linear β == rg_map_quadratic β), доказано контрпримером β=0 (где Qdiv даёт расхождение, lia). Это машинно зафиксированный честный разрыв с Clay-задачей: всё «yang_mills_progress» опирается на ЛИНЕАРИЗОВАННУЮ RG, а настоящая RG квадратична — поэтому континуальная щель НЕ доказана. Образец того, как файл с аспирационными именами (yang_mills_progress, su2_synthesis_main) сам встроил оговорку. Это не теорема о физике, а граница-разметка. _(honest-limitation, millennium, rg, P4, self-limiting)_
- **`yang_mills_progress`** - Капстоун-конъюнкция шести ранее доказанных фактов: неабелевость, щель>0 при 0<β<8, SU(2) сильнее U(1), натяжение>0, RG-сжатие, щель в неподвижной точке. ВСЕ конъюнкты — exact-переэкспорт (qmul_noncommutative, su2_mass_gap_positive, …); 0 нового содержания. Ценность — унификация в одну сводку, читаемую как «карта программы». ВАЖНО (честность кластера): имя «yang_mills_progress» аспирационно — это НЕ прогресс к континуальной щели Янга-Миллса, а сводка фактов о ФИКСИРОВАННОЙ малой решётке (щель через SU2TransferMatrix, ограничена β<8) плюс ЛИНЕАРИЗОВАННАЯ RG; контраст с реальной задачей зафиксирован соседней millennium_gap. _(synthesis, re-export, aspirational-name, finite-lattice)_

**Uniqueness - score 1 (exposition).** Чистая консолидация SU(2)-стека в сводные теоремы (yang_mills_progress, su2_synthesis_main) + редкая встроенная честность: millennium_gap машинно доказывает, что использованная линеаризованная RG ≠ настоящая квадратичная, явно размечая разрыв с Clay-задачей.
> _Caveat:_ 0 нового содержания — все конъюнкты суть exact-переэкспорт ранее доказанных лемм. НЕ доказывает проблему Clay о массовой щели Янга-Миллса: щель — лишь конечно-β (0<β<8) факт на ФИКСИРОВАННОЙ малой решётке (через SU2TransferMatrix), RG — игрушечная ЛИНЕАРИЗОВАННАЯ карта (сама millennium_gap это признаёт). Имена yang_mills_progress / su2_synthesis_main аспирационны — флаг над-брендинга, частично самонейтрализованный millennium_gap. Заголовок «~15 Qed» завышен: фактически 13.

---

## #506 - `src/gauge/SU2TransferMatrix.v` - score 2 (methods)

**SU(2) щель масс через near-identity: SU(2)≈3 копии U(1), gap=(2-β/8)²·(2-β/4)**

- **Topic.** В режиме около единицы SU(2) приближается тремя независимыми копиями U(1); матрица переноса = тензорное произведение трёх 2×2-блоков. Щель масс факторизуется как (2-β/8)²·(щель U(1)) и положительна на 0<β<8.
- **Role.** Импортирует gauge.TransferMatrix (mass_gap_2x2, transfer_eigenvalue_0/1), SU2Group, SU2Lattice, LinearAlgebra, linalg.*, physics.*. Надстройка над U(1)-переносом; экспортирует su2_mass_gap для прочих SU(2)-файлов (щель, сравнение с U(1)).
- **Counts.** Qed 18 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs List Lia ZArith Lqa; ToS: gauge.TransferMatrix; ToS: gauge.SU2Group; ToS: gauge.SU2Lattice; ToS: linalg.MatrixOps; ToS: linalg.EigenvalueTheory; ToS: physics.InnerProductSpace
- **E/R/R.** _Elements:_ конкретные рациональные собственные значения: λ₀=2-β/8 (основное), λ₁=β/8 (возбуждённое); их тензорные степени λ₀³ и λ₀²·λ₁. _Roles:_ su2_mass_gap = роль-зазор спектра (основное минус первое возбуждённое); su2_mass_gap_factor=(2-β/8)² = роль-усилитель над U(1); β = роль-связь (обратная температура решётки). _Rules:_ приближение «около единицы»: тензор трёх копий U(1) ⟹ gap=factor·gap_U1=(2-β/8)²·(2-β/4); положительность ограждена окном 0<β<8. _P4:_ конечно-актуальное: всё считается точной Q-арифметикой на ОДНОМ 2×2⊗2×2⊗2×2 блоке при near-identity; континуум-предел = процесс β→8⁻, где зазор стремится к 0, но НЕ доказательство Clay (нет полной SU(2)-решётки, лишь линеаризованное приближение).
- **Classical counterpart.** Зеркалит решёточную сильно-связную картину неабелевой массовой щели Янга-Миллса (Wilson, Osterwalder-Seiler; transfer-matrix спектр) и эвристику «SU(2) около единицы ≈ U(1)³». ОТЛИЧИЕ: всё над точной Q-арифметикой в линеаризованном near-identity, число копий и формула λ₀,λ₁ постулированы; некоммутативность SU(2) и реальный континуумный предел НЕ присутствуют. Не доказывает Clay-проблему массовой щели.
- **Tags.** gauge, mass-gap, SU2, transfer-matrix, near-identity, Q-arithmetic, finite-lattice, over-branded-header
- **Notes.** Дрейф Qed: шапка ~25, фактически 19 Qed. total_count: (25=25)%nat — декоративный маркер, не математический результат. su2_mass_gap_factor_positive доказан на β<16, но используется в окне β<8.

**Lemmas (23):**

| name | kind | role |
|---|---|---|
| `su2_eigenvalue_ground` | Definition | основное собственное значение λ₀³=(2-β/8)³ |
| `su2_eigenvalue_first` | Definition | первое возбуждённое λ₀²·λ₁=(2-β/8)²·(β/8) |
| `su2_mass_gap` | Definition | щель = ground - first |
| `su2_mass_gap_factor` | Definition | усилитель (2-β/8)² над U(1)-щелью |
| `su2_gap_factored` | Lemma | ★ факторизация: su2_mass_gap == factor · mass_gap_2x2 (через ring) |
| `su2_mass_gap_factor_positive` | Lemma | усилитель >0 для 0<β<16 (nra) |
| `su2_mass_gap_positive` | Theorem | ★ щель >0 на 0<β<8 (произведение двух положительных) |
| `su2_gap_vs_u1` | Theorem | ★ SU(2)-щель > U(1)-щели (неабелево удержание сильнее, factor>1) |
| `su2_gap_at_beta_1` | Lemma | конкретное значение su2_mass_gap 1 == 1575#256 |
| `su2_eigenvalue_ground_positive` | Lemma | λ₀³>0 на 0<β<16 |
| `su2_eigenvalue_first_positive` | Lemma | λ₀²·λ₁>0 на 0<β<16 |
| `su2_ground_dominates` | Theorem | first<ground на 0<β<8 (зазор знаком определён) |
| `su2_gap_at_8` | Lemma | щель обнуляется при β=8 (фазовый переход) |
| `su2_gap_formula` | Lemma | замкнутая форма gap=(2-β/8)²·(2-β/4) (ring) |
| `su2_gap_monotone` | Lemma | щель убывает по β на (0,8) (через факторизацию) |
| `su2_three_fold_enhancement` | Lemma | усилитель ≥1 для β≤8 (три копии не ослабляют) |
| `su2_strong_coupling_gap` | Lemma | сильная связь: щель ≥3 при β≤1 |
| `su2_weak_coupling_gap` | Lemma | слабая связь: щель ≤3 при 4≤β<8 |
| `su2_continuum_limit` | Theorem | ★ для всякого ε>0 есть β∈(0,8) с щелью<ε (процесс β→8⁻) |
| `su2_gap_at_beta_3` | Lemma | щель >0 при β=3 (для RG-точки) |
| `su2_transfer_summary` | Theorem | сводка: положительность+факторизация+>U(1)+ноль@8+монотонность |
| `su2_transfer_main` | Theorem | главное: положительность щели + SU(2)>U(1) |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`su2_gap_factored`** - Несущая лемма файла: алгебраическое тождество su2_mass_gap β == (2-β/8)²·mass_gap_2x2 β, доказанное одним ring после разворачивания определений. Вся положительность, монотонность и сравнение с U(1) сводятся к этой факторизации плюс факты об U(1)-щели из TransferMatrix.v. Честно: это тождество для МНОГОЧЛЕНОВ в приближении «3 независимые копии U(1)», а не свойство истинной матрицы переноса SU(2) — неабелева структура (некоммутативность генераторов) в near-identity отброшена. _(factorization, near-identity, load-bearing, ring)_
- **`su2_gap_vs_u1`** - Содержательное наблюдение: усилитель (2-β/8)²>1 на (0,8), поэтому SU(2)-щель строго больше U(1)-щели — «неабелево удержание сильнее». Это качественно верно для реальной КХД, но здесь это СЛЕДСТВИЕ выбранного тензорного приближения, а не вывод из групповой структуры SU(2); число копий 3 = dim SU(2) вставлено руками. _(non-abelian, confinement, comparison, qualitative)_
- **`su2_continuum_limit`** - «Континуум-предел» как процесс: для любого ε подбирается β близко к 8 (или β=7 при больших ε) с щелью<ε. Это честный ε-факт о Q-функции на отрезке, НЕ доказательство существования/исчезновения континуумной массовой щели; β=8 здесь — точка обнуления полиномиального приближения, а не физический континуумный предел a→0. _(continuum, process, epsilon, not-clay)_

**Uniqueness - score 2 (methods).** Необычная Q-формализация неабелевой щели как полиномиальной факторизации (2-β/8)²·(U(1)-щель) с машинной положительностью/монотонностью и ε-«континуумом» на конечном окне 0<β<8.
> _Caveat:_ Приближение «SU(2)=3 копии U(1)» около единицы — НЕ настоящая матрица переноса SU(2); некоммутативность отброшена, число копий 3 вставлено руками. Это конечно-окно/полиномиальный факт, НЕ доказательство континуумной массовой щели (не Clay). Шапка заявляет ~25 Qed — фактически 19 (total_count=декоративная заглушка).

---

## #507 - `src/gauge/SU3AsymptoticFreedom.v` - score 2 (methods)

**Асимптотическая свобода SU(3): β₀=(33-2N_f)·113/(12·355)>0 для N_f≤16, отказ при 17**

- **Topic.** Однопетлевой коэффициент β-функции SU(3) над Q с π≈355/113 (Цзу Чунчжи). β₀>0 (АС держится) для 6 флейворов, граница N_f=16, отказ при N_f=17. Игрушечный одношаговый RG-поток β↦β²/(β+1) убывает (поведение АС).
- **Role.** Автономный (только Stdlib QArith/Lqa, без ToS-импортов). Опорный для прочих SU(3)-RG/континуум файлов как источник знака β₀ и одношаговой RG-карты.
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa
- **E/R/R.** _Elements:_ конкретные рациональные числа: числитель 33-2N_f (Z), β₀ как Qmake, эффективная связь β²/(β+1) при β=1,6. _Roles:_ β₀ = роль-знак (АС держится ⟺ β₀>0); su3_effective_beta = роль-RG-карта (связь после одного шага); N_f = роль-счётчик флейворов. _Rules:_ β₀=(11·3-2N_f)/(12π), π=355/113 фиксировано; знак переключается между N_f=16 (>0) и N_f=17 (<0); RG: эфф.связь < голой. _P4:_ конечно-актуальное: знак β₀ для КАЖДОГО конкретного N_f решается vm_compute (булева Z.ltb), N_f=17 — наблюдаемая точка переключения; π рационализировано конечной дробью (355/113), бесконечный процесс приближения π обрезан до одной аппроксимации.
- **Classical counterpart.** Зеркалит однопетлевой коэффициент β-функции КХД β₀=(11N_c-2N_f)/(12π) и порог асимптотической свободы N_f<16.5 (Gross-Wilczek-Politzer 1973). ОТЛИЧИЕ: π заменено рациональным 355/113, поток заменён игрушечной картой β²/(β+1) (не интеграл РГ-уравнения); только конкретные N_f проверены численно. Знаковая граница воспроизведена точно.
- **Tags.** gauge, SU3, asymptotic-freedom, beta-function, RG, Q-arithmetic, standalone
- **Notes.** Дрейф Qed: шапка 12, фактически 11. su3_effective_beta — игрушечная карта, не реальный РГ-интеграл. π рационализировано как 355/113.

**Lemmas (14):**

| name | kind | role |
|---|---|---|
| `su3_beta0_numerator` | Definition | числитель 33-2·N_f над Z |
| `su3_beta0` | Definition | β₀=Qmake((33-2N_f)·113)(12·355) |
| `beta0_0f` | Lemma | β₀(0)=33·113/(12·355) (vm_compute) |
| `beta0_6f_positive` | Lemma | ★ β₀(6)>0 (АС для 6 флейворов, vm_compute через Z.ltb) |
| `su3_af_6f` | Theorem | АС держится для 6 флейворов (= beta0_6f_positive) |
| `beta0_16f_positive` | Lemma | β₀(16)>0 (последний АС-флейвор) |
| `su3_af_fails_17` | Theorem | ★ β₀(17)<0 (АС отказывает, точка переключения) |
| `sm_is_af` | Lemma | СМ (6 флейворов) асимптотически свободна (= beta0_6f_positive) |
| `su3_effective_beta` | Definition | одношаговая RG-карта β↦β²/(β+1) |
| `su3_rg_step_1` | Lemma | RG(1)=1/2 (vm_compute) |
| `su3_rg_step_6` | Lemma | RG(6)=36/7 |
| `rg_decreases_6` | Lemma | RG(6)<6 (связь убывает) |
| `rg_decreases_strong` | Lemma | RG(1)<1 (сильная связь ослабевает) |
| `af_synthesis` | Theorem | сводка: β₀(6)>0 ∧ β₀(17)<0 ∧ RG(1)=1/2 |

**Key lemmas (deep):**

- **`su3_af_fails_17`** - Содержательная точка: знак β₀ переключается ровно между N_f=16 и N_f=17, что машинно подтверждает классическую границу асимптотической свободы N_f<33/2=16.5. Доказательство — булев vm_compute на Z.ltb. Это корректный конечный факт о ЧИСЛИТЕЛЕ 33-2N_f; рационализация π=355/113 на знак не влияет (знак определяется числителем), поэтому здесь честно. _(asymptotic-freedom, beta-function, threshold, vm_compute)_
- **`su3_effective_beta`** - Игрушечная RG-карта β↦β²/(β+1): убывает (эфф<голой), что качественно имитирует АС-поток к слабой связи. Но это НЕ интеграл реальной однопетлевой β-функции (там 1/g²(μ) линейно по ln μ); карта выбрана ad hoc ради монотонного убывания. Честный статус — иллюстрация, не вывод РГ-уравнения. _(RG-flow, toy-map, ad-hoc, qualitative)_

**Uniqueness - score 2 (methods).** Машинно-проверенный знак однопетлевого β₀(N_f) над Q с точной границей АС N_f=16→17, плюс автономность (0 ToS-импортов).
> _Caveat:_ Классический результат GWP 1973; ново лишь Q-формализация с π≈355/113. RG-карта β²/(β+1) — ad hoc игрушка, НЕ интеграл β-функции. Шапка заявляет 12 Qed — фактически 11.

---

## #508 - `src/gauge/SU3Characters.v` - score 2 (methods)

**Характеры SU(3) (малоугловое приближение) и коэффициенты переноса t₀₀=1, t₁₀=β/6, t₁₁=β²/72**

- **Topic.** Характеры SU(3) χ₃,χ₈ как квадратичные малоугловые приближения (cos≈1-t²/2) и ведущие коэффициенты сильно-связного разложения матрицы переноса по представлениям (тривиальное/фундаментальное/присоединённое) с проверенной иерархией.
- **Role.** Импортирует gauge.SU3Representations (su3_casimir). Базовый поставщик коэффициентов t_*_su3 для SU3Transfer.v (gap_su3=t₀₀-t₁₀) и SU3Glueball.v (mass_ratio). Корень SU(3)-переносной ветки.
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: gauge.SU3Representations
- **E/R/R.** _Elements:_ характер χ₃(t1,t2)=3-(t₁²+t₂²+(t₁+t₂)²)/2; константы χ₈(0)=8; коэффициенты t_trivial=1, t_fund=β/6, t_adj=β²/72. _Roles:_ характер = роль-след представления на классе сопряжённости; t_*_su3 = роль-вес представления в разложении переноса; иерархия trivial>fund>adj = роль-упорядочение по подавлению. _Rules:_ малый угол: cos≈1-t²/2 ⟹ χ₃≈3-t²; сильная связь: только низкие (p,q) значимы, веса по степеням β; иерархия t_adj(1)<t_fund(1)<t_trivial(1). _P4:_ конечно-актуальное: бесконечный ряд характеров обрезан до квадратичного члена, бесконечное разложение переноса — до трёх ведущих представлений; всё считается точной Q-арифметикой при конкретных β (1,6) или ring-тождествами.
- **Classical counterpart.** Зеркалит характеры неприводимых представлений SU(3) (Weyl character formula) и сильно-связное (strong-coupling / character) разложение решёточного действия (Wilson). ОТЛИЧИЕ: характеры усечены до квадратичного малоуглового приближения над Q (нет точных e^{iθ}), коэффициенты t_* постулированы как ведущие мономы β-разложения, а не интегралы Хаара. Размерности 3,8 и казимиры 4/3,3 воспроизведены точно.
- **Tags.** gauge, SU3, characters, transfer-matrix, strong-coupling, representation-theory, Q-arithmetic, plumbing
- **Notes.** Дрейф Qed: шапка 16, фактически 12. Характеры — малоугловые приближения; коэффициенты t_* = постулированные ведущие мономы, не интегралы Хаара.

**Lemmas (17):**

| name | kind | role |
|---|---|---|
| `chi_fund_approx` | Definition | малоугловой χ₃≈3-(t₁²+t₂²+(t₁+t₂)²)/2 |
| `chi_fund_at_zero` | Lemma | χ₃(0,0)=3=dim(fund) (ring) |
| `chi_fund_decreases` | Lemma | χ₃(t,0)=3-t² (квадратичная поправка) |
| `chi_adj_at_zero` | Definition | χ₈(0,0)=8 (константа) |
| `chi_adj_value` | Lemma | χ₈(0,0)=8=dim(adjoint) |
| `t_trivial_su3` | Definition | вес тривиального представления = 1 |
| `t_fund_su3` | Definition | вес фундаментального = β/6 |
| `t_adj_su3` | Definition | вес присоединённого = β²/72 |
| `t_trivial_value` | Lemma | t_trivial≡1 для всех β |
| `t_fund_at_1` | Lemma | t_fund(1)=1/6 (ring) |
| `t_adj_at_1` | Lemma | t_adj(1)=1/72 (ring) |
| `t_fund_at_6` | Lemma | t_fund(6)=1 (точка β=6) |
| `t_hierarchy_01` | Lemma | ★ t_fund<t_trivial на 0<β<6 (фундаментальное подавлено) |
| `t_hierarchy_su3` | Lemma | ★ t_adj(1)<t_fund(1) (присоединённое сильнее подавлено) |
| `t_fund_nonneg` | Lemma | t_fund≥0 при β≥0 |
| `t_adj_nonneg` | Lemma | t_adj≥0 при β≥0 (nra) |
| `su3_characters_synthesis` | Theorem | сводка: χ₃(0)=3 ∧ t_fund(1)=1/6 ∧ t_adj(1)=1/72 ∧ казимиры 4/3,3 |

**Key lemmas (deep):**

- **`t_hierarchy_01`** - Несущая лемма ветки: t_fund(β)=β/6 < t_trivial=1 на окне 0<β<6 — фундаментальное представление подавлено относительно тривиального, что задаёт знак щели gap_su3=t₀₀-t₁₀>0 в SU3Transfer.v. Доказательство — lra на линейном неравенстве. Честно: веса β/6, β²/72 — это ВЕДУЩИЕ члены сильно-связного разложения, постулированные как мономы, а не вычисленные интегралы по группе SU(3). _(hierarchy, strong-coupling, load-bearing, representation)_
- **`chi_fund_decreases`** - χ₃(t,0)=3-t² — квадратичная (малоугловая) аппроксимация характера фундаментального представления через cos≈1-t²/2. Корректное тождество для ПРИБЛИЖЕНИЯ, но истинный χ₃=e^{iθ₁}+e^{iθ₂}+e^{-i(θ₁+θ₂)} здесь усечён до второго порядка над Q (комплексные экспоненты не представимы точно в Q). Иллюстративная подложка, не точный характер. _(character, small-angle, approximation, quadratic)_

**Uniqueness - score 2 (methods).** Q-формализация ведущих SU(3)-коэффициентов переноса с машинной иерархией trivial>fund>adj — конечный носитель для SU3Transfer/Glueball.
> _Caveat:_ Характеры — квадратичные малоугловые приближения (не точные представления SU(3)); веса t_* постулированы как мономы strong-coupling, не выведены интегралом по группе. Стандартное character-разложение Уилсона. Шапка заявляет 16 Qed — фактически 12.

---

## #509 - `src/gauge/SU3ContinuumLimit.v` - score 1 (exposition)

**SU(3) континуум-тест: убывает ли σa² с β? σ(6)>σ(12)>σ(18)=0 + сравнение с MC-данными**

- **Topic.** Тест масштабирования струнного натяжения: линейная аппроксимация σ=1-β/18 убывает с β (признак АС), что сопоставляется с цитируемыми Монте-Карло числами (σ(5.7)/σ(6.0)≈3.2). Линейная модель ломается при β>18.
- **Role.** Импортирует gauge.SU3StringTension (sigma_su3_strong, sigma_decreases_6_12/12_18, sigma_su3_at_6). Тонкая надстройка: переупаковывает факты убывания натяжения в «континуум-тест» и сравнение с данными.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: gauge.SU3StringTension
- **E/R/R.** _Elements:_ конкретные значения σ=1-β/18 при β=6,12,18,5.7; наши our_sigma_57, our_sigma_60. _Roles:_ sigma_su3_strong = роль-натяжение струны (в решёточных единицах); убывание по β = роль-сигнал асимптотической свободы; сравнение с MC = роль-валидация. _Rules:_ линейная аппроксимация σ=1-β/18 (из σ=-ln(β/18)); σ убывает σ(6)>σ(12)>σ(18)=0; упорядочение σ(5.7)>σ(6.0) совпадает с данными. _P4:_ конечно-актуальное: «континуум» проверяется лишь как монотонность 3 конкретных точек β∈{6,12,18}, НЕ как реальный предел a→0; линейная модель σ=1-β/18 явно ломается при β>18 (становится отрицательной) — конечное окно, не континуум.
- **Classical counterpart.** Зеркалит решёточный анализ масштабирования струнного натяжения σa²(β) и подход к континууму через асимптотический скейлинг (Creutz; Monte-Carlo КХД, σ из петель Вильсона). ОТЛИЧИЕ: σ заменено грубой линейной аппроксимацией σ=1-β/18 (вместо σ=-ln(β/18)), «континуум» = монотонность 3 точек, не предел a→0; количественно расходится с MC (~2.05 vs ~3.2). Только знак/порядок верны.
- **Tags.** gauge, SU3, continuum-limit, string-tension, scaling, MC-comparison, exposition, over-branded-name
- **Notes.** Дрейф Qed: шапка 10, фактически 8. Имя 'ContinuumLimit' аспирационно — лишь 3-точечный монотонный тест линейной модели σ=1-β/18, НЕ доказательство предела a→0; σ(18)=0 = артефакт линеаризации.

**Lemmas (10):**

| name | kind | role |
|---|---|---|
| `sigma_scaling_6_12` | Lemma | σ(12)<σ(6) (= sigma_decreases_6_12) |
| `sigma_scaling_12_18` | Lemma | σ(18)<σ(12) |
| `sigma_scaling` | Theorem | ★ σ(6)>σ(12)>σ(18) (масштабирование = убывание натяжения) |
| `our_sigma_57` | Definition | σ при β=5.7 = sigma_su3_strong(57/10) |
| `our_sigma_60` | Definition | σ при β=6.0 |
| `sigma_57_value` | Lemma | our_sigma_57 = 1-(57/10)(1/18) (ring) |
| `sigma_60_value` | Lemma | our_sigma_60 = 2/3 |
| `sigma_57_gt_60` | Lemma | ★ σ(5.7)>σ(6.0) — верный порядок vs MC |
| `sigma_57_positive` | Lemma | σ(5.7)>0 (оба положительны) |
| `continuum_synthesis` | Theorem | сводка: σ(6)=2/3 ∧ σ(5.7)>σ(6.0) ∧ σ(12)<σ(6) |

**Key lemmas (deep):**

- **`sigma_scaling`** - Главное утверждение файла: σ(6)>σ(12)>σ(18) — струнное натяжение в решёточных единицах убывает с β, что качественно = асимптотическая свобода (a уменьшается ⟹ σa² падает). Доказательство делегировано sigma_decreases_* из SU3StringTension. Честный статус: это монотонность ТРЁХ точек линейной модели σ=1-β/18, а НЕ доказательство континуумного предела; σ(18)=0 — артефакт линейной аппроксимации (реальная КХД сохраняет σ>0, конфайнмент). _(scaling, continuum-test, 3-points, not-clay)_
- **`sigma_57_gt_60`** - Сравнение с Монте-Карло: правильный ПОРЯДОК σ(5.7)>σ(6.0) воспроизведён. Но числовое отношение линейной модели (123/180)/(1/3)≈2.05 заметно расходится с цитируемым MC≈3.2 — файл честно приводит данные в комментарии, не подгоняя. Это валидация знака/порядка, не количественное согласие. _(MC-data, validation, ordering, honest-gap)_

**Uniqueness - score 1 (exposition).** Чистая переупаковка фактов убывания натяжения из SU3StringTension в «континуум-тест» + честное сопоставление с цитируемыми MC-числами.
> _Caveat:_ НЕ доказательство континуумного предела: σ=1-β/18 — грубая линейная модель, ломается при β>18 (σ(18)=0 — артефакт, реальный конфайнмент сохраняет σ>0); количественно ~2.05 vs MC~3.2. 0 нового содержания над SU3StringTension. Шапка заявляет 10 Qed — фактически 8.

---

## #510 - `src/gauge/SU3Glueball.v` - score 2 (methods)

**Масса глюбола SU(3) = щель m_G(1)=5/6; отношение масс 0⁺⁺/0⁻⁺ = 71/60 vs данные 1.39**

- **Topic.** Масса глюбола в решёточных единицах = щель сильно-связного переноса gap_su3; конкретные значения m_G(0)=1, m_G(1)=5/6, m_G(3)=1/2. Отношение масс возбуждённых состояний (t₀₀-t₁₁)/(t₀₀-t₁₀)=71/60>1, сопоставлено с решёточным 1.39.
- **Role.** Импортирует gauge.SU3Characters (t_*_su3) и gauge.SU3Transfer (gap_su3). Лист SU(3)-ветки: интерпретирует щель как массу глюбола и строит отношение масс. Никем дальше не переиспользуется (конечный потребитель).
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: gauge.SU3Characters; ToS: gauge.SU3Transfer
- **E/R/R.** _Elements:_ конкретные значения щели как массы: glueball_mass(0)=1, (1)=5/6, (3)=1/2; отношение mass_ratio(1)=71/60. _Roles:_ glueball_mass_su3 = роль-масса (щель в решёточных единицах); mass_ratio_su3 = роль-отношение возбуждённых уровней 0⁺⁺/0⁻⁺; убывание массы по β = роль-сигнал континуума. _Rules:_ m_G(β)=gap_su3(β)=1-β/6; отношение =(t₀₀-t₁₁)/(t₀₀-t₁₀)=(1-β²/72)/(1-β/6); отношение >1 (возбуждённое тяжелее), масса убывает с β. _P4:_ конечно-актуальное: масса и отношение вычислены точной Q-арифметикой при конкретных β (0,1,3); 'физическая масса m_G=gap/a' лишь упомянута в комментарии — деление на спейсинг a (континуум) НЕ выполнено, остаётся решёточная единица.
- **Classical counterpart.** Зеркалит решёточные вычисления спектра глюболов КХД (масса 0⁺⁺-глюбола ~1.5-1.7 ГэВ, отношение 0⁺⁺/0⁻⁺≈1.39; Morningstar-Peardon и др. через корреляторы петель Вильсона). ОТЛИЧИЕ: масса = щель сильно-связного переноса в решёточных единицах (без деления на a), отношение из постулированных t_*-мономов; число 71/60≈1.18 расходится с данными ~1.39. Только знак/порядок (масса>0, возбуждённое тяжелее) верны.
- **Tags.** gauge, SU3, glueball, mass-gap, mass-ratio, strong-coupling, Q-arithmetic, lattice-units
- **Notes.** Дрейф Qed: шапка 12, фактически 10. Масса/отношение из постулированных t_*-коэффициентов; деление на спейсинг a (физ. масса) не выполнено; 71/60 vs данные 1.39 — расхождение ~15%, честно отмечено в комментарии.

**Lemmas (12):**

| name | kind | role |
|---|---|---|
| `glueball_mass_su3` | Definition | масса глюбола = gap_su3(β) |
| `glueball_at_0` | Lemma | m_G(0)=1 (= gap_su3_at_0) |
| `glueball_at_1` | Lemma | ★ m_G(1)=5/6 (= gap_su3_at_1) |
| `glueball_at_3` | Lemma | m_G(3)=1/2 (= gap_su3_at_3) |
| `glueball_positive` | Lemma | m_G(1)>0 (масса положительна) |
| `mass_ratio_su3` | Definition | отношение (t₀₀-t₁₁)/(t₀₀-t₁₀) |
| `mass_ratio_at_1` | Lemma | ratio(1)=(1-1/72)/(1-1/6) (подстановка) |
| `mass_ratio_at_1_value` | Lemma | ★ ratio(1)=71/60 (vm_compute) |
| `mass_ratio_gt_1` | Lemma | ★ 1<ratio(1) (возбуждённое состояние тяжелее) |
| `glueball_decreases` | Lemma | m_G(3)<m_G(1) (масса убывает) |
| `glueball_decreases_01` | Lemma | m_G(1)<m_G(0) |
| `glueball_synthesis` | Theorem | сводка: m_G(1)=5/6 ∧ >0 ∧ ratio=71/60 ∧ >1 |

**Key lemmas (deep):**

- **`mass_ratio_at_1_value`** - Центральное число файла: отношение масс 0⁺⁺/0⁻⁺ = (1-β²/72)/(1-β/6) при β=1 = 71/60 ≈ 1.183, доказано vm_compute. Файл честно сравнивает с решёточным КХД-значением ≈1.39 («тот же порядок»), не подгоняя. Честный статус: число вычислено из ПОСТУЛИРОВАННЫХ ведущих коэффициентов t_* (SU3Characters), значимо расходится с данными (~15%), и это иллюстрация структуры, а не предсказание спектра глюболов. _(mass-ratio, glueball, vm_compute, honest-gap)_
- **`glueball_at_1`** - Масса глюбола = щель сильно-связного переноса: m_G(1)=5/6 в решёточных единицах (делегировано gap_su3_at_1). Положительность и убывание массы по β качественно отражают существование массивного глюбола и подход к континууму. Но 'физическая масса m_G=gap/a' (деление на спейсинг) НЕ выполнена — всё остаётся в решёточных единицах конечной модели; это НЕ предсказание физической массы глюбола. _(glueball-mass, lattice-units, strong-coupling, not-physical)_

**Uniqueness - score 2 (methods).** Q-интерпретация сильно-связной щели как массы глюбола с машинным отношением масс 71/60 и честным сравнением с решёточным 1.39.
> _Caveat:_ НЕ предсказание физического спектра глюболов: масса в решёточных единицах (деление на a не выполнено), отношение из постулированных t_*-мономов, 71/60≈1.18 расходится с данными 1.39 (~15%). Тонкий лист над SU3Transfer/Characters. Шапка заявляет 12 Qed — фактически 10.

---

## #511 - `src/gauge/SU3GrandSynthesis.v` - score 4 (synthesis+observation)

**SU(3) grand synthesis: dims+Casimirs+gap+σ+glueball+β₀ bundled at strong coupling (exact Q)**

- **Topic.** Top capstone of the SU(3) gauge thread: re-exports the chain A=exists→Distinction→[3,2,1]→SU(3)→reps→transfer→3+1D→observables→asymptotic freedom and bundles the headline facts (dim 3/8, C₂=4/3, gap_su3(1)=5/6>0, β₀(6)>0, 4³=64 sites) into two grand theorems.
- **Role.** Pure consolidation / aggregation node — imports SU3Representations, SU3Characters, SU3Transfer, Lattice3D, SU3Lattice3D, SU3StringTension, SU3Glueball, SU3AsymptoticFreedom and re-asserts their exact-value lemmas via `exact`. Terminal: nothing in the catalogued set imports it.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lia ZArith Lqa; gauge.SU3Representations; gauge.SU3Characters; gauge.SU3Transfer; gauge.Lattice3D; gauge.SU3Lattice3D; gauge.SU3StringTension; gauge.SU3Glueball; gauge.SU3AsymptoticFreedom
- **E/R/R.** _Elements:_ конкретные рациональные значения наблюдаемых SU(3): dim 3/8, C₂=4/3, щель 5/6, σ=2/3, β₀(6), 64 узла 4³-решётки. _Roles:_ файл-капстоун = роль агрегатора: каждое значение — Element, собранный из импортированных лемм; теоремы-связки su3_grand_synthesis/su3_full_stats = роль-сводка. _Rules:_ связывание через `exact L` уже доказанных равенств/неравенств; конъюнкция фактов = единое утверждение. _P4:_ всё на КОНЕЧНОЙ решётке при ФИКСИРОВАННОЙ сильной связи β≈1 — Element-сторона (терминирующее vm_compute над Q); континуумный предел (β→∞, бесконечный объём) = role-limit, НЕ достигнут; «gap>0 как теорема» честно ограничен этой конечной ареной.
- **Classical counterpart.** Strong-coupling lattice gauge theory for SU(3) (Wilson 1974, Creutz) and the Standard-Model gauge group SU(3)×SU(2)×U(1): all classical. What differs is only the medium — exact rational (Q) character-expansion arithmetic instead of floating-point Monte Carlo, so that 'gap > 0' is a machine-checked theorem at the chosen finite parameters, NOT a numerical estimate; and the deductive framing A=exists→Distinction→[3,2,1]→SU(3).
- **Tags.** gauge, SU3, lattice, mass-gap, capstone, exact-Q, strong-coupling, P4, over-branding
- **Notes.** Qed DRIFT: STATUS header says '8 Qed', actual Qed.=6 (the file has 4 Lemma + 2 Theorem, each one Qed). Admitted actual=0 (the 'Admitted.' grep hit at line 35 is the prose '0 Admitted.' inside the HONEST LIMITATIONS comment block, not a real proof). 0 own axioms.

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `grand_reps` | Lemma | сводка представлений: dim(1,0)=3 ∧ dim(1,1)=8 ∧ C₂(1,0)=4/3 |
| `grand_gap` | Lemma | массовая щель: 0<gap_su3(1) ∧ gap_su3(1)=5/6 |
| `grand_3d` | Lemma | 3+1D: gap_su3_3d(1,0)>0 ∧ с пространственной связью щель растёт |
| `grand_af` | Lemma | асимптотическая свобода: β₀(6)>0 ∧ β₀(17)<0 (граница N_f=16) |
| `su3_grand_synthesis` | Theorem | ★ гранд-связка: dim 3/8 + C₂=4/3 + gap>0 + β₀(6)>0 + 64 узла в одном утверждении |
| `su3_full_stats` | Theorem | ★ полная статистика: gap=5/6 + σ=2/3 + glueball=5/6 + mass_ratio=71/60 + gap_3d>0 |

**Key lemmas (deep):**

- **`su3_grand_synthesis`** - Капстоун всей ветки SU(3): шесть классических фактов лёгкого вычислительного содержания (размерности фунд./присоединённого, квадратичный Казимир, положительность щели, знак β₀, число узлов 4³) собраны в одну конъюнкцию через `exact`. Ценность — НЕ новая теорема, а демонстрация того, что весь pipeline свёлся к точной рациональной арифметике с 0 Admitted. Честная граница (записана в шапке файла): сильная связь β≈1 против физической β≈6, лидирующий порядок характерного разложения, 3+1D через штраф, без фермионов. _(capstone, synthesis, exact-Q, strong-coupling)_
- **`grand_gap`** - Несущее наблюдение ветки: массовая щель SU(3) при β=1 РАВНА 5/6 и положительна — доказано (gap_su3_at_1, gap_su3_positive_1), а не оценено численно. Это и есть «mass gap > 0 как теорема»; но честно — лишь для конкретной конечной решётки при сильной связи, что НЕ есть решение проблемы Янга–Миллса Клэя (континуум + произвольная связь остаются role-limit). _(mass-gap, theorem-not-estimate, finite-lattice)_

**Uniqueness - score 4 (synthesis+observation).** Капстоун-узел, собирающий первую SU(3)-решёточную калибровку в Rocq в одну машинно-проверенную конъюнкцию точных рациональных наблюдаемых (dim/Casimir/gap/σ/glueball/β₀) с 0 Admitted — load-bearing сводка ветки.
> _Caveat:_ 0 нового содержания — чистая агрегация импортов через `exact`. ВСЁ при сильной связи β≈1 на конечной 4³-решётке, лидирующий порядок, 3+1D через штраф, без фермионов; это НЕ решение Янга–Миллса Клэя (континуум/слабая связь = role-limit). Имя 'GrandSynthesis' аспирационно. DRIFT: шапка заявляет 8 Qed, фактически 6.

---

## #512 - `src/gauge/SU3Lattice3D.v` - score 2 (methods)

**SU(3) on a 3D lattice: gap = temporal transfer × linear spatial penalty (1−C₂·β_s), exact Q**

- **Topic.** Defines the spatial penalty su3_spatial_penalty(p,q,β_s)=1−C₂(p,q)·β_s, the combined eigenvalue su3_combined = t(β)·penalty per (p,q) mode, and the 3+1D gap gap_su3_3d = combined(0,0)−combined(1,0); proves it equals 5/6 at (β=1,β_s=0), is positive, and increases when spatial coupling is switched on.
- **Role.** Methods/definitional layer of the 3+1D extension. Imports SU3Representations (Casimirs) and SU3Characters (t_*_su3 transfer values). Reused by SU3GrandSynthesis (grand_3d / su3_full_stats consume gap_su3_3d_positive_1_0 and gap_3d_gt_1d).
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; gauge.SU3Representations; gauge.SU3Characters
- **E/R/R.** _Elements:_ конкретные рациональные собственные значения: penalty(1,0,1/100)=1−(4/3)(1/100), combined(1,0,1,1/100), gap_3d(1,0)=5/6. _Roles:_ su3_spatial_penalty — роль пространственного подавления (мера убывания корреляции по C₂); su3_combined — роль полного собственного значения (temporal×spatial); gap_su3_3d — роль наблюдаемой щели. _Rules:_ penalty = 1 − C₂·β_s (линейная аппроксимация exp); combined = t(β)·penalty по моде (p,q) через match; gap = combined(0,0) − combined(1,0). _P4:_ обе оси — конечная решётка, фиксированные рациональные (β,β_s); линейное приближение exp(-x)≈1-x — это КОНЕЧНОЕ усечение нетерминирующего экспоненциального процесса (Element-усечение role-limit); честная щель только при малых β_s, где приближение разумно.
- **Classical counterpart.** Hamiltonian/anisotropic lattice gauge theory where the spatial plaquette contributes a Casimir-weighted suppression exp(-C₂·β_s), and the strong-coupling transfer-matrix gap: both classical (Kogut–Susskind, Wilson). What differs: the spatial suppression is taken in crude LINEAR approximation exp(-x)≈1-x and the temporal×spatial product is evaluated as exact rationals on a single mode, so '3+1D gap' is a finite arithmetic fact, not a continuum-limit statement.
- **Tags.** gauge, SU3, lattice, 3+1D, mass-gap, casimir, linear-approx, exact-Q, strong-coupling, methods
- **Notes.** Qed DRIFT: STATUS header says '14 Qed', actual Qed.=12 (12 Lemma + 1 Theorem proved by Qed; 3 Definitions carry no Qed). 0 Admitted, 0 own axioms. The 5/6 value coincides with the 1D temporal gap because penalty(_,_,0)=1; genuine 3D content is only in the β_s>0 lemmas.

**Lemmas (15):**

| name | kind | role |
|---|---|---|
| `su3_spatial_penalty` | Definition | пространственное подавление 1 − C₂(p,q)·β_s (линейное приближение exp(-C₂β_s)) |
| `penalty_trivial` | Lemma | penalty(0,0,β_s)=1 (тривиальное представление не подавляется) |
| `penalty_fund_at_001` | Lemma | penalty(1,0,1/100)=1−(4/3)(1/100) (фунд. через C₂=4/3) |
| `penalty_adj_at_001` | Lemma | penalty(1,1,1/100)=1−3(1/100) (присоединённое через C₂=3) |
| `penalty_hierarchy` | Lemma | penalty(1,1)<penalty(1,0): присоединённое подавлено сильнее (больший C₂) — vm_compute |
| `su3_combined` | Definition | полное собственное значение t(β)·penalty по моде (p,q) через match на p,q |
| `combined_trivial` | Lemma | combined(0,0,β,β_s)=1 (тривиальная мода) |
| `combined_fund_at_1_001` | Lemma | combined(1,0,1,1/100)=(1/6)(1−(4/3)(1/100)) (конкретное значение) |
| `gap_su3_3d` | Definition | 3+1D щель = combined(0,0) − combined(1,0) |
| `gap_su3_3d_trivial_part` | Lemma | верхняя мода combined(0,0)=1 (делегирует combined_trivial) |
| `gap_su3_3d_at_1_0` | Lemma | ★ gap_su3_3d(1,0)=5/6 (точное рациональное значение, β_s=0) |
| `gap_su3_3d_positive_1_0` | Lemma | 0<gap_su3_3d(1,0) (щель положительна) |
| `gap_3d_gt_1d` | Lemma | ★ gap_3d(1,1/100)>gap_3d(1,0): пространственная связь увеличивает щель |
| `gap_su3_3d_at_1_01` | Lemma | gap_su3_3d(1,1/10)=1−(1/6)(1−(4/3)(1/10)) (точное при β_s=1/10) |
| `su3_3d_synthesis` | Theorem | ★ сводка 3D: gap=5/6 ∧ gap>0 ∧ gap растёт с пространственной связью |

**Key lemmas (deep):**

- **`gap_su3_3d_at_1_0`** - Несущее значение файла: 3+1D массовая щель при (β=1,β_s=0) точно равна 5/6 (то же, что чисто временная щель, т.к. при β_s=0 penalty=1). Доказано раскрытием определений и `ring` над Q — полностью конструктивно, без приближений на этом частном случае. При β_s=0 файл совпадает с одномерным транфер-результатом; всё нетривиальное 3D-содержание появляется лишь во включении β_s. _(mass-gap, 3+1D, exact-Q)_
- **`gap_3d_gt_1d`** - Единственное собственно-3D наблюдение: включение пространственной связи β_s=1/100 УВЕЛИЧИВАЕТ щель относительно β_s=0, потому что пространственный штраф подавляет фундаментальную моду (combined(1,0) уменьшается, а верхняя combined(0,0)=1 не меняется). Это качественная «размерная иерархия gap(3D)>gap(1D)» в духе шапки GrandSynthesis. Честно: эффект — артефакт ЛИНЕЙНОГО приближения exp(-x)≈1-x и одномодового усечения, а не полной 4D транфер-матрицы. _(dimensional-hierarchy, linear-approx, qualitative)_

**Uniqueness - score 2 (methods).** Точная рациональная формализация 3+1D щели SU(3) как произведения временной транфер-моды на линейный пространственный Casimir-штраф; даёт машинно-проверенную размерную иерархию gap(3D)>gap(1D).
> _Caveat:_ Стандартный гамильтонов/анизотропный решёточный приём; пространственное подавление взято в ГРУБОМ линейном приближении exp(-x)≈1-x, одна мода, конечная решётка, сильная связь — НЕ полная 4D транфер-матрица и НЕ континуум. Иерархия gap(3D)>gap(1D) — артефакт приближения. DRIFT: шапка заявляет 14 Qed, фактически 12.

---

## #513 - `src/gauge/SU3ObservablesSynthesis.v` - score 3 (new-framing)

**SU(3) observables synthesis: gap+σ+glueball+Z bundled with an honest QCD-data comparison table**

- **Topic.** Phase-3 observables capstone: re-asserts the exact strong-coupling values of the SU(3) mass gap (5/6), string tension (σ(6)=2/3), glueball mass/ratio (5/6, 71/60) and partition function positivity, plus the mass hierarchy glueball(0)>glueball(1)>glueball(3), and ships a documented comparison with QCD lattice MC data.
- **Role.** Consolidation node parallel to SU3GrandSynthesis but observable-focused. Imports SU3Representations, SU3Transfer, SU3StringTension, SU3Glueball; gathers their lemmas via `exact`. Terminal in the catalogued set.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lia ZArith Lqa; gauge.SU3Representations; gauge.SU3Transfer; gauge.SU3StringTension; gauge.SU3Glueball
- **E/R/R.** _Elements:_ точные рациональные наблюдаемые: gap=5/6, σ(6)=2/3, glueball=5/6, mass_ratio=71/60, Z(1)>0. _Roles:_ файл = роль агрегатора наблюдаемых; каждая лемма-сводка собирает значение+знак (Element + положительность); таблица сравнения = роль честного аудита против MC-данных. _Rules:_ связывание `exact` уже доказанных равенств и неравенств в конъюнкции; иерархия масс = цепочка строгих неравенств. _P4:_ ВСЕ значения при сильной связи β≈1..6 на конечной решётке — Element-сторона; континуум (β→∞), где только и осмысленно сравнение с физической QCD, = role-limit, явно НЕ достигнут (таблица фиксирует расхождения: σ 2/3 против 0.044, glueball lattice-units против 1730 МэВ).
- **Classical counterpart.** Strong-coupling SU(3) lattice observables — mass gap, string tension (Creutz ratio), glueball mass and ratio, partition function Z: all classical lattice-QCD quantities. What differs is only that they are evaluated as EXACT rationals (gap 5/6, σ 2/3, Z 44/9, ratio 71/60) at strong coupling, with an explicit honest comparison table against Monte-Carlo / physical QCD showing the strong≠continuum gap.
- **Tags.** gauge, SU3, lattice, observables, mass-gap, string-tension, glueball, exact-Q, strong-coupling, honest-comparison, over-branding
- **Notes.** Qed actual=6 (3 Lemma + 3 Theorem), matches header '6 Qed' — NO drift here. 0 Admitted, 0 own axioms. Honesty anchor: file ships an explicit ToS-vs-MC-vs-physical-QCD comparison table flagging strong≠continuum (e.g. σ 2/3 vs 0.044 a²; glueball 5/6 lattice-units vs 1730 MeV).

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `observables_gap` | Lemma | gap_su3(1)=5/6 ∧ >0 (массовая щель) |
| `observables_sigma` | Lemma | σ(6)=2/3 ∧ >0 (натяжение струны при β=6) |
| `observables_glueball` | Lemma | glueball(1)=5/6 ∧ mass_ratio(1)>1 (глюбол и его отношение) |
| `su3_observables_complete` | Theorem | ★ сводка: dim 3/8 + gap=5/6 + σ=2/3 + Z(1)>0 в одном утверждении |
| `su3_mass_hierarchy` | Theorem | ★ иерархия масс: glueball(1)<glueball(0) ∧ glueball(3)<glueball(1) |
| `phase3_complete` | Theorem | ★ завершение Фазы 3: gap=5/6 + σ=2/3 + mass_ratio=71/60 |

**Key lemmas (deep):**

- **`su3_observables_complete`** - Главный капстоун наблюдаемых: одна конъюнкция собирает размерности (3,8), массовую щель 5/6, натяжение струны 2/3 и положительность статсуммы Z(1) — всё точными рациональными значениями через `exact`. Содержательно ново НЕ значение каждой величины (все классичны), а то, что они существуют как машинно-проверенные точные рациональные числа в одном файле; и приложенная честная таблица, явно отмечающая, что всё это при СИЛЬНОЙ связи и расходится с континуумной QCD. _(capstone, observables, exact-Q, honest-comparison)_
- **`su3_mass_hierarchy`** - Качественное наблюдение: масса глюбола монотонно убывает с ростом представления, glueball(0)>glueball(1)>glueball(3). Это согласуется с тем, что более высокие представления дают более быстрое убывание корреляций. Честно — следствие конкретной модельной формулы glueball_mass_su3 при сильной связи, а не предсказание спектра реальной QCD (где сравнение требует континуумного предела, см. таблицу: 5/6 lattice-units против 1730 МэВ). _(mass-hierarchy, qualitative, strong-coupling)_

**Uniqueness - score 3 (new-framing).** Единый честный реестр точных рациональных наблюдаемых SU(3) (gap/σ/glueball/Z/ratio) с явной таблицей-сопоставлением против Monte-Carlo и физической QCD, фиксирующей где strong≠continuum.
> _Caveat:_ 0 нового содержания — агрегация импортов через `exact`. Все наблюдаемые при СИЛЬНОЙ связи; таблица сама признаёт расхождения (σ 2/3 против MC 0.044; glueball против 1730 МэВ) — это НЕ предсказания континуумной QCD. Имя 'complete'/'Synthesis' аспирационно. Qed/Admitted header (6/0) совпадает с фактом — drift отсутствует.

---

## #514 - `src/gauge/SU3Representations.v` - score 1 (exposition)

**SU(3) irreps over Q: Weyl dimension & quadratic Casimir by (p,q); 3,3̄,8,6,10,27 machine-checked**

- **Topic.** Foundational arithmetic layer for the SU(3) gauge thread: defines su3_dim(p,q) and su3_casimir(p,q) by the standard closed formulas, verifies the named irreps (trivial 1, fund 3, antifund 3̄, adjoint 8, sextet 6, decuplet 10, 27) and Casimirs (4/3, 3, 10/3), and proves conjugation symmetry and dimension/Casimir monotonicity.
- **Role.** Element-base / bottleneck of the SU(3) thread: imported by SU3Lattice3D (Casimirs for the spatial penalty), SU3Characters/SU3Transfer (dims for transfer values), and re-exported through SU3ObservablesSynthesis & SU3GrandSynthesis. Pure Stdlib dependency only — no upstream ToS gauge files.
- **Counts.** Qed 18 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa
- **E/R/R.** _Elements:_ пары Дынкина (p,q)∈ℕ² (Element-метки представлений); конкретные значения dim и C₂ для названных мультиплетов. _Roles:_ su3_dim — роль размерности (счёт состояний по формуле Вейля); su3_casimir — роль квадратичного Казимира (метка «размера» представления); конъюгация (p,q)↔(q,p) — роль симметрии. _Rules:_ dim(p,q)=(p+1)(q+1)(p+q+2)/2; C₂=(p²+q²+pq+3p+3q)/3·(1#3); конъюгация = перестановка p,q. _P4:_ чистая Element-сторона: все значения вычислимы конечным vm_compute/reflexivity над ℕ и ℚ; никакого role-limit — представления конечномерны, формулы замкнуты, всё терминирует. Это арифметическое дно, на котором покоится ветка.
- **Classical counterpart.** Standard SU(3) representation theory: the Weyl/Dynkin dimension formula dim(p,q)=(p+1)(q+1)(p+q+2)/2 and the quadratic Casimir C₂(p,q)=(p²+q²+pq+3p+3q)/3, with conjugation (p,q)↔(q,p). Textbook (Georgi, Cheng–Li). What differs: nothing mathematically — it is an exact-Q formalization in Rocq of these closed forms (3,3̄,8,6,10,27 etc.), serving as the arithmetic Element-base for the whole SU(3) lattice thread.
- **Tags.** gauge, SU3, representations, casimir, dimension, exact-Q, element-base, bottleneck, exposition
- **Notes.** Qed DRIFT: STATUS header says '20 Qed', actual Qed.=18. The header counted all 20 named declarations, but su3_dim and su3_casimir are Definitions (no Qed) → 18 Lemma/Theorem with Qed. 0 Admitted, 0 own axioms. Most-reused value: casimir_fund (4/3) — feeds the spatial penalty and transfer values across the thread.

**Lemmas (20):**

| name | kind | role |
|---|---|---|
| `su3_dim` | Definition | размерность Вейля (S p)(S q)(S(S(p+q)))/2 над ℕ |
| `dim_trivial` | Lemma | dim(0,0)=1 (синглет) |
| `dim_fund` | Lemma | dim(1,0)=3 (фундаментальное) |
| `dim_antifund` | Lemma | dim(0,1)=3 (антифундаментальное 3̄) |
| `dim_adjoint` | Lemma | dim(1,1)=8 (присоединённое) |
| `dim_6` | Lemma | dim(2,0)=6 (секстет) |
| `dim_10` | Lemma | dim(3,0)=10 (декуплет) |
| `dim_27` | Lemma | dim(2,2)=27 |
| `su3_casimir` | Definition | квадратичный Казимир (p²+q²+pq+3p+3q)/3 над ℚ |
| `casimir_trivial` | Lemma | C₂(0,0)=0 |
| `casimir_fund` | Lemma | C₂(1,0)=4/3 (несущее значение для штрафа/транфера) |
| `casimir_antifund` | Lemma | C₂(0,1)=4/3 |
| `casimir_adjoint` | Lemma | C₂(1,1)=3 |
| `casimir_6` | Lemma | C₂(2,0)=10/3 |
| `dim_conjugate` | Lemma | ★ dim(p,q)=dim(q,p) для всех p,q (конъюгация сохраняет размерность) |
| `casimir_conjugate` | Lemma | ★ C₂(p,q)=C₂(q,p) для всех p,q (конъюгация сохраняет Казимир) |
| `dim_fund_lt_adjoint` | Lemma | dim(1,0)<dim(1,1) (3<8) |
| `dim_adjoint_lt_27` | Lemma | dim(1,1)<dim(2,2) (8<27) |
| `casimir_fund_lt_adj` | Lemma | C₂(1,0)<C₂(1,1) (4/3<3, Казимир растёт с представлением) |
| `su3_rep_synthesis` | Theorem | ★ сводка: dims 1/3/8/10/27 + Casimirs 4/3,3 в одном утверждении |

**Key lemmas (deep):**

- **`casimir_fund`** - Самое нагруженное значение всей ветки: C₂(1,0)=4/3 — именно оно входит в пространственный штраф SU3Lattice3D (penalty=1−(4/3)β_s) и в характерные транфер-значения, через которые получаются gap=5/6, σ, glueball. Доказательство — одно vm_compute над ℚ. Классическое значение (квадратичный Казимир фундаментального представления SU(3)); ценность файла — что оно и его соседи существуют как точные рациональные константы, на которые опирается всё дальнейшее машинное вычисление. _(casimir, exact-Q, load-bearing, element-base)_
- **`dim_conjugate`** - Единственные две леммы с КВАНТОРОМ по всем (p,q) (остальные — точечные значения): dim и C₂ инвариантны относительно конъюгации (p,q)↔(q,p), доказано через коммутативность сложения/умножения и lia. Это структурная (не точечная) собственность — то, что 3 и 3̄ имеют одинаковую размерность и Казимир. Классический факт теории представлений SU(3); здесь даёт общий, а не пример-вычисляемый результат. _(conjugation, symmetry, universally-quantified)_

**Uniqueness - score 1 (exposition).** Чистая точная (ℚ/ℕ) формализация стандартных формул представлений SU(3) — размерность Вейля и квадратичный Казимир — с проверкой названных мультиплетов и общей конъюгационной симметрии; арифметическое Element-дно ветки.
> _Caveat:_ Полностью классическая теория представлений SU(3) (формулы Вейля/Дынкина, Казимир); НИЧЕГО математически нового. Ценность — роль точного фундамента (особенно C₂(1,0)=4/3, несущее для штрафа и транфера), а не результат. DRIFT: шапка заявляет 20 Qed, фактически 18 (две Definition без Qed).

---

## #515 - `src/gauge/SU3StringTension.v` - score 2 (methods)

**SU(3) string tension σ=1−β/18 over Q: monotone decrease σ(6)=2/3>σ(12)=1/3>σ(18)=0, strong coupling**

- **Topic.** Defines the strong-coupling SU(3) string tension sigma_su3_strong(β)=1−β·(1/18) (linear Creutz-ratio approximation) and proves its exact rational values at β=0,6,12,18, positivity at β=6, monotone decrease with β (asymptotic-freedom signature), and the ratio σ(6)=2·σ(12).
- **Role.** Methods leaf of the SU(3) observable suite. Pure Stdlib dependency only (self-contained linear formula). Reused by SU3ObservablesSynthesis (observables_sigma) and SU3GrandSynthesis (su3_full_stats) for the σ(6)=2/3 fact.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa
- **E/R/R.** _Elements:_ конкретные рациональные значения натяжения: σ(0)=1, σ(6)=2/3, σ(12)=1/3, σ(18)=0, σ(5.7). _Roles:_ sigma_su3_strong — роль натяжения струны (наклон ареа-закона / коэффициент конфайнмента); убывание с β — роль сигнатуры асимптотической свободы. _Rules:_ σ = 1 − β·(1/18) (линейное приближение -ln(β/18)); сравнения значений через rewrite+lra. _P4:_ линейная формула — КОНЕЧНОЕ усечение логарифма (нетерминирующего процесса): Element-усечение role-limit; осмысленна лишь при малых β (вблизи сильной связи), где σ>0; при β=18 σ обнуляется (граница применимости), физический континуум β→∞ = role-limit, не охвачен.
- **Classical counterpart.** Strong-coupling string tension of SU(3) lattice gauge theory from the Creutz ratio, σ=-ln(β/18) with the leading linear approximation σ≈1-β/18, decreasing with β (a strong-coupling signature, the precursor of asymptotic freedom). Classical (Wilson area law, Creutz). What differs: σ is taken in the crude LINEAR truncation of the logarithm and evaluated as exact rationals (σ(6)=2/3, σ(12)=1/3, σ(18)=0), with an honest note that 2/3 ≫ the MC value 0.044 because this is strong, not continuum, coupling.
- **Tags.** gauge, SU3, lattice, string-tension, creutz-ratio, asymptotic-freedom, linear-approx, exact-Q, strong-coupling, methods
- **Notes.** Qed DRIFT: STATUS header says '12 Qed', actual Qed.=10 (9 Lemma + 1 Theorem with Qed; sigma_su3_strong is a Definition, no Qed; header over-counted by including the Definition and miscounting). 0 Admitted, 0 own axioms. Honesty anchor: in-file comment states σ≈2/3 is far above MC σa²≈0.044 at β=6 — strong, not continuum, coupling.

**Lemmas (11):**

| name | kind | role |
|---|---|---|
| `sigma_su3_strong` | Definition | натяжение струны σ(β)=1−β·(1/18) (линейное приближение Creutz-ratio) |
| `sigma_at_0` | Lemma | σ(0)=1 (максимальный конфайнмент при нулевой связи) |
| `sigma_su3_at_6` | Lemma | ★ σ(6)=2/3 (несущее значение, потребляется обоими капстоунами) |
| `sigma_su3_at_12` | Lemma | σ(12)=1/3 |
| `sigma_su3_at_18` | Lemma | σ(18)=0 (граница применимости линейного приближения) |
| `sigma_positive_6` | Lemma | 0<σ(6) (натяжение положительно при β=6) |
| `sigma_decreases_6_12` | Lemma | σ(12)<σ(6): убывание с β (асимптотическая свобода) |
| `sigma_decreases_12_18` | Lemma | σ(18)<σ(12): продолжение убывания |
| `sigma_at_57` | Lemma | σ(5.7)=1−(57/10)(1/18) (точка для сравнения с MC) |
| `sigma_ratio` | Lemma | σ(6)=2·σ(12) (точное отношение 2:1) |
| `string_tension_synthesis` | Theorem | ★ сводка: σ(6)=2/3 ∧ >0 ∧ убывает ∧ σ(18)=0 |

**Key lemmas (deep):**

- **`sigma_su3_at_6`** - Несущее значение файла наружу: σ(6)=2/3 — единственный факт отсюда, который потребляют оба капстоуна (su3_observables_complete и su3_full_stats). Доказательство — одно `ring` над ℚ из линейной формулы. Файл сам честно отмечает (комментарий): 2/3 на порядок БОЛЬШЕ MC-значения σa²≈0.044 при β=6, потому что это сильная, а не континуумная связь. Так что значение — машинно-проверенный артефакт грубой модели, не предсказание физической QCD. _(string-tension, exact-Q, load-bearing, honest-gap)_
- **`sigma_decreases_6_12`** - Качественная сигнатура асимптотической свободы: σ убывает с ростом β (σ(12)<σ(6)), а пара sigma_decreases_12_18 продолжает тренд до σ(18)=0. Это правильный знак эффекта (большая связь → меньший конфайнмент в этом приближении). Честно — линейная формула σ=1−β/18 — крайне грубое усечение -ln(β/18); монотонность тривиальна (линейна по β) и обнуляется при β=18, что и есть граница смысла приближения, а не физика. _(asymptotic-freedom, monotone, linear-approx, qualitative)_

**Uniqueness - score 2 (methods).** Точная рациональная формализация строго-связной струнной натяжённости SU(3) (линейный Creutz-ratio σ=1−β/18) с машинно-проверенными значениями и монотонным убыванием как сигнатурой асимптотической свободы.
> _Caveat:_ Стандартная сильно-связная решёточная физика; σ взято в ГРУБОМ линейном приближении логарифма, монотонность тривиальна (линейна), σ(18)=0 — лишь граница применимости. Файл сам признаёт: σ(6)=2/3 ≫ MC 0.044 — это НЕ предсказание континуумной QCD. DRIFT: шапка заявляет 12 Qed, фактически 10 (одна Definition без Qed).

---

## #516 - `src/gauge/SU3Synthesis.v` - score 1 (exposition)

**SU(3) representation theory synthesis: dims, Casimirs, mass gap, partition fn at beta=1**

- **Topic.** Capstone of the SU(3) sub-thread (Phase 1): re-exports and bundles the verified numbers — dim(3)=3, dim(8)=8, dim(10)=10, dim(27)=27, C2(fund)=4/3, C2(adj)=3, gap_su3(1)=5/6, Z_su3(1)>0 — into two omnibus theorems.
- **Role.** Pure consolidation node: imports SU3Representations, SU3Characters, SU3Transfer and re-exports their named facts via exact-application proofs. Adds no new computation. Terminal in the SU(3) chain; not reused by other gauge files (leaf synthesis).
- **Counts.** Qed 5 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lia ZArith Lqa; gauge.SU3Representations; gauge.SU3Characters; gauge.SU3Transfer
- **E/R/R.** _Elements:_ конкретные рациональные числа — размерности неприводимых SU(3) (3,8,10,27), казимиры (4/3, 3), коэффициенты переноса t_fund=1/6, t_adj=1/72, статсумма Z(1)=44/9. _Roles:_ роль файла — собиратель: каждое число несёт роль (размерность / казимир / щель / статсумма); сами теоремы — омнибус-конъюнкции, фиксирующие весь набор. _Rules:_ правила = арифметические тождества разложения по характерам, доказанные в импортируемых файлах; здесь только split + exact <именованный факт>. _P4:_ всё конечно-актуально: фиксированный калибр SU(3), фиксированная связь beta=1, конечный набор неприводимых до (2,2). Никакого континуума, никакого N->inf; это снимок Element-стороны при одном значении связи, а не утверждение о пределе.
- **Classical counterpart.** Классика: теория представлений su(3) (формула размерности Вейля для (p,q), квадратичный казимир C2=(p^2+q^2+pq+3p+3q)/3) и сильносвязное разложение Вильсоновой решёточной статсуммы по характерам. Здесь НЕТ ничего нового по содержанию — лишь конкретные рациональные значения при одной связи, переупакованные в E/R/R-снимок.
- **Tags.** gauge, su3, synthesis, characters, mass-gap-model, lattice, exposition

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `su3_dimensions_correct` | Lemma | dim(1,0)=3 /\ dim(1,1)=8 /\ dim(3,0)=10 (размерности неприводимых) |
| `su3_casimirs_correct` | Lemma | C2(1,0)=4/3 /\ C2(1,1)=3 (квадратичные казимиры фунд./присоед.) |
| `su3_gap_and_Z` | Lemma | gap_su3(1)=5/6 /\ 0<Z_su3(1) (щель и положительность статсуммы при beta=1) |
| `su3_rep_complete` | Theorem | ★ омнибус: dims + казимир + щель 5/6 + Z>0 в одной конъюнкции |
| `su3_phase1_stats` | Theorem | ★ второй омнибус: dim(0,0)=1, dim(2,2)=27, t_fund=1/6, t_adj=1/72 |

**Key lemmas (deep):**

- **`su3_rep_complete`** - Главная конъюнкция-снимок SU(3): пять проверенных фактов (две размерности, казимир фундаментала 4/3, щель 5/6, положительность статсуммы) собраны в одну теорему через exact-применение лемм из SU3Transfer/SU3Representations. Ценность нулевая по содержанию (всё доказано выше) — это удобная точка ссылки. Честно: ЭТО НЕ доказательство щели масс SU(3); это значение модельной функции gap_su3 при beta=1 на грубом разложении по характерам. _(synthesis, su3, snapshot, no-new-content)_
- **`su3_phase1_stats`** - Второй сборник: размерность тривиала=1, размерность (2,2)=27 и два коэффициента переноса t_fund=1/6, t_adj=1/72. Подтверждает, что упаковка не теряет фактов разложения по характерам. Чисто экспозиционно. _(su3, characters, exposition)_

**Uniqueness - score 1 (exposition).** Чистый собиратель Phase-1 SU(3): фиксирует проверенные размерности/казимиры/щель/статсумму в двух омнибус-теоремах для удобной ссылки.
> _Caveat:_ 0 нового содержания — все факты доказаны в импортируемых файлах. Классическая теория представлений su(3). gap_su3(1)=5/6 — значение модельной функции при beta=1 на грубом разложении, НЕ доказательство щели масс SU(3) и НЕ континуумный результат. Заголовок 'complete' аспирационен.

---

## #517 - `src/gauge/SU3Transfer.v` - score 2 (methods)

**SU(3) transfer-matrix observables from character expansion: Z, plaquette, gap = 1 - beta/6**

- **Topic.** Defines the leading-order SU(3) partition function Z(beta)=1+3beta+8beta^2/9, the plaquette expectation dZ/dbeta / Z, and the mass-gap proxy gap_su3(beta)=t_trivial - t_fund = 1 - beta/6; evaluates them at beta in {0,1,3} and proves positivity for small beta.
- **Role.** Computational core of the SU(3) sub-thread. Imports SU3Representations + SU3Characters; consumed by SU3Synthesis (which re-exports gap_su3_at_1, Z_su3_positive_1, etc.). Defines Z_su3_approx, plaquette_su3, gap_su3 used downstream.
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; gauge.SU3Representations; gauge.SU3Characters
- **E/R/R.** _Elements:_ рациональные функции от связи beta: статсумма Z(beta), производная dZ/dbeta, плакетка, щель gap_su3(beta); их значения в точках beta=0,1,3. _Roles:_ Z = роль нормировки/суммы по неприводимым; плакетка = роль наблюдаемой (среднее действие); gap_su3 = роль щели (разность коэффициентов переноса тривиала и фундаментала). _Rules:_ Z = 1 + 3beta + (8/9)beta^2 (ведущий порядок разложения dim^2 * t); gap = t_trivial - t_fund = 1 - beta/6 > 0 при beta<6; доказательства — unfold + ring/field/lra. _P4:_ конечно-актуально и линейно/квадратично: всё вычисляется точно над Q в одной-двух точках связи. 'gap>0 для beta<6' — это положительность конкретного многочлена 1-beta/6, а не спектральная щель оператора; континуум (beta->6 или N->inf) НЕ берётся.
- **Classical counterpart.** Классика: сильносвязное (character/hopping) разложение решёточной калибровочной статсуммы (Wilson 1974; Drouffe-Zuber), где Z разлагается по неприводимым представлениям с весами t. Плакетка = логарифмическая производная Z. Отличие: здесь не выводится разложение, а постулируется его ведущий порядок как явный многочлен над Q и вычисляется в нескольких точках; 'gap' — линейная прокси, не спектр.
- **Tags.** gauge, su3, transfer-matrix, partition-function, strong-coupling, mass-gap-model, lattice, methods
- **Notes.** STATUS header claims 15 Qed; actual Qed. count = 13 (drift). 0 own axioms.

**Lemmas (17):**

| name | kind | role |
|---|---|---|
| `Z_su3_approx` | Definition | статсумма ведущего порядка Z(beta)=1+3beta+(8/9)beta^2 |
| `Z_su3_at_0` | Lemma | Z(0)=1 (ring) |
| `Z_su3_at_1` | Lemma | Z(1)=44/9 (ring) |
| `Z_su3_positive_1` | Lemma | 0<Z(1) (используется в SU3Synthesis) |
| `Z_su3_positive_0` | Lemma | 0<Z(0) |
| `dZ_dbeta` | Definition | производная статсуммы dZ/dbeta = 3 + (16/9)beta |
| `plaquette_su3` | Definition | среднее плакетки = (dZ/dbeta)/Z |
| `dZ_at_0` | Lemma | dZ/dbeta(0)=3 |
| `plaquette_su3_at_0` | Lemma | плакетка(0)=3 (field) |
| `plaquette_positive` | Lemma | 0<dZ/dbeta(1) (числитель плакетки положителен) |
| `gap_su3` | Definition | щель = t_trivial_su3 - t_fund_su3 = 1 - beta/6 |
| `gap_su3_at_0` | Lemma | gap(0)=1 |
| `gap_su3_at_1` | Lemma | gap(1)=5/6 (используется в SU3Synthesis) |
| `gap_su3_positive_1` | Lemma | 0<gap(1) |
| `gap_su3_at_3` | Lemma | gap(3)=1/2 |
| `gap_decreases` | Lemma | gap(1)>gap(3) — щель падает с ростом связи |
| `su3_transfer_synthesis` | Theorem | ★ конъюнкция: Z(1)=44/9, gap(1)=5/6, gap(1)>0, Z(1)>0 |

**Key lemmas (deep):**

- **`gap_su3`** - Определение щели как разности коэффициентов переноса тривиала и фундаментала: 1 - beta/6. Это ЛИНЕЙНАЯ модельная функция, а не собственное значение трансфер-матрицы. Положительность для beta<6 — тривиальная положительность многочлена. gap_decreases фиксирует ожидаемое физическое поведение (связь слабеет — щель падает), но без континуумного предела это лишь сравнение двух рациональных значений. _(mass-gap-model, su3, linear, characters)_
- **`Z_su3_approx`** - Статсумма ведущего порядка: сумма dim(p,q)^2 * t_{p,q} обрезанная до тривиала+фунд.+антифунд.+присоед. = 1+3beta+(8/9)beta^2. Это однопетлевое/сильносвязное приближение, а не точная Вильсонова статсумма. Все наблюдаемые (плакетка) строятся из неё, поэтому она — вычислительное дно сабтреда. _(partition-function, strong-coupling, su3, leading-order)_

**Uniqueness - score 2 (methods).** Точная рациональная (Q) реализация ведущего порядка сильносвязного разложения SU(3): статсумма, плакетка и линейная прокси-щель, вычисленные машинно в конкретных точках связи.
> _Caveat:_ Header 'STATUS: 15 Qed' завышен — фактически 13 Qed (drift). Стандартное сильносвязное разложение; gap_su3=1-beta/6 — линейная прокси, НЕ собственное значение трансфер-матрицы и НЕ доказательство щели масс. Только ведущий порядок, только SU(3), без континуума.

---

## #518 - `src/gauge/Synthesis2D.v` - score 3 (new-framing)

**2+1D mass-gap synthesis at K=2: spatial plaquette rescues the gap (gap = 3/4 at beta=8)**

- **Topic.** Capstone of the 2D thread: contrasts 1+1D (gap_2x2 vanishes at beta=8) against 2+1D (mass_gap_2d_at_8 = 3/4 = 1 - gamma(8)^2 with gamma(8)=1/2), exhibits the 4x4->block eigenvalues {1,1,1/4,1/4}, and asserts gap_antisymmetric(beta)>0 for all beta in (0,8).
- **Role.** Top-level consolidation of the 2+1D K=2 computation: imports Coupled2D, BlockDiagonal2D, Gap2D, TransferMatrix, ExactEigenvalues, GapBound, StrongCoupling and re-exports their named facts. Leaf synthesis (not reused).
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; gauge.Coupled2D; gauge.BlockDiagonal2D; gauge.Gap2D; gauge.TransferMatrix; gauge.ExactEigenvalues; gauge.GapBound; gauge.StrongCoupling
- **E/R/R.** _Elements:_ рациональные значения щели в двух размерностях: mass_gap_2x2(8)=0, mass_gap_2d_at_8=3/4, gamma_2d(8)=1/2, собственные значения блока {1,1/4}, след 5/4, детерминант 1/4. _Roles:_ размерность пространства-времени = роль (1+1D без щели против 2+1D со щелью); пространственная плакетка/вес gamma = роль источника конфайнмента; щель = 1 - gamma^2 = роль фактора подавления. _Rules:_ gap_2d = 1 - gamma^2; gamma(8)=1/2 -> gap=3/4; 4x4 трансфер блочно-диагонализуется, собственные {1,1,1/4,1/4}; доказательства — exact <именованный факт> + lra. _P4:_ всё конечно: фиксированный обрез K=2 (4 состояния на связь), фиксированная связь beta=8, конкретная 4x4 матрица. 'survives continuum limit' означает лишь, что значение при beta=8 (точка RG) равно 3/4 — это снимок в одной точке, НЕ предел N->inf и НЕ континуум. Заявка 'mass gap in 2+1D' аспирационна.
- **Classical counterpart.** Классика: аргумент Пайерлса/сильной связи о конфайнменте в решёточных калибровочных теориях (Wilson 1974), где пространственные плакетки дают энергетическую щель возбуждениям; точная диагонализация малой трансфер-матрицы. Отличие: здесь всё на конкретной 2-состоянийной (K=2) решётке при beta=8 над Q; 'survives continuum' = значение в одной RG-точке, не предел.
- **Tags.** gauge, 2plus1D, mass-gap, confinement, transfer-matrix, block-diagonal, finite-lattice, new-framing, over-branded-name
- **Notes.** STATUS header '~15 Qed' (and SUMMARY '~15') vs actual 10 Qed. (drift). File name/comments are aspirational ('COMPLETE 2+1D RESULT', 'Distance to Millennium') but the file itself flags 3+1D continuum as open. 0 own axioms.

**Lemmas (10):**

| name | kind | role |
|---|---|---|
| `dimension_comparison` | Theorem | ★ 1+1D gap=0 при beta=8 против 2+1D gap=3/4; 1/8 < 3/4 |
| `gap_ratio` | Theorem | 3/4 = 6 * (1/8) (целочисленное соотношение щелей) |
| `gap_anatomy_2d` | Theorem | gap_2d = 1 - gamma^2, gamma(8)=1/2, 1-1/4=3/4 (анатомия щели) |
| `tension_still_positive` | Theorem | 0 < string_tension(8) (натяжение струны положительно) |
| `continuum_gap_2d` | Theorem | gap=3/4, >0, и gap_antisymmetric(8)=3/4 |
| `spatial_mechanism_universal` | Theorem | forall beta in (0,8): 0<gap_antisymmetric(beta) |
| `the_2d_story` | Theorem | ★ полная история: 1+1D пол + 2+1D собств.векторы + gap=3/4 + положительность на (0,8) |
| `what_remains` | Theorem | gap_2x2(8)=0 /\ 0<3/4 (контраст размерностей) |
| `synthesis_2d_main` | Theorem | ★ собств.значения, след 5/4, детерм. 1/4, проверка следа, щель>0, 3/4=6*(1/8) |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`dimension_comparison`** - Центральное наблюдение треда: при K=2 и beta=8 одномерная щель ОБНУЛЯЕТСЯ (стена), а двумерная равна 3/4. Механизм — пространственная плакетка добавляет вес gamma<1, подавляющий рассогласованные конфигурации, и щель = 1 - gamma^2. Это аккуратная конкретная иллюстрация 'пространство создаёт конфайнмент', НО на фиксированной 4x4 матрице при одной связи. Честно: это НЕ теорема о существовании щели в 2+1D континууме. _(dimension, confinement, gap-2d, finite-lattice)_
- **`synthesis_2d_main`** - Сборка всей 2+1D картины: собственные значения блока {1, 1/4}, след 1+1/4+1/4+1=5/2 (проверка), детерминант 1/4, и итоговая щель 3/4=6*(1/8). Демонстрирует, что блочная диагонализация 4x4 трансфер-матрицы согласована (след/детерминант сходятся). Чисто проверочный омнибус поверх ExactEigenvalues/BlockDiagonal2D. _(eigenvalues, block-diagonal, synthesis, 4x4)_

**Uniqueness - score 3 (new-framing).** E/R/R-обрамлённый снимок: пространственное измерение как роль-источник конфайнмента — точная 4x4 блочная диагонализация даёт щель 3/4=1-gamma^2 в 2+1D там, где 1+1D даёт 0.
> _Caveat:_ Header '~15 Qed' и SUMMARY-блок завышены — фактически 10 Qed (drift; SUMMARY перечисляет 10, но '~15' в шапке вводит в заблуждение). Стандартный аргумент Пайерлса о конфайнменте. Конкретная конечная решётка K=2, beta=8 — НЕ доказательство щели масс 2+1D и тем более не 3+1D Millennium. Заголовок 'COMPLETE 2+1D RESULT' / 'Distance to Millennium' аспирационен; сам файл это честно помечает как открытые пункты.

---

## #519 - `src/gauge/TensorGapBound.v` - score 3 (new-framing)

**3+1D continuum gap bound >= 1/18 via tensor product M(x)M(x)M of a 1D continuum operator**

- **Topic.** Argues a positive mass-gap proxy in the 3+1D continuum limit: from the 1D operator's eigenvalues (lambda0=2/3, lambda1<13/24) the tensor operator on V27 has ground (2/3)^3=8/27 and second eigenvalue <= (2/3)^2*(13/24)=13/54, giving gap >= 8/27 - 13/54 = 1/18 > 0.
- **Role.** Top of the tensor/continuum gap argument. Imports ExactEigenvalues, GapBound, Gap3D and combines their facts; the headline bound feeds the overall mass-gap narrative. Leaf result (not imported elsewhere within this batch).
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; gauge.ExactEigenvalues; gauge.GapBound; gauge.Gap3D
- **E/R/R.** _Elements:_ рациональные собственные значения: 1D ground lambda0=2/3, граница lambda1<13/24; тензорные tensor_ground=8/27, tensor_second_bound=13/54, tensor_gap_3d=1/18. _Roles:_ тензорное произведение M(x)M(x)M = роль перехода 1D->3D; ground/second = роли низшего и следующего уровней; разность = роль щели. _Rules:_ собств. значения тензора = произведения lambda_i*lambda_j*lambda_k; ground=lambda0^3=(2/3)^3=8/27; second<=lambda0^2*lambda1<(4/9)(13/24)=13/54; gap=8/27-13/54=1/18>0; доказательства — точная Q-арифметика (lia/lra) + два импортированных факта q(13/24)>0, q(0)<0. _P4:_ конечно-актуально на уровне АЛГЕБРЫ собственных значений (конечная V27, точные рациональные оценки), НО 'continuum operator M' — это уже идеализированный предельный объект, чьи собственные значения берутся из GapBound. Граница условна: она опирается на lambda1<13/24 (через знаки квадратичного фактора) и на структуру второго собственного значения тензора как <=lambda0^2*lambda1 — последнее НЕ доказано здесь как точная характеризация спектра тензора, а взято как оценка.
- **Classical counterpart.** Классика: спектр тензорного произведения операторов = произведения спектров (sigma(A(x)B)=sigma(A)*sigma(B)); оценка спектральной щели снизу через ground и второй уровень. Отличие: здесь 1D-собственные значения берутся как заданные рациональные значения/границы конкретной модели, а 'континуум' и 'V27' — модельные идеализации; результат — арифметическое неравенство 1/18>0, условное на 1D-спектре, а не теорема о щели Янга-Миллса.
- **Tags.** gauge, 3plus1D, tensor-product, mass-gap, continuum, conditional, new-framing, over-branded-name
- **Notes.** STATUS header '~15 Qed' vs actual 14 Qed. (minor drift). In-file comment claims it 'proves mass gap > 0 in the 3+1D continuum limit' — aspirational/over-branded; result is a conditional rational inequality. 0 own axioms.

**Lemmas (17):**

| name | kind | role |
|---|---|---|
| `tensor_ground` | Definition | tensor_ground := 8/27 (низший уровень = lambda0^3) |
| `tensor_second_bound` | Definition | tensor_second_bound := 13/54 (верхняя оценка второго уровня) |
| `tensor_gap_3d` | Definition | tensor_gap_3d := 1/18 (щель 3+1D континуум) |
| `tensor_ground_from_1d` | Theorem | (2/3)^3 = 8/27 = tensor_ground |
| `tensor_ground_positive` | Theorem | 0 < tensor_ground |
| `lambda_1_bound` | Theorem | 0<q(13/24) /\ q(0)<0 (знаки квадратичного фактора => lambda1<13/24) |
| `lambda_0_squared` | Theorem | (2/3)^2 = 4/9 |
| `product_value` | Theorem | (4/9)(13/24) = 13/54 |
| `tensor_second_from_1d` | Theorem | (2/3)^2*(13/24) = tensor_second_bound |
| `tensor_gap_value` | Theorem | ★ tensor_ground - tensor_second_bound = 1/18 |
| `tensor_gap_3d_positive` | Theorem | ★ 0 < tensor_gap_3d (щель положительна) |
| `ground_exceeds_second` | Theorem | tensor_second_bound < tensor_ground |
| `gap_3d_vs_1d_continuum` | Theorem | tensor_gap_3d (1/18) < 1/8 (1+1D континуум) |
| `gap_3d_continuum_vs_lattice` | Theorem | tensor_gap_3d < mass_gap_3d_at_8 (континуум < решётка) |
| `both_3d_gaps_positive` | Theorem | 0<mass_gap_3d_at_8 /\ 0<tensor_gap_3d |
| `tensor_gap_bound_main` | Theorem | ★ омнибус: lambda0=корень, lambda1<13/24, ground=8/27, second=13/54, gap=1/18>0 |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`tensor_gap_value`** - Сердце аргумента: 8/27 - 13/54 = 1/18, точное рациональное вычитание (lia на Qeq). Идея — спектр тензора M(x)M(x)M есть произведения 1D-собственных значений, поэтому щель 3D >= ground^{1/3-структура} минус оценка второго уровня. Алгебра безупречна над Q. НО: что 'второй по величине' собственный уровень тензора <= lambda0^2*lambda1 — это оценка из структуры произведений, и весь вывод УСЛОВЕН на том, что 1D-оператор действительно имеет lambda0=2/3 и lambda1<13/24 (импортируется из GapBound), и что континуумный оператор корректно определён. _(tensor, gap-bound, continuum, conditional)_
- **`tensor_gap_bound_main`** - Флагманский омнибус файла: связывает 1D-факты (char_poly(2/3)=0, q(13/24)>0) с тензорными значениями (8/27, 13/54, 1/18>0) в одну цепочку. Это аккуратная сборка, но именно та точка, где аспирационное имя расходится с содержанием: 'proves mass gap > 0 in the 3+1D continuum limit' (комментарий) НЕ доказано — доказано лишь, что ЕСЛИ спектр 1D таков, ТО разность двух явных рациональных оценок положительна. _(synthesis, continuum, over-branded-name, conditional)_

**Uniqueness - score 3 (new-framing).** E/R/R-обрамлённая тензорная оценка: щель 3+1D континуума >= 1/18 получена точной Q-арифметикой из 1D-спектра через структуру собственных значений M(x)M(x)M.
> _Caveat:_ Header '~15 Qed' vs фактически 14 (минорный drift). Условный результат: всё опирается на 1D-факты lambda0=2/3, lambda1<13/24 (импорт) и на оценку второго уровня тензора. Комментарий 'proves mass gap > 0 in the 3+1D continuum limit' — ОВЕРКЛЕЙM: доказано рациональное неравенство при заданном 1D-спектре, НЕ Millennium-щель Янга-Миллса. Конкретная модель, не общая SU(N) Хаар-теория.

---

## #520 - `src/gauge/ThermodynamicLimit.v` - score 3 (new-framing)

**Gap survives N->infinity: Peierls local cost 3/4 at beta=8, Gershgorin positivity for general beta**

- **Topic.** Two N-uniformity arguments for the 2D strip gap: (1) at beta=8 the domain-wall cost 1-gamma^2=3/4 is local and N-independent, so strip_gap_at_8=3/4 for all N; (2) for general beta a Gershgorin gap bound domain_wall_cost - N*alpha*(1+gamma) is checked positive at small concrete (N,beta), with wall_cost>0 for 0<beta<16.
- **Role.** Top-level thermodynamic-limit argument of the strip thread. Imports DomainWalls, StripTransfer, StripSpectrum, Coupled2D and re-exports/combines gamma_at_8, alpha_at_8, strip_gap_at_8, plus its own domain_wall_cost / gershgorin_gap definitions. Leaf synthesis.
- **Counts.** Qed 20 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith List Bool Lqa; gauge.DomainWalls; gauge.StripTransfer; gauge.StripSpectrum; gauge.Coupled2D
- **E/R/R.** _Elements:_ стоимость доменной стенки domain_wall_cost(beta)=1-gamma^2 в точках beta=0,2,4,8; вес gamma_2d, связь alpha_2d; Gershgorin-щель gershgorin_gap(n,beta) в точках (1,7),(2,7),(n,8); strip_gap_at_8=3/4. _Roles:_ доменная стенка = роль локального возбуждения (одна плакетка); её стоимость = роль щели; gamma/alpha = роли пространственного веса и недиагональной связи; число узлов N = роль размера системы (от которой щель НЕ зависит при beta=8). _Rules:_ стоимость = 1 - gamma^2; при beta=8 alpha=0 => трансфер диагонален => щель = 3/4 НЕЗАВИСИМО от N; для общего beta Gershgorin: щель >= cost - N*alpha*(1+gamma), положительна при малых N*alpha; wall_cost>0 при 0<beta<16 (через факторизацию beta(32-beta)/256, nra). _P4:_ ядро аргумента Пайерлса конечно-актуально и ЧЕСТНО универсально по N в одной точке: при beta=8 стоимость локальна, поэтому щель=3/4 для ЛЮБОГО N — это настоящая N-равномерность (не снимок). НО для ОБЩЕГО beta равномерность по N НЕ доказана: Gershgorin-граница проверяется лишь в конкретных (N,beta), а 'continuity'/'order of limits' — структурные наблюдения (все функции рациональны), а не доказанные пределы. Это конечно-решёточный/конечно-точечный результат, не континуум.
- **Classical counterpart.** Классика: аргумент Пайерлса (1936) о фазовых переходах/щели через локальную стоимость доменных стенок; теорема Гершгорина о локализации собственных значений для оценки спектральной щели; термодинамический предел N->inf. Отличие: здесь Пайерлс реализован точно над Q для конкретной 2D-полосы при beta=8 (где он строго N-равномерен), но Гершгорин-распространение на общий beta проверено лишь точечно; 'order of limits' — рациональность функций, не доказанные пределы.
- **Tags.** gauge, thermodynamic-limit, peierls, gershgorin, domain-wall, mass-gap, 2plus1D, finite-lattice, new-framing, conditional
- **Notes.** STATUS header '~40 Qed' and SUMMARY '~28 Qed' vs actual 20 Qed. (significant drift). SUMMARY block also lists lemmas not present in the file (gershgorin_N2_beta6, gap_condition_concrete). N-uniformity is rigorous only at beta=8; general-beta N->inf is not established (Gershgorin checked only at concrete (N,beta)). step5_uniformity/order_of_limits are trivial reflexivity. 0 own axioms.

**Lemmas (24):**

| name | kind | role |
|---|---|---|
| `peierls_local_cost` | Theorem | 1 - gamma(8)^2 = 3/4 (локальная стоимость доменной стенки) |
| `gamma_sq_at_8` | Lemma | gamma(8)^2 = 1/4 |
| `peierls_gap_uniform` | Theorem | forall n>=2: 1 - quarter_power 1 = 3/4 (щель не зависит от n) |
| `domain_wall_cost` | Definition | стоимость стенки = 1 - gamma_2d(beta)^2 |
| `wall_cost_at_8` | Lemma | cost(8)=3/4 |
| `wall_cost_at_4` | Lemma | cost(4)=7/16 (gamma=3/4) |
| `wall_cost_positive` | Lemma | ★ 0<beta<16 => 0<cost(beta) (через nra, факторизация beta(32-beta)/256) |
| `wall_cost_at_0` | Lemma | cost(0)=0 (нет связи) |
| `wall_cost_at_2` | Lemma | cost(2)=15/64 |
| `alpha_near_8` | Lemma | 0<beta<8 => 0<alpha(beta)<1 (малость недиагонали) |
| `diagonal_at_critical` | Theorem | alpha(8)=0 /\ gamma(8)=1/2 /\ cost(8)=3/4 (трансфер диагонален при beta=8) |
| `gershgorin_radius_ground` | Definition | радиус Гершгорина строки основного состояния = N*alpha*gamma |
| `gershgorin_radius_excited` | Definition | радиус для возбуждённого состояния = N*alpha |
| `gershgorin_gap` | Definition | Gershgorin-оценка щели = cost - N*alpha*(1+gamma) |
| `gershgorin_N2_beta7` | Lemma | 0 < gershgorin_gap 2 7 (конкретная проверка N=2,beta=7) |
| `gershgorin_at_8` | Lemma | forall n: gershgorin_gap n 8 = cost(8) (alpha=0 убирает N-зависимость) |
| `gap_condition_N1_beta7` | Lemma | 0 < gershgorin_gap 1 7 (vm_compute) |
| `step1_gap_at_8` | Theorem | forall n>=2: strip_gap_at_8 = 3/4 |
| `step2_continuity` | Theorem | cost(0)=0, cost(4)=7/16, cost(8)=3/4 (рациональность в beta) |
| `step3_rg_convergence` | Theorem | alpha(8)=0 /\ strip_gap_at_8=3/4 (RG-точка beta=8) |
| `step5_uniformity` | Theorem | forall n1 n2>=2: strip_gap_at_8 = strip_gap_at_8 (тривиальная рефлексивность N-независимости) |
| `mass_gap_thermodynamic` | Theorem | ★ strip_gap_at_8 = 3/4 /\ 0 < strip_gap_at_8 |
| `order_of_limits` | Theorem | внутр. предел (beta->8)=3/4 для каждого N; внеш. предел константы = константа |
| `peierls_summary` | Theorem | ★ стоимость 3/4, не зависит от N, >0, и cost(4)>0 |

**Key lemmas (deep):**

- **`peierls_local_cost`** - Настоящее ядро: стоимость одной доменной стенки = 1 - gamma^2 = 3/4 ЛОКАЛЬНА (одна плакетка), поэтому при beta=8 щель = 3/4 для ЛЮБОГО числа узлов N. Это честная N-равномерность — strip_gap_at_8 буквально не содержит N. Аргумент Пайерлса в действии: локальная стоимость возбуждения => щель, не зависящая от размера. Это самое сильное место файла и единственное, где 'N->infinity' оправдано по существу (для одной точки beta=8). _(peierls, N-uniform, domain-wall, load-bearing)_
- **`wall_cost_positive`** - Единственная нетривиальная вычислительная лемма: 0<beta<16 => 0<1-gamma^2. Через факторизацию 1-(1-beta/16)^2 = beta(32-beta)/256 и nra. Даёт положительность стоимости (а значит и Gershgorin-щели при alpha->0) во ВСЁМ физическом диапазоне связи, а не только в точках. Контрастирует с тривиальными reflexivity-леммами step5/order_of_limits. _(positivity, nra, general-beta, factorization)_
- **`gershgorin_gap`** - Попытка распространить N-равномерность на общий beta: щель >= cost - N*alpha*(1+gamma). Честно: положительность доказана ЛИШЬ в конкретных (N,beta)=(1,7),(2,7) и в пределе alpha->0 (beta=8). Для растущего N при фиксированном beta<8 граница НЕ доказана положительной (N*alpha может превысить cost). Поэтому 'gap survives N->infinity for general beta' — НЕ установлено; это открытая часть, замаскированная step2/step3 (структурные наблюдения о рациональности, не пределы). _(gershgorin, conditional, general-beta, gap-in-argument)_

**Uniqueness - score 3 (new-framing).** Аргумент Пайерлса, реализованный точно над Q: при beta=8 локальность стоимости доменной стенки даёт честно N-независимую щель 3/4; Gershgorin даёт каркас для общего beta.
> _Caveat:_ Header '~40 Qed' и SUMMARY '~28' сильно завышены — фактически 20 Qed (drift; SUMMARY также перечисляет несуществующие леммы gershgorin_N2_beta6, gap_condition_concrete). N-равномерность ДОКАЗАНА строго только при beta=8 (там strip_gap не содержит N); для общего beta Gershgorin проверен лишь в (1,7),(2,7), предел N->inf НЕ установлен. step5/order_of_limits/step2 — тривиальные reflexivity или структурные наблюдения, не пределы. Конечная решётка/конечные точки, не континуум и не Millennium.

---

## #521 - `src/gauge/TopologicalObstruction.v` - score 2 (methods)

**Honest obstruction ledger: what the Q 2x2 transfer model captures vs misses (no continuum, no topology)**

- **Topic.** A self-audit file: re-exports four 'captures' theorems (U(1) gap=0 at beta=8, finite-lattice gap>0, RG Cauchy, string tension>0) and labels four 'misses' (asymptotic freedom — coupling grows the wrong way; topology pi_3(SU(2))=Z; dimensional transmutation; instanton invisibility), bundling them into summary theorems.
- **Role.** Capstone/ledger of the 2x2 gauge sub-thread. Pure aggregation: every 'captures' theorem is `exact`-delegated to GapMatching/ExactRGProcess/StrongCoupling/SU2TransferMatrix; reuses mass_gap_2x2 (#523). Imports TransferMatrix, SU2TransferMatrix, StrongCoupling, GapMatching, ExactRGProcess, GapDecayRate, ConfinementCorrection. Not itself reused as a dependency; it is a terminal honesty document.
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS.CauchyReal; gauge.TransferMatrix; gauge.SU2TransferMatrix; gauge.StrongCoupling; gauge.GapMatching; gauge.ExactRGProcess; gauge.GapDecayRate; gauge.ConfinementCorrection
- **E/R/R.** _Elements:_ конкретная 2x2 матрица переноса в Q, beta, размер решётки k (nat), струнное натяжение, RG-орбита. _Roles:_ 'captures' = роль-достижимое моделью (Element-сторона: разрешимо конечной Q-арифметикой); 'misses' = роль-предел модели (топология/асимптотическая свобода — недостижимы над Q). _Rules:_ захват: gap_2x2(8)=0, gap>0 на конечной решётке, RG=Коши, sigma>0; промах: beta_k РАСТЁТ (противоположно асимптотической свободе), pi_3(SU(2))=Z нерепрезентируем над Q. _P4:_ ОДНА чёткая граница финитизации: то, что выражается конечной Q-арифметикой (Element), отделено от того, что требует R / непрерывного предела / топологических секторов (role-limit). Реифицировать топологию/инстантоны в 2x2-Q-модель = категориальная ошибка; файл честно фиксирует стену, а не пробивает её.
- **Classical counterpart.** Mirrors the textbook contrast between lattice strong-coupling confinement (Wilson) and the genuinely continuum/topological content of 4D Yang-Mills: asymptotic freedom (Gross-Wilczek-Politzer), instantons / pi_3(SU(2))=Z (Belavin-Polyakov-Schwartz-Tyupkin), dimensional transmutation (Lambda_QCD). NEW here is only the honest self-audit packaging — it re-cites already-proved facts from sibling files and labels what the Q-arithmetic 2x2 model can and cannot reach; no new mathematics.
- **Tags.** gauge, yang-mills, honesty, obstruction, finite-lattice, topology, asymptotic-freedom, anti-overclaim, U(1)
- **Notes.** Header 'STATUS: ~12 Qed' matches actual 12 Qed (0 Admitted, 0 axioms). 12 named declarations, all Theorem. topologically_trivial/(2=2), instanton_invisible/(2<3), total_count/(12=12) are vestigial marker-lemmas (trivial reflexivity/lia), not mathematical content. Aspirational naming ('topological_main') flagged: file does NOT prove the Millennium mass gap.

**Lemmas (12):**

| name | kind | role |
|---|---|---|
| `model_captures_u1` | Theorem | mass_gap_2x2 8 == 0 — U(1)-фотон безмассов (делегат gap_vanishes_at_8) |
| `model_captures_finite_lattice` | Theorem | gap>0 при любом конечном размере решётки k (делегат su2_gap_positive_all_k) |
| `model_captures_rg` | Theorem | RG-орбита — процесс Коши (делегат unconditional_cauchy) |
| `model_captures_strong_coupling` | Theorem | струнное натяжение sigma>0 при beta>0 (делегат string_tension_positive) |
| `model_misses_asymptotic_freedom` | Theorem | ★ beta_k РАСТЁТ с k — противоположно асимптотической свободе (делегат beta_k_increasing) |
| `model_misses_topology` | Theorem | повторно gap_2x2(8)=0: Q не несёт топологических секторов pi_3(SU(2))=Z |
| `model_misses_dim_transmutation` | Theorem | повторно gap_2x2(8)=0: Lambda_QCD требует R, не Q |
| `topologically_trivial` | Theorem | (2=2) — заглушка-маркер: K=2 матрица топологически тривиальна |
| `instanton_invisible` | Theorem | (2<3) — заглушка-маркер: инстантоны требуют K>2 и нелокального туннелирования |
| `obstruction_summary` | Theorem | конъюнкция 3 захватов + 1 промаха (beta_k растёт) |
| `topological_main` | Theorem | главная сводка: gap(8)=0 + конечный gap>0 + sigma>0 |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`model_misses_asymptotic_freedom`** - Самая честная строка файла: в этой Q-модели эффективная beta_k РАСТЁТ с масштабом, тогда как реальная КХД асимптотически свободна (связь УБЫВАЕТ на коротких расстояниях). Файл не маскирует это, а делает теоремой — модель ведёт себя ПРОТИВОПОЛОЖНО физике на УФ-конце. Сама beta_k_increasing доказана в ExactRGProcess; ценность здесь — поднять провал в явный реестр обструкций. Анти-оверклейм-якорь всего gauge-кластера. _(honesty, asymptotic-freedom, obstruction, anti-overclaim)_
- **`topological_main`** - Сводный 'главный' результат — но он НЕ доказывает массовую щель Янга-Миллса: это конъюнкция трёх конечно-Q-фактов (U(1)-gap обращается в 0 при beta=8; gap>0 на каждой КОНЕЧНОЙ решётке; sigma>0 в сильной связи). Континуумного предела, SU(2)/SU(3)-непертурбативного gap и топологии здесь нет. Имя 'topological_main' аспирационно; реальное содержание — паспорт ограничений 2x2-модели. _(summary, finite-lattice, not-millennium, delegation)_

**Uniqueness - score 2 (methods).** Необычная для формализаций вещь — машинно-проверенный РЕЕСТР ОБСТРУКЦИЙ: что Q-2x2-модель захватывает и, главное, чего принципиально не может (топология, асимптотическая свобода, размерная трансмутация), причём промахи — настоящие теоремы, а не комментарии.
> _Caveat:_ 0 нового содержания: все 'captures' — exact-делегаты соседних файлов, 'misses' — повторы или (2=2)/(2<3)-заглушки. НЕ доказывает Clay-проблему Янга-Миллса: только конечная решётка + сильная связь над Q; континуума, инстантонов, непертурбативного SU(2)/SU(3)-gap нет. beta_k растёт — модель противоположна асимптотической свободе.

---

## #522 - `src/gauge/Transfer3x3.v` - score 2 (methods)

**3x3 SU(2) transfer block: add j=2 (mult 5) Bessel eigenvalue; rational hierarchy lambda_2<lambda_1<lambda_0 at beta=1, M=0**

- **Topic.** Replicates the truncated-Bessel transfer-eigenvalue machinery (lambda_j = I_{2j} - I_{2j+2} as finite partial sums over Q) and extends the 2x2 picture to a 3x3 block by including the j=2 eigenvalue with multiplicity 5, computing Z_3, sector plaquettes, the 3x3 plaquette average and gap at concrete beta=1, M=0.
- **Role.** Self-contained extension of the character-transfer line; deliberately REPLICATES Qpow/fact_Q/bessel_term/bessel_partial/transfer_eigenvalue from SeriesConvergence+CharacterTransfer to dodge stale .vo (no ToS gauge imports). Standalone leaf — not imported elsewhere; demonstrates the j=2 correction is small but its 5x degeneracy keeps it non-negligible for Z and <P>.
- **Counts.** Qed 17 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lia ZArith Qabs Lqa (no ToS imports — Bessel infra replicated inline)
- **E/R/R.** _Elements:_ усечённые рациональные частичные суммы Бесселя bessel_partial; собственные значения lambda_j = transfer_eigenvalue j beta M; конкретные beta=1, M=0,1. _Roles:_ j = индекс спинового сектора (роль-ярус); кратность 2j+1 (1,3,5) = вес роли; lambda_j = вклад сектора в перенос; gap = lambda_0 - lambda_1. _Rules:_ Z_3 = lambda_0 + 3*lambda_1 + 5*lambda_2 (мультиплетности); P_j = I_{2j+1}/I_{2j} (плакета сектора); gap_3 = lambda_0 - lambda_1. _P4:_ Каждое lambda_j(beta,M) при ФИКСИРОВАННЫХ beta,M — конкретная Q-дробь (Element, vm_compute терминирует); число секторов J и точность M — обрезание конечно-актуального процесса. Истинный спектр требует M->inf (role-limit): файл живёт строго на Element-стороне (M=0,1), наблюдая сходящуюся иерархию, но не её предел.
- **Classical counterpart.** Mirrors the SU(2) heat-kernel / character expansion of the lattice plaquette action: eigenvalues are differences of modified Bessel functions I_{2j}(beta) (Migdal-Kogut-Susskind strong-coupling expansion), and partition function Z = sum_j (2j+1) lambda_j with degeneracy 2j+1. NEW here is only carrying the j=2 (multiplicity 5) term as a truncated rational Bessel partial sum and machine-checking the eigenvalue hierarchy lambda_2<lambda_1<lambda_0 at beta=1; the Bessel/character structure itself is classical.
- **Tags.** gauge, SU(2), bessel, character-expansion, transfer-matrix, mass-gap, eigenvalue-hierarchy, finite-lattice, replicated-infra
- **Notes.** Header 'STATUS: 17 Qed' matches actual 17 Qed (0 Admitted, 0 axioms). 31 named top-level declarations (17 proved lemmas/theorems + 14 Definition/Fixpoint without Qed). NOTE: this file defines its OWN transfer_eigenvalue (Bessel, j-indexed) distinct from gauge/TransferMatrix.v's transfer_eigenvalue_0/1 (the 2-beta/8 algebraic ones) — different formula, same conceptual slot. The exists-num#den lemmas (lambda2_b1_M0_value, sector_plaq_jN_exists, plaquette_3x3_exists) are by-type 'finiteness' witnesses, weak content; a June 2026 comment notes lambda2_b1_M0_value was de-vacuofied (positivity moved to lambda2_positive_b1).

**Lemmas (31):**

| name | kind | role |
|---|---|---|
| `Qpow` | Fixpoint | степень q^n над Q (реплика) |
| `fact_Q` | Definition | факториал как Q через inject_Z (реплика) |
| `fact_prod` | Definition | произведение факториалов fact_Q m * fact_Q n |
| `bessel_term` | Definition | общий член ряда Бесселя I_n: (beta/2)^(n+2m)/(m!(n+m)!) |
| `bessel_partial` | Fixpoint | частичная сумма I_n(beta) до уровня M (усечение) |
| `transfer_eigenvalue` | Definition | lambda_j = bessel_partial(2j) - bessel_partial(2j+2) |
| `lambda2` | Definition | lambda_2(beta,M) = transfer_eigenvalue 2 beta M = I_4 - I_6 |
| `lambda2_b1_M0_value` | Lemma | lambda_2(1,0) — определённая конечная Q-дробь (по типу num#den) |
| `lambda2_positive_b1` | Lemma | 0 < lambda_2(1,0) (vm_compute) |
| `t0_local` | Definition | lambda_0 при M=0 (реплика) |
| `t1_local` | Definition | lambda_1 при M=0 (реплика) |
| `t0_b1` | Lemma | t0_local 1 == 7/8 (конкретное значение) |
| `t1_b1` | Lemma | t1_local 1 == 47/384 (конкретное значение) |
| `lambda2_lt_t1` | Lemma | lambda_2(1,0) < t1_local 1 |
| `t1_lt_t0` | Lemma | t1_local 1 < t0_local 1 |
| `lambda_hierarchy_b1` | Theorem | ★ lambda_2 < lambda_1 < lambda_0 при beta=1, M=0 |
| `Z_3x3` | Definition | Z_3 = lambda_0 + 3*lambda_1 + 5*lambda_2 (мультиплетности 1,3,5) |
| `Z_2x2` | Definition | Z_2 = lambda_0 + 3*lambda_1 (старая 2x2 статсумма) |
| `Z_3x3_positive` | Lemma | 0 < Z_3(1,0) |
| `Z_3x3_gt_Z_2x2` | Theorem | Z_2(1,0) < Z_3(1,0) (больше членов = больше) |
| `sector_plaquette` | Definition | P_j = I_{2j+1}/I_{2j} (плакета в секторе j) |
| `sector_plaq_j0_b1` | Lemma | P_0(1,0) = (1/2)/1 = 1/2 |
| `sector_plaq_j1_exists` | Lemma | P_1(1,0) — определённая Q-дробь |
| `sector_plaq_j2_exists` | Lemma | P_2(1,0) — определённая Q-дробь |
| `plaquette_3x3` | Definition | <P>_3 = [lambda_0 P_0 + 3 lambda_1 P_1 + 5 lambda_2 P_2]/Z_3 |
| `plaquette_3x3_exists` | Lemma | <P>_3(1,0) — определённая Q-дробь |
| `gap_3x3` | Definition | gap_3 = lambda_0 - lambda_1 (та же формула, что 2x2) |
| `gap_3x3_b1_M0` | Lemma | gap_3(1,0) == 289/384 |
| `gap_3x3_positive` | Lemma | 0 < gap_3(1,0) (через значение 289/384) |
| `gap_3x3_M1_positive` | Lemma | 0 < gap_3(1,1) — выше M, точнее gap |
| `transfer_3x3_summary` | Theorem | сводка: иерархия + Z_3>Z_2 + gap=289/384>0 |

**Key lemmas (deep):**

- **`lambda_hierarchy_b1`** - Содержательное ядро файла: при beta=1, M=0 собственные значения трёх секторов строго упорядочены lambda_2 < lambda_1 < lambda_0 (7/8 > 47/384 > lambda_2). Это машинная проверка того, что высшие спиновые секторы дают всё меньший вклад — обоснование обрезания ряда характеров. Классически это убывание известно (Бессель I_n убывает по n при фиксированном малом аргументе); ново лишь рациональное усечённое доказательство через vm_compute и постановка как явной иерархии. _(bessel, eigenvalue-hierarchy, character-expansion, vm_compute)_
- **`gap_3x3_b1_M0`** - gap_3(1,0) = 289/384 — РОВНО та же щель, что в 2x2 (gap = lambda_0 - lambda_1, j=2 не входит в разность). Это тонкая, но честная точка: добавление j=2 меняет Z и <P>, но НЕ щель при M=0. Значение 289/384 ~ 0.7526 — тот же рациональный 'якорь', что повторяется по всему gauge-кластеру (ExactMassGap, TransferMatrixProof). Связывает 3x3-расширение обратно к 2x2-базе. _(mass-gap, 289/384, consistency, M0)_

**Uniqueness - score 2 (methods).** Рациональное (Q) усечённое-Бесселево вычисление SU(2)-переноса, расширенное на j=2 (кратность 5), с машинной иерархией собственных значений и наблюдением, что j=2 сдвигает Z и <P>, но не M=0-щель.
> _Caveat:_ Вся структура классична: характерное/heat-kernel разложение SU(2), собственные значения = разности Бесселей I_{2j}, мультиплетности 2j+1, статсумма Migdal-Kogut-Susskind. Ново только: рациональное усечение + j=2-член + конкретные значения при beta=1, M=0,1. НЕ доказывает массовую щель Янга-Миллса; конечное M (M=0,1), один beta, без континуумного предела. Bessel-инфра скопирована inline (не импорт).

---

## #523 - `src/gauge/TransferMatrix.v` - score 2 (methods)

**Concrete 2x2 U(1) transfer matrix over Q: eigenvalues 2-beta/8 and beta/8, mass gap = 2-beta/4 > 0 for 0<beta<8**

- **Topic.** Builds the explicit 2x2 symmetric transfer matrix T(beta) for a K=2 discretized 1+1D U(1) lattice gauge toy, proves its two eigenvalues (ground 2-beta/8 with eigenvector (1,1); excited beta/8 with (1,-1)), the mass gap Delta=2-beta/4, its positivity on 0<beta<8, monotonicity, trace/det, eigenvector orthogonality, and Rayleigh-quotient confirmations.
- **Role.** Foundational definitional hub of the 2x2 gauge sub-thread: exports mass_gap_2x2, transfer_2x2, transfer_eigenvalue_0/1, gap_vanishes_at_8, mass_gap_2x2_positive — directly reused by TopologicalObstruction (#521) and the strong-coupling/RG/gap-matching siblings. Imports the real linear-algebra stack (LinearAlgebra, linalg.MatrixOps/EigenvalueTheory/PowerMethod, physics.InnerProductSpace/Orthogonality) and the lattice/gauge base (LatticeStructure, GaugeField, WilsonAction).
- **Counts.** Qed 22 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs List Lia ZArith Lqa; ToS.LinearAlgebra; ToS.CauchyReal; physics.InnerProductSpace; physics.Orthogonality; physics.QObservable; physics.QState; linalg.MatrixOps; linalg.EigenvalueTheory; linalg.PowerMethod; gauge.LatticeStructure; gauge.GaugeField; gauge.WilsonAction
- **E/R/R.** _Elements:_ конкретная 2x2 Q-матрица transfer_2x2 beta; собственные векторы (1,1) и (1,-1); beta как параметр связи. _Roles:_ T = пропагатор между пространственными слоями; lambda_0 = основное состояние (роль-доминанта), lambda_1 = возбуждённое; gap = щель масс = роль-разность спектра. _Rules:_ T_{ij} = 1 - (beta/2)(theta_i-theta_j)^2; lambda_0 = 2-beta/8, lambda_1 = beta/8; Delta = lambda_0-lambda_1 = 2-beta/4; T симметрична, trace=2. _P4:_ При фиксированном beta всё конечно-актуально: T — явная 2x2-Q-матрица, спектр и щель — Q-дроби (Element, lra/vm_compute терминируют). НО это K=2-усечение (две конфигурации угла {0,1/2}) одного бесконечно-мерного оператора переноса непрерывной U(1)-теории; реальный спектр — role-limit при K->inf. Файл — Element-срез одной точки этого процесса.
- **Classical counterpart.** Mirrors the lattice transfer-matrix formalism (Osterwalder-Seiler / Creutz): the transfer matrix is a real symmetric positive operator whose two largest eigenvalues set the mass gap Delta = -log(lambda_1/lambda_0). Concretely it is a textbook 2x2 symmetric matrix with eigenvalues trace+/-sqrt computed by hand. NEW here is only the explicit Q-arithmetic instantiation for a K=2 discretized 1+1D U(1) toy (eigenvalues 2-beta/8 and beta/8) with full machine-checked eigenvector verification, det/trace, Rayleigh quotients; the linear algebra is elementary and classical.
- **Tags.** gauge, transfer-matrix, U(1), mass-gap, eigenvalue, rayleigh, 2x2, finite-lattice, definitional-hub, K=2
- **Notes.** Header 'STATUS: ~25 Qed' is DRIFT: actual count is 23 Qed (0 Admitted, 0 axioms). 29 named declarations (23 proved + 6 Definition). The end-marker theorem total_count : (25=25) also encodes the stale 25 and is itself a vestigial reflexivity lemma. IMPORTANT name overlap: this file's transfer_eigenvalue_0/transfer_eigenvalue_1 (algebraic 2-beta/8, beta/8) are DISTINCT from the Bessel transfer_eigenvalue j beta M used in Transfer3x3.v / TransferMatrixProof.v / TridiagonalGap.v — same gauge cluster, two different eigenvalue notions.

**Lemmas (29):**

| name | kind | role |
|---|---|---|
| `transfer_action_1d` | Definition | действие переноса (beta/2)(theta1-theta2)^2 |
| `transfer_element_1d` | Definition | элемент матрицы 1-го порядка: 1 - действие |
| `transfer_action_zero_same` | Lemma | действие = 0 при равных углах |
| `transfer_element_at_same` | Lemma | диагональный элемент = 1 |
| `transfer_2x2` | Definition | ★ 2x2 матрица переноса для 1+1D U(1), K=2: углы {0,1/2} |
| `transfer_eigenvalue_0` | Definition | lambda_0 = 2 - beta/8 (основное) |
| `transfer_eigenvalue_1` | Definition | lambda_1 = beta/8 (возбуждённое) |
| `mass_gap_2x2` | Definition | ★ щель масс = lambda_0 - lambda_1 |
| `transfer_2x2_symmetric` | Lemma | T симметрична |
| `transfer_2x2_trace` | Lemma | trace T = 2 |
| `transfer_2x2_det` | Lemma | det T = 1 - (1-beta/8)^2 |
| `transfer_2x2_eigenvalue_0` | Theorem | ★ lambda_0=2-beta/8 — собственное значение, вектор (1,1) |
| `transfer_2x2_eigenvalue_1` | Theorem | ★ lambda_1=beta/8 — собственное значение, вектор (1,-1) |
| `eigenvalue_0_positive` | Lemma | lambda_0 > 0 при beta < 16 |
| `eigenvalue_1_positive` | Lemma | lambda_1 > 0 при beta > 0 |
| `eigenvalue_0_dominates` | Theorem | lambda_1 < lambda_0 при 0<beta<8 (основное доминирует) |
| `mass_gap_2x2_formula` | Lemma | Delta == 2 - beta/4 |
| `mass_gap_2x2_positive` | Theorem | ★ ТЕОРЕМА ЩЕЛИ: Delta>0 при 0<beta<8 |
| `mass_gap_at_beta_1` | Lemma | Delta(1) == 7/4 (конкретно) |
| `gap_vanishes_at_8` | Lemma | ★ Delta(8) == 0 — щель закрывается (предел U(1)) |
| `eigenvalue_sum_trace` | Lemma | lambda_0 + lambda_1 == trace T |
| `eigenvectors_orthogonal` | Lemma | (1,1).(1,-1) == 0 (ортогональны) |
| `gap_monotone_beta` | Lemma | щель убывает с beta на (0,8) |
| `transfer_positive_entries` | Lemma | все 4 элемента T > 0 при 0<beta<8 |
| `rayleigh_ground_state` | Lemma | Rayleigh((1,1)) == 2-beta/8 (= lambda_0) |
| `rayleigh_excited_state` | Lemma | Rayleigh((1,-1)) == beta/8 (= lambda_1) |
| `transfer_matrix_summary` | Theorem | сводка: симметрия + 2 собств.знач. + gap>0 + ортогональность |
| `transfer_matrix_main` | Theorem | главная: симметрия + спектр + gap>0 |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`mass_gap_2x2_positive`** - Несущая теорема файла и всего 2x2-под-кластера: щель масс Delta(beta)=2-beta/4 строго положительна на 0<beta<8 (одна строка lra). Это РЕЭКСПОРТируется как 'захват' в TopologicalObstruction. Честно: это конечный (2x2, K=2) U(1)-игрушечный факт, а не SU(2)/SU(3)-непертурбативная щель Янга-Миллса; положительность тривиальна (линейная функция beta). Значимость — она якорь, на который ссылаются соседние файлы как на 'модель имеет щель'. _(mass-gap, positivity, U(1), K=2, load-bearing, not-millennium)_
- **`transfer_2x2_eigenvalue_0`** - Полная проверка собственной пары: (1,1) — собственный вектор T с собственным значением 2-beta/8, доказанная через определение is_eigenvalue (ненулевой вектор + T v = lambda v покомпонентно, destruct по индексам + lra). В паре с transfer_2x2_eigenvalue_1 (вектор (1,-1), beta/8) и eigenvectors_orthogonal это даёт честный спектральный разбор 2x2-блока, не полагаясь на абстрактную теорему о диагонализации — отсюда контраст с TransferMatrixProof.v, где T задана уже диагональной. gap_vanishes_at_8 фиксирует, что при beta=8 спектр вырождается (lambda_0=lambda_1=1) — щель закрывается, отмечая безмассовый U(1)-фотон. _(eigenvector, spectral, symmetric-2x2, verification)_

**Uniqueness - score 2 (methods).** Полностью явная Q-арифметическая 2x2 матрица переноса с машинно-проверенными собственными парами, det/trace, монотонностью щели и подтверждением через отношение Рэлея — без обращения к абстрактной диагонализации.
> _Caveat:_ Содержание классическое и элементарное: симметричная 2x2 матрица, собственные значения trace+/-, щель = разность, Delta=2-beta/4 линейна. Это K=2-усечённая 1+1D U(1)-ИГРУШКА, НЕ массовая щель Янга-Миллса (нет SU(N), нет непертурбативности, нет континуумного K->inf-предела). Положительность щели — одна строка lra.

---

## #524 - `src/gauge/TransferMatrixProof.v` - score 2 (methods)

**Transfer matrix as a concrete diagonal DiagMat over Q: diagonal entries = Bessel eigenvalues, spectral gap 289/384 (beta=1), 1/24 (beta=2)**

- **Topic.** Defines a self-contained diagonal-matrix record DiagMat (size + entry function), instantiates it as transfer_mat J beta M with diagonal = transfer_eigenvalue j beta M (Bessel), and proves the spectral facts: off-diagonal vanishes, every diagonal entry is an eigenvalue, ordering t_1<=t_0, and the matrix mass gap equals character_mass_gap / gap_M0 with explicit values 289/384 (beta=1) and 1/24 (beta=2).
- **Role.** The 'full proof terms, no True' diagonal-matrix companion to the character-transfer line. Imports CharacterTransfer, ExactMassGap, GapRatio and delegates all numeric positivity/value facts (t0_positive_beta_1, gap_at_beta_1, eigenvalue_ordering_0_1, ...) to them; the DiagMat layer just re-expresses them as 'matrix' statements. Defines matrix_mass_gap reused as a clean spectral wrapper. Standalone-ish leaf (ends with Print Assumptions); not a heavily-imported dependency.
- **Counts.** Qed 32 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs List Lia ZArith Lqa; ToS.CauchyReal; ToS.SeriesConvergence; gauge.CharacterTransfer; gauge.ExactMassGap; gauge.GapRatio
- **E/R/R.** _Elements:_ запись DiagMat {dm_size; dm_entry}; transfer_mat J beta M с диагональю = Бесселевы собств.значения; конкретные beta=1,2, M=0. _Roles:_ DiagMat = абстракция диагональной матрицы (объект-арена спектра); dm_entry j = j-е собственное значение (роль-сектор); matrix_mass_gap = роль-разность largest - second. _Rules:_ T_{ij} = delta_{ij} d_j; собств.значение = любая диагональ d_j; gap = dm_entry 0 - dm_entry 1 == character_mass_gap; при M=0 = gap_M0. _P4:_ Диагональная матрица КОНЕЧНОГО размера S J — конечно-актуальна (Element): спектр = её диагональ, gap = Q-разность, всё через reflexivity/ring/lra. J — параметр размера (произвольный nat), но gap от него НЕ зависит (входят только j=0,1) — устойчивость к арене. Бесселев предел M->inf остаётся role-limit; файл фиксирует M=0-срез.
- **Classical counterpart.** Mirrors the spectral theory of a diagonal (already-diagonalized) operator: for D=diag(d_0,d_1,...), every diagonal entry is an eigenvalue and the spectral gap is d_0 - d_1. Here the diagonal entries are the SU(2) Bessel transfer eigenvalues (Migdal-Kogut-Susskind character expansion). NEW is only the self-contained DiagMat record abstraction over Q and the J-independence packaging (gap is independent of matrix size J); the spectral facts are trivial for a diagonal matrix and the gap values (289/384 at beta=1, 1/24 at beta=2) are inherited from ExactMassGap/CharacterTransfer.
- **Tags.** gauge, transfer-matrix, diagonal-matrix, SU(2), bessel, mass-gap, 289/384, spectral, finite-lattice, wrapper, delegation
- **Notes.** Header 'STATUS: ~40 Qed' / 'target ~40 Qed' is DRIFT: actual count is 32 Qed (0 Admitted, 0 axioms). 37 named declarations (32 proved + 1 Record DiagMat + 4 Definition). Header tagline 'NO True. Every statement has a complete proof.' verified — no True placeholders. File ends with Check block + Print Assumptions transfer_matrix_proof_summary. transfer_eigenvalue here is the BESSEL (j-indexed) one from CharacterTransfer, NOT the algebraic transfer_eigenvalue_0/1 of TransferMatrix.v (#523).

**Lemmas (37):**

| name | kind | role |
|---|---|---|
| `DiagMat` | Record | ★ диагональная матрица: {dm_size: nat; dm_entry: nat->Q} |
| `dm_mat_entry` | Definition | T_{ij} = if i=j then dm_entry j else 0 |
| `dm_diagonal` | Lemma | T_{jj} == dm_entry j |
| `dm_offdiag` | Lemma | T_{ij} == 0 при i<>j |
| `dm_symmetric` | Lemma | T_{ij} == T_{ji} (диагональная симметрична) |
| `dm_is_eigenvalue` | Definition | lambda собственное = exists j<size, dm_entry j == lambda |
| `dm_entry_is_eigenvalue` | Lemma | каждая диагональ — собственное значение |
| `transfer_mat` | Definition | ★ T(J,beta,M) = diag(transfer_eigenvalue j beta M), размер S J |
| `transfer_mat_size` | Lemma | dm_size = S J |
| `transfer_mat_diagonal` | Theorem | dm_entry j == transfer_eigenvalue j beta M |
| `transfer_mat_entry` | Theorem | явная формула элемента (delta-диагональ) |
| `transfer_mat_offdiag` | Theorem | внедиагональ = 0 |
| `transfer_mat_pos_0_beta1` | Theorem | d_0(beta=1)>0 (делегат t0_positive_beta_1) |
| `transfer_mat_pos_1_beta1` | Theorem | d_1(beta=1)>0 (делегат t1_positive_beta_1) |
| `transfer_mat_nonneg_0` | Theorem | d_0>=0 при beta in [0,2] |
| `transfer_mat_nonneg_1` | Theorem | d_1>=0 при beta in [0,2] |
| `transfer_mat_ordered` | Theorem | d_1 <= d_0 при beta in [0,2] (упорядоченность) |
| `transfer_mat_eigenvalue` | Theorem | каждое t_j (j<S J) — собственное значение |
| `ground_is_eigenvalue` | Theorem | t_0 — собственное значение |
| `excited_is_eigenvalue` | Theorem | t_1 — собственное значение (при J>=1) |
| `eigenvalue_strict_ordering_1` | Theorem | d_1 < d_0 при beta=1 (строго) |
| `eigenvalue_strict_ordering_2` | Theorem | d_1 < d_0 при beta=2 (строго) |
| `spectral_gap_def` | Lemma | d_0 - d_1 == character_mass_gap beta M |
| `spectral_gap_M0` | Lemma | при M=0: d_0 - d_1 == gap_M0 beta |
| `matrix_mass_gap` | Definition | ★ matrix gap = dm_entry 0 - dm_entry 1 |
| `matrix_gap_eq_character` | Theorem | matrix_mass_gap == character_mass_gap |
| `matrix_gap_eq_gap_M0` | Theorem | при M=0: matrix gap == gap_M0 |
| `matrix_gap_nonneg` | Theorem | gap>=0 при beta in [0,2] |
| `matrix_gap_positive_1` | Theorem | gap>0 при beta=1 |
| `matrix_gap_positive_2` | Theorem | gap>0 при beta=2 |
| `matrix_gap_value_1` | Theorem | ★ gap(beta=1) == 289/384 (точное значение) |
| `matrix_gap_value_2` | Theorem | ★ gap(beta=2) == 1/24 (точное значение) |
| `transfer_matrix_has_gap` | Theorem | ★ exists gap >=0 на beta in [0,2] (ключевая) |
| `transfer_matrix_strict_gap_1` | Theorem | exists gap>0 при beta=1 |
| `transfer_matrix_strict_gap_2` | Theorem | exists gap>0 при beta=2 |
| `spectral_gap_from_bessel` | Theorem | end-to-end: Bessel -> собств.знач. -> gap>0, значения |
| `transfer_matrix_proof_summary` | Theorem | сводка: диагональность + спектр + упорядоченность + gap>0 |

**Key lemmas (deep):**

- **`transfer_matrix_has_gap`** - Заявленная 'KEY THEOREM': для любого размера J и beta in [0,2] существует gap = d_0 - d_1 >= 0. Честно: для УЖЕ диагональной матрицы это почти тавтология — 'спектральная щель' = разность двух выбранных диагональных входов, а её неотрицательность делегирована matrix_gap_nonneg -> gap_M0_nonneg из ExactMassGap. Содержательная физика (что эти диагонали суть Бесселевы собственные значения переноса и что gap>0) живёт в импортируемых файлах; здесь — чистая переупаковка в матричный язык. J-независимость (gap не зависит от размера) — единственное лёгкое добавление. _(spectral-gap, diagonal, delegation, J-independence, not-millennium)_
- **`matrix_gap_value_1`** - gap(beta=1) == 289/384 — точное рациональное значение щели, поднятое из gap_at_beta_1 (ExactMassGap) на уровень matrix_mass_gap. Тот же 289/384 ~ 0.7526, что в Transfer3x3 и по всему кластеру: это канонический рациональный 'якорь' M=0-щели SU(2)-характерного переноса. Спарено с matrix_gap_value_2 == 1/24 (beta=2). Значимость — демонстрация, что DiagMat-обёртка ВОСПРОИЗВОДИТ те же значения без потери (lra-перенос равенства), т.е. абстракция корректна. _(289/384, exact-value, beta=1, wrapper-fidelity)_

**Uniqueness - score 2 (methods).** Самодостаточная Q-абстракция диагональной матрицы (DiagMat) с полными термами доказательств (без True/Admitted), переэкспрессирующая Бесселев SU(2)-перенос как матричный спектр и доказывающая независимость щели от размера J.
> _Caveat:_ Спектральные факты ТРИВИАЛЬНЫ для диагональной матрицы (собств.знач. = диагональ; gap = разность входов). Вся числовая суть (положительность, значения 289/384, 1/24, упорядоченность) ДЕЛЕГИРОВАНА в ExactMassGap/CharacterTransfer через exact/lra. НЕ доказывает массовую щель Янга-Миллса: конечная диагональ, M=0, два beta, без континуумного предела и без off-diagonal динамики (та — в TridiagonalGap). Имя '...Proof' аспирационно.

---

## #525 - `src/gauge/TridiagonalGap.v` - score 2 (methods)

**Off-diagonal coupling does not kill the gap: Gershgorin + perturbation over Q; combined gap >= temporal gap in all three regimes**

- **Topic.** Goes beyond the diagonal approximation by bounding the off-diagonal spatial coupling of the SU(2) transfer Hamiltonian: defines rational Gershgorin radii and a perturbation bound, then argues the temporal mass gap survives in three regimes (small beta_s, large beta_s, all couplings), with explicit lower bounds 289/384 (beta=1) and 1/24 (beta=2) independent of the spatial coupling.
- **Role.** The 'beyond-diagonal' robustness companion in the SU(2) gauge line. Imports SU2Characters, CharacterTransfer, ExactMassGap, ClebschGordan, SpatialHamiltonian, CombinedTransfer3D and DELEGATES its load-bearing inequality to combined gap lemmas there (spatial_enhances_gap, combined_gap_positive_1/2, combined_gap_nonneg). Defines gershgorin_radius / perturbation_bound / gap_survives_condition as the local contribution; terminal leaf (ends with Print Assumptions), not re-imported.
- **Counts.** Qed 18 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS.CauchyReal; ToS.SeriesConvergence; stdlib.Combinatorics; gauge.SU2Characters; gauge.CharacterTransfer; gauge.ExactMassGap; gauge.ClebschGordan; gauge.SpatialHamiltonian; gauge.CombinedTransfer3D
- **E/R/R.** _Elements:_ радиусы Гершгорина gershgorin_radius d_sp j; граница возмущения perturbation_bound; combined_gap из соседнего файла; конкретные d_sp=3, beta_s, beta=1,2. _Roles:_ Gershgorin-диск = роль-локализатор спектра; perturbation_bound = роль-оценка внедиагонального вклада; режимы (малый/большой/любой beta_s) = роль-секторы параметра. _Rules:_ radius(j=0)=d_sp*offdiag(0), radius(j>=1)=d_sp*(offdiag(j-1)+offdiag(j)); perturbation = beta_s*radius(1); gap выживает <=> combined_gap > 2*perturbation; combined_gap >= gap_M0 (всегда). _P4:_ Все объекты конечно-актуальны над Q при фиксированных d_sp, beta, beta_s: радиусы и границы — Q-дроби (Element). НО 'выживание щели во ВСЕХ режимах' опирается на combined_gap >= temporal gap, ДОКАЗАННОЕ в CombinedTransfer3D — здесь это посылка. Сам полный пространственный гамильтониан бесконечномерен; Gershgorin/perturbation — конечные оценки одного среза, не континуумное утверждение.
- **Classical counterpart.** Mirrors Gershgorin's circle theorem (eigenvalue localization via row sums) and first-order matrix perturbation theory (Bauer-Fike-style gap stability under an off-diagonal perturbation V). NEW here is only the application to the SU(2) spatial transfer Hamiltonian over Q with concrete rational Gershgorin radii (1, 7/5 at d_sp=3) and the claim that the temporal gap survives off-diagonal spatial coupling in three regimes; the localization/perturbation machinery is classical and the key stability theorem is delegated to a sibling (spatial_enhances_gap).
- **Tags.** gauge, SU(2), gershgorin, perturbation, mass-gap, tridiagonal, off-diagonal, 289/384, robustness, finite-lattice, delegation
- **Notes.** Header 'STATUS: ~35 Qed' is DRIFT (largest gap among the 5): actual count is 18 Qed (0 Admitted, 0 axioms). 24 named declarations (18 proved + 6 Definition). The internal section headers ('~10 lemmas', '~10 lemmas', '~10 lemmas', '~5 lemmas') also over-count vs reality. File ends with Check block + Print Assumptions tridiagonal_gap_summary. Honest tension worth flagging: the Gershgorin apparatus (perturbation_bound 7/5, 2x=14/5) is too coarse to beat the 289/384 temporal gap, so the actual gap-survival result rides on delegated monotonicity (spatial_enhances_gap), not on this file's own perturbation bound.

**Lemmas (24):**

| name | kind | role |
|---|---|---|
| `gershgorin_radius` | Definition | ★ радиус диска Гершгорина для тридиагональной строки j |
| `gershgorin_radius_0` | Lemma | radius(j=0) = d_sp*offdiag(0) |
| `gershgorin_radius_1` | Lemma | radius(j=1) = d_sp*(offdiag(0)+offdiag(1)) |
| `gershgorin_radius_3d_0` | Lemma | radius(3,0) == 1 (конкретно) |
| `gershgorin_radius_3d_1` | Lemma | radius(3,1) == 7/5 (конкретно) |
| `gershgorin_radius_nonneg` | Lemma | radius >= 0 |
| `perturbation_bound` | Definition | граница возмущения = beta_s*radius(d_sp,1) |
| `perturbation_bound_nonneg` | Lemma | perturbation >= 0 при beta_s>=0 |
| `perturbation_3d` | Lemma | perturbation(beta_s=1,d_sp=3) == 7/5 |
| `perturbed_gap` | Definition | возмущённая щель = combined_gap - 2*perturbation |
| `gap_survives_condition` | Definition | ★ условие выживания: combined_gap > 2*perturbation |
| `gap_at_zero_coupling` | Theorem | combined_gap(beta_s=0) == gap_M0 beta (предел нуль-связи) |
| `perturbation_at_zero` | Theorem | perturbation(beta_s=0) == 0 |
| `gap_survives_zero_coupling` | Theorem | при beta_s=0 щель выживает (если gap_M0 1>0) |
| `small_coupling_regime` | Definition | режим малой связи: 0<=beta_s<=1/10 |
| `gap_in_small_regime` | Theorem | combined_gap >= 0 в малом режиме |
| `gap_positive_small_regime_1` | Theorem | combined_gap(beta=1)>0 в малом режиме (делегат) |
| `large_coupling_regime` | Definition | режим большой связи: beta_s>=10 |
| `gap_bounded_below` | Theorem | ★ gap_M0 beta <= combined_gap (делегат spatial_enhances_gap) |
| `gap_positive_all_regimes` | Theorem | ★ combined_gap(beta=1)>0 при любом beta_s>=0 (делегат) |
| `gap_positive_all_regimes_2` | Theorem | combined_gap(beta=2)>0 при любом beta_s>=0 (делегат) |
| `gap_lower_bound_beta_1` | Theorem | ★ 289/384 <= combined_gap(beta=1) при любом beta_s |
| `gap_lower_bound_beta_2` | Theorem | 1/24 <= combined_gap(beta=2) при любом beta_s |
| `tridiagonal_gap_summary` | Theorem | сводка: выживание + положительность во всех режимах + нижние границы |

**Key lemmas (deep):**

- **`gap_bounded_below`** - Несущая ось файла, но она ДЕЛЕГИРОВАНА: 'gap_M0 beta <= combined_gap beta beta_s d_sp' доказывается одной строкой 'exact spatial_enhances_gap' — т.е. ключевое утверждение, что пространственная связь только УВЕЛИЧИВАЕТ щель (не убивает её), живёт в CombinedTransfer3D, а не здесь. Это превращает все 'gap survives'-теоремы (во всех трёх режимах) в следствия одного импортированного монотонного факта. Честно: Gershgorin/perturbation-аппарат файла НЕ используется в этом главном выводе — он параллельная, более слабая (двусторонняя) оценка. _(delegation, gap-survival, monotonicity, perturbation, load-bearing-elsewhere)_
- **`gershgorin_radius_3d_1`** - Конкретный рациональный радиус Гершгорина radius(d_sp=3, j=1) == 7/5 (и radius(3,0)==1) — единственное по-настоящему ЛОКАЛЬНОЕ содержание файла: явная Q-локализация спектра тридиагонального пространственного гамильтониана в 3D. Это иллюстрирует метод (внедиагональная связь ограничена 7/5 при d_sp=3, beta_s=1), но НЕ замыкает аргумент выживания щели — для этого 2*perturbation=14/5 заведомо больше temporal gap 289/384, так что наивная Gershgorin-оценка СЛИШКОМ груба, и реальный вывод идёт через делегированную монотонность. Поучительный честный разрыв между предъявленным методом и работающим доказательством. _(gershgorin, rational-radius, 3D, method-vs-proof-gap)_

**Uniqueness - score 2 (methods).** Рациональная (Q) Gershgorin-локализация + возмущённая оценка тридиагонального пространственного SU(2)-гамильтониана с явными радиусами (1, 7/5) и трёхрежимным утверждением о выживании временной щели под внедиагональной связью.
> _Caveat:_ Gershgorin и теория возмущений классичны; главный вывод (combined_gap >= temporal gap во ВСЕХ режимах) ДЕЛЕГИРОВАН в spatial_enhances_gap/combined_gap_* (CombinedTransfer3D), а предъявленная Gershgorin-оценка слишком груба, чтобы его дать (2*perturbation=14/5 >> 289/384). НЕ доказывает массовую щель Янга-Миллса: конечный M=0-срез, два beta, без континуумного предела; 'три режима' опираются на импортированную монотонность.

---

## #526 - `src/gauge/UniversalityClass.v` - score 1 (exposition)

**Universality class as monotone artifact-vanishing; SO(4)/continuum names ride one Q-inequality**

- **Topic.** Defines in_same_class (both artifacts positive and strictly decreasing in β) and at_fixed_point (artifact<1/1000), then 'proves' fixed-point uniqueness, conformality, isotropy/SO(4) restoration and continuum existence — most of which restate the same small fact lattice_artifact_size 42 < 1/1000.
- **Role.** Top of the gauge continuum-limit narrative. Imports CharacterTransfer, ExactMassGap, GapRatio, LatticeRG, IrrelevantOperators, RGContraction; reuses artifact_positive/artifact_decreasing, gap_ratio_at_beta_1, gap_M0 positivity. A capstone-style summary file, not depended on by core machinery.
- **Counts.** Qed 17 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: CauchyReal SeriesConvergence; gauge: CharacterTransfer ExactMassGap GapRatio LatticeRG IrrelevantOperators RGContraction
- **E/R/R.** _Elements:_ конкретные артефакты-функции artifact: Q->Q (например lattice_artifact_size β = 1/(24β)); пороги 1/1000, 1/2000; коэффициент анизотропии anisotropy β = 1/β. _Roles:_ in_same_class — отношение эквивалентности (рефлексивно+симметрично доказано) между действиями; at_fixed_point — роль-предикат «артефакт пренебрежимо мал»; неподвижная точка = роль-предел RG-потока. _Rules:_ класс ⟺ оба артефакта 0<· и строго убывают по β; на неподвижной точке артефакт < порога; масс-щель RG-инвариантна (цитируется как gap_ratio_at_beta_1). _P4:_ P4-грань: «континуумная неподвижная точка» = роль-ПРЕДЕЛ β→∞ убывающего рационального процесса 1/(24β); ни одна точка его не достигает (artifact>0 всюду), значит SO(4)/конформность — роль на пределе, а Element-сторона = конкретные конечные β=42,100 с проверенным неравенством.
- **Classical counterpart.** Wilson's RG universality (irrelevant operators vanish at the IR fixed point, restoring continuum Euclidean SO(4)/rotational symmetry) and RG-invariance of the mass gap. NEW here: NOTHING of the classical content is proved — universality is DEFINED as monotone vanishing of an artifact β↦1/(24β), and the named fixed-point/SO(4)/continuum theorems all discharge to a single rational inequality artifact(42)<1/1000.
- **Tags.** gauge, RG, universality, continuum-limit, SO4, overclaim, Q-arithmetic, P4, exposition
- **Notes.** STATUS header says ~30 Qed; actual Qed count = 17 (header used '~' estimate). No own axioms/Admitted. Multiple theorems are comment-only restatements of artifact_small_at_42 / wilson_in_class — flagged as over-branding (SO(4), OS axioms, continuum existence claimed but not formalized).

**Lemmas (19):**

| name | kind | role |
|---|---|---|
| `in_same_class` | Definition | два действия в одном классе ⟺ оба артефакта положительны и строго убывают по β |
| `wilson_in_class` | Theorem | вильсоновский артефакт в классе с самим собой (из artifact_positive/artifact_decreasing) |
| `improved_same_class` | Theorem | любое улучшенное действие с положит.+убывающим артефактом в том же классе, что Вильсон |
| `universality_reflexive` | Theorem | класс рефлексивен (артефакт в классе сам с собой) |
| `universality_symmetric` | Theorem | класс симметричен (a1~a2 ⟹ a2~a1) — единственное реальное структурное свойство |
| `at_fixed_point` | Definition | предикат: artifact β < 1/1000 (порог «неподвижной точки») |
| `rg_reaches_fixed_point` | Theorem | СЛАБО: фактически лишь 0 < lattice_artifact_size β0 (комментарий обещает больше, чем доказано) |
| `artifact_small_at_42` | Lemma | ★ нагрузочный факт: lattice_artifact_size 42 < 1/1000 (vm/lia на Q) |
| `artifact_small_at_100` | Lemma | lattice_artifact_size 100 < 1/2000 (второй конкретный β) |
| `fixed_point_unique` | Theorem | ИМЯ-ОБЁРТКА: «единственность неподвижной точки» = exact wilson_in_class (комментарий, не доказательство) |
| `fixed_point_conformal` | Theorem | ИМЯ-ОБЁРТКА: «конформность/масштаб-инвариантность» = artifact_small_at_42 |
| `fixed_point_isotropic` | Theorem | ИМЯ-ОБЁРТКА: «изотропия/SO(4)» = снова artifact_small_at_42 |
| `anisotropy_negligible` | Theorem | реальное: β≥42 ⟹ anisotropy β < 1/40 (честная оценка 1/β через Qlt_shift_inv_r) |
| `fixed_point_mass_gap` | Theorem | масс-щель на неподвижной точке = gap_ratio 1 == 47/336 (цитата gap_ratio_at_beta_1) |
| `fixed_point_gap_positive` | Theorem | 0 < gap_M0 1 /\ 0 < gap_M0 2 (положительность щели на β=1,2) |
| `continuum_theory_exists` | Theorem | ИМЯ-ОБЁРТКА: «континуумная теория + все OS-аксиомы» = щель>0 ∧ анизотропия→0 (OS лишь в комментарии) |
| `continuum_unique` | Theorem | ИМЯ-ОБЁРТКА: «единственность континуума» = universality_symmetric |
| `continuum_limit_well_defined` | Theorem | ИМЯ-ОБЁРТКА: = artifact_small_at_100 |
| `universality_summary` | Theorem | конъюнкция: класс ∧ artifact(42)<1/1000 ∧ щель>0 ∧ artifact(100)<1/2000 |

**Key lemmas (deep):**

- **`anisotropy_negligible`** - Единственная нетривиальная Q-выкладка файла: для β≥42 показано anisotropy β = 1/β < 1/40 честной цепочкой Qlt_shift_inv_r + монотонность умножения на (1#40). Это и есть реальный (хоть и элементарный) Element-факт «анизотропия мала на крупном конечном β», который переиспользуют continuum_theory_exists. Классически — тривиальное затухание 1/β; ценность лишь в аккуратной рациональной форме без R. _(anisotropy, Q-inequality, load-bearing, continuum-limit)_
- **`continuum_theory_exists`** - Витрина оверклейма кластера: комментарий заявляет существование континуумной SU(2) Янг-Миллса со ПОЛНОЙ SO(4) и ВСЕМИ аксиомами Остервальдера-Шрадера; доказанное тело — лишь (0<gap_M0 1 ∧ 0<gap_M0 2 ∧ ∀β≥42, anisotropy<1/40). OS-аксиомы и SO(4) НЕ формализованы здесь, существование неподвижной точки НЕ построено (артефакт всюду >0, предел не достигается). Это P4-роль-предел, поданный как завершённый объект. _(overclaim, SO4, OS-axioms, continuum, role-limit)_
- **`fixed_point_isotropic`** - Образец «имя >> содержание»: три разных теоремы (fixed_point_unique/_conformal/_isotropic) с громкими RG-именами разрешаются ОДНИМ и тем же exact artifact_small_at_42 либо exact wilson_in_class. Информативно как диагностика, что файл — нарратив поверх двух атомарных фактов, а не независимые результаты. _(naming-vs-content, Q-inequality, exposition)_

**Uniqueness - score 1 (exposition).** Аккуратная рациональная (без R) формулировка идеи RG-универсальности как монотонного затухания артефакта 1/(24β), с честной оценкой анизотропии 1/β<1/40 на конечном β и переиспользованием ранее доказанной положительности масс-щели.
> _Caveat:_ ОВЕРБРЕНДИНГ. Классическая универсальность Вильсона, SO(4)-восстановление, существование континуумной теории и аксиомы Остервальдера-Шрадера НЕ доказаны — это комментарии. Реальное содержание = две Q-оценки (artifact 42<1/1000, 100<1/2000) + затухание анизотропии; ~6 «теорем» — переименованные обёртки одного факта. Не континуум, конкретные β только; SU(2) фундаментальное представление.

---

## #527 - `src/gauge/WallBreachSynthesis.v` - score 2 (methods)

**K=2 gap→0 vs K=3 gap=5/18>0: three finite attacks; aspirationally a 'breach', honestly conditional**

- **Topic.** Synthesizes three imported attacks on the 'wall' (K=2 SU(2) gap vanishing at β=8): spectral bound (σ>0 yet gap=0), a 3×3 truncation giving gap 5/18, and a string-tension correction ≥3/32, concluding the wall is a 'K=2 artifact' — but only conditionally on an unproved uniform-in-K gap bound.
- **Role.** Synthesis/capstone of the wall-breach sub-programme. Imports TransferMatrix, SU2TransferMatrix, StrongCoupling, GapDecayRate, ConfinementCorrection, WallTheorem, SpectralBound, KDependence, InstantonEnhanced; pure consolidation of their lemmas, not reused downstream.
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: CauchyReal; gauge: TransferMatrix SU2TransferMatrix StrongCoupling GapDecayRate ConfinementCorrection WallTheorem SpectralBound KDependence InstantonEnhanced
- **E/R/R.** _Elements:_ конкретные конечные трансфер-матрицы 2×2 и 3×3; собственный вектор v101=(1,0,−1); рациональные числа щели 5/18, 3/32, σ(8); конкретный β=8. _Roles:_ K (размер усечения трансфер-матрицы) = роль-параметр финитизации; mass_gap_2x2 / su2_gap_at_k / corrected_gap — роли-наблюдаемые щели; «стена» = роль-предел орбиты β_k→8. _Rules:_ K=2: щель==0 на β=8 и →0 вдоль орбиты (доказано); K=3: собств.значение 16/9 на v101, щель≥5/18; коррекция натяжением: corrected_gap = su2_gap + tension_correction ≥ 3/32. _P4:_ P4-ядро файла: «масс-щель существует» переформулировано как «процесс щели положителен на КАЖДОЙ конечной ступени» (corrected_gap>0 ∀k) — это Element-сторона; роль-предел k→∞ (континуум) НЕ доказан положительным, отсюда честное «сведение к равномерной K-границе» вместо решения.
- **Classical counterpart.** The Clay Yang-Mills mass-gap problem (existence of SU(N) YM with a positive mass gap in the continuum) and the strong-coupling / confinement string-tension picture. NEW here: NOTHING of the Millennium problem is proved — the 'breach' that 'K=3 gap > 0' is the rational arithmetic fact 0 < 16/9 − 3/2 = 5/18 plus ONE imported 3×3 eigenvector check, and the result is explicitly CONDITIONAL ('reduces to a uniform K-bound').
- **Tags.** gauge, mass-gap, yang-mills, wall-breach, millennium, overclaim, conditional, finite-truncation, P4, synthesis
- **Notes.** STATUS header says ~15 Qed; actual Qed count = 14. No own axioms/Admitted. total_count is a final-fact marker (mass_gap_2x2 8==0), not an integer count. Over-branding flagged: 'wall_breach_complete'/'millennium_reduction' do NOT prove the Clay problem; explicitly conditional on an unproved uniform-K gap bound; the 'K=3 gap>0' core is the rational fact 0<5/18 plus one imported eigenvector.

**Lemmas (14):**

| name | kind | role |
|---|---|---|
| `wall_recap` | Theorem | рекап стены: K=2 щель==0 на β=8 ∧ →0 вдоль орбиты ∧ нет RG-совместимой коррекции |
| `attack1_result` | Theorem | атака 1: 0<string_tension 8 ∧ spectral_gap_lower 8==0 (σ>0 при нулевой 2×2-щели) |
| `attack2_result` | Theorem | ★ атака 2: v101 — собств.вектор с λ=16/9, char_poly(3/2)>0, и 0<5/18 |
| `attack3_result` | Theorem | атака 3: натяжение даёт достаточную коррекцию ≥3/32 на β∈(0,8) |
| `all_attacks_agree` | Theorem | конъюнкция трёх атак (стена — артефакт K=2) |
| `wall_breach_complete` | Theorem | ★ ВИТРИНА: стена (W1,W2) + брешь (B1 σ>0, B2 0<5/18, B3 corrected_gap>0) + оценка 0<16/9−3/2 |
| `mass_gap_with_k3` | Theorem | K=3-условная щель: mass_gap_2x2 8==0 ∧ 0<16/9−3/2 (ядро бреши = lra на рац.) |
| `mass_gap_with_tension` | Theorem | натяжная условная щель: 3/32 < corrected_gap ∀β∈(0,8),k |
| `millennium_reduction` | Theorem | ИМЯ-ОБЁРТКА: «Millennium-сведение» = mass_gap_2x2 8==0 ∧ 0<5#18 |
| `process_view` | Theorem | P4-вид: corrected_gap β k>0 ∀β∈(0,8),k (= tension_provides_gap) |
| `our_achievements` | Theorem | реестр 8 достижений: щель>0 K=2, K=2 на 8 ==0, σ(8)>0, 0<5/18 |
| `what_remains` | Theorem | что осталось: K=2 ==0 ∧ 0<5/18 ∧ σ(8)>0 (честная остаточная формулировка) |
| `breach_main` | Theorem | ★ главная брешь: ==0 ∧ 0<5/18 ∧ σ(8)>0 ∧ corrected_gap>0 ∀k |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`attack2_result`** - Единственный кусок с реальным линейно-алгебраическим содержанием: импортирует eigenvec_101_eigenvalue (на 3×3 усечении t3 вектор (1,0,−1) даёт λ=16/9 при β=8) и char_poly_at_3_2_positive, после чего ключевой вывод «щель≥5/18» = чистое lra над 0<5#18. То есть «брешь K=3» опирается на ОДИН конкретный собств.вектор конечной матрицы + рациональное вычитание 16/9−3/2=5/18. Никакого равномерного по K или континуумного утверждения. _(eigenvector, K=3, finite-truncation, Q-arithmetic, load-bearing)_
- **`wall_breach_complete`** - Флагман оверклейма: имя и звёзды обещают завершённый «пролом стены» масс-щели. Тело = (W1 K=2 щель==0) ∧ (W2 →0) ∧ (B1 σ(8)>0) ∧ (B2 0<5#18 — арифметика!) ∧ (B3 corrected_gap>0 ∀k) ∧ (0<16/9−3/2 — снова арифметика). Два из шести конъюнктов — буквально рациональные неравенства, доказанные lra. Честно: это НЕ доказательство Clay-проблемы, а демонстрация, что конкретное 2×2-усечение недостаточно, а 3×3 на одной точке β=8 даёт положительную щель. _(overclaim, millennium, conditional, synthesis, lra)_
- **`mass_gap_with_tension`** - Самый сильный (но всё ещё условный) результат: 3/32 < corrected_gap β k для ВСЕХ k и β∈(0,8), собранный из su2_gap_positive_all_k + tension_correction_lower через lra. Это и есть честная P4-формулировка «щель положительна на каждой конечной ступени с натяжной коррекцией» — но предел k→∞ (= континуум, = настоящая Clay-щель) не покрыт; зависит от импортированных оценок натяжения как от данности. _(process, P4, tension-correction, conditional, every-stage)_

**Uniqueness - score 2 (methods).** Связное рациональное (без R) сведение «исчезающей масс-щели K=2 SU(2)» к артефакту усечения: три независимые конечные атаки (спектральная граница, 3×3-собств.вектор с щелью 5/18, натяжная коррекция ≥3/32) согласованно показывают недостаточность K=2 и положительность щели на каждой конечной ступени при K≥3.
> _Caveat:_ СИЛЬНЫЙ ОВЕРБРЕНДИНГ в именах (wall_breach_complete, millennium_reduction). НЕ доказывает Clay Millennium / континуумную масс-щель. Ядро «бреши» = арифметика 16/9−3/2=5/18 (lra) + ОДИН собств.вектор v101 фиксированной 3×3-матрицы при единственном β=8. Явно условно: «сводится к равномерной по K оценке gap(K,8)», которая НЕ доказана. Только SU(2), квадратичное усечение, конечные K.

---

## #528 - `src/gauge/WallTheorem.v` - score 3 (new-framing)

**The Wall Theorem: K=2 SU(2) gap provably vanishes in the limit; P4 keeps it positive at every finite stage**

- **Topic.** Bundles the obstruction (RG orbit β_k→8 monotone, gap→0 along it, no RG-compatible correction, σ>0 yet gap=0 = string-tension paradox, topological triviality) into one 'Wall Theorem', then gives the P4 resolution: the gap process is positive at every finite k and the RG orbit is Cauchy.
- **Role.** Obstruction+resolution capstone of the gauge mass-gap programme. Imports TransferMatrix, SU2TransferMatrix, StrongCoupling, GapMatching, ExactRGProcess, NonperturbativeGap, GapDecayRate, ConfinementCorrection, TopologicalObstruction; consolidates them, sibling of WallBreachSynthesis.
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: CauchyReal; gauge: TransferMatrix SU2TransferMatrix StrongCoupling GapMatching ExactRGProcess NonperturbativeGap GapDecayRate ConfinementCorrection TopologicalObstruction
- **E/R/R.** _Elements:_ точная RG-орбита β_k = 8 − (8−β)/2^k (рациональная последовательность); конкретный β=8; су2-щель su2_mass_gap β; натяжение string_tension β; выход exact_rg K k β как Z#positive. _Roles:_ «стена» = роль-предел орбиты β→8, где щель обращается в 0; K = роль-параметр усечения; P4-щель = роль «процесс щели положителен на каждой ступени»; Коши-свойство орбиты = роль сходимости процесса. _Rules:_ β_k монотонно растёт к 8 (beta_k_increasing); su2_mass_gap 8 == 0; ∀ε∃k щель<ε (затухание); нет δ с rg_compatible∧preserves_gap; σ>0 всюду при щели 0 на 8 (парадокс); exact_rg-орбита Коши. _P4:_ ЦЕНТРАЛЬНАЯ P4-грань всего кластера: стандартная щель = lim_{k→∞} su2_gap(k) — ОТКРЫТА/равна 0 в этой модели; P4-щель = su2_gap(k)>0 ∀k — ДОКАЗАНА. Различие явно: P4 заменяет «завершённый бесконечный предел» на «процесс». Честно отделено от настоящего Янг-Миллса (wall_not_yang_mills).
- **Classical counterpart.** The Clay Yang-Mills mass-gap problem and the continuum limit of lattice gauge theory. NEW/HONEST here: the file proves the OPPOSITE of a solution for its own model — the K=2 SU(2) gap PROVABLY vanishes in the β→8 (continuum) limit — and reframes 'mass gap exists' via P4 as 'gap process positive at every finite stage', explicitly stating (wall_not_yang_mills) that this is NOT a claim about real Yang-Mills.
- **Tags.** gauge, mass-gap, yang-mills, wall, P4, process-vs-limit, honesty, RG-orbit, string-tension, new-framing
- **Notes.** STATUS header says ~18 Qed; actual Qed count = 12 (and total_count proves 18=18, an aspirational marker that no longer matches the real count). No own axioms/Admitted. Contrast with WallBreachSynthesis: this file is honestly framed (wall_not_yang_mills explicitly disclaims a Yang-Mills result).

**Lemmas (12):**

| name | kind | role |
|---|---|---|
| `the_wall` | Theorem | ★ Стена (6 конъюнктов): β_k монотонна, щель(8)==0, →0 вдоль орбиты, нет совместимой коррекции, σ>0∧щель(8)==0, σ>0 всюду |
| `beyond_the_wall` | Theorem | четыре пути за стену: нелокальность(σ>0), больший K, модиф.RG (щель(k)>0 ∀k), P4 (орбита Коши) |
| `p4_mass_gap` | Theorem | P4-щель: su2_gap_at_k β k>0 ∀β∈(0,8),k (= su2_gap_positive_all_k) |
| `p4_interpretation` | Theorem | P4-интерпретация: щель(k)>0 ∀k ∧ орбита Коши |
| `p4_vs_standard` | Theorem | ★ контраст: стандартная щель=lim открыта (→0), P4-щель(k)>0 доказана |
| `wall_location` | Theorem | локализация стены: su2_mass_gap 8==0 ∧ σ(8)>0 (где локальность+топ.тривиальность кончаются) |
| `wall_not_yang_mills` | Theorem | ★ ЧЕСТНОСТЬ: это НЕ «у ЯМ нет щели» — лишь щель модели затухает (∀ε∃k щель<ε) |
| `our_contribution` | Theorem | вклад ToS: орбита Коши ∧ щель(k)>0 ∀k ∧ нет коррекции ∧ σ>0 всюду |
| `rg_well_defined` | Theorem | RG корректна: exact_rg K k β представимо как num#den (рациональность выхода) |
| `gap_at_every_stage` | Theorem | щель на выходе каждой RG-ступени: 0 < su2_mass_gap (exact_rg K k β) |
| `wall_main` | Theorem | ★ ГЛАВНАЯ: стена (затухание+нет коррекции+парадокс) + за стеной (P4-щель>0 ∀k + орбита Коши) |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`wall_not_yang_mills`** - Самая ценная (метакогнитивная) строка кластера: явная теорема-дисклеймер. Тело = su2_gap_vanishes (∀β∈(0,8)∀ε>0 ∃k su2_gap_at_k β k<ε), а комментарий честно фиксирует: мы НЕ доказываем отсутствие щели у настоящего Янг-Миллса, лишь затухание щели КОНКРЕТНОЙ K=2-модели; у реального ЯМ есть доп.структура (инстантоны, асимптотическая свобода). Образец анти-оверклейма — резко контрастирует с витринными именами в WallBreachSynthesis. _(honesty, anti-overclaim, limit-vanishing, model-vs-reality)_
- **`p4_vs_standard`** - Концептуальное ядро файла и одна из чистейших иллюстраций P4 в репо: стандартный вопрос «gap = lim_{k→∞} su2_gap(k) > 0?» для этой модели имеет ответ НЕТ (→0), тогда как P4-вопрос «su2_gap(k)>0 ∀k?» — доказуемо ДА. Файл делает явным, что вся «масс-щель в P4» держится на замене завершённого бесконечного предела процессом. Это переформулировка-наблюдение, не новая теорема: оба факта (затухание и поступенчатая положительность) импортированы. _(P4, process-vs-limit, reframing, central)_
- **`the_wall`** - Шестиконъюнктный сбор обструкции: монотонность β_k→8, обнуление щели на 8, затухание вдоль орбиты, невозможность RG-совместимой коррекции (no_compatible_gap), парадокс натяжения σ>0∧щель=0, топологическая тривиальность. Все шесть — exact-цитаты импортов; ценность файла = их СБОРКА в один объект «стена» + противопоставление P4-разрешению. Чистая консолидация без нового вычисления. _(obstruction, synthesis, string-tension-paradox, RG-orbit)_

**Uniqueness - score 3 (new-framing).** Честная связка обструкции и разрешения: для K=2 SU(2)-модели масс-щель ДОКАЗУЕМО затухает в континуумном пределе β→8 (стена), но P4-переформулировка «щель как процесс» положительна на каждой конечной ступени и RG-орбита Коши — с явной теоремой-дисклеймером, что это не утверждение о настоящем Янг-Миллсе.
> _Caveat:_ Не решает Clay-проблему и честно это заявляет (wall_not_yang_mills). Все 6 фактов «стены» и P4-факты импортированы — файл лишь консолидирует. total_count : 18=18 — вакуумный маркер, не результат. P4-разрешение = философская переформулировка (предел→процесс), а не доказательство континуумной щели. Только SU(2), K=2, квадратичное действие.

---

## #529 - `src/gauge/WightmanReconstruction.v` - score 2 (methods)

**Explicit OS→Wightman reconstruction on a diagonal transfer matrix; W2/W4 reduced to Q-commutativity**

- **Topic.** Builds an explicit Wightman QFT from the diagonal lattice transfer matrix: energy levels E_j=1−t_j/t_0, vacuum j=0, fields = character operators with Clebsch-Gordan selection rule, two-point function W(t)=(gap_ratio)^t, and restates W1-W5 as real (non-vacuous) propositions.
- **Role.** QFT-language capstone of the gauge correlation chain. Imports CharacterTransfer, ExactMassGap, GapRatio, ReflectionPositivity, LatticeCorrelations, ClebschGordan, CorrelationProof; reuses physical_energy, gap_M0, full_correlation, coupling_allowed. Ends with Print Assumptions wightman_summary.
- **Counts.** Qed 23 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: CauchyReal SeriesConvergence; gauge: CharacterTransfer ExactMassGap GapRatio ReflectionPositivity LatticeCorrelations ClebschGordan CorrelationProof
- **E/R/R.** _Elements:_ уровни энергии E_j=1−t_j/t_0 (физ.значения как Z#positive); собств.значения transfer_eigenvalue; вакуум j=0; двухточечная W(t)=Qpow(gap_ratio β, t); правило отбора coupling_allowed. _Roles:_ гильбертово пространство H=span{\|j⟩} — роль-арена (счётный базис, индекс nat); гамильтониан H\|j⟩=E_j\|j⟩ диагонален; вакуум Ω=\|0⟩ — выделенная роль; поле Φ=χ_1 = роль-оператор; W1–W5 = роли-аксиомы. _Rules:_ E_0=0, E_1>0 (щель); 0≤E_j≤E_0 ⟹ E_j≥0; селекция ⟨j'\|Φ\|j⟩≠0 лишь \|j'−j\|≤1 (Clebsch-Gordan 1⊗j); W(t)=r^t (чистый экспоненц.спад); Qpow(r,t1)·Qpow(r,t2)=Qpow(r,t1+t2). _P4:_ P4-грань: сепарабельность H реализована ТИПОВО — «каждый E_j есть конечное отношение Z#positive» (June 2026: заменило вакуозное ∃e, _==e). Бесконечный спектр — роль-предел перечисления по nat; Element-сторона = любой конкретный конечный уровень/корреляция представим точной рациональной дробью без R.
- **Classical counterpart.** The Osterwalder-Schrader reconstruction theorem (Euclidean OS1-OS5 correlations ⟹ Wightman QFT: Hilbert space, Hamiltonian, vacuum, fields) and the Wightman axioms W1-W5. NEW/HONEST: reconstruction is trivial here because the transfer matrix is DIAGONAL, and two of the five Wightman axioms (W2 Poincaré covariance, W4 locality) are formalized only as Q-commutativity a*b==b*a — far weaker than the classical statements.
- **Tags.** gauge, wightman, osterwalder-schrader, QFT, reconstruction, diagonal, clebsch-gordan, weakened-axioms, Q-arithmetic, methods
- **Notes.** STATUS header says ~30 Qed; actual Qed count = 23. No own axioms/Admitted; file ends with 'Print Assumptions wightman_summary'. Honesty notes: W2/W4 inside wightman_axioms_satisfied are only Q-commutativity (a*b==b*a), much weaker than classical Poincare covariance/locality; header itself notes hilbert_separable was de-vacuated in June 2026.

**Lemmas (24):**

| name | kind | role |
|---|---|---|
| `ground_energy_is_zero` | Theorem | E_0=0 при t_0>0 (= ground_energy_zero) |
| `first_excited_positive` | Theorem | 0 < physical_energy 1 1 (первый возбуждённый уровень положителен на β=1) |
| `energy_nonneg` | Theorem | 0≤E_j при 0<t_0, 0≤t_j≤t_0 (через Qle_shift_div) |
| `energy_gap_is_mass_gap` | Theorem | energy_gap β == physical_energy 1 β (щель = E_1, т.к. E_0=0) |
| `vacuum_unique` | Theorem | вакуум невырожден: 0<gap_M0 1 ∧ 0<gap_M0 2 (t_0>t_1) |
| `hilbert_separable` | Theorem | ★ сепарабельность: ∀j∃num,den physical_energy j 1 = num#den (типовая, не вакуозная) |
| `hamiltonian_diagonal` | Theorem | H диагонален: E_j == 1 − t_j/t_0 (функция только от j) |
| `hamiltonian_bounded_below` | Theorem | inf спектра = E_0=0 ∧ E_1>0 |
| `field_selection_rule` | Theorem | ★ правило отбора Clebsch-Gordan: coupling_allowed j j / j (j+1) / j (j−1) |
| `time_evolution` | Theorem | ⟨1\|Φ(t)\|0⟩ = full_correlation = Qpow(gap_ratio β, t_sep) |
| `wightman_two_point` | Theorem | двухточечная W(t)=Qpow(gap_ratio β, t_sep) (чистый экспон.спад со скоростью=щель) |
| `wightman_positive` | Theorem | W(t)≥0 (Qpow_nonneg при r≥0) |
| `spectral_representation` | Theorem | спектр.представление: одночлен j=1 доминирует, W(t)=Qpow(gap_ratio,t) |
| `wightman_W1` | Theorem | W1 (гильбертово пр-во) = hilbert_separable |
| `wightman_W2` | Theorem | W2 (трансляц.инвариантность): C(t1)·C(t2)==C(t1+t2) через Qpow_add (реальная факторизация) |
| `wightman_W3` | Theorem | W3 (спектр.условие) = energy_nonneg (E_j≥0) |
| `wightman_W4` | Theorem | W4 (локальность) = ∀a b:Q, a*b==b*a (СВЕДЕНО к Q-коммутативности — слабее классики) |
| `wightman_W5` | Theorem | W5 (единственность вакуума) = vacuum_unique (щель>0) |
| `wightman_axioms_satisfied` | Definition | конъюнкция W1–W5 как Prop (W2,W4 = Q-коммутативность) |
| `wightman_from_os` | Theorem | ★ реконструкция: wightman_axioms_satisfied доказана (OS⟹Wightman на диаг.T) |
| `wightman_mass_gap_1` | Theorem | 0 < physical_energy 1 1 (масс-щель на β=1) |
| `wightman_mass_gap_2` | Theorem | 0 < physical_energy 1 2 (масс-щель на β=2) |
| `wightman_gap_equals_energy_gap` | Theorem | energy_gap β == physical_energy 1 β (= energy_gap_is_mass_gap) |
| `wightman_summary` | Theorem | итог: аксиомы ∧ щель(1)>0 ∧ щель(2)>0 ∧ вакуум-единственность; Print Assumptions |

**Key lemmas (deep):**

- **`wightman_from_os`** - Заявленная реконструкция OS⟹Wightman, доказанная целиком — но честность в деталях: W1 (сепарабельность) и W3 (E_j≥0) и W5 (щель>0) — содержательны, тогда как W2 (пуанкаре-ковариантность) и W4 (локальность/коммутативность полей) СВЕДЕНЫ внутри wightman_axioms_satisfied к ∀a b:Q, a*b==b*a — тривиальной коммутативности рациональных чисел. Классическая OS-реконструкция строит операторы на гильбертовом пространстве и доказывает их перестановочность при пространственноподобном разделении; здесь поля скалярно-рациональны, и 'локальность' выполняется автоматически. Реконструкция настоящая лишь в той мере, в какой T диагональна (тривиальный случай). _(OS-reconstruction, weakened-axioms, diagonal, locality)_
- **`wightman_W2`** - Лучший из 'аксиомных' лемм: как самостоятельная теорема W2 доказывает реальную трансляционную инвариантность full_correlation(t1)·full_correlation(t2)==full_correlation(t1+t2) через correlation_eq_ratio + Qpow_add + ring. Это содержательная мультипликативная факторизация корреляции по разделению. ВАЖНО: внутри сводного wightman_axioms_satisfied W2 заменён на Q-коммутативность — то есть сильная версия существует как отдельная лемма, но в итог не попадает. _(translation-invariance, Qpow, factorization, real-content)_
- **`hilbert_separable`** - Образец дероли вакуозности (отмечен в шапке, June 2026): раньше было ∃e, physical_energy j 1 == e (тривиально истинно для любого e=само значение); теперь — ∀j∃num,den, physical_energy j 1 = num#den, т.е. КАЖДЫЙ уровень есть конкретная рациональная дробь по типу. Это P4-сепарабельность: счётный nat-индексированный спектр, каждый член Element-конечен. Честная замена пустого утверждения на типовое, хоть и всё ещё слабое (любое Q таково). _(separability, de-vacuation, P4, Q-rational)_

**Uniqueness - score 2 (methods).** Явная, полностью доказанная OS→Wightman реконструкция на ДИАГОНАЛЬНОЙ решёточной трансфер-матрице над ℚ (без R): диагональный гамильтониан E_j=1−t_j/t_0, вакуум j=0, Clebsch-Gordan правило отбора, двухточечная функция = чистый рациональный экспон.спад Qpow(gap_ratio,t) с реальной трансляц.факторизацией.
> _Caveat:_ Реконструкция тривиализуется диагональностью T (классическая OS-теорема — для недиагонального случая). W2 (Пуанкаре-ковариантность) и W4 (локальность) в сводном wightman_axioms_satisfied СВЕДЕНЫ к ∀a b:Q, a*b==b*a — намного слабее классических аксиом; настоящая W2 существует лишь как отдельная лемма. Поля скалярно-рациональны (не операторнозначные). Только SU(2), щель проверена на β=1,2.

---

## #530 - `src/gauge/WilsonAction.v` - score 2 (methods)

**Wilson action over ℚ: 1st-order Boltzmann weight + 2×2 Hessian with eigenvalues 0 and 2β**

- **Topic.** Concrete rational lattice-gauge primitives: Boltzmann weight w=1−S (gauge-invariant, =1 at vacuum), strong/weak coupling dichotomy, and the 1-plaquette Hessian β·[[1,−1],[−1,1]] shown symmetric, trace 2β, det 0, with eigenvalues 0 (gauge mode (1,1)) and 2β (physical mode (1,−1)), orthogonal eigenvectors.
- **Role.** Low-level building block of the gauge_lattice chain (one of its early files). Imports LinearAlgebra, CauchyReal, physics.{InnerProductSpace,Orthogonality,QObservable,QState}, linalg.{MatrixOps,EigenvalueTheory}, gauge.{LatticeStructure,GaugeField}; provides boltzmann_weight and hessian_1plaq reused by transfer-matrix files.
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs List Lia ZArith Lqa; ToS: LinearAlgebra CauchyReal; physics: InnerProductSpace Orthogonality QObservable QState; linalg: MatrixOps EigenvalueTheory; gauge: LatticeStructure GaugeField
- **E/R/R.** _Elements:_ конкретная конфигурация GaugeConfig N; вакуум zero_config N; 2×2 матрица Гессе hessian_1plaq β = qmat2x2 β −β −β β; собств.векторы qvec2 1 1 и qvec2 1 (−1); рациональные θ. _Roles:_ boltzmann_weight = роль-вес (статвес конфигурации, 1-й порядок); strong/weak_coupling = роли-режимы по β; гессиан = роль-оператор 2-й вариации; собств.значение 0 = роль калибровочной нуль-моды, 2β = роль физической моды. _Rules:_ w=1−S; w(вакуум)==1; w калибровочно-инвариантен (action_gauge_invariant); тр(H)=2β, det(H)=0 (вырожден); H(1,1)=0·(1,1), H(1,−1)=2β·(1,−1); ⟨(1,1),(1,−1)⟩=0; cos≈1−θ²/2. _P4:_ P4-грань мягкая: всё над Element-конечным (2 линка, 1 плакета, точная ℚ-арифметика, vm/lra). Нуль-мода det=0 = калибровочная избыточность (различение без физ.содержания); строго конечная актуальность — никакого предела/континуума здесь нет, это атомарный кирпич.
- **Classical counterpart.** The Wilson lattice gauge action S[g]=(β/2)Σ_P θ_P² (small-angle/quadratic approximation of the plaquette action), its Boltzmann weight e^{-S}, gauge invariance, and the Hessian of a single plaquette with one flat (gauge) zero mode and one physical mode. NEW: only the exact rational (Q) 2×2 computation; the physics (quadratic expansion, 1st-order Boltzmann weight) is standard and explicitly approximate.
- **Tags.** gauge, wilson-action, lattice, boltzmann-weight, hessian, eigenvalue, gauge-zero-mode, Q-arithmetic, linear-algebra, methods
- **Notes.** STATUS header says ~18 Qed (and a body comment says ~14); actual Qed count = 13. total_count proves (14=14), an aspirational marker not matching the real count. No own axioms/Admitted. Cleanest/most honest of the five gauge files in this batch — concrete 2×2 linear algebra, explicitly an approximation, no Millennium/continuum over-branding.

**Lemmas (18):**

| name | kind | role |
|---|---|---|
| `boltzmann_weight` | Definition | статвес 1-го порядка w[g] = 1 − wilson_action_quad N β g |
| `boltzmann_at_vacuum` | Lemma | w(zero_config)==1 (максимум, из action_zero_config) |
| `boltzmann_gauge_invariant` | Lemma | ★ w калибровочно-инвариантен (через action_gauge_invariant) |
| `strong_coupling` | Definition | режим сильной связи: β < 1 |
| `weak_coupling` | Definition | режим слабой связи: 1 ≤ β |
| `coupling_dichotomy` | Lemma | ∀β: strong ∨ weak (lra-разбор) |
| `hessian_1plaq` | Definition | гессиан 1 плакеты: qmat2x2 β −β −β β = β·[[1,−1],[−1,1]] |
| `hessian_symmetric` | Lemma | гессиан симметричен (по элементам 2×2) |
| `hessian_trace` | Lemma | tr(H)==2β |
| `hessian_det` | Lemma | ★ det(H)==0 (вырожден: есть калибровочная нуль-мода) |
| `hessian_eigenvalue_zero` | Lemma | ★ 0 — собств.значение, собств.вектор (1,1) = равномерный сдвиг (калибр.) |
| `hessian_eigenvalue_2beta` | Lemma | ★ 2β — собств.значение, собств.вектор (1,−1) = флуктуация (физ.) |
| `cos_approx_2` | Definition | приближение cos(θ)≈1−θ²/2 |
| `cos_approx_at_zero` | Lemma | cos_approx_2 0 == 1 |
| `vacuum_is_minimum` | Lemma | вакуум — минимум: wilson_action_quad(zero_config)==0 при β>0 |
| `hessian_eigvecs_orthogonal` | Lemma | ⟨(1,1),(1,−1)⟩==0 (ортогональность собств.векторов) |
| `wilson_action_summary` | Theorem | итог: w(вакуум)=1 ∧ w калибр.-инвар. ∧ собств.знач.0 ∧ 2β ∧ det=0 |
| `total_count` | (deleted) | June 2026: tail-stamp sham DELETED from src (self-equality/numerology/duplicate-alias); qed updated |

**Key lemmas (deep):**

- **`hessian_eigenvalue_zero`** - Содержательное ядро файла: на гессиане β·[[1,−1],[−1,1]] явно предъявлен собств.вектор (1,1) с λ=0 — равномерный сдвиг фаз, т.е. КАЛИБРОВОЧНАЯ нуль-мода. Доказательство аккуратно: ненулевость вектора + mat_vec_mul_nth/qv_scale_nth + разбор по компонентам, всё через lra над точной ℚ. Это решёточная реализация утверждения «калибровочная избыточность ⟹ плоское направление действия» на минимальном 2×2. Классически тривиально; ценность — точная рациональная проверка без R. _(hessian, gauge-zero-mode, eigenvalue, Q-arithmetic)_
- **`hessian_eigenvalue_2beta`** - Парная физическая мода: вектор (1,−1) с собств.значением 2β — относительная флуктуация фаз, единственное направление с ненулевой кривизной действия. Вместе с hessian_eigenvalue_zero и det=0 даёт полную спектральную картину одноплакеточного гессиана (0 ⊕ 2β), которую переиспользуют трансфер-матричные файлы. Ортогональность мод (hessian_eigvecs_orthogonal) замыкает разложение. _(hessian, physical-mode, eigenvalue, spectrum)_
- **`boltzmann_gauge_invariant`** - Перенос калибровочной инвариантности с действия на статвес: w[gauge_transform g φ]==w[g], напрямую из action_gauge_invariant. Делает Element-наблюдаемую (вес Больцмана) физически корректной — независимой от калибровочного представителя. Простое следствие, но структурно важное: гарантирует, что последующая статистика интегрирует по физическим, а не калибровочным степеням свободы. _(gauge-invariance, boltzmann-weight, well-defined)_

**Uniqueness - score 2 (methods).** Чистая точная рациональная (без R) формализация базовых примитивов решёточной калибровочной теории: 1-й порядок веса Больцмана (калибр.-инвариантного, =1 в вакууме) и полный спектр одноплакеточного гессиана β·[[1,−1],[−1,1]] — собств.значения 0 (калибр.нуль-мода (1,1)) и 2β (физ.мода (1,−1)), ортогональные, det=0 — всё проверено через vm_compute/lra.
> _Caveat:_ Стандартная физика: квадратичное приближение действия Вильсона и 1-й порядок e^{−S} ЯВНО приближённы (cos≈1−θ²/2). Гессиан — для ОДНОЙ плакеты / 2 линков, не для решётки. Никаких новых результатов — кирпич-плумбинг для трансфер-матричных файлов. Чистейший (без оверклейма) из пяти, но наименее уникальный по содержанию.

---

## #531 - `src/gauge/YangMillsComplete.v` - score 1 (exposition)

**SU(2) lattice mass-gap aggregator: bundles transfer-matrix/OS1-5/Wightman lemmas into one 'Millennium' conjunction**

- **Topic.** Aggregator capstone that conjoins, via exact imports, the whole SU(2) lattice chain: transfer matrix diagonal with Bessel eigenvalues, lattice gap gap_M0>0 at beta=1,2, RG mass relation, OS1-5 verified at beta=1, and a constructed WightmanQFT with positive gap. Each conjunct is `exact <imported_lemma>`.
- **Role.** Top-level synthesis of the Phase-B + Proof-Closure gauge stack. Imports ~30 gauge modules (CharacterTransfer, ExactMassGap, GapRatio, LatticeRG, ReflectionPositivity, TransferMatrixProof, CorrelationProof, HilbertConstruction, ProofClosure, ...). Pure re-export; no file imports it back (leaf).
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: CauchyReal SeriesConvergence; gauge: CharacterTransfer ExactMassGap GapRatio LatticeRG ReflectionPositivity ContinuumGap LatticeCorrelations LatticeOS1_Analyticity LatticeOS2_Regularity LatticeOS3_Covariance WightmanReconstruction YMLevel4Complete YMLevel5Complete TransferMatrixProof ReflectionPositiveProof ClusterProof PhaseB_Synthesis CorrelationProof CovarianceProof HilbertConstruction ProofClosure
- **E/R/R.** _Elements:_ конкретная решётка SU(2); рациональные собственные значения transfer_mat (Бессель I0,I2,I4); рациональная щель gap_M0 = 289/384 при beta=1; корреляторы full_correlation как отношения многочленов. _Roles:_ transfer-матрица = L5-оператор эволюции по слоям; gap = щель спектра; OS1-5 = роли-аксиомы реконструкции; Wightman QFT = реконструированный объект-арена. _Rules:_ цепочка решётка → характеры (Питер-Вейль) → диагонализация → Бессель-позитивность → RG → OS1-5 → Вайтман → Delta>0; каждый конъюнкт = exact импортированной леммы. _P4:_ P4-честно: ВСЁ доказанное живёт на КОНЕЧНОЙ решётке при фиксированных рациональных beta (Element-сторона, vm_compute-разрешимо). Континуальный предел a→0, бесконечный объём и Лоренц-ковариантность — role-limit, НЕ достигнуты; имя 'Millennium' аспирационно, тело же честно (honest_assessment перечисляет ровно решёточное содержание).
- **Classical counterpart.** Clay Millennium 'Yang-Mills existence and mass gap' (Jaffe-Witten 2000) and the Osterwalder-Schrader / Wightman reconstruction theorems. WHAT DIFFERS: this is a SU(2) FINITE-LATTICE transfer-matrix computation with exact-rational (Q) eigenvalues; the OS1-5 'axioms' are verified only for the lattice correlators at fixed beta=1,2, NOT the continuum R^4 theory, NOT any compact simple G, and the continuum/thermodynamic/Lorentz limits are absent. The headline gap 289/384 is a lattice number, not the Clay constant.
- **Tags.** gauge, yang-mills, mass-gap, lattice, su2, aggregator, over-branding, osterwalder-schrader, P4
- **Notes.** DRIFT: header says '~30 Qed', actual Qed = 13. 13 top-level decls (all Theorem). 0 Admitted, 0 own axioms. Honesty: name+banner brand this as the Clay Millennium proof but it is a finite SU(2) lattice computation at beta=1,2; internal honest_assessment/structural_components scope it correctly. 12/13 lemmas are bare `exact <import>` (plumbing); only mass_gap_rg_invariant has a real sub-proof.

**Lemmas (13):**

| name | kind | role |
|---|---|---|
| `yang_mills_mass_gap` | Theorem | ★ гранд-конъюнкция 12 пунктов: диагональность transfer-матрицы + щель + RG + OS1-5 + Вайтман (всё на решётке SU(2), beta=1) |
| `the_key_inequality` | Theorem | 0 < gap_M0 1 /\ 0 < gap_M0 2 — щель Бесселя I0-2I2+I4 > 0 при beta=1,2 |
| `fundamental_bound` | Theorem | gap_ratio 1 < 1 /\ gap_ratio 2 < 1 (фундаментальная граница отношения t1/t0) |
| `energy_gap_positive` | Theorem | 0 < physical_energy при beta=1 для J=1,2 |
| `mass_gap_rg_invariant` | Theorem | physical_mass(rg_step r)(2a) > 0 — единственный лемма с собственным доказательством (Qmult_lt_0_compat), не голый exact |
| `artifacts_vanish` | Theorem | artifact_at_step убывает по шагам RG (решёточные артефакты исчезают) |
| `clay_comparison` | Theorem | ОВЕР-БРЕНД: 'сравнение с призом Клэя' — на деле лишь exists qft, 0 < wqft_gap qft (решёточный Вайтман) |
| `honest_assessment` | Theorem | ★ ЧЕСТНЫЙ якорь: перечисляет ровно решёточное содержание (gap_M0>0, решёточный Вайтман, RP) — без континуума |
| `structural_components` | Theorem | конъюнкция OS1-5 при beta=1 как структурные компоненты |
| `final_numbers` | Theorem | matrix_mass_gap 1 1 0 == 289#384 и 1 2 0 == 1#24 (конкретные рациональные значения щели) |
| `three_millennium_final` | Theorem | ОВЕР-БРЕНД: 'YANG-MILLS: COMPLETE, Delta=289/384' — снова решёточная тройка gap/Вайтман/значение |
| `proof_in_six_lines` | Theorem | тройка off-diagonal + gap_M0>0 + Вайтман (резюме 'доказательство в шесть строк') |
| `yang_mills_complete_summary` | Theorem | финальная сводка: щель + отношение + энергия + Вайтман + OS1-5 + сжатие артефактов |

**Key lemmas (deep):**

- **`yang_mills_mass_gap`** - 12-членная refine-конъюнкция, где каждый пункт = exact одной импортированной леммы. Это чистый плумбинг-агрегатор: ноль нового математического содержания, вся работа — в импортированных gauge-модулях. Имя и шапка ('THE MILLENNIUM PROBLEM', 'Delta>0 on R^4') аспирационны и вводят в заблуждение: реально это конъюнкция КОНЕЧНО-РЕШЁТОЧНЫХ фактов SU(2) при beta=1 (диагональность transfer_mat, gap_M0 = 289/384, OS1-5 для решёточных корреляторов, решёточный Вайтман). Континуум отсутствует. _(aggregator, over-branding, lattice-only, su2)_
- **`honest_assessment`** - Внутренний честный противовес имени файла: явно нумерует 10 ДОКАЗАННЫХ решёточных пунктов (transfer-матрица диагональна, gap_M0>0 при beta=1,2, отношение <1, RG-сжатие r->r^2, OS1-5, решёточный Вайтман) — и ни один из них не есть континуальная теорема Клэя. Ценность файла как каталожной записи именно здесь: тело документа само себя дисклеймит, контраст с over-branded именами (clay_comparison, three_millennium_final). _(honesty, disclaimer, lattice-scope)_
- **`mass_gap_rg_invariant`** - Единственная лемма файла с НЕтривиальным собственным доказательством (не голый exact): из mass_rg_relation и положительности (1+r)/2 выводит положительность physical_mass после RG-шага через Qmult_lt_0_compat. Несёт реальную, но крошечную арифметическую работу; остальные 12 — делегация. _(rg, self-contained-proof, Q-arith)_

**Uniqueness - score 1 (exposition).** Агрегатор-витрина SU(2)-решёточной программы щели масс: собирает transfer-матрицу, Бессель-щель, RG, OS1-5 и решёточный Вайтман в один конъюнкт-капстоун с конкретным рациональным значением 289/384 при beta=1.
> _Caveat:_ НЕ доказывает проблему Клэя. Всё содержание — КОНЕЧНАЯ решётка SU(2) при фиксированных рациональных beta; OS1-5 проверены лишь для решёточных корреляторов при beta=1; континуальный предел a→0, бесконечный объём и Лоренц-ковариантность ОТСУТСТВУЮТ. Имена (yang_mills_mass_gap/clay_comparison/three_millennium_final, 'THE MILLENNIUM PROBLEM') аспирационны; 12 из 13 лемм — голые exact импортов (ноль нового). Шапка '~30 Qed' расходится с фактическими 13.

---

## #532 - `src/gauge/YangMillsCorrected.v` - score 3 (new-framing)

**SU(2) gap, corrected to |t0-t1|: positive for ALL rational beta via irrationality of sqrt(1920)**

- **Topic.** Re-issues the SU(2) lattice mass gap with the CORRECTED definition spectral_gap = |t0-t1| (absolute value) instead of t0-t1, which fixes a real sign bug at beta>=3 (original matrix_mass_gap 1 3 0 < 0). Positivity for all rational beta>0 rests on one arithmetic fact: the gap polynomial has no rational root because sqrt(1920) is irrational.
- **Role.** Corrected sibling of YangMillsComplete: same OS1-3 (formal)/Wightman exports plus SpectralGapCorrect (the |.| fix) and the irrationality lemmas. Imports CharacterTransfer, ExactMassGap, GapRatio, SpectralGapCorrect, Formal{Analytic,Tempered,SO4}. Reused conceptually by YangMillsFinal/Process (which import spectral_gap_pos_all_rational).
- **Counts.** Qed 23 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: CauchyReal SeriesConvergence; gauge: CharacterTransfer ExactMassGap GapRatio TransferMatrixProof ReflectionPositiveProof ClusterProof CorrelationProof HilbertConstruction FormalAnalytic FormalTempered FormalSO4 PhaseB_Synthesis SpectralGapCorrect
- **E/R/R.** _Elements:_ рациональные собственные значения t0_M0,t1_M0; спектральная щель \|t0-t1\|; квартика 384-96beta^2+beta^4; целочисленный факт 1920 не полный квадрат (43^2<1920<44^2). _Roles:_ spectral_gap (с модулем) = исправленная роль-щель; дискриминант/иррациональность = роль-страж положительности; OS1-3 формальные = роли-аксиомы. _Rules:_ \|t0-t1\| > 0 ⟺ t0 != t1 ⟺ квартика без рационального корня ⟺ sqrt(1920) иррационален; пересечение собственных значений при beta≈2.83 (t0<t1 при beta=3), но щель остаётся >0. _P4:_ Element-сторона: для КАЖДОГО рационального beta положительность щели решается иррациональностью (число 1920 — конкретный Element). Иррациональность sqrt(1920) сама — role-limit (нет рационального корня), и именно она ГАРАНТИРУЕТ зазор. Континуум по-прежнему role-limit/открыт.
- **Classical counterpart.** Mirrors the same Clay Millennium framing, but the load-bearing core is a classical NUMBER-THEORY fact: 1920 = 2^7*3*5 is not a perfect square (43^2=1849<1920<1936=44^2), hence sqrt(30)/sqrt(1920) irrational, hence the quartic 384-96b^2+b^4 has no rational root. WHAT DIFFERS from Clay: still a fixed SU(2) lattice spectral-gap statement over rational beta; positivity of \|t0-t1\| for all rational beta is an irrationality argument, NOT a continuum existence/mass-gap proof.
- **Tags.** gauge, yang-mills, mass-gap, lattice, su2, irrationality, perfect-square, bug-fix, vein-A, P4
- **Notes.** DRIFT: header '~30 Qed', actual Qed = 23. 23 top-level decls (all Theorem). 0 Admitted, 0 own axioms. Genuine content vs sibling Complete: the irrationality core (the_key_fact, sqrt_1920_irrational) and the honest self-diagnosis original_fails_at_3 (proves the prior matrix_mass_gap was NEGATIVE at beta=3). spectral_gap redefined as |t0-t1| (abs) — a definition choice that makes 'gap' positive even past the eigenvalue crossing at beta~2.83.

**Lemmas (23):**

| name | kind | role |
|---|---|---|
| `corrected_gap_1` | Theorem | spectral_gap 1 1 0 == 289#384 (значение при beta=1, без изменений) |
| `corrected_gap_2` | Theorem | spectral_gap 1 2 0 == 1#24 (значение при beta=2) |
| `corrected_gap_all` | Theorem | ★ spectral_gap > 0 для ВСЕХ рациональных beta>0 (ядро исправления) |
| `corrected_gap_any_J` | Theorem | spectral_gap > 0 при любом J и beta>0 |
| `corrected_gap_3` | Theorem | 0 < spectral_gap 1 3 0 (был баг в оригинале) |
| `corrected_gap_4` | Theorem | 0 < spectral_gap 1 4 0 (был баг) |
| `corrected_rp` | Theorem | отражательная позитивность 0 <= rp_inner_matrix при 0<=beta<=2 |
| `corrected_cluster` | Theorem | кластер: gap_ratio^N -> 0 (exists N, < eps) |
| `corrected_os1` | Theorem | OS1: корреляторы решёточно-аналитичны (is_lattice_analytic) |
| `corrected_os2` | Theorem | OS2: корреляторы темперированы при beta=1, j∈{0,1} |
| `corrected_os3` | Theorem | OS3: корреляторы SO(4)-инвариантны |
| `corrected_wightman` | Theorem | решёточный Вайтман QFT существует с щелью>0 |
| `yang_mills_CORRECTED` | Theorem | ★ исправленная гранд-конъюнкция: щель>0 для всех рац. beta + значения + OS1-3 + Вайтман |
| `the_key_fact` | Theorem | ★ forall p:Z, ~(p*p=1920) — несущий арифметический факт (1920 не полный квадрат) |
| `sqrt_30_irrational` | Theorem | sqrt(30) иррационален (нет a,b: a^2=30b^2) |
| `sqrt_1920_irrational` | Theorem | sqrt(1920) иррационален |
| `gap_polynomial_no_rational_roots` | Theorem | квартика gap_M0 не зануляется ни при каком рациональном beta>0 |
| `yang_mills_from_arithmetic` | Theorem | из 43^2<1920<44^2 ⟹ щель>0 для всех beta (дисклеймит зависимость от одного факта) |
| `corrected_eigenvalue_crossing` | Theorem | пересечение собственных значений: t1<=t0 при beta<=2, t0<t1 при beta=3, но щель всегда >0 |
| `original_valid_at_1` | Theorem | оригинал matrix_mass_gap корректен при beta=1 (==289#384, >0) |
| `original_fails_at_3` | Theorem | ★ ЧЕСТНО: matrix_mass_gap 1 3 0 < 0 — оригинал БАГ при beta=3 |
| `corrected_works_everywhere` | Theorem | контраст: оригинал >0 лишь при beta<=2 (баг при 3), исправление >0 всюду |
| `corrected_summary` | Theorem | сводка: spectral_gap всегда >=0, >0 при beta>0, значения, OS1-3, Вайтман |

**Key lemmas (deep):**

- **`the_key_fact`** - Несущий камень всего файла: forall p:Z, ~(p*p=1920). Через 43^2=1849<1920<1936=44^2 (классический perfect-square тест) даёт иррациональность sqrt(1920)=8sqrt(30), откуда квартика 384-96beta^2+beta^4 не имеет рационального корня, откуда t0!=t1, откуда \|t0-t1\|>0 для ВСЕХ рациональных beta. Это та же Element/role-limit пружина, что и дискриминант в BoundaryDecidability (#97): положительность щели = иррациональность = role-limit-сторона perfect-square дисциплины. Содержательнее, чем чистый агрегатор Complete: здесь работает настоящий теоретико-числовой аргумент. _(irrationality, perfect-square, vein-A, load-bearing)_
- **`original_fails_at_3`** - Редкая ЧЕСТНАЯ лемма в over-branded кластере: доказывает, что ПРЕДЫДУЩИЙ 'окончательный' результат (matrix_mass_gap с t0-t1 без модуля) ОТРИЦАТЕЛЕН при beta=3, т.е. был багом. Файл сам диагностирует дефект соседних капстоунов (Complete/Sealed используют matrix_mass_gap, валидный лишь при beta<=2). Каталожно ценно: показывает, что 'Final/Complete' имена в этом кластере не монотонно-истинны. _(bug-fix, honesty, self-correction)_
- **`corrected_gap_all`** - Главный исправленный результат: spectral_gap 1 beta 0 > 0 для всех рациональных beta>0, делегирует spectral_gap_pos_all_rational (SpectralGapCorrect.v). Снимает beta<=2 ограничение оригинала ценой переопределения щели через \|.\|. Честная оговорка: это положительность щели ФИКСИРОВАННОЙ решётки при каждом beta — не континуальная теорема; \|t0-t1\| с модулем — определенческий выбор, делающий 'щель' положительной даже там, где упорядочение t0,t1 переворачивается (crossing при beta≈2.83). _(spectral-gap, all-rational-beta, definition-choice)_

**Uniqueness - score 3 (new-framing).** Исправляет SU(2)-решёточную щель до |t0-t1| и сводит её положительность для всех рациональных beta к ОДНОМУ теоретико-числовому факту (1920 не полный квадрат ⟹ sqrt(1920) иррационален), плюс честно диагностирует знаковый баг прежней версии при beta=3.
> _Caveat:_ НЕ проблема Клэя: фиксированная решётка SU(2), щель над рациональными beta; OS1-3 формальны лишь для решёточных корреляторов. Несущий факт (perfect-square тест) и иррациональность sqrt(D) — классика; ново лишь обрамление 'щель = иррациональность' и переопределение через |.|. Имя yang_mills_CORRECTED аспирационно. Шапка '~30 Qed' расходится с фактическими 23.

---

## #533 - `src/gauge/YangMillsFinal.v` - score 3 (new-framing)

**SU(2) Yang-Mills 8-level synthesis: positive AND negative (RG-wall) results, with continuum honestly OPEN**

- **Topic.** Final synthesis of the SU(2) lattice chain across levels L1-L9 (non-abelian, RG contraction r->r^2, Cauchy orbits, exact RG process, gap positive at every finite stage, gap VANISHES in the continuum limit, no correction saves it, P4 reading, spectral gap |t0-t1|>0 for all rational beta). Explicitly separates what is proved from what remains open.
- **Role.** Capstone over the L1-L8 gauge modules (TransferMatrix, SU2Group, StrongCoupling, RGFlow, NonlinearRG, ExactRGProcess, WallTheorem, ...) plus SpectralGapCorrect. Imported by YangMillsProcess.v (which reuses su2_gap_vanishes, su2_mass_gap_positive). Leaf otherwise.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: CauchyReal FixedPoint; gauge: TransferMatrix SU2TransferMatrix SU2Group StrongCoupling RGFlow SU2Synthesis HigherOrderRG PerturbationRG MassGapBound NonlinearRG ExtendedInterval LargerLattice GapMatching ExactRGProcess NonperturbativeGap MillenniumSynthesis GapDecayRate ConfinementCorrection TopologicalObstruction WallTheorem SpectralGapCorrect
- **E/R/R.** _Elements:_ SU(2) как рациональная решётка (некоммутативность qmul); RG-карта rg_map_quadratic с неподвижной точкой 3; точный RG-процесс exact_rg_orbit; щель на стадии su2_gap_at_k; струнное натяжение string_tension; спектральная щель \|t0-t1\|. _Roles:_ уровни L1-L9 = роли-ярусы синтеза; RG-карта = L5-сжатие (is_contraction); стена (WallTheorem) = роль-препятствие; P4-чтение = процессная роль щели. _Rules:_ rg_map_quadratic — сжатие (3#2,4,16#25), орбиты Коши; щель>0 на каждой конечной стадии, НО su2_gap_at_k -> 0 при k->inf; никакая RG-совместимая поправка не сохраняет щель; \|t0-t1\|>0 для всех рац. beta. _P4:_ ОБРАЗЦОВО P4-честно: щель = ПРОЦЕСС {su2_gap_at_k}. На каждой конечной стадии (Element) она >0; её континуальный предел (role-limit) РАВЕН НУЛЮ вдоль RG-орбиты. Два факта сосуществуют без противоречия: фиксированно-beta щель >0, но RG-поток гонит её к 0. Континуум/бесконечный объём/Лоренц — явно ОТКРЫТЫ (what_remains_open).
- **Classical counterpart.** Clay Millennium Yang-Mills again, plus the standard lattice picture of confinement (string tension), asymptotic freedom and the continuum limit. WHAT DIFFERS: this file is unusually HONEST — it pairs positive lattice/process results with explicit NEGATIVE results (gap vanishes along RG orbit, no RG-compatible correction preserves it, tension-gap paradox at beta=8) and names continuum/infinite-volume/Lorentz as OPEN. Not a continuum proof of anything.
- **Tags.** gauge, yang-mills, mass-gap, lattice, su2, rg-flow, negative-results, honesty, P4, process-vs-limit
- **Notes.** DRIFT: header '~18 Qed', actual Qed = 8. 8 top-level decls (all Theorem). 0 Admitted, 0 own axioms. The MOST honest file of the five: negative_results proves the gap vanishes in the continuum limit and that coupling GROWS (no asymptotic freedom), and what_remains_open/what_tos_proves_about_ym explicitly list continuum/infinite-volume/Lorentz as OPEN. The 'complete' in yang_mills_complete is internally disclaimed.

**Lemmas (8):**

| name | kind | role |
|---|---|---|
| `positive_results` | Theorem | ★ 8 положительных фактов: некоммутативность SU(2), щель>0 на (0,8), RG-сжатие, неподвижная точка 3, орбиты Коши, точный процесс Коши, щель>0 на каждой стадии, натяжение>0 |
| `negative_results` | Theorem | ★ 4 ОТРИЦАТЕЛЬНЫХ факта: щель исчезает вдоль орбиты, нет совместимой поправки, парадокс натяжение-щель при beta=8, связь растёт (НЕ асимптотическая свобода) |
| `resolution_paths` | Theorem | пути разрешения: щель>0 на каждой стадии + исчезает в континууме + нет сохраняющей поправки |
| `p4_resolution` | Theorem | P4-разрешение: щель>0 всюду + RG-процесс Коши + согласование щели (gap_matching) |
| `what_remains_open` | Theorem | ★ ЧЕСТНО: тело = spectral_gap>0 для всех рац. beta; комментарий перечисляет ОТКРЫТОЕ (континуум a→0, бесконечный объём, Лоренц-ковариантность) |
| `rg_wall_persists` | Theorem | ★ RG-стена реальна: su2_gap_at_k->0 вдоль орбиты, НО spectral_gap>0 при каждом beta — оба сосуществуют |
| `yang_mills_complete` | Theorem | ★ полный синтез L1-L9 одной конъюнкцией (включает и положительные, и отрицательные ярусы) |
| `what_tos_proves_about_ym` | Theorem | ★ реестр: что ToS ДОКАЗЫВАЕТ (щель на стадиях, RG-процесс, натяжение, P4, OS1-3) vs ОТКРЫТО (континуум, объём, Лоренц) |

**Key lemmas (deep):**

- **`negative_results`** - Самая необычная для over-branded кластера лемма: вместо триумфа доказывает ЧЕТЫРЕ препятствия — (1) su2_gap_at_k -> 0 вдоль RG-орбиты (щель исчезает в континууме), (2) нет RG-совместимой поправки, сохраняющей щель, (3) парадокс: натяжение>0, но su2_mass_gap 8 == 0 при beta=8, (4) связь beta_k РАСТЁТ (НЕ асимптотическая свобода — антифизично для непрерывной YM). Это честный ledger пределов решёточного подхода; именно он спасает файл от over-claim и делает 'Final' содержательным, а не пустым. _(negative-results, rg-wall, honesty, limits)_
- **`rg_wall_persists`** - Тонкая P4-точка: примиряет su2_gap_vanishes (предел=0 вдоль RG) с spectral_gap_pos_all_rational (>0 при каждом фиксированном beta), объясняя, что это РАЗНЫЕ величины — gap_at_k мерит k-ю RG-итерацию, spectral_gap мерит фиксированную решётку. Образцовое применение процессной онтологии: 'щель есть на каждой стадии, но её континуальный предел нулевой' — не парадокс, а две проекции процесса. Это и есть Reading 2 vs Reading 1 различение. _(P4, process-vs-limit, reconciliation)_
- **`what_tos_proves_about_ym`** - Каталожно ключевая: ЯВНЫЙ реестр границы доказанного. Тело — лишь spectral_gap>0 для всех рац. beta, но структурированный комментарий честно делит на ДОКАЗАНО (решёточная щель, RG-процесс Коши, натяжение>0, P4 mass gap, OS1-3, Вайтман) и ОТКРЫТО (континуум с UV-пополнением, бесконечный объём, Лоренц-ковариантная формулировка). Антипод over-branded имён Complete/Sealed: тут сам файл проговаривает, что Millennium-проблема НЕ решена. _(registry, honest-scope, open-problems)_

**Uniqueness - score 3 (new-framing).** Честный двусторонний синтез SU(2)-решёточной программы: положительные результаты (щель на стадиях, RG-сжатие, натяжение) ВМЕСТЕ с отрицательными (щель исчезает в континууме, нет сохраняющей поправки, рост связи) и явным реестром открытого (континуум/объём/Лоренц), оформленный как процессное Reading-2-vs-Reading-1 различение.
> _Caveat:_ НЕ проблема Клэя. Положительные факты — на КОНЕЧНОЙ решётке/в процессе; континуальный предел щели вдоль RG РАВЕН НУЛЮ (доказано негативно). Имя yang_mills_complete аспирационно, но тело честно дисклеймит (what_remains_open, what_tos_proves_about_ym). RG-картина (сжатие, стена, натяжение) — стандартна; ново лишь честное P4-обрамление двух чтений. Шапка '~18 Qed' расходится с фактическими 8.

---

## #534 - `src/gauge/YangMillsProcess.v` - score 4 (synthesis+observation)

**P4 reading of the SU(2) mass gap: the gap PROCESS has PMG (no continuum limit needed); Reading 1 left open**

- **Topic.** Recasts 'Yang-Mills has a mass gap' as a process property: the SU(2) spectral-gap process su2_gap_process satisfies has_process_mass_gap (uniform lower bound 289/384, exponential Cauchy, monotone increase) at beta=1. Foregrounds two explicit readings and proves only the P4 one.
- **Role.** P4/process layer atop YangMillsFinal (imported) and ProcessMassGap/SpectralGapCorrect/GapDecayRate. Defines p4_mass_gap_exists. Connects has_process_mass_gap (the generic PMG predicate) to the concrete SU(2) gap. Leaf capstone; ties the gauge wall to the project's process ontology (ProcessBounds.has_process_mass_gap).
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: CauchyReal SeriesConvergence; gauge: CharacterTransfer SpectralGapCorrect ProcessMassGap GapDecayRate SU2TransferMatrix YangMillsFinal
- **E/R/R.** _Elements:_ процесс щели su2_gap_process beta : nat -> Q; конкретные рациональные стадии 289/384, 7541/7680, 367489/368640; равномерная нижняя граница; экспоненциальный хвост 2*(1/4)^M. _Roles:_ p4_mass_gap_exists = роль-предикат 'процесс имеет PMG'; PMG1-3 = роли-условия (граница/Коши/монотонность); два чтения (стандартное vs P4) = две роли смысла 'mass gap'. _Rules:_ has_process_mass_gap(su2_gap_process 1): PMG1 нижняя граница 289/384, PMG2 \|gap(M+1)-gap(M)\| <= 2(1/4)^M, PMG3 монотонность; стадии строго растут 0<1<2; spectral_gap>0 для всех рац. beta. _P4:_ ЯДРО P4: 'щель масс существует' переопределяется как 'процесс {gap_M} имеет PMG' — БЕЗ завершённого бесконечного объекта, БЕЗ предела a→0. Reading 2 (процесс) ДОКАЗАН для SU(2) при beta=1; Reading 1 (стандартный континуальный предел) явно ОТКРЫТ. Это P4-принцип в действии: процесс ЕСТЬ физика, предел не нужен.
- **Classical counterpart.** The standard (Clay/Wightman) statement 'Yang-Mills has a mass gap' = lim_{a->0} gap(a) > 0. WHAT DIFFERS: this file deliberately substitutes a DIFFERENT, weaker reading (Reading 2) — the gap PROCESS {gap_M} satisfies a finite process-mass-gap predicate (PMG1-3: uniform lower bound + Cauchy + monotone) with NO limit taken. The standard Reading 1 is explicitly left OPEN. This is a reframing of the problem statement, not a proof of the Clay version.
- **Tags.** gauge, yang-mills, mass-gap, P4, process, su2, reframing, process-mass-gap, two-readings, honesty
- **Notes.** DRIFT: header '~25 Qed', actual Qed = 12 (13 decls: 1 Definition + 12 Theorem). 0 Admitted, 0 own axioms. Scored 4 (not lattice-default 1-3) because it genuinely bridges the gauge wall to the project-wide P4/process ontology (has_process_mass_gap) and reframes the QUESTION — the distinctive ToS move — while staying honest: two_readings shows Reading 1 open + gap vanishing along RG. The reframing is a weakening of the problem statement, which the caveat states plainly.

**Lemmas (13):**

| name | kind | role |
|---|---|---|
| `p4_mass_gap_exists` | Definition | предикат: процесс su2_gap_process beta имеет has_process_mass_gap (P4-определение щели) |
| `p4_mass_gap_beta_1` | Theorem | ★ ГЛАВНАЯ: p4_mass_gap_exists 1 — P4 щель масс для SU(2) при beta=1 |
| `gap_process_positive` | Theorem | процесс щели строго положителен на каждой стадии M |
| `gap_process_monotone` | Theorem | монотонность: M<=N ⟹ gap(M)<=gap(N) |
| `gap_process_lower_bound` | Theorem | равномерная нижняя граница 289/384 <= gap(M) для всех M (PMG1) |
| `gap_process_cauchy` | Theorem | экспоненциальная Коши: \|gap(M+1)-gap(M)\| <= 2*(1/4)^M (PMG2) |
| `spectral_gap_universal` | Theorem | для всех рац. beta>0 спектральная щель при M=0 положительна |
| `concrete_gaps` | Theorem | конкретные значения: gap(0)=289/384, gap(1)=7541/7680, gap(2)=367489/368640 |
| `gap_increases_01` | Theorem | gap(0) < gap(1) (строгий рост на первом шаге) |
| `gap_increases_12` | Theorem | gap(1) < gap(2) |
| `two_readings` | Theorem | ★ два чтения: Reading 2 доказано (P4) + RG-стена + spectral_gap>0; Reading 1 = spectral_gap>0 для всех рац. beta |
| `yang_mills_with_process` | Theorem | интеграция: P4 щель + spectral_gap>0 + RG-стена + щель>0 на (0,8) |
| `yang_mills_process_summary` | Theorem | сводка: P4 щель + положительность + монотонность + граница + Коши + универсальная спектральная щель |

**Key lemmas (deep):**

- **`p4_mass_gap_beta_1`** - Флагман процессного чтения: p4_mass_gap_exists 1, т.е. su2_gap_process 1 удовлетворяет has_process_mass_gap (общий PMG-предикат из ProcessMassGap/ProcessBounds). Содержательная новизна кластера именно здесь — НЕ 'предел щели >0' (это Reading 1, открыт), а 'процесс щели финитно квалифицирован как PMG': равномерно ограничен снизу 289/384, экспоненциально Коши, монотонен. Это переопределение самого ВОПРОСА в P4-онтологию (процесс = потенциальная, не актуальная бесконечность). Честно: меняет планку — доказывает достижимую процессную теорему вместо недостижимой континуальной. _(P4, process-mass-gap, reframing, flagship-local)_
- **`two_readings`** - Каталожно решающая лемма: ЯВНО предъявляет обе формулировки 'щели масс' рядом — Reading 1 (стандартный предел a→0, L→inf, Лоренц; ОТКРЫТ) и Reading 2 (процесс {gap_M} имеет PMG; ДОКАЗАН). Внутри одной теоремы соседствуют su2_has_process_mass_gap, su2_gap_vanishes (RG-стена!) и spectral_gap_pos_all_rational. Это противоядие over-branding'у: файл сам отделяет доказанное процессное от открытого континуального и даже включает факт исчезновения щели вдоль RG. _(two-readings, honesty, open-vs-proved)_
- **`concrete_gaps`** - Опорная вычислительная лемма: точные рациональные значения щели на трёх стадиях (289/384 ~ 0.7526, 7541/7680 ~ 0.9819, 367489/368640 ~ 0.99688) — vm_compute-проверяемые Element-факты, на которых стоят PMG1 (нижняя граница) и монотонность. Демонстрирует процесс конкретными числами: щель растёт к ~1, оставаясь ограниченной снизу первым значением. Классически тривиально (рациональная арифметика), но это и есть Element-сторона, делающая PMG доказуемым. _(concrete, Q-arith, vm-compute, pmg1)_

**Uniqueness - score 4 (synthesis+observation).** Переопределяет 'Yang-Mills имеет щель масс' как ПРОЦЕССНОЕ свойство (su2_gap_process удовлетворяет has_process_mass_gap: равномерная граница + экспоненциальная Коши + монотонность) без завершённого бесконечного предела — мост от gauge-стены к процессной онтологии всего проекта (P4), с явным разделением доказанного Reading 2 и открытого Reading 1.
> _Caveat:_ НЕ решает проблему Клэя. Доказанное Reading 2 — это ВЫБОР более слабой формулировки (финитный PMG-предикат на процессе), а не стандартный континуальный mass gap; Reading 1 (предел a→0, бесконечный объём, Лоренц-ковариантность) явно ОСТАЁТСЯ ОТКРЫТЫМ, и щель вдоль RG-орбиты вообще ИСЧЕЗАЕТ (su2_gap_vanishes здесь же). Всё — SU(2) при beta=1. Ценность — унификация (gauge↔P4-онтология) и честное двойное чтение, не новая континуальная теорема. Шапка '~25 Qed' расходится с фактическими 12.

---

## #535 - `src/gauge/YangMillsSealed.v` - score 1 (exposition)

**SU(2) mass gap 'sealed' with formal OS1-3 surrogates at beta=1; concrete value 289/384**

- **Topic.** Restates the SU(2) lattice mass gap with FORMAL definitions of OS1-3 (is_lattice_analytic, is_tempered, is_SO4_invariant) plugged in, verified for the lattice correlators at beta=1, plus OS4 (reflection positivity), OS5 (cluster), the value matrix_mass_gap 1 1 0 == 289/384, and a constructed WightmanQFT.
- **Role.** Near-duplicate capstone of YangMillsCorrected restricted to beta=1 with the formal OS1-3 surrogates foregrounded. Imports CharacterTransfer, ExactMassGap, GapRatio, the Proof modules, Formal{Analytic,Tempered,SO4}, HilbertConstruction. Leaf; no downstream importer.
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: CauchyReal SeriesConvergence; gauge: CharacterTransfer ExactMassGap GapRatio TransferMatrixProof ReflectionPositiveProof ClusterProof CorrelationProof HilbertConstruction PhaseB_Synthesis FormalAnalytic FormalTempered FormalSO4
- **E/R/R.** _Elements:_ решёточные корреляторы full_correlation 1 t j 1 0; рациональная щель matrix_mass_gap 1 1 0 = 289/384; формальные предикаты is_lattice_analytic/is_tempered/is_SO4_invariant. _Roles:_ OS1-5 = роли-аксиомы реконструкции, теперь с ФОРМАЛЬНЫМИ (но слабыми) определениями; Wightman QFT = реконструированный объект; 'sealed' = роль-печать 'все определения формальны, нет True/Admitted'. _Rules:_ OS1 = отношение многочленов с denom>0; OS2 = ограниченность (темперированность); OS3 = зависимость только от \|x\|; OS4 = rp_inner_matrix>=0; OS5 = gap_ratio^N -> 0; всё при beta=1 ⟹ Вайтман существует. _P4:_ Element-сторона при ОДНОМ beta=1: каждое OS-условие — формально проверяемое решёточное свойство конкретных рациональных корреляторов. 'Sealed' заявляет отсутствие плейсхолдеров, но определения OS1-3 — СЛАБЫЕ суррогаты континуальных аксиом; континуальный OS->Wightman (role-limit) не строится. final_status честно отмечает прошлую замену пиннингового exists на реальное значение.
- **Classical counterpart.** Osterwalder-Schrader axioms OS1 (analyticity), OS2 (regularity/temperedness), OS3 (Euclidean SO(4) invariance) and the OS->Wightman reconstruction. WHAT DIFFERS: OS1-3 are replaced by FORMAL but WEAK lattice surrogates (is_lattice_analytic = ratio of polynomials with positive denominator; is_tempered = bounded; is_SO4_invariant = depends only on \|x\|) checked for SU(2) lattice correlators at beta=1. Not the continuum OS axioms; not the Clay theorem.
- **Tags.** gauge, yang-mills, mass-gap, lattice, su2, osterwalder-schrader, formal-surrogate, aggregator, over-branding, beta-1
- **Notes.** DRIFT: header '~15 Qed', actual Qed = 11 (all Theorem). 0 Admitted, 0 own axioms. Near-duplicate of YangMillsCorrected restricted to beta=1, with the difference being formal OS1-3 predicates (Formal*.v) foregrounded. Those predicates are weak lattice surrogates (is_SO4_invariant ~ 'function of |x|' is near-tautological). 10/11 lemmas are bare `exact`; final_status carries the only honest self-correction (replaced a pinned `exists gap, gap==289#384` tautology with the actual matrix_mass_gap value).

**Lemmas (11):**

| name | kind | role |
|---|---|---|
| `sealed_os1` | Theorem | OS1: корреляторы решёточно-аналитичны (is_lattice_analytic) для всех J,j,t_sep |
| `sealed_os2` | Theorem | OS2: корреляторы темперированы при beta=1, j∈{0,1} |
| `sealed_os3` | Theorem | OS3: корреляторы SO(4)-инвариантны (зависят лишь от \|x\|) |
| `sealed_os4` | Theorem | OS4: отражательная позитивность rp_inner_matrix>=0 при 0<=beta<=2 |
| `sealed_os5` | Theorem | OS5: кластер gap_ratio^N -> 0 (exists N, < eps) |
| `ym_lattice_os_bundle (ex yang_mills_SEALED)` | Theorem | ★ 'запечатанная' гранд-конъюнкция при beta=1: значение 289/384 + OS1-5 формальные + Вайтман |
| `os1_analytic_verified` | Theorem | OS1 повторно (verified-обёртка) при beta=1 |
| `os2_tempered_verified` | Theorem | OS2 повторно при beta=1 |
| `os3_invariant_verified` | Theorem | OS3 повторно при beta=1 |
| `final_status` | Theorem | ★ ЧЕСТНО: matrix_mass_gap 1 1 0 == 289#384 /\ >0 (комментарий: было пиннинговое exists, заменено реальным значением) |
| `ym_lattice_os_summary (ex sealed_summary)` | Theorem | сводка: OS1-5 формальные + Вайтман (общая по J,j,beta,M где применимо) |

**Key lemmas (deep):**

- **`ym_lattice_os_bundle (ex yang_mills_SEALED)`** - Капстоун-конъюнкция, отличающаяся от Complete/Corrected тем, что OS1-3 поданы через ФОРМАЛЬНЫЕ предикаты (is_lattice_analytic/is_tempered/is_SO4_invariant из Formal*.v), а не через ad hoc неравенства. Честная цена: эти определения — СЛАБЫЕ решёточные суррогаты континуальных OS-аксиом (аналитичность = отношение многочленов с denom>0; темперированность = ограниченность; SO(4) = функция от \|x\|). Всё фиксировано при beta=1. 'Sealed' = маркетинговая печать 'нет True/Admitted', но не печать решения проблемы Клэя: континуум отсутствует. _(aggregator, formal-surrogate, os-axioms, beta-1, over-branding)_
- **`final_status`** - Редкий честный комментарий в кластере: документирует, что прежняя версия была `exists gap, gap == 289#384 /\ 0 < gap` — ПИННИНГОВЫЙ экзистенциал о свежей переменной (тавтологичный), и заменена на содержательное утверждение о ФАКТИЧЕСКОЙ matrix_mass_gap 1 1 0. Микро-урок честности формализации: 'exists x, x = c' ничего не утверждает о системе; правильное содержание — значение и положительность реального объекта. Каталожно ценно как след самокоррекции over-claim. _(honesty, self-correction, pinned-existential)_
- **`sealed_os3`** - Показательный пример слабости суррогата: is_SO4_invariant сведён к 'корреляторы зависят только от расстояния \|x\|' (f(d1)=f(d2) когда d1=d2) — что для функции от единственного аргумента-сепарации ПОЧТИ тавтологично и заведомо слабее настоящей евклидовой SO(4)-ковариантности континуальной теории. Иллюстрирует, почему score низкий: 'формальные определения' закрывают букву OS3, но не его континуальную силу. _(so4, weak-surrogate, near-tautology)_

**Uniqueness - score 1 (exposition).** 'Запечатанная' витрина SU(2)-щели при beta=1: те же трансфер/RP/кластер/Вайтман факты, что и в Complete/Corrected, но с формальными предикатами OS1-3 (is_lattice_analytic/is_tempered/is_SO4_invariant) вместо ad hoc неравенств, плюс честная замена пиннингового экзистенциала на реальное значение 289/384.
> _Caveat:_ НЕ проблема Клэя. Формальные OS1-3 — СЛАБЫЕ решёточные суррогаты (аналитичность=отношение многочленов; темперированность=ограниченность; SO(4)=функция от |x|, почти тавтология), проверены лишь при beta=1 для SU(2); континуальный OS->Wightman не строится. 10/11 лемм — голые exact импортов; ценность только в final_status (честная самокоррекция). Имя ym_lattice_os_bundle (ex yang_mills_SEALED) аспирационно. Шапка '~15 Qed' расходится с фактическими 11.

---

## #536 - `src/gauge/YM3DComplete.v` - score 1 (exposition)

**SU(2) 3+1D mass-gap synthesis: temporal+spatial gap > 0, the dimension ladder**

- **Topic.** Aggregator that bundles the 3+1D SU(2) lattice results into named theorems: combined_gap > 0 at beta=1,2 for all spatial couplings, the gap decomposition gap = gap_M0 + t1*spatial_penalty, and a 1+1D->4+1D 'dimension ladder'. Every theorem is `exact <imported_lemma>` — no new content.
- **Role.** Re-export/synthesis layer over CombinedTransfer3D, ExactMassGap, SpatialHamiltonian, TridiagonalGap, ClebschGordan, YMWallBreach. Imported in turn by YMLevel4Complete (which re-bundles it upward). Pure plumbing on top of the real computation files.
- **Counts.** Qed 16 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: CauchyReal SeriesConvergence; ToS: stdlib.Combinatorics; gauge.SU2Characters CharacterTransfer ExactMassGap ClebschGordan SpatialHamiltonian CombinedTransfer3D TridiagonalGap ContinuumCharacter YMWallBreach; zeta.ZetaProcess zeta.ComplexZeta
- **E/R/R.** _Elements:_ конкретные рациональные щели combined_gap beta beta_s d_sp, gap_M0 beta на малой решётке; собственные значения t0_M0,t1_M0. _Roles:_ теоремы-обёртки = роль «витрина-фасад»: каждая делегирует exact импортированной лемме; статус-Prop ym_level3_status агрегирует их в один объект. _Rules:_ combined_gap = gap_M0 + t1_M0*spatial_penalty (правило разложения); лестница: d_sp=2,3,4 -> та же положительность через combined_gap_positive_1. _P4:_ Element-сторона: щель — вычисляемая рациональная величина на КОНЕЧНОЙ решётке при beta in {1,2}; континуум (a->0, все beta) НЕ здесь — это финитный срез, выдаваемый именем '3plus1D_complete' за полный 3+1D результат (P4: имя обещает больше, чем выводит файл).
- **Classical counterpart.** Зеркалит решёточную калибровочную теорию Вильсона для SU(2) в 3+1D: характерное (Peter-Weyl) разложение трансфер-матрицы, Клебш-Гордан для пространственных плакетов, щель = разность бесселевых собственных значений. ОТЛИЧИЕ: ничего нового против классики — файл лишь переименовывает импортированные конкретно-рациональные факты при beta in {1,2} в ERR-'лестницу размерностей'; континуумная теорема Янга-Миллса (Клэй) НЕ доказана.
- **Tags.** gauge, yang-mills, su2, mass-gap, lattice, 3plus1D, synthesis, re-export, over-branding, finite-lattice
- **Notes.** Заголовок STATUS заявляет ~30 Qed; фактически 16 Qed (drift). 17 деклараций (16 Theorem + 1 Definition ym_level3_status). 0 Admitted, 0 axioms. Все доказательства — exact/apply импортированных лемм; новых вычислений нет. Завершается Print Assumptions yang_mills_3plus1D_complete.

**Lemmas (17):**

| name | kind | role |
|---|---|---|
| `su2_mass_gap_3plus1D_beta1` | Theorem | при beta=1: combined_gap > 0 для всех beta_s>=0 (= combined_gap_positive_1) |
| `su2_mass_gap_3plus1D_beta2` | Theorem | при beta=2: combined_gap > 0 для всех beta_s>=0 (= combined_gap_positive_2) |
| `su2_mass_gap_3plus1D_nonneg` | Theorem | для beta in [0,2]: combined_gap >= 0 (= combined_gap_nonneg) |
| `su2_gap_decomposition` | Theorem | combined_gap == gap_M0 + t1_M0*spatial_penalty (= combined_gap_decomposition) |
| `su2_gap_lower_bound` | Theorem | gap_M0 <= combined_gap (пространство только усиливает щель; = spatial_enhances_gap) |
| `su2_gap_3d_positive` | Theorem | при d_sp=3, beta=1: gap_3plus1D > 0 (= gap_3plus1D_positive_1) |
| `ladder_1plus1D` | Theorem | уровень 0 (1+1D): gap_M0 >= 0 на [0,2] (= gap_M0_nonneg) |
| `ladder_1plus1D_positive` | Theorem | 0 < gap_M0 1 (= gap_at_beta_1_positive) |
| `ladder_2plus1D` | Theorem | уровень 1 (d_sp=2): combined_gap > 0 |
| `ladder_3plus1D` | Theorem | уровень 2 (d_sp=3): combined_gap > 0 |
| `ladder_4plus1D` | Theorem | уровень 3 (d_sp=4): combined_gap > 0 (та же лемма, иной d_sp) |
| `spatial_always_helps` | Theorem | на любой размерности gap_M0 <= combined_gap (= spatial_enhances_gap) |
| `wall_breach_holds` | Theorem | ym_wall_status выполнено (= ym_wall_broken из YMWallBreach) |
| `ym_level3_status` | Definition | Prop-агрегат: 1+1D nonneg + положительность beta=1,2 + 3+1D combined > 0 + пространство помогает |
| `ym_level3_achieved` | Theorem | ym_level3_status доказан (split на 6 импортированных лемм) |
| `three_millennium_level3` | Theorem | сводка трёх стен: YM level3 + ym_wall + ns_wall + rh_wall (импорты из YMWallBreach) |
| `yang_mills_3plus1D_complete` | Theorem | ★ капстоун-конъюнкция 'полного 3+1D' — на деле финитный срез beta in {1,2}, d_sp=3 |

**Key lemmas (deep):**

- **`su2_gap_decomposition`** - Единственная содержательная структура файла (и та импортирована): combined_gap == gap_M0 beta + t1_M0 beta * spatial_penalty beta_s d_sp 1 — щель = временная часть плюс пространственная добавка, помноженная на t1. Из неё немедленно следует spatial_enhances_gap (добавка >= 0). Доказательство — exact combined_gap_decomposition; реальная работа в CombinedTransfer3D.v. Классически это структура трансфер-матрицы 3+1D через Клебша-Гордана; ново лишь именование как ERR-разложения. _(decomposition, transfer-matrix, re-export)_
- **`yang_mills_3plus1D_complete`** - Капстоун с аспирационным именем '...complete'. Конъюнкция: gap_M0 nonneg на [0,2] И 0<gap_M0 1 И combined_gap>0 при d_sp=3 для beta in {1,2} И transfer_is_diagonal И wall_breach_structural. ЧЕСТНО: это НЕ полный 3+1D результат и НЕ континуум — каждая числовая часть привязана к beta in {1,2} на конечной решётке; 'complete' относится к сборке именованных кусков, не к решению задачи. Над-брендинг имени: содержание = финитный срез, выданный за завершённый 3+1D. _(capstone, over-branding, finite-lattice, conjunction)_

**Uniqueness - score 1 (exposition).** Чистая витрина-обёртка: именует и собирает 3+1D SU(2) результаты (combined_gap>0, разложение щели, лестница размерностей) в одну цепочку теорем.
> _Caveat:_ 0 нового содержания — каждая теорема есть `exact <импортированная лемма>`. Все числа привязаны к КОНЕЧНОЙ решётке при beta in {1,2}, SU(2) only; это НЕ континуумная теорема и НЕ решение Clay Millennium. Имя 'yang_mills_3plus1D_complete' над-брендировано. Заголовок: ~30 Qed против фактических 16.

---

## #537 - `src/gauge/YMLevel4Complete.v` - score 2 (methods)

**SU(2) continuum mass-gap synthesis: 10-step chain, RG-invariant mass, 5/7 Clay items**

- **Topic.** Aggregator bundling the 'Level 4' continuum-limit story into a 10-step chain (eigenvalues>0 -> lattice gap>0 -> ratio in (0,1) -> RG contraction r->r^2 -> physical mass (1-r)/a > 0 -> RG-approx-invariance -> positive at all scales -> RP -> cluster -> 3+1D), then maps 5 of 7 Clay requirements onto these. Every step is `exact <imported_lemma>`.
- **Role.** Re-export/synthesis over GapRatio, LatticeRG, ReflectionPositivity, ContinuumGap, plus YM3DComplete. Itself imported by YMLevel5Complete. Pure consolidation; no own computation.
- **Counts.** Qed 25 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: CauchyReal SeriesConvergence; ToS: stdlib.Combinatorics; gauge.SU2Characters CharacterTransfer ExactMassGap ClebschGordan CombinedTransfer3D GapRatio LatticeRG ReflectionPositivity ContinuumGap YM3DComplete
- **E/R/R.** _Elements:_ рациональные собственные значения t0_M0,t1_M0; gap_ratio beta; физическая масса physical_mass r a = (1-r)/a; шаг РГ rg_ratio_step. _Roles:_ 10 теорем-ступеней = роль «несущая лестница доказательства»; РГ-шаг = роль-преобразование масштаба; physical_energy/mass = наблюдаемая-результат. _Rules:_ РГ-сжатие r->r^2 (r<1 => r^2<r); масс-РГ-соотношение m' = (1+r)/2 * m; масса>0 на всех итерациях масштаба. _P4:_ Element-сторона: всё считается на решётке при beta in {1,2}; континуум выдаётся РГ-инвариантностью physical_mass, но это ПРИБЛИЖЁННАЯ (ограниченная) инвариантность при дискретных шагах удвоения a, НЕ настоящий предел a->0; имена 'continuum'/'Level4Complete' обещают предел, файл даёт финитную РГ-итерацию (P4: процесс масштабов выдан за достигнутый континуум).
- **Classical counterpart.** Зеркалит схему конструктивной QFT: решёточная щель -> отношение собственных значений из монотонности Бесселя -> РГ-поток -> предполагаемый континуумный предел с осями Остервальдера-Шрадера (RP, кластер) и реконструкцией Вайтмана. ОТЛИЧИЕ: классическая программа требует НАСТОЯЩЕГО предела a->0 со всеми сохранёнными аксиомами; здесь — финитная РГ-итерация при beta in {1,2}, ПРИБЛИЖЁННАЯ инвариантность массы, и OS1-3/Вайтман лишь свидетельствуются тривиальными Prop. Clay Millennium НЕ решён.
- **Tags.** gauge, yang-mills, su2, mass-gap, continuum, rg-flow, reflection-positivity, clay, synthesis, re-export, over-branding, stub-witness
- **Notes.** Заголовок STATUS заявляет ~30 Qed; фактически 25 Qed (drift). 25 деклараций (все Theorem). 0 Admitted, 0 axioms. step9/clay_cluster_property — тривиальные lra-заглушки; remaining_os1..3 и remaining_reconstruction свидетельствуются тривиальными Prop (реальные OS-аксиомы не формализованы здесь — это сделано в Level5). Завершается двумя Print Assumptions.

**Lemmas (25):**

| name | kind | role |
|---|---|---|
| `step1_eigenvalues_positive` | Theorem | 0<t0_M0 1 и 0<t0_M0 2 (положительность собственных значений) |
| `step2_lattice_gap_positive` | Theorem | 0<gap_M0 1 и 0<gap_M0 2 (решёточная щель) |
| `step3_gap_ratio_bounded` | Theorem | gap_ratio beta in (0,1) при beta=1,2 |
| `step4_rg_contraction` | Theorem | rg_ratio_step r < r при 0<r<1 (РГ сжимает; = rg_contraction) |
| `step5_physical_mass_positive` | Theorem | physical_mass(gap_ratio b) a > 0 для a>0 при b=1,2 |
| `step6_mass_rg_invariant` | Theorem | physical_mass(rg_step r)(2a) == (1+r)/2 * physical_mass r a (масс-РГ-соотношение) |
| `step7_mass_positive_all_scales` | Theorem | масса>0 при rg_iterate r n / lattice_spacing a n (на всех масштабах) |
| `step8_reflection_positivity` | Theorem | взвешенная сумма квадратов с t_j >= 0 (RP на решётке; rp_holds_beta_1) |
| `step9_cluster_property` | Theorem | 0<gap => 0<1-(1-gap) (тривиальная lra; кластерное свойство-заглушка) |
| `step10_spatial_enhancement` | Theorem | 3+1D: physical_mass(combined_ratio 1 beta_s 3) a > 0 при условии beta_s*3*(2/9)<1 |
| `yang_mills_continuum_mass_gap` | Theorem | ★ конъюнкция шагов 1-8 (главная 'континуумная' теорема — на деле РГ-итерация при beta in {1,2}) |
| `clay_3plus1D` | Theorem | Clay #1 (3+1 измерения): = continuum_mass_gap_3d (условно) |
| `clay_su2_gauge` | Theorem | Clay #2 (SU(2)): = step2_lattice_gap_positive |
| `clay_mass_gap_positive` | Theorem | Clay #3 (Delta>0): = mass_positive_beta_1 |
| `clay_reflection_positivity` | Theorem | Clay #4 (RP): = step8 |
| `clay_cluster_property` | Theorem | Clay #5 (кластер): тривиальная lra-заглушка 0<1-(1-gap_M0 beta) |
| `clay_continuum_limit` | Theorem | Clay #6 (континуум): = mass_positive_all_rg (РГ-итерация, не предел) |
| `millennium_comparison` | Theorem | сводка: 5 из 7 Clay-пунктов как конъюнкция |
| `remaining_os1` | Theorem | OS1 свидетельствуется тривиально: bessel_partial 0 1 0 == 1 (аналитичность лишь упомянута) |
| `remaining_os2` | Theorem | OS2 свидетельствуется тривиально: gap_ratio 1 < 1 (регулярность лишь упомянута) |
| `remaining_os3` | Theorem | OS3 свидетельствуется тривиально: transfer_is_diagonal (ковариантность лишь упомянута) |
| `remaining_reconstruction` | Theorem | OS->Wightman: свидетель 0<gap_M0 1,2 (реконструкция лишь процитирована, ~500 Qed не сделаны) |
| `ym_level4_status` | Theorem | статус: gap_ratio in (0,1) при beta=1,2 (= step3) |
| `ym_level4_achieved` | Theorem | = step2_lattice_gap_positive (с комментарием-сводкой ~1340 Qed) |
| `three_millennium_level4` | Theorem | сводка трёх стен на уровне 4 (YM gap + ns + rh куски) |

**Key lemmas (deep):**

- **`yang_mills_continuum_mass_gap`** - Главная теорема с именем 'continuum mass gap'. Восьмичленная конъюнкция шагов 1-8: собственные значения>0, решёточная щель>0, отношение в (0,1), РГ-сжатие r->r^2, физическая масса>0, масс-РГ-соотношение m'=(1+r)/2*m, масса>0 на всех масштабах, 3+1D масса>0. ЧЕСТНО: 'continuum' здесь означает РГ-инвариантность physical_mass=(1-r)/a при ДИСКРЕТНЫХ удвоениях a, доказанную при beta in {1,2}; настоящего предела a->0 нет, и step6 даёт лишь ПРИБЛИЖЁННУЮ инвариантность (множитель (1+r)/2, а не 1). Все доказательства — exact импортированных лемм. Это синтез-обёртка, не новый континуумный результат. _(capstone, continuum, rg-invariance, approximate, over-branding)_
- **`millennium_comparison`** - Сопоставление с призом Клэя: утверждает '5 из 7' выполненными. Но клеи-пункты делегируют решёточным фактам при beta in {1,2} (clay_su2_gauge = step2_lattice_gap_positive; clay_cluster_property — тривиальная lra 0<1-(1-gap)). OS1/OS2/OS3 в этом файле (remaining_os1..3) свидетельствуются ТРИВИАЛЬНЫМИ Prop (bessel=1, ratio<1, transfer diagonal) — реального аналитичность/регулярность/SO(4)-ковариантность не формализованы. Ценность пункта — честная самооценка ('5 из 7', Part IV 'What's Still Missing'), но имя 'millennium' над-брендировано относительно содержания. _(clay, millennium, self-assessment, stub-witness, over-branding)_

**Uniqueness - score 2 (methods).** Синтез-обёртка, оформляющая континуумную историю как явную 10-ступенчатую цепочку и честную карту '5 из 7 Clay' с разделом 'что ещё не сделано'.
> _Caveat:_ 0 нового содержания — все шаги `exact <импортированная лемма>`. 'Continuum' = ПРИБЛИЖЁННАЯ РГ-инвариантность при дискретных удвоениях a, НЕ предел a->0; OS1/OS2/OS3 свидетельствуются тривиальными Prop; реконструкция Вайтмана лишь процитирована. Решётка, beta in {1,2}, SU(2) only. НЕ решение Clay. Заголовок: ~30 Qed против фактических 25. Score 2 (а не 1) только за дисциплину явной ступенчатой структуры и честный Part IV.

---

## #538 - `src/gauge/YMLevel5Complete.v` - score 2 (methods)

**SU(2) lattice: all 5 OS axioms + Wightman reconstruction bundled; 7/7 Clay 'on the lattice'**

- **Topic.** Top aggregator of the Yang-Mills programme: re-exports OS1-OS5 and Wightman reconstruction (each from its own LatticeOS*/WightmanReconstruction file) and asserts all 7 Clay requirements 'on the lattice'. Notably also contains the project's MOST EXPLICIT self-honesty lemmas (honest_caveat, what_is_proved, what_is_structural) stating exactly what is lattice-only / structural / not continuum.
- **Role.** Apex re-export of the gauge cluster (imports LatticeOS1/2/3, LatticeCorrelations, WightmanReconstruction, YMLevel4Complete). End of the Level chain; nothing imports it. Pure consolidation + honest caveat block.
- **Counts.** Qed 14 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa; ToS: CauchyReal SeriesConvergence; gauge.CharacterTransfer ExactMassGap GapRatio ReflectionPositivity ContinuumGap LatticeCorrelations LatticeOS1_Analyticity LatticeOS2_Regularity LatticeOS3_Covariance WightmanReconstruction YMLevel4Complete
- **E/R/R.** _Elements:_ Prop-свидетели os1_analyticity, os2_regularity, os3_covariance, wightman_axioms_satisfied; physical_energy 1 beta; connected_two_point. _Roles:_ теоремы-обёртки = роль «фасад всех 7 требований Clay»; три honest_*-леммы = роль «совесть/оговорка», явно очерчивающая границу выведенного. _Rules:_ клеи-список 7/7 как конъюнкция; кластер: 0<gap_ratio<1 => 0<connected_two_point (экспоненциальный спад); масс-щель = physical_energy>0. _P4:_ Острейший P4-срез всего репозитория: honest_caveat ПРЯМО утверждает, что доказана РЕШЁТКА (дискретное пространство-время), а Clay просит КОНТИНУУМ; OS3 на решётке даёт лишь гиперкубическую (не SO(4)) ковариантность, полная SO(4) — только в a->0. P4-ход 'решётка при разрешении a ЕСТЬ физика' честно назван как расхождение со стандартом, а не замаскирован.
- **Classical counterpart.** Зеркалит аксиомы Остервальдера-Шрадера (OS1 аналитичность, OS2 регулярность, OS3 евклидова ковариантность, OS4 отражательная положительность, OS5 кластер) и теорему реконструкции OS->Wightman (1973). ОТЛИЧИЕ: классические OS-аксиомы — о КОНТИНУУМНЫХ евклидовых корреляторах со ВСЕЙ SO(4); здесь все пять — решёточные суррогаты при beta in {1,2} (OS3 = гиперкубическая симметрия, не SO(4); OS1/OS2 = решёточные Prop-свидетели), а реконструкция Вайтмана лишь постулирована свидетелем, не построена (~500 Qed признаны несделанными). Clay Millennium НЕ решён — что файл честно фиксирует.
- **Tags.** gauge, yang-mills, su2, mass-gap, os-axioms, wightman, clay, millennium, synthesis, re-export, honesty, anti-overclaim, over-branding, lattice-only
- **Notes.** Заголовок STATUS заявляет ~25 Qed; фактических ДОКАЗАТЕЛЬНЫХ Qed — 14 (по числу деклараций). Сырой Grep 'Qed\.' = 15, но 15-е совпадение — строка-комментарий '7,000+ Qed. 0 Admitted.' (строка 235), не терминатор доказательства. 0 Admitted (слово 'Admitted' встречается лишь в комментариях '0 Admitted'). 0 axioms. 14 деклараций, все Theorem. Ключевая ценность файла — НЕ теоремы, а блок honest_caveat/what_is_proved/what_is_structural.

**Lemmas (14):**

| name | kind | role |
|---|---|---|
| `clay_os1` | Theorem | OS1 аналитичность: = os1_on_lattice (свидетель os1_analyticity) |
| `clay_os2` | Theorem | OS2 регулярность: = os2_on_lattice |
| `clay_os3` | Theorem | OS3 ковариантность: = os3_on_lattice (гиперкубическая, не SO(4)) |
| `clay_os4` | Theorem | OS4 RP: = step8_reflection_positivity (взвешенная сумма квадратов >= 0) |
| `clay_os5` | Theorem | OS5 кластер: 0<connected_two_point при 0<gap_ratio<1 (= exponential_clustering) |
| `clay_wightman` | Theorem | Вайтман: = wightman_from_os (свидетель wightman_axioms_satisfied) |
| `clay_mass_gap` | Theorem | масс-щель: 0<physical_energy 1 1 и 0<physical_energy 1 2 |
| `clay_requirements_complete` | Theorem | ★ конъюнкция всех 7/7 требований Clay 'на решётке' |
| `honest_caveat` | Theorem | ★ ОГОВОРКА: доказана решётка, Clay просит континуум; OS3 гиперкубич., SO(4) лишь в a->0; свидетель os1/\os2/\os3 |
| `what_is_proved` | Theorem | ★ перечень РЕАЛЬНО доказанного (9 пунктов, без True); свидетель 0<physical_energy |
| `what_is_structural` | Theorem | ★ перечень СТРУКТУРНОГО/непокрытого (OS1-3->настоящие, реконструкция ~500 Qed); свидетель wightman |
| `ym_level5_status` | Theorem | статус: os1/\os2/\os3/\wightman (5 содержательных + 2 структурных) |
| `ym_level5_achieved` | Theorem | = 0<gap_M0 1,2 (с комментарием-сводкой ~1450 Qed) |
| `three_millennium_complete` | Theorem | ★ финальная сводка трёх стен: YM gap>0 + NS gap_ratio==47/336 + RH 0<gap_ratio<1 |

**Key lemmas (deep):**

- **`clay_requirements_complete`** - Венчающая конъюнкция: OS1/\OS2/\OS3/\OS4(RP)/\OS5(кластер)/\Вайтман/\(масс-щель>0) — 'все 7 требований Clay'. КРИТИЧЕСКИ ЧЕСТНО: os1_analyticity, os2_regularity, os3_covariance, wightman_axioms_satisfied — это Prop-свидетели, выведенные в файлах LatticeOS1/2/3 и WightmanReconstruction; на решётке OS3 — лишь ГИПЕРКУБИЧЕСКАЯ ковариантность, а 'аналитичность/регулярность' — решёточные суррогаты, не настоящие комплексно-аналитические/Шварц-распределительные свойства. Имя 'requirements_complete' над-брендировано; '7/7 на решётке' != решение Clay (континуум). Сам файл это признаёт в honest_caveat. _(capstone, clay, os-axioms, wightman, over-branding, lattice-only)_
- **`honest_caveat`** - Редкая и ценная лемма-совесть: в комментарии ПРЯМО формулирует расхождение — 'доказана РЕШЁТКА (дискретное пространство-время), Clay просит КОНТИНУУМ'; OS3 на решётке -> дискретная (гиперкубическая) ковариантность, полная SO(4) только в a->0; зазор между P4 ('решётка при разрешении a ЕСТЬ физика -> готово') и стандартом ('нужен предел a->0 со всеми аксиомами -> трудно'). Это и есть честный пол всей gauge-программы: парный с what_is_proved (9 реально доказанных пунктов) и what_is_structural (что лишь структурно). Само утверждение тривиально (os1/\os2/\os3), но КОММЕНТАРИЙ — главный анти-оверклейм репозитория в этом кластере. _(honesty, caveat, lattice-vs-continuum, P4, anti-overclaim)_
- **`three_millennium_complete`** - Финальная сводка-плакат трёх стен: YM (0<gap_M0 1,2) /\ NS (gap_ratio 1 == 47/336) /\ RH (0<gap_ratio 1<1). Имя 'three_millennium_complete' и комментарий-баннер ('7,000+ Qed, 3 Millennium Problems') — самое сильное над-брендирование: ни одна из трёх Millennium-задач не решена в стандартном смысле (YM — решётка; NS — условная регулярность; RH — лишь zero-free Re=1). Конъюнкция доказывает три скромных рациональных факта, а оформление подаёт их как 'complete'. Флаг честности обязателен. _(millennium, over-branding, poster, three-walls)_

**Uniqueness - score 2 (methods).** Апекс-обёртка всей gauge-программы (7/7 Clay 'на решётке' + OS1-5 + Вайтман) С ВСТРОЕННЫМ честным анти-оверклейм-блоком (honest_caveat / what_is_proved / what_is_structural), очерчивающим решётка-vs-континуум границу.
> _Caveat:_ 0 нового содержания — всё `exact <импортированная лемма>`; OS1/OS2/OS3 и Wightman — решёточные Prop-свидетели, не настоящие континуумные аксиомы; реконструкция Вайтмана не построена. Имена 'requirements_complete'/'three_millennium_complete' над-брендированы — Millennium-задачи НЕ решены. Score 2 (а не 1) исключительно за встроенные леммы-совесть, редкие в репо. Заголовок: ~25 Qed против фактических 14 (сырой grep 'Qed.' даёт 15 — лишний из комментария '7,000+ Qed.').

---

## #539 - `src/gauge/YMWallBreach.v` - score 2 (methods)

**Exact SU(2) gap via character expansion: gap=289/384 (beta=1), 1/24 (beta=2); 'wall breach' synthesis**

- **Topic.** Synthesis claiming the 'wall' (need true SU(2) Wilson action, not a U(1)-like approximation) is breached: character expansion gives exact diagonalization and gap = I0-2I2+I4 > 0, verified rationally at gap_M0 1 == 289/384 and gap_M0 2 == 1/24. Defines the cross-cluster ym/ns/rh_wall_status Props reused by YM3DComplete.
- **Role.** Foundational synthesis of the exact-SU(2) 1+1D thread; supplies ym_wall_status / ns_wall_status / rh_wall_status (the three-walls Props) reused by YM3DComplete and the Level chain. Imports the real compute files (ExactMassGap, CharacterTransfer, ContinuumCharacter, SU2Characters, zeta.*). All theorems delegate via exact.
- **Counts.** Qed 19 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith Lqa List; ToS: CauchyReal SeriesConvergence; ToS: stdlib.Combinatorics; gauge.SU2Characters CharacterTransfer ExactMassGap ContinuumCharacter; zeta.ZetaProcess zeta.ComplexZeta
- **E/R/R.** _Elements:_ конкретные рациональные щели simplified_gap=3/4, tensor_gap=1/18, domain_wall_gap=3/4; точные gap_M0 1==289/384, gap_M0 2==1/24; характеры su2_character. _Roles:_ the_wall/ym_wall_status/ns_wall_status/rh_wall_status = роль «статус-объект стены»; теоремы-обёртки = роль «свидетель пролома»; характеры = ортогональный базис (роль диагонализатора). _Rules:_ щель = t0_M0-t1_M0 = I0-2I2+I4 (бесселевы разности, Peter-Weyl); точное SU(2) (289/384) превосходит упрощённое (288/384=3/4) на 1/384. _P4:_ Element-сторона: 'пролом' = ВЫЧИСЛЕНИЕ точной рациональной щели при beta in {1,2} на конечной решётке; 'стена' (нужен истинный SU(2)) преодолена в ОДНОЙ точке параметра, не во всём континууме. Имена 'wall_breach'/'grand_total' выдают финитный численный факт за глобальный прорыв (P4: пролом локален по beta).
- **Classical counterpart.** Зеркалит характерное (Peter-Weyl) разложение решёточной калибровочной теории SU(2): характеры chi_j = U_{2j}(cos theta) диагонализуют трансфер-матрицу, собственные значения t_j = I_{2j}-I_{2j+2} (разности модифицированных Бесселя), щель = I0-2I2+I4. ОТЛИЧИЕ: классический результат качественный/асимптотический; здесь — ТОЧНОЕ рациональное значение щели (289/384 при beta=1, 1/24 при beta=2) на конечной решётке и ERR-нарратив 'стена/пролом'. Пролом реален как преодоление U(1)-приближения, но ЛОКАЛЕН по beta и решёточен — не континуумная теорема Янга-Миллса.
- **Tags.** gauge, yang-mills, su2, mass-gap, character-expansion, peter-weyl, exact-rational, wall-breach, three-walls, synthesis, re-export, over-branding, finite-lattice
- **Notes.** Заголовок STATUS заявляет ~30 Qed; фактически 19 Qed (drift). 26 деклараций (19 Theorem/Lemma с доказательством + 7 Definition: simplified_gap, tensor_gap, domain_wall_gap, the_wall, ym_wall_status, ns_wall_status, rh_wall_status). 0 Admitted, 0 axioms. Файл — корень exact-SU(2) синтеза: поставляет три статус-объекта стен, переиспользуемые выше. Завершается Print Assumptions grand_total.

**Lemmas (26):**

| name | kind | role |
|---|---|---|
| `simplified_gap` | Definition | щель упрощённой модели = 3/4 |
| `simplified_gap_positive` | Lemma | 0 < 3/4 (lra) |
| `tensor_gap` | Definition | тензорная щель = 1/18 |
| `tensor_gap_positive` | Lemma | 0 < 1/18 (lra) |
| `domain_wall_gap` | Definition | щель доменной стенки = 3/4 |
| `domain_wall_gap_positive` | Lemma | 0 < 3/4 (lra) |
| `the_wall` | Definition | Prop-стена: 0<tensor_gap /\ 0<domain_wall_gap |
| `wall_breach_gap` | Theorem | gap_M0 beta >= 0 на [0,2] (= gap_M0_nonneg) |
| `wall_breach_specific_1` | Theorem | ★ gap_M0 1 == 289/384 /\ 0<gap_M0 1 (точное SU(2) при beta=1) |
| `wall_breach_specific_2` | Theorem | ★ gap_M0 2 == 1/24 /\ 0<gap_M0 2 (точное SU(2) при beta=2) |
| `exact_beats_simplified_ratio` | Lemma | 289/384 > 288/384 (точное превосходит упрощённое на 1/384; lra) |
| `breach_diagonality` | Theorem | transfer_is_diagonal (структурно; Peter-Weyl) |
| `breach_eigenvalue_ordering` | Theorem | t1_M0 beta <= t0_M0 beta на [0,2] (= eigenvalue_ordering_0_1) |
| `breach_eigenvalues_nonneg` | Theorem | 0<=t0_M0 /\ 0<=t1_M0 на [0,2] |
| `breach_gap_computable` | Theorem | exists num den, gap_M0 beta = num#den (щель рациональна/вычислима) |
| `ym_wall_status` | Definition | Prop YM: диагональность /\ упорядочение /\ 0<gap_M0 1,2 /\ вычислимость |
| `ym_wall_broken` | Theorem | ★ ym_wall_status доказан (= 'стена YM сломана') |
| `ns_wall_status` | Definition | Prop NS: zeta_partial 2 K<=2 /\ процесс Коши (стена СТОИТ) |
| `ns_wall_standing` | Theorem | ns_wall_status доказан (NS-стена стоит) |
| `rh_wall_status` | Definition | Prop RH: 0<zeta_partial 2 K /\ процесс Коши (стена СТОИТ) |
| `rh_wall_standing` | Theorem | rh_wall_status доказан (RH-стена стоит) |
| `three_millennium_updated` | Theorem | ym(сломана) /\ ns(стоит) /\ rh(стоит) |
| `characters_provide_gap` | Theorem | характеры рациональны /\ ортогональны /\ моменты>=0 /\ диагональность /\ щель>=0 |
| `continuum_gap_persists` | Theorem | 0<physical_gap 1,2 /\ enhanced_gap>=0 /\ wall_breach_structural |
| `yang_mills_wall_breach` | Theorem | ★ ym_wall_status /\ wall_breach_structural /\ gap_M0>=0 ('стена сломана') |
| `grand_total` | Theorem | ★ 12-членная конъюнкция всего: характеры+диагональ+щель+физ.щель+три стены |

**Key lemmas (deep):**

- **`wall_breach_specific_1`** - Содержательное ядро 'пролома': gap_M0 1 == 289/384 — ТОЧНАЯ рациональная масс-щель точной SU(2)-модели (Вильсон, характерное разложение) при beta=1, плюс 0<gap_M0 1. Парная exact_beats_simplified_ratio показывает 289/384 > 288/384=3/4: точное SU(2) на 1/384 превосходит упрощённую доменно-стеночную модель. Это и есть 'пролом стены' (нужен истинный SU(2), не U(1)-приближение) — реальный, но ЛОКАЛЬНЫЙ: одна точка beta, конечная решётка. Доказательство exact gap_at_beta_1; вычисление — в ExactMassGap.v. Классически = Peter-Weyl диагонализация трансфер-матрицы; ново лишь рациональная точность 289/384 и ERR-обрамление 'стена/пролом'. _(exact-su2, rational-gap, 289/384, wall-breach, finite-beta)_
- **`grand_total`** - 12-членный капстоун-плакат: рациональность характеров, диагональность трансфера, упорядочение собственных значений, неотрицательность/положительность щели при beta in {1,2}, физическая щель>0, размерное усиление, и три millennium-статуса (ym сломана, ns/rh стоят). Имя 'grand_total' и баннер над-брендированы: конъюнкция собирает скромные рациональные факты при beta in {1,2}, не глобальный результат. Каждый конъюнкт — exact импортированной леммы. Ценно как индекс-сводка кластера, но 'grand total' != решение Янга-Миллса. _(capstone, grand-total, conjunction, over-branding, three-walls)_
- **`ym_wall_broken`** - Определяет и доказывает ym_wall_status: трансфер диагонален (Peter-Weyl) /\ t1<=t0 на [0,2] /\ 0<gap_M0 1,2 /\ щель всегда рациональна. Это переиспользуемый 'статус-объект' (наряду с ns_wall_status/rh_wall_status), который импортируют YM3DComplete и Level-цепочка как готовый кирпич трёх-стенных сводок. Содержательно — комбинация структурного факта (диагональность) и численных фактов при beta in {1,2}; имя 'broken' опять локально по beta. _(status-object, reused, peter-weyl, three-walls)_

**Uniqueness - score 2 (methods).** Синтез точной SU(2)-щели через характерное разложение с ТОЧНЫМИ рациональными значениями (289/384, 1/24) и переиспользуемыми статус-объектами трёх стен (ym/ns/rh_wall_status); 'пролом' = точное SU(2) превосходит упрощённую модель.
> _Caveat:_ 0 нового содержания — все теоремы `exact <импортированная лемма>` (вычисление в ExactMassGap/CharacterTransfer). 'Пролом стены' реален лишь как преодоление U(1)-приближения, но ЛОКАЛЕН: точные числа при beta in {1,2}, конечная решётка, SU(2) only — НЕ континуум и НЕ решение Clay. Имена 'wall_breach'/'grand_total'/'three_millennium' над-брендированы. Заголовок: ~30 Qed против фактических 19. Score 2 за конкретный рациональный результат (289/384) и переиспользуемые статус-Prop, не выше.

