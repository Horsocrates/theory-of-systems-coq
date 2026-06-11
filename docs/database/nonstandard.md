# Database - cluster `nonstandard`

_Generated from `nonstandard.json` by `generate.ps1` - do not edit by hand; edit the JSON._

**14 files / 130 Qed.** Score distribution: s5=0 / s4=3 / s3=10 / s2=1 / s1=0 / s0=0

---

## #1895 - `src/nonstandard/BoundaryIsInvertibility.v` - score 3 (new-framing)

**two atlases = one invertibility: matrix unit (det±1) ⟺ germ unit (eventually-nonzero), the Element side of the boundary**

- **Topic.** Closes the bridge between the reduction-atlas Element side (unimodular det±1, H73–H78) and the germ-ring units of A1 (UnitZeroDivisorBoundary): proves an integer 2×2 matrix is invertible ⟺ det=±1 (explicit adjugate inverse), and a constant germ gconst q (q≠0) is a germ-ring unit (inverse gconst(1/q)) — Element = units on both arenas.
- **Role.** nonstandard-analysis 'generating structure of the boundary' file, direction A2. Self-contained (ZArith/QArith/Lqa); cites A1 (UnitZeroDivisorBoundary), the reduction atlas (H73–78), and the Part-XVIII zero-divisor synthesis. Consolidation/bridge file.
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib: ZArith QArith Arith Lia Lqa
- **E/R/R.** _Elements:_ Mat2/det2/mul2/invertible2 (над ℤ); germ gconst/g_unit (над ℚ); анкеры fib_gen (det1), scale2 (det2). _Roles:_ det±1 = роль-единица-матрицы; обратимость = Element-маркер на ОБЕИХ сторонах; не-единица = role-limit-маркер (делитель нуля). _Rules:_ invertible2 M ⟺ det2 M=±1 (явный обратный adj/−adj); gconst q единица ⟺ q≠0; обе стороны Element = единицы кольца. _P4:_ конструктивно: det мультипликативна (ring); обратный матрицы выписан явно (adj при det=1, −adj при det=−1); germ-обратный явен (gconst(1/q)) ⟹ 0 аксиом, никакого classic. Граница = обратимость, на обеих сторонах. ★ Элемент-как-система: целочисл. матрица = 4 числа (Elements) / линейное преобразование (Roles) / обратима над ℤ ⟺ det=±1 (Rules).
- **Classical counterpart.** GL₂(ℤ) units ⟺ det=±1 (a matrix over a commutative ring is invertible iff its determinant is a unit), the adjugate formula M·adj(M)=det·I, and the units of a germ/Fréchet ring being the eventually-nonzero elements are all classical commutative-algebra facts. NEW is only the ToS re-packaging: identifying the Element side of the reduction atlas (det±1 unimodular core) and the germ-ring units (eventually-nonzero) as ONE notion — invertibility — so 'two atlases of the project' become two poles of one boundary.
- **Tags.** nonstandard, germ-ring, unit-zero-divisor, gl2-z, det-pm1, reduction-atlas, invertibility, boundary, vein-A
- **Notes.** STATUS header says '13 Qed' but actual Qed. count is 7 (drift). cluster derived from path src/nonstandard/ → 'nonstandard'. A2 direction file in the 'generating structure of the boundary' arc. 0 own axioms (fully constructive, no classic).

**Lemmas (27):**

| name | kind | role |
|---|---|---|
| `Mat2` | Record | целочисленная 2×2 матрица {m11 m12 m21 m22} |
| `det2` | Definition | детерминант m11·m22−m12·m21 |
| `mul2` | Definition | произведение матриц |
| `id2` | Definition | единичная матрица |
| `adj` | Definition | адъюгат (для det=1 обратной) |
| `negadj` | Definition | −адъюгат (для det=−1 обратной) |
| `invertible2` | Definition | обратимость над ℤ: exists N, M·N=N·M=I |
| `det_mult` | Lemma | det мультипликативна (ring) — ядро направления (⟹) |
| `mul2_M_adj` | Lemma | M·adj(M)=det·I |
| `mul2_adj_M` | Lemma | adj(M)·M=det·I |
| `mul2_M_negadj` | Lemma | M·negadj(M)=−det·I |
| `mul2_negadj_M` | Lemma | negadj(M)·M=−det·I |
| `Z_mul_one` | Lemma | целочисл. единицы: a·b=1 ⟹ a=±1 (через \|a\|·\|b\|=1, Nat.mul_eq_1) |
| `invertible_det_pm1` | Lemma | (⟹) обратима ⟹ det=±1 (det·det⁻¹=1 в ℤ) |
| `det_pm1_invertible` | Lemma | (⟸) det=±1 ⟹ обратима (явный обратный adj/−adj) |
| `det_pm1_iff_invertible` | Lemma | ★ ЕДИНИЦА целочисл. матрицы ⟺ det±1 |
| `fib_gen` | Definition | унимодулярный анкер (1 1;0 1), det 1 |
| `scale2` | Definition | анкер-масштаб (2 0;0 1), det 2 |
| `fib_gen_invertible` | Lemma | fib-генератор обратим (det 1) |
| `scale2_not_invertible` | Lemma | ★ масштаб det-2 НЕОБРАТИМ (не-единица) |
| `GProc` | Definition | germ-процесс nat→Q |
| `geq` | Definition | germ-равенство: в-конце совпадают |
| `gmul` | Definition | поточечное умножение germ'ов |
| `gconst` | Definition | константный germ |
| `g_unit` | Definition | germ-единица: exists y, gmul x y =germ= 1 |
| `gconst_unit` | Lemma | ★ мост к A1: gconst q (q≠0) — единица germ-кольца (обратный gconst(1/q)) |
| `two_atlases_one_invertibility` | Theorem | ★ капстоун: матрица обратима⟺det±1 ∧ fib обратим ∧ scale2 нет ∧ germ-единица — одна обратимость |

**Key lemmas (deep):**

- **`det_pm1_iff_invertible`** - Главный мост: целочисленная 2×2 матрица обратима ⟺ det=±1. (⟹) det мультипликативна (det_mult, ring) ⟹ det·det⁻¹=1 в ℤ ⟹ det=±1 (Z_mul_one через Nat.mul_eq_1). (⟸) явный целочисленный обратный — adj при det=1, −adj при det=−1 (адъюгат-тождества). Это classic-факт о GL₂(ℤ), здесь переказанный как «Element-сторона редукционного атласа = единицы SL₂(ℤ)±». Анкеры: fib-генератор обратим, scale2 (det 2) нет. _(gl2-z, det-pm1, unimodular, atlas, constructive)_
- **`gconst_unit`** - Мост к A1 (UnitZeroDivisorBoundary): константный germ gconst q при q≠0 есть ЕДИНИЦА germ-кольца с явным обратным gconst(1/q) (Qmult_inv_r от индекса 0). Это ставит обе арены — целочисленные матрицы det±1 И germ-процессы в-конце-ненулевые — под ОДНО понятие обратимости. role-limit = не-единицы (делители нуля, цитата к A1/синтезу XVIII). Содержательно тривиально, ценность — унификация двух «атласов» проекта. _(germ-ring, unit, bridge-A1, invertibility)_

**Uniqueness - score 3 (new-framing).** Element-сторона редукционного атласа (унимодулярный det±1) и единицы germ-кольца A1 (в-конце-ненулевые) сведены к ОДНОМУ понятию — обратимости: целочисл. матрица обратима ⟺ det=±1 (явный adj/−adj-обратный), константный germ единица ⟺ q≠0; «два атласа проекта = одна обратимость».
> _Caveat:_ Всё классично: GL₂(ℤ) единицы ⟺ det=±1, адъюгат-формула M·adj(M)=det·I, единицы germ/Фреше-кольца = в-конце-ненулевые. Ново лишь E/R/R-переказ + сведение двух атласов в одну ось. Связь со ВСЕМИ 5 движками атласа (H78) — ЦИТАТА; здесь unit-ядро + germ-мост. role-limit=делители — цитата к A1. Header заявляет 13 Qed — фактически 7.

---

## #1896 - `src/nonstandard/DerivativeViaInfinitesimal.v` - score 3 (new-framing)

**derivative as the shadow of a difference quotient: Berkeley dissolved (δ≠0 nowhere), polynomial f' stays Element (0 axioms)**

- **Topic.** Defines the derivative over processes as f'(x)=st((f(x+δ)−f(x))/δ) with δ=1/(n+1): proves exact difference-quotient identities (x²→2x+δ, x³→3x²+3xδ+δ², x→1, c→0) where δ≠0 makes division legal, then takes the shadow (st via δ→0 Archimedes) to get f'(x²)=2x, f'(x)=1, f'(c)=0 — with the limit rational, so polynomial differentiation stays inside the finitization boundary.
- **Role.** nonstandard-analysis file, climax of Part-XVIII Batch A. Self-contained (QArith/Lqa); replicates δ from GermInfinitesimal and converges from StandardPart (cited), uses QArith Archimedean. Application/capstone of the infinitesimal arc; the general smooth-process st-derivative is deferred to a future file (cited).
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Arith Lia Lqa
- **E/R/R.** _Elements:_ GProc=nat→Q; delta=1/(n+1); diffquot; f_sq/f_cube/f_id/f_const; converges (двусторонняя, lra). _Roles:_ δ = роль-приращение (∞-малое, ненулевое); diffquot = роль-наклон-секущей; st = роль-тень; f' = касательная. _Rules:_ δ≠0 на каждом шаге ⟹ деление законно (нет 0/0); diffquot = производная + остаток·δ (точное тождество); st отбрасывает остаток (δ→0) ⟹ f' точна; f' полинома = Element. _P4:_ ★ всё конечно-глубинно (Element); δ→0 = Архимед (процесс, не завершённая малость); предел 2x рационален ⟹ дифференцирование полинома НЕ выходит за границу финитизации (контраст с √2-процессами → role-limit). Призрак Беркли = δₙ: ненулев на шаге (делим), исчезает лишь в тени. ЧЕСТНО: для куба тождество доказано, st-шаг (тень 3xδ+δ²) опущен; x²/x/const доказаны полностью.
- **Classical counterpart.** The nonstandard-analysis definition of the derivative f'(x)=st((f(x+δ)−f(x))/δ) and its resolution of Berkeley's 'ghosts of departed quantities' are due to Robinson (1960s); the polynomial difference-quotient identities (x² → 2x+δ etc.) are elementary algebra. NEW is only the ToS re-grounding: δ as a concrete process 1/(n+1) (nowhere zero, vanishing only in the shadow st via Archimedes), and the boundary observation that a polynomial derivative converges INSIDE the Element side (rational limit) — contrast with √2-processes that converge to role-limit.
- **Tags.** nonstandard, infinitesimal, derivative, berkeley, standard-part, element-side, finitization-boundary, P4
- **Notes.** STATUS header says '12 Qed' but actual Qed. count is 6 (drift). cluster derived from path src/nonstandard/ → 'nonstandard'. Cube st-step honestly omitted (only exact identity dq_cube proved). 0 own axioms; δ→0 via standard QArith Archimedean.

**Lemmas (21):**

| name | kind | role |
|---|---|---|
| `GProc` | Definition | germ-процесс nat→Q (реплика GermInfinitesimal) |
| `Qsn` | Definition | inject_Z (S n) — знаменатель приращения |
| `Qsn_pos` | Lemma | 0<Qsn n |
| `delta` | Definition | бесконечно малое δ=1/(n+1) |
| `delta_pos` | Lemma | 0<δ n (положительно на шаге) |
| `delta_nonzero` | Lemma | ★ δ≠0 на КАЖДОМ шаге — деление на δ законно (нет 0/0) |
| `converges` | Definition | двусторонняя сходимость процесса к L (реплика StandardPart) |
| `delta_converges_0` | Lemma | ★ δ→0: для любого eps хвост 1/(n+1)<eps (Архимед) |
| `diffquot` | Definition | разностное отношение (f(x+δ)−f(x))/δ как процесс |
| `f_sq` | Definition | f(x)=x² |
| `f_cube` | Definition | f(x)=x³ |
| `f_id` | Definition | f(x)=x |
| `f_const` | Definition | f(x)=c |
| `dq_sq` | Lemma | ★ (x²) разностное отношение = 2x+δ ТОЧНО (field, δ≠0) |
| `dq_cube` | Lemma | ★ (x³) разностное отношение = 3x²+3xδ+δ² (точное тождество) |
| `dq_id` | Lemma | (x) разностное отношение = 1 |
| `dq_const` | Lemma | (c) разностное отношение = 0 |
| `deriv_sq` | Lemma | ★★ ФЛАГМАН: f(x)=x² ⟹ f'(x)=2x (тень от 2x+δ) |
| `deriv_id` | Lemma | f(x)=x ⟹ f'(x)=1 |
| `deriv_const` | Lemma | f(x)=c ⟹ f'(x)=0 |
| `derivative_summary` | Theorem | ★ капстоун: δ≠0 ∧ dq_sq ∧ f'(x²)=2x ∧ f'(x)=1 ∧ f'(c)=0 |

**Key lemmas (deep):**

- **`deriv_sq`** - Флагман: f(x)=x² ⟹ f'(x)=2x как ТЕНЬ (st) разностного отношения dq_sq=2x+δ. δ нигде не нуль (delta_nonzero — делили законно), значение 2x достигается лишь в тени, через δ→0 (delta_converges_0, Архимед). Это NSA-определение производной Робинсона, но над КОНКРЕТНЫМ процессом δ=1/(n+1), 0-аксиомно. Граница: 2x рационален (при рациональном x) ⟹ процесс 2x+δₙ сходится ВНУТРЬ Element-стороны — дифференцирование полинома не выходит за границу финитизации. _(derivative, shadow, nsa, element-side, flagship)_
- **`dq_cube`** - Разрешение парадокса Беркли в действии: для x³ доказано ТОЧНОЕ тождество (f(x+δ)−f(x))/δ=3x²+3xδ+δ² (field, опираясь на δ≠0) — никакого 0/0, ибо δ ненулев на каждом шаге. Честно помечено: полный st-шаг куба (тень от 3xδ+δ² = «ограниченное × бесконечно малое») здесь НЕ доказывается (потребовал бы Qabs-оценок) — опущено явно, не выдаётся за сделанное. Контраст с dq_sq/dq_id/dq_const, чьи converges доказаны полностью. _(berkeley, exact-identity, honest-gap, cube)_

**Uniqueness - score 3 (new-framing).** Производная над процессами как тень разностного отношения f'(x)=st((f(x+δ)−f(x))/δ) с конкретным δ=1/(n+1): парадокс Беркли растворён (δ≠0 на каждом шаге, исчезает лишь в тени), а наблюдение «производная полинома = Element» (рациональный предел) ставит дифференцирование внутрь границы финитизации.
> _Caveat:_ NSA-определение производной и растворение «призраков исчезнувших величин» — Робинсон (1960-е); полиномиальные тождества разностного отношения элементарны. Ново лишь ToS-обоснование (δ как конкретный процесс, граница Element/role-limit). Для x³ st-шаг ОПУЩЕН (честно), доказано лишь точное тождество; converges есть только для x²/x/const. Общая st-производная гладких процессов — будущий файл (цитата). Header заявляет 12 Qed — фактически 6.

---

## #1897 - `src/nonstandard/FinitizationBoundaryGeneratingStructure.v` - score 4 (synthesis+observation)

**Порождающая структура границы финитизации: одно семя negb, два полюса (единица=Element ⊕ делитель нуля=role-limit)**

- **Topic.** Великий синтез направления «порождающая структура границы»: граница финитизации = обратимость germ-кольца ℚ^ℕ/Фреше; ЕДИНИЦА (germ-константа) на Element-полюсе, ДЕЛИТЕЛЬ НУЛЯ (even_ind) на role-limit-полюсе; ОДНО семя negb (анти-неподвижная точка) порождает делитель И блокирует Element-тотализацию (Кантор/Рассел через Ловера); корень = P1.
- **Role.** КАПСТОУН-консолидация поднаправления E (порождающая структура границы): сводит genuine-результаты A1/A2/B1/B2/D в один файл + вердикт-карту полюсов. Импортирует только Stdlib (germ-кольцо и Ловер реплицированы локально); внешние H1/H71/H78/Core_ERR (P1) — цитаты в шапке, не импорты.
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Arith Lia Lqa
- **E/R/R.** _Elements:_ bool/negb; germ-процессы nat→ℚ (единица gconst(/q), делитель even_ind·odd_ind); point_surjective; перечисления Phenomenon/Pole. _Roles:_ negb = семя (анти-неподвижная точка); единица = Element-полюс; делитель нуля = role-limit-полюс; pole_of = роль-вердикт, относящая явление к полюсу. _Rules:_ negb b ≠ b (L5-семя); единица ⟺ в-конце-ненулева (обратимость, Element); делитель ⟺ нуль кофинально (role-limit); семя блокирует Element-тотализацию (нет сюръекции ℕ→2^ℕ; нет наивной компрегензии); только UnitPhen на Element-полюсе. _P4:_ конструктивно (0 акс): все представители выписаны явно (единица gconst(/q); делитель even_ind со свидетелем odd_ind; Ловер — явная диагональ; negb через destruct). Дальняя сторона границы = одно семя negb (тень P1-самочленства), преломлённое структурами; ближняя = единицы атласа.
- **Classical counterpart.** Теорема Ловера о неподвижной точке (Lawvere 1969) и её следствия — диагональ Кантора (несчётность 2^ℕ) и парадокс Рассела — классичны; германное кольцо ℚ^ℕ/Фреше с делителями нуля (фактор по неглавному фильтру) и обратимость как граница — стандартная алгебра. НОВО только обрамление: единица=Element-полюс ⊕ делитель=role-limit-полюс одной обратимости, и сведение Кантора/Рассела к ОДНОМУ семени negb как тени P1 ядра ToS (russell_paradox_blocked).
- **Tags.** nonstandard, frechet, germ-ring, lawvere, diagonal, negb-seed, zero-divisor, P1, synthesis, vein-E, two-poles
- **Notes.** Qed drift: STATUS-шапка указывает 12 Qed, фактический счёт 'Qed.' = 11. 0 Admitted, 0 собственных Axiom/Parameter. germ-кольцо и Ловер реплицированы локально (изоляция от stale .vo); H1/H71/H78/Core_ERR — цитаты в прозе, не импорты.

**Lemmas (24):**

| name | kind | role |
|---|---|---|
| `negb_no_fixpoint` | Lemma | ★ семя: negb b ≠ b — анти-неподвижная точка (= тень P1) |
| `GProc` | Definition | тип germ-процесса nat→ℚ |
| `geq` | Definition | germ-равенство по фильтру Фреше: совпадение при n≥N |
| `gmul` | Definition | поточечное умножение процессов |
| `gconst` | Definition | константный процесс |
| `g_unit` | Definition | обратимость germ: exists y, x·y ~ 1 |
| `cofinal_nz` | Definition | процесс ненулев кофинально (бесконечно часто) |
| `g_zero_divisor` | Definition | делитель нуля: есть кофинально-ненулевой y с x·y ~ 0 |
| `even_ind` | Definition | индикатор чётных (1 на чёт, 0 иначе) |
| `odd_ind` | Definition | индикатор нечётных |
| `gconst_unit` | Lemma | germ-константа q≠0 — единица (Element-полюс населён) |
| `one_is_unit` | Lemma | gconst 1 обратима |
| `odd_ind_cofinal_nz` | Lemma | odd_ind ненулев на нечётных кофинально |
| `even_odd_product_zero` | Lemma | even_ind·odd_ind = 0 поточечно (комплемент-дизъюнктность) |
| `even_ind_zero_divisor` | Lemma | ★ even_ind — делитель нуля (role-limit-полюс населён) |
| `point_surjective` | Definition | точечная сюръективность g: X→(X→B) |
| `lawvere` | Lemma | ★ теорема Ловера о неподвижной точке: point_surjective ⟹ всякая f:B→B имеет точку |
| `cantor` | Lemma | ★ Кантор: нет сюръекции ℕ→2^ℕ (из Ловера+negb) |
| `russell` | Lemma | ★ Рассел: нет наивной компрегензии (из Ловера+negb) |
| `Phenomenon` | Inductive | перечисление явлений: Unit/ZeroDiv/Cantor/Russell |
| `Pole` | Inductive | перечисление полюсов: Element/RoleLimit |
| `pole_of` | Definition | вердикт-карта: явление ↦ полюс |
| `only_unit_is_element` | Lemma | только UnitPhen на Element-полюсе; остальные — role-limit |
| `finitization_boundary_generating_structure` | Theorem | ★ КАПСТОУН: семя negb + единица + делитель + Кантор + Рассел + вердикт-карта в одной конъюнкции |

**Key lemmas (deep):**

- **`finitization_boundary_generating_structure`** - Гранд-капстоун поднаправления E: одна конъюнкция собирает (1) семя negb b≠b; (2) населённость Element-полюса (gconst 1 — единица); (3) населённость role-limit-полюса (even_ind — делитель нуля); (4) Кантор; (5) Рассел; (6) вердикт-карту полюсов. Тезис: дальняя сторона границы финитизации = ОДИН объект (семя negb = тень P1-самочленства), преломлённый алгеброй (делитель), счётом (несчётность), логикой (Рассел). Чистая консолидация — НЕ новая теорема; genuine-кирпичи лежат в A1/A2/B1/B2/D. _(capstone, synthesis, negb-seed, two-poles, vein-E)_
- **`lawvere`** - Извлечённый общий двигатель: point_surjective g ⟹ всякая f:B→B имеет неподвижную точку. Кантор и Рассел получаются как ДВА инстанса с f=negb (у которого точки нет — negb_no_fixpoint), а не передоказываются. Та же диагональ, что в cs/BoundaryDecidability (diagonal_defeats_decider) и cs/LawvereFixedPoint. Классика (Lawvere 1969); ново — её роль как ЕДИНОГО семени role-limit-полюса germ-кольца. _(lawvere, diagonal, engine, cantor, russell)_
- **`even_ind_zero_divisor`** - Конкретный обитатель role-limit-полюса: even_ind·odd_ind ~ 0, но odd_ind ненулев кофинально, значит even_ind — делитель нуля (germ-кольцо ℚ^ℕ/Фреше — НЕ поле). Машинный след отсутствующего ультрафильтра: U решил бы «чётные ИЛИ нечётные велики», сделав ровно один обратимым. Element-полюс (единица) контрастирует с role-limit-полюсом (делитель) на одной обратимости. Классика — делители нуля факторкольца по неглавному фильтру; ново — рамка Element/role-limit. _(zero-divisor, frechet, role-limit, not-a-field)_

**Uniqueness - score 4 (synthesis+observation).** Капстоун-унификация: одна граница (обратимость germ-кольца), два населённых полюса (единица=Element ⊕ делитель нуля=role-limit), одно семя negb, порождающее role-limit-полюс И блокирующее Element-тотализацию (Кантор/Рассел через Ловера), с машинной вердикт-картой полюсов.
> _Caveat:_ Каждый кирпич классичен (Ловер, Кантор, Рассел, делители нуля кольца Фреше). Это ЯВНО помечено как СИНТЕЗ/КОНСОЛИДАЦИЯ, НЕ новые теоремы — genuine-результаты в A1/A2/B1/B2/D, здесь они лишь сведены; «единое семя» эмпирично (germ-инстанс), не мета-теорема. STATUS-шапка пишет 12 Qed — фактически 11 (drift).

---

## #1898 - `src/nonstandard/GermInfinitesimal.v` - score 3 (new-framing)

**Бесконечно малое как ПРОЦЕСС: germ-кольцо ℚ^ℕ/Фреше, δ=1/(n+1) (Element-ядро NSA, без ультрафильтра)**

- **Topic.** Пилот Части XVIII: строит germ-кольцо процессов nat→ℚ по фильтру Фреше (конструктивен, в отличие от ультрафильтра). Бесконечно малое δ=1/(n+1) — НЕНУЛЕВО как germ, но ∞-мало как роль; ω=n+1 ∞-велико, ω·δ=1; ∞-малые образуют идеал. Делители нуля even·odd~0 = машинный след отсутствующего ультрафильтра.
- **Role.** Корневой Element-файл нестандартного анализа над процессами (традиция Шмиден–Лаугвиц 1958). Импортирует только Stdlib; служит якорем ElementCore в IllusoryConstructions и образующей в NonstandardOverProcessesSynthesis/HyperfiniteSum (δ, ∞-малость).
- **Counts.** Qed 19 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lqa ZArith Lia Arith
- **E/R/R.** _Elements:_ процессы nat→ℚ; δₙ=1/(n+1); ωₙ=n+1; индикаторы even_ind/odd_ind; константы gconst. _Roles:_ germ-класс (eventual-поведение); ∞-малое / конечное / ∞-большое = роли по поведению; δ — канон ∞-малого, ω=1/δ — канон ∞-большого; идеал ∞-малых. _Rules:_ x~y ⟺ xₙ=yₙ при n≥N (Фреше); кольцо поточечно конгруэнтно (gadd_geq/gmul_geq); δ ненулево (элемент) ∧ ∞-мало (роль); ω·δ=1; ∞-малые замкнуты по + и при умножении на конечное. _P4:_ ★ парадокс ∞-малого растворён: не завершённое число, а процесс — ненулевость есть факт об элементах, ∞-малость есть роль. ★★ делители нуля = след отсутствующего ультрафильтра (цена «кольцо, не поле» = LPO-зазор); поле *ℝ = role-limit. δ — полная E/R/R-система: правило-спуск n↦1/(n+1) + роль-∞-малость + рациональные элементы.
- **Classical counterpart.** Нестандартный анализ Робинсона строит *ℝ=ℚ^ℕ/U через неглавный ультрафильтр U (поле, полный перенос Лося). Конструктивный фактор по фильтру Фреше (germ-кольцо с делителями нуля) — это традиция Шмиден–Лаугвиц (1958) и smooth infinitesimal analysis. Архимедовость, идеал ∞-малых — стандартный QArith. НОВО: формализация над ПРОЦЕССАМИ nat→ℚ + расщепление ∞-малого на элемент/роль (растворение парадокса Беркли) + делители нуля как явный машинный СЛЕД отсутствующего ультрафильтра (= граница финитизации).
- **Tags.** nonstandard, infinitesimal, germ-ring, frechet, berkeley, zero-divisor, ultrafilter-trace, process, element-vs-role, schmieden-laugwitz
- **Notes.** Qed соответствует STATUS-шапке (19). 0 Admitted, 0 собственных Axiom/Parameter. Корневой пилот Части XVIII; все определения локальны (Stdlib only).

**Lemmas (32):**

| name | kind | role |
|---|---|---|
| `arch_nat` | Lemma | архимедовость: для любого B∈ℚ есть nat-мажоранта |
| `Qle_of_nat_le` | Lemma | монотонность инъекции ℕ→ℚ |
| `Qinv_lt_swap` | Lemma | реципрокное переворачивание неравенства /a<b → /b<a |
| `Qdiv_pos` | Lemma | деление положительных положительно |
| `GProc` | Definition | тип процесса nat→ℚ |
| `geq` | Definition | germ-равенство по фильтру Фреше |
| `gadd` | Definition | поточечное сложение |
| `gmul` | Definition | поточечное умножение |
| `gconst` | Definition | константный процесс |
| `geq_refl` | Lemma | рефлексивность germ-равенства |
| `geq_sym` | Lemma | симметричность |
| `geq_trans` | Lemma | транзитивность (через max N₁ N₂) |
| `gadd_geq` | Lemma | сложение конгруэнтно по germ-равенству |
| `gmul_geq` | Lemma | умножение конгруэнтно |
| `g_infinitesimal` | Definition | роль ∞-малого: < всякого ε eventually |
| `g_finite` | Definition | роль конечного: ограничено eventually |
| `g_infinite` | Definition | роль ∞-большого: > всякого B eventually |
| `Qsn` | Definition | инъекция S n → ℚ |
| `Qsn_pos` | Lemma | Qsn n > 0 |
| `Qsn_nonzero` | Lemma | Qsn n ≠ 0 |
| `delta` | Definition | канон ∞-малого δ=1/(n+1) |
| `omega` | Definition | канон ∞-большого ω=n+1 |
| `delta_nonzero` | Lemma | ★ δ ненулево как germ (факт об элементах) |
| `delta_infinitesimal` | Lemma | ★ δ бесконечно мало (роль) |
| `omega_infinite` | Lemma | ★ ω бесконечно велико |
| `omega_delta_one` | Lemma | ★ ω·δ=1 (обратные друг другу) |
| `even_ind` | Definition | индикатор чётных |
| `odd_ind` | Definition | индикатор нечётных |
| `zero_divisors_exist` | Lemma | ★★ even·odd~0, оба≠0 — делители нуля (след ультрафильтра) |
| `infinitesimal_add` | Lemma | сумма ∞-малых ∞-мала (идеал по +) |
| `finite_times_infinitesimal` | Lemma | конечное×∞-малое = ∞-малое (поглощение идеала) |
| `germ_ring_infinitesimal_summary` | Theorem | ★ КАПСТОУН: δ ∞-мало+ненулево, ω ∞-велико, ω·δ=1, делители нуля |

**Key lemmas (deep):**

- **`delta_infinitesimal`** - Сердце файла: δ=1/(n+1) меньше всякого стандартного ε при достаточно больших n (через arch_nat и Qinv_lt_swap). В паре с delta_nonzero реализует флагманский тезис: бесконечно малое — это ПРОЦЕСС, а не завершённое число. «Парадокс» Беркли (ненулевое, но меньше любого положительного) растворён расщеплением на два уровня E/R/R: ненулевость = факт об ЭЛЕМЕНТАХ (каждое δₙ∈ℚ≠0), ∞-малость = РОЛЬ (eventual-поведение). Конструктивно, 0 аксиом. Содержание классично (Шмиден–Лаугвиц); ново — onтологическая рамка процесса. _(infinitesimal, process, berkeley, element-vs-role)_
- **`zero_divisors_exist`** - ★★ Машинный след ОТСУТСТВУЮЩЕГО ультрафильтра: even_ind и odd_ind оба ненулевы как germ (1 бесконечно часто), но их произведение ~0. Значит ℚ^ℕ/Фреше — кольцо С ДЕЛИТЕЛЯМИ НУЛЯ, не поле. Это и есть честная цена конструктивности: ультрафильтр (role-limit, завершённый выбор на 2^ℕ) решил бы «чётные ИЛИ нечётные велики», сделав ровно один множитель обратимым — без него остаётся LPO-зазор. Тот же делитель появляется в FinitizationBoundaryGeneratingStructure (полюс) и обобщается в NonstandardOverProcessesSynthesis (форма ×). _(zero-divisor, ultrafilter-trace, LPO, not-a-field, frechet)_
- **`omega_delta_one`** - ω·δ=1 поточечно (Qmult_inv_r): ∞-большое и ∞-малое строго взаимно обратны как germ. Показывает, что δ обратимо (в отличие от even_ind), то есть конструктивная конечно-актуальная пара даёт законную единицу — Element-сторона обратимости germ-кольца. Тривиально по содержанию, но фиксирует, что не ВСЕ нестандартные элементы патологичны: патология (делитель) локализована в undecided-индикаторах. _(infinite, reciprocal, unit, element)_

**Uniqueness - score 3 (new-framing).** Element-ядро NSA как процессы: бесконечно малое δ — это ПРОЦЕСС (ненулевой элемент ∧ ∞-малая роль, парадокс Беркли растворён), а делители нуля germ-кольца Фреше — машинный след отсутствующего ультрафильтра (граница к полю *ℝ = role-limit).
> _Caveat:_ ПОЛЕ *ℝ, полный перенос Лося, насыщенность (всё, что требует ультрафильтра) — НЕ здесь и честно помечено как role-limit. Германное кольцо Фреше и его делители нуля классичны (Шмиден–Лаугвиц). Genuine-вклад — рамка процесса + расщепление элемент/роль, НЕ новая теорема анализа.

---

## #1899 - `src/nonstandard/HyperfiniteSum.v` - score 2 (methods)

**Интеграл как стандартная часть гиперконечной римановой суммы: ∫₀¹ x = 1/2 через тень ∞-малой сетки**

- **Topic.** Парный к производной (DerivativeViaInfinitesimal) файл: ∫₀¹f = st(Σₖ f(kδ)·δ) с δ=1/n. Доказывает ЗАКРЫТУЮ форму термwise римановой суммы (rsumlin = Qof(Σk)·h² через сумму Гаусса 2Σk=n(n−1)) и флагман ∫₀¹ x = 1/2 точно (риманова сумма (n−1)/(2n) → 1/2 по Архимеду).
- **Role.** Половина «исчисление = одна операция st» Части XVIII (вторая — производная). Импортирует только Stdlib; δ/converges/Архимед заимствованы по образцу DerivativeViaInfinitesimal (цитата в шапке), общий ∫ — арена RiemannIntegration (цитата). Цитируется в NonstandardOverProcessesSynthesis.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith ZArith Arith Lia Lqa
- **E/R/R.** _Elements:_ GProc; rsumlin (термwise рим. сумма); sumk (Гаусс Σk над ℕ); Qof (ℕ→ℚ); delta; integral_x; converges. _Roles:_ δ = роль-сетка (∞-малая); rsumlin = роль-аппроксимация площади; st (предел) = роль-тень/интеграл; sumk = Гаусс-счётчик. _Rules:_ δ≠0 на каждом шаге ⟹ сумма законна; rsumlin = Qof(Σk)·h² (точно, не подставленная формула); 2·Σk=n(n−1) (Гаусс индукцией над ℕ); st убирает остаток 1/(2n) ⟹ ∫x=1/2. _P4:_ всё конечно-глубинно (Element): частичная сумма R(n)=(n−1)/(2n) рациональна, сетка δ нигде не нуль; тень 1/2 НЕ член последовательности (R(n)<1/2 всегда), но РАЦИОНАЛЬНА ⟹ сходимость ВНУТРЬ Element-стороны — интегрирование полинома не выходит за границу финитизации (парно к дифференцированию). δ→0 = Архимед.
- **Classical counterpart.** Интеграл как стандартная часть гиперконечной римановой суммы — стандартный приём нестандартного анализа (Robinson; Keisler «Elementary Calculus»). ∫₀¹ x = 1/2 и сумма Гаусса Σk=n(n−1)/2 элементарны. НОВО только: формализация над ПРОЦЕССАМИ nat→ℚ без ультрафильтра (st = обычный предел/Архимед), доказанная закрытая форма реальной термwise суммы (не подстановка), и наблюдение «обе половины анализа = одна операция st» + рациональность предела как Element-граница. ⚠ ∫x²=1/3 (Σk²) и общий ∫ — цитаты, не доказаны здесь.
- **Tags.** nonstandard, integral, standard-part, riemann-sum, gauss-sum, infinitesimal, process, calculus, element-side, finitization-boundary
- **Notes.** Qed соответствует STATUS-шапке (10). 0 Admitted, 0 собственных Axiom/Parameter. δ/converges/Архимед — по образцу DerivativeViaInfinitesimal (парный файл, цитата); общий ∫ — RiemannIntegration (цитата).

**Lemmas (17):**

| name | kind | role |
|---|---|---|
| `GProc` | Definition | тип процесса nat→ℚ |
| `Qof` | Definition | инъекция ℕ→ℚ |
| `Qof_add` | Lemma | аддитивность Qof |
| `Qof_S` | Lemma | Qof(S m)=Qof m+1 |
| `Qof_pos` | Lemma | Qof(S m)>0 |
| `sumk` | Fixpoint | сумма Гаусса Σ_{j<n} j над ℕ |
| `sumk_closed_Q` | Lemma | ★ Гаусс в ℚ: 2·Qof(Σk)=Qof n·(Qof n−1) |
| `rsumlin` | Fixpoint | термwise левая риманова сумма для f(x)=x |
| `rsumlin_closed` | Lemma | ★ закрытая форма: rsumlin = Qof(Σk)·h² (настоящая сумма) |
| `integral_x` | Definition | интеграл-кандидат: рим. сумма n точек, сетка 1/n |
| `integral_x_closed` | Lemma | ★ явный вид: ∫-сумма(S m)=1/2−(1/2)/n |
| `converges` | Definition | ε-N сходимость процесса к L |
| `delta` | Definition | ∞-малая сетка δ=1/(n+1) |
| `delta_pos` | Lemma | δ>0 на каждом шаге |
| `delta_converges_0` | Lemma | δ→0 (Архимед) |
| `integral_x_converges` | Lemma | ★ ФЛАГМАН: ∫₀¹ x = 1/2 через тень |
| `hyperfinite_sum_summary` | Theorem | ★ КАПСТОУН: закрытая форма + явный вид + ∫x=1/2 |

**Key lemmas (deep):**

- **`integral_x_converges`** - ★ ФЛАГМАН (genuine-вычисление): ∫₀¹ x = 1/2 получается как тень (предел) римановой суммы (n−1)/(2n), без ε-δ-определения интеграла — через st ∞-малой сетки. Левая сумма с n точками законна (δ=1/n нигде не нуль), а 1/2 достигается лишь в тени (R(n)<1/2 всегда). Это конкретная реализация «интегрирование = операция st», парная к производной st(Δf/δ). Содержание (∫x=1/2) тривиально классично; ценность — что обе половины анализа суть одна теневая операция над ∞-малой δ. _(integral, standard-part, flagship, riemann-sum)_
- **`rsumlin_closed`** - Честный фундамент флагмана: rsumlin — НАСТОЯЩАЯ термwise рекурсивная сумма Σ(k·h)·h, и доказано (индукцией + сумма Гаусса), что она РАВНА закрытой форме Qof(Σk)·h², а не подставленной формуле. Это отличает файл от «вписать ответ»: суммирование выполнено реально, замкнутая форма выведена. sumk_closed_Q (2Σk=n(n−1)) доказана над ℕ без ℕ-вычитания. _(closed-form, gauss-sum, honest, induction)_
- **`integral_x_closed`** - Мост от закрытой формы к сходимости: ∫-сумма для n=S m точно равна 1/2 − (1/2)/n. Делает остаток 1/(2n) явным и рациональным, откуда сходимость к 1/2 — прямое следствие δ→0 (Архимед). Граница финитизации: предел 1/2 РАЦИОНАЛЕН, значит риманов процесс сходится ВНУТРЬ Element-стороны — интеграл полинома не порождает role-limit (в отличие, скажем, от ∫ с иррациональным пределом). _(explicit-form, rational-limit, element-side, finitization-boundary)_

**Uniqueness - score 2 (methods).** Гиперконечное интегрирование над процессами: ∫₀¹ x = 1/2 как тень st настоящей термwise римановой суммы (закрытая форма Qof(Σk)·h² доказана, не подставлена), парное к производной — обе половины анализа суть одна операция st над ∞-малой сеткой.
> _Caveat:_ Содержание классично (NSA-интеграл, ∫x=1/2, сумма Гаусса). Доказан ТОЛЬКО линейный флагман: ∫x²=1/3 (квадратичная Σk²) и общий ∫ гладкой функции явно НЕ доказаны — честно помечены как цитаты (RiemannIntegration). Новизна — необычная 0-аксиомная формализация над ℚ-процессами, не теорема.

---

## #1900 - `src/nonstandard/IllusoryConstructions.v` - score 3 (new-framing)

**Честный вердикт-реестр «за-границей» конструкций: {Element-ядро / role-limit-инструмент / ИЛЛЮЗОРНОЕ}; якорь Банах–Тарши**

- **Topic.** Сердце честной миссии Части XVIII: перечисляет 9 «за-границей» конструкций и присваивает каждой трёхзначный онтологический вердикт. Illusory = нужен AC ∧ нет Element-свидетеля ∧ даже не устранимые леса (чистый ZFC-фантом: Банах–Тарши/Витали/Гамель/полный порядок ℝ). Якорная теорема: удвоение шара несовместимо с ненулевой Element-мерой (μ=2μ⟹μ=0).
- **Role.** Онтологический классификатор-реестр направления. Импортирует только Stdlib; вердикты подкреплены ссылками-цитатами на якорные файлы (UltrafilterRoleLimit для FreeUltrafilter; GermInfinitesimal/StandardPart/Derivative для ElementCore), сами якоря не импортируются. Капстоун честности перед синтезом.
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lqa
- **E/R/R.** _Elements:_ перечисление Construction (9 конструкций); булевы предикаты needs_AC/has_element_witness/is_conservative_scaffold; Q-мера (Банах–Тарши). _Roles:_ конструкция = роль-кандидат; вердикт (ElementCore/RoleLimitTool/Illusory) = роль-статус; диагностики needs_AC/witness/scaffold = роли; мера = роль-сохранение (Element). _Rules:_ трёхзначный вердикт; Illusory = AC ∧ ¬witness ∧ ¬scaffold (фантом); RoleLimitTool = scaffold ∧ AC (консервативно устранимо, Хенсон–Кейслер); ElementCore = ¬AC ∧ witness; Банах–Тарши: μ=p1+p2 ∧ p1=μ ∧ p2=μ ⟹ μ=0. _P4:_ ElementCore = 0 AC, актуализуемо (есть Coq-свидетель-процесс); RoleLimitTool = AC-леса, но продукт консервативен ⟹ устраним (не фантом); Illusory = AC-фантом без референта/вычислимого содержания, ничего Element не доставляет. Ключевое различение Illusory vs RoleLimitTool: леса УСТРАНИМЫ и что-то ДОСТАВЛЯЮТ через консервативность, фантом не доставляет ничего. «Куски» Банах–Тарши = ровно то, что P4 не актуализирует.
- **Classical counterpart.** Парадокс Банах–Тарши (1924), множество Витали, базис Гамеля, теорема Цермело о полном порядке ℝ — классические следствия аксиомы выбора; консервативность нестандартного расширения (свободный ультрафильтр, *ℝ) — Хенсон–Кейслер. НОВО: не математический результат, а ОНТОЛОГИЧЕСКИЙ трёхзначный реестр {ElementCore/RoleLimitTool/Illusory} с машинной сигнатурой фантома (AC∧¬witness∧¬scaffold) + якорная теорема μ=2μ⟹μ=0, дающая ПРИЧИНУ иллюзорности БТ (несовместимость с Element-мерой). AC-зависимости Витали/Гамеля/полного порядка цитируются, не передоказываются.
- **Tags.** nonstandard, banach-tarski, axiom-of-choice, no-AC, measure, ontology, classification, verdict-registry, illusory, conservativity, honesty
- **Notes.** Qed drift: STATUS-шапка указывает 8 Qed, фактический счёт 'Qed.' = 7. 0 Admitted, 0 собственных Axiom/Parameter. Никакая иллюзорная конструкция не ассертируется (существование БТ-разбиения не постулируется); якоря-файлы цитируются в прозе, не импортируются.

**Lemmas (13):**

| name | kind | role |
|---|---|---|
| `Construction` | Inductive | перечисление 9 «за-границей» конструкций (БТ, Витали, Гамель, полный порядок ℝ, ультрафильтр, *ℝ-поле, germ-δ, тень, f' полинома) |
| `Verdict` | Inductive | трёхзначный статус: ElementCore/RoleLimitTool/Illusory |
| `verdict` | Definition | карта конструкция ↦ вердикт |
| `needs_AC` | Definition | диагностика: требует ли AC |
| `has_element_witness` | Definition | диагностика: есть ли Coq-свидетель |
| `is_conservative_scaffold` | Definition | диагностика: устранимые консервативные леса |
| `illusory_hallmark` | Lemma | ★ сигнатура фантома: Illusory ⟹ AC ∧ ¬witness ∧ ¬scaffold |
| `element_core_props` | Lemma | ElementCore ⟹ ¬AC ∧ witness |
| `role_limit_scaffold` | Lemma | RoleLimitTool ⟹ scaffold ∧ AC |
| `verdict_total` | Lemma | классификация тотальна (каждая — в одном из трёх классов) |
| `element_not_illusory` | Lemma | классы взаимоисключающи (Element-ядро ≠ Illusory) |
| `banach_tarski_contradicts_measure` | Lemma | ★ ЯКОРНЫЙ ФЛАГМАН: μ=2μ⟹μ=0 (БТ несовместим с Element-мерой) |
| `illusory_constructions_summary` | Theorem | ★ КАПСТОУН: сигнатуры трёх классов + БТ + три якоря вердиктов |

**Key lemmas (deep):**

- **`banach_tarski_contradicts_measure`** - ★ ЯКОРНЫЙ ФЛАГМАН (genuine-теорема, не классификация): если конечно-аддитивная движение-инвариантная Element-мера μ удовлетворяла бы заявлению Банах–Тарши (μ=p1+p2, каждая группа кусков собирается в целое: p1=μ, p2=μ), то μ=μ+μ ⟹ μ=0. Значит ненулевой Element-меры на кусках НЕ существует — куски неизмеримы, у них НЕТ Element-референта. Это машинное ПОЧЕМУ иллюзорности БТ: он несовместим с сохранением, которое несёт Element-мера. Сам парадокс (существование разбиения) НЕ ассертируется — лишь его несовместимость. Тривиальная lra-арифметика, но онтологически нагруженная. _(banach-tarski, measure, flagship, no-AC, anchor)_
- **`illusory_hallmark`** - Машинная сигнатура ИЛЛЮЗОРНОГО: всякая Illusory-конструкция одновременно требует AC, не имеет Coq-свидетеля И не является устранимыми лесами. Это и есть формальная граница «фантом vs инструмент»: RoleLimitTool (свободный ультрафильтр, *ℝ-поле) — устранимые консервативные леса (что-то Element ДОСТАВЛЯЮТ через Хенсон–Кейслер), тогда как Illusory (БТ/Витали/Гамель/полный порядок ℝ) не доставляет ничего. Различение — genuine онтологический вклад ToS; сами AC-зависимости классичны и цитируются, не передоказываются. _(illusory, classification, AC, conservativity, ontology)_
- **`verdict_total`** - Тотальность классификации: каждая из 9 конструкций попадает ровно в один класс (доказано destruct-перебором). В паре с element_not_illusory (взаимоисключаемость) даёт корректность трёхзначного реестра. Это плумбинг честной миссии: гарантирует, что вердикт-карта не оставляет «серых зон». Содержательно тривиально (конечный перебор), но нужно для целостности реестра. _(totality, classification, well-formed)_

**Uniqueness - score 3 (new-framing).** Онтологический трёхзначный вердикт-реестр конструкций {Element-ядро / устранимые role-limit-леса / ИЛЛЮЗОРНЫЙ ZFC-фантом} с машинной сигнатурой фантома и якорной теоремой Банах–Тарши (μ=2μ⟹μ=0), дающей причину иллюзорности через несовместимость с Element-мерой.
> _Caveat:_ Это РЕЕСТР/КЛАССИФИКАЦИЯ (синтез), НЕ новые теоремы — КРОМЕ одной якорной (БТ μ=2μ⟹μ=0, сама по себе элементарная lra-арифметика). Вердикты Витали/Гамель/полный-порядок лишь ЦИТИРУЮТ классическую AC-зависимость; различение Illusory/RoleLimitTool опирается на консервативность (Хенсон–Кейслер), не доказанную здесь. STATUS-шапка пишет 8 Qed — фактически 7 (drift).

---

## #1901 - `src/nonstandard/NonstandardOverProcessesSynthesis.v` - score 4 (synthesis+observation)

**Капстоун Части XVIII: одно свойство undecided S порождает ТРИ алгебраические формы role-limit-зазора (делитель × / осциллятор + / необратимость кольцо)**

- **Topic.** Финальный синтез нестандартного направления над процессами: извлекает ЕДИНЫЙ корень всех role-limit-явлений — неразрешённость Фреше «какое подмножество велико» (undecided S = S и not-S оба кофинальны, ПОЗИТИВНО, без classic). Доказывает, что одно это свойство влечёт делитель нуля (×), осциллятор-без-тени (+) и необратимость (кольцо). Evens — лишь частный undecided.
- **Role.** КАПСТОУН-унификация Части XVIII: абстрагирует Evens-результаты (UltrafilterRoleLimit/StandardPart) к общему undecided S. Импортирует только Stdlib (germ-операции реплицированы); исчисление=st (Derivative/HyperfiniteSum) и трёхзначный вердикт (IllusoryConstructions) — цитаты в шапке, не импорты.
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Arith Lia Lqa
- **E/R/R.** _Elements:_ GProc; cofinal/undecided (позитивные, конструктивные); ind/osc; evens; geq/gmul/gconst; g_invertible. _Roles:_ undecided = роль-неразрешённое-различение (Фреше не решает «что велико»); ind = индикатор; osc = осциллятор ±1; делитель/тень/единица = три проявления зазора. _Rules:_ undecided S = cofinal S ∧ cofinal not-S (позитивно); undecided S ⟹ (×) ind S·ind not-S~0 при обоих ≠0 — делитель; (+) osc S без константной тени — осциллятор; (кольцо) ind S необратим. Один корень — три формы. _P4:_ ★ конструктивно (важно): undecided определён ПОЗИТИВНО (оба кофинальны), НЕ через двойное отрицание (~cofinite потребовало бы classic/DNE) — поэтому все три формы выводятся БЕЗ аксиомы classic, чистая Element-сторона. Единственный role-limit — РАЗРЕШЕНИЕ undecided (ультрафильтр), которое НЕ ассертируется. undecided S — полная E/R/R-система: ни одно конечное наблюдение не решает «что велико» ⟹ корень всех трёх форм.
- **Classical counterpart.** Делители нуля и необратимые элементы факторкольца ℚ^ℕ по неглавному фильтру Фреше, и отсутствие предела у осциллирующей (±1)-последовательности — классическая алгебра/анализ; неразрешимость «какое подмножество велико» без ультрафильтра — суть конструктивного провала (LPO/role-limit). НОВО: УНИФИКАЦИЯ — доказательство, что ОДНО позитивно-конструктивное свойство (undecided S) порождает все ТРИ алгебраические формы (×/+/кольцо) одного зазора, с абстрагированием от частного Evens к общему S, БЕЗ аксиомы classic.
- **Tags.** nonstandard, synthesis, capstone, frechet, zero-divisor, oscillator, non-unit, undecided, constructive, no-classic, one-root-three-forms, vein-E
- **Notes.** Qed drift: STATUS-шапка указывает 10 Qed, фактический счёт 'Qed.' = 11. 0 Admitted, 0 собственных Axiom/Parameter. germ-операции реплицированы локально (Stdlib only); Derivative/HyperfiniteSum/IllusoryConstructions — цитаты в шапке, не импорты.

**Lemmas (21):**

| name | kind | role |
|---|---|---|
| `GProc` | Definition | тип процесса nat→ℚ |
| `geq` | Definition | germ-равенство по фильтру Фреше |
| `gmul` | Definition | поточечное умножение |
| `gconst` | Definition | константный процесс |
| `g_invertible` | Definition | обратимость germ: exists y, x·y~1 |
| `cofinal` | Definition | S истинно бесконечно часто (позитивно, конструктивно) |
| `undecided` | Definition | ★ неразрешённое различение: cofinal S ∧ cofinal not-S |
| `ind` | Definition | индикатор подмножества (1/0) |
| `osc` | Definition | осциллятор (+1 / −1) |
| `evens` | Definition | каноническое подмножество чётных |
| `cofinal_evens` | Lemma | чётные кофинальны |
| `cofinal_odds` | Lemma | нечётные кофинальны |
| `undecided_evens` | Lemma | evens — каноническое неразрешённое различение |
| `ind_complement_product_zero` | Lemma | ind S·ind not-S=0 поточечно |
| `ind_not_zero` | Lemma | cofinal S ⟹ ind S ≁ 0 |
| `undecided_zero_divisor` | Theorem | ★ форма ×: undecided ⟹ делитель нуля (произведение~0, оба множителя≠0) |
| `osc_true` | Lemma | osc S n = 1 при S n=true |
| `osc_false` | Lemma | osc S n = −1 при S n=false |
| `undecided_no_shadow` | Theorem | ★ форма +: undecided ⟹ осциллятор без константной тени |
| `undecided_non_unit` | Theorem | ★ форма кольцо: undecided ⟹ ind S необратим |
| `nonstandard_synthesis` | Theorem | ★ КАПСТОУН: один корень undecided ⟹ три формы (×/+/кольцо) |

**Key lemmas (deep):**

- **`nonstandard_synthesis`** - ★ ГРАНД-КАПСТОУН Части XVIII (genuine унифицирующая теорема): одна конъюнкция показывает, что ОДНО структурное свойство undecided S (и S, и not-S кофинальны — Фреше не различает «что велико») порождает ТРИ алгебраические формы role-limit-зазора: делитель нуля (мультипликативно), осциллятор-без-тени (аддитивно), необратимость (кольцо). Evens — лишь частный undecided. Это абстрагирование частных Evens-результатов (UltrafilterRoleLimit, StandardPart) к общему корню — настоящая унификация, не повтор. Спина капстоуна направления. _(capstone, synthesis, unification, one-root-three-forms, vein-E)_
- **`undecided`** - Конструктивное ядро всего файла: undecided определён ПОЗИТИВНО — cofinal S ∧ cofinal not-S («оба истинны бесконечно часто»), а НЕ через двойное отрицание ~cofinite (которое потребовало бы classic/DNE). Именно поэтому все три формы выводятся БЕЗ аксиомы classic — чистая Element-сторона, 0 аксиом. Это тонкий, но важный P4-ход: неразрешённость кодируется позитивно-конструктивно, не классически. Единственный role-limit (разрешение undecided через ультрафильтр) остаётся не-ассертированным. _(positive-definition, constructive, no-classic, frechet, undecided)_
- **`undecided_zero_divisor`** - Форма × единого корня: undecided S ⟹ ind S·ind not-S~0, но ни ind S, ни ind not-S не ~0. Обобщает zero_divisors_exist из GermInfinitesimal (там частный случай even/odd) до ПРОИЗВОЛЬНОГО undecided S. Показывает, что делитель нуля germ-кольца — не случайность чётности, а необходимое следствие любого неразрешённого Фреше-различения. Параллельно undecided_non_unit (кольцо) и undecided_no_shadow (+) дают три грани одного факта. _(zero-divisor, generalization, frechet, role-limit-form)_

**Uniqueness - score 4 (synthesis+observation).** Унифицирующий капстоун: ОДНО позитивно-конструктивное свойство undecided S (Фреше не решает «что велико») порождает ТРИ алгебраические формы role-limit-зазора — делитель нуля (×), осциллятор-без-тени (+), необратимость (кольцо) — БЕЗ аксиомы classic; Evens лишь частный случай.
> _Caveat:_ Это ЯВНО СИНТЕЗ/УНИФИКАЦИЯ — абстрагирование Evens-результатов (UltrafilterRoleLimit/StandardPart) к общему undecided, НЕ новые отдельные теоремы. Каждая из трёх форм по содержанию классична (делители нуля/необратимость кольца Фреше, осциллятор без предела). Genuine-вклад — что один корень даёт все три формы машинно; «исчисление=st» и трёхзначный вердикт — цитаты к файлам XVIII.

---

## #1902 - `src/nonstandard/RoleLimitIsP1Shadow.v` - score 3 (new-framing)

**Root of the arc: the role-limit seed `negb` = shadow of P1 self-membership; one Lawvere theorem yields Cantor AND Russell**

- **Topic.** Proves Lawvere's fixed-point theorem (point-surjective g forces every f:B->B to have a fixed point) and derives, from the single anti-fixed-point negb, both Cantor (no point-surjective nat -> (nat -> bool), i.e. 2^N uncountable) and Russell (no point-surjective membership, i.e. naive comprehension impossible = what P1 blocks).
- **Role.** Declared root (D) of the nonstandard arc's far side: one negb seed unifies counting (Cantor), membership (Russell/P1), measure (ultrafilter-prime, B1) and algebra (zero divisor, A1). Self-contained (no Require). Cites Core_ERR (russell_paradox_blocked), SeedDiagonalBridge (B2), ProcessDiagonal. Capstone-level framing file.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** (none — self-contained in Coq prelude: bool/negb/nat/f_equal)
- **E/R/R.** _Elements:_ Type X/B; bool и negb; предикат point_surjective; mem (членство X -> (X -> bool)). _Roles:_ negb = семя / анти-неподвижность; point_surjective = тотализация (сюръекция / компрегензия); Ловер = генератор no-go. _Rules:_ Ловер: point_surjective g ⟹ всякая f имеет неподвижную точку; negb b ≠ b ⟹ нет сюръекции (Кантор) и нет компрегензии (Рассел=P1). _P4:_ конструктивно (Ловер = явная диагональ h=λy.f(g y y), f_equal по точке x; negb b ≠ b — destruct b) ⟹ 0 аксиом. role-limit-семя negb = тень запрещённого самочленства; P1 ядра (нет x∈x) = его конструктивное укрощение на уровне членства.
- **Classical counterpart.** Lawvere's fixed-point theorem and its corollaries Cantor (no surjection onto the powerset) and Russell (no naive comprehension) are all classical (Lawvere 1969); the concrete ToS P1 (no x in x in the Level hierarchy, russell_paradox_blocked) lives in Core_ERR and is only CITED here. NEW is only the framing observation: that role-limit's seed `negb` is the shadow of forbidden self-membership, so Cantor and Russell are two instances of ONE Lawvere/negb root that P1 constructively tames.
- **Tags.** nonstandard, lawvere, diagonal, cantor, russell, P1, negb, role-limit, vein-E, synthesis

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `negb_no_fixpoint` | Lemma | negb b ≠ b — семя/анти-неподвижная точка (destruct b) |
| `point_surjective` | Definition | g : X -> (X -> B) точечно-сюръективна: всякая h есть g x |
| `lawvere` | Theorem | ★ Ловер: point_surjective g ⟹ всякая f:B->B имеет неподвижную точку (явная диагональ) |
| `no_fixpoint_no_pointsurjective` | Lemma | контрапозиция: f без неподвижной точки ⟹ нет точечно-сюръективной g |
| `cantor_uncountable` | Corollary | ★ Кантор: нет точечно-сюръективной ℕ → (ℕ → bool); 2^ℕ несчётно |
| `russell_no_comprehension` | Corollary | ★ Рассел: нет точечно-сюръективного mem; наивная компрегензия невозможна (= то, что укрощает P1) |
| `rolelimit_is_p1_shadow` | Theorem | ★ капстоун: Ловер ∧ negb≠ ∧ Кантор ∧ Рассел — один negb-корень |

**Key lemmas (deep):**

- **`lawvere`** - Подлинная теорема Ловера о неподвижной точке, машинно и без аксиом: диагональ h = λy.f(g y y) реализуется некоторым x (точечная сюръективность), и f_equal по точке x даёт g x x = f(g x x). Это извлечённый общий двигатель — Кантор и Рассел получаются как контрапозиции с f = negb, а не передоказываются. Классика (Lawvere 1969); ценность файла — что её корень = ОДНО семя negb. _(lawvere, fixed-point, diagonal, engine)_
- **`rolelimit_is_p1_shadow`** - Капстоун-наблюдение всей дальней стороны границы: ОДНА теорема Ловера + negb порождает Кантор (счёт) И Рассел (членство), а тот же negb (по цитате) даёт ультрафильтр-prime (B1) и делитель нуля (A1). Рассел = ровно то, что блокирует P1 (нет x∈x), поэтому role-limit-семя = тень запрещённого самочленства, а P1 ядра ToS = его конструктивное укрощение. Уровень — new-framing: каждый кирпич классичен, ново сведение в одну ось + связь с ToS-P1. _(synthesis, p1, negb, shadow, unification)_

**Uniqueness - score 3 (new-framing).** Role-limit-семя negb переосмыслено как тень запрещённого самочленства P1: одна теорема Ловера + negb даёт Кантор (счёт) и Рассел (членство), а P1 ядра ToS = его конструктивное укрощение; та же карта negb связывает меру (B1) и алгебру (A1).
> _Caveat:_ Ловер / Кантор / Рассел — КЛАССИКА (переинстанцированы, НЕ новые теоремы). ToS-конкретный P1 (нет x∈x) и russell_paradox_blocked — ЦИТАТА к Core_ERR (ядро не правится). Ультрафильтр-prime (B1) и делитель нуля (A1) — другие armы, лишь упомянуты. Genuine-новое = только обрамляющее наблюдение об одном negb-корне.

---

## #1903 - `src/nonstandard/SeedDiagonalBridge.v` - score 3 (new-framing)

**Bridge B2: `negb` as the common complement-structure generating three role-limit phenomena (Cantor / ultrafilter-prime / zero-divisor)**

- **Topic.** Takes the anti-fixed-point involution negb (the engine of Lawvere's diagonal, H71) and machine-derives three role-limit phenomena from negb b <> b: Cantor's no-surjection (uncountability), the ultrafilter-prime distinctness m S <> m(not S), and the complement zero-divisor ind S * ind(not S) ~ 0 over the germ ring.
- **Role.** Bridge node (B2) of the nonstandard arc: declared seed-supplier whose negb feeds the root RoleLimitIsP1Shadow (D) and the measure bridge SeedMeasureBridge (B1). Imports QArith/Arith/Lqa only; cites H71 FixedPointTaxonomy and ProcessDiagonal. Honesty-anchored: rejects 'undecided = diagonal'.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Arith Lqa
- **E/R/R.** _Elements:_ bool и negb; множества nat→bool; is_uf_measure; ind / germ GProc (nat→Q). _Roles:_ negb = семя / анти-неподвижность; комплемент = flip; prime / zero-product / no-surjection = три проявления одного семени. _Rules:_ negb b ≠ b; Кантор (нет сюръекции ℕ→2^ℕ); prime m S ≠ m ¬S (ВЫВЕДЕНО из negb); ind S · ind ¬S ~ 0 (из negb-дизъюнктности). _P4:_ конструктивно (negb destruct; диагональ выписана явно; prime и zero-product выведены из negb_no_fixpoint, без classic) ⟹ 0 аксиом. ЧЕСТНО: НЕ «undecided = диагональ» (разные объекты — отвергнуто); negb = общая комплемент-структура, доказано порождающая три.
- **Classical counterpart.** Cantor's diagonal (no surjection nat -> 2^N), the complement-respecting ('prime') property of a two-valued ultrafilter (Stone), and the indicator zero-divisor are each standard; NEW is only proving constructively that the single anti-fixed-point involution `negb` GENERATES all three (logic/count, measure, algebra), tying the H71 diagonal to B1 (measure) and A1 (algebra) through one map — explicitly REFUSING the false label 'undecided = diagonal'.
- **Tags.** nonstandard, negb, diagonal, cantor, ultrafilter, zero-divisor, bridge, role-limit, vein-E, synthesis
- **Notes.** DRIFT: STATUS header says '7 Qed', actual Qed. count = 6 (одна из 5 веток капстоуна — это Definition, не Qed). Catalogued with actual 6.

**Lemmas (12):**

| name | kind | role |
|---|---|---|
| `negb_no_fixpoint` | Lemma | negb b ≠ b — семя диагонали/Кантора/Рассела/halting (destruct b) |
| `negb_invol` | Lemma | negb (negb b) = b — инволюция (комплемент дважды = тождество) |
| `cantor_no_surjection` | Lemma | ★ арм 1 (счёт): диагональ d=λk.negb(e k k) отличается от каждой строки ⟹ нет сюръекции ℕ→2^ℕ |
| `is_uf_measure` | Definition | ультрафильтр как 2-значная комплемент-уважающая мера (реплик. из B1) |
| `uf_complement_distinct` | Lemma | ★ арм 2 (мера): m S ≠ m ¬S — ВЫВЕДЕНО из negb b ≠ b (prime ультрафильтра) |
| `GProc` | Definition | germ-процесс nat→Q (реплик.) |
| `geq` | Definition | Фреше-эквивалентность: совпадение на коконечном хвосте |
| `gmul` | Definition | поточечное произведение germ-процессов |
| `gconst` | Definition | постоянный germ-процесс |
| `ind` | Definition | индикатор множества S как germ-процесс (1/0) |
| `complement_product_zero` | Lemma | ★ арм 3 (алгебра): ind S · ind ¬S ~ 0 — negb-дизъюнктность даёт делитель нуля |
| `seed_diagonal_bridge` | Theorem | ★ капстоун: одно семя negb — три role-limit-явления + инволюция |

**Key lemmas (deep):**

- **`seed_diagonal_bridge`** - Капстоун-мост: ОДНА анти-неподвижная карта negb машинно порождает ТРИ role-limit-явления — Кантор (нет сюръекции ℕ→2^ℕ), prime ультрафильтра (m S ≠ m ¬S), делитель нуля (ind S · ind ¬S ~ 0) — связывая H71 (диагональ) ↔ B1 (мера) ↔ A1 (алгебра) через одну карту. Genuine именно потому, что это ВЫВОД (три арма доказаны из negb_no_fixpoint), а НЕ ярлык: файл явно отвергает ложное «undecided = диагональ» (разные объекты). _(negb, bridge, three-arms, synthesis, honesty)_
- **`uf_complement_distinct`** - Арм меры: prime-свойство ультрафильтра m S ≠ m ¬S выведено напрямую из negb b ≠ b через комплемент-уважение (m ¬S = negb (m S)). Показывает, что 2-значная мера наследует анти-неподвижность negb — множество и его дополнение никогда не имеют одну меру. Классический факт (Stone), но здесь подан как инстанс того же negb, что в Канторе. _(measure, ultrafilter, prime, negb)_

**Uniqueness - score 3 (new-framing).** Машинно доказано, что одна анти-неподвижная инволюция negb порождает три role-limit-явления (Кантор-несчётность, prime ультрафильтра, делитель нуля), связывая логику/счёт ↔ меру ↔ алгебру через одну карту; честно отвергает ложное отождествление undecided=диагональ.
> _Caveat:_ Каждое из трёх явлений классично (диагональ Кантора, prime-ультрафильтр/Stone, индикатор-делитель). Ново — обрамление «одно семя negb» как ВЫВОД, а не ярлык. H71 и ProcessDiagonal лишь цитируются. STATUS-заголовок завышает: 7 Qed против фактических 6 (drift).

---

## #1904 - `src/nonstandard/SeedMeasureBridge.v` - score 3 (new-framing)

**Bridge B1: undecided set = what the two-valued Frechet premeasure leaves undetermined; ultrafilter (= two-valued FA measure) resolves it**

- **Topic.** Defines cofinite/finite/cofinal/undecided sets and proves (only the forward direction, constructively) that an undecided S is neither cofinite nor finite — so the canonical two-valued Frechet premeasure fixes neither 1 nor 0 — while any two-valued complement-respecting (ultrafilter) measure is prime and thus totalizes the open case. Evens is the canonical witness.
- **Role.** Measure node (B1) of the nonstandard arc: receives the negb seed from SeedDiagonalBridge (B2), supplies the measure face of the one-object filter=measure=algebra picture. Imports Arith/Lia only; cites A1 (UnitZeroDivisorBoundary), synthesis XVIII, Stone. Honesty-anchored: naive non-measurability bridge rejected.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith Lia
- **E/R/R.** _Elements:_ множества nat→bool; cofinite / finite / cofinal / undecided; is_uf_measure; evens. _Roles:_ undecided = неопределённость 2-знач. премеры; uf-мера = тотализация (ультрафильтр); cofinite / finite = определённые премерой. _Rules:_ undecided S ⟹ ~cofinite S ∧ ~finite S; uf-мера прайм (m S = 1 ∨ m ¬S = 1); forced на cofinite/finite, free на undecided. _P4:_ конструктивно (undecided определён ПОЗИТИВНО как cofinal S ∧ cofinal ¬S, поэтому → направление без classic) ⟹ 0 аксиом. ЧЕСТНО: обратное (undetermined ⟹ undecided) нужен classic/DNE; density-1/2 = вещ. мера (Element); ровно 2-значная uf-мера = role-limit (AC, НЕ ассертим); наивный мост «undecided↔неизмеримое» отвергнут (Evens — контрпример).
- **Classical counterpart.** The identification 'ultrafilter = two-valued finitely-additive measure' (Stone) and the Frechet (cofinite/finite) premeasure are standard; NEW is only the framing that an undecided set is exactly what the canonical two-valued Frechet premeasure leaves undetermined, with the honest correction that the naive 'undecided <-> non-measurable' bridge is FALSE (Evens is density-1/2-measurable).
- **Tags.** nonstandard, ultrafilter, measure, frechet, undecided, stone, no-AC, role-limit, new-framing

**Lemmas (16):**

| name | kind | role |
|---|---|---|
| `cofinite` | Definition | S истинно на всём хвосте (Фреше-премера ↦ 1) |
| `finite` | Definition | S ложно на всём хвосте (Фреше-премера ↦ 0) |
| `cofinal` | Definition | S истинно бесконечно часто (позитивно, конструктивно) |
| `undecided` | Definition | ★ и S, и ¬S истинны бесконечно часто (Фреше не решает) |
| `evens` | Definition | чётные — каноническое неразрешённое множество |
| `is_uf_measure` | Definition | ультрафильтр как 2-знач. мера: содержит ℕ, прайм, монотонна (Stone) |
| `cofinal_evens` | Lemma | чётные бесконечно часто (свидетель 2N) |
| `cofinal_odds` | Lemma | нечётные бесконечно часто (свидетель 2N+1) |
| `undecided_evens` | Lemma | Evens — undecided (семя) |
| `undecided_not_cofinite` | Lemma | undecided S ⟹ S не коконечно (премера не ↦ 1) |
| `undecided_not_finite` | Lemma | undecided S ⟹ S не конечно (премера не ↦ 0) |
| `undecided_premeasure_undetermined` | Lemma | ★ undecided S ⟹ 2-знач. Фреше-премера оставляет S неопределённым (ни 1, ни 0) |
| `evens_premeasure_undetermined` | Lemma | анкер: премера не определяет Evens |
| `uf_measure_prime` | Lemma | ★ 2-знач. uf-мера прайм: ровно одно из S, ¬S имеет меру 1 |
| `uf_measure_resolves_undecided` | Theorem | ★ uf-мера разрешает undecided S — выбор role-limit |
| `seed_measure_bridge` | Theorem | ★ капстоун: undecided → премера-undetermined; uf-мера resolves; один объект — фильтр/мера/алгебра |

**Key lemmas (deep):**

- **`undecided_premeasure_undetermined`** - Ядро моста, доказано конструктивно благодаря ПОЗИТИВНОМУ определению undecided (cofinal S ∧ cofinal ¬S): прямое противоречие cofinal с eventually-true/false даёт ~cofinite ∧ ~finite без classic. Это Element-сторона честности — только → направление; обратное undetermined ⟹ undecided требует classic/DNE и явно НЕ доказывается. Стандартное содержание (Фреше-фильтр), ценность — точная формулировка undecided как недоопределённости премеры. _(undecided, premeasure, frechet, constructive, directional)_
- **`uf_measure_resolves_undecided`** - role-limit-сторона: любая 2-значная комплемент-уважающая мера (= ультрафильтр, Stone) прайм, поэтому тотализует то, что Фреше-премера оставила открытым — m S = 1 ∨ m ¬S = 1. Честно: СУЩЕСТВОВАНИЕ нетривиальной такой меры = фрагмент AC и НЕ ассертится (лемма условна на is_uf_measure m). Это даёт «один объект, три вида»: фильтр (undecided) / мера (ультрафильтр) / алгебра (делитель нуля A1). _(ultrafilter, prime, resolve, AC, role-limit)_

**Uniqueness - score 3 (new-framing).** Undecided множество переосмыслено как ровно то, что каноническая 2-значная Фреше-премера оставляет неопределённым, а ультрафильтр (= 2-знач. FA-мера, Stone) его тотализует; объединяет фильтр/меру/алгебру в один объект.
> _Caveat:_ ultrafilter=2-значная мера (Stone) и Фреше-премера — КЛАССИКА; ново только обрамление undecided↔премера. Честные пробелы: обратное направление нужен classic; существование uf-меры = AC (не ассертим); наивный мост undecided↔неизмеримое ОТВЕРГНУТ (Evens density-1/2 — контрпример). A1/синтез XVIII — цитаты.

---

## #1905 - `src/nonstandard/StandardPart.v` - score 3 (new-framing)

**Standard part (shadow) as a PARTIAL function: total on convergent (Element), undefined on bounded-divergent (role-limit); witness alt=(-1)^n**

- **Topic.** Defines convergence/Cauchy/bounded two-sidedly over germ processes nat->Q and proves the shadow is unique where it exists (L5 determinism) and total on constants, but the oscillator alt(n)=(-1)^n is bounded yet not Cauchy and has NO shadow — mod 'Evens big' its shadow is 1, mod 'Odds big' it is -1 (two incompatible values => ultrafilter/role-limit). Bridges alt = even_ind - odd_ind to the zero-divisor.
- **Role.** Part XVIII Batch A file (after GermInfinitesimal, UltrafilterRoleLimit): supplies the additive face (no shadow) of the same Evens/Odds split whose multiplicative face is the zero-divisor. Imports QArith/Arith/Lqa; cites UltrafilterRoleLimit, GermInfinitesimal, CauchyReal, RoleLimitLadder.
- **Counts.** Qed 12 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Arith Lia Lqa
- **E/R/R.** _Elements:_ GProc = nat→Q; converges / is_cauchy / bounded (двусторонние, чисто линейные lra); alt = (−1)ⁿ; even_ind / odd_ind; gconst. _Roles:_ germ = процесс; тень = роль-стандартное-значение; сходимость = роль-Коши; alt = роль-осциллятор / свидетель. _Rules:_ st однозначна где есть (L5-детерминизм); тотальна на сходящихся (Element), нет на огранич.-расходящихся (role-limit); alt — два несовместимых значения тени ±1; alt = even_ind − odd_ind. _P4:_ всё конечно-глубинно по координате (Element); единственный role-limit — тень огранич.-расходящегося (выбор подпоследовательности / ультрафильтр), НЕ ассертим, ибо у alt два значения. Двусторонняя сходимость выбрана сознательно (линейна, lra, без Qabs). st в RealProcess для общего Коши-germ = цитата к CauchyReal.
- **Classical counterpart.** The standard part (shadow) st of nonstandard analysis is total on finite hyperreals precisely BECAUSE an ultrafilter picks the subsequential limit (Robinson NSA); over Q-Cauchy the general st-into-RealProcess is CauchyReal.v's business (cited). NEW is only the framing: st is a PARTIAL function whose partiality (no shadow for the bounded-divergent oscillator alt) IS the finitization boundary H1 in 'shadow' form, plus the machine bridge alt = even_ind - odd_ind to the zero-divisor.
- **Tags.** nonstandard, standard-part, shadow, infinitesimal, partial-function, ultrafilter, evens-odds, role-limit, H1, new-framing

**Lemmas (23):**

| name | kind | role |
|---|---|---|
| `GProc` | Definition | germ-процесс nat→Q |
| `converges` | Definition | сходимость к рац. L (двусторонне: −eps < xₙ−L < eps) |
| `has_shadow` | Definition | у x есть тень: ∃ L, converges x L |
| `is_cauchy` | Definition | свойство Коши (двусторонне) |
| `bounded` | Definition | ограниченность (двусторонне) |
| `alt` | Definition | ★ осциллятор alt(n) = (−1)ⁿ — канонический свидетель |
| `even_ind` | Definition | индикатор чётных (1 на чётных) |
| `odd_ind` | Definition | индикатор нечётных (1 на нечётных) |
| `gconst` | Definition | постоянный процесс |
| `geq_on_evens` | Definition | равенство на хвосте ВНУТРИ чётных (= «Evens велико») |
| `geq_on_odds` | Definition | равенство на хвосте ВНУТРИ нечётных (= «Odds велико») |
| `small_two_sided` | Lemma | зажим: окрестность 0 для всех eps ⟹ значение нуль (lra) |
| `shadow_unique` | Lemma | ★ тень единственна (стандартная часть корректно определена где есть, L5) |
| `const_has_shadow` | Lemma | Element: константы имеют тень |
| `alt_even` | Lemma | alt n = 1 на чётных |
| `alt_odd` | Lemma | alt n = −1 на нечётных |
| `alt_bounded` | Lemma | alt ограничен: −1 ≤ alt n ≤ 1 |
| `alt_not_cauchy` | Lemma | alt НЕ Коши (соседние чёт/нечёт отличаются на 2) |
| `no_shadow_for_alt` | Lemma | ★★ alt НЕ имеет тени (L должна лежать и в (0,2), и в (−2,0)) |
| `alt_shadow_mod_evens` | Lemma | ★ mod «Evens велико» тень alt = 1 |
| `alt_shadow_mod_odds` | Lemma | ★ mod «Odds велико» тень alt = −1 |
| `alt_decomp` | Lemma | ★ машинный мост: alt = even_ind − odd_ind (аддитивный след того же раскола, что делитель нуля) |
| `standard_part_summary` | Theorem | ★ капстоун: единственность + тень констант + полная частичность на alt |

**Key lemmas (deep):**

- **`no_shadow_for_alt`** - Главный role-limit-результат: осциллятор alt = (−1)ⁿ ограничен, но не имеет тени — предполагаемое L при eps=1 обязано лежать одновременно в (0,2) (из чётных значений +1) и в (−2,0) (из нечётных −1), что противоречиво (lra). Это конкретный машинный свидетель того, что st ЧАСТИЧНА, а частичность = граница финитизации H1 в форме «тень»: bounded-divergent требует внешнего выбора подпоследовательности. _(shadow, role-limit, oscillator, partiality, H1)_
- **`alt_decomp`** - Машинный мост к UltrafilterRoleLimit: alt = even_ind − odd_ind, т.е. осциллятор без тени = РАЗНОСТЬ тех же двух индикаторов, чьё ПРОИЗВЕДЕНИЕ — делитель нуля. Один и тот же неразрешённый раскол Evens/Odds проявляется дважды — аддитивно (нет тени) и мультипликативно (делитель нуля). Та же граница в двух алгебраических формах — это и есть genuine-связка файла. _(bridge, decomposition, evens-odds, zero-divisor, synthesis)_
- **`shadow_unique`** - Element-сторона / L5-детерминизм: где тень существует, она единственна (два предела сходящегося процесса равны через зажим small_two_sided на L1−L2). Стандартная единственность предела, поданная как корректная определённость стандартной части на сходящихся; контраст к частичности на alt. _(uniqueness, L5, convergence, element)_

**Uniqueness - score 3 (new-framing).** Стандартная часть (тень) подана как ЧАСТИЧНАЯ функция над germ-процессами: тотальна и единственна на сходящихся (Element), не определена на ограниченно-расходящемся alt (role-limit, два несовместимых значения ±1), с машинным мостом alt = even_ind − odd_ind к делителю нуля.
> _Caveat:_ st нонстандартного анализа и его тотальность через ультрафильтр — КЛАССИКА (Robinson); st-в-RealProcess для общего Коши-germ = ЦИТАТА к CauchyReal (не передоказывается). Ново только обрамление частичности как границы H1 + аддитивно-мультипликативный мост. Финитно/конкретно: один свидетель alt.

---

## #1906 - `src/nonstandard/UltrafilterRoleLimit.v` - score 4 (synthesis+observation)

**Machine certificate: ultrafilter = role-limit, not Element-truth — germ ring not a field + localized non-canonical resolution**

- **Topic.** Over the replicated Frechet germ ring Q^N/Frechet proves even_ind*odd_ind ~ 0, then the no-go (even_ind is non-zero but non-invertible, so the ring is NOT a field), then LOCALIZES the whole obstruction to one undecided set: declaring 'Evens big' makes even_ind a unit (its own inverse), declaring 'Odds big' makes it zero — one element, two opposite fates => non-canonical => role-limit.
- **Role.** Anchor file of the nonstandard arc (Part XVIII Batch A): extracts the ontological verdict from GermInfinitesimal's zero_divisors_exist. Feeds StandardPart (same Evens/Odds split) and the seed bridges. Imports QArith/Arith/Lqa; cites GermInfinitesimal, RoleLimitLadder, ZFCAxiomLedger, Henson-Keisler.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Arith Lia Lqa
- **E/R/R.** _Elements:_ GProc = nat→Q; even_ind / odd_ind; geq (Фреше), geq_on_evens / geq_on_odds (уточн. фильтры); gmul / gconst. _Roles:_ even_ind = роль-индикатор Evens; обратимость = роль-единица; фильтр = роль-решатель; ультрафильтр = тотальный решатель (role-limit); делитель нуля = роль-препятствие / след. _Rules:_ germ-кольцо Фреше НЕ поле (∃ ненулевой необратимый); препятствие = Evens; mod Evens — единица, mod Odds — нуль. _P4:_ всё конечно-глубинно по координате ⟹ Element; единственный role-limit — тотальное решение (ультрафильтр), НЕ ассертим: предъявляем необходимость (no-go) и неканоничность (два разрешения). ЧЕСТНО: консервативность Хенсона–Кейслера и общий no-go = цитаты/экстраполяция; доказано для КАНОНИЧЕСКОЙ конструкции Фреше.
- **Classical counterpart.** The germ ring Q^N/Frechet having zero divisors (so not a field), the ultrafilter completing it to a field, and the Henson-Keisler conservativity of the *R product are all classical NSA; NEW is only recasting the zero divisor as a MACHINE CERTIFICATE of the absent ultrafilter — proving the obstruction localizes to exactly one undecided set (Evens) whose two free resolutions (unit vs zero) are non-canonical => verdict 'ultrafilter = role-limit'.
- **Tags.** nonstandard, ultrafilter, germ-ring, zero-divisor, not-field, evens-odds, role-limit, no-AC, vein-C, synthesis

**Lemmas (17):**

| name | kind | role |
|---|---|---|
| `GProc` | Definition | germ-процесс nat→Q (реплик. из GermInfinitesimal) |
| `gmul` | Definition | поточечное произведение |
| `gconst` | Definition | постоянный germ-процесс |
| `geq` | Definition | Фреше-эквивалентность (совпадение на коконечном хвосте) |
| `g_invertible` | Definition | обратимость mod Фреше: ∃ обратный |
| `even_ind` | Definition | индикатор чётных (тот же делитель нуля, что в GermInfinitesimal) |
| `odd_ind` | Definition | индикатор нечётных |
| `geq_on_evens` | Definition | равенство на хвосте ВНУТРИ чётных (= «Evens велико») |
| `geq_on_odds` | Definition | равенство на хвосте ВНУТРИ нечётных (= «Odds велико») |
| `even_times_odd_zero` | Lemma | анкер: even_ind · odd_ind ~ 0 (поточечно ноль) |
| `even_ind_not_zero` | Lemma | even_ind ≁ 0 mod Фреше (значение 1 на каждой чётной точке хвоста) |
| `even_ind_not_invertible` | Lemma | ★★ NO-GO-ядро: even_ind необратим (обратный = 1/0 на нечётных) |
| `germ_ring_not_field` | Theorem | ★ germ-кольцо Фреше НЕ поле: ∃ ненулевой необратимый |
| `even_ind_invertible_mod_evens` | Lemma | ★ mod «Evens велико» even_ind = единица (сам себе обратный) |
| `even_ind_zero_mod_odds` | Lemma | ★ mod «Odds велико» тот же even_ind = нуль |
| `ultrafilter_decision_required` | Theorem | ★ неканоничность: один элемент — единица при Evens, нуль при Odds |
| `ultrafilter_role_limit_summary` | Theorem | ★ капстоун-вердикт: no-go + локализация + неканоничность = role-limit |

**Key lemmas (deep):**

- **`germ_ring_not_field`** - Машинное no-go: even_ind ненулевой mod Фреше (значение 1 на чётном хвосте), но необратим — обратный был бы 1/even_ind = 1/0 на нечётных индексах (свидетель n=2N+1 даёт 0·y=1, ложь). Значит germ-кольцо ℚ^ℕ/Фреше не поле. Классический факт (germ ring has zero divisors), но здесь подан как сертификат ОТСУТСТВУЮЩЕГО ультрафильтра, а не курьёз. _(no-go, germ-ring, not-field, zero-divisor)_
- **`ultrafilter_decision_required`** - Сердце вердикта: ВСЁ препятствие локализуется в одно неразрешённое множество Evens. Объяви «Evens велико» — even_ind становится единицей (even_ind·even_ind=1 на чётных); объяви «Odds велико» — тот же even_ind становится нулём. Один элемент, две противоположные судьбы от свободного решения ⟹ канонического значения НЕТ ⟹ ультрафильтр лежит на role-limit-стороне (фрагмент AC, строго НАД лестницей LLPO⊏WLPO⊏LPO). Genuine-перевод концептуального вердикта в машинную локализацию. _(localization, non-canonical, evens-odds, role-limit, AC)_
- **`ultrafilter_role_limit_summary`** - Капстоун, собирающий три кирпича: no-go (не поле) + локализация (препятствие = Evens) + неканоничность (Evens→единица, Odds→нуль). Делитель нуля = машинный СЛЕД отсутствующего ультрафильтра. Файл явно НЕ опровергает аксиому ультрафильтра (консистентна, независима в ZF) — он предъявляет ровно то препятствие, которое она латает, и доказывает неканоничность латания. _(capstone, verdict, role-limit, honesty)_

**Uniqueness - score 4 (synthesis+observation).** Делитель нуля germ-кольца Фреше переведён в машинное СВИДЕТЕЛЬСТВО того, что ультрафильтр = role-limit, а не Element-истина: no-go (не поле) + локализация всего препятствия в одно неразрешённое множество Evens + неканоничность его разрешения (единица mod Evens, нуль mod Odds).
> _Caveat:_ germ-кольцо с делителями нуля, ультрафильтр-как-поле-пополнение и консервативность *ℝ (Хенсон–Кейслер) — КЛАССИКА NSA. Консервативность и общий «никакой выбор-свободный фактор ℚ^ℕ не поле» = ЦИТАТЫ/честная экстраполяция (доказано лишь для канонической конструкции Фреше). СУЩЕСТВОВАНИЕ ультрафильтра (AC) НЕ ассертится и НЕ опровергается. Ново — машинная локализация + вердикт, не теорема NSA.

---

## #1907 - `src/nonstandard/UndecidedHierarchy.v` - score 3 (new-framing)

**The far side of the boundary is GRADED, not binary: membership (Turing) axis vs magnitude (LPO) axis**

- **Topic.** Over nat->bool sets, separates two undecidability axes — membership (is n in S, Turing) and magnitude (is S 'large', LPO) — and proves every nat->bool set has decidable membership while evens is undecided-in-magnitude (cofinal both ways) and singleton {0} is finite; so role-limit-ness of evens lives in the TOTALISATION, not the set.
- **Role.** C-direction refinement of the nonstandard boundary arc: shows the role-limit (far) side is stratified into rungs Element (singleton) < LPO-rung (evens) < Turing-rung (halting). Imports only Stdlib (Arith/Lia); the Turing rung is CITED to cs/HaltingRoleLimit, not formalized here. Neighbour of H69 (LPO ladder).
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith Lia
- **E/R/R.** _Elements:_ множества nat->bool (cofinite/finite/cofinal/undecided); decidable_pred (sumbool в Type); конкретные evens=Nat.even, singleton=Nat.eqb 0. _Roles:_ членство = axis-1 (Тьюринг-ось разрешимости); величина = axis-2 (LPO-ось, велико/мало); рунг = глубина role-limit на дальней стороне границы. _Rules:_ nat->bool ⟹ разрешимое членство (destruct (S n)); evens = разрешимо поэлементно, но undecided величина (cofinal в обе стороны); singleton = разрешимо + конечно (величина решена). _P4:_ конструктивно (decidable_pred даётся явным destruct; singleton finite предъявлен явно) ⟹ 0 аксиом. ЧЕСТНО: Тьюринг-рунг (halting, неразрешимое членство) — ЦИТАТА, ибо non-computable nat->Prop нельзя предъявить в Coq; genuine = LPO-анкор (role-limit при разрешимом членстве) + наблюдение градации двух фронтиров.
- **Classical counterpart.** The membership/value distinction is classical recursion theory: a decidable predicate (nat->bool) can still have an undecidable totalisation — the canonical instance is LPO (Limited Principle of Omniscience, Bishop), the constructively-unprovable 'is this sequence eventually 0 / infinitely often 1', distinct from Turing-undecidability of halting. NEW is only re-casting these two known frontiers as a STRATIFIED 'far side' of the ToS finitization boundary (membership=Turing axis vs magnitude=LPO axis) and the anchor observation that evens has decidable membership yet undecided magnitude.
- **Tags.** nonstandard, lpo, role-limit, membership-vs-magnitude, stratification, finitization-boundary, P4, constructive

**Lemmas (13):**

| name | kind | role |
|---|---|---|
| `cofinite` | Definition | S кофинитно: ∃N, на хвосте S n = true |
| `finite` | Definition | S конечно = дополнение кофинитно |
| `cofinal` | Definition | S кофинально: ∀N ∃n≥N, S n = true (позитивно, бесконечно часто) |
| `undecided` | Definition | S undecided = S и дополнение оба кофинальны (величина не решена) |
| `decidable_pred` | Definition | axis-1: P : nat->Prop разрешим поэлементно (sumbool в Type) |
| `evens` | Definition | evens n = Nat.even n — LPO-анкор (разрешимое членство, undecided величина) |
| `singleton` | Definition | singleton n = Nat.eqb n 0 — Element-анкор (конечная величина) |
| `bool_pred_decidable` | Lemma | ★ всякое nat->bool множество имеет разрешимое членство (axis-1 ниже границы) |
| `cofinal_evens` | Lemma | evens кофинально (свидетель 2N, Nat.even_add_mul_2) |
| `cofinal_odds` | Lemma | дополнение evens кофинально (свидетель 2N+1) |
| `undecided_evens` | Lemma | ★ evens — undecided ВЕЛИЧИНА (LPO-рунг): обе стороны кофинальны |
| `singleton_finite` | Lemma | ★ singleton {0} конечно — Element (величина решена: мало) |
| `undecided_hierarchy` | Theorem | ★ капстоун: undecided evens /\ finite singleton — два фронтира LPO ⊏ Тьюринг |

**Key lemmas (deep):**

- **`bool_pred_decidable`** - Axis-1 фундамент: ЛЮБОЕ nat->bool множество разрешимо поэлементно (тривиальный destruct (S n) с reflexivity/discriminate). Конструктивно, 0 аксиом. Смысл не в трудности (её нет), а в том, что он фиксирует Тьюринг-ось НИЖЕ границы для всех bool-предикатов — тем самым изолируя, что вся role-limit-ность evens приходит со ВТОРОЙ оси (величина), а не с членства. Это разделяющий шаг для всего файла. _(decidable, membership-axis, constructive)_
- **`undecided_evens`** - Генуинный анкер: evens имеет РАЗРЕШИМОЕ членство (Nat.even вычислима, bool_pred_decidable), НО undecided величину — и evens, и нечётные кофинальны, так что Фреше-мера «велико ли» не решается. Это и есть LPO-рунг: классически = LPO (Бишоп), конструктивно непровабельный принцип всеведения. Ключевое наблюдение: role-limit-ность НЕ в множестве (оно вычислимо), а в ТОТАЛИЗАЦИИ. Честно: LPO — известный конструктивный водораздел; ново лишь его размещение как промежуточного рунга между Element и Тьюрингом. _(lpo, totalisation, role-limit, anchor)_
- **`undecided_hierarchy`** - Капстоун-наблюдение (0 аксиом): дальняя сторона границы финитизации НЕ бинарна, а стратифицирована — Element (singleton, конечная величина) ⊏ LPO-рунг (evens, разрешимое членство + undecided величина) ⊏ Тьюринг-рунг (halting, неразрешимое членство, цитата cs/HaltingRoleLimit). evens и singleton различает ВЕЛИЧИНА, не членство. Уровень — new-framing: оба фронтира (LPO и Тьюринг) классичны; ново их сведение в одну градуированную ось role-limit-глубины. Тьюринг-рунг здесь не формализован (non-computable предикат нельзя предъявить в Coq). _(stratification, two-frontiers, capstone, new-framing)_

**Uniqueness - score 3 (new-framing).** Дальняя (role-limit) сторона границы финитизации стратифицирована по тому, ГДЕ живёт неразрешимость: членство (Тьюринг) vs величина (LPO); машинный анкор — evens разрешимо поэлементно, но undecided в величине, так что role-limit-ность в тотализации, а не в множестве.
> _Caveat:_ Оба фронтира классичны: LPO — известный конструктивный принцип (Бишоп), Тьюринг-неразрешимость halting стандартна. Ново только обрамление-градация. Тьюринг-рунг здесь НЕ доказан, а ЦИТИРУЕТСЯ (cs/HaltingRoleLimit; non-computable nat->Prop нельзя предъявить конструктивно в Coq). Genuine-вклад = LPO-анкор + наблюдение двух фронтиров; всё конечно/конструктивно над nat->bool.

---

## #1908 - `src/nonstandard/UnitZeroDivisorBoundary.v` - score 3 (new-framing)

**The finitization boundary = INVERTIBILITY in the germ ring: unit <-> eventually-nonzero (Element), zero-divisor <-> zero-set cofinal (role-limit)**

- **Topic.** In the germ ring Q^N/Frechet, characterizes both poles of invertibility constructively: x is a unit <-> eventually non-zero (inverse = 1/x on the tail), x is a zero-divisor <-> its zero-set is cofinal (witness = indicator of the zero-set); anchors with delta=1/(n+1) a unit and even_ind a zero-divisor.
- **Role.** A1-direction root of the nonstandard 'generating structure of the boundary' arc: extracts the algebraic floor that Element side = units, role-limit side = zero-divisors (undecided). Imports only Stdlib (QArith/ZArith/Arith/Lqa). The link 'Element = atlas units (det +-1 = unit of SL2(Z))' is a CITATION (bridge A2); 'deciding the pole = LPO/halting' is an OBSERVATION (cs/ScaleFlowUndecidable).
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith ZArith Arith Lia Lqa
- **E/R/R.** _Elements:_ germ-кольцо GProc=nat->Q (geq=в-конце-равны, gmul, gconst); полюса g_unit/g_zero_divisor; позитивные eventually_nonzero/cofinal_nz/cofinal_z; анкеры delta=1/(n+1), even_ind=индикатор чётных. _Roles:_ обратимость = Element-маркер (терминирует, /x на хвосте); необратимость = role-limit-маркер; нуль-множество = носитель неразрешённости (его конечность/кофинальность решает полюс). _Rules:_ L5: unit_iff (единица ⟺ в-конце-ненулев); zero_divisor_iff (делитель ⟺ нуль-множество кофинально); delta единица (всюду ненулева), even_ind делитель (нуль на нечётных, кофинально). _P4:_ конструктивно: единица строит ЯВНЫЙ обратный fun n => /x n; делитель использует ПОЗИТИВНЫЙ cofinal (бесконечно часто, не двойное отрицание) + Qmult_integral; индикатор нуль-множества предъявлен явно ⟹ 0 аксиом, classic не нужен. Единственный role-limit — undecided нуль-множество — НЕ ассертируется.
- **Classical counterpart.** The germ ring Q^N/Frechet (functions mod eventual agreement) is the classical reduced-power / Robinson-NSA construction; the fact that a unit <-> eventually non-zero and a zero-divisor <-> zero-set cofinal is standard ring theory of that ring. NEW is only mapping invertibility's two poles onto the ToS finitization boundary (unit=Element side / atlas det +-1, zero-divisor=role-limit/undecided side) and the constructive (classic-free) positive-cofinal proof of both characterizations.
- **Tags.** nonstandard, germ-ring, unit, zero-divisor, invertibility, finitization-boundary, infinitesimal, constructive, P4

**Lemmas (23):**

| name | kind | role |
|---|---|---|
| `GProc` | Definition | germ-носитель: nat->Q |
| `geq` | Definition | равенство germ'ов: ∃N, на хвосте x n == y n (по модулю Фреше) |
| `gmul` | Definition | поточечное умножение germ'ов |
| `gconst` | Definition | константный germ |
| `g_unit` | Definition | единица: ∃y, gmul x y ~ gconst 1 (обратим) |
| `eventually_nonzero` | Definition | ∃N, на хвосте x n ≠ 0 |
| `cofinal_nz` | Definition | позитивно: ∀N ∃n≥N, x n ≠ 0 (кофинально-ненулев) |
| `cofinal_z` | Definition | позитивно: ∀N ∃n≥N, x n = 0 (нуль-множество кофинально) |
| `g_zero_divisor` | Definition | делитель нуля: ∃y кофинально-ненулев с gmul x y ~ 0 |
| `eventually_nonzero_unit` | Lemma | ⟸: в-конце-ненулев ⟹ единица (обратный = /x на хвосте, Qmult_inv_r) |
| `unit_eventually_nonzero` | Lemma | ⟹: единица ⟹ в-конце-ненулев (иначе 0=1 на нуле) |
| `unit_iff_eventually_nonzero` | Lemma | ★ ЕДИНИЦА ⟺ в конце ненулевой |
| `cofinal_z_zero_divisor` | Lemma | ⟸: нуль-множество кофинально ⟹ делитель (свидетель = индикатор нуль-множества) |
| `zero_divisor_cofinal_z` | Lemma | ⟹: делитель ⟹ нуль-множество кофинально (Qmult_integral на y≠0) |
| `zero_divisor_iff_cofinal_z` | Lemma | ★ ДЕЛИТЕЛЬ НУЛЯ ⟺ нуль-множество кофинально |
| `Qof` | Definition | вложение nat->Q через inject_Z |
| `Qof_pos` | Lemma | 0 < Qof (S m) (положительность хвоста) |
| `delta` | Definition | delta m = 1/(m+1) — Element-инфинитезималь |
| `even_ind` | Definition | even_ind n = индикатор чётных (1 на чётных, 0 на нечётных) |
| `delta_is_unit` | Lemma | ★ delta — ЕДИНИЦА (всюду ненулева, обратный = n+1) |
| `even_ind_cofinal_z` | Lemma | even_ind нулевой на нечётных — кофинально (свидетель 2N+1) |
| `even_ind_is_zero_divisor` | Lemma | ★ even_ind — ДЕЛИТЕЛЬ НУЛЯ (undecided необратим) |
| `boundary_is_invertibility` | Theorem | ★ капстоун: оба ⟺ + delta единица + even_ind делитель = граница как обратимость |

**Key lemmas (deep):**

- **`unit_iff_eventually_nonzero`** - Element-полюс как точная характеризация: x обратим в germ-кольце ⟺ x в конце ненулев. ⟸ строит ЯВНЫЙ обратный fun n => /x n и Qmult_inv_r на хвосте (конструктивно, без classic); ⟹ — если на нуле, то 0=1 (Qmult_0_l + lra). Это алгебраическое ядро Element-стороны границы: обратимость = терминирующее свойство (/x вычислимо на хвосте). Связь к редукционному атласу (det +-1 = единица SL2(Z)) ЦИТИРУЕТСЯ (мост A2), здесь не доказывается. _(unit, element-pole, constructive, germ-ring)_
- **`zero_divisor_iff_cofinal_z`** - Role-limit-полюс как точная характеризация: x — делитель нуля ⟺ его нуль-множество кофинально (нуль бесконечно часто). ⟸ предъявляет свидетеля = индикатор нуль-множества (if Qeq_bool (x n) 0 then 1 else 0), кофинально-ненулевой по построению; ⟹ из y≠0 кофинально + x·y~0 извлекает x=0 через Qmult_integral. Используется ПОЗИТИВНЫЙ cofinal (бесконечно часто), а не двойное отрицание — потому 0 аксиом. Это алгебраическое лицо role-limit/undecided стороны. _(zero-divisor, role-limit-pole, positive-cofinal, Qmult_integral)_
- **`boundary_is_invertibility`** - Капстоун арки A1: ВСЯ граница финитизации = вопрос ОБРАТИМОСТИ в germ-кольце Q^N/Фреше. Конъюнкция (единица⟺в-конце-ненулев) /\ (делитель⟺нуль-множество-кофинально) /\ (delta единица) /\ (even_ind делитель) фиксирует трихотомию 0 / единица / делитель = в-конце-ноль / в-конце-ненулев / undecided. Два атласа проекта (Element=атлас редукций, role-limit=синтез XVIII) суть два полюса инвертируемости. Уровень — new-framing: germ-кольцо и его теория единиц/делителей классичны (Robinson-NSA / reduced power); ново отождествление двух полюсов со сторонами границы. 'Разрешить полюс = конечно ли нуль-множество = LPO/halting' — наблюдение (цитата cs/ScaleFlowUndecidable). _(capstone, invertibility, trichotomy, new-framing)_

**Uniqueness - score 3 (new-framing).** Граница финитизации отождествлена с ОБРАТИМОСТЬЮ в germ-кольце Q^N/Фреше: единица ⟺ в-конце-ненулев (Element-полюс), делитель нуля ⟺ нуль-множество кофинально (role-limit-полюс); обе характеризации доказаны конструктивно (0 аксиом, позитивный cofinal), с анкерами delta-единица и even_ind-делитель.
> _Caveat:_ Germ-кольцо Q^N/Фреше и его теория единиц/делителей нуля классичны (приведённая степень / NSA Робинсона). Ново только отождествление двух полюсов инвертируемости со сторонами границы финитизации. Связь 'Element = единицы редукционного атласа (det +-1)' — ЦИТАТА (мост A2), здесь не доказана; 'разрешить полюс = LPO/halting' — наблюдение (cs/ScaleFlowUndecidable), не передоказывается. Всё конструктивно над Q.

