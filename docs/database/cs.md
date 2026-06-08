# Database - cluster `cs`

_Generated from `cs.json` by `generate.ps1` - do not edit by hand; edit the JSON._

**23 files / 160 Qed.** Score distribution: s5=3 / s4=11 / s3=7 / s2=2 / s1=0 / s0=0

---

## #97 - `src/cs/BoundaryDecidability.v` - score 5 (synthesis+observation)

**Element-drawn vs role-limit-drawn: the decidable finitization boundary; one diagonal, three faces**

- **Topic.** Defines the second-order predicates ElementDrawn (a decision-criterion IS decidable) and RoleLimitDrawn (no total decider — a self-negating diagonal exists), then instantiates them on the discriminant-perfect-square test (number), halting (program) and Cantor (set).
- **Role.** FLAGSHIP of vein A (decidable finitization boundary) + vein E (one diagonal). Imports cs.HaltingRoleLimit; reused by KolmogorovRoleLimit, ScaleFlowUndecidable, RecursionTheorem, ComputationModel.
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: PeanoNat Bool Arith; cs.HaltingRoleLimit
- **E/R/R.** _Elements:_ конкретные критерии-разрезы (дискриминант Δ, halts, surjection-флаг); решатели dec: Dom->bool. _Roles:_ ElementDrawn / RoleLimitDrawn — роли ВТОРОГО порядка: классифицируют сами критерии; решатель = роль-оракул. _Rules:_ Side d <-> dec d = true (Element) против forall dec, exists d, Side d <-> dec d = false (диагональ). _P4:_ ОДНА граница, две стороны: разрешимое = Element (терминирует), самоотрицающая диагональ = role-limit; реифицировать role-limit в тотальный решатель = категориальная ошибка, запрещённая negb-диагональю.
- **Classical counterpart.** Cantor's theorem / Lawvere's diagonal (the role-limit engine) and the decidability of perfect-square testing (the Element side) are both classical; NEW is bundling them as a SECOND-ORDER Element/role-limit classification of decision-criteria, with the discriminant as the Element coordinate.
- **Tags.** diagonal, decidable, role-limit, vein-A, vein-E, P4, synthesis

**Lemmas (13):**

| name | kind | role |
|---|---|---|
| `ElementDrawn` | Definition | критерий Side разрешим: exists dec, forall d, Side d <-> dec d = true |
| `RoleLimitDrawn` | Definition | против каждого dec есть самоотрицающий свидетель: Side d <-> dec d = false |
| `element_drawn_implies_decidable` | Lemma | ElementDrawn даёт булеву разрешимость членства |
| `diagonal_defeats_decider` | Theorem | ★ универсальный движок: самоотрицающий свидетель ⟹ RoleLimitDrawn |
| `is_square` | Definition | булев тест полного квадрата через Nat.sqrt |
| `is_square_iff` | Lemma | is_square n = true <-> exists r, r*r = n (корректность теста) |
| `rational_split` | Definition | дискриминант d = полный квадрат (Element-сторона собственного значения) |
| `discriminant_element_drawn` | Theorem | ★ ElementDrawn rational_split — Δ-perfect-square РАЗРЕШИМ (вена A) |
| `disc_hadamard_role_limit` | Example | is_square 8 = false (иррациональный корень) |
| `disc_pell_role_limit` | Example | is_square 32 = false |
| `disc_rational_element` | Example | is_square 9 = true (рациональный корень) |
| `halting_role_limit_drawn` | Theorem | самоприменение ⟹ self-halting есть RoleLimitDrawn |
| `one_boundary_three_faces` | Theorem | ★ число (Element) / программа / множество — одна граница, один negb-движок |

**Key lemmas (deep):**

- **`diagonal_defeats_decider`** - Универсальная форма канторовской/халтинговой диагонали: если для всякого кандидата-решателя dec существует свидетель d с Side d <-> dec d = false, то Side не разрешим. Это извлечённый общий двигатель — все role-limit-грани (halting, Райс, Колмогоров, Тарский) доказываются как его инстансы, а не повторно. Сводит «несчётность/неразрешимость» к одному факту b <> negb b. _(diagonal, role-limit, engine)_
- **`discriminant_element_drawn`** - Вена A в одной теореме: вопрос «рационально ли собственное значение 2x2-матрицы» = «дискриминант Δ полный квадрат» РАЗРЕШИМ булевым тестом is_square. Это Element-сторона границы финитизации, наблюдаемо контрастирующая с role-limit-сторонами того же файла. Честно: разрешимость perfect-square тривиальна; ценность — постановка её как ОДНОЙ координаты с halting/Cantor. _(discriminant, decidable, vein-A, eigenvalue)_
- **`one_boundary_three_faces`** - Капстоун-наблюдение: число (Δ, Element), программа (halting, role-limit) и множество (Cantor, role-limit) — три грани ОДНОЙ границы Element/role-limit, и все role-limit-грани движимы единственной negb-диагональю. KolmogorovRoleLimit расширяет до четырёх граней. Уровень — синтез+наблюдение: каждая грань классична, ново их сведение в одну ось. _(synthesis, three-faces, unification)_

**Uniqueness - score 5 (synthesis+observation).** Второпорядковая классификация самих критериев-разрезов (ElementDrawn/RoleLimitDrawn) + разрешимый дискриминантный тест как Element-сторона + извлечённый универсальный диагональный движок, сводящий число/программу/множество к одной границе.
> _Caveat:_ Каждый кирпич классичен (разрешимость perfect-square, диагональ Кантора, неразрешимость halting). Ново — сведение в одну ось и второпорядковая рамка; универсальность эмпирична (≈68 инстансов в репо), НЕ мета-теорема.

---

## #98 - `src/cs/ChomskyHierarchy.v` - score 3 (new-framing)

**Chomsky hierarchy as a graded role-limit ladder; regular ⊊ context-free, proven**

- **Topic.** Casts the language classes as a finitization ladder (finite memory → stack → tape → full computation) and PROVES the bottom rung strictly: {a^n b^n} is context-free (CFG S→ε|aSb) but not regular.
- **Role.** Extends the Phase-3 regular-floor upward. Imports RegularElementFloor, PumpingRoleLimit, PumpingPigeonhole. Orthogonal to the diagonal vertical (no overlap with the concurrent capstones).
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: List; cs.RegularElementFloor; cs.PumpingRoleLimit; cs.PumpingPigeonhole
- **E/R/R.** _Elements:_ слова; грамматика CFG_anbn (правила S→ε\|aSb); DFA. _Roles:_ класс языка (регулярный/контекстно-свободный) = роль-ярус иерархии; «память» (конечная/стек/лента) = роль. _Rules:_ порождение грамматикой (cfg_eps/cfg_wrap); распознавание DFA; pumping-стена. _P4:_ иерархия = лестница role-limit'ов: регулярные = Element-пол (разрешимо), каждый ярус добавляет память = поднимается по role-limit-градиенту; верх (RE) = halting role-limit.
- **Classical counterpart.** The Chomsky hierarchy and the pumping lemma (a^n b^n not regular) are standard automata theory; NEW is only the Element/role-limit 'memory ladder' framing.
- **Tags.** formal-languages, chomsky, ladder, role-limit, separation

**Lemmas (10):**

| name | kind | role |
|---|---|---|
| `CFG_anbn` | Inductive | грамматика S→ε\|aSb как индуктивный предикат над list bool |
| `repeat_snoc` | Lemma | repeat a n ++ [a] = repeat a (S n) |
| `anbn_succ` | Lemma | разворот a^(n+1) b^(n+1) = a·(a^n b^n)·b |
| `CFG_anbn_to_InL` | Lemma | грамматика ⟹ принадлежность {a^n b^n} |
| `InL_to_CFG_anbn` | Lemma | принадлежность ⟹ грамматика (обратное) |
| `CFG_anbn_iff_In_L` | Lemma | грамматика порождает РОВНО {a^n b^n} |
| `anbn_2` | Example | [a b] порождается |
| `anbn_4` | Example | [a a b b] порождается |
| `regular_recognized` | Definition | L регулярен = некоторый конечный DFA его распознаёт |
| `regular_subsetneq_context_free` | Theorem | ★ {a^n b^n} контекстно-свободен, но НЕ регулярен (строгое включение) |

**Key lemmas (deep):**

- **`regular_subsetneq_context_free`** - Строгое включение нижнего яруса лестницы: язык порождается КС-грамматикой, но никакой DFA его не распознаёт (через no_dfa_for_anbn_unconditional). Конкретное доказательство «память=стек строго мощнее конечной памяти» = строго первый шаг role-limit-градиента над Element-полом. _(separation, context-free, ladder)_
- **`CFG_anbn_iff_In_L`** - Точная характеризация: индуктивная грамматика и арифметическое описание {a^n b^n} совпадают. Мост между порождающей (грамматика) и счётной (cF/cT-баланс) формами — нужен, чтобы перенести pumping-несрегулярность на грамматический класс. _(grammar, characterization)_

**Uniqueness - score 3 (new-framing).** Иерархия Хомского переосмыслена как градуированная лестница Element/role-limit (память = роль), с машинно-проверенным строгим нижним ярусом.
> _Caveat:_ Стандартная теория автоматов; pumping/КС-грамматики классичны. Ново только обрамление-лестница. Честные пробелы: верх RE=halting лишь цитируется, LBA и regex↔DFA не формализованы.

---

## #99 - `src/cs/ComputationModel.v` - score 4 (synthesis+observation)

**The computation arena as one object; capstone: computation = the finitization boundary**

- **Topic.** Bundles a computation model into one Record CompModel, restates bounded-halting decidability on that object, and gathers the whole picture into one capstone: Element side decidable + one diagonal four faces + Lawvere root.
- **Role.** Synthesis/capstone of the diagonal vertical. Pure consolidation (0 new content). Imports HaltingRoleLimit, BoundaryDecidability, KolmogorovRoleLimit, LawvereFixedPoint. Concurrent-workstream file.
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** Stdlib: PeanoNat Bool; cs.HaltingRoleLimit; cs.BoundaryDecidability; cs.KolmogorovRoleLimit; cs.LawvereFixedPoint
- **E/R/R.** _Elements:_ конкретные машины (countdown); ограниченные прогоны run n. _Roles:_ CompModel — арена (объект); Element/role-limit — роли критерия-решения; решатель — роль-оракул; корень — неподвижная точка Ловера. _Rules:_ модель связывает step (L5-порядок) + halted (статус); граница «терминирует ⟺ Element» как одно правило. _P4:_ ОДНА арена несёт ОБЕ стороны: ограниченная остановка разрешима (Element), безграничная/сложность/несчётность — role-limit (одна диагональ, four faces), корень — Ловер.
- **Classical counterpart.** Church-Turing computation models and Rice/Cantor/halting are classical; NEW is only the one-object CompModel bundling and the four-faces+Lawvere consolidation (no new content).
- **Tags.** capstone, computation-model, four-faces, lawvere, synthesis, P4

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `CompModel` | Record | арена вычисления: {cm_config; cm_step; cm_halted} |
| `cm_halts_in` | Definition | остановка в бюджете n на арене |
| `cm_halts` | Definition | полная (безграничная) остановка — role-limit-завершение |
| `cm_bounded_decidable` | Theorem | ★ Element-сторона на арене: ограниченная остановка разрешима для любой машины/бюджета |
| `countdown` | Definition | конкретный обитатель арены: счётчик-машина (pred, =0) |
| `countdown_halts_cm` | Example | countdown 3 останавливается (vm_compute) |
| `computation_is_finitization_boundary` | Theorem | ★ КАПСТОУН: Element разрешим + four faces + корень Ловера в одной теореме |

**Key lemmas (deep):**

- **`computation_is_finitization_boundary`** - Гранд-капстоун всей вертикали: (1) на ЛЮБОЙ машине ограниченная остановка разрешима (Element/P4); (2) role-limit-сторона = одна диагональ в ЧЕТЫРЁХ гранях (число/программа/множество/сложность); (3) корень — теорема Ловера о неподвижной точке, инстансом которой является каждая грань. Чистая консолидация HaltingRoleLimit+BoundaryDecidability+Kolmogorov+Lawvere — спина Части XV книги. _(capstone, four-faces, lawvere, synthesis)_
- **`cm_bounded_decidable`** - Element-сторона, поднятая с Section-машин на бандл-объект CompModel: для любой записи-арены и любого бюджета ограниченная остановка разрешима. Делегирует bounded_halting_decidable — показывает, что объектная упаковка не теряет разрешимости. _(element, decidable, bundling)_

**Uniqueness - score 4 (synthesis+observation).** Единый объект-арена CompModel несёт обе стороны границы финитизации; капстоун собирает Element-разрешимость + четыре грани + корень Ловера в одну теорему — спина книжной Части XV.
> _Caveat:_ Чистая консолидация, 0 нового содержания; ценность — унификация, не теорема. Параллельный поток (не мой).

---

## #100 - `src/cs/CountableDependentChoiceFree.v` - score 4 (synthesis+observation)

**Dependent choice over ℕ without DC: the least-successor chain of a decidable total relation**

- **Topic.** Builds an infinite R-chain with NO Dependent-Choice axiom: for a decidable total relation on ℕ, the least valid successor (nat_least) makes each step deterministic, so the trajectory is canonical and unique.
- **Role.** Vein B (deterministic selection without AC), countable-dependent level. Builds on CountableSelectionFree; bundled by SelectionWithoutChoiceSynthesis. Concurrent-workstream file (H50).
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib: PeanoNat Arith Lia; cs.CountableSelectionFree
- **E/R/R.** _Elements:_ ℕ — счётный носитель; разрешимое тотальное отношение R. _Roles:_ преемник next x = роль по правилу «наименьший допустимый»; цепь = детерминированная траектория. _Rules:_ nat_least выбирает наименьший преемник ⟹ детерминированный шаг ⟹ R-цепь без DC. _P4:_ зависимый выбор — Element-сторона при разрешимом+тотальном R на ℕ (наименьший-преемник, 0 акс); неразрешимое ⟹ DC = role-limit (BolzanoWeierstrass платит classic за неразрешимость критерия половины).
- **Classical counterpart.** Dependent Choice (DC) and its constructive elimination for decidable relations are known (Bishop / constructive epsilon); NEW is the least-successor packaging with uniqueness, framed as vein-B determinism.
- **Tags.** no-AC, no-DC, vein-B, selection, deterministic, P4

**Lemmas (9):**

| name | kind | role |
|---|---|---|
| `next` | Definition | детерминированный преемник = наименьший y с R x y (через nat_least) |
| `next_sound` | Lemma | преемник валиден: R x (next x) = true |
| `next_least` | Lemma | next x — наименьший: любой валидный y ≥ next x |
| `dc_chain` | Fixpoint | траектория next от x0 (цепь зависимого выбора) |
| `dc_chain_step` | Theorem | ★ цепь ЕСТЬ R-цепь: зависимый выбор без аксиомы DC |
| `dc_chain_unique` | Lemma | правило фиксирует ТУ цепь — нет выбора среди преемников |
| `lt_total` | Lemma | отношение x<y тотально (S x — преемник) |
| `lt_chain_increasing` | Example | детерминированная цепь от 0 строго возрастает на каждом шаге |
| `countable_dependent_choice_free` | Theorem | капстоун: R-цепь + каноничность + единственность |

**Key lemmas (deep):**

- **`dc_chain_step`** - Зависимый выбор без DC: для разрешимого тотального R на ℕ бесконечная R-цепь строится наименьшим-преемником (nat_least) на каждом шаге — никакой аксиомы Dependent Choice. Это вена B на уровне зависимого выбора: порядок ℕ + разрешимый тест ВЫБИРАЮТ за оракула. _(no-DC, vein-B, deterministic)_
- **`dc_chain_unique`** - Каноничность-как-детерминизм: любая функция f с f0=x0 и шагом next совпадает с dc_chain. Правило ПРИШПИЛИВАЕТ единственную цепь — нет свободного выбора среди преемников, потому и нет нужды в DC. Это ядро тезиса «выбор свободен ⟺ разрешим». _(uniqueness, determinism, no-DC)_

**Uniqueness - score 4 (synthesis+observation).** Зависимый выбор над ℕ для разрешимых тотальных отношений АКСИОМО-СВОБОДЕН через наименьший-преемник; цепь детерминирована и единственна — аналог H49 на уровне зависимого выбора.
> _Caveat:_ Наименьший-преемник-спуск стандартен при наличии nat_least; вклад — упаковка decidable-DC, её детерминизм и параллель к счётному выбору. Параллельный поток (не мой).

---

## #101 - `src/cs/CountableSelectionFree.v` - score 4 (synthesis+observation)

**Countable choice without AC: ℕ's canonical least-witness selector for decidable families**

- **Topic.** For a decidable P:ℕ→bool the LEAST witness is a canonical axiom-free selector (nat_least); hence countable choice for decidably-nonempty families is free, and the choice is the MINIMAL valid one (canonicity = determinism).
- **Role.** Vein B, countable level — bridges DecidableSelection.first_witness (finite) off finite carriers. Self-contained (ConstructiveEpsilon). Foundation for CountableDependentChoiceFree. Concurrent (H49).
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib: ConstructiveEpsilon PeanoNat Bool Arith Lia
- **E/R/R.** _Elements:_ ℕ — счётный носитель; разрешимый предикат P / семейство Q. _Roles:_ наименьший свидетель / функция выбора — роль, назначаемая правилом; «наименьший» = канонично (одна селекция, не свобода). _Rules:_ разрешимый тест + порядок ℕ РАЗРЕШАЮТ выбор: наименьший = первый прошедший (L5). _P4:_ счётный РАЗРЕШИМЫЙ выбор — Element-сторона: детерминирован, канонический наименьший, 0 акс; неразрешимое семейство ⟹ AC = role-limit (завершённый choice-граф, P4-запрещён).
- **Classical counterpart.** Countable Choice (AC-omega) and constructive epsilon (Bishop; ConstructiveEpsilon.epsilon_smallest) are classical; NEW is the decidable-countable-choice packaging, canonicity (minimal valid choice), and the finite->countable bridge.
- **Tags.** no-AC, countable-choice, vein-B, least-witness, deterministic, P4
- **Notes.** Header STATUS says 6 Qed; actual Qed count = 7 (geq_family_nonempty added). Drift flagged.

**Lemmas (8):**

| name | kind | role |
|---|---|---|
| `nat_least` | Lemma | ★ разрешимый P над ℕ с свидетелем имеет НАИМЕНЬШИЙ свидетель (канонич. ε для ℕ, 0 акс) |
| `dec_family_choice` | Definition | функция выбора: i ↦ наименьший n с Q i n |
| `dec_family_choice_correct` | Lemma | ★★ функция выбора попадает в каждое множество — счётный выбор без аксиомы |
| `dec_family_choice_least` | Lemma | каждое значение — наименьший свидетель своего множества |
| `dec_family_choice_canonical` | Lemma | ★★ выбор правила = МИНИМАЛЬНЫЙ валидный: для любого g, choice i ≤ g i |
| `geq_family_nonempty` | Lemma | семейство {n: i≤n} разрешимо непусто |
| `geq_family_choice_correct` | Example | его выбор попадает в каждое множество (наименьший n≥i) |
| `countable_selection_free` | Theorem | капстоун: селектор + счётный выбор + каноничность |

**Key lemmas (deep):**

- **`nat_least`** - Канонический селектор ℕ: разрешимый предикат с хоть одним свидетелем имеет НАИМЕНЬШИЙ (через epsilon_smallest). Порядок + разрешимый тест разрешают выбор без оракула — это конструктивный ε и ядро всей вены B на счётном уровне (first_witness расширен с конечных списков на ℕ). _(least-witness, constructive-epsilon, vein-B)_
- **`dec_family_choice_canonical`** - Удар «без свободного выбора»: выбор правила — МИНИМАЛЬНЫЙ валидный (choice i ≤ g i для любой валидной g). Значит селекция ОПРЕДЕЛЕНА правилом (наименьший), а не выбрана свободно — ровно одна правило-селекция. Превращает «счётный выбор» из аксиомы в теорему о детерминированной функции. _(canonicity, determinism, no-AC)_

**Uniqueness - score 4 (synthesis+observation).** Счётный выбор для разрешимых семейств СВОБОДЕН (0 акс) через канонический наименьший свидетель; каноничность = детерминизм (минимальный валидный выбор). Мост finite→countable вены B.
> _Caveat:_ Конструктивный ε стандартен; вклад — упаковка decidable-countable-choice, её каноничность и мост. Параллельный поток (не мой). Заголовок указывает 6 Qed, фактически 7.

---

## #102 - `src/cs/DecidableKonig.v` - score 4 (synthesis+observation)

**König's lemma without choice on the decidable side: deterministic infinite path**

- **Topic.** Localizes the choice-content of König's lemma: given a DECIDABLE infiniteness test + the finitely-branching pigeonhole step, the infinite path is built deterministically (always the first infinite child, via first_witness) — 0 axioms, no AC/DC/WKL.
- **Role.** Vein B, König/WKL level. Builds on cs.DecidableSelection (first_witness). Bundled by SelectionWithoutChoiceSynthesis. Concurrent (H51). Self-claims a decidable König as new-in-repo.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: List PeanoNat; cs.DecidableSelection
- **E/R/R.** _Elements:_ конечно-ветвящееся дерево children; разрешимый флаг inf_b; узлы-ℕ; каждая конечная стадия пути актуальна. _Roles:_ путь = role-limit (незавершённая ветвь); next = наименьший бесконечный ребёнок (роль по правилу «первый»). _Rules:_ konig_step + разрешимый inf_b ⟹ first_witness детерминированно берёт ребёнка ⟹ путь без выбора. _P4:_ König Element-сторона при РАЗРЕШИМОМ inf (детерминир. путь, 0 акс); классическое содержание (pigeonhole) локализовано в гипотезе konig_step; без разрешимости — WKL/выбор (role-limit).
- **Classical counterpart.** Koenig's lemma and Weak Koenig's Lemma (WKL, reverse mathematics) are classical; NEW is the explicit decidable-side path extraction localizing the AC-content to the pigeonhole step (0 axioms).
- **Tags.** no-AC, konig, WKL, vein-B, deterministic, tree, P4

**Lemmas (11):**

| name | kind | role |
|---|---|---|
| `next` | Definition | детерминированный преемник: первый бесконечный ребёнок (first_witness) |
| `next_spec` | Lemma | под konig_step next берёт настоящего бесконечного ребёнка |
| `path` | Fixpoint | траектория next от корня |
| `path_inf` | Lemma | каждый узел пути бесконечен (индукция через konig_step) |
| `path_edge` | Theorem | ★★ König: из бесконечного корня — бесконечный путь из настоящих рёбер, без AC/DC/WKL |
| `path_unique` | Lemma | ★ путь единствен/детерминирован: правило пришпиливает ТУ ветвь |
| `bin_children` | Definition | полное бинарное дерево (2x+1, 2x+2) |
| `bin_konig_step` | Lemma | каждый узел бесконечен, шаг König = первый ребёнок |
| `bin_path_values` | Example | путь от корня по левым детям: 1, 3, 7 (vm_compute) |
| `bin_path_edge` | Example | каждый шаг — настоящее ребро (König инстанцирован, 0 акс) |
| `decidable_konig` | Theorem | капстоун: путь-рёбра + единственность |

**Key lemmas (deep):**

- **`path_edge`** - König без выбора: из бесконечного корня строится бесконечный путь, каждый шаг — настоящее ребро дочернего списка, БЕЗ AC/DC/WKL. Локализация: всё choice-содержание König'а — в гипотезе konig_step (pigeonhole) и в РАЗРЕШИМОСТИ inf, а не в извлечении пути. Это вершина вены B (König = «слабый выбор» в обратной математике). _(konig, no-WKL, vein-B, AC-localization)_
- **`path_unique`** - Та же подпись детерминизма, что у dc_chain_unique/path_unique: правило (first-infinite-child) задаёт ЕДИНСТВЕННУЮ ветвь — нет выбора среди детей. Делает «König-путь» теоремой о функции, а не результатом выбора. _(uniqueness, determinism)_

**Uniqueness - score 4 (synthesis+observation).** Извлечение пути канонической теоремы слабого выбора (König/WKL) — Element-сторона, как только бесконечность РАЗРЕШИМА; AC-содержание локализовано в pigeonhole-шаге. Вершина вены B.
> _Caveat:_ WKL/обратная математика хорошо изучены; угол — явная формализация разрешимой стороны + локализация цены AC. Заголовок сам помечает «новая теорема (decidable König)» + синтез. Параллельный поток (не мой).

---

## #103 - `src/cs/DecidableSelection.v` - score 4 (synthesis+observation)

**Finite selection without AC: first_witness — a decidable existential yields a computable witness**

- **Topic.** The finite base of vein B: a decidable existential over a list returns the FIRST witness (sound, complete, leftmost), giving decidable_list_choice; plus deterministic trajectories of a step function (unique, an R-chain).
- **Role.** Vein B foundation (finite level). Reused by CountableSelectionFree, DecidableKonig, SelectionWithoutChoiceSynthesis. Generalises the EVT_idx argmax-by-index idea.
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib: List PeanoNat Bool
- **E/R/R.** _Elements:_ конечный список-носитель; разрешимый предикат P; шаг-функция. _Roles:_ первый свидетель = роль по правилу (первый прошедший); траектория = детерминированная роль-цепь. _Rules:_ разрешимый ∃ над списком ⟹ вычислимый свидетель; порядок списка делает выбор «первым». _P4:_ конечный выбор — Element-сторона: детерминированный first_witness, 0 акс; основа лестницы, на которую опираются счётный/зависимый/König уровни.
- **Classical counterpart.** Constructive choice over finite sets is standard; NEW is first_witness as the leftmost-canonical finite selector (generalizing EVT_idx argmax-by-index) - the axiom-free root of the no-AC ladder.
- **Tags.** no-AC, finite-choice, vein-B, leftmost, argmax-by-index, P4

**Lemmas (9):**

| name | kind | role |
|---|---|---|
| `first_witness` | Fixpoint | первый элемент списка, проходящий P (option) |
| `first_witness_sound` | Lemma | если вернул x, то x в списке и P x |
| `first_witness_complete` | Lemma | если свидетель есть, вернёт Some (не None) |
| `first_witness_first` | Lemma | возвращает ЛЕВЫЙ свидетель (все до него — не-P) |
| `decidable_list_choice` | Lemma | ★ разрешимый выбор над списком: {x\|In x l/\P x} + {все не-P} |
| `first_gt5` | Example | первый элемент >5 в конкретном списке |
| `trajectory` | Fixpoint | итерация шаг-функции от состояния |
| `trajectory_unique` | Lemma | детерминированная траектория единственна |
| `trajectory_is_R_chain` | Lemma | соседние состояния связаны шаг-отношением |

**Key lemmas (deep):**

- **`decidable_list_choice`** - Конечная база вены B: разрешимый экзистенциал над списком ДАЁТ вычислимого свидетеля (или доказательство, что все не подходят) — сумма-тип {x\|...}+{...}, не голое ∃. Это обобщение argmax-by-index из EVT_idx: «ищи позицию, не значение» делает выбор детерминированным и Leibniz-разрешимым. Корень, который CountableSelectionFree/DecidableKonig поднимают на бесконечные носители. _(finite-choice, vein-B, computable-witness)_
- **`first_witness_first`** - Леммa о ЛЕВИЗНЕ: выбранный свидетель — первый по порядку списка (все предшествующие не-P). Это конституирующий L5-порядок, делающий выбор каноническим, а не произвольным — та же идея, что «наименьший» у nat_least. _(leftmost, L5-order, canonical)_

**Uniqueness - score 4 (synthesis+observation).** Конечный детерминированный выбор-как-теорема (first_witness, левый свидетель), обобщающий argmax-by-index; аксиомо-свободный корень всей лестницы выбора без AC.
> _Caveat:_ Линейный поиск свидетеля тривиален; распознаётся как корень, на котором держится систематическая безаксиомная замена выбора по всей вене B.

---

## #104 - `src/cs/HaltingRoleLimit.v` - score 4 (synthesis+observation)

**Halting as Element (bounded, decidable) vs role-limit (unbounded); the negb diagonal seed**

- **Topic.** The branch foundation: an abstract machine (run/halts_in/halts/diverges), bounded halting DECIDABLE (Element/P4), the negb-no-fixpoint diagonal, Cantor-no-surjection, and no_halting_decider (the role-limit).
- **Role.** FOUNDATION reused by ~all cs files (negb_no_fixpoint, bounded_halting_decidable, run/halts). The Element/role-limit split made concrete.
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** Stdlib: PeanoNat Bool
- **E/R/R.** _Elements:_ конфигурации Config; ограниченные прогоны run n c; конкретные машины (countdown, incr). _Roles:_ halts_in = роль-в-бюджете (P4); halts/diverges = role-limit-завершения; решатель D = роль-оракул. _Rules:_ run = «прогон k шагов, затем, может, ещё шаг»; halted-статус; negb b ≠ b — семя диагонали. _P4:_ ОГРАНИЧЕННАЯ остановка РАЗРЕШИМА (Element); безграничная — role-limit; тотальный halting-решатель = реификация role-limit в Element = категориальная ошибка (no_halting_decider).
- **Classical counterpart.** Turing's halting theorem and Cantor's diagonal (negb has no fixpoint) are classical; NEW is the bounded(Element)/unbounded(role-limit) split and the negb-seed as the repo's single shared diagonal root.
- **Tags.** halting, diagonal, decidable, role-limit, P4, foundation, vein-E

**Lemmas (19):**

| name | kind | role |
|---|---|---|
| `run` | Fixpoint | прогон n шагов машины от конфигурации |
| `halts_in` | Definition | halted (run n c) = true — остановка в бюджете n |
| `halts` | Definition | exists n, halts_in n c — role-limit-завершение |
| `diverges` | Definition | forall n, не остановилась |
| `run_S` | Lemma | разворот рекурсии run (S n) |
| `run_absorb` | Lemma | после остановки прогон стабилен |
| `halts_in_S` | Lemma | остановка в n ⟹ в (S n) |
| `halts_in_mono` | Lemma | монотонность остановки по бюджету |
| `bounded_halting_decidable` | Lemma | ★ Element: ограниченная остановка РАЗРЕШИМА (любой n, c) |
| `halts_not_diverges` | Lemma | halts и diverges несовместны |
| `countdown_halts` | Example | счётчик останавливается |
| `incr_diverges` | Example | инкремент расходится |
| `negb_no_fixpoint` | Lemma | ★ b ≠ negb b — СЕМЯ всех диагоналей репо |
| `cantor_no_surjection` | Theorem | ★ нет сюръекции A→(A→bool) (Кантор из negb) |
| `Decides` | Definition | D решает halting на самоприменении |
| `SelfProgrammable` | Definition | домен допускает диагональную программу |
| `no_halting_decider` | Theorem | ★ нет тотального halting-решателя (role-limit) |
| `no_total_halting_oracle` | Corollary | следствие: тотальный оракул невозможен |
| `decidable_implies_not_self_programmable` | Corollary | разрешимость ⟹ нет диагонали (контрапозиция) |

**Key lemmas (deep):**

- **`bounded_halting_decidable`** - Element-сторона границы: для любого бюджета n и конфигурации c вопрос «остановилась ли за n шагов» РАЗРЕШИМ (булев halted после run n). P4 в чистом виде: бесконечность — свойство процесса перебора, не объекта; каждое конечное наблюдение актуально и разрешимо. Переиспользуется как cm_bounded_decidable и в ScaleFlow. _(element, decidable, P4, foundation)_
- **`negb_no_fixpoint`** - Семя: булево отрицание не имеет неподвижной точки (b ≠ negb b), доказывается разбором случаев. Это ЕДИНСТВЕННЫЙ диагональный факт, к которому сводятся Кантор, halting, Райс, Колмогоров, Тарский, Рассел — позже все опознаны как инстансы Ловера. Минимальный корень вены E. _(diagonal, seed, vein-E)_
- **`no_halting_decider`** - Role-limit-сторона: при наличии диагональной программы (SelfProgrammable) ни один тотальный D не решает self-halting. Категориальная ошибка реификации role-limit в Element-решатель, запрещённая той же negb-диагональю. Контрапозиция (decidable_implies_not_self_programmable) связывает с Element-стороной. _(halting, role-limit, diagonal)_

**Uniqueness - score 4 (synthesis+observation).** Halting расщеплён на Element (ограниченное, разрешимое, P4) и role-limit (безграничное); negb-семя как единый корень всех диагоналей репо; хаб переиспользования всей ветки.
> _Caveat:_ Неразрешимость halting и диагональ Кантора классичны (Тьюринг/Кантор). Вклад — E/R/R/P4-обрамление + роль корня-хаба, а не сами факты.

---

## #105 - `src/cs/KolmogorovRoleLimit.v` - score 4 (synthesis+observation)

**Kolmogorov complexity as the FOURTH face: incompressibility (Element) + uncomputable complexity (role-limit)**

- **Topic.** Two views of the same E/R/R act: budget-describability with incompressibility by pure counting (Element), and the complexity boundary as RoleLimitDrawn — an instance of diagonal_defeats_decider (Berry/Chaitin). The fourth face of the boundary.
- **Role.** Bridge toward information (Part XVI). Imports HaltingRoleLimit, BoundaryDecidability; extends one_boundary_three_faces → one_boundary_four_faces. Concurrent-workstream file.
- **Counts.** Qed 5 / Admitted 0 / axioms 0
- **Imports.** Stdlib: PeanoNat Bool Lia; cs.HaltingRoleLimit; cs.BoundaryDecidability
- **E/R/R.** _Elements:_ программы-коды (nat) и объекты (nat); декомпрессор decode. _Roles:_ desc_within = бюджет-роль (P4); Complex = роль-ПРЕДЕЛ (K = минимум по ВСЕМ программам, не Element-объект); решатель = роль-оракул. _Rules:_ desc_within x n — описуемость в бюджете n; диагональ Берри/Чейтина = та же b ≠ negb b. _P4:_ ограниченная описуемость — Element (коротких программ конечно, потому incompressible_exists); невычислимость сложности — role-limit (та же диагональ, что halting/Cantor); K модель-относительна.
- **Classical counterpart.** Kolmogorov complexity, incompressibility-by-counting, and Berry/Chaitin uncomputability are classical; NEW is K as the fourth face = an instance of the shared diagonal, with honest model-relativity (no invariance theorem claimed).
- **Tags.** kolmogorov, incompressibility, diagonal, role-limit, four-faces, information, P4

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `desc_within` | Definition | x описуем в бюджете n: ∃ программа ≤ n, decode = x |
| `maxd` | Fixpoint | наибольший объект от программ ≤ n (конечный скан) |
| `decode_le_maxd` | Lemma | образ [0..n] ограничен maxd n |
| `incompressible_exists` | Theorem | ★ Element/счёт: при каждом бюджете НЕКОТОРЫЙ объект несжимаем |
| `kolmogorov_role_limit_drawn` | Theorem | ★ Complex с диагональю ⟹ RoleLimitDrawn (инстанс diagonal_defeats_decider) |
| `complexity_decidable_no_diagonal` | Corollary | контрапозиция: ElementDrawn Complex ⟹ нет диагонали |
| `one_boundary_four_faces` | Theorem | ★ число/программа/множество/СЛОЖНОСТЬ — четыре грани, один движок |

**Key lemmas (deep):**

- **`incompressible_exists`** - Element-сторона чистым счётом: при бюджете n коротких программ КОНЕЧНО (образ [0..n]), поэтому объект S(maxd n) не описуем в n — несжимаем. 0 аксиом, pigeonhole. Честно: машинная инвариантность K НЕ заявляется — K модель-относительна, что и есть честный охват. _(incompressibility, counting, element)_
- **`one_boundary_four_faces`** - Расширяет one_boundary_three_faces четвёртой гранью: сложность (Колмогоров) присоединяется к числу/программе/множеству, все role-limit-грани движимы единственной negb-диагональю (корень — Ловер). Колмогоров опознан как ИНСТАНС diagonal_defeats_decider — то же ядро, что halting и Кантор, а не отдельный результат. _(four-faces, synthesis, unification)_

**Uniqueness - score 4 (synthesis+observation).** Колмогоров — ЧЕТВЁРТАЯ грань одной границы: несжимаемость = Element (счёт), невычислимость сложности = role-limit как ИНСТАНС универсального движка diagonal_defeats_decider; мост к теории информации.
> _Caveat:_ Несжимаемость (счёт) и Берри/Чейтин классичны; K здесь модель-относительна (инвариантность к машине НЕ заявлена) — честно помечено. Параллельный поток (не мой).

---

## #106 - `src/cs/LambdaGrounding.v` - score 3 (methods)

**Grounding halting in a real de Bruijn λ-machine: Ω diverges, (λx.x)(λx.x) halts**

- **Topic.** A concrete untyped λ-calculus (de Bruijn lift/subst/call-by-name step) instantiating the abstract halting machine: Ω=(λx.xx)(λx.xx) genuinely steps to itself and diverges; a real halting term; bounded halting decidable.
- **Role.** Makes the abstract Section-machines of HaltingRoleLimit concrete in an actual computation model. Imported by LambdaRecursion, SemanticRecursion.
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib: PeanoNat; cs.HaltingRoleLimit (run/halts/diverges)
- **E/R/R.** _Elements:_ термы Term (Var/Lam/App де Брёйна); конкретные omega/Omega/id_term/halt_term. _Roles:_ step = L5-правило редукции; haltedT = статус-роль; Omega = role-limit-обитатель (расходится). _Rules:_ lift/subst/step (call-by-name); haltedT через отсутствие шага. _P4:_ настоящая машина несёт обе стороны: halt_term останавливается (Element), Omega расходится (role-limit) — абстрактный halting заземлён в реальном λ.
- **Classical counterpart.** Church's untyped lambda-calculus and Omega=(\x.xx)(\x.xx) divergence are textbook; NEW is only grounding the abstract halting machine in a concrete de Bruijn reducer.
- **Tags.** lambda-calculus, de-bruijn, divergence, grounding, halting

**Lemmas (17):**

| name | kind | role |
|---|---|---|
| `Term` | Inductive | untyped λ де Брёйна: Var/Lam/App |
| `lift` | Fixpoint | сдвиг индексов де Брёйна |
| `subst` | Fixpoint | подстановка по индексу |
| `step` | Fixpoint | одношаговая call-by-name редукция (option Term) |
| `stepT` | Definition | тотализованный шаг (id при остановке) |
| `haltedT` | Definition | статус: нет шага = halted |
| `omega` | Definition | λx. x x |
| `Omega` | Definition | (λx.xx)(λx.xx) — расходящийся комбинатор |
| `step_Omega` | Lemma | ★ step Omega = Some Omega (vm_compute) |
| `haltedT_Omega` | Lemma | Omega не остановлена |
| `stepT_Omega` | Lemma | stepT Omega = Omega |
| `run_Omega` | Lemma | любой прогон Omega = Omega |
| `diverges_Omega` | Lemma | ★ Omega расходится в смысле HaltingRoleLimit.diverges |
| `id_term` | Definition | λx. x |
| `halt_term` | Definition | (λx.x)(λx.x) → λx.x |
| `halt_term_halts` | Lemma | halt_term останавливается |
| `halting_within_decidable` | Lemma | ограниченная остановка λ-терма разрешима |

**Key lemmas (deep):**

- **`diverges_Omega`** - Заземление role-limit-стороны: Omega РЕАЛЬНО расходится в конкретной λ-машине — step Omega = Some Omega (vm_compute), значит run n Omega = Omega для всех n, значит diverges по определению HaltingRoleLimit. Не абстрактная Section-машина, а настоящая редукция: даёт онтологическую опору всей ветке. _(divergence, lambda, grounding, role-limit)_
- **`halting_within_decidable`** - Element-сторона на реальном λ: ограниченная остановка терма разрешима — переносит bounded_halting_decidable на конкретный stepT/haltedT. Подтверждает, что заземление сохраняет Element-разрешимость. _(element, decidable, lambda)_

**Uniqueness - score 3 (methods).** Абстрактный halting заземлён в РЕАЛЬНОЙ de-Bruijn λ-машине: Ω вычислимо расходится, halt_term останавливается — обе стороны границы в настоящей редукции, не в Section-абстракции.
> _Caveat:_ Бестиповое λ-исчисление и Ω/Y стандартны; ценность — онтологическое заземление cs-абстракций, а не новая теория.

---

## #107 - `src/cs/LambdaRecursion.v` - score 3 (methods)

**The Y-combinator in the real machine: step (fixpoint f) = Some (App f (fixpoint f))**

- **Topic.** Constructs the Y/Curry fixpoint combinator in the grounded λ-machine and proves it actually unfolds: for closed f, fixpoint f steps to f (fixpoint f). Supporting well-scopedness lemmas (wf/closed, lift/subst invariance).
- **Role.** Vein-E/grounding: realises recursion in the actual machine (the constructive counterpart to Kleene/Lawvere recursion). Imports cs.LambdaGrounding.
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** Stdlib; cs.LambdaGrounding (Term/step/lift/subst)
- **E/R/R.** _Elements:_ термы; well-scoped предикат wf k t; Wf/fixpoint-конструкции. _Roles:_ fixpoint = роль-самопорождение (рекурсия как процесс); wf = роль-корректность области индексов. _Rules:_ Wf f = λx. f (x x); fixpoint f = (Wf f)(Wf f); шаг разворачивает рекурсию. _P4:_ рекурсия — процесс саморазворачивания, не завершённый объект: Y_step2 показывает ОДИН разворот, бесконечность — в итерации шага.
- **Classical counterpart.** Curry's Y / fixed-point combinator is textbook; NEW is only its operational verification in the grounded machine, linking to the categorical recursion theorem.
- **Tags.** Y-combinator, lambda-calculus, recursion, fixpoint, de-bruijn

**Lemmas (12):**

| name | kind | role |
|---|---|---|
| `wf` | Fixpoint | well-scoped: все индексы < k |
| `closed` | Definition | wf 0 t — замкнутый терм |
| `wf_mono` | Lemma | монотонность wf по границе |
| `lift_wf` | Lemma | lift не меняет well-scoped терм |
| `subst_wf` | Lemma | subst не меняет well-scoped терм |
| `lift_closed` | Lemma | lift 0 замкнутого = он сам |
| `subst_closed` | Lemma | подстановка в замкнутый = он сам |
| `Wf` | Definition | λx. f (x x) — половина Y |
| `fixpoint` | Definition | (Wf f)(Wf f) — неподвижная точка f |
| `Y_step2` | Lemma | ★ для closed f: step (fixpoint f) = Some (App f (fixpoint f)) |
| `Yc` | Definition | замкнутый Y-комбинатор как терм |
| `Y_step1` | Lemma | step (App Yc f) = Some (fixpoint f) |

**Key lemmas (deep):**

- **`Y_step2`** - Y-комбинатор РАЗВОРАЧИВАЕТСЯ в настоящей машине: для замкнутого f шаг от fixpoint f даёт App f (fixpoint f) — то есть f применяется к собственной неподвижной точке. Конструктивный двойник теоремы рекурсии Клини (которая в RecursionTheorem.v выводится как инстанс Ловера): здесь та же рекурсия реализована операционно, а не аксиоматически. _(Y-combinator, fixpoint, recursion, lambda)_
- **`subst_wf`** - Несущая лемма гигиены де Брёйна: подстановка в well-scoped терм его не меняет за границей — без неё Y_step1/Y_step2 не считаются. Типичный «скучный, но load-bearing» хелпер, который база честно отмечает как scaffolding. _(well-scoped, de-bruijn, scaffolding)_

**Uniqueness - score 3 (methods).** Y-комбинатор построен и ОПЕРАЦИОННО проверен в заземлённой λ-машине (разворачивается в f(Yf)) — конструктивная реализация рекурсии, двойник Kleene/Lawvere-вывода.
> _Caveat:_ Y-комбинатор и его разворот — учебная классика; ценность — операционное заземление и стыковка с RecursionTheorem.

---

## #108 - `src/cs/LawvereFixedPoint.v` - score 5 (synthesis+observation)

**Lawvere's fixed-point theorem — the categorical ROOT of every diagonal in the repo**

- **Topic.** Proves Lawvere's fixed-point theorem (a point-surjection forces every endo a fixed point) and shows the cs diagonals (Cantor, ℕ→ℕ non-enumerable) are its instances — identifying the single root under all role-limits.
- **Role.** ROOT of vein E. Imports cs.HaltingRoleLimit. Feeds RecursionTheorem (Kleene=Lawvere), TarskiUndefinability, RussellViaLawvere.
- **Counts.** Qed 5 / Admitted 0 / axioms 0
- **Imports.** Stdlib; cs.HaltingRoleLimit (negb_no_fixpoint)
- **E/R/R.** _Elements:_ типы A, B; точка-сюръекция φ: A→(A→B); эндо-функции f: B→B. _Roles:_ point_surjective = роль-универсальность (всё представимо); неподвижная точка = вынужденная роль. _Rules:_ если φ точка-сюръективна, то любой f имеет неподвижную точку f b = b — диагональная конструкция. _P4:_ корень всех role-limit-граней: реификация role-limit (тотальный решатель/сюръекция) сталкивается с диагональю Ловера; negb — частный случай при B=bool, f=negb.
- **Classical counterpart.** Lawvere's fixed-point theorem (1969) is classical; NEW is nothing in the theorem itself but the systematic identification of THIS repo's diagonals (Cantor/halting/Rice/Tarski/Russell) as its instances.
- **Tags.** lawvere, fixpoint, diagonal, root, vein-E, unification

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `point_surjective` | Definition | φ: A→(A→B) точечно покрывает все f: A→B |
| `lawvere_fixed_point` | Theorem | ★ точка-сюръекция ⟹ всякий f: B→B имеет неподвижную точку |
| `lawvere_no_point_surjection` | Corollary | если у f нет неподвижной точки, нет точка-сюръекции |
| `cantor_via_lawvere` | Corollary | Кантор как инстанс (B=bool, f=negb) |
| `nat_fun_not_enumerable` | Corollary | ℕ→ℕ не перечислимо (инстанс с f=succ) |
| `cs_diagonals_are_lawvere` | Theorem | ★ диагонали ветки опознаны как инстансы Ловера |

**Key lemmas (deep):**

- **`lawvere_fixed_point`** - Корень: точка-сюръекция φ: A→(A→B) заставляет любой эндо f: B→B иметь неподвижную точку (диагональ a₀ с φ a₀ = λa. f(φ a a)). Доказательство в одну строку через f_equal. Контрапозиция (f без неподвижной точки, напр. negb) даёт ВСЕ диагонали — Кантор, halting, Райс, Тарский, Рассел становятся следствиями одной теоремы 1969 года. _(lawvere, fixpoint, root, vein-E)_
- **`cs_diagonals_are_lawvere`** - Явное опознание: диагонали ветки (negb_no_fixpoint, cantor_no_surjection) — инстансы Ловера, а не независимые трюки. Это и есть унификация вены E: «одна диагональ» получает категориальный корень, превращая россыпь несвязанных невозможностей в одну структуру. _(unification, diagonal, synthesis)_

**Uniqueness - score 5 (synthesis+observation).** Единый категориальный КОРЕНЬ (Ловер) всех диагоналей репо: Кантор/halting/Райс/Тарский/Рассел опознаны как инстансы одной теоремы о неподвижной точке.
> _Caveat:_ Теорема Ловера классична (1969), доказательство тривиально. Уникальность — в систематической унификации ИМЕННО диагоналей этого репо под ней (вена E), а не в самой теореме.

---

## #109 - `src/cs/PumpingPigeonhole.v` - score 2 (methods)

**Discharging the pumping hypothesis via pigeonhole: a^n b^n needs no assumption**

- **Topic.** Proves the DFA-prefix collision (two distinct a^i, a^j reach the same state) by pigeonhole over the finite state set, turning no_dfa_for_anbn into the unconditional no_dfa_for_anbn_unconditional.
- **Role.** Tightening of PumpingRoleLimit (removes its collision hypothesis). Used by ChomskyHierarchy. Reuses RegularElementFloor.run.
- **Counts.** Qed 4 / Admitted 0 / axioms 0
- **Imports.** Stdlib: List PeanoNat; cs.RegularElementFloor; cs.PumpingRoleLimit
- **E/R/R.** _Elements:_ конечное множество состояний; префиксы word_a n; их образы под run. _Roles:_ коллизия состояний = вынужденная роль (голубятня); состояние = конечная память-роль. _Rules:_ среди \|Q\|+1 префиксов два дают одно состояние (pigeonhole) ⟹ pump. _P4:_ конечность памяти (Element-пол) ВЫНУЖДАЕТ коллизию — несрегулярность a^n b^n получается без гипотез, прямо из конечности.
- **Classical counterpart.** The pigeonhole principle and the pumping lemma are classical; NEW is only discharging the pumping hypothesis to make a^n b^n unconditional.
- **Tags.** pigeonhole, pumping, regular, automata, unconditional

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `gpref` | Definition | состояние после прочтения word_a n |
| `seq_nodup_local` | Lemma | seq не содержит дубликатов |
| `map_collision` | Lemma | отображение длинного списка в конечный ⟹ коллизия |
| `gpref_collision` | Lemma | ∃ i≠j с одинаковым состоянием-префиксом |
| `no_dfa_for_anbn_unconditional` | Theorem | ★ {a^n b^n} не распознаётся DFA — БЕЗ гипотез |

**Key lemmas (deep):**

- **`no_dfa_for_anbn_unconditional`** - Снимает гипотезу коллизии из PumpingRoleLimit: по голубятне над конечным Q два различных префикса a^i, a^j (i≠j) приводят в одно состояние, дальше pump_preserves даёт противоречие с балансом. Безусловная несрегулярность — финальный кирпич строгого включения regular ⊊ context-free. _(pigeonhole, pumping, unconditional)_
- **`map_collision`** - Чистая комбинаторная голубятня: отображение списка длиннее \|codomain\| в конечный тип даёт два индекса с равными образами. Переиспользуемый хелпер, локализующий «конечность памяти ⟹ коллизия». _(pigeonhole, finite, helper)_

**Uniqueness - score 2 (methods).** Безусловная несрегулярность a^n b^n: pumping-гипотеза разряжена голубятней над конечным множеством состояний.
> _Caveat:_ Классическая голубятня/pumping; ценность — аккуратное снятие гипотезы для строгого включения в ChomskyHierarchy.

---

## #110 - `src/cs/PumpingRoleLimit.v` - score 3 (new-framing)

**a^n b^n is not regular: the role-limit just above the Element floor**

- **Topic.** The pumping argument via letter-counting (cF/cT): pumping a loop preserves DFA acceptance but breaks the a/b balance, so {a^n b^n} escapes any finite-memory DFA — the first role-limit above the regular Element floor.
- **Role.** Phase-3 role-limit step. Provides word_a/word_b/In_L reused by PumpingPigeonhole and ChomskyHierarchy. Reuses RegularElementFloor.
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: List PeanoNat; cs.RegularElementFloor
- **E/R/R.** _Elements:_ слова над {a,b}; word_a/word_b; счётчики cF/cT. _Roles:_ язык {a^n b^n} = role-limit (требует неограниченной памяти-счёта); петля-pump = роль повторения. _Rules:_ repeat петли сохраняет принятие DFA; cF/cT считают буквы; баланс i=j. _P4:_ конечная память (Element) НЕ держит баланс a^n b^n — это role-limit над полом: бесконечность счёта не реифицируется в конечное состояние.
- **Classical counterpart.** The pumping lemma for regular languages (a^n b^n not regular) is classical; NEW is only the 'first role-limit above the Element floor' framing.
- **Tags.** pumping, non-regular, automata, role-limit, counting

**Lemmas (17):**

| name | kind | role |
|---|---|---|
| `repeat_word` | Fixpoint | k-кратное повторение слова |
| `loop_pump` | Lemma | петля состояния повторяется при pump |
| `pump_preserves` | Lemma | ★ pump сохраняет принятие/отвержение DFA |
| `word_a` | Definition | a^n = repeat false n |
| `word_b` | Definition | b^n = repeat true n |
| `In_L` | Definition | {w : ∃n, w = a^n b^n} |
| `cF` | Definition | число a (false) в слове |
| `cT` | Definition | число b (true) в слове |
| `cF_app` | Lemma | cF аддитивен по конкатенации |
| `cF_a` | Lemma | cF(a^n)=n |
| `cF_b` | Lemma | cF(b^n)=0 |
| `cT_app` | Lemma | cT аддитивен |
| `cT_a` | Lemma | cT(a^n)=0 |
| `cT_b` | Lemma | cT(b^n)=n |
| `anbn_balanced` | Lemma | In_L(a^j b^i) ⟹ i=j (баланс) |
| `collision_contradicts` | Theorem | коллизия состояний ⟹ противоречие с балансом |
| `no_dfa_for_anbn` | Theorem | ★ нет DFA для {a^n b^n} (при гипотезе коллизии) |

**Key lemmas (deep):**

- **`pump_preserves`** - Сердце pumping-леммы: если чтение петли возвращает DFA в то же состояние, то вставка любого числа копий петли не меняет принятие. Формализует «конечная память не различает число прокруток» — операционная причина, почему счётный баланс a^n b^n недостижим конечным автоматом. _(pumping, invariance, role-limit)_
- **`no_dfa_for_anbn`** - Role-limit над Element-полом: при коллизии состояний (later безусловной в PumpingPigeonhole) pump ломает баланс i=j, противореча anbn_balanced. Первый строгий шаг лестницы Хомского: конечная память (регулярный Element) строго слабее стека. _(non-regular, role-limit, separation)_

**Uniqueness - score 3 (new-framing).** Несрегулярность a^n b^n переосмыслена как первый role-limit над регулярным Element-полом (счётный баланс не реифицируется в конечную память).
> _Caveat:_ Pumping-лемма и счёт букв — стандарт теории автоматов; ново только обрамление Element/role-limit.

---

## #111 - `src/cs/PvsNP_Framing.v` - score 2 (new-framing)

**P vs NP as an Element/role-limit framing (NOT a proof): bounded NP-search is decidable**

- **Topic.** Frames verification as Element (a decidable check) and NP as bounded search: bounded NP-search is decidable, P⊆NP. Explicitly a framing exercise — the barriers (relativization etc.) are in comments, no resolution claimed.
- **Role.** Honest framing file. Self-contained. Marks the limit of the Element/role-limit angle: it organises P/NP, does not decide it.
- **Counts.** Qed 4 / Admitted 0 / axioms 0
- **Imports.** Stdlib
- **E/R/R.** _Elements:_ входы Input; сертификаты Cert; верификатор v; решатель dec. _Roles:_ verifies = роль-проверка (Element); in_NP/in_P = роли-классы; поиск = роль-перебор. _Rules:_ verifies v; in_NP = ∃ верификатор; in_P = ∃ решатель; ограниченный поиск разрешим. _P4:_ проверка сертификата — Element (разрешима); НЕОГРАНИЧЕННЫЙ поиск сертификата — role-limit; ограниченный — снова Element (NP_bounded_search_decidable). P vs NP = где именно проходит граница, НЕ решается здесь.
- **Classical counterpart.** P vs NP and the verifier-based NP definition are classical; NEW is NONE as a result - explicitly a framing exercise (bounded search decidable is trivial).
- **Tags.** P-vs-NP, framing, bounded-search, element, role-limit, honest-scope

**Lemmas (9):**

| name | kind | role |
|---|---|---|
| `verifies` | Definition | v корректно проверяет сертификаты |
| `Decider` | Definition | dec решает язык |
| `in_NP` | Definition | ∃ верификатор (Element-проверка + перебор) |
| `in_P` | Definition | ∃ прямой решатель |
| `verification_is_element` | Lemma | проверка сертификата — Element-сторона |
| `P_subset_NP` | Lemma | решатель даёт верификатор: P⊆NP |
| `NP_search_decides` | Lemma | перебор сертификатов решает NP-член при разрешимой области |
| `NP_bounded_search_decidable` | Lemma | ★ ОГРАНИЧЕННЫЙ NP-поиск разрешим (Element) |
| `P_collapses_NP` | Definition | in_NP→in_P как формулируемое утверждение (не доказывается) |

**Key lemmas (deep):**

- **`NP_bounded_search_decidable`** - Точная Element-локализация: ОГРАНИЧЕННЫЙ поиск сертификата (по конечной области) разрешим — verification всегда Element, role-limit входит лишь с НЕОГРАНИЧЕННЫМ перебором. Это весь честный вклад файла: показывает, ГДЕ граница, не сдвигая её. _(bounded-search, element, decidable)_
- **`P_subset_NP`** - Тривиальное P⊆NP (решатель = верификатор, игнорирующий сертификат) — включено как каркас рамки, а не результат. Честность файла: он организует P/NP в язык Element/role-limit, явно НЕ претендуя на разрешение. _(P-subset-NP, framing)_

**Uniqueness - score 2 (new-framing).** P vs NP уложен в язык Element/role-limit (проверка=Element, неограниченный поиск=role-limit), с разрешимостью ограниченного поиска как точкой границы.
> _Caveat:_ ЯВНО не доказательство и не сдвиг барьеров (релятивизация и пр. — в комментариях). Чистое обрамление; над-брендировать нельзя.

---

## #112 - `src/cs/RecursionTheorem.v` - score 4 (synthesis+observation)

**Kleene's recursion theorem as a Lawvere instance; Rice from recursion**

- **Topic.** Derives Kleene's recursion theorem as a direct instance of lawvere_fixed_point (A=B=Prog), then chains it to Rice — exhibiting recursion and Rice as faces of the same fixed-point root.
- **Role.** Vein-E linkage. Imports LawvereFixedPoint, BoundaryDecidability, RiceRoleLimit. Connects the operational Y (LambdaRecursion) to the categorical root.
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** cs.LawvereFixedPoint; cs.BoundaryDecidability; cs.RiceRoleLimit
- **E/R/R.** _Elements:_ программы Prog; самоприменение; неподвижные точки преобразований программ. _Roles:_ теорема рекурсии = роль-самопорождение; Rice-диагональ = роль-предел семантики. _Rules:_ Kleene = Ловер при A=B=Prog; рекурсия ⟹ Rice-диагональ. _P4:_ рекурсия и Rice — грани ОДНОГО корня неподвижной точки; реификация семантики в тотальный решатель запрещена тем же Ловером.
- **Classical counterpart.** Kleene's recursion theorem and its known equivalence to Lawvere are classical; NEW is the explicit in-repo derivation of Kleene as a Lawvere instance and the chain to Rice.
- **Tags.** kleene, recursion-theorem, lawvere, rice, vein-E, synthesis

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `kleene_recursion_from_lawvere` | Theorem | ★ теорема рекурсии Клини = инстанс Ловера (A=B=Prog) |
| `rice_diagonal_from_recursion` | Theorem | из рекурсии — самоотрицающая Rice-диагональ |
| `rice_from_lawvere` | Theorem | ★ Rice выведен по цепочке от Ловера |

**Key lemmas (deep):**

- **`kleene_recursion_from_lawvere`** - Теорема рекурсии Клини получена НЕ отдельным трюком, а как прямой инстанс lawvere_fixed_point при A=B=Prog. Превращает «Kleene ≡ Lawvere» (известный факт) в машинно-проверенную внутрирепозиторную цепочку, стыкуя операционный Y (LambdaRecursion) с категориальным корнем (вена E). _(kleene, lawvere, recursion, instance)_
- **`rice_from_lawvere`** - Замыкает грань: Rice выводится по цепочке рекурсия→диагональ от того же корня Ловера. Демонстрирует, что неразрешимость семантических свойств — не новый принцип, а следствие единой неподвижной точки. _(rice, lawvere, chain)_

**Uniqueness - score 4 (synthesis+observation).** Теорема рекурсии Клини и Rice выведены как инстансы ОДНОГО корня Ловера — машинная стыковка операционной (Y) и категориальной рекурсии.
> _Caveat:_ Эквивалентность Kleene≡Lawvere известна; вклад — явная внутрирепозиторная цепочка от корня к Rice, а не новый результат.

---

## #113 - `src/cs/RegularElementFloor.v` - score 3 (new-framing)

**Regular languages = the decidable Element floor; DFA membership + Boolean closure**

- **Topic.** DFAs as the Element floor: membership is decidable, complement flips acceptance, and the product DFA gives intersection/union closure. The bottom (decidable) rung of the role-limit ladder.
- **Role.** Phase-3 Element floor. Provides run/accepts reused by PumpingRoleLimit, PumpingPigeonhole, ChomskyHierarchy.
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: List Bool
- **E/R/R.** _Elements:_ состояния Q; алфавит Sigma; слова; функция перехода delta. _Roles:_ язык-регулярный = Element-роль (конечная память); accept-предикат = статус-роль. _Rules:_ run = fold_left delta; accepts; произведение автоматов для ∩/∪. _P4:_ регулярные языки — Element-пол: членство РАЗРЕШИМО (конечная память актуальна), булевы операции замкнуты — низшая разрешимая ступень лестницы.
- **Classical counterpart.** DFA theory - decidable membership, product-automaton closure under intersection/union, complement - is classical; NEW is only the 'decidable Element floor' framing.
- **Tags.** automata, regular, decidable, element, floor, boolean-closure

**Lemmas (13):**

| name | kind | role |
|---|---|---|
| `run` | Definition | прогон DFA по слову (fold_left delta) |
| `run_app` | Lemma | run по конкатенации = композиция прогонов |
| `accepts` | Definition | слово принято: acc(run ...) = true |
| `membership_decidable` | Lemma | ★ членство в регулярном языке РАЗРЕШИМО (Element) |
| `complement_spec` | Lemma | дополнение-DFA принимает ⟺ исходный отвергает |
| `dprod` | Definition | переход произведения (Q1×Q2) |
| `run_prod` | Lemma | прогон произведения = пара прогонов |
| `intersection_spec` | Lemma | произведение-DFA даёт пересечение |
| `union_spec` | Lemma | произведение-DFA даёт объединение |
| `parity_delta` | Definition | пример: автомат чётности (xor) |
| `parity_accepts_empty` | Example | пустое слово принято (чётно) |
| `parity_rejects_one` | Example | одна буква отвергнута |
| `parity_accepts_two` | Example | две буквы приняты |

**Key lemmas (deep):**

- **`membership_decidable`** - Определяет Element-пол: членство в регулярном языке разрешимо булевым прогоном DFA — конечная память актуальна и наблюдаема (P4). Контраст с role-limit-ярусами выше (a^n b^n, halting) задаёт всю лестницу Element/role-limit. _(element, decidable, floor)_
- **`intersection_spec`** - Замкнутость регулярного класса под ∩ через произведение автоматов (run_prod). Показывает, что Element-пол — настоящий булев класс, а не отдельные примеры; конструктивный продукт-DFA вычислим. _(closure, product-automaton)_

**Uniqueness - score 3 (new-framing).** Регулярные языки представлены как разрешимый Element-ПОЛ лестницы role-limit'ов (членство разрешимо, булевы операции замкнуты конструктивно).
> _Caveat:_ DFA, произведение автоматов, замкнутость — стандарт; ново обрамление как «Element-пол» под ролевой лестницей.

---

## #114 - `src/cs/RiceRoleLimit.v` - score 3 (new-framing)

**Rice's theorem as Element/role-limit dichotomy: trivial properties decidable, semantic ones not**

- **Topic.** Splits program properties: trivial ones are ElementDrawn (decidable), while a nontrivial SEMANTIC property admits the Rice diagonal against every decider — hence role-limit. No semantic decider.
- **Role.** Vein-E face. Used by RecursionTheorem, SemanticRecursion. Reuses the BoundaryDecidability machinery.
- **Counts.** Qed 4 / Admitted 0 / axioms 0
- **Imports.** Stdlib; cs.BoundaryDecidability (Element/RoleLimit)
- **E/R/R.** _Elements:_ программы Prog; семантическое свойство P; решатели dec. _Roles:_ тривиальное свойство = Element-роль (разрешимо); нетривиальное семантическое = роль-ПРЕДЕЛ. _Rules:_ P_extensional; против каждого dec есть Rice-диагональ ⟹ RoleLimitDrawn. _P4:_ семантика программы — role-limit (зависит от поведения, не текста); тотальный семантический решатель = реификация = категориальная ошибка.
- **Classical counterpart.** Rice's theorem is classical; NEW is casting it as a precise Element(trivial)/role-limit(nontrivial-semantic) dichotomy with the diagonal as an instance of the shared engine.
- **Tags.** rice, semantic, role-limit, decidable, diagonal, vein-E

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `trivial_property_element_drawn` | Lemma | тривиальное (константное) свойство разрешимо (Element) |
| `RiceDiagonal` | Definition | самоотрицающий свидетель против решателя dec |
| `rice_diagonal_exists` | Lemma | для нетривиального семантического P диагональ существует |
| `rice_role_limit` | Theorem | ★ нетривиальное семантическое свойство — RoleLimitDrawn |
| `rice_no_semantic_decider` | Corollary | нет тотального решателя семантического свойства |

**Key lemmas (deep):**

- **`rice_role_limit`** - Теорема Райса в дихотомии Element/role-limit: нетривиальное СЕМАНТИЧЕСКОЕ (экстенсиональное) свойство против каждого решателя имеет самоотрицающего свидетеля ⟹ RoleLimitDrawn (инстанс diagonal_defeats_decider). Семантика — про поведение, не про текст; её разрешение реифицирует role-limit в Element. _(rice, role-limit, semantic, diagonal)_
- **`trivial_property_element_drawn`** - Другая сторона дихотомии Райса: ТРИВИАЛЬНОЕ (константное) свойство разрешимо — Element. Делает теорему точной границей: ровно нетривиальность+семантичность толкает свойство в role-limit. _(trivial, element, decidable)_

**Uniqueness - score 3 (new-framing).** Теорема Райса как точная дихотомия Element/role-limit: тривиальное свойство разрешимо, нетривиальное семантическое — role-limit (инстанс универсального движка).
> _Caveat:_ Райс классичен; ново — постановка как Element/role-limit-граница и вывод диагонали как инстанса BoundaryDecidability, а не отдельно.

---

## #115 - `src/cs/RussellViaLawvere.v` - score 4 (synthesis+observation)

**Russell / Liar / Grelling / Cantor-Prop as ONE diagonal under Lawvere**

- **Topic.** Proves (~P)<>P (no Prop fixpoint), then derives Russell (no universal set), the Liar, Grelling, and Cantor-on-Prop — capped by paradoxes_one_diagonal: all four paradoxes are the single negb/Lawvere diagonal.
- **Role.** Vein-E breadth (paradox unification). Imports LawvereFixedPoint, TarskiUndefinability. The Prop-side mirror of the bool-side faces.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** cs.LawvereFixedPoint; cs.TarskiUndefinability
- **E/R/R.** _Elements:_ пропозиции P: Prop; предикаты членства/истинности/гетерологичности. _Roles:_ парадокс = роль-самоотрицание (s=f(s)); универсальное множество/истинность = реифицированный role-limit. _Rules:_ (~P)<>P — нет неподвижной точки отрицания на Prop; отсюда Рассел/Лжец/Греллинг. _P4:_ каждый парадокс = попытка реифицировать самоотрицающую роль в Element-объект; блокируется одной диагональю (Ловер) на типовом уровне.
- **Classical counterpart.** Russell's paradox, the Liar, Grelling, and Cantor are all known as Lawvere/diagonal phenomena; NEW is their systematic in-repo unification as ONE diagonal and the tie to the computational faces.
- **Tags.** paradox, russell, liar, grelling, diagonal, lawvere, vein-E, unification

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `not_no_fixpoint` | Lemma | (~P)<>P — отрицание не имеет неподвижной точки на Prop (через eq_rect) |
| `cantor_prop` | Corollary | Кантор на Prop как инстанс |
| `russell_no_universal_set` | Theorem | ★ нет универсального множества (Рассел) |
| `liar` | Corollary | нет p с p<->~p (Лжец) |
| `grelling` | Corollary | гетерологичность противоречива (Греллинг) |
| `paradoxes_one_diagonal` | Theorem | ★ Рассел/Лжец/Греллинг/Кантор — ОДНА диагональ |

**Key lemmas (deep):**

- **`paradoxes_one_diagonal`** - Капстоун широты вены E: Рассел, Лжец, Греллинг и Кантор-на-Prop собраны как ОДНА диагональ (через (~P)<>P, инстанс Ловера). Превращает четыре «разных» парадокса в одну структуру самоотрицания — Prop-зеркало bool-граней (число/программа/множество/сложность). _(paradox, one-diagonal, unification, vein-E)_
- **`not_no_fixpoint`** - Технически тонкий корень: (~P)<>P доказан транспортом eq_rect (а не rewrite, который не прогрессирует на голом Prop). Важна и скобочная ловушка: ~P<>P парсится как ~(P<>P), поэтому всюду явные (~P)<>P. Prop-аналог negb_no_fixpoint. _(prop-fixpoint, eq_rect, diagonal)_

**Uniqueness - score 4 (synthesis+observation).** Четыре семантических парадокса (Рассел/Лжец/Греллинг/Кантор-Prop) унифицированы как ОДНА диагональ под Ловером — Prop-зеркало вычислительных граней.
> _Caveat:_ Парадокс-как-неподвижная-точка известен со времён Тарского/Ловера (доказательства коротки). Уникальность — в систематической унификации именно этих парадоксов с вычислительными гранями репо.

---

## #116 - `src/cs/ScaleFlowUndecidable.v` - score 4 (synthesis+observation)

**Bridge halting ↔ hierarchy: a bounded/unbounded scale-flow distinction is undecidable**

- **Topic.** Builds a monotone scale-flow g(c) counting non-halting steps; it is bounded (flow_element) iff the machine halts, unbounded (flow_role_limit) iff it diverges — so the Element/role-limit flow split is undecidable, linking the halting boundary to the InterLevelCalculus hierarchy branch.
- **Role.** Cross-branch BRIDGE to «Иерархии и Каскады» (InterLevelCalculus). Replicates flow predicates locally (stale-vo avoidance). Reuses HaltingRoleLimit + BoundaryDecidability.
- **Counts.** Qed 17 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith; cs.HaltingRoleLimit; cs.BoundaryDecidability (replicated flow predicates)
- **E/R/R.** _Elements:_ масштаб-поток ScaleFlow=nat→Q; счётчик не-остановленных шагов nh_count. _Roles:_ flow_element = ограниченный монотонный поток (Element); flow_role_limit = неограниченный (role-limit). _Rules:_ g(c) считает не-halted шаги; ограничен ⟺ останавливается, неограничен ⟺ расходится. _P4:_ та же граница Element/role-limit, что и halting, но в форме ограниченности масштаб-потока иерархии: bounded/unbounded НЕразрешимо, ибо эквивалентно halting.
- **Classical counterpart.** Undecidability of boundedness of a computable monotone sequence (reducible to halting) is classical; NEW is the cross-branch bridge identifying it with the InterLevelCalculus scale-flow Element/role-limit boundary.
- **Tags.** bridge, undecidable, scale-flow, hierarchy, halting, InterLevelCalculus, P4

**Lemmas (19):**

| name | kind | role |
|---|---|---|
| `ScaleFlow` | Definition | поток масштаба nat→Q |
| `nondecreasing/bounded_above/unbounded` | Definition | монотонность и (не)ограниченность потока |
| `flow_element` | Definition | монотонный + ограниченный = Element |
| `flow_role_limit` | Definition | монотонный + неограниченный = role-limit |
| `arch_nat` | Lemma | архимедовость: любой Q превзойдён inject_Z натурального |
| `Qle_of_nat_le` | Lemma | перенос ≤ с nat на Q (через Zle_Qle) |
| `RoleLimitDrawn_iff` | Lemma | перенос RoleLimitDrawn по эквивалентности предикатов |
| `nh_count` | Fixpoint | число не-остановленных шагов до n |
| `g` | Definition | масштаб-поток-счётчик inject_Z(nh_count) |
| `nh_count_step/mono` | Lemma | монотонность счётчика |
| `g_nondecreasing` | Lemma | поток g не убывает |
| `nh_count_diverges` | Lemma | при расходимости счётчик растёт неограниченно |
| `g_diverges_unbounded` | Lemma | расходимость ⟹ g неограничен |
| `not_halts_diverges/diverges_iff_not_halts` | Lemma | связь halts/diverges |
| `nh_count_const_after/le_N` | Lemma | после остановки счётчик постоянен/ограничен N |
| `g_halts_bounded` | Lemma | остановка ⟹ g ограничен |
| `flow_element_of_halts` | Lemma | остановка ⟹ flow_element g |
| `flow_role_limit_iff_diverges` | Lemma | ★ flow_role_limit g ⟺ расходимость |
| `scale_flow_role_limit_undecidable` | Theorem | ★ Element/role-limit разрез масштаб-потока НЕразрешим (= halting) |

**Key lemmas (deep):**

- **`scale_flow_role_limit_undecidable`** - Мост между ветками: вопрос «ограничен ли масштаб-поток g(c)» (Element против role-limit в терминах InterLevelCalculus) НЕразрешим, потому что эквивалентен halting. Показывает, что граница Element/role-limit ветки CS — ТА ЖЕ линия, что bounded/unbounded в иерархии масштабов «Иерархии и Каскады». Синергия двух направлений в одной теореме. _(bridge, undecidable, scale-flow, hierarchy)_
- **`flow_role_limit_iff_diverges`** - Несущая эквивалентность: монотонный счётчик не-остановленных шагов неограничен ТОЧНО когда машина расходится. Аккуратная Q-арифметика (arch_nat, Qle_of_nat_le обходят Zle_Qle-как-равенство) превращает halting в свойство ограниченности потока. _(equivalence, divergence, Q-arithmetic)_

**Uniqueness - score 4 (synthesis+observation).** Кросс-веточный мост: граница Element/role-limit ветки CS отождествлена с границей bounded/unbounded масштаб-потока ветки иерархий — одна неразрешимая линия, увиденная с двух сторон.
> _Caveat:_ Неразрешимость ограниченности монотонного потока следует из halting; ценность — именно мост-обрамление между двумя ветками репо, а не новая неразрешимость.

---

## #117 - `src/cs/SelectionWithoutChoiceSynthesis.v` - score 5 (synthesis+observation)

**The choice ladder: selection is axiom-free EXACTLY when a decidable test + an order resolve it**

- **Topic.** Bundles vein B's four free levels (finite / countable / dependent / König) and states the unifying thesis: all reduce to iterating the canonical least selector; AC/DC/WKL is the price ONLY at the undecidable/unordered boundary — selection-freedom ⟺ decidability.
- **Role.** FLAGSHIP synthesis of vein B. Imports DecidableSelection + CountableSelectionFree + CountableDependentChoiceFree + DecidableKonig. Ties vein B to H1/H48 (finitization boundary). Concurrent (H52).
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: List PeanoNat Bool; cs.DecidableSelection; cs.CountableSelectionFree; cs.CountableDependentChoiceFree; cs.DecidableKonig
- **E/R/R.** _Elements:_ уровни выбора (конечный/счётный/зависимый/König/граница); флаг axiom_free. _Roles:_ свободный уровень = выбор, разрешённый ПРАВИЛОМ (тест+порядок); граница = AC/DC/WKL (role-limit). _Rules:_ разрешимый тест + порядок ⟹ 0 акс (наименьший = первый); неразрешимое/неупорядоченное ⟹ цена. _P4:_ свобода выбора ⟺ РАЗРЕШИМОСТЬ — та же линия, что H48/H1; четыре уровня = итерации наименьшего селектора; AC — цена структурного дефицита.
- **Classical counterpart.** AC/DC/WKL and their constructive eliminability under decidability (reverse mathematics, Bishop constructivism) are known; NEW is the bundled ladder plus the explicit thesis 'selection-freedom <-> decidability' tying vein B to the finitization boundary.
- **Tags.** no-AC, choice-ladder, vein-B, synthesis, decidability, selection, P4

**Lemmas (12):**

| name | kind | role |
|---|---|---|
| `SelectionLevel` | Inductive | уровни: Finite/CountableChoice/CountableDC/KonigPath/UnstructuredBoundary |
| `axiom_free` | Definition | true на всех структурных уровнях, false на границе |
| `all_levels` | Definition | список всех пяти уровней |
| `count_free/count_priced` | Definition | счётчики свободных/платных уровней |
| `count_free_4` | Lemma | ★ ЧЕТЫРЕ структурных уровня аксиомо-свободны |
| `count_priced_1` | Lemma | ОДИН (неструктурированный) — граница AC/DC/WKL |
| `ladder_total` | Lemma | free+priced = длина лестницы |
| `level_finite` | Lemma | конечный уровень обитаем (decidable_list_choice) |
| `level_countable_choice` | Lemma | счётный уровень обитаем (nat_least) |
| `level_countable_dc` | Lemma | зависимый уровень обитаем (dc_chain_step) |
| `level_konig` | Lemma | König-уровень обитаем (path_edge) |
| `selection_without_choice_synthesis` | Theorem | ★ КАПСТОУН: 4 свободных уровня + 1 платная граница + тезис |

**Key lemmas (deep):**

- **`selection_without_choice_synthesis`** - Флагман вены B: собирает четыре машинно-проверенных свободных уровня (finite/countable/dependent/König) в одну теорему и формулирует объединяющий тезис — выбор аксиомо-свободен ТОЧНО когда разрешимый тест + порядок (Rule, L5) его разрешают, а AC/DC/WKL — цена ровно структурного дефицита (неразрешимый тест/неупорядоченный носитель). Все уровни — итерации канонического наименьшего селектора (nat_least/first_witness). _(choice-ladder, synthesis, vein-B, thesis)_
- **`count_free_4`** - Численный костяк тезиса: из пяти уровней лестницы 4 структурных — аксиомо-свободны, ровно 1 (неструктурированная граница) платный. reflexivity-факт, но он КОНКРЕТИЗИРУЕТ «где именно проходит цена выбора» в виде конечного перечня. _(count, ladder, boundary)_

**Uniqueness - score 5 (synthesis+observation).** Объединяющий тезис вены B: выбор аксиомо-свободен ⟺ разрешимый тест + порядок его разрешают; AC = цена структурного дефицита. Четыре уровня = итерации наименьшего селектора; selection-freedom ⟺ decidability = та же граница, что финитизация (H1/H48), с двух сторон.
> _Caveat:_ Никакой новой математики — связка результатов нити под тезисом. Сила — в синтезе/наблюдении (selection-freedom ⟺ decidability), не в новой теореме. Параллельный поток (не мой).

---

## #118 - `src/cs/SemanticRecursion.v` - score 3 (synthesis+observation)

**Reconciling Leibniz-recursion with reduction-recursion; Rice from semantic recursion**

- **Topic.** Reconciles the two recursion notions (Leibniz-equality vs reduction) — leibniz_recursion_is_semantic — and re-derives the Rice diagonal from a semantic (reduction-grounded) recursion, grounded in the λ-machine.
- **Role.** The «примирение» (reconciliation) file. Imports BoundaryDecidability + RiceRoleLimit + LambdaGrounding + LambdaRecursion (explicit, since LambdaRecursion does not re-export Term/step).
- **Counts.** Qed 4 / Admitted 0 / axioms 0
- **Imports.** cs.BoundaryDecidability; cs.RiceRoleLimit; cs.LambdaGrounding; cs.LambdaRecursion
- **E/R/R.** _Elements:_ программы/термы; отношение редукции reduces; Rice-диагональ. _Roles:_ семантическая рекурсия = роль-самопорождение через поведение; Leibniz-рекурсия = роль через равенство. _Rules:_ leibniz_recursion_is_semantic мостит две формы; reduces — индуктивная редукция. _P4:_ рекурсия как процесс (reduction) против рекурсии как завершённого равенства (Leibniz): примирение показывает, что Element-сторона (operational) согласована с role-limit-выводом Rice.
- **Classical counterpart.** Kleene's recursion theorem and the Leibniz-vs-reduction notions of recursion are classical; NEW is the explicit reconciliation and a second (operational) derivation of Rice.
- **Tags.** recursion, reconciliation, rice, semantic, lambda, grounded

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `rice_diagonal_from_sem_recursion` | Theorem | ★ Rice-диагональ из семантической рекурсии |
| `leibniz_recursion_is_semantic` | Lemma | ★ Leibniz-рекурсия = семантическая (примирение двух форм) |
| `rice_from_sem_recursion` | Theorem | Rice выведен от семантической рекурсии |
| `reduces` | Inductive | отношение многошаговой редукции (заземление) |
| `recursion_grounded` | Lemma | рекурсия заземлена в reduces (λ-машина) |

**Key lemmas (deep):**

- **`leibniz_recursion_is_semantic`** - Ядро «примирения»: показывает, что рекурсия в смысле Leibniz-равенства совпадает с семантической (поведенческой, reduction-grounded) рекурсией. Снимает кажущееся противоречие между двумя способами говорить о рекурсии в репо — операционным (Y, reduces) и пропозициональным (равенство), стыкуя Element- и role-limit-стороны. _(reconciliation, recursion, leibniz, semantic)_
- **`rice_from_sem_recursion`** - Замыкает: Rice получается и из СЕМАНТИЧЕСКОЙ рекурсии, заземлённой в reduces/λ — то есть неразрешимость семантики выводится в операционной форме, а не только категориально (RecursionTheorem). Две дороги к Rice сходятся. _(rice, semantic, grounded)_

**Uniqueness - score 3 (synthesis+observation).** Примирение двух понятий рекурсии (Leibniz-равенство vs редукция) и вывод Rice из семантической, заземлённой в λ рекурсии — стыковка операционной и пропозициональной сторон.
> _Caveat:_ Эквивалентность форм рекурсии концептуально известна; вклад — явное внутрирепозиторное примирение и второй (операционный) путь к Rice.

---

## #119 - `src/cs/TarskiUndefinability.v` - score 4 (synthesis+observation)

**Tarski's undefinability of truth as a face of the one diagonal (via Lawvere)**

- **Topic.** Proves no truth predicate can exist: the self-referential diagonal (from recursion) forces P<->~P, which is absurd (iff_not_self_absurd). Packaged both from recursion and directly from Lawvere.
- **Role.** Vein-E face (truth). Feeds RussellViaLawvere. Connects to RecursionTheorem's diagonal.
- **Counts.** Qed 4 / Admitted 0 / axioms 0
- **Imports.** Stdlib; cs.LawvereFixedPoint / recursion diagonal
- **E/R/R.** _Elements:_ пропозиции; предикат истинности True_pred; диагональное предложение. _Roles:_ истинностный предикат = реифицированный role-limit (хочет решать всю семантику); диагональ = роль-самоотрицание. _Rules:_ диагональ ⟹ P<->~P; iff_not_self_absurd: P<->~P ложно. _P4:_ тотальный предикат истины = реификация role-limit-семантики в Element = категориальная ошибка; запрещена одной диагональю (Ловер).
- **Classical counterpart.** Tarski's undefinability of truth (1936) is classical; NEW is its identification as a face of the one Lawvere diagonal, tied to the other repo faces.
- **Tags.** tarski, truth, diagonal, lawvere, vein-E, unification

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `iff_not_self_absurd` | Lemma | (P<->~P)→False — самоотрицание абсурдно |
| `diag_from_recursion` | Lemma | диагональное предложение из рекурсии |
| `tarski_no_truth_predicate` | Theorem | ★ нет тотального предиката истинности (Тарский) |
| `tarski_from_lawvere` | Theorem | ★ Тарский напрямую из Ловера |

**Key lemmas (deep):**

- **`tarski_no_truth_predicate`** - Неопределимость истины как грань одной диагонали: предполагаемый тотальный предикат истинности порождает (через диагональ из рекурсии) самоотрицающее предложение P<->~P, абсурдное по iff_not_self_absurd. Семантика истины не реифицируется в Element-предикат — тот же запрет, что у halting/Rice. _(tarski, truth, diagonal, role-limit)_
- **`tarski_from_lawvere`** - Двойная упаковка: Тарский выведен и от рекурсии, и НАПРЯМУЮ от Ловера — явно помещая неопределимость истины в тот же корень, что Кантор/halting/Рассел. Делает вену E замкнутой: все «невозможности» — инстансы одной неподвижной точки. _(tarski, lawvere, unification)_

**Uniqueness - score 4 (synthesis+observation).** Неопределимость истины Тарского встроена как грань ОДНОЙ диагонали (Ловер), стыкуясь с Кантор/halting/Рассел — Prop-сторона унификации вены E.
> _Caveat:_ Теорема Тарского классична; вклад — её опознание как инстанса Ловера и стыковка с остальными гранями репо, не новый результат.

