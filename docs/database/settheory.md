# Database - cluster `settheory`

_Generated from `settheory.json` by `generate.ps1` - do not edit by hand; edit the JSON._

**10 files / 128 Qed.** Score distribution: s5=0 / s4=4 / s3=3 / s2=2 / s1=1 / s0=0

---

## #1058 - `src/settheory/BorelDeterminacy.v` - score 3 (new-framing)

**Finite-horizon game determinacy (axiom-free); full Borel determinacy a role-limit**

- **Topic.** Length-K games with strategies for I/II: weak_determinacy for any payoff at finite horizon, zero-length games trivially determined, decidable play outcomes, plus a transfer-matrix path-count layer. The unbounded (genuine Borel) determinacy is the role-limit.
- **Role.** Set-theory determinacy at the finite/Element side. Self-contained (lists, Q). Re-declares the classic axiom (one of 4 textual copies in the repo).
- **Counts.** Qed 19 / Admitted 0 / axioms 0
- **Imports.** Stdlib: List QArith
- **E/R/R.** _Elements:_ состояния игры GameState=list nat; стратегии I/II; конечные партии play K. _Roles:_ детерминированность как роль-исход; полная борелевская детерминированность = role-limit. _Rules:_ play играет K ходов; wins_I; determined = у кого-то выигрышная стратегия. _P4:_ конечный горизонт K разрешим (Element, weak_determinacy/decidable_play_outcome); безграничная борелевская детерминированность = role-limit (Мартин, сильные аксиомы) — не подделана.
- **Classical counterpart.** Borel determinacy (Martin) is classical and consumes large cardinals / strong axioms; HERE only FINITE-HORIZON determinacy (length-K games) is proven, axiom-free, plus a decidable-outcome layer. NEW: only the finite/role-limit split — full Borel determinacy stays a cited role-limit. (Re-declares classic locally.)
- **Tags.** determinacy, games, finite-horizon, role-limit, P4

**Lemmas (17):**

| name | kind | role |
|---|---|---|
| `GameState/Strategy_I/Strategy_II` | Definition | состояния и стратегии игры |
| `play` | Fixpoint | разыгрывание K ходов двумя стратегиями |
| `wins_I/determined` | Definition | выигрыш I; детерминированность горизонта K |
| `play_0/play_length/play_1/play_2` | Lemma | базовые свойства партии (длина=K и т.п.) |
| `trivial_win/impossible_win` | Definition | тривиальные payoff'ы True/False |
| `trivial_game_determined/impossible_game_determined` | Lemma | тривиальные игры детерминированы |
| `first_move_game/first_move_determined` | Lemma | игра, решаемая первым ходом |
| `determined_weak` | Definition | слабая детерминированность |
| `weak_determinacy` | Theorem | ★ конечный горизонт: всякий payoff слабо детерминирован |
| `zero_game_determined` | Theorem | игры длины 0 детерминированы |
| `decidable_W/decidable_play_outcome` | Lemma | разрешимый payoff ⟹ разрешимый исход |
| `TransferMatrix/path_count` | Definition | матрица переходов и счёт путей (Q) |
| `path_count_0/0_diag/0_off` | Lemma | базовые значения счёта путей |
| `const_strategy/mirror_strategy` | Definition | константная и зеркальная стратегии |
| `const_play_1/mirror_play_1` | Lemma | их поведение на 1 ходу |
| `player_I_can_win/can_win_or_not` | Lemma | разрешимость «может ли I выиграть» |
| `trivial_can_win/impossible_cannot_win` | Lemma | конкретные случаи |

**Key lemmas (deep):**

- **`weak_determinacy`** - Element-сторона детерминированности: на КОНЕЧНОМ горизонте K любой payoff слабо детерминирован — никаких сильных аксиом. Контраст с полной борелевской детерминированностью (Мартин, требует больших кардиналов), которая честно оставлена role-limit. Тот же P4-разрез ограниченное/безграничное. _(determinacy, finite-horizon, element)_
- **`decidable_play_outcome`** - При разрешимом payoff исход конечной партии разрешим — конечная игра полностью вычислима (P4). Делает определённость не аксиомой, а вычислением для ограниченного горизонта. _(decidable, finite)_

**Uniqueness - score 3 (new-framing).** Детерминированность игр расщеплена P4-разрезом: конечный горизонт аксиомо-свободно детерминирован (Element), полная борелевская — честный role-limit (Мартин, большие кардиналы), не подделана.
> _Caveat:_ Конечные игры тривиально детерминированы; вклад — только обрамление Element/role-limit + честная граница. Локально пере-объявляет аксиому classic (одна из 4 текстовых копий в репо).

---

## #1059 - `src/settheory/CantorBendixsonFull.v` - score 3 (new-framing)

**Cantor-Bendixson derivative as an iterable rule; perfect vs scattered over Q**

- **Topic.** Isolated/accumulation points, the CB derivative CB_deriv, its finite and omega iterations, perfect and scattered predicates, the empty set perfect, a concrete finite scattered set (its derivative empties), and an ordinal CB step.
- **Role.** Descriptive set theory over Q-point-sets. Self-contained (QArith/Qabs).
- **Counts.** Qed 23 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs
- **E/R/R.** _Elements:_ точечные множества PointSet=Q→Prop; изолированные/предельные точки. _Roles:_ производная Кантора-Бендиксона как правило-сгущение; perfect/scattered как роли множества. _Rules:_ CB_deriv = предельные точки; CB_iter итерирует; CB_omega = пересечение всех итераций. _P4:_ ранг КБ = процесс итерирования производной (role-limit для трансфинитного), каждая конечная итерация актуальна (Element); конкретное scattered множество опустошается за конечный шаг.
- **Classical counterpart.** The Cantor-Bendixson derivative, perfect/scattered sets, and CB rank are classical descriptive set theory; NEW is only formalizing the derivative as an iterable RULE over Q-point-sets (CB_iter, CB_omega) with a concrete scattered finite set worked out, axiom-free.
- **Tags.** cantor-bendixson, derivative, scattered, descriptive-set-theory, process

**Lemmas (15):**

| name | kind | role |
|---|---|---|
| `PointSet` | Definition | Q→Prop |
| `is_isolated/is_accumulation` | Definition | изолированная/предельная точка |
| `CB_deriv` | Definition | производная = множество предельных точек |
| `CB_iter/CB_omega` | Fixpoint/Definition | конечные итерации и ω-пересечение |
| `is_perfect/is_countable/is_scattered/subset/empty_set` | Definition | роли множеств и носители |
| `CB_deriv_subset/CB_iter_subset/CB_iter_monotone` | Lemma | производная/итерации убывают, монотонны |
| `CB_omega_subset/in_all/stable` | Lemma | свойства ω-ядра |
| `isolated_not_accumulation/accumulation_not_isolated` | Lemma | изолированность ⟂ предельность |
| `empty_is_perfect/CB_deriv_empty/CB_omega_empty` | Lemma | пустое множество совершенно |
| `S_finite` | Definition | конкретное конечное множество {0,1,2} |
| `S_finite_near_0/1/2 + _isolated` | Lemma | каждая точка изолирована |
| `CB_deriv_finite_empty/CB_iter_finite_empty/CB_omega_finite_empty` | Lemma | производная конечного пуста |
| `S_finite_scattered` | Lemma | ★ {0,1,2} рассеяно (scattered) |
| `CB_ord_step` | Definition | трансфинитный шаг КБ (ординал) |
| `CB_ord_omega_eq/CB_omega_accumulation_in_parent` | Lemma | связь ω-шага и ординального |

**Key lemmas (deep):**

- **`S_finite_scattered`** - Конкретное scattered множество {0,1,2}⊂Q: каждая точка изолирована (S_finite_*_isolated), производная пуста уже на шаге 1 — рассеянность вычислена, а не постулирована. Демонстрирует ранг КБ как ТЕРМИНИРУЮЩИЙ процесс на конечных множествах (Element-сторона). _(scattered, concrete, CB-rank)_
- **`CB_iter_monotone`** - Итерации производной монотонно убывают — это и есть «правило-сгущение» как процесс. Трансфинитная стабилизация (CB_omega) = role-limit-завершение; конечные шаги актуальны (P4). _(monotone, process, derivative)_

**Uniqueness - score 3 (new-framing).** Производная Кантора-Бендиксона как итерируемое ПРАВИЛО над Q-точечными множествами (CB_iter/CB_omega) + конкретное рассеянное множество, опустошаемое за конечный шаг — ранг КБ как процесс.
> _Caveat:_ Дескриптивная теория множеств (производная КБ, perfect/scattered, ранг) классична; вклад — формализация над Q + процессное обрамление, не новый результат.

---

## #1060 - `src/settheory/CantorTheoremGeneral.v` - score 4 (synthesis+observation)

**General Cantor: no surjection X -> (X -> bool), axiom-free (vein E)**

- **Topic.** For an arbitrary type X, the diagonal predicate defeats any candidate surjection f : X -> (X -> bool): the diagonal differs from every f x at the point x, so no surjection exists; hence no maximal bool-power.
- **Role.** Vein E (one diagonal) on the set side, axiom-free. The settheory mirror of cs/HaltingRoleLimit.cantor_no_surjection. Self-contained.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib
- **E/R/R.** _Elements:_ произвольный тип X; кандидат-сюръекция f: X→(X→bool); диагональный предикат. _Roles:_ несчётность как ПРАВИЛО (нет сюръекции); диагональ = роль-самоотрицание. _Rules:_ cantor_diagonal x = negb (f x x); отличается от каждого f x в точке x. _P4:_ та же negb-диагональ, что halting/Russell; несчётность — правило, не объект; реификация сюръекции запрещена диагональю (вена E).
- **Classical counterpart.** Cantor's theorem (no surjection X -> P(X)) is classical; NEW is only its axiom-free general form over an arbitrary X via the same negb-no-fixpoint diagonal that drives halting/Russell in the cs branch — vein E, one diagonal.
- **Tags.** cantor, diagonal, vein-E, uncountability, 0-axiom

**Lemmas (8):**

| name | kind | role |
|---|---|---|
| `surjective` | Definition | f: X→(X→bool) накрывает все предикаты |
| `cantor_diagonal` | Definition | диагональ: x ↦ negb (f x x) |
| `no_bool_fixpoint` | Lemma | b = negb b ⟹ False (семя) |
| `diagonal_differs_at_point` | Lemma | диагональ ≠ f x в точке x |
| `diagonal_not_in_image` | Theorem | диагональ не в образе f |
| `cantor_no_surjection` | Theorem | ★ нет сюръекции X→(X→bool) (общий Кантор) |
| `exists_predicate_unhit` | Theorem | всегда есть непокрытый предикат |
| `no_maximal_bool_power` | Theorem | ★ нет максимальной bool-степени |

**Key lemmas (deep):**

- **`cantor_no_surjection`** - Общий Кантор для произвольного X, аксиомо-свободно: диагональ negb(f x x) не в образе никакой f. Это set-сторона ОДНОЙ диагонали — то же negb-семя, что в cs (halting, Russell). Несчётность подана как ПРАВИЛО (вена E), а не как кардинальный объект. _(cantor, diagonal, vein-E, 0-axiom)_
- **`no_maximal_bool_power`** - Нет максимальной bool-степени: для всякого X степень (X→bool) строго больше — role-limit-восхождение без верха, тот же узор, что no_maximal_rung (алгебраическое замыкание) и no_maximal_cardinality. _(no-maximum, role-limit)_

**Uniqueness - score 4 (synthesis+observation).** Общий Кантор (нет сюръекции X→(X→bool)) аксиомо-свободно через ту же negb-диагональ, что halting/Russell — set-грань ОДНОЙ диагонали (вена E), несчётность как правило.
> _Caveat:_ Теорема Кантора классична; уникальность — в аксиомо-свободности и явной унификации с вычислительными/парадоксальными гранями (вена E), не в самой теореме.

---

## #1061 - `src/settheory/CardinalityWithoutChoice.v` - score 4 (synthesis+observation)

**Cardinality without choice: Schroeder-Bernstein yes, surjection->injection (=AC) refused**

- **Topic.** injects/surjects/bijects as a preorder; cardinal_antisym (mutual injection => bijection, i.e. Schroeder-Bernstein) WITHOUT AC; no_maximal_cardinality. The converse surjection->injection (exactly AC) is deliberately omitted.
- **Role.** Vein B flagship (no-AC cardinality). Pairs with ChoicePriceMap (which audits its axiom price = PL3_L4). Self-contained.
- **Counts.** Qed 10 / Admitted 0 / axioms 0
- **Imports.** Stdlib
- **E/R/R.** _Elements:_ типы A,B; инъекции/сюръекции/биекции между ними. _Roles:_ кардинальное сравнение как предпорядок; антисимметрия = Шрёдер-Бернштейн. _Rules:_ injects both ways ⟹ bijects (без AC); surjection→injection (=AC) НЕ доказывается. _P4:_ Шрёдер-Бернштейн аксиомо-свободен (Element-сторона, цена PL3_L4 в ChoicePriceMap); surjection→injection = AC = role-limit, сознательно не пересечён.
- **Classical counterpart.** Cardinal comparability and Schroeder-Bernstein are classical; NEW is proving cardinal antisymmetry (injects both ways => bijects) WITHOUT the Axiom of Choice, and deliberately NOT proving surjection->injection (which IS exactly AC) — vein B, the AC-localization made explicit.
- **Tags.** cardinality, schroeder-bernstein, no-AC, vein-B, axiom-price

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `injects/surjects/bijects` | Definition | инъекция/сюръекция/биекция между типами |
| `injects_refl/trans` | Lemma | инъекции — предпорядок |
| `surjects_refl/trans` | Lemma | сюръекции — предпорядок |
| `bijects_refl/trans` | Lemma | биекции — эквивалентность |
| `bijects_injects/bijects_both` | Lemma | биекция ⟹ инъекция (и сюръекция) |
| `cardinal_antisym` | Theorem | ★ взаимная инъекция ⟹ биекция (Шрёдер-Бернштейн без AC) |
| `no_maximal_cardinality` | Theorem | ★ нет максимальной мощности (Кантор-восхождение) |

**Key lemmas (deep):**

- **`cardinal_antisym`** - Шрёдер-Бернштейн БЕЗ AC: взаимная инъекция даёт биекцию. Ключевая честность вены B — обратное (surjection→injection) ЕСТЬ ровно Аксиома Выбора и сознательно НЕ доказывается. ChoicePriceMap аудирует цену этого результата как PL3_L4 (classic+L4_witness, не AC). _(schroeder-bernstein, no-AC, vein-B)_
- **`no_maximal_cardinality`** - Нет максимальной мощности — тот же role-limit-узор no-maximum, что no_maximal_bool_power / no_maximal_rung. Кантор-восхождение как правило. _(no-maximum, cantor, role-limit)_

**Uniqueness - score 4 (synthesis+observation).** Шрёдер-Бернштейн (антисимметрия мощностей) БЕЗ Аксиомы Выбора, с сознательным отказом доказывать surjection→injection (=ровно AC) — вена B, явная локализация цены выбора.
> _Caveat:_ Шрёдер-Бернштейн классичен и обычно конструктивен; уникальность — в систематическом разделении «что свободно vs что есть AC» (с аудитом цены в ChoicePriceMap), не в теореме.

---

## #1062 - `src/settheory/ChoicePriceMap.v` - score 4 (synthesis+observation)

**The audited axiom-price map: which set-theory result costs what (0 / L3 / L3+L4 / AC)**

- **Topic.** An enumerated price function over the repo's set-theoretic results: general Cantor / countability of Q / transfinite-level = 0 axioms; Higman = L3 (classic); Schroeder-Bernstein / cardinal antisymmetry = L3+L4; full AC = the boundary. Proven results sit below the boundary.
- **Role.** Vein B meta-artifact: the honest AC-price ledger for the whole set-theory cluster. Machine-checked. Self-contained.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib
- **E/R/R.** _Elements:_ имена результатов ResultName; цены AxiomPrice (PZero/PL3/PL3_L4/PBoundary). _Roles:_ цена аксиомы как роль-стоимость результата; граница AC как role-limit-порог. _Rules:_ price r = аксиоматическая стоимость; below_boundary отделяет доказанное от AC. _P4:_ результаты ниже границы AC = Element (доказуемы при L3/L4); полная AC = role-limit-порог; карта — машинно-проверенный честный реестр цены.
- **Classical counterpart.** Reverse mathematics / the axiom-of-choice hierarchy is classical; NEW is a small AUDITED in-repo price table assigning each set-theoretic result its exact axiom cost (0 / L3 / L3+L4 / AC-boundary) and proving the proven results sit BELOW the AC boundary — vein B, the honesty ledger made machine-checked.
- **Tags.** axiom-price, choice, no-AC, vein-B, audit, reverse-mathematics

**Lemmas (9):**

| name | kind | role |
|---|---|---|
| `AxiomPrice` | Inductive | цены: PZero \| PL3 \| PL3_L4 \| PBoundary |
| `ResultName` | Inductive | имена результатов репо |
| `price` | Definition | функция стоимости результата |
| `cantor_general_zero/countability_q_zero/transfinite_level_zero` | Lemma | ★ эти результаты = 0 аксиом |
| `higman_uses_L3_not_AC` | Lemma | Хигман = L3 (classic), не AC |
| `sb_uses_L3_L4_not_AC/cardinal_antisym_uses_L3_L4` | Lemma | Шрёдер-Бернштейн = L3+L4, не AC |
| `below_boundary` | Definition | цена строго ниже порога AC |
| `full_AC_is_boundary` | Lemma | полная AC = граница |
| `proven_results_below_boundary` | Lemma | ★ все доказанные результаты ниже границы AC |

**Key lemmas (deep):**

- **`proven_results_below_boundary`** - Машинно-проверенный честный реестр: КАЖДЫЙ доказанный set-результат репо имеет явную аксиоматическую цену (0 / L3 / L3+L4), и ВСЕ они строго ниже порога полной AC. Это редкий мета-артефакт — формализованная бухгалтерия цены выбора, ядро честности вены B. _(axiom-price, audit, vein-B, below-AC)_
- **`cantor_general_zero`** - Общий Кантор / счётность Q / трансфинитные уровни стоят 0 аксиом — Element-сторона. Локализует, что именно бесплатно, отделяя от L3/L4/AC-порога. _(0-axiom, price)_

**Uniqueness - score 4 (synthesis+observation).** Машинно-проверенная аудированная КАРТА цены выбора: каждому set-результату назначена точная стоимость (0/L3/L3+L4/AC), доказано, что всё доказанное лежит ниже порога AC — реестр честности вены B.
> _Caveat:_ Иерархия силы аксиом (обратная математика) известна; уникальность — в формализованном внутрирепозиторном реестре цены, не в новой метаматематике.

---

## #1063 - `src/settheory/FiniteTreeEmbedding.v` - score 1 (exposition)

**Finite trees and the tree-embedding order (machinery for Kruskal)**

- **Topic.** Finite trees FTree, the embedding relation tree_embed (reflexive, leaf embeds anything), concrete embeddings/non-embeddings, size and depth, and the chain/fork families with their successor embeddings.
- **Role.** Combinatorial foundation beneath KruskalTree/KruskalFull/Higman. Self-contained.
- **Counts.** Qed 18 / Admitted 0 / axioms 0
- **Imports.** Stdlib: List
- **E/R/R.** _Elements:_ конечные деревья FTree (FLeaf/FNode); конкретные деревья t_1/t_2/chain/fork. _Roles:_ tree_embed = роль-вложение (порядок на деревьях); size/depth как роли-меры. _Rules:_ FLeaf вкладывается во всё; рефлексивность; list_embed для детей. _P4:_ конечные деревья — полностью актуальные данные (Element); порядок вложения вычислим.
- **Classical counterpart.** Homeomorphic/tree embedding and the embedding order on finite trees are standard combinatorics; NEW: nothing — concrete finite-tree machinery (embedding, size, depth, chains, forks) supporting the Kruskal/Higman files.
- **Tags.** finite-trees, embedding, wqo, infrastructure

**Lemmas (10):**

| name | kind | role |
|---|---|---|
| `FTree` | Inductive | конечное дерево (лист/узел со списком детей) |
| `tree_embed` | Inductive | отношение вложения деревьев |
| `t_leaf/t_1/t_2/t_chain2/t_chain3/t_fork` | Definition | конкретные деревья |
| `embed_leaf_anything/tree_embed_refl/list_embed_refl` | Lemma | лист вкладывается во всё; рефлексивность |
| `embed_1_in_2/embed_chain2_in_chain3` | Lemma | конкретные вложения |
| `no_node_in_leaf/list_embed_nil_inv/list_embed_2_1_false/not_embed_2_in_1` | Lemma | конкретные НЕ-вложения |
| `tree_size/tree_size_leaf/1/2` | Fixpoint/Lemma | размер дерева |
| `tree_depth/tree_depth_leaf/1/chain3` | Fixpoint/Lemma | глубина дерева |
| `chain/chain_0/chain_embed_succ` | Fixpoint/Lemma | цепи и их вложения-наследники |
| `fork/fork_embed_succ` | Definition/Lemma | развилки и их вложения |

**Key lemmas (deep):**

- **`chain_embed_succ`** - Цепь длины n вкладывается в цепь n+1 — растущее семейство для wqo-аргументов Kruskal. Конкретный строительный блок: бесконечная антицепь невозможна среди цепей. _(embedding, chain, wqo-building-block)_
- **`not_embed_2_in_1`** - Конкретное НЕ-вложение (узел с 2 детьми не вкладывается в узел с 1) — показывает, что порядок вложения нетривиален (есть несравнимые), что и делает теорему Краскала содержательной. _(non-embedding, order)_

**Uniqueness - score 1 (exposition).** Конкретная машина конечных деревьев (вложение, размер, глубина, цепи/развилки) — комбинаторный фундамент под Kruskal/Higman.
> _Caveat:_ Полностью стандартная комбинаторика деревьев; ценность инфраструктурная.

---

## #1064 - `src/settheory/HigmanLemma.v` - score 2 (methods)

**Higman's lemma: concrete wqo cases (unit, bool) + Dickson**

- **Topic.** Well-quasi-order definition, the list embedding order list_le, Dickson's lemma for pairs of nat-sequences, wqo on nat/unit/bool, and Higman's lemma for lists over unit (by length).
- **Role.** wqo theory at the concrete/finite side. Re-declares classic. Self-contained.
- **Counts.** Qed 8 / Admitted 0 / axioms 0
- **Imports.** Stdlib: List PeanoNat
- **E/R/R.** _Elements:_ wqo-структуры на nat/unit/bool; список-вложение list_le. _Roles:_ is_wqo как роль «нет бесконечной антицепи»; Хигман как подъём wqo на списки. _Rules:_ list_le; Диксон для пар; wqo по длине для unit. _P4:_ конкретные wqo (nat/unit/bool) разрешимы (Element); общий Хигман над произвольным wqo использует classic (role-limit-сторона).
- **Classical counterpart.** Higman's lemma (the embedding order on words over a wqo is a wqo) and Dickson's lemma are classical; NEW: only the concrete special cases (over unit, bool) proven directly, axiom-free apart from a local classic. (Re-declares classic.)
- **Tags.** higman, dickson, wqo, methods

**Lemmas (9):**

| name | kind | role |
|---|---|---|
| `is_wqo` | Definition | well-quasi-order: всякая последовательность имеет вкладывающуюся пару |
| `list_le` | Inductive | порядок вложения списков |
| `list_le_nil_always` | Lemma | пустой вкладывается во всё |
| `wqo_nat_le` | Lemma | Nat.le — wqo |
| `dickson_pair` | Lemma | Диксон: пары nat-последовательностей имеют вкл. пару |
| `wqo_unit/wqo_bool` | Lemma | unit и bool — wqo |
| `unit_list_embed_by_length` | Lemma | вложение списков unit по длине |
| `higman_unit` | Lemma | ★ Хигман для списков над unit |
| `higman_synthesis` | Theorem | сводка конкретных wqo-результатов |

**Key lemmas (deep):**

- **`higman_unit`** - Хигман для списков над unit (через длину): порядок вложения — wqo, доказано конкретно. Element-сторона теоремы Хигмана; общий случай над произвольным wqo требует classic (role-limit). Честная локализация силы. _(higman, wqo, concrete)_
- **`dickson_pair`** - Лемма Диксона для пар nat-последовательностей: всегда есть индекс-пара с покомпонентным ≤. Базовый wqo-факт, на котором стоят Хигман/Краскал. _(dickson, wqo)_

**Uniqueness - score 2 (methods).** Лемма Хигмана и Диксон в конкретных wqo-случаях (nat/unit/bool), аксиомо-свободно (кроме локального classic) — Element-сторона wqo-теории.
> _Caveat:_ Хигман и Диксон классичны; вклад — конкретные случаи + честная граница с общим случаем. Пере-объявляет classic локально (одна из 4 копий).

---

## #1065 - `src/settheory/KruskalFull.v` - score 3 (new-framing)

**Kruskal tree theorem: structured wqo cases + L5 link**

- **Topic.** Well-quasi-order of finite trees on structured subfamilies: depth-0, chains, monotone-growing, forks, depth-1 (grows with children count); the full Kruskal statement as a Prop, and L5_from_kruskal tying it to the L5 constitutive order.
- **Role.** Kruskal at the structured/Element side. Builds on FiniteTreeEmbedding. Ties wqo to L5. Self-contained.
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: List; settheory.FiniteTreeEmbedding
- **E/R/R.** _Elements:_ последовательности конечных деревьев f: nat→FTree; структурные подсемейства. _Roles:_ wqo как роль «нет бесконечной антицепи»; Kruskal как подъём на деревья. _Rules:_ depth0/chain/growing/fork/depth1 — структурные wqo; L5_from_kruskal связывает с L5. _P4:_ структурированные случаи разрешимы (Element); полный Kruskal — сильная теорема (role-limit), заявлена как Prop.
- **Classical counterpart.** Kruskal's tree theorem (finite trees are well-quasi-ordered by embedding) is classical and proof-theoretically strong; NEW: only restricted/structured cases (depth-0, chains, growing, forks, depth-1) proven directly, with the full statement stated and tied to L5. 
- **Tags.** kruskal, wqo, trees, L5, new-framing

**Lemmas (9):**

| name | kind | role |
|---|---|---|
| `is_leaf/leaf_embeds_leaf` | Definition/Lemma | лист вкладывается в лист |
| `depth0_wqo` | Lemma | глубина-0 последовательности — wqo |
| `chain_wqo/chain_all_pairs` | Lemma | цепи — wqo |
| `growing_wqo/growing_full_monotone` | Lemma | растущие последовательности — wqo |
| `fork_wqo` | Lemma | развилки — wqo |
| `num_children/repeat_leaf_list_embed` | Fixpoint/Lemma | счёт детей; вложение списков листьев |
| `depth1_grows_with_children/depth1_wqo` | Lemma | ★ глубина-1 — wqo (растёт с числом детей) |
| `kruskal_full_statement` | Definition | полное утверждение Kruskal как Prop |
| `L5_from_kruskal` | Theorem | ★ Kruskal ⟹ L5-конститутивный порядок |

**Key lemmas (deep):**

- **`depth1_wqo`** - Деревья глубины 1 образуют wqo (число детей растёт ⟹ вкладывается) — содержательный структурный случай Kruskal, доказанный прямо. Element-сторона; полная теорема (произвольная глубина) — сильный role-limit. _(kruskal, wqo, depth-1)_
- **`L5_from_kruskal`** - Связывает Kruskal с L5-конститутивным порядком ToS: wqo-структура даёт детерминированный порядок-резолюцию. Мост между set-теорией и ядром E/R/R (L5). _(L5, bridge, wqo)_

**Uniqueness - score 3 (new-framing).** Теорема Краскала в структурных случаях (depth-0/chain/growing/fork/depth-1) + мост к L5-конститутивному порядку ToS — wqo как Element-сторона + связь с ядром.
> _Caveat:_ Kruskal классична и проофтеоретически сильна; доказаны лишь ограниченные случаи, полное утверждение лишь сформулировано. Ценность — структурные случаи + L5-мост.

---

## #1066 - `src/settheory/KruskalTree.v` - score 2 (methods)

**Kruskal building blocks: monotone subsequences, no infinite descent on nat**

- **Topic.** wqo and monotone-subsequence definitions; chain and fork embedding families with monotone witnesses; composition of strictly-increasing maps; seq_min and the no-infinite-descent lemma for nat; wqo of Nat.le; Kruskal for chains and forks.
- **Role.** Kruskal infrastructure (subsequence/descent machinery). Self-contained.
- **Counts.** Qed 19 / Admitted 0 / axioms 0
- **Imports.** Stdlib: List PeanoNat
- **E/R/R.** _Elements:_ последовательности; цепи/развилки; строго возрастающие отображения. _Roles:_ монотонная подпоследовательность как роль-свидетель wqo; seq_min как селектор минимума. _Rules:_ композиция строго возрастающих; нет бесконечного спуска на nat; wqo Nat.le. _P4:_ отсутствие бесконечного спуска на nat = Element (фундированность); монотонные подпоследовательности строятся детерминированно (seq_min).
- **Classical counterpart.** Kruskal's tree theorem and the no-infinite-descent / monotone-subsequence machinery are classical; NEW: nothing beyond a direct constructive treatment of the building blocks (chains, forks, monotone subsequences, min-selection, no infinite descent on nat).
- **Tags.** kruskal, wqo, well-founded, monotone-subsequence, methods

**Lemmas (9):**

| name | kind | role |
|---|---|---|
| `is_wqo/has_monotone_subseq` | Definition | wqo и наличие монотонной подпоследовательности |
| `chain_embed_all/chain_identity_monotone/chain_nondec_wqo_pair` | Lemma | цепи: вложение и монотонность |
| `repeat_leaf_list_embed/fork_embed_all/fork_identity_monotone/fork_nondec_wqo_pair` | Lemma | развилки: вложение и монотонность |
| `consec_embed_monotone/shift_subseq_strict/const_seq_monotone` | Lemma | построение монотонных подпоследовательностей |
| `strict_incr_mono/compose_strict_increasing/monotone_subseq_compose` | Lemma | композиция строго возрастающих сохраняет монотонность |
| `seq_min/seq_min_le/seq_min_achieved` | Fixpoint/Lemma | минимум первых n значений (детерминированный селектор) |
| `nat_no_infinite_descent_aux` | Lemma | ★ нет бесконечного строго убывания на nat |
| `wqo_nat_le` | Lemma | Nat.le — wqo |
| `kruskal_chains/kruskal_forks` | Lemma | Kruskal для цепей и развилок |

**Key lemmas (deep):**

- **`nat_no_infinite_descent_aux`** - Нет бесконечного строго убывания на nat (фундированность) — арифметическое ядро всех wqo-аргументов. Element-сторона: фундированность ℕ вычислима, и из неё детерминированно (seq_min) извлекаются монотонные подпоследовательности без выбора. _(well-founded, no-descent, nat)_
- **`seq_min_achieved`** - seq_min(f,n) достигается на некотором k≤n — детерминированный селектор минимума (как first_witness/nat_least вены B): монотонные подпоследовательности строятся правилом, не выбором. _(min-selector, deterministic, no-AC-flavour)_

**Uniqueness - score 2 (methods).** Строительные блоки Краскала (монотонные подпоследовательности через детерминированный seq_min, отсутствие бесконечного спуска на nat) — Element-сторона wqo, перекликается с детерминированным выбором вены B.
> _Caveat:_ Стандартная wqo-машина; ценность — конструктивное/детерминированное исполнение, не новый результат.

---

## #1067 - `src/settheory/StructuralWellOrdersWithoutChoice.v` - score 4 (synthesis+observation)

**Structural well-orders without choice: nat and the Level hierarchy**

- **Topic.** level_depth is injective and order-reflecting, the Level order is total; well_orders/well_orderable defined; nat and Level are well-orderable from their intrinsic structure (no choice). The general well-ordering theorem (= AC) is not claimed.
- **Role.** Vein B (no-AC well-ordering where structure permits). Ties to the ToS Level hierarchy. Self-contained.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib; ToS Level hierarchy
- **E/R/R.** _Elements:_ носители nat, Level; их структурная глубина level_depth. _Roles:_ вполне-упорядоченность как роль, ДАННАЯ структурой (не выбором). _Rules:_ level_depth инъективна и отражает порядок ⟹ Level вполне-упорядочиваем; nat — тоже. _P4:_ структурированные носители вполне-упорядочиваемы аксиомо-свободно (Element); общая теорема о вполне-упорядочении = AC = role-limit, не заявлена.
- **Classical counterpart.** The well-ordering theorem is equivalent to AC; NEW is showing that SPECIFIC structured carriers (nat, the ToS Level hierarchy) are well-orderable WITHOUT choice, via their intrinsic depth/structure — vein B, well-ordering for free where the structure provides it.
- **Tags.** well-order, no-AC, vein-B, level, structure

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `level_depth_pos/level_depth_inj` | Lemma | глубина уровня ≥1 и инъективна |
| `depth_lt_imp_level_lt` | Lemma | глубина отражает порядок уровней |
| `level_lt_total` | Lemma | порядок на Level тотален |
| `well_orders/well_orderable` | Definition | вполне-упорядоченность и упорядочиваемость |
| `nat_well_orderable` | Lemma | ★ nat вполне-упорядочиваем (без AC) |
| `level_well_orderable` | Lemma | ★ Level вполне-упорядочиваем из структуры (без AC) |

**Key lemmas (deep):**

- **`level_well_orderable`** - Иерархия уровней ToS вполне-упорядочиваема БЕЗ выбора — через инъективную структурную глубину level_depth, отражающую порядок. Вена B: вполне-упорядочение бесплатно там, где структура его даёт; общая теорема (= AC) не заявлена. _(well-order, no-AC, vein-B, level)_
- **`nat_well_orderable`** - nat вполне-упорядочиваем из собственного порядка — каноничный случай, где структура заменяет выбор. Контраст с general well-ordering theorem, эквивалентной AC. _(well-order, nat, no-AC)_

**Uniqueness - score 4 (synthesis+observation).** Структурные носители (nat, иерархия Level) вполне-упорядочиваемы БЕЗ выбора через внутреннюю глубину — вена B: вполне-упорядочение бесплатно, где структура его даёт; общая теорема (=AC) не заявлена.
> _Caveat:_ Что nat вполне-упорядочен — тривиально; уникальность — в систематическом «структура вместо выбора» и явном отказе от general well-ordering (=AC), не в новой теореме.

