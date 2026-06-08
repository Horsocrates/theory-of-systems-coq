# Database - cluster `category`

_Generated from `category.json` by `generate.ps1` - do not edit by hand; edit the JSON._

**13 files / 49 Qed.** Score distribution: s5=0 / s4=0 / s3=0 / s2=7 / s1=6 / s0=0

---

## #70 - `src/category/EquivalenceOfCategories.v` - score 2 (methods)

**Equivalence of categories: CatEquiv, fully-faithful + essentially-surjective**

- **Topic.** The CatEquiv record (functors both ways with natural-iso unit/counit), components are isos, F and G essentially surjective, F preserves isos, and equivalence is symmetric.
- **Role.** Constructive (setoid) category theory: equivalence. Builds on the setoid category core. 
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** ToS category core (Category/Functor/NaturalIso)
- **E/R/R.** _Elements:_ категории C,D; функторы F,G; естественные изоморфизмы unit/counit. _Roles:_ эквивалентность как роль-двусторонняя-обратимость; ess-surjective/full/faithful как роли функтора. _Rules:_ CatEquiv = F,G + natural iso unit/counit; компоненты — изо. _P4:_ эквивалентность конструктивна (setoid-равенство), без классических аксиом.
- **Classical counterpart.** Equivalence of categories and its characterization (fully faithful + essentially surjective) are classical; NEW: nothing — a setoid-based constructive formalization (CatEquiv record, unit/counit natural isos, F essentially surjective).
- **Tags.** category-theory, equivalence, setoid, constructive, methods

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `CatEquiv` | Record | эквивалентность: функторы обе стороны + natural iso unit/counit |
| `ce_unit_is_nat_iso/ce_counit_is_nat_iso` | Lemma | unit/counit — естественные изоморфизмы |
| `is_ess_surjective/is_faithful/is_full` | Definition | существенно сюръективный/верный/полный функтор |
| `equiv_counit_components_iso/equiv_unit_components_iso` | Lemma | компоненты — изоморфизмы |
| `equiv_F_ess_surjective/equiv_G_ess_surjective` | Lemma | ★ F,G существенно сюръективны |
| `equiv_sym` | Definition | симметрия эквивалентности |
| `equiv_F_preserves_iso` | Lemma | F сохраняет изоморфизмы |

**Key lemmas (deep):**

- **`equiv_F_ess_surjective`** - Из эквивалентности следует существенная сюръективность F — половина характеризации «эквивалентность ⟺ fully faithful + ess. surjective». Конструктивно над setoid-категориями, без выбора/классики. _(equivalence, essentially-surjective)_
- **`equiv_sym`** - Эквивалентность симметрична (меняем F↔G, unit↔counit) — делает её отношением эквивалентности на категориях. Структурная аккуратность setoid-подхода. _(symmetry, equivalence)_

**Uniqueness - score 2 (methods).** Эквивалентность категорий конструктивно над setoid-категориями: CatEquiv, естественные изо unit/counit, существенная сюръективность.
> _Caveat:_ Эквивалентность категорий — стандартная теория; вклад — setoid/конструктивное исполнение, не новый результат.

---

## #71 - `src/category/FunctorCategory.v` - score 1 (exposition)

**The functor category [C,D]**

- **Topic.** Natural-transformation equality, the functor category FunctorCat C D as a Category, morphism-equality iff componentwise, identity/composition components, and componentwise iso characterization.
- **Role.** Constructive category theory: functor categories. Setoid-based.
- **Counts.** Qed 4 / Admitted 0 / axioms 0
- **Imports.** ToS category core
- **E/R/R.** _Elements:_ функторы C→D (объекты); естественные преобразования (морфизмы). _Roles:_ [C,D] как категория функторов; компонентное равенство как роль. _Rules:_ nt_eq покомпонентно; FunctorCat — категория; изо покомпонентно. _P4:_ функторная категория конструктивна (setoid-равенство преобразований).
- **Classical counterpart.** The functor category [C,D] (functors as objects, natural transformations as morphisms) is classical; NEW: nothing — its setoid-based construction with componentwise iso characterization.
- **Tags.** category-theory, functor-category, setoid, exposition

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `nt_eq` | Definition | равенство естественных преобразований (покомпонентно) |
| `FunctorCat` | Definition | ★ категория функторов [C,D] |
| `FunctorCat_mor_eq_iff` | Lemma | равенство морфизмов ⟺ покомпонентно |
| `FunctorCat_id_component/comp_component` | Lemma | компоненты id и композиции |
| `FunctorCat_iso_componentwise` | Lemma | ★ изо в [C,D] ⟺ покомпонентно изо |

**Key lemmas (deep):**

- **`FunctorCat`** - [C,D] как настоящая Category (функторы-объекты, естественные преобразования-морфизмы) над setoid-равенством — фундамент для Йонеды и пределов в функторных категориях. _(functor-category, construction)_
- **`FunctorCat_iso_componentwise`** - Изоморфизм в [C,D] ⟺ покомпонентный изоморфизм (естественный изо) — ключевая характеризация, используемая в эквивалентностях/Йонеде. _(iso, componentwise)_

**Uniqueness - score 1 (exposition).** Функторная категория [C,D] конструктивно над setoid: построение + покомпонентная характеризация изоморфизмов.
> _Caveat:_ Стандартная конструкция; ценность инфраструктурная (под Йонеду/пределы).

---

## #72 - `src/category/IdentityEquivalence.v` - score 1 (exposition)

**The identity equivalence C ~ C**

- **Topic.** Natural transformations between the identity functor and its self-composition, the identity equivalence id_equiv as a CatEquiv, its unit components, and its essential surjectivity.
- **Role.** Constructive category theory: a base CatEquiv instance. Setoid-based.
- **Counts.** Qed 2 / Admitted 0 / axioms 0
- **Imports.** ToS category core, EquivalenceOfCategories
- **E/R/R.** _Elements:_ тождественный функтор и его самокомпозиция; естественные преобразования между ними. _Roles:_ id_equiv как базовая эквивалентность C~C. _Rules:_ nt между Id и Id∘Id; id_equiv — CatEquiv. _P4:_ тождественная эквивалентность конструктивна (базовый инстанс).
- **Classical counterpart.** That a category is equivalent to itself (the identity equivalence) is trivial classical category theory; NEW: nothing — the explicit setoid construction of id_equiv as a CatEquiv.
- **Tags.** category-theory, equivalence, identity, setoid, exposition

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `nt_id_to_comp/nt_comp_to_id` | Definition | преобразования Id ↔ Id∘Id |
| `id_equiv` | Definition | ★ тождественная эквивалентность C~C |
| `id_equiv_unit_components` | Lemma | компоненты unit тождественны |
| `id_equiv_ess_surjective` | Lemma | тождественный функтор существенно сюръективен |

**Key lemmas (deep):**

- **`id_equiv`** - Тождественная эквивалентность C~C как явный CatEquiv — база рефлексивности отношения эквивалентности категорий (с equiv_sym/трансзитивностью даёт setoid на категориях). _(identity, equivalence, base-case)_

**Uniqueness - score 1 (exposition).** Тождественная эквивалентность C~C как явный CatEquiv — база рефлексивности эквивалентности категорий.
> _Caveat:_ Тривиальная классика; ценность — базовый конструктивный инстанс.

---

## #73 - `src/category/NaturalIsomorphism.v` - score 1 (exposition)

**Natural isomorphisms: the groupoid of functors**

- **Topic.** NaturalIso between functors, identity/symmetry/transitivity, component characterization, components mono and epi, and that the componentwise inverse is itself natural.
- **Role.** Constructive category theory: natural isos. Setoid-based. Used by equivalence/Yoneda.
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** ToS category core
- **E/R/R.** _Elements:_ функторы F,G,H; естественные преобразования и их компоненты. _Roles:_ естественный изоморфизм как роль-обратимость в [C,D]; группоид функторов. _Rules:_ NaturalIso рефлексивен/симметричен/транзитивен; обратное естественно. _P4:_ естественные изо образуют группоид конструктивно (setoid).
- **Classical counterpart.** Natural isomorphisms (componentwise-iso natural transformations) and their groupoid structure are classical; NEW: nothing — a setoid formalization (refl/sym/trans, mono/epi components, natural inverse is natural).
- **Tags.** category-theory, natural-isomorphism, groupoid, setoid, exposition

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `NaturalIso` | Definition | естественный изоморфизм функторов |
| `nat_iso_id/sym/trans` | Lemma | ★ группоидная структура (refl/sym/trans) |
| `nat_iso_components` | Lemma | характеризация через компоненты |
| `nat_iso_component_mono/epi` | Lemma | компоненты — моно и эпи |
| `natural_inverse_is_natural` | Lemma | ★ покомпонентное обратное естественно |

**Key lemmas (deep):**

- **`natural_inverse_is_natural`** - Покомпонентное обратное естественного изоморфизма само естественно — нетривиальный факт, делающий NaturalIso настоящей обратимостью в [C,D] (а не просто покомпонентной). Несущий для эквивалентностей. _(natural-inverse, naturality)_
- **`nat_iso_trans`** - Транзитивность естественных изо — вместе с refl/sym даёт группоид функторов, на котором стоит понятие эквивалентности категорий. _(groupoid, transitivity)_

**Uniqueness - score 1 (exposition).** Естественные изоморфизмы как группоид функторов конструктивно (refl/sym/trans, естественность обратного).
> _Caveat:_ Стандартная классика; ценность инфраструктурная (под эквивалентность/Йонеду).

---

## #74 - `src/category/RightAdjointPreservesLimits.v` - score 2 (methods)

**Right adjoint preserves limits (terminal-object fragment)**

- **Topic.** Adjunction unit naturality, the transpose roundtrip, and the proven fragment: a right adjoint preserves the terminal object.
- **Role.** Constructive category theory: an RAPL fragment. Setoid-based. 
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** ToS category core (Adjunction)
- **E/R/R.** _Elements:_ сопряжение C⊣D; unit/transpose; терминальный объект. _Roles:_ правый сопряжённый как сохраняющий пределы (здесь — терминал). _Rules:_ unit_natural; transpose roundtrip; правый сопряжённый сохраняет терминал. _P4:_ доказан фрагмент RAPL (терминал); общий RAPL для всех пределов — role-limit, не здесь.
- **Classical counterpart.** RAPL (right adjoints preserve limits) is classical; NEW: only a fragment — right adjoint preserves the terminal object, via adjunction transpose roundtrip, setoid-based.
- **Tags.** category-theory, adjunction, RAPL, terminal, methods

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `unit_natural` | Definition | естественность unit сопряжения |
| `id_adjunction_unit_natural` | Lemma | unit тождественного сопряжения естественен |
| `right_adjoint_transpose_roundtrip` | Lemma | транспонирование туда-обратно = id |
| `right_adjoint_preserves_terminal` | Theorem | ★ правый сопряжённый сохраняет терминал |

**Key lemmas (deep):**

- **`right_adjoint_preserves_terminal`** - Фрагмент RAPL: правый сопряжённый сохраняет терминальный объект — доказано через roundtrip транспонирования сопряжения. Element-сторона теоремы RAPL; общий случай (все пределы) остаётся role-limit. _(RAPL, terminal, adjunction)_

**Uniqueness - score 2 (methods).** Фрагмент RAPL (правый сопряжённый сохраняет терминал) через roundtrip транспонирования, конструктивно.
> _Caveat:_ RAPL классична; доказан лишь терминальный фрагмент, общий случай не собран.

---

## #75 - `src/category/SetoidCategory.v` - score 2 (methods)

**The category of setoids (the cluster's base category)**

- **Topic.** Setoid (carrier + equivalence), SetoidMor (equality-respecting maps), identity/composition, morphism equality, SetoidCat as a Category, and the discrete-setoid embedding of types.
- **Role.** Foundational base of the whole category cluster (a constructive set-like topos). Self-contained.
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** Stdlib
- **E/R/R.** _Elements:_ сетоиды (носитель + эквивалентность); сетоид-морфизмы. _Roles:_ SetoidCat как базовая категория множеств-с-равенством; дискретный сетоид как роль-вложение типов. _Rules:_ setoid_id/comp; SetoidMorEq покомпонентно; SetoidCat — категория. _P4:_ сетоид-равенство = конструктивная интенсиональная идентичность (ToS); основа без классики.
- **Classical counterpart.** The category of setoids (sets-with-equivalence and equality-respecting maps) is classical constructive mathematics; NEW: nothing — the base SetoidCat construction the whole cluster builds on.
- **Tags.** category-theory, setoid, base-category, constructive, methods

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `Setoid` | Record | носитель + отношение эквивалентности |
| `SetoidMor` | Record | отображение, уважающее равенство |
| `setoid_id/setoid_comp/SetoidMorEq` | Definition | тождество, композиция, равенство морфизмов |
| `SetoidCat` | Definition | ★ категория сетоидов |
| `SetoidCat_mor_eq_iff/comp_map/id_map` | Lemma | свойства равенства/композиции/тождества |
| `discrete_setoid/discrete_mor` | Definition | дискретный сетоид типа и его морфизм |

**Key lemmas (deep):**

- **`SetoidCat`** - Категория сетоидов SetoidCat — базовый «конструктивный аналог Set», на котором строится весь кластер (классификатор, ДКЗ, (ко)пределы, Йонеда). Сетоид-равенство = интенсиональная идентичность ToS, без классических аксиом. _(setoid-category, base, constructive-set)_

**Uniqueness - score 2 (methods).** Категория сетоидов SetoidCat как конструктивная база-«Set» всего кластера (равенство = интенсиональная идентичность ToS).
> _Caveat:_ Сетоиды и их категория — стандартный конструктивизм; ценность — база топос-структуры, не новый результат.

---

## #76 - `src/category/SetoidClassifier.v` - score 2 (methods)

**The subobject classifier Omega in the setoid topos**

- **Topic.** The Prop-valued omega_setoid, the true arrow, the characteristic map char of a predicate, the sub-setoid and inclusion, the classifier commuting square and the subobject universal property (mediator unique).
- **Role.** Constructive topos ingredient (classifier). Builds on SetoidCategory.
- **Counts.** Qed 4 / Admitted 0 / axioms 0
- **Imports.** ToS SetoidCategory
- **E/R/R.** _Elements:_ omega-сетоид (Prop); предикаты на сетоиде; подсетоиды. _Roles:_ Omega как классификатор подобъектов; характеристическая функция char как роль. _Rules:_ char P; подсетоид + включение; квадрат классификатора коммутирует; медиатор единствен. _P4:_ субобъект-классификатор Omega конструктивен (Prop-сетоид) — ингредиент setoid-топоса без классики.
- **Classical counterpart.** The subobject classifier Omega and the subobject pullback square in a topos are classical; NEW: only its explicit setoid construction (Omega as a Prop-setoid, char map, subobject universal property), one ingredient of a constructive Setoid topos.
- **Tags.** category-theory, topos, subobject-classifier, setoid, methods

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `omega_setoid/setoid_true` | Definition | Omega=Prop-сетоид; стрелка true |
| `char` | Definition | характеристическая функция предиката |
| `char_self` | Lemma | char согласован с самим классификатором |
| `sub_setoid/sub_incl` | Definition | подсетоид по предикату и включение |
| `subobject_commute` | Lemma | ★ квадрат классификатора коммутирует |
| `subobject_mediator/subobject_univ/subobject_unique` | Definition/Lemma | ★ универсальное свойство (медиатор единствен) |

**Key lemmas (deep):**

- **`subobject_univ`** - Универсальное свойство классификатора подобъектов: всякий подобъект однозначно классифицируется характеристической стрелкой в Omega (медиатор существует и единствен). Ключевой ингредиент конструктивного setoid-ТОПОСА (вместе с CCC и (ко)пределами кластера). _(subobject-classifier, universal-property, topos)_
- **`subobject_commute`** - Квадрат классификатора коммутирует (подобъект = pullback true вдоль char) — определяющее свойство Omega, конструктивно над Prop-сетоидом. _(pullback, classifier)_

**Uniqueness - score 2 (methods).** Субобъект-классификатор Omega в setoid-топосе конструктивно (Prop-сетоид, char, универсальное свойство) — один ингредиент конструктивного топоса.
> _Caveat:_ Классификатор подобъектов — стандартная топос-теория; вклад — явная setoid-конструкция, не новый результат.

---

## #77 - `src/category/SetoidCoproducts.v` - score 1 (exposition)

**Coproducts and initial object in the setoid topos**

- **Topic.** The empty setoid (initial), the sum setoid with its relation, the two injections, the copairing mediator, and the coproduct universal property (beta laws + uniqueness).
- **Role.** Constructive topos ingredient (coproducts/initial). Builds on SetoidCategory.
- **Counts.** Qed 4 / Admitted 0 / axioms 0
- **Imports.** ToS SetoidCategory
- **E/R/R.** _Elements:_ пустой сетоид; сумма сетоидов; инъекции. _Roles:_ копроизведение/инициальный объект как универсальные роли. _Rules:_ inl/inr; copair-медиатор; beta-законы + единственность. _P4:_ копроизведения и инициальный объект конструктивны (setoid).
- **Classical counterpart.** Coproducts and the initial object in the category of setoids are classical; NEW: nothing — explicit setoid coproduct (sum), initial (empty), injections and the copairing universal property.
- **Tags.** category-theory, coproduct, initial, setoid, exposition

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `empty_setoid/setoid_initial` | Definition/Lemma | ★ пустой сетоид инициален |
| `sum_rel/sum_setoid` | Definition | отношение и сетоид суммы |
| `inl_mor/inr_mor` | Definition | инъекции в сумму |
| `sum_copair` | Definition | копарный медиатор |
| `coprod_beta1/beta2/coprod_unique` | Lemma | ★ универсальное свойство копроизведения |

**Key lemmas (deep):**

- **`coprod_unique`** - Универсальное свойство копроизведения: медиатор из суммы единствен (beta1/beta2 + uniqueness). Конструктивный ингредиент (ко)полноты setoid-топоса. _(coproduct, universal-property)_
- **`setoid_initial`** - Пустой сетоид инициален (единственный морфизм из него куда угодно) — нижний (ко)предел, дополняющий терминал из SetoidProducts. _(initial, colimit)_

**Uniqueness - score 1 (exposition).** Копроизведения (сумма) и инициальный объект (пустой) в setoid-топосе с универсальным свойством.
> _Caveat:_ Стандартная конструкция; ингредиент (ко)полноты топоса.

---

## #78 - `src/category/SetoidEqualizers.v` - score 1 (exposition)

**Equalizers in the setoid topos**

- **Topic.** The equalizer setoid (points where f=g), its inclusion, the mediator from any equalizing map, that it equalizes, and the universal property (uniqueness).
- **Role.** Constructive topos ingredient (equalizers => limits). Builds on SetoidCategory.
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** ToS SetoidCategory
- **E/R/R.** _Elements:_ сетоиды A,B; пара морфизмов f,g; уравнитель (где f=g). _Roles:_ уравнитель как универсальный предел пары стрелок. _Rules:_ eq_setoid = {x: f x = g x}; включение; медиатор; единственность. _P4:_ уравнители конструктивны (подсетоид), дают конечные пределы топоса.
- **Classical counterpart.** Equalizers in the category of setoids are classical; NEW: nothing — the explicit setoid equalizer (sub-setoid where f=g), inclusion, mediator and universal property.
- **Tags.** category-theory, equalizer, limit, setoid, exposition

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `eq_setoid/eq_incl` | Definition | сетоид-уравнитель и его включение |
| `eq_mediator` | Definition | медиатор из уравнивающего морфизма |
| `eq_equalizes` | Lemma | включение уравнивает f,g |
| `eq_univ/eq_unique` | Lemma | ★ универсальное свойство (единственность) |

**Key lemmas (deep):**

- **`eq_univ`** - Универсальное свойство уравнителя: любой уравнивающий морфизм пропускается единственно через включение. Вместе с произведениями (SetoidProducts) даёт ВСЕ конечные пределы setoid-топоса. _(equalizer, limit, universal-property)_

**Uniqueness - score 1 (exposition).** Уравнители в setoid-топосе (подсетоид f=g) с универсальным свойством — с произведениями дают конечные пределы.
> _Caveat:_ Стандартная конструкция; ингредиент полноты топоса.

---

## #79 - `src/category/SetoidExponential.v` - score 2 (methods)

**Exponentials in the setoid topos (cartesian closure)**

- **Topic.** The exponential setoid of morphisms A->B, evaluation, currying of a map from C*A, and the exponential beta law and uniqueness (the CCC structure).
- **Role.** Constructive topos ingredient (cartesian closure). Builds on SetoidProducts.
- **Counts.** Qed 2 / Admitted 0 / axioms 0
- **Imports.** ToS SetoidCategory, SetoidProducts
- **E/R/R.** _Elements:_ сетоид экспоненты B^A; вычисление eval; каррирование. _Roles:_ экспонента как роль-внутренний-hom; CCC-структура. _Rules:_ setoid_eval; setoid_curry; beta + единственность. _P4:_ декартова замкнутость конструктивна (setoid-экспонента).
- **Classical counterpart.** Exponential objects (cartesian closure) in the category of setoids are classical; NEW: nothing — the explicit exponential setoid B^A, evaluation, currying and the beta/uniqueness laws.
- **Tags.** category-theory, exponential, CCC, setoid, methods

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `exp_setoid` | Definition | сетоид морфизмов A→B (экспонента) |
| `setoid_eval` | Definition | вычисление eval: B^A × A → B |
| `curry_app/setoid_curry` | Definition | каррирование морфизма из C×A |
| `exp_beta` | Lemma | ★ beta-закон экспоненты |
| `exp_unique` | Lemma | ★ единственность каррирования (CCC) |

**Key lemmas (deep):**

- **`exp_unique`** - Единственность каррирования (вместе с beta) — определяющее свойство экспоненциального объекта, делающее setoid-топос ДЕКАРТОВО ЗАМКНУТЫМ (CCC). Внутренний hom для интерпретации функциональных типов конструктивно. _(exponential, CCC, universal-property)_

**Uniqueness - score 2 (methods).** Экспоненты B^A в setoid-топосе (eval, curry, beta, единственность) — декартова замкнутость конструктивно.
> _Caveat:_ CCC-структура сетоидов стандартна; вклад — явная конструкция, ингредиент топоса.

---

## #80 - `src/category/SetoidProducts.v` - score 1 (exposition)

**Products and terminal object in the setoid topos**

- **Topic.** The unit setoid (terminal), the product setoid, the two projections, the pairing mediator, and the product universal property (beta laws + uniqueness).
- **Role.** Constructive topos ingredient (products/terminal => with equalizers, all finite limits). Builds on SetoidCategory.
- **Counts.** Qed 4 / Admitted 0 / axioms 0
- **Imports.** ToS SetoidCategory
- **E/R/R.** _Elements:_ unit-сетоид; произведение сетоидов; проекции. _Roles:_ произведение/терминальный объект как универсальные роли. _Rules:_ fst/snd; pair-медиатор; beta-законы + единственность. _P4:_ произведения и терминал конструктивны; с уравнителями — все конечные пределы.
- **Classical counterpart.** Products and the terminal object in the category of setoids are classical; NEW: nothing — explicit product setoid, terminal (unit), projections and the pairing universal property.
- **Tags.** category-theory, product, terminal, setoid, exposition

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `unit_setoid/setoid_terminal` | Definition/Lemma | ★ unit-сетоид терминален |
| `prod_setoid` | Definition | произведение сетоидов |
| `setoid_fst/setoid_snd` | Definition | проекции |
| `setoid_pair` | Definition | парный медиатор |
| `setoid_prod_beta1/beta2/prod_unique` | Lemma | ★ универсальное свойство произведения |

**Key lemmas (deep):**

- **`setoid_prod_unique`** - Универсальное свойство произведения: медиатор в произведение единствен (beta1/beta2 + uniqueness). С уравнителями (SetoidEqualizers) даёт ВСЕ конечные пределы setoid-топоса. _(product, limit, universal-property)_
- **`setoid_terminal`** - Unit-сетоид терминален — вершина конечных пределов, дополняющая инициальный из SetoidCoproducts. _(terminal, limit)_

**Uniqueness - score 1 (exposition).** Произведения и терминал в setoid-топосе с универсальным свойством — с уравнителями дают все конечные пределы.
> _Caveat:_ Стандартная конструкция; ингредиент полноты топоса.

---

## #81 - `src/category/YonedaEmbedding.v` - score 2 (methods)

**The Yoneda embedding is fully faithful**

- **Topic.** The Yoneda embedding on morphisms, its component description, and that it is faithful and full.
- **Role.** Constructive category theory: Yoneda embedding. Builds on YonedaLemma/representables.
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** ToS category core, YonedaLemma
- **E/R/R.** _Elements:_ объекты категории; представимые функторы; морфизмы. _Roles:_ вложение Йонеды как полно-верный функтор C↪[C^op,Set]. _Rules:_ yoneda_embed_mor; верность и полнота. _P4:_ вложение Йонеды конструктивно полно-верно (setoid).
- **Classical counterpart.** The Yoneda embedding and its full faithfulness are classical; NEW: nothing — the setoid formalization (the embedding on morphisms, faithful and full).
- **Tags.** category-theory, yoneda, embedding, fully-faithful, setoid, methods

**Lemmas (4):**

| name | kind | role |
|---|---|---|
| `yoneda_embed_mor` | Definition | вложение Йонеды на морфизмах |
| `yoneda_embed_mor_component` | Lemma | компонентное описание вложения |
| `yoneda_faithful` | Lemma | ★ вложение Йонеды верно |
| `yoneda_full` | Lemma | ★ вложение Йонеды полно |

**Key lemmas (deep):**

- **`yoneda_full`** - Вложение Йонеды полно (всякое естественное преобразование представимых = образ морфизма) — вместе с верностью даёт полно-верность C↪[C^op,Set], конструктивно над сетоидами. Структурное ядро «объекты познаются по морфизмам в них». _(yoneda, full, embedding)_

**Uniqueness - score 2 (methods).** Вложение Йонеды полно-верно конструктивно над сетоидами (верность + полнота).
> _Caveat:_ Полно-верность Йонеды — фундаментальная классика; вклад — setoid-формализация, не новый результат.

---

## #82 - `src/category/YonedaLemma.v` - score 2 (methods)

**The Yoneda lemma over setoids**

- **Topic.** The hom-setoid, the representable functor, the two Yoneda transposes (to/from F x), the roundtrip isomorphisms and uniqueness.
- **Role.** Constructive category theory: the Yoneda lemma. Builds on FunctorCategory/SetoidCategory.
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** ToS category core, FunctorCategory
- **E/R/R.** _Elements:_ hom-сетоид Hom(x,a); представимый функтор; элементы F x. _Roles:_ лемма Йонеды как естественный изоморфизм Nat(Hom(x,−),F) ≅ F x. _Rules:_ yoneda_to/from; roundtrip = id; единственность. _P4:_ лемма Йонеды конструктивна (setoid), естественный изоморфизм без классики.
- **Classical counterpart.** The Yoneda lemma (Nat(Hom(x,-),F) ~ F x) is classical; NEW: nothing — the setoid formalization (representable functor, the two transposes, roundtrips and uniqueness).
- **Tags.** category-theory, yoneda, representable, setoid, methods

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `hom_setoid` | Definition | сетоид морфизмов Hom(x,a) |
| `representable` | Definition | представимый функтор Hom(x,−) |
| `yoneda_to/yoneda_from` | Definition | две стороны изоморфизма Йонеды |
| `yoneda_to_from/yoneda_from_to` | Lemma | ★ roundtrip = id (изоморфизм) |
| `yoneda_unique` | Lemma | единственность |

**Key lemmas (deep):**

- **`yoneda_to_from`** - Roundtrip yoneda_to∘yoneda_from=id (и обратно) — устанавливает естественный изоморфизм Nat(Hom(x,−),F)≅F x, сердце леммы Йонеды, конструктивно над сетоидами. Фундамент представимости и вложения Йонеды. _(yoneda-lemma, isomorphism, representable)_

**Uniqueness - score 2 (methods).** Лемма Йонеды (Nat(Hom(x,−),F)≅F x) конструктивно над сетоидами через два транспонирования и roundtrip.
> _Caveat:_ Лемма Йонеды — фундаментальная классика; вклад — setoid-формализация, не новый результат.

