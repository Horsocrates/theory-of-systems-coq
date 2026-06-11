# Database - cluster `algebra`

_Generated from `algebra.json` by `generate.ps1` - do not edit by hand; edit the JSON._

**12 files / 156 Qed.** Score distribution: s5=1 / s4=5 / s3=3 / s2=3 / s1=0 / s0=0

---

## #18 - `src/algebra/AlgebraicClosureProcess.v` - score 4 (synthesis+observation)

**Q-bar as a PROCESS, not a completed object: the ascending tower of finite extensions**

- **Topic.** The algebraic closure of Q recast as an ascending tower (rungs = finite extensions) with strictly increasing dimensions: no maximal rung, every closure element sited at a finite rung (direct limit). Concrete multiquadratic skeleton (dims 2^n) whose rung 2 IS the GaloisQ23 field.
- **Role.** Vein C (X = process) applied to the algebraic closure. Self-contained (QArith/List/Eqdep_dec). Concrete rung 2 ties to GaloisDegreeQ23.ext_degree = 4.
- **Counts.** Qed 14 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith List PeanoNat Lia Eqdep_dec
- **E/R/R.** _Elements:_ конечные расширения (rungs) и элементы, сидящие на конечном rung; germ = пара (n, элемент rung n). _Roles:_ алгебраическое замыкание = role-limit восходящей башни; multiquadratic = конкретный непустой скелет. _Rules:_ вложения rung_n ↪ rung_{n+1}; размерности строго растут; germ_of сшивает rung'и в colimit. _P4:_ Q-bar — ПРОЦЕСС, не завершённый объект: каждое алгебраическое число = конечные данные на каком-то rung; «единый объект со всеми корнями» = платонистский излишек, отброшен; Q-bar P4-актуальнее R.
- **Classical counterpart.** The algebraic closure of Q and its construction as a direct limit of finite extensions are classical; NEW is only the P4 'process not completed object' reframing (keep the rule 'the roots of any rational polynomial lie in SOME finite extension', drop the platonist surplus of one object holding all roots), executed axiom-free incl. no UIP.
- **Tags.** process-ontology, algebraic-closure, vein-C, direct-limit, tower, P4

**Lemmas (19):**

| name | kind | role |
|---|---|---|
| `AlgTower` | Record | абстрактная башня: rungs, размерности cdim, вложения |
| `tower_height_le_dim` | Lemma | n ≤ cdim T n (высота ограничена размерностью) |
| `no_maximal_rung` | Theorem | ★ ни один конечный rung не есть всё замыкание |
| `tower_unbounded` | Theorem | размерности превосходят любую конечную границу |
| `rung_embeds_faithfully` | Lemma | вложения — настоящие инъекции (decidable eq на ℕ, без UIP) |
| `Germ` | Definition | элемент colimit'а: { n & carrier T n } |
| `germ_of` | Definition | вложение элемента rung n в Germ |
| `germ_finitely_sited` | Theorem | ★ каждый элемент замыкания живёт на КОНЕЧНОМ rung (direct limit) |
| `germ_of_inj` | Lemma | germ_of инъективно |
| `closure_is_a_process` | Theorem | ★ замыкание = процесс над конечными элементами, не завершённая тотальность |
| `pad` | Definition | zero-padding вложение list Q (скелет удвоения размерности) |
| `pad_length` | Lemma | length (pad l) = 2·length l |
| `pad_firstn` | Lemma | pad сохраняет исходный префикс |
| `pad_inj` | Lemma | pad инъективно |
| `two_pow_grows` | Lemma | 2^n < 2^(S n) |
| `multiquadratic` | Definition | конкретная башня dims 2^n (1,2,4,8,…) |
| `rung0_dim` | Example | cdim 0 = 1 (Q) |
| `rung1_dim` | Example | cdim 1 = 2 (Q[√2]) |
| `rung2_dim` | Example | cdim 2 = 4 (= [Q[√2,√3]:Q] = GaloisQ23) |

**Key lemmas (deep):**

- **`germ_finitely_sited`** - Онтологический payload: каждый элемент замыкания (colimit'а) живёт на НЕКОТОРОМ конечном rung — замыкание есть прямой предел, процесс над конечными элементами, никогда не актуально завершённая тотальность. Это формальное ядро тезиса «Q-bar = процесс»: то, что классика называет «построением замыкания как объекта», расщепляется на конструктивное правило + платонистский излишек. _(direct-limit, process-ontology, P4)_
- **`no_maximal_rung`** - Ни один конечный rung не исчерпывает замыкание (размерности строго растут) — role-limit-сторона: башня не имеет максимума. Вместе с germ_finitely_sited даёт точную картину «бесконечность = свойство восходящего правила, не объекта». _(role-limit, tower, unbounded)_

**Uniqueness - score 4 (synthesis+observation).** Вена C на алгебраическом замыкании: Q-bar как аксиомо-свободный процесс-башня (no maximal rung, germ finitely sited) с конкретным multiquadratic-скелетом, rung 2 которого ЕСТЬ поле GaloisQ23. Замыкание = direct limit, не стена-объект.
> _Caveat:_ Конструкция прямого предела стандартна (Bishop/конструктивизм); вклад — онтологическое переобрамление P4 + аксиомо-свободное (без UIP) исполнение, не новая алгебра.

---

## #19 - `src/algebra/FieldExtension.v` - score 2 (methods)

**Polynomial machinery over Q: minimal polynomials and extension degree**

- **Topic.** eval_poly / poly_degree / poly_add / poly_scale over Q-coefficient lists; the minimal polynomials x^2-2 (degree 2) and x^3-2 (degree 3), non-root checks at rationals, and the concrete tower law 3*2=6.
- **Role.** Foundational polynomial layer beneath the Galois cluster. Self-contained (QArith).
- **Counts.** Qed 20 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith
- **E/R/R.** _Elements:_ полиномы над Q (списки коэффициентов); рациональные точки. _Roles:_ степень расширения = степень минимального полинома; корень = роль обнуления. _Rules:_ eval_poly (Горнер), poly_add/scale, poly_degree = pred(length); is_root = eval ≡ 0. _P4:_ степень = конечные данные расширения; минимальный полином — конечный сертификат алгебраичности элемента.
- **Classical counterpart.** Polynomial evaluation, minimal polynomials (x^2-2 of degree 2, x^3-2 of degree 3) and the tower law are standard field theory; NEW: nothing — foundational polynomial machinery supporting the Galois files.
- **Tags.** polynomials, field-extension, minimal-polynomial, tower-law, infrastructure

**Lemmas (22):**

| name | kind | role |
|---|---|---|
| `eval_poly` | Fixpoint | вычисление полинома в точке (схема Горнера) |
| `poly_degree` | Definition | степень = pred(length коэффициентов) |
| `is_root` | Definition | eval_poly p x ≡ 0 |
| `poly_add` | Fixpoint | сложение полиномов |
| `poly_scale` | Fixpoint | умножение на скаляр |
| `eval_poly_nil/const/linear/quadratic` | Lemma | вычисление для пустого/константы/линейного/квадратичного |
| `degree_of_x2_minus_2` | Lemma | deg[x²−2]=2 |
| `degree_of_x3_minus_2` | Lemma | deg[x³−2]=3 |
| `degree_of_linear/constant` | Lemma | deg линейного=1, константы=0 |
| `sqrt2_poly` | Definition | минимальный полином √2 = [−2;0;1] |
| `sqrt2_poly_at_x` | Lemma | значение x²−2 |
| `sqrt2_root_approx` | Lemma | приближённый корень √2 |
| `one_not_root_sqrt2` | Lemma | 1 не корень x²−2 |
| `three_halves_not_root_sqrt2` | Lemma | 3/2 не корень |
| `seven_fifths_not_root_sqrt2` | Lemma | 7/5 не корень |
| `cbrt2_poly` | Definition | минимальный полином ∛2 = [−2;0;0;1] |
| `cbrt2_poly_at_x` | Lemma | значение x³−2 |
| `five_fourths_not_root_cbrt2` | Lemma | 5/4 не корень x³−2 |
| `ext_degree_sqrt2_is_2` | Lemma | [Q[√2]:Q]=2 |
| `ext_degree_cbrt2_is_3` | Lemma | [Q[∛2]:Q]=3 |
| `tower_law_concrete` | Lemma | конкретный tower law 3·2=6 |
| `eval_poly_add/scale` | Lemma | eval гомоморфно по add/scale |

**Key lemmas (deep):**

- **`ext_degree_cbrt2_is_3`** - Степень расширения как степень минимального полинома: [Q[∛2]:Q]=3 (x³−2). Вместе с ext_degree_sqrt2_is_2 даёт конечно-данную интерпретацию степени; ∛2 — degree-3 role-limit (связь с CubicRoleLimit / Делийская задача в q-kinematics). _(extension-degree, minimal-polynomial, cubic)_
- **`tower_law_concrete`** - Конкретная мультипликативность степеней 3·2=6 — арифметический скелет tower law, на котором стоят GaloisDegreeQ23 (2·2=4) и общая башня. _(tower-law, degree)_

**Uniqueness - score 2 (methods).** Базовая полиномиальная машина над Q (eval/degree/add/scale) + минимальные полиномы √2,∛2 и конкретный tower law — фундамент под Галуа-кластер.
> _Caveat:_ Полностью стандартная теория полей; ценность чисто инфраструктурная (опора для GaloisQ23/Degree).

---

## #20 - `src/algebra/FiniteFieldFp.v` - score 2 (methods)

**Finite fields F_5, F_7 by computation + Fermat's little theorem**

- **Topic.** Concrete finite fields F_5 and F_7: explicit inverse tables (every nonzero residue invertible), Fermat's little theorem a^(p-1) = 1 mod p for these primes, and 0 has no inverse.
- **Role.** Closes a 'no finite fields' gap with concrete instances. Self-contained (Arith/Lia).
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith Lia
- **E/R/R.** _Elements:_ вычеты 0..p-1; операции mod p. _Roles:_ ненулевой вычет = единица (обратимый); 0 = не-единица. _Rules:_ для простого p всякий ненулевой вычет обратим ⟹ F_p поле; Ферма a^(p−1)≡1. _P4:_ конкретные поля F5/F7 проверены вычислением (Element); общий случай «p просто ⟹ F_p поле» = role-limit (нужен Безу).
- **Classical counterpart.** Finite fields F_p = Z/pZ and Fermat's little theorem are classical; NEW: nothing — concrete F5/F7 by computation closing a 'no finite fields' gap; honest gap: general 'p prime => F_p a field' needs Bezout/modular inverse.
- **Tags.** finite-field, fermat, computation, concrete, methods
- **Notes.** Header STATUS says 7 Qed; actual Qed count = 6. Drift flagged.

**Lemmas (10):**

| name | kind | role |
|---|---|---|
| `fp_add/fp_mul` | Definition | сложение/умножение mod p |
| `has_inverses` | Definition | у каждого ненулевого вычета есть обратный |
| `inv5` | Definition | таблица обратных в F5 |
| `F5_field` | Theorem | ★ F5 — поле (все ненулевые обратимы) |
| `inv7` | Definition | таблица обратных в F7 |
| `F7_field` | Theorem | ★ F7 — поле |
| `fermat5` | Theorem | a⁴ ≡ 1 mod 5 (1≤a≤4) |
| `fermat7` | Theorem | a⁶ ≡ 1 mod 7 (1≤a≤6) |
| `zero_no_inverse_F7` | Theorem | 0 не имеет обратного в F7 |
| `inv7_in_range` | Theorem | inv7 остаётся в 1..6 |

**Key lemmas (deep):**

- **`F5_field`** - Конкретное поле: явная таблица обратных inv5 проверяет, что каждый ненулевой вычет F5 обратим — вычислительное свидетельство «F_p поле» для p=5. Закрывает gap честно (по вычислению), не претендуя на общий случай. _(finite-field, computation, concrete)_
- **`fermat7`** - Малая теорема Ферма для p=7: a⁶≡1 mod 7 для всех ненулевых a — проверена перебором 1..6. Конечно-актуальная форма (P4) теоретико-числового факта. _(fermat, concrete)_

**Uniqueness - score 2 (methods).** Конкретные F5/F7 как поля (явные таблицы обратных) + Ферма по вычислению — закрытие gap «нет конечных полей».
> _Caveat:_ Конечные поля и Ферма классичны; вклад — конкретные инстансы по вычислению; общий «p просто ⟹ поле» оставлен фронтиром (нужен Безу). Заголовок STATUS пишет 7 Qed, фактически 6.

---

## #21 - `src/algebra/GaloisCorrespondence.v` - score 3 (new-framing)

**Galois correspondence as numeric coincidences; quintic unsolvable (count level)**

- **Topic.** Subgroup-count = field-count matches for Z/2 (2) and V4 (5), order=degree, V4 abelian, and the Abel-Ruffini chain at the count level: S5 order 120, A5 order 60 simple, quintic group = S5 not solvable by radicals.
- **Role.** The numeric-coincidence version that GaloisQ23.v upgrades to a genuine concrete correspondence. Self-contained (QArith).
- **Counts.** Qed 21 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Qabs Lia ZArith List Bool Lqa PeanoNat
- **E/R/R.** _Elements:_ подгруппы, промежуточные поля, степени расширений (как nat-счётчики). _Roles:_ соответствие Галуа (биекция), разрешимость (цепь); A5 как простая. _Rules:_ subgroup count = field count, normal ↔ Galois, A5 проста ⟹ квинтика неразрешима. _P4:_ настоящее соответствие здесь — role-limit (только счётчики совпадают); конкретные автоморфизмы строятся в GaloisQ23 (Element-сторона).
- **Classical counterpart.** The Galois correspondence and Abel-Ruffini (quintic unsolvable; S5 with simple A5) are classical; HERE they appear only as NUMERIC coincidences (subgroup counts = field counts, \|Gal\|=degree, A5 simple => quintic unsolvable) — UPGRADED to the real automorphism action by GaloisQ23.v. NEW: only the count-level skeleton.
- **Tags.** galois, correspondence, abel-ruffini, quintic, count, new-framing
- **Notes.** Header STATUS says 20 Qed; actual Qed count = 21. Drift flagged.

**Lemmas (18):**

| name | kind | role |
|---|---|---|
| `z2_subgroups` | Lemma | Z/2 имеет 2 подгруппы |
| `quadratic_intermediate_fields` | Lemma | 2 промежуточных поля квадратичного |
| `correspondence_quadratic` | Lemma | счёт подгрупп = счёт полей (Z/2) |
| `klein_four_subgroups` | Lemma | V4 имеет 5 подгрупп |
| `v4_order_is_4` | Lemma | \|V4\|=4 |
| `biquadratic_fields` | Lemma | 5 промежуточных полей бикватичного |
| `correspondence_biquadratic` | Lemma | ★ счёт подгрупп = счёт полей (V4=5) |
| `order_equals_degree_quadratic/biquadratic` | Lemma | \|Gal\| = степень |
| `v4_is_abelian` | Lemma | 2·2=\|V4\| (абелевость через счёт) |
| `normal_subgroup_galois_abelian` | Lemma | нормальность ↔ Галуа (абелев случай) |
| `s5_order_is_120` | Lemma | \|S5\|=120 |
| `a5_order_is_60` | Lemma | \|A5\|=60 |
| `a5_is_simple` | Lemma | A5 проста (как счётчик нормальных подгрупп=2) |
| `s5_not_solvable` | Lemma | S5 неразрешима (флаг) |
| `quintic_group_is_s5` | Lemma | группа квинтики = S5 |
| `quintic_not_solvable_by_radicals` | Lemma | ★ квинтика неразрешима в радикалах (вывод Абеля-Руффини на счётном уровне) |
| `lagrange_v4_trivial/z2/full` | Lemma | Лагранж: делимость порядков подгрупп V4 |
| `index_v4_z2` | Lemma | индекс [V4:Z2]=2 |

**Key lemmas (deep):**

- **`correspondence_biquadratic`** - Сердце count-level соответствия: V4 имеет 5 подгрупп и расширение Q[√2,√3] — 5 промежуточных полей, числа совпадают. Это «численное совпадение», которое GaloisQ23.v честно ПОВЫШАЕТ до настоящей биекции с реальным действием автоморфизмов — здесь же только счётчики. _(correspondence, count, V4)_
- **`quintic_not_solvable_by_radicals`** - Вывод Абеля-Руффини на счётном уровне: группа квинтики = S5, её коммутант A5 прост (счётчик нормальных подгрупп = 2), значит неразрешима в радикалах. Настоящая (не-счётная) простота A5 и эквивалентность радикалы⟺разрешимая-группа остаются role-limit (SolvableGroup даёт абстрактный движок). _(abel-ruffini, quintic, count)_

**Uniqueness - score 3 (new-framing).** Соответствие Галуа и Абель-Руффини как численные совпадения (счёт подгрупп = счёт полей, |Gal|=степень, A5 проста ⟹ квинтика неразрешима) — счётный скелет, повышаемый до настоящего действия в GaloisQ23.
> _Caveat:_ Совпадают только ЧИСЛА; файл НЕ строит автоморфизмы (это флагман GaloisQ23) и принимает простоту A5 как счётчик. Честно как численный каркас. Заголовок STATUS пишет 20 Qed, фактически 21.

---

## #22 - `src/algebra/GaloisDegreeQ23.v` - score 4 (synthesis+observation)

**[E:Q] = |Gal(E/Q)| = 4 for E = Q[sqrt2, sqrt3], with tower law 2*2=4**

- **Topic.** The four automorphisms id, sigma, tau, sigma*tau are pairwise distinct (witnessed on sqrt2, sqrt3), so |Gal| = 4; the basis {1,sqrt2,sqrt3,sqrt6} gives degree 4; the tower law [E:Q]=[E:Q[sqrt2]]*[Q[sqrt2]:Q]=2*2=4 holds.
- **Role.** Vein D flagship component. Builds on GaloisQ23.v. Degree-order match for the concrete model.
- **Counts.** Qed 7 / Admitted 0 / axioms 0
- **Imports.** ToS: algebra.GaloisQ23; Stdlib: QArith Lqa Arith
- **E/R/R.** _Elements:_ четыре автоморфизма, действующие различно на базисные сурды. _Roles:_ порядок Галуа как счёт ролей; степень расширения как размерность базиса. _Rules:_ 4 попарно различных автоморфизма ⟹ \|Gal\|=4=[E:Q]; башня 2·2=4. _P4:_ степень = \|Gal\| на конкретной модели (Element); верность реальному полю (Q-линейная независимость сурдов) = фронтир/role-limit.
- **Classical counterpart.** The degree=order theorem ([E:Q]=\|Gal(E/Q)\|) and the tower law are classical FTGT; NEW is the fully explicit concrete instance for Q[sqrt2,sqrt3], with the four automorphisms witnessed PAIRWISE DISTINCT by their action on the basis surds. Caveat: faithfulness to the real field rests on irrationality results (frontier).
- **Tags.** galois, degree, vein-D, tower-law, V4, concrete
- **Notes.** Header STATUS says 8 Qed; actual Qed count = 7. Drift flagged.

**Lemmas (8):**

| name | kind | role |
|---|---|---|
| `st_neq_id` | Lemma | στ ≠ id (на √2) |
| `sig_neq_tau` | Lemma | σ ≠ τ (на √2) |
| `sig_neq_st` | Lemma | σ ≠ στ (на √3) |
| `tau_neq_st` | Lemma | τ ≠ στ (на √2) |
| `galois_group_four_distinct` | Theorem | ★ четыре автоморфизма попарно различны ⟹ \|Gal\|=4 |
| `ext_degree/galois_order/sub_degree_sqrt2/rel_degree` | Definition | степени и порядок как nat (4,4,2,2) |
| `degree_equals_galois_order` | Theorem | ext_degree = galois_order (4=4) |
| `tower_law` | Theorem | ★ 2·2 = 4 (мультипликативность степеней) |

**Key lemmas (deep):**

- **`galois_group_four_distinct`** - Ядро degree-order совпадения: четыре автоморфизма id/σ/τ/στ ПОПАРНО различны, засвидетельствовано их действием на √2 и √3 — значит V4 имеет порядок ровно 4. Делает \|Gal\|=4 не постулатом, а следствием конкретного различения ролей. _(galois-order, distinctness, V4)_
- **`tower_law`** - Мультипликативность степеней 2·2=4 на конкретной башне Q⊂Q[√2]⊂E. Вместе с IndependenceQ23 (√3∉Q[√2]) делает обе ступени настоящими degree-2 расширениями. _(tower-law, degree)_

**Uniqueness - score 4 (synthesis+observation).** Полностью явное degree=order совпадение [E:Q]=|Gal|=4 для конкретного Q[√2,√3]: четыре автоморфизма засвидетельствованы попарно различными действием на базисные сурды + tower law 2·2.
> _Caveat:_ Теорема degree=order и tower law классичны (FTGT); вклад — явный конкретный инстанс; верность реальному полю опирается на иррациональности (фронтир, не пере-доказано). Заголовок STATUS пишет 8 Qed, фактически 7.

---

## #23 - `src/algebra/GaloisGroup.v` - score 2 (methods)

**Concrete permutation groups S3 / Z2 and the quadratic discriminant**

- **Topic.** Permutations as nat->nat: transpositions and 3-cycles of S3, S3 non-commutative, orders (|S3|=6, |Z2|=2), and the quadratic discriminant (disc[x^2-2], disc[x^2-3]).
- **Role.** Concrete group-theory support beneath the Galois cluster. Self-contained.
- **Counts.** Qed 18 / Admitted 0 / axioms 0
- **Imports.** Stdlib
- **E/R/R.** _Elements:_ перестановки nat→nat; транспозиции, 3-циклы. _Roles:_ элементы группы и их порядки; дискриминант как роль типа корней. _Rules:_ perm_compose, transpose; дискриминант b²−4c; орбиты-инволюции. _P4:_ конкретные конечные группы, всё вычислимо (Element); S3 неабелева = источник неразрешимости (связь с SolvableGroup).
- **Classical counterpart.** The symmetric group S3 (transpositions, 3-cycles, non-commutativity) and the quadratic discriminant b^2-4c are textbook; NEW: nothing — concrete permutation-group computations supporting the Galois files.
- **Tags.** group-theory, S3, permutations, discriminant, methods

**Lemmas (15):**

| name | kind | role |
|---|---|---|
| `Perm/perm_id/perm_compose/transpose` | Definition | перестановки и операции |
| `s3_*` | Definition | элементы S3 (id, транспозиции, 3-циклы) |
| `perm_id_left/right` | Lemma | id — нейтраль композиции |
| `transpose_self` | Lemma | транспозиция инволютивна |
| `transpose_involution_concrete_12/13/23` | Lemma | конкретные инволюции |
| `s3_non_commutative` | Lemma | ★ S3 неабелева |
| `s3_12_23_at_1 / s3_23_12_at_1` | Lemma | свидетели некоммутативности (2 ≠ 3) |
| `s3_order_is_factorial` | Lemma | \|S3\|=3·2·1=6 |
| `gal_quadratic_order` | Lemma | \|Gal квадратичного\|=2 |
| `gal_cubic_max_order` | Lemma | порядок кубической ≤ 6 |
| `discriminant_quadratic` | Definition | b²−4c |
| `discriminant_x2_minus_2/3` | Lemma | дискриминанты x²−2, x²−3 |
| `three_cycle_order/132_order` | Lemma | 3-циклы имеют порядок 3 |
| `three_cycles_inverse` | Lemma | 3-циклы взаимно обратны |
| `z2_is_abelian` | Lemma | Z2 абелева |

**Key lemmas (deep):**

- **`s3_non_commutative`** - S3 неабелева (свидетели s3_12_23_at_1=2 vs s3_23_12_at_1=3) — корень неразрешимости кубики/квинтики на уровне групп: некоммутативность = нетривиальный коммутант. Стыкуется с SolvableGroup (perfect⇒не-solvable). _(S3, non-commutative, unsolvability)_
- **`discriminant_x2_minus_2`** - Дискриминант b²−4c квадратичного минимального полинома — та же дискриминантная ручка, что в BoundaryDecidability (вена A): квадрат ⟺ рациональный корень. Здесь — вход в группу Галуа квадратичного. _(discriminant, vein-A-link)_

**Uniqueness - score 2 (methods).** Конкретные перестановочные группы S3/Z2 (некоммутативность, порядки, 3-циклы) + квадратичный дискриминант — групповая опора Галуа-кластера.
> _Caveat:_ Полностью стандартная теория групп; ценность инфраструктурная. Дискриминант перекликается с веной A, но здесь без второпорядковой рамки.

---

## #24 - `src/algebra/GaloisQ23.v` - score 5 (synthesis+observation)

**The REAL concrete Galois correspondence Q[sqrt2,sqrt3] = V4, with genuine automorphism action**

- **Topic.** Builds the field Q[sqrt2,sqrt3] as 4-tuples, the four automorphisms id/sigma/tau/sigma*tau as ring homomorphisms fixing Q, proves the group is the Klein four-group V4, and exhibits the subgroup<->intermediate-field bijection explicitly, inclusion-reversing.
- **Role.** FLAGSHIP of vein D (unusually-complete concrete formalization). Foundation for GaloisDegreeQ23, IndependenceQ23, SplittingFieldQ23. Self-contained (QArith/Lqa).
- **Counts.** Qed 26 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith Lqa
- **E/R/R.** _Elements:_ a + b√2 + c√3 + d√6 (4-мерное Q-векторное пространство). _Roles:_ четыре автоморфизма id/σ/τ/στ как полевые отображения, фиксирующие Q; подгруппы V4 как роли симметрии. _Rules:_ σ:√2↦−√2, τ:√3↦−√3; каждое — кольцевой гомоморфизм, фиксирующий Q; фиксированные подполя ↔ подгруппы, обращая включение. _P4:_ конкретные конечные данные Галуа полностью актуальны (Element); абстрактный Aut(L/K) для произвольного L/K остаётся role-limit.
- **Classical counterpart.** The Fundamental Theorem of Galois Theory is classical; NEW is the unusually COMPLETE explicit formalization of one nontrivial instance (Q[sqrt2,sqrt3]) with the actual automorphisms as ring homomorphisms and the inclusion-reversing subgroup<->subfield bijection exhibited — versus the abstract-theory approach standard in proof libraries. Caveat: a concrete instance, not the abstract functor Aut(L/K).
- **Tags.** galois, vein-D, V4, concrete, FTGT, ring-homomorphism, flagship

**Lemmas (17):**

| name | kind | role |
|---|---|---|
| `E` | Record | элемент поля: {c0;c1;c2;c3} = a+b√2+c√3+d√6 |
| `Eeq/Eadd/Emul/Eofq` | Definition | равенство, кольцо, вложение Q |
| `a_id/a_sig/a_tau/a_st` | Definition | четыре автоморфизма |
| `Eeq_refl/sym/trans` | Lemma | Eeq — отношение эквивалентности |
| `sig_add/tau_add/st_add` | Lemma | автоморфизмы аддитивны |
| `sig_mul/tau_mul/st_mul` | Lemma | ★ автоморфизмы мультипликативны (кольцевые гомоморфизмы) |
| `sig_fixes_base/tau/st` | Lemma | фиксируют Q |
| `sig_invol/tau/st` | Lemma | инволютивны (порядок 2) |
| `sig_tau_eq_st / tau_sig_eq_st` | Lemma | σ∘τ=στ=τ∘σ (структура V4) |
| `V4_abelian` | Lemma | ★ группа абелева = Клейнова четверная V4 |
| `fixed_by` | Definition | φ фиксирует u |
| `fix_sig_iff/tau/st` | Lemma | характеризация фиксированных подполей каждого σ/τ/στ |
| `fix_V4_iff` | Lemma | фиксированное поле всей V4 = Q |
| `base_fixed_by_all` | Theorem | Q фиксируется всеми |
| `correspondence_inclusion_reversing` | Theorem | ★ подгруппа↔подполе, обращая включение |
| `r2/r3` | Definition | √2, √3 как элементы |
| `sig_neq_id / tau_neq_id` | Theorem | σ,τ нетривиальны (двигают √2,√3) |

**Key lemmas (deep):**

- **`correspondence_inclusion_reversing`** - Сердце флагмана: явная биекция { подгруппы V4 } ↔ { промежуточные поля }, обращающая включение — настоящее Фундаментальное соответствие Галуа для конкретного degree-4 расширения, а не совпадение счётчиков (как в GaloisCorrespondence). Редко встречается полностью формализованным (библиотеки используют абстрактную теорию). _(FTGT, bijection, vein-D, inclusion-reversing)_
- **`V4_abelian`** - Группа автоморфизмов ЕСТЬ Клейнова четверная V4: σ,τ инволютивны и коммутируют, σ∘τ=στ. Не постулат, а вычисленная структура реального действия на 4-кортежах — основа всего соответствия. _(V4, klein-four, automorphism-group)_
- **`sig_mul`** - Каждый автоморфизм — настоящий КОЛЬЦЕВОЙ гомоморфизм (σ(uv)=σu·σv), не просто перестановка координат. Именно это делает соответствие реальным (а не численным): σ,τ уважают полевую структуру. _(ring-homomorphism, automorphism)_

**Uniqueness - score 5 (synthesis+observation).** Полностью явное конкретное соответствие Галуа Q[√2,√3]≅V4: реальное действие автоморфизмов (кольцевые гомоморфизмы σ,τ,στ), биекция фикс-подполе↔подгруппа выписана и обращает включение, |Gal|=[E:Q]=4. Редкость в полностью формализованном виде.
> _Caveat:_ FTGT классична; уникальность — в НЕОБЫЧНОЙ ПОЛНОТЕ явной формализации одного нетривиального инстанса (vs абстрактная теория в библиотеках), не в новой теореме. Абстрактный Aut(L/K) остаётся role-limit.

---

## #25 - `src/algebra/IndependenceQ23.v` - score 4 (synthesis+observation)

**sqrt3 not in Q[sqrt2]: the degree-4 tower is GENUINE**

- **Topic.** Proves sqrt3 not in Q[sqrt2] purely algebraically over Q: if sqrt3 = a + b*sqrt2 then squaring forces 2ab=0 and a^2+2b^2=3, impossible — using only irrationality of sqrt3 and sqrt6. Makes the tower Q < Q[sqrt2] < Q[sqrt2,sqrt3] non-degenerate.
- **Role.** Vein D flagship: the load-bearing independence behind [E:Q]=4. Imports GaloisQ23, Sqrt3Irrational, GeneralSqrt.
- **Counts.** Qed 3 / Admitted 0 / axioms 0
- **Imports.** ToS: algebra.GaloisQ23, analysis.Sqrt3Irrational, stdlib.GeneralSqrt; Stdlib: QArith Lqa
- **E/R/R.** _Elements:_ кандидаты-представления a+b√2 для √3 внутри Q[√2]. _Roles:_ Q[√2] как собственное подрасширение; √3 как подлинно новый генератор. _Rules:_ a+b√2 в квадрате = 3 ⟹ 2ab=0 ∧ a²+2b²=3, невозможно над Q. _P4:_ genuine степень-2 ступени делают башню невырожденной (Element-данные); верность реальному полю — фронтир.
- **Classical counterpart.** That sqrt3 is not in Q[sqrt2] (linear disjointness of Q[sqrt2] and Q[sqrt3]) is standard; NEW is supplying it as the explicit axiom-free LOAD-BEARING step behind the concrete GaloisQ23 degree-4, purely over Q (no real embedding).
- **Tags.** independence, vein-D, load-bearing, surds, tower

**Lemmas (3):**

| name | kind | role |
|---|---|---|
| `no_sq_6` | Lemma | 6 не рациональный квадрат (Q-литеральная форма) |
| `sqrt3_not_in_Qsqrt2` | Theorem | ★ √3 ∉ Q[√2] (подлинная независимость) |
| `tower_nondegenerate` | Corollary | башня Q⊊Q[√2]⊊E невырождена |

**Key lemmas (deep):**

- **`sqrt3_not_in_Qsqrt2`** - Несущая независимость: √3∉Q[√2], чисто алгебраически над Q (без вещественного вложения) — если √3=a+b√2, то 2ab·√2=3−a²−2b²∈Q ⟹ ab=0; b=0⟹a²=3 (√3 ирр.), a=0⟹(2b)²=6 (√6 ирр.). Именно это делает degree-4 НАСТОЯЩИМ, а не размерностью формального модуля. project-uniqueness-map выделяет эту лемму отдельно. _(independence, vein-D, load-bearing)_
- **`tower_nondegenerate`** - Следствие: каждая ступень башни Q⊊Q[√2]⊊E — genuine degree-2 расширение. Закрывает gap верности за degree-4 совпадением GaloisDegreeQ23. _(tower, non-degenerate)_

**Uniqueness - score 4 (synthesis+observation).** Несущая независимость √3∉Q[√2] чисто над Q (без вещественного вложения), делающая [E:Q]=4 ПОДЛИННЫМ, а не формальной размерностью модуля — load-bearing шаг за флагманом.
> _Caveat:_ Линейная дизъюнктность Q[√2],Q[√3] стандартна; ценность — её поставка как явного аксиомо-свободного шага верности за конкретным GaloisQ23.

---

## #26 - `src/algebra/RationalRootTest.v` - score 3 (synthesis+observation)

**General Gauss lemma and the rational root test (any degree)**

- **Topic.** Gauss's lemma generalized to every degree: coprime x and x | y^n => x = +-1 (via Euclid/rel_prime); hence the n-th root of an integer is an integer or irrational. Subsumes sqrt2/sqrt3/sqrt5 (n=2) and cbrt2 (n=3).
- **Role.** Generalizes the cube-specific coprime_div_cube_unit (AngleTrisection, q-kinematics) to all degrees. Self-contained (ZArith/Znumtheory).
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: ZArith Znumtheory Lia
- **E/R/R.** _Elements:_ целые числа, взаимная простота (rel_prime), делимость. _Roles:_ лемма Гаусса как правило «coprime делит степень ⟹ единица». _Rules:_ rel_prime x y, x \| y^n ⟹ x=±1 (любая степень n). _P4:_ разрешимый целочисленный критерий «корень целый или иррационален» = Element/role-limit-ручка для чистых корней.
- **Classical counterpart.** Gauss's lemma and the rational root theorem (pure-power case) are classical; NEW is generalizing the repo's cube-specific coprime_div_cube_unit to EVERY degree via Znumtheory, unifying sqrt2, sqrt3, sqrt5, cbrt2 under one criterion. Caveat: pure-root/power criterion only; full RRT for arbitrary integer polynomials not yet assembled.
- **Tags.** gauss-lemma, rational-root-test, irrationality, number-theory, synthesis

**Lemmas (7):**

| name | kind | role |
|---|---|---|
| `zpow` | Fixpoint | степень над Z (zpow y (S k) = y·zpow y k) |
| `rel_prime_x_1` | Lemma | x взаимно просто с 1 |
| `rel_prime_zpow` | Lemma | взаимная простота сохраняется при степени |
| `coprime_div_pow_unit` | Theorem | ★ Гаусс: coprime x, x\|y^n ⟹ x=±1 (любая степень) |
| `nth_root_integer_or_irrational` | Theorem | ★ n-й корень целого = целый или иррационален |
| `gauss_square` | Corollary | случай n=2 (квадратный корень) |
| `gauss_cube` | Corollary | случай n=3 (кубический корень) |

**Key lemmas (deep):**

- **`coprime_div_pow_unit`** - Лемма Гаусса в общей степени: если x взаимно просто с y и x делит y^n, то x=±1 (через Евклида/rel_prime). Обобщает кубо-специфичный coprime_div_cube_unit на ЛЮБУЮ степень — один критерий вместо россыпи по n. _(gauss-lemma, general-degree, coprime)_
- **`nth_root_integer_or_irrational`** - Тест рационального корня (чистый случай): n-й корень целого либо целый, либо иррационален (q=1 в несократимой записи). Подводит √2,√3,√5 (n=2) и ∛2 (n=3) под ОДИН критерий — связь с Greek-impossibilities нитью q-kinematics. _(rational-root-test, irrationality, unification)_

**Uniqueness - score 3 (synthesis+observation).** Лемма Гаусса и тест рационального корня обобщены на ВСЕ степени, унифицируя √2/√3/√5/∛2 под одним критерием (n-й корень целого = целый или иррационален).
> _Caveat:_ Лемма Гаусса и RRT классичны; вклад — обобщение репозиторного кубо-специфичного результата на любую степень. Только чистый степенной случай; полный RRT для произвольных полиномов не собран.

---

## #27 - `src/algebra/SolvableGroup.v` - score 4 (synthesis+observation)

**The Abel-Ruffini engine: perfect => not solvable (0 axioms, abstract)**

- **Topic.** The group-theoretic half of Abel-Ruffini over an abstract GroupStr with Leibniz equality: derived series, Solvable = series reaches {e}, Perfect = own derived subgroup; the engine 'perfect non-trivial => not solvable', applied to the quintic given Perfect Quintic as a premise.
- **Role.** Abstract Abel-Ruffini engine, 0 axioms. Companion to GaloisCorrespondence (which gives the count-level quintic). Self-contained (Bool).
- **Counts.** Qed 18 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Bool
- **E/R/R.** _Elements:_ абстрактная группа, её подгруппы, коммутаторы. _Roles:_ разрешимость как role-limit «производный ряд достигает {e}»; perfect = сам себе коммутант. _Rules:_ производная подгруппа = минимальная, содержащая все коммутаторы; perfect нетривиальная никогда не достигает {e}. _P4:_ solvable = процесс, ТЕРМИНИРУЮЩИЙ в {e} (Element-сторона); perfect = процесс, который НИКОГДА не закрывается (role-limit); A5-простота локализована в посылке.
- **Classical counterpart.** Abel-Ruffini and the solvable-series theory are classical; NEW is the 0-axiom ABSTRACT formalization of the perfect=>not-solvable engine over an abstract GroupStr (no classic, no funext), honestly localizing the heavy A5-simplicity to an explicit premise rather than a global axiom.
- **Tags.** abel-ruffini, solvable-group, perfect, derived-series, 0-axiom, P4

**Lemmas (22):**

| name | kind | role |
|---|---|---|
| `GroupStr` | Record | абстрактная группа (Leibniz-равенство) |
| `inv_id/inv_unique/inv_op` | Lemma | свойства обратного |
| `comm` | Definition | коммутатор aba⁻¹b⁻¹ |
| `comm_eq_id` | Lemma | коммутирующие ⟹ коммутатор = e |
| `SubGrp` | Record | подгруппа |
| `fullS/trivialS` | Definition | вся группа / {e} |
| `IsDerived` | Definition | D = производная подгруппа H |
| `AbelianS` | Definition | подгруппа абелева |
| `abelian_IsDerived_trivial` | Lemma | абелева ⟹ производная = {e} |
| `SolvableFrom` | Inductive | разрешимость от подгруппы (ряд до {e}) |
| `Solvable` | Definition | SolvableFrom fullS |
| `trivialS_solvable/abelian_solvable` | Lemma | {e} и абелевы разрешимы |
| `derived_unique` | Lemma | производная подгруппа единственна (до mem_equiv) |
| `IsDerived_transport_l/r / SolvableFrom_transport` | Lemma | перенос по эквивалентности подгрупп |
| `perfect_solvable_trivial` | Lemma | perfect + solvable ⟹ тривиальна |
| `perfect_nontrivial_not_solvable` | Theorem | ★ perfect нетривиальная НЕ разрешима (движок) |
| `Perfect/NonAbelianFull` | Definition | perfect; неабелева полная |
| `nonabelian_has_nontrivial` | Lemma | неабелева ⟹ есть нетривиальный элемент |
| `perfect_nonabelian_not_solvable` | Theorem | ★ perfect+неабелева ⟹ не разрешима |
| `quintic_galois_group_not_solvable` | Theorem | ★ группа квинтики не разрешима (дано Perfect Quintic) |
| `boolGroup` | Definition | конкретная Z/2 |
| `boolGroup_abelian/solvable` | Lemma | Z/2 абелева ⟹ разрешима |

**Key lemmas (deep):**

- **`perfect_nontrivial_not_solvable`** - Движок Абеля-Руффини: perfect-группа ([G,G]=G) с неединичным элементом НЕ разрешима — её производный ряд застывает на G, не достигая {e}. Доказано абстрактно над GroupStr с 0 аксиомами (без classic/funext). Чисто P4: solvable ⟺ процесс терминирует в {e}. _(abel-ruffini, perfect, not-solvable, engine)_
- **`quintic_galois_group_not_solvable`** - Применение к квинтике: её группа Галуа неразрешима, ПОТОМУ ЧТО содержит perfect A5 — и это подаётся как явная ПОСЫЛКА Perfect Quintic, а не глобальная аксиома (файл остаётся 0-ax). Честная локализация тяжёлой 60-элементной простоты A5. _(quintic, abel-ruffini, honest-premise)_

**Uniqueness - score 4 (synthesis+observation).** Групповая половина Абеля-Руффини абстрактно с 0 аксиомами (без classic/funext) над GroupStr: производный ряд, perfect⇒не-solvable, применено к квинтике; разрешимость как терминирующий процесс (P4).
> _Caveat:_ Абель-Руффини и теория разрешимых рядов классичны; вклад — 0-аксиомное абстрактное исполнение + честная локализация простоты A5 в явную посылку (не аксиому). A5-простота в-движке + радикалы⟺solvable остаются role-limit.

---

## #28 - `src/algebra/SplittingFieldQ23.v` - score 3 (synthesis+observation)

**The concrete splitting field of (x^2-2)(x^2-3): roots, generation, basis dimension 4**

- **Topic.** All roots +-sqrt2, +-sqrt3, sqrt6 as elements of E; sqrt2*sqrt3=sqrt6 closure; root sums/products; the generation theorem (every element = combo of basis {1,sqrt2,sqrt3,sqrt6}); basis dimension 4.
- **Role.** Concrete splitting field, companion to GaloisQ23. Self-contained.
- **Counts.** Qed 11 / Admitted 0 / axioms 0
- **Imports.** Stdlib: QArith (E from GaloisQ23-style 4-tuples)
- **E/R/R.** _Elements:_ корни ±√2,±√3,√6 в E; комбинации combo a b c d. _Roles:_ E как поле разложения; базис {1,√2,√3,√6}. _Rules:_ корневые уравнения, √2·√3=√6, generation; basis_dimension=4. _P4:_ конкретное конечное поле разложения, полностью актуально (Element).
- **Classical counterpart.** Splitting fields are standard; NEW is the explicit construction for (x^2-2)(x^2-3) over Q with all roots +-sqrt2, +-sqrt3, sqrt6 named, the generation theorem, and basis dimension 4 — the concrete companion to GaloisQ23.
- **Tags.** splitting-field, galois, vein-D, basis, concrete

**Lemmas (11):**

| name | kind | role |
|---|---|---|
| `pos2/neg2/pos3/neg3/sqrt6` | Definition | корни ±√2,±√3 и √6 как элементы |
| `pos2_root/neg2_root/pos3_root/neg3_root` | Lemma | корни x²−2, x²−3 |
| `sqrt2_mul_sqrt3` | Lemma | ★ √2·√3=√6 (замкнутость) |
| `sqrt6_squared` | Lemma | √6²=6 |
| `roots2_distinct` | Lemma | √2≠−√2 |
| `roots2_sum_zero` | Lemma | √2+(−√2)=0 |
| `roots2_product` | Lemma | √2·(−√2)=−2 |
| `combo` | Definition | линейная комбинация базиса |
| `generation` | Theorem | ★ каждый элемент = combo базиса {1,√2,√3,√6} |
| `basis_dimension` | Definition | =4 |
| `degree_equals_galois_order` | Theorem | basis_dimension = 4 |

**Key lemmas (deep):**

- **`generation`** - Поле разложения порождается корнями: всякий элемент E = combo базиса {1,√2,√3,√6}. Это конкретное свидетельство, что E — поле разложения (x²−2)(x²−3), на котором стоит размерность 4 и всё соответствие GaloisQ23. _(splitting-field, generation, basis)_
- **`sqrt2_mul_sqrt3`** - Замкнутость: √2·√3=√6 — почему четвёртый базисный элемент √6 необходим и достаточен (произведение генераторов остаётся в поле). Делает {1,√2,√3,√6} настоящим базисом, а не списком. _(closure, sqrt6, basis)_

**Uniqueness - score 3 (synthesis+observation).** Конкретное поле разложения (x²−2)(x²−3): все корни ±√2,±√3,√6 названы, теорема порождения, размерность базиса 4 — конкретный спутник GaloisQ23.
> _Caveat:_ Поля разложения стандартны; вклад — явная конкретная конструкция для данного бикватичного расширения, опора под флагман.

---

## #1870 - `src/algebra/QuinticUnsolvable.v` - score 4 (synthesis+observation)

**Abel-Ruffini for x^5-6x+3: transposition + 5-cycle GENERATE S_5 (120 perms), computed; engine reused**

- **Topic.** Computes (vm_compute) that the right-multiplication closure of {(0 1),(0 1 2 3 4)} is exactly the 120 distinct permutations of {0..4} = S_5, shows it non-abelian, verifies the polynomial's arithmetic (no rational root, sign changes => >=3 real roots), and assembles Abel-Ruffini for x^5-6x+3 feeding the existing solvability engine.
- **Role.** Singleton experiment supplying the COMPUTED group structure missing from algebra/SolvableGroup.v (which proved 'perfect non-abelian => not solvable' abstractly). Imports algebra.SolvableGroup; assembles its quintic_galois_group_not_solvable with the concrete S_5 and polynomial data.
- **Counts.** Qed 6 / Admitted 0 / axioms 0
- **Imports.** Stdlib: List PeanoNat Bool Arith Lia ZArith; algebra.SolvableGroup
- **E/R/R.** _Elements:_ перестановки {0..4} (списки длины 5); многочлен x^5-6x+3; генераторы t (транспозиция (0 1)), c (5-цикл (0 1 2 3 4)) — конечные объекты, P4. _Roles:_ разрешимость в радикалах = role-limit (производный ряд -> {e}); группа Галуа = роль симметрий корней; комплексное сопряжение = транспозиция-роль. _Rules:_ BFS-замыкание под умножением на генераторы (разрешимо: ровно 120 перестановок = S_5); Abel-Ruffini: perfect non-abelian => не разрешима (движок); рацион. корень монического => целый делитель 3. _P4:_ порождение S_5 транспозицией+5-циклом = Element (замкнутое vm_compute-вычисление 120 различных перестановок, 0 аксиом) — НОВОЕ ядро; неразрешимость квинтика = role-limit на классических мостах (Gal=S_5; A_5 простая; критерий Галуа), честно цитируемых, не подделанных.
- **Classical counterpart.** Abel-Ruffini (the general quintic is not solvable by radicals) and the specific example x^5-6x+3 are classical (Eisenstein irreducibility, exactly 2 non-real roots => Galois group S_5, A_5 simple => S_5 not solvable, Galois solvability criterion). NEW here is the MACHINE-CHECKED group-theoretic heart: a transposition + a 5-cycle generate S_5 (120 perms) by closed BFS computation, the piece SolvableGroup.v took as an abstract premise.
- **Tags.** algebra, galois, abel-ruffini, S5, quintic, computation, synthesis, role-limit
- **Notes.** STATUS header says 7 Qed; actual Qed. count = 6 (drift). 0 Admitted, 0 own Axiom/Parameter (the unsolvability engine enters as a forall-hypothesis in the capstone, discharged by imported quintic_galois_group_not_solvable).

**Lemmas (25):**

| name | kind | role |
|---|---|---|
| `perm` | Definition | перестановка = список образов длины 5 |
| `dom` | Definition | носитель {0;1;2;3;4} |
| `app` | Definition | применение перестановки nth i p 0 |
| `comp` | Definition | композиция (p∘q)(i)=p(q i) через map по dom |
| `idp` | Definition | тождественная перестановка |
| `t` | Definition | транспозиция (0 1) = [1;0;2;3;4] |
| `c` | Definition | 5-цикл (0 1 2 3 4) = [1;2;3;4;0] |
| `gens` | Definition | генераторы {t; c} |
| `leqb` | Fixpoint | булево равенство перестановок |
| `inb` | Definition | членство перестановки в списке |
| `addnew` | Definition | добавить перестановку, если новая |
| `next` | Definition | один раунд BFS: правое умножение всех на генераторы |
| `gen_closure` | Definition | подгруппа <t,c> = 50 раундов BFS от [idp] |
| `is_perm5` | Definition | проверка: длина 5 и каждая точка ровно раз |
| `gen_report` | Definition | ★ булев отчёт: \|closure\|=120, все perm5, замкнуто, содержит id, 120 различных |
| `gen_report_true` | Lemma | ★★ gen_report = true (vm_compute) — <t,c> = S_5 |
| `s5_size` | Lemma | ★ \|gen_closure\| = 120 (= \|S_5\|) |
| `s5_nonabelian` | Lemma | ★ t·c != c·t (S_5 неабелева, вход NonAbelianFull) |
| `qf` | Definition | многочлен x^5-6x+3 над Z |
| `root_candidates` | Definition | кандидаты-корни +-1,+-3 (делители 3) |
| `no_rational_root` | Definition | ни один кандидат не корень (булево) |
| `no_rational_root_true` | Lemma | ★ нет рационального корня (rational-root theorem, монический) |
| `sign_changes` | Definition | знаки f на -2,-1,1,2 чередуются (булево) |
| `sign_changes_true` | Lemma | ★ смена знака => >=3 вещественных корня (IVT) |
| `quintic_x5m6x3_unsolvable_assembly` | Theorem | ★★ КАПСТОУН: (A) S_5 порождена + (B) арифметика + (C) движок => неразрешимость собрана |

**Key lemmas (deep):**

- **`gen_report_true`** - ★ Подлинно новый машинный результат файла: BFS-замыкание {транспозиция, 5-цикл} под правым умножением вычисляется (vm_compute) и проверяется как РОВНО 120 различных подлинных перестановок {0..4}, замкнутых под генераторами, с тождеством — то есть <t,c> = S_5. Это группо-теоретическое СЕРДЦЕ Abel-Ruffini, которое algebra/SolvableGroup.v брал абстрактной посылкой; здесь оно ПОСЧИТАНО, 0 аксиом, замкнутое конечное вычисление (Element-сторона). Классически 'транспозиция+p-цикл порождают S_p' известно; новизна — машинная проверка на конкретном S_5 в составе сборки. _(S5, generation, computation, abel-ruffini, element)_
- **`quintic_x5m6x3_unsolvable_assembly`** - Капстоун-сборка: (A) НОВОЕ — S_5 порождена транспозицией+5-циклом (gen_report); (B) НОВОЕ — арифметика многочлена (нет рацион. корня + >=3 вещественных корня по IVT); (C) переиспользованный движок quintic_galois_group_not_solvable (perfect non-abelian => не разрешима). Вместе с ЧЕСТНО цитируемыми классическими мостами (Gal=S_5 из (A)+(B); A_5 проста => перфектная секция; критерий радикальной башни) — x^5-6x+3 не разрешим в радикалах. Мосты — role-limit, та же completed-object стена, что SolvableGroup называет для простоты A_5; файл их НЕ подделывает. _(capstone, assembly, role-limit, honest-bridges)_

**Uniqueness - score 4 (synthesis+observation).** Машинно-проверенное порождение S_5 транспозицией+5-циклом (120 различных перестановок, замкнуто, vm_compute, 0 аксиом) — недостающее группо-теоретическое ядро движка Abel-Ruffini — плюс арифметика конкретного x^5-6x+3 и сборка неразрешимости с честно цитируемыми галуа-мостами.
> _Caveat:_ Сам Abel-Ruffini, пример x^5-6x+3 и факт 'транспозиция+p-цикл порождают S_p' классичны; галуа-мосты (Gal=S_5, A_5 проста, критерий радикалов) НЕ формализованы, а цитируются как role-limit. Ново — машинная проверка порождения S_5 и 0-аксиомная сборка, не сами теоремы. DRIFT: заголовок STATUS заявляет 7 Qed, фактически 6. Движковая посылка (C) — forall-гипотеза, НЕ axiom.

