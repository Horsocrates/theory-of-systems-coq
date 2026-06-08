# Database - cluster `numbertheory`

_Generated from `numbertheory.json` by `generate.ps1` - do not edit by hand; edit the JSON._

**9 files / 138 Qed.** Score distribution: s5=0 / s4=0 / s3=0 / s2=6 / s1=3 / s0=0

---

## #647 - `src/numbertheory/ArithmeticFunctions.v` - score 1 (exposition)

**Arithmetic functions tau, sigma, phi over nat (computational)**

- **Topic.** divisors as a list, tau/sigma/phi defined from it, the divisors spec, concrete values (tau 12=6, sigma 12=28, phi 12=4) and multiplicativity examples on coprime arguments.
- **Role.** Number-theory foundation (divisor functions). Self-contained (nat). Feeds MobiusDirichlet, book Part XIII.
- **Counts.** Qed 23 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith List
- **E/R/R.** _Elements:_ натуральные n; список делителей divisors n. _Roles:_ tau/sigma/phi как роли-меры числа (счёт/сумма делителей, тотиент). _Rules:_ divisors через перебор; tau=length, sigma=sum, phi=счёт взаимно простых. _P4:_ арифметические функции вычислимы конечным перебором (Element, vm_compute); мультипликативность проверена на конкретных coprime парах.
- **Classical counterpart.** The arithmetic functions tau (divisor count), sigma (divisor sum), phi (Euler totient) and their multiplicativity are classical; NEW: nothing — a clean computational nat formalization with vm_compute examples, 0 axioms.
- **Tags.** arithmetic-functions, totient, divisors, computational, exposition

**Lemmas (8):**

| name | kind | role |
|---|---|---|
| `prime_coprime_below` | Lemma | простое взаимно просто с меньшими |
| `divisors/tau/sigma/phi` | Definition | делители и три функции |
| `divisors_spec` | Lemma | характеризация списка делителей |
| `divisors_12/tau_12/sigma_12/phi_12` | Example | конкретные значения для 12 |
| `tau_1/sigma_1/phi_1/tau_7/sigma_7/phi_7/phi_8` | Example | значения для 1,7,8 (vm_compute) |
| `tau_mult_12/sigma_mult_12/phi_mult_12/phi_mult_15/tau_mult_15` | Example | мультипликативность на coprime парах |
| `coprime_below_5/coprime_below_5_general` | Example | взаимная простота |
| `one_in_divisors/self_in_divisors/tau_ge_1` | Lemma | 1 и n — делители; tau≥1 |

**Key lemmas (deep):**

- **`divisors_spec`** - Характеризация списка делителей (d в divisors n ⟺ d\|n в диапазоне) — основа корректности tau/sigma/phi. Element-сторона: делители = конечный вычислимый список (P4), функции считаются перебором. _(divisors, computational)_
- **`phi_mult_15`** - phi(15)=phi(3)·phi(5) — мультипликативность тотиента на coprime аргументах, проверена конкретно (полная мультипликативность доказана в ChineseRemainder.phi_mult). Демонстрирует ключевое свойство как вычисление. _(multiplicative, totient)_

**Uniqueness - score 1 (exposition).** Арифметические функции tau/sigma/phi над nat вычислительно (списком делителей) + конкретные значения и мультипликативность на примерах.
> _Caveat:_ Полностью стандартная теория чисел; ценность — чистая 0-аксиомная вычислимая формализация (питает Möbius/книгу), не новый результат.

---

## #648 - `src/numbertheory/ChineseRemainder.v` - score 2 (methods)

**Chinese Remainder Theorem + multiplicativity of phi**

- **Topic.** Modular inverse existence for coprime moduli, CRT existence and uniqueness mod m*n, the CRT pairing bijection, and phi(m*n)=phi(m)*phi(n) for coprime m,n; concrete examples.
- **Role.** Number theory (CRT). Self-contained (nat). Supplies phi multiplicativity to ArithmeticFunctions.
- **Counts.** Qed 17 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith List Permutation
- **E/R/R.** _Elements:_ вычеты по m, n, m·n; пары вычетов. _Roles:_ CRT-биекция между Z/mn и Z/m × Z/n; обратимость как роль. _Rules:_ coprime ⟹ существует обратный; CRT существование+единственность; phi мультипликативна. _P4:_ CRT конструктивен (Element, вычислимый обратный); мультипликативность phi — счёт биекции.
- **Classical counterpart.** The Chinese Remainder Theorem (existence + uniqueness) and multiplicativity of Euler's totient are classical; NEW: nothing — a constructive nat formalization (modular inverse, CRT bijection => phi multiplicative), 0 axioms.
- **Tags.** CRT, totient, modular-inverse, constructive, methods

**Lemmas (10):**

| name | kind | role |
|---|---|---|
| `mod_inverse_exists` | Lemma | обратный по модулю для coprime |
| `crt_exists` | Theorem | ★ CRT: решение системы вычетов существует |
| `coprime_divides_mul` | Lemma | coprime делимость произведения |
| `crt_unique` | Theorem | ★ CRT: решение единственно mod m·n |
| `crt_3_5/crt_3_5_exists/crt_unique_11_26/inverse_2_mod_15` | Example | конкретные CRT-примеры |
| `NoDup_map_inj/NoDup_list_prod` | Lemma | вспомогательные о NoDup/произведении списков |
| `coprime_of_mul_l/r/mod_mod_mul_l/r` | Lemma | coprime и mod через произведение |
| `crt_pair` | Definition | пара (k mod m, k mod n) |
| `phi_mult` | Theorem | ★ phi(m·n)=phi(m)·phi(n) (coprime) |
| `phi_mult_3_5/phi_mult_8_9` | Example | конкретная мультипликативность |

**Key lemmas (deep):**

- **`crt_exists`** - CRT существование, конструктивно: для coprime m,n система вычетов имеет решение — через явный модульный обратный. Element-сторона: решение ВЫЧИСЛЯЕТСЯ, не постулируется. _(CRT, constructive)_
- **`phi_mult`** - phi(m·n)=phi(m)·phi(n) для coprime — выведено из CRT-биекции (crt_pair взаимно однозначна на единицах). Мультипликативность тотиента как СЛЕДСТВИЕ структурной биекции, не отдельный факт. _(totient, multiplicative, bijection)_

**Uniqueness - score 2 (methods).** CRT (существование+единственность) конструктивно над nat + мультипликативность phi как следствие CRT-биекции.
> _Caveat:_ CRT и мультипликативность phi классичны; вклад — чистая конструктивная 0-аксиомная формализация, не новый результат.

---

## #649 - `src/numbertheory/EuclidInfinitude.v` - score 1 (exposition)

**Euclid's infinitude of primes**

- **Topic.** A prime divides n! for primes up to n; hence there is a prime above any N (via factorial+1), and no finite list contains all primes; example: a prime above 100.
- **Role.** Number theory (Euclid). Self-contained (nat, uses is_prime/divides/fact).
- **Counts.** Qed 5 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith List; stdlib primes (is_prime, fact)
- **E/R/R.** _Elements:_ простые числа; факториал fact n; конечные списки простых. _Roles:_ бесконечность простых как ПРАВИЛО (нет конечного списка-всех). _Rules:_ p\|fact n для p≤n; простое выше N через fact+1; нет конечного списка всех простых. _P4:_ бесконечность простых = role-limit-правило (всегда есть больший), каждый конкретный больший простой актуален (Element).
- **Classical counterpart.** Euclid's theorem (infinitely many primes) is classical (c. 300 BC); NEW: nothing — a clean nat formalization (a prime above N via N!+1, primes not contained in any finite list), 0 axioms.
- **Tags.** euclid, primes, infinitude, no-maximum, exposition

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `divides_fact` | Lemma | p ≤ n ⟹ p \| n! |
| `exists_larger_prime` | Theorem | ★ для любого N есть простое > N |
| `in_le_fold_max` | Lemma | элемент списка ≤ его максимума |
| `primes_not_finite` | Theorem | ★ нет конечного списка всех простых |
| `prime_above_100` | Example | конкретное простое > 100 |

**Key lemmas (deep):**

- **`exists_larger_prime`** - Евклид: для любого N существует простое > N (через простой делитель N!+1). Role-limit-узор «нет максимума» (как no_maximal_cardinality / no_maximal_rung): бесконечность простых — правило восхождения, не завершённое множество. _(euclid, primes, no-maximum)_
- **`primes_not_finite`** - Никакой конечный список не содержит все простые — прямая формулировка бесконечности как отрицания конечной полноты. P4-форма: бесконечность = свойство правила, не объекта. _(infinitude, role-limit)_

**Uniqueness - score 1 (exposition).** Бесконечность простых (Евклид) над nat: простое выше любого N, нет конечного списка всех простых — role-limit-узор «нет максимума».
> _Caveat:_ Теорема Евклида — древнейшая классика; ценность — чистая формализация + связь с узором no-maximum, не новый результат.

---

## #650 - `src/numbertheory/EulerFermat.v` - score 2 (methods)

**Fermat's little theorem via the permuted-residues product**

- **Topic.** The product of residues a*x over x=1..p-1 is a permutation of 1..p-1 (cancellation by coprimality), giving a^(p-1) = 1 mod p; corollary a^p = a; concrete examples (3^6 mod 7, etc.).
- **Role.** Number theory (Fermat, full proof). Self-contained (nat, Permutation).
- **Counts.** Qed 14 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith List Permutation; stdlib primes
- **E/R/R.** _Elements:_ вычеты 1..p-1; произведения a·x mod p. _Roles:_ умножение на a = перестановка вычетов (роль-биекция); Ферма как её следствие. _Rules:_ a·x mod p — перестановка ⟹ произведение инвариантно ⟹ a^(p−1)=1. _P4:_ Ферма доказана конечным перестановочным аргументом (Element, vm_compute примеры).
- **Classical counterpart.** Fermat's little theorem (a^(p-1) = 1 mod p) is classical; NEW: nothing — a full nat proof via the permuted-residues product argument, 0 axioms, plus computational examples.
- **Tags.** fermat, primes, permutation-argument, methods

**Lemmas (8):**

| name | kind | role |
|---|---|---|
| `NoDup_map_local/Nprod/Nprod_perm/Nprod_map_mult/Nprod_map_cong` | Lemma/Definition | произведение списка, инвариантность к перестановке |
| `mod_eq_divides_sub/divides_sub_mod_eq` | Lemma | равенство по модулю ⟺ делимость разности |
| `mod_mul_cancel_l` | Lemma | сокращение на a при coprime |
| `prime_divides_Nprod/not_p_divides_fact` | Lemma | простое не делит произведение единиц |
| `res` | Definition | умножение-вычет (a·x) mod p |
| `fermat_little` | Theorem | ★ a^(p−1) ≡ 1 mod p |
| `fermat_pow_p` | Corollary | a^p ≡ a |
| `fermat_3_7/fermat_2_11/fermat_5_13` | Example | конкретные проверки |

**Key lemmas (deep):**

- **`fermat_little`** - Малая теорема Ферма полным аргументом: умножение на a переставляет вычеты 1..p−1, потому их произведение инвариантно, откуда a^(p−1)≡1. Не вычислительный частный случай (как FiniteFieldFp.fermat5), а ОБЩЕЕ доказательство для произвольного простого p. Element-сторона: конечная перестановка. _(fermat, permutation-argument, general)_
- **`mod_mul_cancel_l`** - Сокращение на a по модулю простого (при ~p\|a) — несущая лемма перестановочного аргумента. Локализует, почему именно простота даёт биекцию вычетов. _(cancellation, prime)_

**Uniqueness - score 2 (methods).** Малая теорема Ферма ОБЩИМ перестановочным аргументом над nat (не частный вычислительный случай) + следствие a^p=a.
> _Caveat:_ Ферма классичен; вклад — полное конструктивное доказательство для произвольного p (контраст с конкретными F5/F7), не новый результат.

---

## #651 - `src/numbertheory/EulerTheorem.v` - score 2 (methods)

**Euler's theorem a^phi(n) = 1 mod n via the units**

- **Topic.** The units mod n (coprime residues) as a list, phi = length of units, units closed under multiplication-cancellation, and Euler's theorem a^phi(n)=1 mod n for coprime a; examples (2^phi(9) mod 9, etc.).
- **Role.** Number theory (Euler, generalizing Fermat). Self-contained (nat).
- **Counts.** Qed 13 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith List Permutation
- **E/R/R.** _Elements:_ единицы mod n (взаимно простые вычеты); их список units n. _Roles:_ группа единиц как роль; умножение на a — перестановка единиц. _Rules:_ phi = \|units\|; умножение на coprime a переставляет единицы ⟹ a^phi=1. _P4:_ Эйлер доказан через конечную группу единиц (Element); обобщает Ферма с простого на любое n.
- **Classical counterpart.** Euler's theorem (a^phi(n) = 1 mod n for coprime a,n) generalizing Fermat is classical; NEW: nothing — a nat proof via the group of units, 0 axioms, with examples.
- **Tags.** euler, units, totient, methods

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `gcd_mod_n/coprime_mult/mod_mul_cancel_coprime` | Lemma | gcd, coprime, сокращение |
| `units` | Definition | список единиц mod n (взаимно простые) |
| `phi_eq_length_units/units_spec/units_lt/units_nodup` | Lemma | phi=\|units\|, характеризация, без дубликатов |
| `gcd_Nprod_units` | Lemma | произведение единиц взаимно просто с n |
| `euler_theorem` | Theorem | ★ a^phi(n) ≡ 1 mod n (coprime a) |
| `euler_2_9/euler_3_10/euler_2_15/phi_7_is_6` | Example | конкретные проверки |

**Key lemmas (deep):**

- **`euler_theorem`** - Теорема Эйлера через группу единиц: умножение на coprime a переставляет единицы mod n, произведение инвариантно ⟹ a^phi(n)≡1. Обобщает Ферма (n простое ⟹ phi=p−1) на ПРОИЗВОЛЬНОЕ n. Element-сторона: конечная группа единиц. _(euler, units, generalizes-fermat)_
- **`phi_eq_length_units`** - phi(n) = длина списка единиц — связывает тотиент с РАЗМЕРОМ группы единиц, ядро доказательства Эйлера (порядок элемента делит порядок группы). _(totient, units)_

**Uniqueness - score 2 (methods).** Теорема Эйлера a^phi(n)=1 через конечную группу единиц над nat, обобщая Ферма на любое n.
> _Caveat:_ Теорема Эйлера классична; вклад — конструктивная формализация через units, не новый результат.

---

## #652 - `src/numbertheory/MobiusDirichlet.v` - score 2 (methods)

**Mobius function and Dirichlet convolution (computational)**

- **Topic.** Dirichlet convolution dconv, its commutativity (via divisor-complement pairing), the Mobius function mu from squarefree factorization, the unit/epsilon/id/phi arithmetic functions, Mobius inversion and Gauss totient sum as examples.
- **Role.** Number theory (Mobius/Dirichlet). Self-contained (nat/Z). Builds on factorization.
- **Counts.** Qed 21 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith ZArith List Permutation
- **E/R/R.** _Elements:_ арифметические функции nat→Z; делители и их дополнения. _Roles:_ свёртка Дирихле как роль-произведение функций; mu как знак по squarefree. _Rules:_ dconv f g n = sum по делителям; коммутативна через парность делителей; mu по факторизации. _P4:_ свёртка и mu вычислимы конечным перебором делителей (Element, vm_compute).
- **Classical counterpart.** The Mobius function, Dirichlet convolution, Mobius inversion and the totient/divisor identities are classical; NEW: nothing — a computational nat/Z formalization (Dirichlet convolution commutative, divisor pairing, mu via squarefree factorization), 0 axioms.
- **Tags.** mobius, dirichlet-convolution, totient, computational, methods

**Lemmas (9):**

| name | kind | role |
|---|---|---|
| `Zsum_perm/NoDup_map_local` | Lemma | сумма инвариантна к перестановке |
| `div_div_cancel/divisor_complement/divisors_pairing` | Lemma | ★ парность делителей d ↔ n/d |
| `dconv` | Definition | свёртка Дирихле |
| `dconv_comm` | Theorem | ★ свёртка коммутативна (через парность) |
| `factorize_aux/factorize/no_dup_bool/mu` | Fixpoint/Definition | факторизация и функция Мёбиуса |
| `arith_one/eps/id/phi_Z` | Definition | функции 1, eps, id, phi как nat→Z |
| `factorize_12/30/mu_1/2/6/30/4/12` | Example | конкретные факторизации и значения mu |
| `mobius_sum_identity/gauss_totient_sum/mobius_inversion_phi` | Example | ★ тождества Мёбиуса и Гаусса |
| `mobius_id_comm/gauss_comm/dconv_one_r/dconv_mu_one_12` | Theorem/Lemma/Example | коммутативность сверток, свертка с 1 |

**Key lemmas (deep):**

- **`dconv_comm`** - Свёртка Дирихле коммутативна — доказано через парность делителей (d ↔ n/d, divisors_pairing). Ядро мультипликативной теории: коммутативность свёртки = структурное свойство решётки делителей, не вычисление по случаям. _(dirichlet-convolution, commutative, divisor-pairing)_
- **`mobius_inversion_phi`** - Обращение Мёбиуса на примере тотиента (phi через mu*id) — связывает mu, свёртку и phi в одно тождество. Element-сторона: проверено vm_compute, но опирается на структурную коммутативность свёртки. _(mobius-inversion, totient)_

**Uniqueness - score 2 (methods).** Функция Мёбиуса и свёртка Дирихле вычислительно над nat/Z: коммутативность свёртки через парность делителей, обращение Мёбиуса, тождество Гаусса.
> _Caveat:_ Мёбиус, свёртка Дирихле и обращение классичны; вклад — чистая вычислимая формализация, не новый результат.

---

## #653 - `src/numbertheory/PrimeCounting.v` - score 1 (exposition)

**Prime-counting pi(x) via the sieve (computational)**

- **Topic.** pi(x) = length of the sieve up to x, concrete computed values (pi 10=4, pi 100=25, pi 1000=168), the sieve membership spec, monotonicity, and pi(x)>=1 for x>=2.
- **Role.** Number theory (prime counting, computational). Self-contained (nat, uses sieve).
- **Counts.** Qed 9 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith List; stdlib sieve
- **E/R/R.** _Elements:_ решето sieve x; простые ≤ x. _Roles:_ pi(x) как роль-счётчик простых до x. _Rules:_ pi = длина решета; монотонность по x. _P4:_ pi(x) вычислима решетом для конкретных x (Element, vm_compute: pi 1000=168); асимптотика (ТРПЧ) — role-limit, не здесь.
- **Classical counterpart.** The prime-counting function pi(x) and concrete values (pi(1000)=168) are classical; NEW: nothing — a computational sieve-based pi with verified values and monotonicity, 0 axioms.
- **Tags.** prime-counting, sieve, computational, exposition

**Lemmas (6):**

| name | kind | role |
|---|---|---|
| `pi` | Definition | число простых ≤ x = длина решета |
| `pi_10/pi_30/pi_100/pi_1000` | Example | ★ конкретные значения (pi 1000=168) |
| `in_sieve_iff` | Lemma | характеризация членства в решете |
| `pi_monotone` | Lemma | pi монотонна по x |
| `two_in_sieve/pi_ge_1` | Lemma | 2 в решете; pi≥1 при x≥2 |
| `pi_grows` | Example | pi 10 < pi 1000 |

**Key lemmas (deep):**

- **`pi_1000`** - pi(1000)=168 — вычислено решетом и машинно-проверено (vm_compute). Element-сторона теории распределения простых: конкретные значения АКТУАЛЬНЫ (P4), тогда как асимптотический закон ТРПЧ (pi(x)~x/ln x) остаётся role-limit (требует анализа/вещественных). _(prime-counting, computational, concrete)_
- **`pi_monotone`** - pi монотонна по x — базовое структурное свойство (больше диапазон ⟹ не меньше простых). Делает счётчик корректной мерой. _(monotone, counting)_

**Uniqueness - score 1 (exposition).** Функция pi(x) решетом вычислительно: проверенные значения (pi 1000=168), монотонность — Element-сторона распределения простых.
> _Caveat:_ pi(x) и её значения классичны; ценность — машинно-проверенная вычислимость, асимптотика (ТРПЧ) не затронута. Не новый результат.

---

## #654 - `src/numbertheory/PrimeFactorization.v` - score 2 (methods)

**Fundamental theorem of arithmetic: prime factorization exists and is unique**

- **Topic.** prod_list, Euclid's lemma (p|ab => p|a or p|b), existence of a prime factor and of a full factorization, and uniqueness of the prime factorization up to permutation; the FTA and a concrete example.
- **Role.** Number theory (FTA, full proof). Self-contained (nat). Foundational for the cluster.
- **Counts.** Qed 21 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith List Permutation
- **E/R/R.** _Elements:_ натуральные n; списки простых множителей. _Roles:_ разложение на простые как роль-представление; единственность = роль-каноничность. _Rules:_ лемма Евклида p\|ab⟹p\|a∨p\|b; существование разложения; единственность до перестановки. _P4:_ разложение существует и единственно (Element, конструктивно); каждое разложение — конечные данные.
- **Classical counterpart.** The Fundamental Theorem of Arithmetic (existence + uniqueness of prime factorization) and Euclid's lemma are classical; NEW: nothing — a full constructive nat proof (factor existence, Euclid's lemma, uniqueness up to permutation), 0 axioms.
- **Tags.** FTA, factorization, euclid-lemma, primes, methods

**Lemmas (10):**

| name | kind | role |
|---|---|---|
| `prod_list/prod_nil/prod_cons/prod_app` | Definition/Lemma | произведение списка |
| `Forall_app_intro/elim/divides_iff_Ndivide` | Lemma | вспомогательные о Forall/делимости |
| `is_prime_bool_true_is_prime/is_prime_2/is_prime_3` | Lemma | простота 2,3 |
| `prime_divisor_1_or_self/prime_coprime_of_not_divides` | Lemma | делители простого; coprime |
| `euclid_lemma` | Lemma | ★ лемма Евклида p\|ab⟹p\|a∨p\|b |
| `factor_exists/exists_prime_divisor` | Lemma | существование (простого) делителя |
| `prime_eq_of_divides/prime_in_of_divides_prod/prod_one_all_primes_nil` | Lemma | простое делит произведение ⟹ в списке |
| `prime_factorization_unique` | Theorem | ★ единственность разложения (до перестановки) |
| `fundamental_theorem_of_arithmetic` | Theorem | ★ ОТА: существование+единственность |
| `factorization_12/factorization_12_unique` | Example | конкретное разложение 12 и его единственность |

**Key lemmas (deep):**

- **`fundamental_theorem_of_arithmetic`** - Основная теорема арифметики полностью: всякое n≥1 раскладывается на простые единственным образом (до перестановки). Конструктивно над nat. Element-сторона: разложение — конечные данные, единственность = каноничность представления. _(FTA, factorization, uniqueness)_
- **`euclid_lemma`** - Лемма Евклида (p\|ab⟹p\|a∨p\|b) — несущая для единственности разложения. Та же роль, что в алгебре (RationalRootTest/Gauss): простота как неделимость-генератор. _(euclid-lemma, prime, load-bearing)_

**Uniqueness - score 2 (methods).** Основная теорема арифметики (существование + единственность разложения) полным конструктивным доказательством над nat, через лемму Евклида.
> _Caveat:_ ОТА — фундаментальная классика; вклад — чистое 0-аксиомное конструктивное доказательство, не новый результат.

---

## #655 - `src/numbertheory/VonMangoldt.v` - score 2 (methods)

**Von Mangoldt Lambda and Chebyshev psi in exponent form (log-free)**

- **Topic.** Prime-power detection, Lambda in exponent form (the prime if n is a prime power), the multiplicative mangoldt_prod = n identity (log-free), psi in exponent form, and verified values.
- **Role.** Number theory (von Mangoldt/Chebyshev, log-free). Self-contained (nat). Bridges toward the zeta/PNT material.
- **Counts.** Qed 15 / Admitted 0 / axioms 0
- **Imports.** Stdlib: Arith List
- **E/R/R.** _Elements:_ натуральные n; степени простых; экспонент-форма Lambda. _Roles:_ Lambda как роль «n=степень простого ⟹ это простое»; psi как сумматорная роль. _Rules:_ is_prime_power_bool; mangoldt_prod = произведение = n (лог-свободно); psi_exp. _P4:_ Lambda/psi в ЭКСПОНЕНТ-форме избегают вещественного log (Element, vm_compute); связь с дзета/ТРПЧ — role-limit.
- **Classical counterpart.** The von Mangoldt function Lambda, the Chebyshev psi function and the identity prod_{d\|n} = n (log form sum_{d\|n} Lambda = log n) are classical; NEW: nothing — an exponent-form nat formalization avoiding logs, with verified values, 0 axioms.
- **Tags.** von-mangoldt, chebyshev-psi, log-free, prime-power, methods

**Lemmas (5):**

| name | kind | role |
|---|---|---|
| `is_pow_aux/is_prime_power_bool` | Fixpoint/Definition | детектор степени простого |
| `Lambda_exp/mangoldt_prod/psi_exp` | Definition | Lambda, мультипликативная форма, psi (экспоненты) |
| `Lambda_1/2/3/4/8/9/6/12` | Example | ★ значения Lambda (степени простых vs составные) |
| `mangoldt_prod_12/8/mangoldt_identity_upto_20` | Example | ★ тождество произведения = n |
| `psi_exp_1/4/10/psi_exp_grows` | Example | значения psi и рост |

**Key lemmas (deep):**

- **`mangoldt_identity_upto_20`** - Тождество фон Мангольдта в ЛОГ-СВОБОДНОЙ мультипликативной форме: произведение по структуре степеней-простых = n, проверено до 20 (vm_compute). Элегантный P4-приём: классическое sum_{d\|n} Lambda(d)=log n переписано как произведение = n, избегая вещественного логарифма (Element). _(von-mangoldt, log-free, identity)_
- **`Lambda_4`** - Lambda(4)=2 (4=2², степень простого ⟹ значение = само простое), Lambda(6)=1 (составное вне степени ⟹ 1). Конкретно показывает экспонент-форму, отличающую степени простых от прочих. _(lambda, prime-power)_

**Uniqueness - score 2 (methods).** Функция фон Мангольдта и psi Чебышёва в ЭКСПОНЕНТ-форме над nat, избегающей вещественного log (мультипликативное тождество = n) — лог-свободный P4-приём.
> _Caveat:_ Lambda, psi и тождество классичны; вклад — лог-свободная вычислимая формулировка (мост к дзета/ТРПЧ), не новый результат.

