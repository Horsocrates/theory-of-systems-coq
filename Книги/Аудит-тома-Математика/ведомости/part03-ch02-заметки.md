# Глава III.2 «Рациональные числа» — заметки к ведомости (13.11.2026)

Ведомость: `part03-ch02.json` — 35 ручных записей + 3 автоматических; `merge --dry` проходит без замечаний,
список «без сверки» пуст. Вердикты ручных записей: ok — 31, mismatch-statement — 4 (с автоматическими: ok — 34).
Вердиктов mismatch-price, missing-name, wrong-number нет: цена на странице названа дважды («без единой аксиомы»,
«без аксиом») и оба раза совпадает с ответом компилятора; все названные имена существуют; чисел `Qed`, файлов и
аксиом страница не приводит.

Четыре записи с расхождением относятся к трём местам (расхождения 1–3): две — о словах «деления на нуль
формальная запись не допускает», одна — о сравнении статуса с целыми, одна — о слове «биекция».

Глава почти целиком философская и о своём формальном статусе говорит прямо: тип рациональных взят из стандартной
библиотеки, «соразмерное чтение несёт проза» (стр. 826–830). Мест вида «выведено в Rocq при том, что это дано» в
главе нет: слова «получаются», «разворачивается», «построена» относятся к изложению, а не к формализации, и глава
это оговаривает сама.

Пробные файлы лежат в `C:/Users/abary/tos-audit-build/_part03/ch02/`: `Check.v` (сведения главы о типе `Q`;
уравнение соразмерности; позиционное чтение; делимость отрезка и медианта; недостающее звено биекции; собственная
запись соразмерной позиции), `CheckPA.v` (цена имён стандартной библиотеки), `status.txt` (вывод
`tom-status.cjs chapter 03/02`), `Check.out` (ответы компилятора). `Check.v` собирается; все 30 команд
`Print Assumptions` в нём отвечают «Closed under the global context». В `src` и в собранной копии ничего не
менялось.

Глава называет один файл формализации — `src/Countability_Q.v` (33 `Qed`). Для проверки слов главы прочитаны ещё
`src/stdlib/RingField.v` (20), `src/stdlib/SternBrocot.v` (13), `src/CoordinateIntegers.v` (13), определения
`Group` в `src/stdlib/GroupTheory.v`, теорема `P4_finite_at_each_stage` в `src/foundation/PrinciplesFromLaws.v`, а
также исходники стандартной библиотеки `Stdlib/QArith/QArith_base.v`, `Qfield.v`, `Qreduction.v`.

## Что проверить не удалось

- Отсылки к другим главам (Глава II.1; Глава III.1, § 1.1, 1.3–1.7; Глава III.3; «Глава 4.3»; Часть I, Часть IV)
  не сверялись; это предмет ведомостей этих глав. Из соседних глав прочитано только нужное для слов этой главы:
  в Главе III.1 — стр. 754–759, 1071–1085, 1121–1128 (статус формализации целых), в Главе III.3 — стр. 538–588
  (как там сказано о биекции).
- Отсутствие в `src` собственного типа рациональных установлено поиском (объявления с именами вида `Rat`,
  `Rational`, `Frac`, `Fraction`; записи с полем числителя; имена файлов), а не чтением всех 2048 файлов.
- Слова о дальнейших частях тома («в части, посвящённой алгебре…», стр. 514–515, 641–642, 655–656; «предмет
  дальнейших частей», стр. 713–714) проверены только поиском по страницам тома (см. «Сомнительные места», п. 3 и 4).
- Комментарий файла `Countability_Q.v` о неперечислимости процессов (стр. 503–505 файла) сверен только с одной
  теоремой `ShrinkingIntervals_ERR.v` — её утверждением и ценой; сама теорема — предмет Части IV.
- Философские тезисы главы (акт различения внутри шага, двойной статус единицы, деление на нуль как
  бессмыслица, разбор E/R/R) не оценивались.
- Английская страница и LaTeX-исходник главы не смотрелись.

Всё остальное проверено по исходнику и компилятору.

## Расхождение 1. «Деления на нуль формальная запись не допускает» (стр. 445–448, 527–528)

**Было:**

> (445–448) Тем условие $q \neq 0$ (§ 2.4) оказывается *встроенным в самый тип*: знаменатель просто не может быть
> нулём, и деления на нуль формальная запись не допускает не запретом, а устройством типа.
>
> (527–528) Ненулевость знаменателя встроена в тип: деления на нуль формальная запись не допускает устройством, а
> не запретом.

**Проверка.** Стандартная библиотека, `Stdlib/QArith/QArith_base.v:254–261` и `:747`:

```coq
Definition Qinv (x : Q) :=
  match Qnum x with
  | Z0 => 0#1
  | Zpos p => (QDen x)#p
  | Zneg p => (Zneg (Qden x))#p
  end.

Definition Qdiv (x y : Q) := Qmult x (Qinv y).

Theorem Qmult_inv_r : forall x, ~ x == 0 -> x*(/x) == 1.
```

В пробном файле (`Check.v`; все — Closed under the global context):

```coq
Lemma denominator_never_zero : forall x : Q, Z.pos (Qden x) <> 0%Z.   (* discriminate *)
Lemma Qinv_of_zero : / 0 = 0.                                          (* reflexivity *)
Lemma Qdiv_by_zero_example : 1 / 0 = 0.                                (* reflexivity *)
Lemma Qdiv_by_zero : forall x : Q, x / 0 == 0.
Lemma inverse_law_fails_at_zero : ~ (0 * / 0 == 1).
```

**В чём расхождение.** Устройством типа исключена *дробь* с нулевым знаменателем: запись `p # q` с нулевым `q`
составить нельзя. *Операция* деления той же библиотеки нулевой делитель принимает и возвращает нуль, а условие
«не нуль» стоит в библиотеке посылкой теоремы об обратном элементе. Этой операцией пользуется вся формализация
(`QArith` подключают 1640 файлов `src`).

**(а) Довести формализацию.** Определения библиотеки менять нельзя и незачем. Честно возможно другое — записать
теоремами то, что говорит § 2.4 об уравнении соразмерности $q \cdot u = p$: оно задаёт шаг тогда и только тогда,
когда $q \neq 0$; значение, которое библиотека возвращает при нулевом делителе, уравнения не решает; и дать
деление, в тип которого условие встроено. Набросок проверен (`Check.v`, Closed under the global context):

```coq
Theorem commensuration_solved : forall q p : Q, ~ q == 0 -> q * (p / q) == p.
Proof. intros q p Hq. field. exact Hq. Qed.

Theorem commensuration_unique : forall q p u : Q,
  ~ q == 0 -> q * u == p -> u == p / q.
Proof. intros q p u Hq H. rewrite <- H. field. exact Hq. Qed.

(* q = 0, p <> 0: решения нет *)
Theorem zero_parts_no_step : forall p u : Q, ~ p == 0 -> ~ (0 * u == p).
Proof. intros p u Hp H. apply Hp. rewrite <- H. ring. Qed.

(* q = 0, p = 0: годится любой шаг *)
Theorem zero_parts_any_step : forall u : Q, 0 * u == 0.
Proof. intro u. ring. Qed.

(* уравнение задаёт шаг: решение есть и оно одно (с точностью до Qeq) *)
Definition determines_step (q p : Q) : Prop :=
  exists u : Q, q * u == p /\ forall u' : Q, q * u' == p -> u' == u.

Theorem commensuration_determines_iff : forall q p : Q,
  determines_step q p <-> ~ q == 0.
Proof.
  intros q p. split.
  - intros [u [Hu Huniq]] Hq.
    assert (Hp : p == 0). { rewrite <- Hu, Hq. ring. }
    assert (H1 : q * (u + 1) == p). { rewrite Hq, Hp. ring. }
    specialize (Huniq (u + 1) H1).
    assert (Habs : 1 == 0).
    { setoid_replace 1 with ((u + 1) - u) by ring. rewrite Huniq. ring. }
    unfold Qeq in Habs. simpl in Habs. discriminate Habs.
  - intro Hq. exists (p / q). split.
    + apply commensuration_solved. exact Hq.
    + intros u' H. apply commensuration_unique; assumption.
Qed.

Theorem library_value_at_zero_is_not_a_solution : forall p : Q,
  ~ p == 0 -> ~ (0 * (p / 0) == p).
Proof. intros p Hp. apply zero_parts_no_step. exact Hp. Qed.

(* деление, в тип которого встроено условие q <> 0 *)
Definition NonZeroQ : Type := { q : Q | ~ q == 0 }.
Definition step_of (p : Q) (q : NonZeroQ) : Q := p / proj1_sig q.

Theorem step_of_spec : forall (p : Q) (q : NonZeroQ),
  proj1_sig q * step_of p q == p /\
  (forall u : Q, proj1_sig q * u == p -> u == step_of p q).
```

Теоремы `zero_parts_no_step` и `zero_parts_any_step` — два случая § 2.4 (стр. 349–358), а
`commensuration_determines_iff` — его вывод (стр. 360–362: «либо решения нет вовсе, либо оно не единственно и
потому ничего не определяет»). Место для них — новый файл с подключением одной `QArith` (имя — по решению автора).
После добавления страница может ссылаться на них вместо слов об устройстве типа.

**(б) Поправить слова:**

> (445–448) Тем условие $q \neq 0$ (§ 2.4) оказывается *встроенным в самый тип*: знаменатель просто не может быть
> нулём, и дроби с нулевым знаменателем формальная запись не допускает не запретом, а устройством типа. Об
> *операции* деления нужна оговорка: библиотечная функция деления определена для любой пары чисел и при нулевом
> делителе возвращает нуль — это техническое соглашение, принятое, чтобы функция была определена всюду; закон
> обратного элемента библиотека доказывает при условии $x \neq 0$. Уравнения соразмерности это соглашение не
> решает: $0 \cdot u = p$ при $p \neq 0$ не выполняется ни для какого $u$ (§ 2.4).
>
> (527–528) Ненулевость знаменателя встроена в тип: дроби с нулевым знаменателем формальная запись не допускает
> устройством, а не запретом. Операция деления в библиотеке определена всюду и при нулевом делителе возвращает
> нуль по техническому соглашению; закон обратного элемента доказан там для ненулевого числа.

Слова стр. 651–652 («обратные определены всюду (кроме деления на нуль)») сказаны о стандартной алгебраической
системе $ℚ$, не о библиотеке, и правки не требуют.

## Расхождение 2. Статус: «как и для целых» (стр. 826–828; связано — стр. 420–421)

**Было:**

> Оговорка о статусе, как и для целых (Глава III.1): ToS не строит свой тип рациональных — пользуется стандартным
> `Q` из `QArith` (`Record` числитель/знаменатель, § 2.5);

**Проверка.** О рациональных сказано верно: собственного типа в `src` нет, объявлений о соразмерности в смысле
главы тоже нет. Для целых положение другое. `src/CoordinateIntegers.v` (13 `Qed`, без аксиом):

```coq
Record FormalDiff := mkFD { fd_pos : nat ; fd_neg : nat }.                                  (* :41 *)
Lemma fd_equiv_iff_Z : forall x y, fd_equiv x y <-> fd_to_Z x = fd_to_Z y.                  (* :70 *)
Lemma fd_to_of_Z : forall z, fd_to_Z (fd_of_Z z) = z.                                       (* :82 *)
Lemma fd_add_to_Z : forall x y, fd_to_Z (fd_add x y) = fd_to_Z x + fd_to_Z y.               (* :98 *)
Lemma fd_mul_to_Z : forall x y, fd_to_Z (fd_mul x y) = fd_to_Z x * fd_to_Z y.               (* :119 *)
```

Глава III.1 говорит об этом в своей оговорке (стр. 1121–1128): «у этой главы теперь есть *свой* файл-якорь —
`CoordinateIntegers.v` (§ 1.8.1) строит запись целого как формальной разности (`Record FormalDiff`) и доказывает
её изоморфизм стандартному `Z`».

**В чём расхождение.** Для целых собственная запись в формализации есть и её соответствие `Z` доказано; для
рациональных такой записи нет. Слова «как и для целых» уравнивают два разных положения.

**(а) Довести формализацию.** Возможно, без аксиом: запись соразмерной позиции по образцу `FormalDiff`. Набросок
проверен (`Check.v`, все леммы — Closed under the global context):

```coq
(* позиция = число взятых малых шагов и число новых границ внутри единичного шага;
   частей на единицу больше, чем границ, — нуля частей не бывает *)
Record Commens := mkCm { cm_steps : Z ; cm_cuts : nat }.

Definition cm_parts (x : Commens) : positive := Pos.of_succ_nat (cm_cuts x).
Definition cm_to_Q (x : Commens) : Q := cm_steps x # cm_parts x.
Definition cm_of_Q (q : Q) : Commens :=
  mkCm (Qnum q) (Nat.pred (Pos.to_nat (Qden q))).
Definition cm_eq (x y : Commens) : Prop :=
  (cm_steps x * Z.pos (cm_parts y) = cm_steps y * Z.pos (cm_parts x))%Z.

Lemma cm_parts_count : forall x : Commens, Pos.to_nat (cm_parts x) = S (cm_cuts x).
Lemma cm_to_of : forall q : Q, cm_to_Q (cm_of_Q q) = q.
Lemma cm_of_to : forall x : Commens, cm_of_Q (cm_to_Q x) = x.
Lemma cm_eq_iff_Qeq : forall x y : Commens, cm_eq x y <-> cm_to_Q x == cm_to_Q y.
Lemma cm_no_cuts_is_integer : forall z : Z, cm_to_Q (mkCm z 0) = inject_Z z.
Lemma cm_add_to_Q : forall x y : Commens, cm_to_Q (cm_add x y) = cm_to_Q x + cm_to_Q y.
Lemma cm_mul_to_Q : forall x y : Commens, cm_to_Q (cm_mul x y) = cm_to_Q x * cm_to_Q y.

(* § 2.2: позиция p/q есть p-кратное повторение малого шага 1/q; q малых шагов составляют единицу *)
Lemma position_is_multiple_of_small_step : forall (p : Z) (q : positive),
  p # q == inject_Z p * (1 # q).
Lemma small_steps_make_unit : forall q : positive, inject_Z (Z.pos q) * (1 # q) == 1.
Lemma new_step_reading : forall (p : Z) (q : positive),
  inject_Z (Z.pos q) * (p # q) == inject_Z p.

(* § 2.7: внутренние точки единичного отрезка; медианта *)
Lemma inner_point : forall k n : positive,
  (k < n)%positive -> 0 < Z.pos k # n /\ Z.pos k # n < 1.
Lemma mediant_between_Q : forall (a c : Z) (b d : positive),
  a # b < c # d -> a # b < (a + c) # (b + d) /\ (a + c) # (b + d) < c # d.
```

Оговорка к наброску. Запись `Commens` — та же пара, что и `Q`, с числом границ вместо числа частей (§ 2.2:
«$q-1$ границ»); переходы `cm_to_Q` и `cm_of_Q` взаимно обратны на самих записях. Новое содержание несёт не тип,
а теоремы о нём: позиционное чтение, «$q$ малых шагов составляют единицу», согласованность действий, уравнение
соразмерности (расхождение 1). Нужна ли тому такая запись или достаточно теорем о стандартном `Q`, решает автор.

**(б) Поправить слова** (стр. 826–830):

> Оговорка о статусе. Для целых у тома есть собственная машинная конструкция (`CoordinateIntegers.v`,
> Глава III.1); для рациональных её нет: ToS не строит свой тип рациональных — пользуется стандартным `Q` из
> `QArith` (`Record` числитель/знаменатель, § 2.5); машинно проверенное — сама полевая арифметика `Q` и отношение
> `Qeq`, а соразмерное чтение несёт проза.

Фраза стр. 420–421 («Как и для целых чисел, ToS не строит рациональные числа заново») повторяет слова Главы III.1
в том же месте (стр. 756–758: «Целые числа ToS не строит заново») и о типе сказана верно; в ведомости она
записана как ok с пометкой.

## Расхождение 3. «Полная биекция $ℕ \leftrightarrow ℚ$ … доказана» (стр. 949–951; связано — стр. 954–956)

**Было:**

> Стоит заранее оговорить точный статус: *полная* биекция $ℕ \leftrightarrow ℚ$ с вычислимым обращением доказана
> не только для положительных, но и для всего $ℚ$ — со знаком и нулём. Функция `enum_Q` приписывает обходу знак и
> позицию нуля, обратная `index_of_Q` по рациональному находит его номер, а теорема `Q_bijection` доказывает —
> тоже без аксиом, — что они взаимно обратны (с точностью до `Qeq`: $2/4$ и $1/2$ — получают один номер).

**Проверка.** `src/Countability_Q.v:759`:

```coq
Theorem Q_bijection :
  (forall n : nat, index_of_Q (enum_Q n) = n) /\
  (forall q : Q, enum_Q (index_of_Q q) == q).
Proof. split; [ exact index_of_Q_enum_id | exact enum_Q_index_id ]. Qed.
```

Closed under the global context — цена на странице названа верно. Обе круговые формулы доказаны; вторая — с
точностью до `Qeq`, как и сказано.

Для биекции между номерами и рациональными, взятыми с точностью до `Qeq`, нужно ещё одно: номер не должен зависеть
от записи дроби, `p == q -> index_of_Q p = index_of_Q q`. Такой леммы в `src` нет: имя `index_of_Q` встречается
только в `Countability_Q.v` (определение и три теоремы) и в комментарии `process/ProcessRationalsNull.v`. Из двух
формул теоремы она не следует — им удовлетворяет и пара тождественных функций на $ℕ$ при отношении, в котором все
числа равны (`Check.v`, Closed under the global context):

```coq
Lemma round_trips_alone_do_not_give_quotient_bijection :
  exists (E : nat -> nat -> Prop) (f g : nat -> nat),
    Equivalence E /\
    (forall n, g (f n) = n) /\
    (forall t, E (f (g t)) t) /\
    (exists a b, E a b /\ g a <> g b).
```

Для действительных `enum_Q` и `index_of_Q` недостающее свойство верно — оно следует из определения
`index_of_Q` (номер берётся по несократимой записи `Qred q`) и библиотечной леммы `Qred_complete`. Пример
страницы подтверждается вычислением: `index_of_Q (2 # 4) = index_of_Q (1 # 2) = 3`.

**В чём расхождение.** Теорема доказывает, что обход и обращение возвращают друг друга. Что равным дробям
отвечает один номер — без этого нет биекции с рациональными *значениями*, — на странице сказано в скобках как
пояснение, а в формализации теоремой не записано. Утверждение верно; недостаёт одной леммы. Та же формулировка
стоит в Главе III.3 (стр. 559–572, 585–588).

**(а) Довести формализацию.** Возможно, без аксиом; добавить в `Countability_Q.v` после `Q_bijection` (новых
подключений не требуется: `QArith` вывозит `Qreduction`). Набросок проверен (`Check.v`, Closed under the global
context):

```coq
Lemma index_of_Q_compat : forall p q : Q, p == q -> index_of_Q p = index_of_Q q.
Proof.
  intros p q H. unfold index_of_Q. rewrite (Qred_complete p q H). reflexivity.
Qed.

Lemma index_of_Q_reflects : forall p q : Q, index_of_Q p = index_of_Q q -> p == q.
Proof.
  intros p q H.
  transitivity (enum_Q (index_of_Q p)).
  - symmetry. apply enum_Q_index_id.
  - rewrite H. apply enum_Q_index_id.
Qed.

Theorem enum_Q_injective : forall n m : nat, enum_Q n == enum_Q m -> n = m.
Proof.
  intros n m H.
  transitivity (index_of_Q (enum_Q n)); [ symmetry; apply index_of_Q_enum_id | ].
  transitivity (index_of_Q (enum_Q m)); [ | apply index_of_Q_enum_id ].
  apply index_of_Q_compat. exact H.
Qed.

Theorem Q_bijection_up_to_Qeq :
  (forall n : nat, index_of_Q (enum_Q n) = n) /\
  (forall q : Q, enum_Q (index_of_Q q) == q) /\
  (forall p q : Q, p == q <-> index_of_Q p = index_of_Q q) /\
  (forall n m : nat, enum_Q n == enum_Q m <-> n = m).
```

После добавления слова страницы верны без правки (имя теоремы можно заменить на `Q_bijection_up_to_Qeq`).

**(б) Поправить слова** (если формализацию не трогать):

> Стоит заранее оговорить точный статус: обход с вычислимым обращением построен и доказан не только для
> положительных, но и для всего $ℚ$ — со знаком и нулём. Функция `enum_Q` приписывает обходу знак и позицию нуля,
> обратная `index_of_Q` по рациональному находит его номер, а теорема `Q_bijection` доказывает — тоже без
> аксиом, — что они взаимно обратны (с точностью до `Qeq`). Что равные дроби — $2/4$ и $1/2$ — получают один
> номер, видно из определения `index_of_Q`: номер берётся по несократимой записи; отдельной теоремой в файле это
> пока не записано.

## Сомнительные места (не расхождения)

1. **Стр. 830–833, «работает с *положительными* парами `QPos`».** Описание файла неполное: его разделы со
   стр. 534 работают со всем $ℚ$ (`enum_Q`, `Q_countable`, `index_of_Q`, `Q_bijection`), о чём сама глава говорит
   ниже (стр. 949–956). Согласованная форма: «…есть якорь *следующей* главы: он работает с *положительными*
   парами `QPos` и достраивает обход до всего $ℚ$ (§ 2.8.5)».
2. **Сноска 1 (стр. 976) и стр. 439–441, место объявлений.** Тип `Q` объявлен в модуле
   `Stdlib.QArith.QArith_base`; модуль `QArith` его вывозит. В Rocq 9 стандартная библиотека поставляется
   отдельным пакетом `Stdlib` (в установке — `user-contrib/Stdlib`), а типы `positive` и `Z` объявлены в базовой
   библиотеке `Corelib.Numbers.BinNums`. Существо сноски — тип взят не из репозитория ToS — верно. Точнее: «в
   стандартной библиотеке Rocq — в модуле `QArith` (файл `QArith_base`)»; «`QArith` есть часть стандартной
   библиотеки Rocq, не Rocq-репозитория ToS».
3. **Стр. 514–515, «в части, посвящённой алгебре, оно будет пройдено в полной мере».** На страницах Части XI
   («Алгебра, поля, Галуа») слов «дробей», «дроби» нет; во всём томе выражение «поле дробей» встречается только в
   этой главе. В `src` общего построения поля дробей нет (поиск по именам и комментариям). Рядом, стр. 641–642:
   «к которому глава ещё вернётся в части об алгебре» — возвращаться может том, не глава.
4. **Стр. 711–714, «полную теорию плотности $ℚ$ … глава здесь не разворачивает; это предмет дальнейших частей».**
   Последующие главы ссылаются за плотностью назад, на эту: Глава III.4, стр. 50 («Соразмерная разметка плотна
   (Глава III.2)»). В формализации утверждение «между двумя рациональными лежит рациональное» есть в двух видах:
   `mediant_between_left`, `mediant_between_right` (`src/stdlib/SternBrocot.v:97`, `:102` — медианта, в
   перекрёстной записи над `Z`) и `midpoint_between`, `midpoint_below`
   (`src/process/ProcessSpectralTheoryQ.v:99`, `:106` — середина, над `Q`); все четыре — Closed under the global
   context. Слова «и притом бесконечно много» теоремой не записаны. Примеры страницы верны: медианта $1/3$ и
   $1/2$ есть $2/5$, медианта $2/5$ и $1/2$ есть $3/7$ (`Check.v`, `mediant_1_3_1_2`).
5. **Стр. 438–452, слово `positive`.** Оговорка главы имеет буквальное соответствие в коде: в формализации имя
   `positive` носят два разных объявления — тип стандартной библиотеки и поле записи `Distinction`
   (`Distinction.positive : Distinction -> Prop`, `src/foundation/Distinction.v`). В файле, подключающем оба,
   команда `Locate positive` отвечает обоими.
6. **Стр. 499 и 885, «Глава 4.3».** Имеется в виду Глава 3 Части IV («Точка как класс эквивалентности
   процессов»); во всех остальных местах главы ссылки записаны в виде «Глава III.1». Единообразно: «Глава IV.3».
7. **Стр. 209–215, «Глава II.1 показала: единица есть *сам первый акт различения*».** Слово «показала» отнесено к
   изложению Главы II.1 и здесь не оценивалось; это предмет ведомости Части II. Для сведения: в формализации
   `one_from_distinction (D : Distinction) : nat := 1` (`src/foundation/PrimalityOfOne.v:40`) — определение, не
   зависящее от аргумента.
8. **Стр. 856–861, «по $P4$ всякое рациональное есть *конечный* объект — пара числитель/знаменатель».** Страница
   на теорему не ссылается. В формализации ближайшее утверждение — `P4_finite_at_each_stage`
   (`src/foundation/PrinciplesFromLaws.v:218`): `forall (R : nat -> Q) (n : nat), exists (num : Z) (den :
   positive), R n = num # den` — разбор значения типа `Q` на два поля; Closed under the global context. Свойство
   «конечный» в ней не определяется.
9. **Стр. 545, 773, 931, слова «построена», «построены».** Относятся к изложению: формально тип взят из
   библиотеки, и глава говорит это сама (стр. 420–423, 523–526, 826–830). При правке по расхождению 2 можно
   оставить как есть.
10. **Стр. 567–573, «у целого числа $2$ такого обратного среди целых чисел нет».** Утверждение верно; в `src`
    теоремой не записано (есть `Z_ring : Ring`, `src/stdlib/RingField.v:238`). В пробном файле:
    `two_has_no_integer_inverse : ~ exists z : Z, (2 * z = 1)%Z` и `Z_has_no_inverse_operation` — Closed under
    the global context.

## Вне главы: шапки и состав файлов

Для сведения (в главе эти строки не цитируются):

- `Countability_Q.v:6` — шапка называет целью «bijection ℕ ↔ ℚ⁺», а файл доказывает обход и обращение для
  всего $ℚ$. Комментарий `:559–563` («Доказана именно СЮРЪЕКЦИЯ (роль-правило), не реифицированная
  биекция-объект») стоит перед разделом `:642–762`, озаглавленным «FULL BIJECTION ℕ ↔ ℚ». Заголовок «SECTION 10»
  стоит дважды (`:491`, `:642`).
- `Countability_Q.v:503–505` — комментарий: «THEOREM B (ShrinkingIntervals): ℕ → (ℕ → ℚ) is not surjective. For
  any f : ℕ → (ℕ → ℚ), there exists D : ℕ → ℚ with D ≠ f(n) for all n. PROOF: Uses only LEM (classic)». Теорема
  `unit_interval_uncountable_trisect_v2` (`src/ShrinkingIntervals_ERR.v:3569`) имеет посылку
  `valid_regular_enumeration E`, говорит о процессах Коши на $[0,1]$ и о неэквивалентности (`not_equiv`), а не о
  неравенстве функций; `Print Assumptions` — Closed under the global context.
- `stdlib/RingField.v:54` — в записи `Field` нет требования $0 \neq 1$; закон обратного стоит под условием
  `~ g_eq x (g_id …)`, как в библиотеке. Экземпляр `Q_field` (`:314`)
  берёт обратным библиотечный `Qinv`, то есть со значением `/ 0 = 0`.
- `stdlib/RingField.v`, `stdlib/SternBrocot.v`, `CoordinateIntegers.v` — число `Qed` в шапках (20, 13, 13)
  совпадает с действительным счётом.

## Дополнительные проверки

- Файлы `Countability_Q.v`, `stdlib/RingField.v`, `stdlib/SternBrocot.v`, `CoordinateIntegers.v`,
  `foundation/PrinciplesFromLaws.v`, `stdlib/GroupTheory.v`, `ShrinkingIntervals_ERR.v` в репозитории и в
  собранной копии совпадают побайтно.
- Счёт `Qed` (`grep -c 'Qed\.'`): `Countability_Q.v` — 33 (и одно `Defined`), `stdlib/RingField.v` — 20,
  `stdlib/SternBrocot.v` — 13, `CoordinateIntegers.v` — 13. Строк `Axiom` и `Parameter` в этих файлах нет. Чисел
  такого рода на странице нет.
- `Print Assumptions` для всех имён главы из `Countability_Q.v` (`QPos`, `enum_QPos`, `Q_positive_countable`,
  `enum_Q`, `index_of_Q`, `Q_bijection`) и для `Q_countable`, `enum_Q_index_id`, `index_of_Q_enum_id`,
  `enum_injective`, `enum_surjective`, `Q_field`, `Z_ring`, `mediant_between_left`, `mediant_between_right`,
  `P4_finite_at_each_stage` — Closed under the global context.
- Имена стандартной библиотеки (`CheckPA.v`): `Q`, `Qnum`, `Qden`, `Qeq`, `Qinv`, `Qdiv`, `positive`, `Qsft`,
  `Qmult_inv_r`, `Q_Setoid`, `Qred_complete`, `Qred_correct` — Closed under the global context.
- Блок кода (стр. 428–431) совпадает с `Stdlib/QArith/QArith_base.v:23` и с ответом `Print Q`. Отметка
  инструмента «ОТЛИЧАЕТСЯ» вызвана тем, что блок сравнён с `Variable Q : Type` из `src/cs/PumpingPigeonhole.v:38`.
- Сведения главы о типе `Q` проверены леммами пробного файла: `half_neq_two_quarters : (1 # 2) <> (2 # 4)`,
  `half_Qeq_two_quarters : (1 # 2) == (2 # 4)`, `Qeq_is_cross_product`, `denominator_never_zero`,
  `Qinv_m3_4 : / (-3 # 4) = (-4 # 3)`, `Qinv_neg_general : / (Z.neg p # q) = (Z.neg q # p)`.
- Поле: в библиотеке — `Qsft : field_theory 0 1 Qplus Qmult Qminus Qopp Qdiv Qinv Qeq` (`Qfield.v:31`); в проекте —
  `Q_field : Field` (`stdlib/RingField.v:314`) над `Q_ring` (`:282`) и `Q_add_group` (`stdlib/GroupTheory.v:415`),
  равенство носителя — `Qeq`. Страница эти объявления не называет; их можно назвать в § 2.6 и в оговорке
  стр. 829–830.
- Вычислено: `enum_QPos 0..4 = (1,1), (1,2), (2,1), (1,3), (3,2)`; `enum_Q 0..4 = 0, 1, -1, 1#2, -1#2`;
  `index_of_Q (1#2) = 3`, `index_of_Q (2#4) = 3`, `index_of_Q 0 = 0`, `index_of_Q (-3#4) = 28`.
- Слова стр. 966–968 («файл прямо отмечает этот контраст») относятся к комментариям `Countability_Q.v:6–9` и
  `:494–531`; теоремы о процессах в самом файле нет, и страница этого не утверждает.
