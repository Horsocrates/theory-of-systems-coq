# Глава III.3 «Счётность рациональных чисел» — заметки к ведомости (13.11.2026)

Ведомость: `part03-ch03.json` — 60 ручных записей + 7 автоматических (`positive`, `nat`, `xH`, `xO`, `xI`, `Qeq`,
`Qred` — имена стандартной библиотеки); `merge --dry` проходит без замечаний, список «без сверки» пуст.
Вердикты ручных записей: ok — 53, mismatch-statement — 7 (с автоматическими: ok — 60). Расхождений цены, имён
без объявления и неверных чисел нет.

Семь записей с расхождением относятся к двум местам: шесть — к расхождению 1 (четыре о биекции для всего $ℚ$,
две о словах «каждое значение однажды» при `enum_coprime`), одна — к расхождению 2 (строка таблицы).

Глава называет один файл — `src/Countability_Q.v` (776 строк, 33 `Qed`, одно `Defined`; строк `Axiom`,
`Parameter`, `Admitted` нет). Файл прочитан целиком; для всех 34 объявлений снят `Print Assumptions` — каждое
«Closed under the global context». Исходник в репозитории и в собранной копии совпадают (`diff`).

Пробные файлы лежат в `C:/Users/abary/tos-audit-build/_part03/ch03/`:

- `status.txt` — вывод `tom-status.cjs chapter 03/03`;
- `PA.v` — `Print Assumptions` всех объявлений `Countability_Q.v`;
- `Check.v` — вычисления первых членов обхода; недостающие утверждения об уровне значений; контрпример к строке
  таблицы; схема, показывающая, что два круговых обхода сами по себе биекции значений не дают; независимость
  результата `path_to_node_fuel` от запаса для всякой пары. Собирается; все тринадцать утверждений файла —
  «Closed under the global context»;
- `addition.v.txt` и `CountabilityQPlus.v` — текст предлагаемого дополнения и копия `Countability_Q.v` с этим
  дополнением в конце (проверка, что дополнение собирается в окружении самого файла: 43 `Qed`, все новые
  утверждения — «Closed under the global context»).

В `src` и в собранной копии ничего не менялось; база связей не менялась (`merge` запускался только с `--dry`).

## Что проверить не удалось

- Отсылки к другим главам и частям (Глава III.2, § 2.5 и § 2.7; Часть I; Часть II; Часть IV) по содержанию не
  сверялись — это предмет их ведомостей. Сверены только адреса: в Главе III.2 пятый раздел — «Формальная
  конструкция» (подраздел «Равенство дробей»), седьмой — «Делимость единичного отрезка» (подраздел «Знак
  рациональной позиции»); Часть IV — «Процессные действительные числа», её четвёртая глава — «Несчётность
  процессов»; внутренние отсылки § 3.8.3 и § 3.8.4 указывают на разбор E/R/R и на раздел «Чего рациональным
  числам недостаёт».
- Теорема, на которую ссылается комментарий файла («THEOREM B (ShrinkingIntervals)», сноска 6 главы), — предмет
  Части IV. Проверено только, что `unit_interval_uncountable_trisect_v2` существует
  (`src/ShrinkingIntervals_ERR.v:3569`) и что `Print Assumptions` даёт «Closed under the global context».
- Общий тезис «перечислима всякая совокупность конечных выражений над счётным алфавитом» (стр. 727–736,
  776–779, 802–803) с формализацией не сверялся: глава не называет его формализованным, и общей теоремы такого
  вида поиском по `src` (объявления со словами countab, enumerab) не найдено. То же о словах «целые …
  перечислимы» (стр. 779): отдельного перечисления целых в `src` поиском по именам не найдено; глава теоремы и
  не называет.
- Слово «вычислимо» проверено только делом: функции `enum_QPos`, `index_of_QPos`, `enum_Q`, `index_of_Q` —
  определения без аксиом, и на конкретных номерах и дробях они вычисляются командой `vm_compute`. Общего
  понятия вычислимости в названном файле нет, и глава на него не ссылается.
- Сведения о стандартной математике (диагональное перечисление, дерево Штерна–Броко; стр. 128–132) вне
  предмета аудита.
- Английская страница и LaTeX-исходник главы не смотрелись.

Всё остальное проверено по исходнику и компилятору.

## Расхождение 1. «Биекция рациональных значений»: доказаны два круговых обхода; утверждения «равные по значению дроби получают один номер» в файле нет (стр. 559–562, 569–572, 585–588, 869–874; для положительных — стр. 883–886, 912)

**Было:**

> (559–562) Это *полная биекция $ℕ \leftrightarrow ℚ$ с вычислимым обращением* — уже не только для
> положительных, а для всего $ℚ$, конструктивно и *без единой аксиомы* (`Print Assumptions Q_bijection`:
> «Closed under the global context»).
>
> (569–572) Потому `index_of_Q_enum_id` точна на $ℕ$ (равенство номеров), а `enum_Q_index_id` — с точностью до
> `Qeq` на $ℚ$; вместе это и есть биекция рациональных *значений*.
>
> (585–588) …и теорема `Q_bijection` доказывает их взаимную обратность — полную биекцию $ℕ \leftrightarrow ℚ$
> (с точностью до `Qeq`, 0 аксиом) уже для всего $ℚ$.
>
> (869–874) Оговорка о статусе теперь снята: для всего $ℚ$ доказана *полная* биекция $ℕ \leftrightarrow ℚ$ с
> вычислимым обращением — две круговые теоремы `enum_Q_index_id` и `index_of_Q_enum_id`, 0 аксиом — с
> единственной точностью, что $ℚ$ берётся до `Qeq` ($2/4$ и $1/2$ получают один номер), иначе биекции и быть не
> может.
>
> (883–886) И правило канона: несократимость (`enum_coprime`) — всякое рациональное *значение* встречается
> ровно раз, $2/4$ не появляется отдельно от $1/2$ (§ 3.3).
>
> (912) | несократимость (`enum_coprime`) | каждое значение однажды | Rule |

**Проверка.** `src/Countability_Q.v:759`:

```coq
Theorem Q_bijection :
  (forall n : nat, index_of_Q (enum_Q n) = n) /\
  (forall q : Q, enum_Q (index_of_Q q) == q).
Proof. split; [ exact index_of_Q_enum_id | exact enum_Q_index_id ]. Qed.
```

`Print Assumptions Q_bijection`: Closed under the global context. Цена на странице названа верно.

Из двух членов теоремы следует:

- `enum_Q` инъективна по равенству записей: `enum_Q n = enum_Q m -> n = m`;
- всякое `q` равно по `Qeq` члену обхода со своим номером;
- разные значения получают разные номера: `index_of_Q q = index_of_Q q' -> q == q'`.

Не следует — и отдельной теоремой в файле не записано:

- номер зависит только от значения: `q == q' -> index_of_Q q = index_of_Q q'`;
- равносильное ему: обход не повторяет значений, `enum_Q n == enum_Q m -> n = m`.

Без этого утверждения функция `index_of_Q` не определена на значениях (на $ℚ$ с точностью до `Qeq`), и о
биекции значений говорить нельзя. Что из двух круговых обходов оно не выводится, показывает схема
(`Check.v`, `roundtrips_do_not_force_value_injectivity`, Closed under the global context): на типе `nat` с
отношением «`Nat.div2 x = Nat.div2 y`» и тождественными `E` и `I` выполнено и `I (E n) = n`, и `E (I x) ≈ x`,
а значения повторяются (`E 0 ≈ E 1`).

Сам факт для `enum_Q` и `index_of_Q` верен, и довод страницы (стр. 566–567: «обратный ход проходит через
приведение `Qred`») — правильный: `index_of_Q q` зависит только от `Qred q`, а `Qred` на равных по `Qeq`
дробях даёт одну запись (`Qred_complete` стандартной библиотеки). На примере страницы это вычислено:
`index_of_Q (2 # 4) = index_of_Q (1 # 2) = 3`. Но лемма `Qred_complete` в `src` не используется ни в одном
файле (поиск), то есть общий факт нигде в формализации не доказан.

То же для положительного обхода. `src/Countability_Q.v:189`:

```coq
Corollary enum_coprime : forall n,
  let (a, b) := enum_QPos n in
  Z.gcd (Z.pos a) (Z.pos b) = 1%Z.
```

Утверждение одно: всякая пара обхода взаимно проста (отсюда «$2/4$ не появляется»). «Всякое значение
встречается ровно раз» в файле доказано для несократимых пар с равенством пар (`enum_injective`, `:291`;
`enum_surjective`, `:450`). Перехода от пар к значениям — «у положительного значения одна несократимая пара» —
в файле нет; теоремы вида `qpos_to_Q (enum_QPos n) == qpos_to_Q (enum_QPos m) -> n = m` нет.

**В чём расхождение.** Доказаны два круговых обхода и соответствие номеров с несократимыми парами; утверждение
«равные по значению дроби получают один номер» (для положительных — «значение не повторяется в обходе») верно,
но теоремой не записано, а без него слова «биекция значений» и «каждое значение ровно раз» сильнее доказанного.

**(а) Довести формализацию до слов главы.** Возможно, без аксиом и без изменения существующих объявлений:
дописать в конец `Countability_Q.v` (после `Q_bijection`) восемь утверждений. Набросок проверен дважды — в
пробном файле поверх собранного модуля (`Check.v`) и в копии самого файла с дополнением
(`CountabilityQPlus.v`: собирается, 43 `Qed` — эти восемь и два утверждения к расхождению 2). Текст
дополнения (`addition.v.txt`):

```coq
(* Номер зависит только от значения: 2#4 и 1#2 получают один номер. *)
Lemma index_of_Q_Qeq : forall q q' : Q, q == q' -> index_of_Q q = index_of_Q q'.
Proof.
  intros q q' H. unfold index_of_Q.
  rewrite (Qred_complete q q' H). reflexivity.
Qed.

(* Обход не повторяет значений. *)
Theorem enum_Q_Qeq_injective : forall n m : nat, enum_Q n == enum_Q m -> n = m.
Proof.
  intros n m H.
  transitivity (index_of_Q (enum_Q n)); [ symmetry; apply index_of_Q_enum_id | ].
  transitivity (index_of_Q (enum_Q m)); [ | apply index_of_Q_enum_id ].
  apply index_of_Q_Qeq. exact H.
Qed.

(* Разные значения получают разные номера. *)
Theorem index_of_Q_inj_Qeq : forall q q' : Q, index_of_Q q = index_of_Q q' -> q == q'.
Proof.
  intros q q' H.
  transitivity (enum_Q (index_of_Q q)); [ symmetry; apply enum_Q_index_id | ].
  rewrite H. apply enum_Q_index_id.
Qed.

(* Биекция nat <-> Q с точностью до Qeq в полном виде. *)
Theorem Q_bijection_values :
  (forall n : nat, index_of_Q (enum_Q n) = n) /\
  (forall q : Q, enum_Q (index_of_Q q) == q) /\
  (forall q q' : Q, q == q' <-> index_of_Q q = index_of_Q q') /\
  (forall n m : nat, enum_Q n == enum_Q m <-> n = m).
Proof.
  split; [ exact index_of_Q_enum_id | ].
  split; [ exact enum_Q_index_id | ].
  split.
  - intros q q'. split; [ apply index_of_Q_Qeq | apply index_of_Q_inj_Qeq ].
  - intros n m. split; [ apply enum_Q_Qeq_injective | intros ->; reflexivity ].
Qed.

(* У положительного значения одна несократимая пара. *)
Lemma qpos_coprime_Qeq_eq : forall a b c d : positive,
  Z.gcd (Z.pos a) (Z.pos b) = 1%Z ->
  Z.gcd (Z.pos c) (Z.pos d) = 1%Z ->
  (Z.pos a # b) == (Z.pos c # d) -> (a, b) = (c, d).
Proof.
  intros a b c d H1 H2 H.
  apply Qred_complete in H.
  rewrite (Qred_id_pos a b H1), (Qred_id_pos c d H2) in H.
  injection H as Ha Hb. subst. reflexivity.
Qed.

Theorem enum_QPos_value_injective : forall n m : nat,
  qpos_to_Q (enum_QPos n) == qpos_to_Q (enum_QPos m) -> n = m.
Proof.
  intros n m H. apply enum_injective.
  pose proof (enum_coprime n) as Hn. pose proof (enum_coprime m) as Hm.
  destruct (enum_QPos n) as [a b]. destruct (enum_QPos m) as [c d].
  cbn [qpos_to_Q] in H. apply qpos_coprime_Qeq_eq; assumption.
Qed.

Theorem enum_QPos_value_surjective : forall q : Q,
  0 < q -> exists n : nat, qpos_to_Q (enum_QPos n) == q.
Proof.
  intros q Hq.
  pose proof (Qred_correct q) as Hr.
  pose proof (Qred_coprime q) as Hc.
  assert (Hpos : 0 < Qred q) by (rewrite Hr; exact Hq).
  remember (Qred q) as r eqn:E. destruct r as [z d].
  cbn [Qnum Qden] in Hc.
  destruct z as [ | a | a ].
  - exfalso. unfold Qlt in Hpos. cbn in Hpos. lia.
  - destruct (enum_surjective a d Hc) as [n Hn]. exists n.
    rewrite Hn. cbn [qpos_to_Q]. exact Hr.
  - exfalso. unfold Qlt in Hpos. cbn in Hpos. lia.
Qed.

(* Каждое положительное рациональное ЗНАЧЕНИЕ стоит в обходе ровно один раз. *)
Theorem enum_QPos_each_value_once : forall q : Q, 0 < q ->
  exists n : nat, qpos_to_Q (enum_QPos n) == q /\
    forall m : nat, qpos_to_Q (enum_QPos m) == q -> m = n.
Proof.
  intros q Hq. destruct (enum_QPos_value_surjective q Hq) as [n Hn].
  exists n. split; [ exact Hn | ].
  intros m Hm. apply enum_QPos_value_injective. rewrite Hm, Hn. reflexivity.
Qed.
```

`Print Assumptions Q_bijection_values`, `Print Assumptions enum_QPos_each_value_once`: Closed under the global
context. После такого дополнения слова страницы верны без правки; достаточно добавить к ним имена:
`Q_bijection_values` — на стр. 559–562 и 869–874, `enum_QPos_each_value_once` — на стр. 883–886 и 912. Число
«776 строк» на стр. 865 при дополнении файла изменится — его нужно будет обновить по `wc -l`.

**(б) Поправить слова** (если формализацию не дополнять).

Стр. 559–562:

> Это *взаимная обратность прямого и обратного хода с вычислимым обращением* — уже не только для
> положительных, а для всего $ℚ$, конструктивно и *без единой аксиомы* (`Print Assumptions Q_bijection`:
> «Closed under the global context»).

Стр. 569–572:

> Потому `index_of_Q_enum_id` точна на $ℕ$ (равенство номеров), а `enum_Q_index_id` — с точностью до `Qeq` на
> $ℚ$; вместе с тем, что номер зависит только от значения дроби (это видно из определения `index_of_Q` через
> `Qred`; отдельной теоремой в файле не записано), это и есть биекция рациональных *значений*.

Стр. 585–588:

> …и теорема `Q_bijection` доказывает их взаимную обратность (с точностью до `Qeq`, 0 аксиом) уже для всего
> $ℚ$ — два круговых обхода, на которых стоит биекция $ℕ \leftrightarrow ℚ$.

Стр. 869–874:

> Оговорка о статусе теперь снята: для всего $ℚ$ доказаны две круговые теоремы `enum_Q_index_id` и
> `index_of_Q_enum_id`, 0 аксиом, — прямой и обратный ход взаимно обратны, обращение вычислимо; $ℚ$ при этом
> берётся до `Qeq` ($2/4$ и $1/2$ получают один номер — по определению `index_of_Q` через `Qred`), иначе
> биекции и быть не может.

Стр. 883–886:

> И правило канона: несократимость (`enum_coprime`) — в обходе стоят только несократимые пары, $2/4$ не
> появляется отдельно от $1/2$ (§ 3.3); а так как пары в обходе не повторяются (`enum_injective`), всякое
> рациональное *значение* представлено в нём одним узлом.

Стр. 912:

> | несократимость (`enum_coprime`) | в обходе только несократимые пары | Rule |

Места, которые при этом править не нужно: стр. 260–270 и 286–292 (страница сама оговаривает, что значение
берётся через несократимого представителя), стр. 488–494, 505–507, 514–516 (сказано «в несократимом
представлении»), стр. 637–639, 917–920.

## Расхождение 2. «Биекция `nat` $\leftrightarrow$ `QPos`»: тип `QPos` содержит и сократимые пары, обход их не достигает (стр. 911)

**Было:**

> | навигация $\leftrightarrow$ номер; обратимость | биекция `nat` $\leftrightarrow$ `QPos` | Rule |

**Проверка.** `Definition QPos := (positive * positive)%type.` (`src/Countability_Q.v:42`) — тип всех пар; глава
говорит это сама (стр. 209: «тип *всех* положительных пар»; стр. 219–220: «$(2, 4)$ и $(1, 2)$ — разные
элементы `QPos`»). Обход достигает только взаимно простых пар (`enum_coprime`, `:189`). В пробном файле
(`Check.v`, Closed under the global context):

```coq
Lemma enum_QPos_misses_2_4 : forall n : nat, enum_QPos n <> (2, 4)%positive.
Proof.
  intros n H. pose proof (enum_coprime n) as Hc. rewrite H in Hc.
  vm_compute in Hc. discriminate.
Qed.

Lemma index_of_QPos_not_injective :
  index_of_QPos (2, 4)%positive = index_of_QPos (1, 2)%positive /\ (2, 4)%positive <> (1, 2)%positive.
Proof. split; [ vm_compute; reflexivity | discriminate ]. Qed.
```

**В чём расхождение.** Обход взаимно однозначен с несократимыми парами, а в таблице назван весь тип `QPos`, в
который входят и сократимые пары.

**(а) Довести формализацию.** Для этого обхода нельзя: пара $(2,4)$ — контрпример к сюръективности на `QPos`,
пары $(2,4)$ и $(1,2)$ — к инъективности `index_of_QPos` на `QPos`. Точное утверждение можно свести в одну
теорему из трёх уже доказанных лемм (проверено в `CountabilityQPlus.v`, Closed under the global context):

```coq
Theorem enum_QPos_bijection_coprime :
  (forall n : nat, let (a, b) := enum_QPos n in Z.gcd (Z.pos a) (Z.pos b) = 1%Z) /\
  (forall n : nat, index_of_QPos (enum_QPos n) = n) /\
  (forall a b : positive, Z.gcd (Z.pos a) (Z.pos b) = 1%Z ->
     enum_QPos (index_of_QPos (a, b)) = (a, b)).
Proof.
  split; [ exact enum_coprime | ].
  split; [ exact index_of_QPos_enum | exact enum_QPos_index ].
Qed.
```

**(б) Поправить слова.**

> | навигация $\leftrightarrow$ номер; обратимость | биекция `nat` $\leftrightarrow$ несократимые пары `QPos` | Rule |

## Сомнительные места (расхождением не являются)

1. **Блок кода `path_to_node_fuel` (стр. 435–444).** От исходника (`:130`) отличается пометками области: в
   исходнике `(a =? b)%positive` и `(a <? b)%positive`, на странице — `(a =? b)` и `(a <? b)`. В самом файле
   область `positive_scope` открыта (`:29`), и запись страницы там читается так же; вне файла без открытой
   области блок страницы не соберётся. Остальные восемь блоков кода совпадают с исходником.
2. **Сноска 4, «топлива всегда достаточно».** В файле это доказано для узлов дерева (`path_fuel_cw_node`,
   `:315`: при любом запасе не меньше $a + b$ результат один) и для взаимно простых пар
   (`path_fuel_coprime_fuel_mono`, `:386`); оба объявления — `Lemma`. Для сократимых пар утверждения нет. Для
   всякой пары независимость результата от запаса сверх $a + b$ доказана в пробном файле (`path_fuel_indep`,
   Closed under the global context). Так как в дереве стоят только несократимые пары, слова сноски
   доказанному соответствуют.
3. **Стр. 425, «Если $a = b$, дробь есть $1/1$».** Функция возвращает `xH` при `a = b` для любой пары, в том
   числе для $(2,2)$. На сократимой паре `path_to_node` даёт путь несократимого представителя (вычислено:
   `cw_node (path_to_node (2,4)) = (1,2)`). Страница говорит о дробях дерева и условие несократимости называет
   (стр. 471–474).
4. **Стр. 543–544, «формула реализована буквально».** Определение `enum_Q` (`:582`) записано через `Nat.div2`
   и `Nat.even`; вид $E(2n+1)$, $E(2n+2)$ дают леммы `enum_Q_hit_pos` (`:590`) и `enum_Q_hit_neg` (`:597`),
   обе — равенства записей.
5. **«Теоремы о круговом обходе» (стр. 466, сноска 5).** `path_cw_node_roundtrip` и `cw_node_path_roundtrip`
   объявлены как `Lemma`. Вторая сформулирована в виде «дробь → путь → дробь»; слова страницы «проведённой в
   номер и обратно» точно соответствуют лемме `enum_QPos_index` (`:660`).
6. **Стр. 39–41, «именно в таком виде оно и доказывается в Rocq».** В виде «инъективность и сюръективность»
   записана теорема о положительных (`Q_positive_countable`); для всего $ℚ$ форма другая — сюръекция
   `Q_countable` и два круговых обхода `Q_bijection`.
7. **Стр. 60–62, операциональное определение счётности.** Отдельного определения («совокупность счётна, если
   есть процедура и обратная процедура») в названном файле нет; счётность $ℚ$ выражена конкретными теоремами.
   Глава такого определения формализованным и не называет.
8. **Имена `cw_left`, `cw_right`.** Одноимённые объявления есть в `src/stdlib/CalkinWilf.v:57–58`, там они
   определены на парах целых (`Z * Z`), а не на `QPos`. Глава называет `Countability_Q.v`; путаницы на
   странице нет.
9. **К исходнику, не к странице.** Комментарии `Countability_Q.v` в трёх местах отстали от самого файла и от
   компилятора: (i) `:503–505` — «THEOREM B … PROOF: Uses only LEM (classic)», тогда как
   `unit_interval_uncountable_trisect_v2` даёт «Closed under the global context» и доказана для регулярных
   перечислений, а не «для любой $f$»; (ii) `:559–563` — «Доказана именно СЮРЪЕКЦИЯ … не … биекция», тогда
   как ниже в том же файле доказана `Q_bijection`; (iii) два раздела имеют номер 10 (`:491` и `:642`), а шапка
   называет целью биекцию $ℕ \leftrightarrow ℚ^+$. Сноска 6 главы ссылается на комментарий (i) как на намеченный
   контраст и называет его комментарием — это верно.
