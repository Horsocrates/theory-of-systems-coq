# Глава II.4 «Бинарный путь: число как количество двоичного выбора» — заметки к ведомости (13.11.2026)

Ведомость: `part02-ch04.json` — 41 ручная запись + 12 автоматических; `merge --dry` проходит без замечаний,
список «без сверки» пуст. Вердикты ручных записей: ok — 38, mismatch-statement — 3 (с автоматическими: ok — 50).

Три записи с расхождением относятся к трём местам: одно в § 4.4 (стр. 459–462), два — в сноске 1 (стр. 1097;
знак сноски стоит на стр. 199).

Пробный файл: `C:/Users/abary/tos-audit-build/_part02/ch04/Check.v` — собирается; в нём 29 утверждений, для 20
итоговых снят `Print Assumptions` (ответы приведены по месту и сводкой в конце заметок). В `src` и в собранной
копии ничего не менялось.

Глава называет четыре файла `src/foundation/`: `Binarity.v` (17 `Qed`), `BitString.v` (7), `Distinction.v` (20),
`PrimalityOfOne.v` (15). Для проверки слов главы прочитаны ещё `DistinctionCoDefinition.v`, `BinarityVsTotality.v`,
объявления `LevelNatIso.v` и блоки кода главы II.2. Для всех объявлений `Binarity.v` и `BitString.v` снят
`Print Assumptions`: у всех — `Closed under the global context`. `Binarity.v` подключён в `src` одним файлом —
`BitString.v`; сам `BitString.v` не подключён никем.

Общий итог: о статусе формализации глава говорит точно в главном — двоичность в коде *задана* типом `Side`, а не
выведена из записи `Distinction` (стр. 178–199, 1012–1014); слой `BitString.v` описан дословно, блоки кода
совпадают с исходником, счёт «7 теорем, 0 аксиом» верен.

## Что проверить не удалось

- Отсылки к другим главам (II.1 § 1.2; II.2 § 2.3.3, 2.5, 2.6, 2.7; II.3 § 3.3.5, 3.4, 3.5, 3.6.5, 3.7; II.5;
  I.3) не сверялись: это предмет ведомостей этих глав. Из соседних глав прочитано только нужное для слов этой
  главы: блоки кода II.2 (для слов «прямое перенесение кардинального аппарата», стр. 431–432) и
  `LevelNatIso.v` (для слов о трёх операциях следования, стр. 566–570).
- Слова о теории информации (бит Шеннона, вероятностная мера; стр. 265–350) и о физике (энтропия,
  микросостояния, мера беспорядка; стр. 357–382, 1067–1070) вне предмета аудита. Проверено одно: в `Binarity.v`
  о них есть только комментарии (`:61–62`, `:71–72`), теорем нет — глава говорит то же.
- Одноимённые объявления в других файлах (`Side` — ещё в пяти файлах, `L2_exclusive` и `L3_exhaustive` — в
  `ERRKnowledgeBase.v`) не читались, кроме `BinarityVsTotality.v`: глава называет файл `Binarity.v`.
- Английская страница и LaTeX-исходник главы не смотрелись.

Всё остальное проверено по исходнику и компилятору.

## Расхождение 1. Число-сторона бинарного счёта «читается прямо», а в формализации её нет (стр. 459–462)

**Было:**

> Счёт здесь берётся со стороны *записи* (предикат `positive_bit_count` на `BitString`), а не индексируется
> числом; число-сторона («для всякого $n \ge 1$ есть запись длины $n$») читается с него прямо и параллельна уже
> доказанной `positive_nat_is_distinction_count` из `PrimalityOfOne.v`.

**Проверка.** `src/foundation/BitString.v:67–73`:

```coq
Definition positive_bit_count (bs : BitString) : Prop := (bit_length bs >= 1)%nat.

Lemma nonempty_positive_count : forall bs, bs <> [] -> positive_bit_count bs.
```

Это направление «от записи к числу»: непустая запись имеет длину не меньше единицы. Утверждение «для всякого
$n \ge 1$ есть запись длины $n$» идёт в обратную сторону — от числа к записи — и требует предъявить запись;
из предиката и из леммы оно не получается. В `BitString.v` (7 лемм) такого утверждения нет; нет его и в других
файлах `src` (`BitString.v` никем не подключён).

Теорема, с которой глава сравнивает, — `src/foundation/PrimalityOfOne.v:55, :94`:

```coq
Definition distinction_count_from_one (n : nat) : Prop :=
  exists (Ds : list Distinction), length Ds = n /\ (1 <= n)%nat.

Theorem positive_nat_is_distinction_count : forall n,
  (1 <= n)%nat -> distinction_count_from_one n.
```

`Print Assumptions positive_nat_is_distinction_count`: `Axioms: Classical_Prop.classic : forall P : Prop, P \/ ~ P`
(свидетель — список из `distinction_of True`).

**В чём расхождение.** Глава называет число-сторону читаемой «прямо» с предиката на записях; в Rocq это отдельное
утверждение обратного направления, и оно не доказано.

**(а) Довести формализацию.** Возможно, без аксиом; набросок проверен (`Check.v`, все — `Closed under the global
context`). Свидетель — запись из $n$ знаков `Marked`:

```coq
Lemma repeat_marked_length : forall n : nat, bit_length (repeat Marked n) = n.
Proof. intro n. unfold bit_length. apply repeat_length. Qed.

Theorem positive_nat_is_bit_count :
  forall n : nat, 1 <= n -> exists bs : BitString, bs <> [] /\ bit_length bs = n.
Proof.
  intros n Hn. exists (repeat Marked n). split.
  - destruct n as [| n']; [ lia | simpl; discriminate ].
  - apply repeat_marked_length.
Qed.

Theorem empty_not_positive_count : ~ positive_bit_count [].
Proof. unfold positive_bit_count, bit_length. simpl. lia. Qed.

(* положительные числа — в точности длины непустых записей *)
Theorem bit_count_iff_positive :
  forall n : nat,
    (exists bs : BitString, bs <> [] /\ bit_length bs = n) <-> 1 <= n.
Proof.
  intro n. split.
  - intros [bs [Hne Hlen]]. subst n.
    exact (nonempty_positive_count bs Hne).
  - apply positive_nat_is_bit_count.
Qed.
```

(Файл открывает `nat_scope`: `Binarity.v` оставляет открытым `Q_scope`.) В отличие от кардинального двойника,
бинарная теорема аксиом не требует: запись строится из конструктора `Marked`, а не из `distinction_of True`.
Там же проверены `positive_bit_count_iff_nonempty` (положительный счёт ⟺ запись непуста) и
`one_bit_is_least_positive_count` (единица — наименьший положительный счёт) — формальные двойники слов § 4.4.4
«нуль не первый бит и не положительный счёт» и «первое положительное число бинарного пути». Если леммы будут
дописаны в `BitString.v`, счёт «7 теорем» на стр. 462 и 983 изменится; если в отдельный файл — останется.

**(б) Поправить слова.** Стало (если формализация не меняется):

> Счёт здесь берётся со стороны *записи* (предикат `positive_bit_count` на `BitString`), а не индексируется
> числом; число-сторона («для всякого $n \ge 1$ есть запись длины $n$») в `BitString.v` отдельной леммой не
> записана — ей нужен свидетель, запись из $n$ бит, — и по смыслу параллельна уже доказанной
> `positive_nat_is_distinction_count` из `PrimalityOfOne.v`.

Стало (если теоремы дописаны):

> Счёт здесь берётся со стороны *записи* (предикат `positive_bit_count` на `BitString`), а не индексируется
> числом; число-сторона («для всякого $n \ge 1$ есть запись длины $n$») доказана отдельно — теоремой
> `positive_nat_is_bit_count`, а вместе с обратным направлением — `bit_count_iff_positive`: длины непустых
> записей суть в точности числа $n \ge 1$. Она параллельна уже доказанной `positive_nat_is_distinction_count` из
> `PrimalityOfOne.v` и, в отличие от неё, аксиом не требует.

## Расхождение 2. `side_binarity` названо теоремой, а это имя определения (сноска 1, стр. 1097)

**Было:**

> …эти определения теперь построены: в файле `BitString.v` (поверх `Binarity.v`) доказана синтетическая теорема
> `side_binarity := Marked <> Unmarked /\ (forall s, s = Marked \/ s = Unmarked)` (из `L2_exclusive` и
> `L3_exhaustive`);

**Проверка.** `src/foundation/BitString.v:30–34`:

```coq
Definition side_binarity : Prop :=
  Marked <> Unmarked /\ (forall s : Side, s = Marked \/ s = Unmarked).

Lemma side_is_binary : side_binarity.
Proof. split; [ exact L2_exclusive | exact L3_exhaustive ]. Qed.
```

`Print Assumptions side_is_binary`: `Closed under the global context`. В `src` есть второе объявление с тем же
именем — `Theorem side_binarity : forall s : Side, s = Pos \/ s = Neg` (`BinarityVsTotality.v:61`): оно о другом
типе `Side` (`Pos | Neg`) и говорит только об исчерпанности.

**В чём расхождение.** Имя `side_binarity` в `BitString.v` принадлежит пропозиции (определению); теорема, которая
её доказывает, называется `side_is_binary`. Содержание сноски верно.

**(а) Довести формализацию.** Менять нечего: утверждение доказано. Переименование не предлагается.

**(б) Поправить слова.** Стало:

> …эти определения теперь построены: в файле `BitString.v` (поверх `Binarity.v`) двоичность записана одной
> пропозицией `side_binarity := Marked <> Unmarked /\ (forall s : Side, s = Marked \/ s = Unmarked)` и доказана
> леммой `side_is_binary` (из `L2_exclusive` и `L3_exhaustive`);

## Расхождение 3. «Счёт сторон = 2» по двум леммам есть только «не больше двух» (сноска 1, стр. 1097)

**Было:**

> а для буквального «счёт сторон $=2$» — список `all_sides := [Marked; Unmarked]` с леммами полноты
> (`all_sides_complete`) и длины (`all_sides_length`: `length all_sides = 2`).

**Проверка.** `src/foundation/BitString.v:37–43`:

```coq
Definition all_sides : list Side := [Marked; Unmarked].

Lemma all_sides_complete : forall s : Side, In s all_sides.

Lemma all_sides_length : length all_sides = 2%nat.
```

Обе — `Closed under the global context`. Полный список длины 2 есть и у типа с одним значением; проверено
(`Check.v`, `Closed under the global context`):

```coq
Lemma complete_length_two_is_not_exactly_two :
  exists l : list unit, (forall u : unit, In u l) /\ length l = 2.
Proof.
  exists [tt; tt]. split.
  - intros []. left. reflexivity.
  - reflexivity.
Qed.
```

Леммы о том, что в `all_sides` нет повторов, в `src` нет.

**В чём расхождение.** Полнота списка и его длина дают оценку сверху — сторон не больше двух; «ровно две»
получается только вместе с неповторяемостью списка (она следует из `L2_exclusive`, но отдельным утверждением не
записана). Одного формального утверждения «сторон ровно две» в виде счёта в файле нет.

**(а) Довести формализацию.** Возможно, без аксиом; набросок проверен (`Check.v`, обе — `Closed under the global
context`):

```coq
Lemma all_sides_nodup : NoDup all_sides.
Proof.
  unfold all_sides. constructor.
  - intros [H | []]. exact (L2_exclusive (eq_sym H)).
  - constructor.
    + intros [].
    + constructor.
Qed.

(* всякое перечисление сторон без повторов имеет длину ровно 2 *)
Theorem side_count_exactly_two :
  forall l : list Side, NoDup l -> (forall s : Side, In s l) -> length l = 2.
Proof.
  intros l Hnd Hall.
  assert (H1 : length l <= length all_sides).
  { apply NoDup_incl_length; [ exact Hnd | intros s _; apply all_sides_complete ]. }
  assert (H2 : length all_sides <= length l).
  { apply NoDup_incl_length; [ exact all_sides_nodup | intros s _; apply Hall ]. }
  rewrite all_sides_length in H1, H2. lia.
Qed.
```

Вторая теорема не зависит от выбранного списка: число 2 в ней — свойство типа `Side`, а не записи
`[Marked; Unmarked]`. В ней работают обе леммы главы: `L2_exclusive` (через `all_sides_nodup`) и `L3_exhaustive`
(через `all_sides_complete`).

**(б) Поправить слова.** Стало (если формализация не меняется):

> а для счёта сторон — список `all_sides := [Marked; Unmarked]` с леммами полноты (`all_sides_complete`) и длины
> (`all_sides_length`: `length all_sides = 2`): полнота и длина дают «сторон не больше двух», различие
> конструкторов (`L2_exclusive`) — «не меньше двух».

Стало (если теоремы дописаны):

> а для буквального «счёт сторон $=2$» — список `all_sides := [Marked; Unmarked]` с леммами полноты
> (`all_sides_complete`), неповторяемости (`all_sides_nodup`) и длины (`all_sides_length`:
> `length all_sides = 2`) и теорема `side_count_exactly_two`: всякое перечисление сторон без повторов имеет
> длину $2$.

## Сомнительные места, которые расхождением не являются

1. **Леммы `L2_exclusive` и `L3_exhaustive` не опираются на законы (стр. 159–169, 191–199, 987–989).** Обе
   доказаны свойствами индуктивного типа (`discriminate`; `destruct s`), обе `Closed under the global context`;
   исключённое третье (`Classical_Prop.classic`) в `L3_exhaustive` не входит. Буквы «L2» и «L3» в именах — прочтение.
   Глава говорит это сама («задана типом `Side` и подтверждена двумя леммами, отвечающими $L2$ и $L3$»), о цене
   лемм не говорит ничего сверх «0 аксиом». Слова «выведена из законов логики» (стр. 71–72, 97–98, 305–306,
   944–948, 1068–1069) относятся к рассуждению § 4.2, а не к коду; оговорка о коде стоит на стр. 178–199 и в
   итоговых абзацах не повторена.

2. **После 13.11.2026 о сторонах записи `Distinction` есть теоремы (к стр. 196–199).** Слова «двоичность не
   выведена в коде из записи `Distinction`» остаются верными для типа `Side`. Для самой записи теперь доказано:
   `sides_distinct : forall D, positive D <> negative D`, `sides_not_equivalent`
   (`DistinctionCoDefinition.v:125, :117`; используют оба поля), `binarity_from_codefinition :
   (n <-> ~ p) -> ~ ~ (p \/ n)` (`:193`) — все `Closed under the global context`. Связи между типом `Side` и
   записью `Distinction` в `src` по-прежнему нет. Она возможна без аксиом; проверено (`Check.v`):

   ```coq
   Definition side_holds (D : Distinction) (s : Side) : Prop :=
     match s with Marked => positive D | Unmarked => negative D end.

   Theorem distinction_has_exactly_one_side :
     forall D : Distinction,
       exists s : Side, side_holds D s /\ forall s' : Side, side_holds D s' -> s' = s.

   Theorem side_holds_injective :
     forall (D : Distinction) (s1 s2 : Side), side_holds D s1 = side_holds D s2 -> s1 = s2.
   ```

   Первая теорема: у всякого совершённого различения положена ровно одна сторона типа `Side`; существование
   берётся из поля `exhaustive` ($L3$ записи), единственность — из поля `exclusive` ($L2$ записи). Вторая — из
   `sides_distinct`. Это ровно разделение ролей, которое глава даёт в прозе («$L2$ удерживает стороны
   раздельными, $L3$ исчерпывает рамку»). Функции `Distinction -> Side`, выбирающей положенную сторону, без
   аксиом построить нельзя (поле `exhaustive` — дизъюнкция в `Prop`), поэтому мост записан отношением
   `side_holds`. Если такой файл появится, фразу стр. 196–199 можно будет дополнить ссылкой на него; сейчас она
   точна.

3. **Число в формализации бинарного пути не строится, а берётся готовым (§ 4.4–4.5).** `bit_length (bs :
   BitString) : nat := length bs` отображает запись в тип `nat` стандартной библиотеки; «добавление бита есть
   `S`» — лемма `add_bit_increments_length`, закрываемая `reflexivity`. Глава о построении числа в коде не
   заявляет (её слово — «якорь», стр. 452–465), а о сборке длиной говорит прямо (стр. 704–718). Слова
   «наращивание записи порождает весь натуральный ряд» (стр. 594–596, 636–642) формального двойника в `src` не
   имеют; им отвечает набросок Расхождения 1 (`bit_count_iff_positive`).

4. **«Список различий в третьей деривации не участвует» (стр. 61–63) и `BitString := list Bit`.** На уровне
   файлов независимость есть: `BitString.v` подключает только `Binarity.v` и стандартную библиотеку — ни
   `Distinction.v`, ни `PrimalityOfOne.v`, ни файлы об уровнях. Общим остаётся механизм списка и длины
   (`list`, `length`), и глава называет это сама (стр. 704–718). Расхождения нет.

5. **`two_pow`, `microstates` и «$K$ бит дают $2^K$ исходов» (стр. 368–376, 993–995, строка таблицы 1022).**
   `microstates n := two_pow n`; леммы об «удвоении числа состояний» (`new_dist_doubles`, `pow_double`) суть
   раскрытие определения `two_pow`. Со слоем `BitString` функции не связаны: утверждения «записей длины $K$
   ровно $2^K$» в `src` нет. Глава называет это «заготовками» и «леммами о степенях двойки плюс комментарии»;
   слово «комбинаторные» точнее заменить на «арифметические» — счёта объектов в леммах нет. Связь доказуема без
   аксиом; проверено (`Check.v`, `Closed under the global context`):

   ```coq
   Fixpoint all_bitstrings (K : nat) : list BitString :=
     match K with
     | O => [[]]
     | S K' => map (add_bit Marked) (all_bitstrings K')
               ++ map (add_bit Unmarked) (all_bitstrings K')
     end.

   Theorem bitstrings_of_length_count :
     forall K : nat,
       NoDup (all_bitstrings K) /\
       (forall bs : BitString, In bs (all_bitstrings K) <-> bit_length bs = K) /\
       length (all_bitstrings K) = microstates K.

   Theorem bitstrings_count_is_forced :
     forall (K : nat) (l : list BitString),
       NoDup l -> (forall bs : BitString, In bs l <-> bit_length bs = K) ->
       length l = two_pow K.
   ```

   С такой теоремой развилка § 4.4.3 получила бы обе стороны формально: $K$ = `bit_length`, $2^K$ = число
   записей длины $K$; в доказательстве работают `L2_exclusive` (неповторяемость) и `L3_exhaustive` (полнота).

6. **«Три операции — одна операция `S`», «тождественный ряд» (стр. 566–570, 630–634, 722–738, 759–765).** О
   доказанности в Rocq глава здесь не говорит. В формализации этому отвечают три отдельные леммы с `S` в
   заключении — `add_distinction_increments` (`PrimalityOfOne.v:79`), `level_to_nat_LS` (`LevelNatIso.v:50`),
   `add_bit_increments_length` (`BitString.v:56`), — и то, что все три меры принимают значения в одном типе
   `nat`. Теоремы, сопоставляющей пути между собой, в `src` нет. Что доказуемо о двух путях из трёх
   (`Check.v`): `cardinal_and_binary_counts_coincide : forall n, distinction_count_from_one n <-> (exists bs,
   bs <> [] /\ bit_length bs = n)` — оба предиката равносильны $n \ge 1$. Направление слева направо —
   `Closed under the global context`; справа налево — `Classical_Prop.classic` (свидетель списка различий —
   `distinction_of True`). Начала путей в коде: `one_bit_length` даёт 1; `first_count_is_one` — 1 (цена
   `classic`); у уровней `level_to_nat L1 = 0`, `level_depth L1 = 1` (`LevelNatIso.v:37, :121`) — предмет
   главы II.3.

7. **Индукция «для всякой двоичной записи» без слова «непустой» (стр. 810–815, 823–826, 834–838, 843–847).**
   Формальный принцип главы — для непустых записей (`forall bs, bs <> [] -> P bs`), и раздел «Форма» это
   называет (стр. 866–873). В предшествующей прозе условие опущено, при том что § 4.4.4 признаёт пустую запись
   «полноправным объектом» (стр. 510–512). Без условия принцип неверен; проверено (`Check.v`, `Closed under the
   global context`):

   ```coq
   Theorem induction_from_one_bit_misses_empty :
     ~ (forall P : BitString -> Prop,
          (forall b : Bit, P [b]) ->
          (forall (b : Bit) (bs : BitString), P bs -> P (b :: bs)) ->
          forall bs : BitString, P bs).
   ```

   (свойство «запись непуста» проходит базу и шаг и неверно для `[]`). Достаточно одного слова: «чтобы свойство
   было верно для всякой *непустой* двоичной записи» (стр. 811), «Всякая *непустая* двоичная запись либо есть
   запись в один знак, либо…» (стр. 834).

8. **«Стандартная индукция по `nat` … даёт тот же результат», «один принцип» (стр. 886–889, 893–896).** В `src`
   сопоставления нет. Оно верно в обе стороны; проверено (`Check.v`, обе `Closed under the global context`):
   `nonempty_bitstring_ind_via_nat` (тот же принцип — индукцией по `nat` по длине записи) и
   `nat_ind_from_one_via_bitstrings` (индукция по числам от единицы — из `nonempty_bitstring_ind`).

9. **«Индукция не есть аксиома» (стр. 843, 963–965).** В смысле `Print Assumptions` верно:
   `nonempty_bitstring_ind` — лемма, `Closed under the global context`. Доказана она тактикой `induction bs`, то
   есть принципом, который Rocq порождает вместе с объявлением индуктивного типа `list`: индукция в коде дана
   вместе с типом, а не получена из наращивания записи отдельным выводом. Рассуждение главы («всякая запись и
   состоит из первого бита и добавлений к нему») описывает то же устройство словами.

10. **«`Side` — тип с разрешимым равенством» (стр. 1010).** Верно, но леммы в `src` нет. Проверено (`Check.v`):
    `Lemma Side_eq_dec : forall a b : Side, {a = b} + {a <> b}. Proof. decide equality. Defined.`

11. **Добавление бита справа (стр. 573–575).** В `BitString.v` есть только добавление в голову (`add_bit`).
    Для `bs ++ [b]` леммы нет; факт верен, проверено (`Check.v`): `add_bit_right_increments_length :
    bit_length (bs ++ [b]) = S (bit_length bs)`.

12. **«7 теорем» (стр. 462, 983).** Счёт верен (7 `Qed`, все `Closed under the global context`). Три из семи —
    `reflexivity` на определении (`add_bit_increments_length`, `one_bit_length`, `all_sides_length`), одна —
    пара готовых лемм (`side_is_binary`); формулировки глава приводит дословно, так что о силе этих лемм она не
    говорит больше, чем в них есть.

13. **`positive_nat_is_distinction_count` (стр. 461).** Цена — `Classical_Prop.classic`; заключение
    `distinction_count_from_one n` содержит посылку `1 <= n` конъюнктом и список *любых* различений нужной длины
    (свидетель — $n$ копий `distinction_of True`). Глава II.4 только ссылается на теорему как на параллель; её
    разбор — предмет ведомости главы II.2. Слова «без единой аксиомы» (стр. 462–463) относятся к `BitString.v`
    и к этой теореме не применимы.

14. **Комментарии `Binarity.v` говорят больше главы и кода (к стр. 974–976 и сноске 3).** Шапка файла (`:4`):
    «Binary = derived from distinction. Shannon bit = 1 distinction.»; комментарий `:62`: «Binary code DERIVED
    from L2+L3. Shannon bit = 1 distinction.» В коде `Side` не выводится, а глава различает структурный бит и
    бит Шеннона (стр. 278–290). Шапка не имеет принятого в проекте вида (нет строк Roles и `STATUS`). Это
    замечание к файлу, не к странице; в рамках этой проверки `src` не менялся.

15. **Одноимённые объявления.** `Side` объявлен в шести файлах, `side_binarity` — в двух с разными
    утверждениями (см. Расхождение 2), `L2_exclusive` и `L3_exhaustive` — ещё в `ERRKnowledgeBase.v`. Глава
    везде называет файл, поэтому неоднозначности на странице нет.

## Сводка пробного файла `Check.v`

Подключает `foundation.Distinction`, `foundation.Binarity`, `foundation.BitString`,
`foundation.DistinctionCoDefinition`, `foundation.PrimalityOfOne`, `TheoryOfSystems_Core_ERR`,
`foundation.LevelNatIso`. Строк `Axiom`, `Parameter`, `Admitted` нет.

| утверждение | к какому месту | `Print Assumptions` |
|---|---|---|
| `complete_length_two_is_not_exactly_two` | Расхождение 3 (контрпример) | Closed under the global context |
| `all_sides_nodup`, `side_count_exactly_two` | Расхождение 3 | Closed under the global context |
| `positive_nat_is_bit_count`, `bit_count_iff_positive` | Расхождение 1 | Closed under the global context |
| `positive_bit_count_iff_nonempty`, `one_bit_is_least_positive_count` | § 4.4.4 | Closed under the global context |
| `distinction_has_exactly_one_side`, `side_holds_injective` | сомнительное место 2 | Closed under the global context |
| `bitstrings_of_length_count`, `bitstrings_count_is_forced` | сомнительное место 5 | Closed under the global context |
| `three_successors_one_S` (три готовые леммы рядом) | сомнительное место 6 | Closed under the global context |
| `cardinal_count_gives_bit_count` | сомнительное место 6 | Closed under the global context |
| `cardinal_and_binary_counts_coincide`, `bit_count_gives_distinction_count` | сомнительное место 6 | Axioms: classic : forall P : Prop, P \/ ~ P |
| `induction_from_one_bit_misses_empty` | сомнительное место 7 | Closed under the global context |
| `nonempty_bitstring_ind_via_nat`, `nat_ind_from_one_via_bitstrings` | сомнительное место 8 | Closed under the global context |
| `Side_eq_dec` | сомнительное место 10 | Closed under the global context |
| `add_bit_right_increments_length` | сомнительное место 11 | Closed under the global context |

Аксиома в двух строках таблицы — `Classical_Prop.classic` (в выводе названа коротким именем, модуль подключён);
она приходит из `positive_nat_is_distinction_count`, собственных обращений к ней в пробном файле нет.

Если наброски Расхождений 1 и 3 и сомнительных мест 2 и 5 решено вносить, естественное место — новый файл
`src/foundation/` поверх `BitString.v` (сам `BitString.v` тогда не меняется, и счёт «7 теорем» на странице
остаётся верным); регистрация в `_CoqProject` — добавлением своей строки, по правилу `CLAUDE.md`.
