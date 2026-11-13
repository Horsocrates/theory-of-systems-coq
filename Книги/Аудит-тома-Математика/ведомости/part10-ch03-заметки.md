# Глава X.3 «Сравнение мощностей без выбора: Шрёдер–Бернштейн и теорема Кантора» — заметки к ведомости (12.11.2026)

Ведомость: `part10-ch03.json` — 65 ручных записей, автоматических нет (все имена главы покрыты ручными
записями); `merge --dry` проходит без замечаний, список «без сверки» пуст. Вердикты: ok — 47,
mismatch-statement — 12, mismatch-price — 5, missing-name — 1.

Восемнадцать записей с расхождением относятся к пяти предметам:

| № | предмет | записей | строки |
|---|---|---|---|
| 1 | мост «сюръекция → вложение» назван недоказуемым из `L4_witness` | 9 и 1 общая с № 2 | 23, 29, 109, 111, 116, 120, 142, 157, 166; общая — 146 |
| 2 | «без выбора» у Шрёдера–Бернштейна при цене `L4_witness` | 4 и та же общая | 18, 20, 70, 74; общая — 146 |
| 3 | цена `L3_informative` и два пути `L4_witness` в доказательстве | 2 | 174, 175 |
| 4 | дихотомия цепи описана не так, как в файле | 1 | 61 |
| 5 | сокращённая запись шести имён | 1 | 173 |

Теорема Кантора и предпорядок вложений сверены без расхождений: утверждения общие (произвольный тип),
`Print Assumptions` — `Closed under the global context` у всех одиннадцати лемм (`injects_refl`, `injects_trans`,
`surjects_refl`, `surjects_trans`, `bijects_refl`, `bijects_trans`, `bijects_injects`, `bijects_both`,
`cantor_no_surjection`, `no_maximal_bool_power`, `no_maximal_cardinality`). Цена `Schroeder_Bernstein` и
`cardinal_antisym` — `Classical_Prop.classic` и `ToS_Axioms.L4_witness`, как на странице. Чисел (счёт `Qed`, число
файлов) страница не приводит. Блоков кода на странице нет.

Пробные файлы лежат в `C:/Users/abary/tos-audit-build/_part10/ch03/`: `Check.v`, `CheckSB.v`, `CheckBridge.v`,
`CheckChain.v`. Все четыре собираются; ответы `Print Assumptions` приведены по месту. В `src`, в собранной копии и
на сайте ничего не менялось.

## Что проверить не удалось

- **Недоказуемость.** Что мост «сюръекция → вложение» не выводится из исключённого третьего и определённого
  описания (без полного `L4_witness`) — утверждение о недоказуемости; средствами Rocq оно не проверяется. Проверено
  обратное: из полного `L4_witness` мост выводится (расхождение 1), а Шрёдеру–Бернштейну полного `L4_witness` не
  нужно (расхождение 2).
- **Классические утверждения о выборе** (стр. 9–11, 139–140, 143–144: линейная шкала кардиналов, теорема Цермело,
  трихотомия «требует выбора») компилятором не проверялись. Проверено только, что теоремы о линейности порядка
  `injects` в `src` нет. Выводима ли трихотомия из `classic` + `L4_witness`, не проверялось.
- **«В точности аксиома выбора»** (стр. 24–25, 120) — математическое замечание в разделе сомнительных мест (п. 4);
  равносильность выбору проверена в Rocq для формы «каждая сюръекция имеет правую обратную», для формы
  «существует вложение» не проверялась (в классической теории множеств это открытый вопрос).
- **P1 и степень-как-множество** (стр. 94–97, 143): в трёх файлах главы об этом только комментарий шапки
  `CantorTheoremGeneral.v`; ссылка на P1 и главу 10.1 не сверялась.
- Отсылки к главам 10.1, 10.2, 10.4 не сверялись.
- Английская страница и LaTeX-исходник главы не смотрелись.

Всё остальное проверено по исходнику и компилятору.

## Расхождение 1. Мост «сюръекция → вложение» назван недоказуемым из `L4_witness` (стр. 23–26, 29–30, 109–113, 116–118, 120–122, 142, 146–149, 157–159, 166–169)

**Было:**

> (23–26) И сразу честная оговорка, которую глава доведёт до конца: *обратный* мост — от сюръекции
> $A\twoheadrightarrow B$ к вложению $B\hookrightarrow A$ — это в точности аксиома выбора. В ToS он *не*
> доказывается; именно там, и только там, в теории мощностей живёт выбор.
>
> (109–113) Именно этот обратный мост — *выбрать по одному прообразу для каждого $b\in B$* — и есть аксиома выбора
> (выбор по слоям сюръекции). В ToS он *не* доказывается и честно помечен как граница.[^6] С одним лишь
> `L4_witness` можно обратить *биекцию* (прообразы единственны), но не произвольную сюръекцию (прообразов в слое
> может быть много, и нужен выбор по *всем* слоям сразу).
>
> (116–118) Содержательные результаты главы — предпорядок, антисимметрия, отсутствие максимума — выбора не требуют;
> выбор локализован ровно в одном непроведённом переходе.
>
> (120–122) *Сюръекция-в-инъекцию — это ровно место, где требуется выбор, и ToS его не проводит.*
>
> (142) **Честные границы.** Обратный мост сюръекция${}\to{}$инъекция — сам выбор, не проведён.
>
> (157–159) Аксиома выбора понадобилась бы лишь для обратного моста сюръекция${}\to{}$инъекция и для линейности
> шкалы — и именно их ToS не проводит.

То же — в курсивных итогах на стр. 28–30, 146–149, 166–169.

**Проверка.** `L4_witness` (`src/ToS_Axioms.v:105`):

```coq
Axiom L4_witness : forall (A : Type) (P : A -> Prop), (exists x, P x) -> {x : A | P x}.
```

Условия единственности в нём нет. Единственности требует производная лемма `L4_definite` (`ToS_Axioms.v:135`,
`(exists! x, P x) -> {x | P x}`). В пробном файле `Check.v` доказано:

```coq
Theorem surjection_has_section :
  forall (A B : Type) (f : A -> B),
    (forall b : B, exists a : A, f a = b) ->
    exists g : B -> A, forall b : B, f (g b) = b.
Proof.
  intros A B f Hf.
  exists (fun b => proj1_sig (L4_witness (fun a => f a = b) (Hf b))).
  intro b. exact (proj2_sig (L4_witness (fun a => f a = b) (Hf b))).
Qed.

Theorem surjects_injects_back :
  forall A B : Type, surjects A B -> injects B A.
Proof.
  intros A B [f Hf].
  destruct (surjection_has_section A B f Hf) as [g Hg].
  exists g. intros b1 b2 H.
  rewrite <- (Hg b1), <- (Hg b2), H. reflexivity.
Qed.
```

`Print Assumptions` обеих теорем: `ToS_Axioms.L4_witness` — и только он (без `classic`). Опорная лемма уже есть
в формализации: `l4_statement_gives_functional_choice` (`src/settheory/ChoicePriceMap.v:164`, `Closed under the
global context`) — из утверждения `L4_witness` получается функция выбора по произвольному семейству. Теоремы о
самом мосте в `src` нет (поиск по `surjects`, `injects`: только `CardinalityWithoutChoice.v`).

Шапка `CardinalityWithoutChoice.v` (строки 17–22) говорит то же, что страница: «With only L4_witness one inverts a
BIJECTION (unique preimages), not an arbitrary surjection». Сноска 6 шапку передаёт верно; неверна сама шапка.

**В чём расхождение.** Переход от сюръекции к вложению назван границей, которую ToS не проводит и которую
`L4_witness` провести не может; на деле он выводится из одного `L4_witness` в три строки, и цена его ниже цены
антисимметрии (не нужен `classic`).

**(а) Довести формализацию до слов главы.** Нельзя: утверждение «`L4_witness` не обращает произвольную сюръекцию»
неверно, контр-доказательство приведено выше. Делом можно закрепить ту границу, которая в формализации есть на
самом деле, — между извлечением единственного свидетеля и извлечением произвольного:

1. в `CardinalityWithoutChoice.v` дописать `surjection_has_section` и `surjects_injects_back` (текст выше; цена —
   `L4_witness`) и исправить шапку файла;
2. дописать равносильность «правая обратная ⇔ функциональный выбор» — она закрепляет слова «это и есть выбор по
   слоям сюръекции». Набросок проверен (`CheckBridge.v`), `Print Assumptions` — `Closed under the global context`:

```coq
Definition functional_choice : Prop :=
  forall (I X : Type) (R : I -> X -> Prop),
    (forall i, exists x, R i x) -> exists f : I -> X, forall i, R i (f i).

Definition surjections_split : Prop :=
  forall (A B : Type) (f : A -> B),
    (forall b, exists a, f a = b) -> exists g : B -> A, forall b, f (g b) = b.

Theorem choice_gives_split : functional_choice -> surjections_split.
Proof.
  intros FC A B f Hf.
  exact (FC B A (fun b a => f a = b) Hf).
Qed.

Theorem split_gives_choice : surjections_split -> functional_choice.
Proof.
  intros SS I X R HR.
  pose (S := {p : I * X | R (fst p) (snd p)}).
  pose (pi := fun s : S => fst (proj1_sig s)).
  assert (Hpi : forall i, exists s, pi s = i).
  { intro i. destruct (HR i) as [x Hx].
    exists (exist (fun p : I * X => R (fst p) (snd p)) (i, x) Hx). reflexivity. }
  destruct (SS S I pi Hpi) as [g Hg].
  exists (fun i => snd (proj1_sig (g i))).
  intro i.
  pose proof (proj2_sig (g i)) as H. cbv beta in H.
  pose proof (Hg i) as E. unfold pi in E.
  rewrite E in H. exact H.
Qed.

Theorem split_iff_choice : surjections_split <-> functional_choice.
Proof. split; [apply split_gives_choice | apply choice_gives_split]. Qed.
```

3. дописать Шрёдера–Бернштейна из исключённого третьего и определённого описания (расхождение 2): тогда обе
   стороны границы названы теоремами — антисимметрии хватает единственного свидетеля, мосту нужен произвольный.

**(б) Поправить слова.** Ход мысли главы сохраняется: выбор входит ровно в одном переходе. Меняется одно: переход
не «не проведён», а проводится полной силой L4, которая антисимметрии не нужна.

> (23–26) И сразу честная оговорка, которую глава доведёт до конца: *обратный* мост — от сюръекции
> $A\twoheadrightarrow B$ к вложению $B\hookrightarrow A$ — требует выбрать по прообразу в каждом слое, а прообраз в
> слое не единствен. Шрёдеру–Бернштейну хватает извлечения *единственного* свидетеля; мосту нужен свидетель
> произвольный. Здесь, внутри L4, и проходит в теории мощностей граница выбора: полный `L4_witness` мост проводит,
> а его определённая часть (`L4_definite`), на которой стоит антисимметрия, к слою неприменима.
>
> (28–30) *Мощность — роль-режим сравнения, а не кардинал-число; её упорядочение — правило вложения.
> Антисимметрии (Шрёдер–Бернштейн) хватает исключённого третьего и единственного свидетеля; отсутствие максимума
> (Кантор) обходится без допущений; выбор по семейству входит в одном переходе — сюръекция в инъекцию, — и цена
> этого перехода есть полный `L4_witness`.*
>
> (109–113) Именно этот обратный мост — *выбрать по одному прообразу для каждого $b\in B$* — и есть выбор по слоям
> сюръекции: утверждение «каждая сюръекция имеет правую обратную» равносильно функциональному выбору по
> семейству.[^6] Определённое описание (`L4_definite`), которым обходится антисимметрия, здесь неприменимо:
> прообразов в слое может быть много. Полный `L4_witness` условия единственности не ставит; применённый к каждому
> слою, он даёт правую обратную, а она инъективна. Мост, таким образом, в ToS проводится — ценой `L4_witness`,
> взятого в полную силу.
>
> (115–118) Вот почему антисимметрия $\le$ опирается на Шрёдер–Бернштейна (L3${}+{}$L4), а не на выбор по
> семейству: она работает с *инъекциями*, где обратный частичный однозначен. Содержательные результаты главы —
> предпорядок, антисимметрия, отсутствие максимума — выбора по семейству не требуют; он входит ровно в одном
> переходе, и входит через полную силу L4.
>
> (120–122) *Сюръекция-в-инъекцию — это ровно место, где требуется выбор по семейству; ToS проводит его ценой
> полного `L4_witness`. Антисимметрия живёт на инъекциях (там L4 обращает единственное), а не на слоях сюръекции
> (там L4 выбирает из многих).*
>
> (142) **Честные границы.** Обратный мост сюръекция${}\to{}$инъекция — выбор по слоям; его цена — полный
> `L4_witness`, и антисимметрии эта цена не нужна.
>
> (146–149) *Сравнение мощностей — предпорядок ролей; антисимметрии (Шрёдер–Бернштейн) хватает исключённого
> третьего и единственного свидетеля, отсутствие максимума (Кантор) обходится без допущений; выбор по семейству
> входит в переходе от сюръекции к инъекции (цена — полный `L4_witness`); линейность шкалы здесь не утверждается.*
>
> (157–159) Выбор по семейству понадобился лишь для обратного моста сюръекция${}\to{}$инъекция — там он оплачен
> полным `L4_witness`; линейность шкалы ToS не утверждает.
>
> (166–169) *Мощность есть роль в предпорядке вложений, а не кардинал-число; антисимметрии хватает единственного
> свидетеля, отсутствие максимума доказуемо без допущений. Выбор не исчезает — он точно локализуется: в переходе от
> сюръекции к инъекции, где L4 берётся в полную силу, и в линейности кардинальной шкалы, которую ToS оставляет
> непроведённой.*

Сноска 6 — если теоремы пункта (а) дописаны:

> [^6]: `surjects_injects_back` (`CardinalityWithoutChoice.v`): `surjects A B -> injects B A`; `Print Assumptions`
> — один `L4_witness`. Равносильность правой обратной и функционального выбора — `split_iff_choice`, 0 аксиом. Тот
> же ход для произвольного семейства — `l4_statement_gives_functional_choice` (`settheory/ChoicePriceMap.v`).

Сноска 6 — если формализацию не трогать:

> [^6]: В `CardinalityWithoutChoice.v` переход `surjects` $\to$ `injects` обратного направления отдельной теоремой
> не записан. Из `L4_witness` он следует: `l4_statement_gives_functional_choice` (`settheory/ChoicePriceMap.v`,
> 0 аксиом) даёт функцию выбора по слоям.

Слова «антисимметрии хватает исключённого третьего и единственного свидетеля» в этих текстах опираются на
расхождение 2, пункт (а): в `src` такой теоремы пока нет, набросок проверен.

## Расхождение 2. «Без выбора» у Шрёдера–Бернштейна при цене `L4_witness` (стр. 18–20, 70–71, 74–75; заголовок главы)

**Было:**

> (18–20) Глава держится на двух столпах, оба — *без аксиомы выбора*:
> - **Шрёдер–Бернштейн**: … Это делает предпорядок вложений *антисимметричным* с точностью до биекции — и
>   доказывается без выбора, ценою L3 и L4 (не 0 аксиом), на конечной глубине цепи.
>
> (70–71) Поэтому фундаментальная теорема о мощностях держится без выбора.
>
> (74–75) Завершённая цепь заменена конечной глубиной (P4); цена — L3${}+{}$L4, не выбор.*

**Проверка.** `Print Assumptions cardinal_antisym` и `Print Assumptions Schroeder_Bernstein`:

```
Axioms:
Classical_Prop.classic : forall P : Prop, P \/ ~ P
ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A | P x}
```

Слова «ценою L3 и L4» верны. Но `L4_witness` — допущение, из которого выбор по семейству следует:
`l4_statement_gives_functional_choice` (`ChoicePriceMap.v:164`) и пробная `surjection_has_section` (расхождение 1).
Шапка `ChoicePriceMap.v` это уже записывает (строки 28–31): `So PL4 and PL3_L4 are NOT «below full AC»: whatever
rests on L4_witness rests on a principle from which choice over families follows`; и (строки 42–44): прежний тезис
снят во второй половине — `Schroeder–Bernstein, cardinal antisymmetry and the closed-set dichotomy rest on
L4_witness`. Страница на стр. 69–70 сама оговаривает «choice-подобную силу» и добавляет, что «завершённого графа
выбора теорема не требует»; теоремы, которая бы это показывала, в `src` нет.

Содержательно оговорка страницы верна, и это проверено: в пробном файле `CheckSB.v` теорема Шрёдера–Бернштейна
доказана из двух посылок-утверждений — исключённого третьего и определённого описания (извлечение *единственного*
свидетеля), без `L4_witness`:

```coq
Schroeder_Bernstein_definite
     : (forall P : Prop, P \/ ~ P) ->
       (forall (T : Type) (P : T -> Prop), (exists ! x : T, P x) -> {x : T | P x}) ->
       forall (A B : Type) (f : A -> B) (g : B -> A),
       (forall a1 a2 : A, f a1 = f a2 -> a1 = a2) ->
       (forall b1 b2 : B, g b1 = g b2 -> b1 = b2) ->
       exists h : A -> B,
         (forall a1 a2 : A, h a1 = h a2 -> a1 = a2) /\
         (forall b : B, exists a : A, h a = b)
```

`Print Assumptions Schroeder_Bernstein_definite`: `Closed under the global context`.

**В чём расхождение.** Компилятор называет ценой теоремы допущение, из которого выбор по семейству выводится;
слова «без выбора» вывод компилятора не подтверждает. Доказательство полной силой `L4_witness` не пользуется, но
в формализации это не записано теоремой.

**(а) Довести формализацию.** Возможно, без новых допущений; набросок проверен (`CheckSB.v`). Доказательство
повторяет `SchroederBernstein_ERR.v` (строки 113–351) с двумя заменами: вместо `L4_definite` — посылка `DD`,
вместо `L3_informative` — лемма `em_inf`, выведенная из `EM` и `DD` (свидетель-бит единствен):

```coq
Section SB_definite.

Variable EM : forall P : Prop, P \/ ~ P.
Variable DD : forall (T : Type) (P : T -> Prop), (exists! x, P x) -> {x : T | P x}.

Lemma em_inf : forall P : Prop, {P} + {~ P}.
Proof.
  intro P.
  assert (Hex : exists! b : bool, if b then P else ~ P).
  { destruct (EM P) as [HP | HnP].
    - exists true. split; [exact HP |].
      intros [|] Hb; [reflexivity | exfalso; exact (Hb HP)].
    - exists false. split; [exact HnP |].
      intros [|] Hb; [exfalso; exact (HnP Hb) | reflexivity]. }
  destruct (DD bool _ Hex) as [b Hb].
  destruct b; [left | right]; exact Hb.
Defined.

Variables A B : Type.
Variable f : A -> B.
Variable g : B -> A.
Hypothesis f_inj : forall a1 a2, f a1 = f a2 -> a1 = a2.
Hypothesis g_inj : forall b1 b2, g b1 = g b2 -> b1 = b2.

(* g_preimage_unique — как в SchroederBernstein_ERR.v *)

Definition g_inv (a : A) (H : exists b, g b = a) : B :=
  proj1_sig (DD B (fun b => g b = a) (g_preimage_unique a H)).

(* … B_rooted_depth, B_rooted, леммы о глубине, h (с em_inf на месте L3_informative),
   h_injective, h_surjective — как в SchroederBernstein_ERR.v; полный текст в CheckSB.v … *)

Theorem Schroeder_Bernstein_definite : exists h : A -> B,
  (forall a1 a2, h a1 = h a2 -> a1 = a2) /\
  (forall b, exists a, h a = b).
Proof. exists h. split; [exact h_injective | exact h_surjective]. Qed.

End SB_definite.
```

Новую теорему можно положить отдельным файлом (тогда `SchroederBernstein_ERR.v` не меняется) либо перестроить на
неё сам `SchroederBernstein_ERR.v`: прежняя теорема получается подстановкой `classic` и `L4_definite`, её запись
и цена остаются прежними (проверено там же под именем `Schroeder_Bernstein_again`; `Print Assumptions` — `classic`
и `L4_witness`). От `SchroederBernstein_ERR.v` в `src` зависит один файл — `CardinalityWithoutChoice.v`.

```coq
Theorem Schroeder_Bernstein_again :
  forall (A B : Type) (f : A -> B) (g : B -> A),
    (forall a1 a2 : A, f a1 = f a2 -> a1 = a2) ->
    (forall b1 b2 : B, g b1 = g b2 -> b1 = b2) ->
    exists h : A -> B,
      (forall a1 a2 : A, h a1 = h a2 -> a1 = a2) /\
      (forall b : B, exists a : A, h a = b).
Proof. exact (Schroeder_Bernstein_definite classic (@L4_definite)). Qed.

Theorem cardinal_antisym_definite :
  (forall P : Prop, P \/ ~ P) ->
  (forall (T : Type) (P : T -> Prop), (exists! x, P x) -> {x : T | P x}) ->
  forall A B : Type, injects A B -> injects B A -> bijects A B.
Proof.
  intros EM DD A B [f Hf] [g Hg].
  destruct (Schroeder_Bernstein_definite EM DD A B f g Hf Hg) as [h [hi hs]].
  exists h. split; [exact hi | exact hs].
Qed.
```

`Print Assumptions cardinal_antisym_definite`: `Closed under the global context`.

После этого слова главы «без выбора» опираются на теорему: антисимметрия следует из исключённого третьего и
извлечения единственного свидетеля; извлечение произвольного свидетеля (то, что даёт выбор по семейству) в
посылки не входит. К сноске 3 тогда добавляется фраза:

> Что полная сила `L4_witness` доказательству не нужна, закреплено теоремой `Schroeder_Bernstein_definite`: то же
> заключение из двух посылок — исключённого третьего и определённого описания; `Print Assumptions` — 0 аксиом.

**(б) Поправить слова** (если формализацию не трогать):

> (18) Глава держится на двух столпах; выбор по семейству не используется ни в одном:
>
> (20) … Это делает предпорядок вложений *антисимметричным* с точностью до биекции — и доказывается ценою L3 и L4
> (не 0 аксиом), причём L4 применяется только к единственному свидетелю, на конечной глубине цепи.
>
> (70–71) Поэтому фундаментальная теорема о мощностях выбором по семейству не пользуется, хотя допущение, на
> которое она записана, — `L4_witness` — такой выбор даёт.
>
> (74–75) Завершённая цепь заменена конечной глубиной (P4); цена — L3${}+{}$L4, причём L4 — только для
> единственного свидетеля.*

Заголовок главы («Сравнение мощностей без выбора») при пути (а) остаётся верным; при пути (б) его стоит
согласовать с принятой формулой.

## Расхождение 3. Цена `L3_informative` и два пути `L4_witness` в доказательстве (стр. 174, 175)

**Было:**

> (174) Глубина цепи — `nat`; признак `B_rooted` решается через `L3_informative` (информативное исключённое
> третье) — это и есть цена L3.
>
> (175) В самом доказательстве `L4_witness` применяется через производную лемму определённого описания
> `L4_definite` (CDD), извлекающую *единственный* частичный прообраз из $\exists!$ — именно так помечает технику
> шапка файла.

**Проверка.** `L3_informative` (`src/ToS_Axioms.v:119`): `forall P : Prop, {P} + {~P}`. `Print Assumptions`:

```
Axioms:
Classical_Prop.classic : forall P : Prop, P \/ ~ P
ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A | P x}
```

Её доказательство (`ToS_Axioms.v:120–130`) применяет `L4_witness` напрямую к `exists b : bool, if b then P else
~P` (строка 126); комментарий над леммой говорит то же: «Follows from L3 … + L4 (extract witness)». В
`SchroederBernstein_ERR.v` лемма `L3_informative` стоит в определении `h` (строка 274) и в доказательствах
`h_injective` (287, 288) и `h_surjective` (328, 333, 340, 344). `L4_definite` применяется в `g_inv` (строка 84);
`f_inv` (строка 80) определён и в доказательстве теоремы не используется.

**В чём расхождение.** Информативная разрешимость признака стоит L3 и L4, а не одного L3; `L4_witness` входит в
доказательство двумя путями — через `L4_definite` и через `L3_informative`, — а страница называет один.

**(а) Довести формализацию.** Возможны два пути, оба без новых допущений.

- Вывести `L3_informative` через `L4_definite` (свидетель-бит единствен; доказательство — лемма `em_inf` из
  `CheckSB.v`, приведена в расхождении 2, с `L4_definite` на месте `DD`). Тогда фраза сноски 3 становится точной:
  все применения `L4_witness` в доказательстве идут через `L4_definite`. Утверждение леммы и вывод `Print
  Assumptions` не меняются; правка касается `ToS_Axioms.v`, после неё нужна полная пересборка.
- Принять путь (а) расхождения 2: `Schroeder_Bernstein_definite` закрепляет то же самое теоремой и `ToS_Axioms.v`
  не затрагивает.

Цена `L3_informative` при любом пути остаётся `classic` + `L4_witness`; фразу сноски 2 «это и есть цена L3»
делом не довести — правятся слова.

**(б) Поправить слова:**

> (174) Глубина цепи — `nat`; признак `B_rooted` решается через `L3_informative` (информативное исключённое
> третье, `{P} + {~P}`) — здесь входит L3. Сама `L3_informative` стоит L3${}+{}$L4: дизъюнкцию `classic` в выбор
> ветви превращает `L4_witness`.
>
> (175) В самом доказательстве `L4_witness` применяется дважды: через производную лемму определённого описания
> `L4_definite` (CDD), извлекающую *единственный* частичный прообраз из $\exists!$, — именно так помечает технику
> шапка файла, — и внутри `L3_informative`, где он извлекает бит-ответ, тоже единственный.

На стр. 69 («L3 входит как разрешимость признака укоренённости») правка не обязательна; точнее было бы «L3 входит
как разрешимость признака укоренённости (в информативной форме — вместе с L4)».

## Расхождение 4. Дихотомия цепи описана не так, как в файле (стр. 61–64)

**Было:**

> ToS заменяет завершённую бесконечную цепь *конечной глубиной* — натуральным числом: каждая точка либо укоренена
> на конечной глубине (доходит до точки без прообраза за конечное число шагов), либо принадлежит
> двусторонне-бесконечной цепи.

**Проверка.** В `SchroederBernstein_ERR.v` определён один признак — укоренённость в $B$:

```coq
Inductive B_rooted_depth : nat -> A -> Prop :=
  | B_rooted_depth_0 : forall a b, g b = a -> no_f_preimage b -> B_rooted_depth 0 a
  | B_rooted_depth_S : forall n a b a',
      g b = a -> f a' = b -> B_rooted_depth n a' -> B_rooted_depth (S n) a.

Definition B_rooted (a : A) : Prop := exists n, B_rooted_depth n a.
```

Функция `h` (строка 273) разбирает два случая: `B_rooted a` и его отрицание. Под отрицание попадают и точки, чья
цепь назад обрывается в $A$ (на точке без $g$-прообраза — тоже за конечное число шагов), и точки, чья цепь не
обрывается. Укоренённость в $A$ в файле не определена (`no_g_preimage`, строка 114, объявлено и не используется);
понятия «двусторонне-бесконечная цепь» и утверждения о дихотомии в файле нет. Следующая фраза страницы («на
укоренённых в $B$ точках берём частичный обратный $g^{-1}$, иначе — $f$») исходнику соответствует.

**В чём расхождение.** Страница делит точки на «укоренённые на конечной глубине» и «лежащие в
двусторонне-бесконечной цепи»; в файле деление другое — «укоренённые в $B$» и «все остальные», причём среди
остальных есть точки с конечной глубиной (укоренённые в $A$).

**(а) Довести формализацию.** Возможно, ценой `classic`: трихотомия цепи. Набросок проверен (`CheckChain.v`);
`Print Assumptions chain_trichotomy` — `classic : forall P : Prop, P \/ ~ P` (без `L4_witness`); связь с признаком
файла `B_rooted_iff_B_stops` — `Closed under the global context`.

```coq
(* a'' получается из a за n полных шагов назад: a = g b, b = f a', ... *)
Inductive back : nat -> A -> A -> Prop :=
  | back_0 : forall a, back 0 a a
  | back_S : forall n a b a' a'',
      g b = a -> f a' = b -> back n a' a'' -> back (S n) a a''.

Definition A_stops (a : A) : Prop :=
  exists n a', back n a a' /\ ~ (exists b, g b = a').

Definition never_stops (a : A) : Prop :=
  forall n, exists a', back n a a'.

Theorem chain_trichotomy :
  forall a : A, B_rooted f g a \/ A_stops a \/ never_stops a.
Proof.
  intro a.
  destruct (classic (B_rooted f g a)) as [HB | HnB]; [left; exact HB |].
  destruct (classic (A_stops a)) as [HA | HnA]; [right; left; exact HA |].
  right; right. intro n. induction n as [| n [a' Hb]].
  - exists a. apply back_0.
  - destruct (classic (exists b, g b = a')) as [[b Hgb] | Hno].
    + destruct (classic (exists a'', f a'' = b)) as [[a'' Hfa] | Hnf].
      * exists a''. apply back_extend with a' b; assumption.
      * exfalso. apply HnB. apply B_rooted_iff_B_stops.
        exists n, a', b. split; [exact Hb | split; [exact Hgb | exact Hnf]].
    + exfalso. apply HnA. exists n, a'. split; assumption.
Qed.
```

(Вспомогательные `back_extend`, `B_rooted_depth_back`, `back_B_rooted_depth`, `B_rooted_iff_B_stops` — в
`CheckChain.v`.) Третий случай — «на любой глубине есть шаг назад» — и есть точная форма слов «цепь не
обрывается»; циклические цепи входят в него же.

**(б) Поправить слова:**

> ToS заменяет завершённую бесконечную цепь *конечной глубиной* — натуральным числом: точка либо укоренена в $B$
> на конечной глубине (её цепь, прослеженная назад, за конечное число шагов доходит до точки $B$ без прообраза),
> либо нет — тогда её цепь обрывается в $A$ или не обрывается вовсе.

## Расхождение 5. Сокращённая запись шести имён (стр. 173)

**Было:** «`surjects_refl/_trans`, `bijects_refl/_trans/_injects/_both` — все **0 аксиом**».

**Проверка.** Объявлений `surjects_refl/_trans` и `bijects_refl/_trans/_injects/_both` нет; это сокращение шести
имён, каждое из которых существует в `CardinalityWithoutChoice.v`: `surjects_refl` (54), `surjects_trans` (57),
`bijects_refl` (67), `bijects_trans` (74), `bijects_injects` (85), `bijects_both` (88). У всех шести `Print
Assumptions` — `Closed under the global context`; слова «0 аксиом» верны.

(а) Не требуется. (б) «стало»:

> [^1]: В `settheory/CardinalityWithoutChoice.v` (эта работа): `injects`, `surjects`, `bijects`; `injects_refl`,
> `injects_trans` (предпорядок $\le$), `surjects_refl`, `surjects_trans`, `bijects_refl`, `bijects_trans`,
> `bijects_injects`, `bijects_both` — все **0 аксиом**.

## Сомнительные места, расхождением не являющиеся

**1. «Максимальной мощности нет» и порядок вложений (стр. 21, 86–91, 99–101, 117, 128, 136, 146–148, 156–157).**
Глава определяет мощность как позицию в предпорядке *вложений* (стр. 14–16), а теорема `no_maximal_cardinality`
говорит о *сюръекциях*: `forall X, ~ surjects X (X -> bool)`. Страница это оговаривает прямо (стр. 88–91: «не
строгость в инъекционном порядке»), поэтому записи стоят с вердиктом ok. Оговорку можно снять делом — ценой главы
(L3 + L4). Набросок проверен (`Check.v`), `Print Assumptions` всех трёх теорем — `classic` и `L4_witness`:

```coq
Theorem injects_into_bool_power : forall X : Type, injects X (X -> bool).
Proof.
  intro X.
  exists (fun x y => if L3_informative (x = y) then true else false).
  intros x1 x2 H.
  assert (H1 : (if L3_informative (x1 = x1) then true else false)
             = (if L3_informative (x2 = x1) then true else false)).
  { exact (f_equal (fun p : X -> bool => p x1) H). }
  destruct (L3_informative (x1 = x1)) as [_ | Hn].
  - destruct (L3_informative (x2 = x1)) as [E | _].
    + symmetry. exact E.
    + discriminate H1.
  - exfalso. apply Hn. reflexivity.
Qed.

Theorem bool_power_not_injects_back :
  forall X : Type, ~ injects (X -> bool) X.
Proof.
  intros X Hback.
  destruct (cardinal_antisym X (X -> bool) (injects_into_bool_power X) Hback)
    as [h [_ hs]].
  apply (no_maximal_cardinality X). exists h. exact hs.
Qed.

Theorem no_maximal_in_injection_order :
  forall X : Type, exists Y : Type, injects X Y /\ ~ injects Y X.
Proof.
  intro X. exists (X -> bool). split.
  - apply injects_into_bool_power.
  - apply bool_power_not_injects_back.
Qed.
```

С этими теоремами «максимальной мощности нет» верно в том самом порядке, которым глава определяет мощность: над
каждым носителем есть строго больший. Цена — L3 + L4 (а не 0 аксиом); сюръективная форма остаётся без допущений.

**2. Равенство функций в `surjective`; предикаты со значениями в `Prop` (стр. 79–84, 93–95, 176).** В
`surjective f := forall g, exists a, f a = g` стоит равенство функций, а не совпадение значений в каждой точке.
Посылка от этого сильнее, теорема слабее: поточечная форма — «нет $f$, у которой каждая $g$ поточечно совпадает с
какой-то строкой» — в файле не записана, хотя доказательство файла по существу поточечное
(`diagonal_differs_at_point`). Слова страницы утверждению в Rocq соответствуют. Обе усиленные формы проверены
(`Check.v`), `Print Assumptions` — `Closed under the global context`:

```coq
Theorem cantor_no_pointwise_surjection :
  forall (X : Type) (f : X -> (X -> bool)),
    ~ (forall g : X -> bool, exists a : X, forall x : X, f a x = g x).
Proof.
  intros X f H.
  destruct (H (fun x => negb (f x x))) as [a Ha].
  exact (no_bool_fixpoint (f a a) (Ha a)).
Qed.

Theorem cantor_no_pointwise_surjection_Prop :
  forall (X : Type) (f : X -> (X -> Prop)),
    ~ (forall g : X -> Prop, exists a : X, forall x : X, f a x <-> g x).
Proof.
  intros X f H.
  destruct (H (fun x => ~ f x x)) as [a Ha].
  destruct (Ha a) as [H1 H2].
  assert (Hn : ~ f a a). { intro Hf. exact (H1 Hf Hf). }
  exact (Hn (H2 Hn)).
Qed.
```

Вторая теорема — о всех предикатах `X -> Prop`, а не только о разрешимых (`X -> bool`); она ближе к словам «нет
накрытия своей степени» и тоже не требует допущений.

**3. Симметрия равномощности (стр. 16, 44, 48, 51–53).** Для `bijects` в файле доказаны рефлексивность и
транзитивность; симметрии (`bijects A B -> bijects B A`) и вложения в обратную сторону нет. Страница симметрии не
утверждает, но слова «равномощны», «совпадение ролей» её подразумевают. Для симметрии нужна обратная функция, то
есть извлечение единственного прообраза; ценой `L4_witness` через `L4_definite` она доказана в `Check.v`
(`bijects_sym`, `Print Assumptions` — `ToS_Axioms.L4_witness`). Это же подтверждает слова стр. 111 «с одним лишь
`L4_witness` можно обратить биекцию». Можно ли доказать симметрию вовсе без допущений, не проверялось.

**4. «В точности аксиома выбора» (стр. 24–25, 120).** Равносильна выбору форма «каждая сюръекция имеет правую
обратную» (в Rocq: `split_iff_choice`, `CheckBridge.v`, без допущений). Более слабая форма — «если есть сюръекция
$A$ на $B$, то есть вложение $B$ в $A$» — в классической теории множеств называется принципом разбиения; из
аксиомы выбора он следует, а следует ли из него аксиома выбора в ZF — открытый вопрос. Слова «в точности», «ровно»
точны для первой формы (так сказано на стр. 109–110) и неточны для второй (стр. 24–25). Замечание
математическое, компилятором не проверялось; в текстах «стало» расхождения 1 оно учтено.

**5. Степень-как-множество и P1 (стр. 94–97, 143).** В файлах главы это комментарий шапки
`CantorTheoremGeneral.v` (строки 14–16), теоремы нет; страница на теорему и не ссылается. В реестре
`ChoicePriceMap.v` строка `RPowerSetObject => PBoundary` — запись таблицы («not constructed»), а не доказанное
свойство; глава X.3 на реестр не ссылается.

**6. Реестр цен.** Строки `ChoicePriceMap.v`, относящиеся к теоремам главы, с компилятором согласны:
`RCantorGeneral` — `PZero` (`cantor_no_surjection`, `no_maximal_bool_power`, `no_maximal_cardinality`: closed);
`RSchroederBernstein`, `RCardinalAntisym` — `PL3_L4` (`classic` + `L4_witness`).

**7. Вне страницы: шапки и неиспользуемые объявления.** Шапка `SchroederBernstein_ERR.v` называет 14 Qed, в файле
16; там же «NO epsilon», тогда как из `classic` и `L4_witness` эпсилон Гильберта выводится
(`l3_l4_statements_give_epsilon`, `ChoicePriceMap.v:175`). Переменные секции `inhA`, `inhB` (строки 49–50) и
объявления `f_inv`, `f_inv_spec`, `f_preimage_unique`, `no_g_preimage` в доказательстве теоремы не участвуют.
Шапка `CardinalityWithoutChoice.v` (строки 17–22) содержит опровергнутую фразу о `L4_witness` (расхождение 1).
Страница этих мест не цитирует; правка — вместе с правкой формализации.
