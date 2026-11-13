# Глава X.6 «Синтез Части X: что доказуемо без выбора, и карта границ» — заметки к ведомости (12.11.2026)

Ведомость: `part10-ch06.json` — 96 ручных записей + 9 автоматических; `merge --dry` проходит без замечаний, список
«без сверки» пуст. Вердикты ручных записей: ok — 56, mismatch-statement — 25, mismatch-price — 9, wrong-number — 4,
missing-name — 2 (с автоматическими: ok — 65).

Сорок записей с расхождением относятся к пятнадцати местам (расхождения 1–15).

Пробные файлы лежат в `C:/Users/abary/tos-audit-build/_part10/ch06/`: `CheckDickson.v`, `CheckSB.v`, `CheckBridge.v`,
`CheckRegistry.v`, `CheckCB.v`, `CheckGameTree.v`, `CheckZermelo.v`, `CheckKruskal.v`. Все восемь собираются; ответы
`Print Assumptions` приведены по месту. В `src`, в собранной копии и на сайте ничего не менялось.

## Что проверить не удалось

- «Линейность кардинальной шкалы (трихотомия мощностей, тоже выбор)» (стр. 84) и «трансфинитная рекурсия за пределами
  конструктивных нотаций» (стр. 84–85): в формализации таких утверждений нет; выводима ли трихотомия из `classic` и
  `L4_witness`, не проверялось.
- «Степенное множество $\mathcal{P}(X)$ как завершённый Элемент (P1)» (стр. 91–92): имени в главе нет; теоремы с такой
  формулировкой поиском по `src` не найдено. Ближайшие — `russell_paradox_blocked` и `P1_no_self_membership`
  (`TheoryOfSystems_Core_ERR.v:248, 126`, обе Closed); их сверка — предмет главы X.1.
- Формулировки теорем глав X.1–X.5, на которые глава ссылается обзорно (`P4_eliminates_ATR0`, `P4_eliminates_Infinity`,
  `P4_eliminates_Pi11`, ординалы, `Schroeder_Bernstein`, трисекция), здесь сверены по цене; по формулировке — в
  ведомостях своих глав. Исключение — `P4ProhibitsImpredicative.v` и `P4ProhibitsAC.v`: прочитаны целиком (расхождение
  13, запись строки 90).
- Лемма Хигмана для двухбуквенного алфавита и для алфавита ℕ (расхождение 7): доказательство не пробовалось.
- Что теорему Шрёдера — Бернштейна нельзя получить в Rocq на одном `classic`, без извлечения свидетеля, — рассуждение
  (функция $A\to B$ строится разбором случаев по высказыванию из `Prop`), компилятором оно не проверяется.
- Контрпример к «ω-предел — совершенное ядро» (расхождение 10) — математическое рассуждение, не формализован.
- Файлы, на которые ссылается только шапка `FormerWallsLedger.v` (`DeterminacyAscent.v`, `WqoProcessDecidable.v`,
  `ProcessHierarchy*.v`), просмотрены, построчно не сверялись: на странице они не названы.
- Английская страница и LaTeX-исходник главы не смотрелись.

Всё остальное проверено по исходнику и компилятору.

## Сверка реестра `settheory/ChoicePriceMap.v` с компилятором — построчно

Функция `price` (`ChoicePriceMap.v:110`) задана на 18 именах. Опорные теоремы взяты из комментария реестра (стр. 81–109
файла); вывод `Print Assumptions` — дословно.

| строка реестра | ярус в реестре | опорная теорема (файл:строка) | `Print Assumptions` | итог |
|---|---|---|---|---|
| `RCantorGeneral` | `PZero` | `cantor_no_surjection` (`CantorTheoremGeneral.v:55`), `no_maximal_bool_power` (:75), `no_maximal_cardinality` (`CardinalityWithoutChoice.v:108`) | Closed under the global context | согласовано |
| `RCountabilityQ` | `PZero` | `Q_countable` (`Countability_Q.v:610`), `Q_bijection` (:759) | Closed | согласовано |
| `RDiagonal` | `PZero` | `binary_processes_not_enumerable` (`ProcessDiagonal.v:108`) | Closed | согласовано |
| `RCantorBendixson` | `PZero` | `S_finite_scattered` (`CantorBendixsonFull.v:344`), `CB_omega_accumulation_in_parent` (:413); все 23 леммы файла | Closed | согласовано |
| `RTransfiniteLevel` | `PZero` | `no_universal_level` (`TransfiniteInductionLevel.v:72`) | Closed | согласовано |
| `RFiniteChoice` | `PZero` | в комментарии не названа | — | опоры нет; подходят `finite_choice` (`P4_Eliminates_AC.v:47`), `finite_choice_works` (`P4ProhibitsAC.v:171`) — обе Closed |
| `RShrinkingIntervals` | `PZero` | `unit_interval_uncountable_trisect_v2` (`ShrinkingIntervals_ERR.v:3569`) | Closed | согласовано |
| `RKruskalFamilies` | `PZero` | `kruskal_chains`, `kruskal_forks` (`KruskalTree.v:265, 276`), `depth1_wqo`, `L5_from_kruskal` (`KruskalFull.v:129, 166`) | Closed | согласовано |
| `RACOnNat` | `PZero` | `ac_on_nat_free` (`ChoicePriceMap.v:198`) | Closed | согласовано |
| `RHigman` | `PL3` | `higman_synthesis` (`HigmanLemma.v:169`) | `Classical_Prop.classic` | согласовано; `higman_unit` (:158) — Closed, `classic` входит только через `dickson_pair` (:103) — см. расхождение 6 |
| `RFiniteDeterminacy` | `PL3` | `weak_determinacy` (`BorelDeterminacy.v:154`) | `BorelDeterminacy.classic` | согласовано по цене; о формулировке — расхождение 8 |
| `RFunctionalChoice` | `PL4` | `l4_statement_gives_functional_choice` (`ChoicePriceMap.v:164`) | Closed | по правилу реестра («ярус = вывод `Print Assumptions`») у названной леммы ярус `PZero`: L4 взят посылкой. Теоремы, доказанной от самой аксиомы, в `src` нет; в `CheckRegistry.v` она есть (`functional_choice_from_L4_axiom`, в выводе компилятора только `L4_witness`) |
| `RSchroederBernstein` | `PL3_L4` | `Schroeder_Bernstein` (`SchroederBernstein_ERR.v:357`) | `Classical_Prop.classic`, `ToS_Axioms.L4_witness` | согласовано |
| `RCardinalAntisym` | `PL3_L4` | `cardinal_antisym` (`CardinalityWithoutChoice.v:98`) | `Classical_Prop.classic`, `ToS_Axioms.L4_witness` | согласовано |
| `RContinuumHypothesis` | `PL3_L4` | `process_continuum_hypothesis` (`ProcessContinuumHypothesis.v:620`) | `Classical_Prop.classic`, `ToS_Axioms.L4_witness` | согласовано |
| `RPowerSetObject`, `RFullKruskal`, `RBorelDeterminacy` | `PBoundary` | «not constructed» | — | теорем нет, как и сказано; `kruskal_full_statement` (`KruskalFull.v:158`) — определение без доказательства |

Итог: из пятнадцати строк ниже границы тринадцать согласованы с компилятором; у одной (`RFiniteChoice`) опорная
теорема не названа; у одной (`RFunctionalChoice`) ярус относится к следствию аксиомы, а названная лемма замкнута.
Все 17 лемм самого файла — Closed.

## Сверка таблицы страницы (стр. 56–60) с компилятором и реестром

| строка страницы | что названо | компилятор | в реестре |
|---|---|---|---|
| 56, «0 аксиом» | счётность ℚ; `diagonal_differs`; трисекция; общий Кантор; Кантор–Бендиксон; Крускал | Closed | есть, `PZero` |
| 56, «0 аксиом» | ординалы, $\varepsilon_0$, `wf_ord_lt`, `transfinite_ind` | Closed | строки нет |
| 56, «0 аксиом» | уровневая индукция | `level_strong_induction` — Closed | `RTransfiniteLevel`, `PZero` |
| 56, «0 аксиом» | «`P4_Eliminates`/`Prohibits`-кластер» | все леммы семи файлов — Closed | строки нет |
| 57, «classic (L3)» | Хигман | `higman_synthesis` — `Classical_Prop.classic`; `higman_unit` — Closed | `RHigman`, `PL3` |
| 57, «classic (L3)» | конечная детерминированность | `weak_determinacy`, `zero_game_determined` — `BorelDeterminacy.classic` | `RFiniteDeterminacy`, `PL3` |
| 58, «classic + L4» | Шрёдер–Бернштейн; `cardinal_antisym` | `Classical_Prop.classic`, `ToS_Axioms.L4_witness` | `PL3_L4` |
| 59, «вычислительный примитив» | $\Pi^1_1$-переинтерпретация | `P4_eliminates_Pi11` — только `P4_Eliminates_Pi11.eval_program`; `pi11_negation` — ещё `Classical_Prop.classic` | строки и яруса нет |
| 60, «Граница» | завершённый объект; полный Крускал; Борель | теорем нет | `PBoundary` — три строки; строки о графе выбора нет |
| — | — | — | в реестре есть, на странице нет: `RFiniteChoice`, `RACOnNat` (`PZero`), `RFunctionalChoice` (`PL4`), `RContinuumHypothesis` (`PL3_L4`) |

## Вердикт по непроверенной записи сверки 12.11 (стр. 57)

> | classic (L3) | Хигман; конечная детерминированность |

Цена строки верна для двух итоговых теорем: `higman_synthesis` — `Classical_Prop.classic`; `weak_determinacy`,
`zero_game_determined` — `BorelDeterminacy.classic`. Вопрос записи («для `higman_unit` — нет, для `dickson_pair` —
исключённое третье») решается так: оба ответа сводной страницы верны. `higman_unit` (лемма Хигмана для однобуквенного
алфавита) — Closed; `dickson_pair` (лемма Диксона для пар) — `Classical_Prop.classic`; `higman_synthesis` — конъюнкция
пяти утверждений, `classic` приходит в неё через одно, лемму Диксона. Слово «Хигман» в ярусе `classic` поэтому
относится к итоговой конъюнкции, а не к лемме Хигмана: записано расхождение по цене (расхождение 6). Лемма Диксона для
пар доказуема без `classic` (проверено, `CheckDickson.v`); после такой правки вся строка «Хигман» переходит в ярус
«0 аксиом». Запись сверки заменяется тремя записями ведомости на строке 57.

---

## Расхождение 1. Свойство таблицы названо доказательством того, что аксиома выбора не требуется (стр. 50–52, 62–64, 73–75, 175)

**Было:**

> (50–52) Это оформлено как разрешимая таблица: каждому результату сопоставлен ярус, и доказан итог — ни один
> *доказанный* результат не *требует* полной аксиомы выбора (ZFC).[^5]
>
> (62–64) Главное наблюдение: содержательное ядро теории множеств — от счётности до Кантора–Бендиксона и wqo — живёт на
> ярусах 0/ L3/ L3${}+{}$L4, и *ни один* доказанный результат не требует полной аксиомы выбора.
>
> (73–75) *Карта цен — роль-аудит: каждый результат несёт ярус (0 / L3 / L3${}+{}$L4), и доказано, что доказанное не
> *требует* полной AC.
>
> (175) функция `price`, и `proven_results_below_boundary` — каждый доказанный результат строго ниже границы.

**Проверка.** `proven_results_below_boundary` (`ChoicePriceMap.v:217`):

```coq
Definition below_boundary (p : AxiomPrice) : Prop :=
  match p with PBoundary => False | _ => True end.

Lemma proven_results_below_boundary :
  below_boundary (price RCantorGeneral) /\ below_boundary (price RSchroederBernstein) /\
  below_boundary (price RHigman) /\ … /\ below_boundary (price RACOnNat).
Proof. repeat split; exact I. Qed.
```

Closed under the global context. Конъюнктов десять (из пятнадцати строк ниже границы); каждый вычисляется в `True` по
таблице `price`, записанной рукой. В `CheckRegistry.v` показано, что то же верно для любой таблицы, не возвращающей
`PBoundary` (`below_boundary_is_table_property`): о самих результатах лемма ничего не использует.

Шапка того же файла (правка 17.10.2026) говорит обратное странице: «PL4 and PL3_L4 are NOT «below full AC»: whatever
rests on L4_witness rests on a principle from which choice over families follows»; «The old thesis … «nothing in
Part X uses the full Axiom of Choice» is withdrawn in its second half»; при самой лемме: «This says nothing about
strength relative to choice». Основание — лемма `l4_statement_gives_functional_choice` (`ChoicePriceMap.v:164`,
Closed): из формулировки `L4_witness` следует функция выбора для произвольного семейства. В `CheckRegistry.v` тот же
вывод сделан от самой аксиомы:

```coq
Theorem functional_choice_from_L4_axiom :
  forall (I X : Type) (R : I -> X -> Prop),
    (forall i, exists x, R i x) -> exists f : I -> X, forall i, R i (f i).
```

`Print Assumptions`: `L4_witness`.

**В чём расхождение.** Доказано, что в таблице у десяти строк стоит не «граница»; утверждения «результат не требует
аксиомы выбора» лемма не содержит, а сам реестр с октября говорит, что ярус L3 + L4 стоит на принципе, из которого
выбор следует.

**(а) Довести формализацию.** Утверждение «теорема не требует аксиомы выбора» — о выводимости; внутри Rocq оно
теоремой не записывается, и таблица его не заменит. Честно доводится более узкое: показать, что именно берётся из
L4. Для Шрёдера — Бернштейна это сделано в расхождении 2 (теорема из исключённого третьего и извлечения
*единственного* свидетеля, Closed). Для леммы Диксона и конечной детерминированности на деревьях — расхождения 6 и 9
(обе переходят в ярус «0 аксиом»). Саму лемму реестра можно заменить утверждением обо всей таблице (проверено,
`CheckRegistry.v`, Closed):

```coq
Lemma boundary_rows_exactly : forall r : ResultName,
  price r = PBoundary <->
  (r = RPowerSetObject \/ r = RFullKruskal \/ r = RBorelDeterminacy).
```

Оно остаётся свойством таблицы и так и должно называться.

**(б) Поправить слова:**

> (50–52) Это оформлено как таблица-реестр: каждому результату сопоставлен ярус — те допущения, которые компилятор
> печатает под его теоремой.[^5]
>
> (62–64) Главное наблюдение: содержательное ядро теории множеств — от счётности до Кантора–Бендиксона и wqo — живёт на
> ярусах 0 / L3 / L3${}+{}$L4. Результаты ярусов 0 и L3 выбором не пользуются. Ярус L3${}+{}$L4 стоит на L4 — извлечении
> свидетеля; из формулировки L4 следует функциональный выбор, и реестр фиксирует это отдельной леммой.
>
> (73–75) *Карта цен — роль-аудит: каждый результат несёт ярус по ответу компилятора. Ярусы 0 и L3 свободны от выбора;
> сила яруса L4 названа прямо. Цена меряется явно, а не замалчивается.*
>
> (175) `settheory/ChoicePriceMap.v`: `AxiomPrice` (`PZero`/`PL3`/`PL4`/`PL3_L4`/`PBoundary`), функция `price` и
> `proven_results_below_boundary` — перечисленные строки таблицы не помечены границей. Таблица записана рукой и
> сверена с `Print Assumptions`; теоремой о результатах она не является. В том же файле доказано, чего стоит ярус L4:
> из его формулировки следует функциональный выбор (`l4_statement_gives_functional_choice`).

## Расхождение 2. «Без выбора» при теореме, стоящей на L4 (стр. 9–10, 148, 149–150, 163–165)

**Было:**

> (9–10) Глава 10.3 свела сравнение мощностей к предпорядку вложений (Шрёдер–Бернштейн, Кантор) — без выбора.
>
> (148) Теория множеств перестроена без аксиомы выбора и без завершённой бесконечности
>
> (149–150) Содержательные теоремы выжили: Шрёдер–Бернштейн и общая теорема Кантора без выбора
>
> (163–165) Доказуемое без выбора простирается до Шрёдера–Бернштейна, bool-варианта теоремы Кантора
> ($X\not\twoheadrightarrow(X\to\mathtt{bool})$), Кантора–Бендиксона и wqo

**Проверка.** `Schroeder_Bernstein` (`SchroederBernstein_ERR.v:357`): `Print Assumptions` —
`Classical_Prop.classic`, `ToS_Axioms.L4_witness`. То же у `cardinal_antisym` и `process_continuum_hypothesis`.
`L4_witness : forall (A : Type) (P : A -> Prop), (exists x, P x) -> {x : A | P x}`; из этой формулировки выводится
функциональный выбор (расхождение 1). Теорема Кантора (`cantor_no_surjection`, `no_maximal_bool_power`) — Closed.

В доказательстве Шрёдера — Бернштейна L4 применяется только через `L4_definite` (стр. 80, 84 файла — прообраз при
инъекции, он единствен) и `L3_informative` (стр. 274–344 — булев свидетель для `P \/ ~P`, он тоже единствен).
Свидетель среди нескольких кандидатов нигде не выбирается.

**В чём расхождение.** Компилятор показывает под теоремой аксиому, из которой выбор следует; слова «без выбора»
относятся к тому, как эта аксиома применена, а не к тому, что стоит в выводе компилятора.

**(а) Довести формализацию.** Возможно, без новых аксиом: доказать теорему из двух посылок — исключённого третьего и
извлечения *единственного* свидетеля. Тогда «выбор не используется» становится теоремой. Набросок проверен
(`CheckSB.v`), ответ компилятора — Closed under the global context:

```coq
Section SB.
  Variables A B : Type.
  Variable f : A -> B.
  Variable g : B -> A.
  Hypothesis f_inj : forall a1 a2, f a1 = f a2 -> a1 = a2.
  Hypothesis g_inj : forall b1 b2, g b1 = g b2 -> b1 = b2.
  Hypothesis EM : forall P : Prop, P \/ ~ P.
  Hypothesis UC : forall (T : Type) (P : T -> Prop),
    (exists x, P x /\ forall y, P y -> y = x) -> {x : T | P x}.

  Inductive C : A -> Prop :=
    | C0 : forall a, (forall b, g b <> a) -> C a
    | CS : forall a, C a -> C (g (f a)).

  Lemma C_inv : forall a, C a ->
    (forall b, g b <> a) \/ exists a', C a' /\ a = g (f a').
  Proof.
    intros a Hc. destruct Hc as [a Hno | a' Hc'].
    - left. exact Hno.
    - right. exists a'. split; [exact Hc' | reflexivity].
  Qed.

  Definition R (a : A) (b : B) : Prop :=
    (C a /\ b = f a) \/ (~ C a /\ g b = a).

  Lemma R_total_unique : forall a,
    exists b, R a b /\ forall b', R a b' -> b' = b.
  Proof.
    intro a. destruct (EM (C a)) as [Hc | Hn].
    - exists (f a). split.
      + left. split; [exact Hc | reflexivity].
      + intros b' [[_ Hb'] | [Hn' _]]; [exact Hb' | contradiction].
    - destruct (EM (exists b, g b = a)) as [[b Hb] | Hno].
      + exists b. split.
        * right. split; assumption.
        * intros b' [[Hc' _] | [_ Hb']]; [contradiction |].
          apply g_inj. rewrite Hb, Hb'. reflexivity.
      + exfalso. apply Hn. apply C0. intros b Hb. apply Hno. exists b. exact Hb.
  Qed.

  Definition h (a : A) : B := proj1_sig (UC B (R a) (R_total_unique a)).

  Lemma h_spec : forall a, R a (h a).
  Proof.
    intro a. unfold h. exact (proj2_sig (UC B (R a) (R_total_unique a))).
  Qed.

  Theorem SB_unique_choice :
    exists h : A -> B,
      (forall a1 a2, h a1 = h a2 -> a1 = a2) /\ (forall b, exists a, h a = b).
  Proof.
    exists h. split.
    - intros a1 a2 Heq.
      destruct (h_spec a1) as [[Hc1 H1] | [Hn1 H1]];
        destruct (h_spec a2) as [[Hc2 H2] | [Hn2 H2]].
      + apply f_inj. rewrite <- H1, <- H2. exact Heq.
      + exfalso. apply Hn2. rewrite <- H2, <- Heq, H1. apply CS. exact Hc1.
      + exfalso. apply Hn1. rewrite <- H1, Heq, H2. apply CS. exact Hc2.
      + rewrite <- H1, <- H2, Heq. reflexivity.
    - intro b. destruct (EM (C (g b))) as [Hc | Hn].
      + destruct (C_inv (g b) Hc) as [Hno | [a [Hca Ha]]].
        * exfalso. exact (Hno b eq_refl).
        * exists a. apply g_inj in Ha.
          destruct (h_spec a) as [[_ H1] | [Hna _]]; [| contradiction].
          rewrite H1. symmetry. exact Ha.
      + exists (g b).
        destruct (h_spec (g b)) as [[Hc _] | [_ H1]]; [contradiction |].
        apply g_inj. exact H1.
  Qed.
End SB.
```

Посылка `UC` — определённое описание: свидетель извлекается только там, где он один. Из одного `classic`, без такого
извлечения, теорема в Rocq, по-видимому, недоступна (см. «Что проверить не удалось»). Эта теорема уместна в
`SchroederBernstein_ERR.v` или `CardinalityWithoutChoice.v`; сверка её места — за ведомостью главы X.3.

**(б) Поправить слова** (вариант при добавленной теореме — в скобках):

> (9–10) Глава 10.3 свела сравнение мощностей к предпорядку вложений: теорема Кантора — без допущений,
> Шрёдер–Бернштейн — на L3 и L4, причём из L4 берётся только единственный свидетель.
>
> (148) Теория множеств перестроена без завершённой бесконечности и без аксиомы выбора как отдельного постулата
>
> (149–150) Содержательные теоремы выжили: общая теорема Кантора без допущений, Шрёдер–Бернштейн на L3 и L4
> (выводится из исключённого третьего и извлечения единственного свидетеля)
>
> (163–165) Без допущений доказаны bool-вариант теоремы Кантора ($X\not\twoheadrightarrow(X\to\mathtt{bool})$),
> счётность ℚ, свойства производной Кантора–Бендиксона и wqo названных семейств; Шрёдер–Бернштейн стоит на L3 и L4

## Расхождение 3. Дихотомия Кантора — Бендиксона: цена (стр. 150–151 против стр. 56)

**Было:**

> (150–151) дихотомия Кантора–Бендиксона
>
> (56, ярус «0 аксиом») … Кантор–Бендиксон; Крускал (конкретные семейства) …

**Проверка.** Дихотомия в формализации одна — `process_continuum_hypothesis`
(`ProcessContinuumHypothesis.v:620`): `forall C : BinCollection, is_closed C -> is_enumerable C \/ has_perfect_subset C`.
`Print Assumptions`: `Classical_Prop.classic`, `ToS_Axioms.L4_witness`. В `CantorBendixsonFull.v` дихотомии нет (см.
расхождение 10). Реестр разводит их сам: «The perfect-set DICHOTOMY for closed sets is RContinuumHypothesis, not this
entry», `price RContinuumHypothesis = PL3_L4`.

**В чём расхождение.** Абзац стр. 148–152 перечисляет дихотомию среди теорем, выживших «без аксиомы выбора», а в карте
цен единственная строка с именем Кантора — Бендиксона стоит в ярусе «0 аксиом»; по компилятору дихотомия стоит на
`classic` и `L4_witness`.

**(а) Довести формализацию.** Не предлагается: по комментарию реестра L4 применяется здесь к счётному семейству
(`ProcessContinuumHypothesis.v`, стр. 70–80), то есть свидетели действительно выбираются; снять это допущение — отдельная
работа, предмет главы IV.5.

**(б) Поправить слова.** В таблице развести две строки (текст — в расхождении 5): в ярусе «0 аксиом» — «свойства
производной Кантора–Бендиксона», в ярусе «classic + L4» — «дихотомия замкнутых множеств
(`process_continuum_hypothesis`)».

## Расхождение 4. Мост «сюръекция → инъекция» назван не привлечённым (стр. 83, 115–116)

**Было:**

> (83) обратный мост сюръекция${}\to{}$инъекция (это сам выбор);
>
> (115–116) *не привлечено* (процессные формы полного Крускала и Мартина, мост выбора, линейность шкалы — открыто)

**Проверка.** В `src` такой теоремы нет; шапка `CardinalityWithoutChoice.v` (стр. 17–22): «With only L4_witness one
inverts a BIJECTION (unique preimages), not an arbitrary surjection». Это замечание неверно: `L4_witness` применим к
любому `exists`. Набросок проверен (`CheckBridge.v`):

```coq
Theorem surjects_to_injects_from_L4 : forall A B : Type,
  surjects A B -> injects B A.
Proof.
  intros A B [f Hf].
  set (g := fun b => proj1_sig (@ToS_Axioms.L4_witness A (fun a => f a = b) (Hf b))).
  assert (Hg : forall b, f (g b) = b).
  { intro b. unfold g.
    exact (proj2_sig (@ToS_Axioms.L4_witness A (fun a => f a = b) (Hf b))). }
  exists g. intros b1 b2 H.
  rewrite <- (Hg b1), <- (Hg b2). rewrite H. reflexivity.
Qed.
```

`Print Assumptions`: `L4_witness`.

**В чём расхождение.** Мост отнесён к тому, чего в теории нет, а он выводится в три шага из аксиомы, на которой уже
стоят Шрёдер — Бернштейн и антисимметрия мощностей.

**(а) Довести формализацию.** Добавить теорему в `CardinalityWithoutChoice.v` (счёт файла станет 11 Qed), исправить
замечание шапки, в реестр внести строку с ярусом `PL4`. Новых аксиом не требуется.

**(б) Поправить слова:**

> (83) обратный мост сюръекция${}\to{}$инъекция стоит особо: на ярусах 0 и L3 его нет (это сам выбор), из L4 он
> выводится в три шага — этим и меряется сила яруса L4;
>
> (115–116) *не привлечено* (процессные формы полного Крускала и Мартина, линейность шкалы — открыто)

## Расхождение 5. Таблица страницы и реестр разошлись (стр. 50, 56–60, 175)

**Было:**

> (50) Все результаты Части X выстраиваются по *цене аксиом*. Это оформлено как разрешимая таблица: каждому результату
> сопоставлен ярус
>
> (175) `AxiomPrice` (`PZero`/`PL3`/`PL3_L4`/`PBoundary`)

**Проверка.** `Inductive AxiomPrice : Set := PZero | PL3 | PL4 | PL3_L4 | PBoundary.` (`ChoicePriceMap.v:52`) — ярусов
пять. Построчное сравнение — в двух таблицах выше: в реестре нет трёх строк страницы (ординалы и $\varepsilon_0$;
файлы `P4_…`; $\Pi^1_1$) и яруса «вычислительный примитив»; на странице нет четырёх строк реестра и яруса `PL4`.

**В чём расхождение.** Страница описывает таблицу как формализованную, а её состав и число ярусов отличаются от
реестра в файле.

**(а) Довести формализацию.** В `ResultName` добавить строки для ординалов (`wf_ord_lt`, `transfinite_ind` — `PZero`),
файлов `P4_…` (`PZero`), моста сюръекция → инъекция (`PL4`, расхождение 4) и $\Pi^1_1$-переинтерпретации; для
последней нужен шестой ярус — «параметр» (в выводе компилятора стоит `eval_program`). У `RFiniteChoice` назвать
опорную теорему; для `RFunctionalChoice` добавить теорему от самой аксиомы (`functional_choice_from_L4_axiom`,
`CheckRegistry.v`), чтобы ярус совпал с выводом компилятора. Всё это — правка перечисления и леммы, доказываемые
`reflexivity`.

**(б) Поправить слова.** Таблица стр. 54–60, приведённая к реестру и компилятору (без правки формализации):

> | **Ярус (цена)** | **Результаты** |
> |---|---|
> | 0 аксиом | счётность ℚ (Калкин–Уилф); диагональ (`diagonal_differs`); несчётность $[0,1]$ для регулярных перечислений (трисекция); общий Кантор $X\to(X\to\mathtt{bool})$; свойства производной Кантора–Бендиксона; Крускал (цепи, вилки, звёзды); Хигман для однобуквенного алфавита; выбор из непустых списков; ординалы, $\varepsilon_0$, `wf_ord_lt`, `transfinite_ind` (сверено `Print Assumptions`: Closed); уровневая индукция; файлы `P4_Eliminates_*.v`, `P4Prohibits*.v` — ATR, Бесконечность, импредикативность |
> | classic (L3) | лемма Диксона для пар; исключённое третье для «у первого игрока есть выигрышная стратегия» |
> | L4 | функциональный выбор по произвольному семейству — следствие формулировки L4 |
> | classic ${}+{}$ L4 | Шрёдер–Бернштейн; антисимметрия мощностей (`cardinal_antisym`); дихотомия замкнутых множеств (`process_continuum_hypothesis`) |
> | вычислительный примитив | $\Pi^1_1$-переинтерпретация — при `eval_program` (`Parameter`); в реестр не внесена |
> | **Граница (`PBoundary`)** | (без изменений) |

После правок формализации из расхождений 6 и 9 строка «classic (L3)» пустеет наполовину: лемма Диксона и
детерминированность конечных деревьев переходят в ярус «0 аксиом».

## Расхождение 6. Хигман в ярусе classic; «конструктивные ядра» (стр. 57, 39–41, 45)

**Было:**

> (57) | classic (L3) | Хигман; конечная детерминированность |
>
> (39–41) ToS проводит их *конструктивные ядра для конкретных семейств* без выбора — но *не* в полной общности.
>
> (45) Это конструктивные ядра «высоких» теорем, не их полная общность.

**Проверка.** `HigmanLemma.v`, 11 лемм: `higman_unit`, `wqo_nat_le`, `wqo_bool`, `wqo_unit` и ещё три — Closed;
`tail_min_exists`, `right_min_unbounded`, `dickson_pair`, `higman_synthesis` — `Classical_Prop.classic`.
В `BorelDeterminacy.v` три леммы (`weak_determinacy`, `zero_game_determined`, `can_win_or_not`) —
`BorelDeterminacy.classic`.

**В чём расхождение.** Лемма Хигмана в доказанном объёме обходится без допущений; исключённое третье несёт лемма
Диксона для пар, записанная в тот же итог. Обратно, «конструктивными» названы ядра, два из которых (лемма Диксона,
детерминированность) стоят на исключённом третьем.

**(а) Довести формализацию.** Возможно: лемма Диксона для пар доказывается без `classic`. Идея: вдоль цепочки
индексов, на которой `f` не убывает, `g` не может строго убывать больше `g`(начало) раз; цепочка, длина которой
задана функцией от её начала, строится индукцией по `f 0`. Набросок проверен (`CheckDickson.v`); `Print Assumptions`
для `dickson_pair_constructive`, `wqo_nat_pair`, `higman_synthesis_closed` — Closed under the global context:

```coq
Fixpoint FChain (f : nat -> nat) (k i : nat) : Prop :=
  match k with
  | O => True
  | S k' => exists j, (i < j)%nat /\ (f i <= f j)%nat /\ FChain f k' j
  end.

Lemma fchain_shift : forall f c k i,
  FChain (fun n => f (n + c)) k i -> FChain f k (i + c).
Proof.
  intros f c k. induction k as [| k IH]; intros i H.
  - exact I.
  - simpl in H. destruct H as [j [Hij [Hle Hc]]].
    simpl. exists (j + c). split; [lia | split; [exact Hle | apply IH; exact Hc]].
Qed.

Lemma fchain_exists_bounded : forall k,
  (forall f : nat -> nat, exists i, FChain f k i) ->
  forall m (f : nat -> nat), (f 0 <= m)%nat -> exists i, FChain f (S k) i.
Proof.
  intros k IHk. induction m as [| m IHm]; intros f Hf0.
  - destruct (IHk (fun n => f (n + 1))) as [i' Hi'].
    apply fchain_shift in Hi'.
    exists 0. simpl. exists (i' + 1). split; [lia | split; [lia | exact Hi']].
  - destruct (IHk (fun n => f (n + 1))) as [i' Hi'].
    apply fchain_shift in Hi'.
    destruct (Nat.le_gt_cases (f 0) (f (i' + 1))) as [Hle | Hgt].
    + exists 0. simpl. exists (i' + 1). split; [lia | split; [exact Hle | exact Hi']].
    + destruct (IHm (fun n => f (n + (i' + 1)))) as [i'' Hi''].
      * simpl. lia.
      * apply fchain_shift in Hi''. exists (i'' + (i' + 1)). exact Hi''.
Qed.

Lemma fchain_exists : forall k (f : nat -> nat), exists i, FChain f k i.
Proof.
  induction k as [| k IHk]; intro f.
  - exists 0. exact I.
  - exact (fchain_exists_bounded k IHk (f 0) f (Nat.le_refl _)).
Qed.

Lemma fchain_dep_bounded : forall m (f h : nat -> nat),
  (f 0 <= m)%nat -> exists i, FChain f (h i) i.
Proof.
  induction m as [| m IHm]; intros f h Hf0.
  - destruct (h 0) as [| k] eqn:Eh.
    + exists 0. rewrite Eh. exact I.
    + destruct (fchain_exists k (fun n => f (n + 1))) as [i' Hi'].
      apply fchain_shift in Hi'.
      exists 0. rewrite Eh. simpl. exists (i' + 1).
      split; [lia | split; [lia | exact Hi']].
  - destruct (h 0) as [| k] eqn:Eh.
    + exists 0. rewrite Eh. exact I.
    + destruct (fchain_exists k (fun n => f (n + 1))) as [i' Hi'].
      apply fchain_shift in Hi'.
      destruct (Nat.le_gt_cases (f 0) (f (i' + 1))) as [Hle | Hgt].
      * exists 0. rewrite Eh. simpl. exists (i' + 1).
        split; [lia | split; [exact Hle | exact Hi']].
      * destruct (IHm (fun n => f (n + (i' + 1))) (fun n => h (n + (i' + 1))))
          as [i'' Hi''].
        -- simpl. lia.
        -- cbv beta in Hi''. apply fchain_shift in Hi''.
           exists (i'' + (i' + 1)). exact Hi''.
Qed.

Lemma fchain_good_pair : forall (f g : nat -> nat) k i,
  FChain f k i -> (g i < k)%nat ->
  exists p q, (p < q)%nat /\ (f p <= f q)%nat /\ (g p <= g q)%nat.
Proof.
  intros f g k. induction k as [| k IH]; intros i Hc Hg.
  - lia.
  - simpl in Hc. destruct Hc as [j [Hij [Hle Hc]]].
    destruct (Nat.le_gt_cases (g i) (g j)) as [Hgle | Hggt].
    + exists i, j. split; [exact Hij | split; [exact Hle | exact Hgle]].
    + apply (IH j Hc). lia.
Qed.

Theorem dickson_pair_constructive : forall f g : nat -> nat,
  exists i j : nat, (i < j)%nat /\ (f i <= f j)%nat /\ (g i <= g j)%nat.
Proof.
  intros f g.
  destruct (fchain_dep_bounded (f 0) f (fun i => S (g i)) (Nat.le_refl _)) as [i Hi].
  cbv beta in Hi.
  exact (fchain_good_pair f g (S (g i)) i Hi (Nat.lt_succ_diag_r _)).
Qed.
```

Этим доказательством заменяются `tail_min_exists`, `right_min_unbounded` и прежнее доказательство `dickson_pair`;
формулировки `dickson_pair` и `higman_synthesis` не меняются, импорт `Classical_Prop` из файла уходит. В реестре
`price RHigman` становится `PZero`, лемма `higman_uses_L3_not_AC` переписывается. Конечная детерминированность на
деревьях — расхождение 9. После обеих правок слова «конструктивные ядра» верны для всех четырёх результатов.

**(б) Поправить слова** (если формализацию не трогать):

> (57) | classic (L3) | лемма Диксона для пар; конечная детерминированность |
>
> (в ярус «0 аксиом» добавить) Хигман для однобуквенного алфавита
>
> (39–41) ToS проводит их *ядра для конкретных семейств* без выбора — но *не* в полной общности; лемма Диксона и
> детерминированность при этом стоят на исключённом третьем.
>
> (45) Это ядра «высоких» теорем для конкретных семейств, не их полная общность.

## Расхождение 7. Лемма Хигмана: доказан один алфавит (стр. 29–31)

**Было:**

> *Лемма Хигмана*: списки над конечным алфавитом образуют хорошо-квазиупорядочение (wqo) — доказано для конкретных
> алфавитов (единичного, булева, $ℕ$) с леммой Диксона в основе.[^1]

**Проверка.** `higman_unit` (`HigmanLemma.v:158`): `is_wqo (list_le (fun _ _ : unit => True))` — списки над
однобуквенным алфавитом; доказательство сводит вложение к сравнению длин (`wqo_nat_le`). `wqo_bool` (:135):
`is_wqo (fun a b : bool => implb a b = true)` и `wqo_nat_le` (:59): `is_wqo Nat.le` — утверждения о самих `bool` и
`nat`. `dickson_pair` в доказательстве `higman_unit` не участвует. Шапка файла: «Higman's lemma for an ARBITRARY
finite alphabet is NOT proved here: only the one-letter case».

**В чём расхождение.** Для списков доказан один алфавит из трёх названных; для `bool` и ℕ доказано, что сами эти
множества хорошо-квазиупорядочены, а лемма Диксона — отдельное утверждение, не основание.

**(а) Довести формализацию.** Нужно доказать `is_wqo (list_le (@eq bool))` (двухбуквенный алфавит) и
`is_wqo (list_le Nat.le)`. Оба утверждения верны; для двух букв известны конструктивные доказательства (Кокан —
Фридлендер; формализация Бергхофера), но это отдельная работа в несколько сотен строк, здесь не пробовалась. Случай
алфавита ℕ в классическом изложении идёт через минимальную плохую последовательность и потребует `classic` вместе с
зависимым выбором.

**(б) Поправить слова:**

> *Лемма Хигмана*: списки над конечным алфавитом образуют хорошо-квазиупорядочение (wqo). Доказан случай
> однобуквенного алфавита — он сводится к wqo на длинах; рядом доказаны wqo для самих $\mathtt{bool}$ и $ℕ$ и лемма
> Диксона для пар.[^1]
>
> [^1]: `HigmanLemma.v`: `is_wqo`, `wqo_nat_le`, `higman_unit` (списки над однобуквенным алфавитом), `dickson_pair`,
> итог — `higman_synthesis`. 11 Qed; `classic` (L3) несёт только лемма Диксона.

## Расхождение 8. Конечная детерминированность не доказана в общем виде (стр. 35–37, 44–46, 151–152, 174)

**Было:**

> (35–37) И *конечная детерминированность игр* (Цермело, 1913): всякая конечная игра определена.[^4]
>
> (44–45) Без выбора доказуемы и wqo-результаты (Хигман, Крускал — для конкретных семейств) и конечная (цермеловская)
> детерминированность.
>
> (174) `BorelDeterminacy.v`: `weak_determinacy`, `zero_game_determined`. 15 Qed, 1 аксиома (`classic`). NB: вопреки
> имени файла, доказана именно *конечная* (цермеловская) детерминированность, а *не* борелевская (Мартина).

**Проверка.** `BorelDeterminacy.v`:

```coq
Definition determined (W : GameState -> Prop) (K : nat) : Prop :=
  (exists sI, forall sII, wins_I sI sII W K) \/
  (exists sII, forall sI, ~ wins_I sI sII W K).

Definition determined_weak (W : GameState -> Prop) (K : nat) : Prop :=
  (exists sI, forall sII, W (play sI sII K)) \/
  ~ (exists sI, forall sII, W (play sI sII K)).

Theorem weak_determinacy : forall W K, determined_weak W K.
Theorem zero_game_determined : forall W, determined W 0.
```

`weak_determinacy` имеет вид `P \/ ~ P` и доказано одним применением `classic`. Свойство `determined` доказано в
четырёх случаях: `W = True` (:88), `W = False` (:101), игра первого хода при `K >= 1` (:134), `K = 0` (:164).
Комментарий реестра (`ChoicePriceMap.v:95–101`) говорит то же: «this is excluded middle applied to «player I has a
winning strategy», not determinacy proper».

**В чём расхождение.** Теорема Цермело утверждает, что стратегия есть у одного из двух игроков; в файле для
произвольной игры доказано только, что у первого игрока стратегия либо есть, либо её нет.

**(а) Довести формализацию.** Возможно; набросок проверен (`CheckZermelo.v`, 105 строк):

```coq
Fixpoint WinI (W : GameState -> Prop) (r : nat) (h : GameState) : Prop :=
  match r with
  | O => W h
  | S r' => if Nat.even (length h)
            then exists m, WinI W r' (h ++ [m])
            else forall m, WinI W r' (h ++ [m])
  end.

Theorem zermelo_determinacy : forall W K, determined W K.
```

`Print Assumptions`: `classic` (объявление `BorelDeterminacy.v:21`) и `L4_witness`. Ход: `WinI W r h` — «первый игрок
форсирует `W` из истории `h` за `r` ходов»; по `classic` это верно или неверно для пустой истории; стратегия
выигрывающей стороны на каждой истории берёт ход, сохраняющий инвариант. `L4_witness` нужен, чтобы из «для каждой
истории есть хороший ход» получить функцию-стратегию: ходов бесконечно много (`nat`), условие `W` неразрешимо. Цена
при этом — ярус L3 + L4, а не L3. Вариант без допущений — для конечных деревьев — в расхождении 9.

**(б) Поправить слова** (если формализацию не трогать):

> (35–37) И *конечная детерминированность игр* (Цермело, 1913): в игре конечной длины выигрышная стратегия есть у
> одного из игроков. В формализации это доказано для игры без ходов и для трёх простых условий выигрыша; для
> произвольной игры доказано исключённое третье для высказывания «у первого игрока есть выигрышная стратегия».[^4]
>
> (44–45) Без выбора доказуемы wqo-результаты (Хигман — для однобуквенного алфавита, Крускал — для конкретных
> семейств) и частные случаи конечной (цермеловской) детерминированности.
>
> (174) `BorelDeterminacy.v`: `determined` (стратегия есть у одного из игроков), `zero_game_determined`,
> `trivial_game_determined`, `first_move_determined`; `weak_determinacy` — исключённое третье для «у первого игрока
> есть стратегия». 19 Qed, 1 аксиома (`classic`). NB: вопреки имени файла, речь об играх конечной длины; ни общая
> цермеловская, ни борелевская (Мартина) детерминированность здесь не доказаны.

Так же правится стр. 151–152 («конечная детерминированность» → «частные случаи конечной детерминированности»).

## Расхождение 9. `finite_game_determined` — булева дихотомия (стр. 110–111, 177)

**Было:**

> (110–111) конечная детерминированность — обратная индукция на дереве игры, тоже без башни.
>
> (177) `foundation/FiniteGameDeterminacy.v` (`finite_game_determined`, обратная индукция)

**Проверка.** `FiniteGameDeterminacy.v:40`:

```coq
Theorem finite_game_determined : forall g, mover_wins g = true \/ mover_wins g = false.
Proof. intro g. destruct (mover_wins g); [left | right]; reflexivity. Qed.
```

Closed. Утверждение верно для любой функции со значениями в `bool`; определение `mover_wins` (обратная индукция) в
доказательстве не раскрывается. О том, что значение `true` означает выигрыш ходящего, теоремы нет (то же отмечено в
комментарии реестра: «no link to winning strategies is proved»).

**В чём расхождение.** Обратная индукция стоит в определении функции, а теорема утверждает лишь, что булево значение
равно `true` или `false`.

**(а) Довести формализацию.** Возможно, без допущений. Набросок проверен (`CheckGameTree.v`, 108 строк), Closed under
the global context:

```coq
Inductive Win : GameTree -> Prop :=
  | win_leaf : Win (GLeaf true)
  | win_node : forall cs c, In c cs -> Lose c -> Win (GNode cs)
with Lose : GameTree -> Prop :=
  | lose_leaf : Lose (GLeaf false)
  | lose_node : forall cs, (forall c, In c cs -> Win c) -> Lose (GNode cs).

Theorem backward_induction_sound : forall g,
  (mover_wins g = true -> Win g) /\ (mover_wins g = false -> Lose g).

Theorem win_lose_exclusive : forall g, Win g -> Lose g -> False.

Theorem finite_game_strategically_determined : forall g,
  (Win g \/ Lose g) /\ ~ (Win g /\ Lose g) /\
  (mover_wins g = true <-> Win g) /\ (mover_wins g = false <-> Lose g).
```

`Win g` — «ходящий в позиции `g` форсирует выигрыш» (есть ход в позицию, проигранную противником); `Lose g` — «любой
ход ведёт в позицию, выигранную противником». Теорема говорит: каждая позиция конечного дерева выиграна ровно одной
стороной, и `mover_wins` вычисляет, какой. Индукция по дереву со списком детей — через вспомогательный принцип
`GameTree_ind'` (в файле). С этой теоремой слова стр. 110–111 и 177 верны, а «конечная детерминированность» в карте
цен получает опору в ярусе «0 аксиом».

**(б) Поправить слова:**

> (110–111) значение конечной игры вычисляется обратной индукцией по дереву, тоже без башни.
>
> (177) `foundation/FiniteGameDeterminacy.v` (`mover_wins` — значение позиции обратной индукцией)

## Расхождение 10. Кантор — Бендиксон: совершенное ядро и конечные множества (стр. 34–35, 173)

**Было:**

> (34–35) *Кантор–Бендиксон*: производная замкнутого множества как процесс, $\omega$-предел — совершенное ядро.[^3]
>
> (173) `CantorBendixsonFull.v`: `CB_deriv` (удаление изолированных точек), `CB_omega` ($\omega$-предел);
> совершенное-или-пустое ядро, конечные множества рассеяны. 20 Qed, 0 аксиом.

**Проверка.** Теоремы `is_perfect (CB_omega S)` в файле нет; «omega-limit is perfect (or empty)» стоит только в строке
Rules шапки. Ближайшие леммы:

```coq
Lemma CB_omega_stable : forall S x, CB_omega S x -> CB_deriv (CB_omega S) x -> CB_omega S x.
Proof. intros S x Hom _. exact Hom. Qed.

Lemma CB_omega_accumulation_in_parent : forall S x,
  CB_omega S x -> forall eps, eps > 0 -> exists y, S y /\ ~(x == y) /\ Qabs (x - y) < eps.
```

Первая возвращает свою посылку (вторая посылка не используется); вторая даёт близкие точки исходного множества `S`,
а не ω-предела. `S_finite_scattered` (:344) — о множестве $\{0,1,2\}$ (`S_finite`, :164). Все 23 леммы — Closed.

В общем виде «ω-предел совершенен или пуст» неверно. Пример: множество ранга Кантора — Бендиксона $\omega+1$ (копия
ординала $\omega^\omega+1$ в ℚ: к точке 0 сходятся куски рангов 1, 2, 3, …). Точка 0 остаётся во всех конечных
итерациях, все прочие точки на каком-то шаге уходят; ω-предел — одна точка $\{0\}$, она изолирована. Совершенное ядро
в общем случае достигается только трансфинитным продолжением итерации.

**В чём расхождение.** Главное утверждение о ядре в файле не доказано и в такой общности неверно; рассеянность
доказана для одного трёхточечного множества.

**(а) Довести формализацию.** Доказуемы без допущений три верных утверждения (проверено, `CheckCB.v`, все Closed):

```coq
(* всякое совершенное подмножество лежит в ω-пределе: предел содержит совершенное ядро *)
Theorem perfect_kernel_in_omega : forall (A P : PointSet),
  subset P A -> is_perfect P -> subset P (CB_omega A).

(* если процесс стабилизируется на шаге n, этот шаг совершенен, равен ω-пределу
   и содержит всякое совершенное подмножество *)
Theorem stable_stage_is_perfect_kernel : forall (A : PointSet) (n : nat),
  (forall x, CB_iter A n x -> CB_iter A (S n) x) ->
  is_perfect (CB_iter A n) /\
  (forall x, CB_omega A x <-> CB_iter A n x) /\
  (forall P : PointSet, subset P A -> is_perfect P -> subset P (CB_iter A n)).

(* всякое конечное множество рациональных чисел рассеяно, его производная пуста *)
Definition in_list (l : list Q) : PointSet := fun x => exists q, In q l /\ x == q.
Theorem finite_set_scattered : forall l : list Q, is_scattered (in_list l).
Theorem finite_set_deriv_empty : forall (l : list Q) (x : Q), ~ CB_deriv (in_list l) x.
```

Ключевая лемма первого:

```coq
Lemma perfect_subset_in_iter : forall (A P : PointSet),
  subset P A -> is_perfect P -> forall n x, P x -> CB_iter A n x.
Proof.
  intros A P Hsub Hperf. induction n as [| n IH]; intros x Hx.
  - simpl. apply Hsub. exact Hx.
  - simpl. unfold CB_deriv, is_accumulation. split.
    + apply IH. exact Hx.
    + intros eps Heps. destruct (Hperf x Hx) as [_ Hacc].
      destruct (Hacc eps Heps) as [y [Hy [Hne Hd]]].
      exists y. split; [apply IH; exact Hy | split; assumption].
Qed.
```

Рассеянность конечного множества — через наименьшее расстояние от точки до остальных точек списка (`finite_gap`).

**(б) Поправить слова** (первый вариант — при добавленных теоремах, второй — без правки формализации):

> (34–35) *Кантор–Бендиксон*: производная множества как процесс; $\omega$-предел итераций содержит всякое совершенное
> подмножество, а при стабилизации на конечном шаге совпадает с совершенным ядром.[^3]
>
> (34–35, без правки формализации) *Кантор–Бендиксон*: производная множества как процесс — убывающая цепь итераций и
> её $\omega$-предел.[^3]
>
> (173) `CantorBendixsonFull.v`: `CB_deriv` (точки накопления), `CB_iter`, `CB_omega` ($\omega$-предел); цепь итераций
> убывает (`CB_iter_monotone`); множество $\{0,1,2\}$ рассеяно, его $\omega$-предел пуст. 23 Qed, 0 аксиом.

## Расхождение 11. Сноска о Крускале называет не те леммы (стр. 172)

**Было:**

> `KruskalFull.v`/`KruskalTree.v`: `chain_wqo`, `fork_wqo`, `growing_wqo`, `depth1_wqo`, итог — `L5_from_kruskal`.
> 15 Qed, 0 новых аксиом.

**Проверка.** `KruskalFull.v`:

```coq
Lemma chain_wqo : forall f : nat -> FTree,
  (forall k, f k = chain k) -> exists i j, (i < j)%nat /\ tree_embed (f i) (f j).
Lemma growing_wqo : forall f : nat -> FTree,
  (forall k, tree_embed (f k) (f (S k))) -> exists i j, (i < j)%nat /\ tree_embed (f i) (f j).
```

У `chain_wqo` и `fork_wqo` посылка фиксирует одну последовательность (`chain 0, chain 1, …`); у `growing_wqo`
заключение есть посылка при `k = 0`. Все три доказаны парой `(0, 1)`. `L5_from_kruskal` (:166) — конъюнкция этих
трёх и `depth0_wqo` (все деревья — листья); `depth1_wqo` в неё не входит, о L5 утверждение не говорит. Свойство wqo
для *семейств* доказано в другом файле: `kruskal_chains`, `kruskal_forks` (`KruskalTree.v:265, 276`) —
`is_wqo (fun m n => tree_embed (chain m) (chain n))`, любая последовательность цепей (вилок). `depth1_wqo` (:129) —
любая последовательность звёзд. Все 30 лемм — Closed.

**В чём расхождение.** Слова главы (стр. 32–34) опираются на семейные теоремы, а сноска называет леммы об одной
последовательности и лемму, повторяющую свою посылку.

**(а) Довести формализацию.** Не требуется: нужные теоремы есть. По желанию — закрыть «глубину $\le 1$» целиком,
включая последовательности, где листья чередуются со звёздами (`depth1_wqo` их не покрывает); проверено,
`CheckKruskal.v`, Closed:

```coq
Definition depth_le1 (t : FTree) : Prop :=
  t = FLeaf \/ exists m, t = FNode (repeat FLeaf m).

Theorem depth_le1_wqo : forall f : nat -> FTree,
  (forall k, depth_le1 (f k)) ->
  exists i j, (i < j)%nat /\ tree_embed (f i) (f j).
Proof.
  intros f Hd.
  pose (g := fun k => match f k with FLeaf => 0 | FNode ch => S (length ch) end).
  destruct (KruskalTree.wqo_nat_le g) as [i [j [Hij Hle]]].
  exists i, j. split; [exact Hij |].
  unfold g in Hle.
  destruct (Hd i) as [Hi | [mi Hi]]; rewrite Hi in *.
  - constructor.
  - destruct (Hd j) as [Hj | [mj Hj]]; rewrite Hj in *.
    + exfalso. lia.
    + apply depth1_grows_with_children.
      rewrite !repeat_length in Hle. lia.
Qed.
```

**(б) Поправить слова:**

> (32–34) *Теорема Крускала*: конечные деревья wqo под гомеоморфным вложением — доказано для конкретных семейств
> (цепи, вилки, звёзды — деревья глубины 1).[^2]
>
> [^2]: `KruskalTree.v`: `kruskal_chains`, `kruskal_forks` (семейства цепей и вилок); `KruskalFull.v`: `depth1_wqo`
> (звёзды). 19 и 11 Qed, 0 аксиом.

## Расхождение 12. «Содержание достигается без завершённого объекта»; статусы стен (стр. 105–108, 177)

**Было:**

> (105–108) То, что классически требует *завершённой бесконечности* — полный $\mathcal{P}(\mathbb{N})$,
> минимально-плохая последовательность Крускала, башня итерированных степеней Бореля, — при разборе оказывается
> ZFC-*упаковкой*, а не стеной: содержание достигается *без* завершённого объекта.
>
> (177) ровно завершённая бесконечность запрещена, три «стены» откатываются (`ReachedFreely`/`NotYetBuilt`).

**Проверка.** `FormerWallsLedger.v`:

```coq
Definition status (w : Wall) : Status :=
  match w with
  | WPowersetObject     => ReachedFreely
  | WMinimalBadSequence => PartiallyReached
  | WBorelTower         => PartiallyReached
  | WCompletedInfinity  => ForbiddenObject
  end.

Definition zfc_posits_completed_object (w : Wall) : bool := true.
Definition tos_needs_completed_object (w : Wall) : bool :=
  match w with WCompletedInfinity => true | _ => false end.
```

`former_walls_are_artifacts` (:106) и `only_completed_infinity_is_a_wall` (:70) — свойства этих таблиц; функция
`zfc_posits_completed_object` от аргумента не зависит. Статус `NotYetBuilt` объявлен (:55), но ни одной стене не присвоен. Свидетели: для степени —
`powerset_card`, `cantor_bool_seq` (содержательны, Closed); для Крускала — `bool_pigeonhole3`
(`forall a b c : bool, a = b \/ b = c \/ a = c`); для Бореля — `finite_game_determined` (расхождение 9). Шапка файла:
«Мы НЕ доказываем ПОЛНЫХ Крускала/Бореля — их ПОЛНЫЕ формы остаются ГОРИЗОНТОМ».

**В чём расхождение.** «Содержание достигается» сказано о трёх теоремах сразу; доказано оно для степени, а для
Крускала и Бореля есть конечные ядра и классификация, записанная рукой. Статусы в сноске названы по прежней версии
таблицы.

**(а) Довести формализацию.** Полные теоремы Крускала и Мартина — за пределами этой правки. Свидетель для
детерминированности можно сделать содержательным (расхождение 9). Определение `zfc_posits_completed_object` полезнее
убрать, чем оставлять константой: первый конъюнкт `former_walls_are_artifacts` тогда сводится ко второму столбцу
таблицы.

**(б) Поправить слова:**

> (105–108) То, что классически требует *завершённой бесконечности* — полный $\mathcal{P}(\mathbb{N})$,
> минимально-плохая последовательность Крускала, башня итерированных степеней Бореля, — при разборе раскладывается на
> ядро и упаковку. Для степени ядро достигнуто целиком *без* завершённого объекта; для Крускала и Бореля достигнуты
> конечные ядра, а полные формы пока не построены.
>
> (177) ровно завершённая бесконечность запрещена; из трёх «стен» одна достигнута свободно (`ReachedFreely`), две —
> частично (`PartiallyReached`).

## Расхождение 13. Импредикативная тотальность: «несовместимо с конечной актуальностью» (стр. 92–93)

**Было:**

> импредикативная тотальность-в-себе (P1${}+{}$P4). Это не «пока не доказано», а *несовместимо* с конечной
> актуальностью.

**Проверка.** Несовместимость с P4 доказана для завершённого бесконечного множества (`completed_inf_contradicts_P4`,
`P4CompletedInfinity.v:64`) и графа всюду определённой функции (`completed_graph_contradicts_P4`,
`P4ProhibitsAC.v:108`), обе при условии `bridge`, обе Closed. В `P4ProhibitsImpredicative.v` (7 лемм, Closed):

```coq
Theorem P1_blocks_russell : forall (member : nat -> nat -> Prop),
  (forall x, ~ member x x) -> forall x, russell_criterion member x.   (* russell_criterion member x := ~ member x x *)
Theorem russell_contradiction_without_P1 : forall (member : nat -> nat -> Prop) (r : nat),
  (forall x, member x r <-> ~ member x x) -> False.
```

У первой заключение совпадает с посылкой; вторая — парадокс Рассела, посылки P4 в ней нет. Определения `NatTotality`
и `impredicative_prop` в теоремах не участвуют. Остальное в файле — ограниченность стадий для `nat`.

**В чём расхождение.** Слово «несовместимо» подкреплено теоремой для двух пунктов перечня из четырёх; для
импредикативной тотальности теоремы с посылкой P4 в файле нет.

**(а) Довести формализацию.** Предмет главы X.5 (её сноска 6 ссылается на тот же файл); здесь не предлагается.

**(б) Поправить слова:**

> импредикативная тотальность-в-себе (P1${}+{}$P4). Для завершённой бесконечности и завершённого графа несовместимость
> с конечной актуальностью доказана теоремой; степень-Элемент и тотальность-в-себе исключает P1: расселова
> совокупность не строится ни на каком уровне.

## Расхождение 14. Числа Qed в сносках (стр. 171–174)

| строка | на странице | в файле (`grep -c 'Qed\.'`) |
|---|---|---|
| 171 | `HigmanLemma.v` — 15 Qed | 11 |
| 172 | `KruskalFull.v`/`KruskalTree.v` — 15 Qed | 11 и 19 |
| 173 | `CantorBendixsonFull.v` — 20 Qed | 23 |
| 174 | `BorelDeterminacy.v` — 15 Qed | 19 |

Числа страницы совпадают с шапками файлов (`KruskalFull.v`, `KruskalTree.v`, `CantorBendixsonFull.v`,
`BorelDeterminacy.v`), которые устарели; у `HigmanLemma.v` шапка верна (11). Числа аксиом и слова о цене в этих
сносках верны. `ZFCAxiomLedger.v` — 9 Qed, на странице верно (в шапке файла — 10).

**(а)** Поправить шапки четырёх файлов. **(б)** На странице: 11; «19 и 11»; 23; 19 — тексты сносок приведены в
расхождениях 7, 8, 10, 11.

## Расхождение 15. Сокращённые имена в таблице (стр. 56)

**Было:**

> `P4_Eliminates`/`Prohibits`-кластер — ATR, Бесконечность, импредикативность

**Проверка.** Объявлений `P4_Eliminates` и `Prohibits` нет; это части имён файлов `P4_Eliminates_ATR.v`,
`P4_Eliminates_Infinity.v`, `P4_Eliminates_AC.v`, `P4_Eliminates_Pi11.v`, `P4ProhibitsImpredicative.v`,
`P4ProhibitsAC.v`. Цена всех лемм этих файлов, кроме `P4_Eliminates_Pi11.v`, — Closed.

**(б) Поправить слова:**

> файлы `P4_Eliminates_*.v` и `P4Prohibits*.v` — ATR, Бесконечность, импредикативность

---

## Сомнительные места, которые расхождением не являются

- Стр. 56, «несчётность $[0,1]$ (трисекция)»: теорема дана для перечислений регулярных процессов Коши
  (`valid_regular_enumeration`); в ячейке таблицы условие не названо. Сверяется в ведомости главы X.2.
- Стр. 59, «0 логич. аксиом»: верно для итоговой `P4_eliminates_Pi11`; лемма `pi11_negation` того же файла опирается
  на `Classical_Prop.classic`. Сама итоговая теорема — развёртка определения `P4_forall_functions` (предмет X.5).
- Стр. 60: ярус `PBoundary` в реестре означает «не построено», а на странице в той же строке стоит «P4-запрет»;
  «завершённый граф-выбора» в реестре строки не имеет. Запрет — отдельная теорема.
- Стр. 66–71: «„Полная AC“ … не точки нашего пространства». В реестре функциональный выбор по произвольному семейству
  — доказанное следствие формулировки L4 (`l4_statement_gives_functional_choice`), то есть высказывание внутри
  формализации. Философский тезис не оценивался.
- Стр. 90–91: при «завершённом графе выбора» названа общая теорема `completed_inf_contradicts_P4`; точное имя для
  графа — `completed_graph_contradicts_P4` (`P4ProhibitsAC.v:108`). Она верна для графа любой всюду определённой
  функции и дана при условии `bridge` (все индексы актуальны на стадии 0); шапка файла это оговаривает.
- Стр. 99–103: пересказ таблицы `tos_verdict` дан в изъявительном наклонении («заменены P4»); глава называет его
  аудитом, сноска — классификацией. Леммы-якоря есть у четырёх вердиктов из девяти; у `Replacement` и трёх
  «тривиальных» ссылки на доказанное нет.
- Стр. 111–113: «не привлечённые процессные конструкции» — в таблице `status` у этих двух стен стоит
  `PartiallyReached` («нижние рунги построены»); полные формы действительно не построены.
- Стр. 171: `is_wqo` требует только хорошую пару в каждой последовательности; рефлексивность и транзитивность
  отношения в определение не входят (то же в `KruskalTree.v:28`).
- Стр. 173: «`CB_deriv` (удаление изолированных точек)» — определение оставляет точки накопления; с удалением
  изолированных это совпадает при исключённом третьем. «Замкнутого множества» (стр. 35) — в определениях замкнутость
  не участвует.
- Стр. 177: `bool_pigeonhole3` названа «конечным голубятным ядром wqo» — лемма о трёх булевых значениях, об
  упорядочениях и последовательностях она не говорит.
- Стр. 175, «а не новая математика»: в файле есть три доказанные леммы о силе L4, которых страница не упоминает.

## Наблюдения о формализации, не относящиеся к словам страницы

- `ChoicePriceMap.v`: у `RFiniteChoice` не названа опорная теорема; у `RFunctionalChoice` названная лемма замкнута
  (L4 — посылка); `proven_results_below_boundary` перечисляет десять строк из пятнадцати.
- Устаревшие шапки: `TransfiniteInduction.v` («Print Assumptions: classic, L4_witness» — по компилятору Closed);
  `KruskalFull.v` («Bounded-depth trees (by Higman on child lists)» — доказано сведением к `wqo_nat_le`; «15 Qed»);
  `KruskalTree.v`, `CantorBendixsonFull.v`, `BorelDeterminacy.v`, `ZFCAxiomLedger.v` — счёт Qed;
  `CardinalityWithoutChoice.v` — замечание о том, что L4 обращает только биекции (расхождение 4).
- `ToS_Axioms.v`, стр. 72–100 («This is NOT the Axiom of Choice … L4_witness extracts a witness from a SINGLE
  existential») расходится с леммой реестра `l4_statement_gives_functional_choice`: применённое к каждому индексу
  семейства, извлечение свидетеля даёт функцию выбора.
- `CB_omega_stable` (`CantorBendixsonFull.v:112`) и `P1_blocks_russell` (`P4ProhibitsImpredicative.v:56`) возвращают
  собственную посылку.
- В `BorelDeterminacy.v` объявлена своя `Axiom classic` (:21) — отдельное объявление того же высказывания.
