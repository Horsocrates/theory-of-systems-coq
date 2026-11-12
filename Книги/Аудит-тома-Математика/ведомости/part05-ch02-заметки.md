# Глава V.2 «Топология и компактность» — заметки к ведомости (12.11.2026)

Ведомость: `part05-ch02.json` — 122 ручные записи + 14 автоматических; `merge --dry` проходит без замечаний,
список «без сверки» пуст. Вердикты (вместе с автоматическими): ok — 110, mismatch-statement — 21,
mismatch-price — 2, wrong-number — 1, missing-name — 2 (оба — имена, разорванные переносом строки).
21 запись о формулировке — это 13 разных мест по существу (расхождения 1–13 ниже; несколько записей повторяют
одно и то же слово в разных местах главы), две записи о цене — расхождения 14 и 15, число — расхождение 16.

Главное. Цена названа верно почти везде: топологический слой — без допущений (все 68 объявлений трёх файлов),
восстановленный Гейне — Борель — без допущений, Больцано — Вейерштрасс — на `classic` и `L4_witness`. Все 16 блоков
кода совпадают с исходниками. Условие теоремы Гейне — Бореля (равномерность покрытия) в главе названо.
Расхождения — в пересказе формулировок: предикат точки сгущения слабее слов главы; процессная обёртка
Больцано — Вейерштрасса теорему не переносит; «путь-достижимость» выполнена для всякого множества;
шар на классах замкнутый, а назван открытым; «число Лебега» — на деле более сильное условие.
Почти всё доводится до слов главы делом — без новых аксиом; наброски проверены компилятором.

## Что проверить не удалось

- Ссылки на номера параграфов (§ 2.1, § 2.2.4, § 2.5, § 2.7.2 и другие): заголовки страницы без номеров,
  соответствие сверялось по смыслу.
- Счёт «одиннадцать файлов — шесть основных и пять обёрток» (стр. 99–100): глава не даёт списка, восстановить
  авторский счёт однозначно не удалось; записано как расхождение в числе с оговоркой (расхождение 16).
- Контрпример главы с иррациональным α (стр. 501–528) буквально в формализацию не переносится: радиус
  ½|x − α| иррационален, а покрытие в файле — функция `Q -> Q`. Рассуждение проверено вручную; рациональный
  аналог проверен компилятором (расхождение 13).
- «ℚ вполне несвязно» (стр. 901–905) — математический факт без теоремы в формализации; компилятором не
  проверялся (глава его формализации и не приписывает).
- Невыводимость: что теорему Больцано — Вейерштрасса нельзя доказать без `L4_witness` (расхождение 14, пункт «а»),
  компилятором не проверяется — это оценка.
- Английская страница и LaTeX-исходник главы не смотрелись.

## Что было известно заранее — итог сверки

- **Цена бисекции Больцано — Вейерштрасса (стр. 1016, не сверено 12.11).** Сверено, слова верны:
  `Print Assumptions bolzano_weierstrass` — `Classical_Prop.classic : forall P : Prop, P \/ ~ P` и
  `ToS_Axioms.L4_witness : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A | P x}`.
  То же у `bw_step`, `bw_iter`, у 24 объявлений `BolzanoWeierstrass.v` из 34 и у 9 объявлений `ProcessBW.v`
  из 12. Только на `classic` стоят `infinite_pigeonhole`, `monotone_bounded_cauchy`, `decreasing_bounded_cauchy`.
  Уточнение — расхождение 14: `L3_informative` сама стоит на обоих допущениях.
- **`process_BW`.** Заключение слабее пересказа главы — расхождение 2.
- **Гейне — Борель и число Лебега.** Условие в главе названо (стр. 545–600, 970, 1009). Формально оно —
  общая нижняя граница радиусов, что сильнее числа Лебега, — расхождение 6. Цена (`Heine_Borel`,
  `Heine_Borel_uniform` — `Closed under the global context`) подтверждена.
- **Слова о цене, правленные 12.11 (стр. 44–45, 611–615).** Верны; `not_coverable_half` — единственное из 46
  объявлений `HeineBorel_ERR.v` с допущением (`classic`), и в зависимости теорем Гейне — Бореля оно не входит
  (`Print All Dependencies Heine_Borel_uniform`).

## Расхождение 1. Точка сгущения: предикат слабее слов главы (стр. 768–771, 861–863)

**Было (стр. 768–771):**

> Коши-совместимую форму. В терминах ToS, где предел — это процесс:
> всякая ограниченная последовательность рациональных чисел имеет
> *точку сгущения* — процесс Коши, к которому члены
> последовательности с большими индексами сколь угодно приближаются.

**Было (стр. 861–863):**

> Предикат `is_cluster_point` определён Коши-совместимо:
> для любой точности и любого порога найдётся член последовательности с
> большим индексом, лежащий к точке сгущения ближе требуемого.

Проверка. `is_cluster_point` (`src/analysis/BolzanoWeierstrass.v:430`):
`forall eps, 0 < eps -> forall N, exists k, exists M, (N <= k)%nat /\ Qabs (cs_seq L M - s k) < eps`.
Номер `M` стоит под квантором существования и снизу не ограничен: требуется близость члена последовательности
к одному какому-нибудь члену процесса `L`, а не к далёким его членам, то есть не к точке. Проверено компилятором
(`Closed under the global context`): для последовательности из одних нулей и процесса `L = (0, 1, 1, 1, …)`,
который задаёт точку 1, предикат выполнен (`M = 0`); для эквивалентного ему постоянного процесса 1 предикат
ложен. Значит, это свойство представителя, а не точки.

Простыми словами: глава говорит «члены последовательности подходят сколь угодно близко к точке», а записано
«подходят близко к какому-то члену процесса»; доказательство при этом устанавливает сильное свойство, слаба только запись.

**(а) Довести формализацию.** Возможно, без новых допущений. Набросок проверен
(`_part05/ch02/CheckBW.v`; `Print Assumptions bolzano_weierstrass_strong` — те же `classic` и `L4_witness`,
остальные три леммы — `Closed under the global context`):

```coq
Definition is_cluster_point_strong (s : nat -> Q) (L : CauchySeq) : Prop :=
  forall eps : Q, 0 < eps ->
    exists M0 : nat, forall M : nat, (M0 <= M)%nat ->
      forall N : nat, exists k : nat, (N <= k)%nat /\ Qabs (cs_seq L M - s k) < eps.

Lemma strong_implies_weak : forall s L, is_cluster_point_strong s L -> is_cluster_point s L.

(* свойство точки, а не представителя *)
Lemma strong_cluster_invariant : forall s (L L' : CauchySeq),
  cauchy_equiv L L' -> is_cluster_point_strong s L -> is_cluster_point_strong s L'.

Theorem bolzano_weierstrass_strong : forall (s : nat -> Q) (a b : Q),
  a < b -> bounded_seq s a b ->
  exists L : CauchySeq, is_cluster_point_strong s L.
Proof.
  intros s a b Hab Hbnd.
  assert (Hvalid : a <= b) by lra.
  exists (mkCauchy _ (bw_left_cauchy s a b Hab)).
  intros eps Heps.
  destruct (bw_width_to_zero s a b Hab eps Heps) as [M0 HM0].
  exists M0. intros M HM N.
  destruct (bw_infinitely_many s a b M0 Hvalid Hbnd N) as [k [HkN [Hklo Hkhi]]].
  exists k. split; [exact HkN|].
  change (Qabs (bw_left (bw_iter s (mkBW a b) M) - s k) < eps).
  pose proof (bw_left_mono s a b Hvalid M0 M HM) as H1.
  pose proof (bw_right_mono s a b Hvalid M0 M HM) as H3.
  assert (H2 : bw_left (bw_iter s (mkBW a b) M) <= bw_right (bw_iter s (mkBW a b) M)).
  { apply bw_iter_valid. exact Hvalid. }
  apply Qabs_lt_bound; lra.
Qed.
```

Почему верно: член последовательности берётся из интервала уровня `M0` шириной меньше `eps`, а все левые концы
уровней `M >= M0` лежат в том же интервале. Достаточно заменить определение `is_cluster_point` сильным (старое
из него следует) — слова главы тогда верны без правки.

**(б) Поправить слова.** Стр. 768–771, стало:

> Коши-совместимую форму. В терминах ToS, где предел — это процесс:
> всякая ограниченная последовательность рациональных чисел имеет
> *точку сгущения* — процесс Коши, к членам которого члены
> последовательности с большими индексами сколь угодно приближаются.

Стр. 861–863, стало:

> Предикат `is_cluster_point` записан в слабой форме: для любой точности и любого порога найдутся член
> последовательности с большим индексом и член процесса-предела, отстоящие друг от друга меньше требуемого.
> Близости к *далёким* членам процесса — то есть к самой точке — запись не требует, хотя доказательство её
> даёт: член последовательности берётся из того же интервала бисекции, где лежат все дальнейшие левые концы.

## Расхождение 2. Процессная обёртка теорему не переносит (стр. 875–876, 879–881)

**Было:**

> Теорема `bw_is_process_construction` собирает это в единую
> картину E/R/R

> Аксиомного основания процессная обёртка не меняет: она ничего не
> добавляет и не убавляет, перенося на язык процессов теорему, как она
> есть — доказанную, с опорой на $L3$ и $L4$.

Проверка. `process_BW` (`src/process/ProcessBW.v:136`):
`a < b -> bounded_seq s a b -> exists L : RealProcess, ProcessCore.is_Cauchy L`; в доказательстве свойство точки
сгущения отброшено (`destruct (bolzano_weierstrass …) as [L _]`). `bw_is_process_construction` (`:152`):
`a < b -> bounded_seq s a b -> exists left_proc right_proc, monotone_increasing left_proc /\ monotone_decreasing right_proc /\ is_Cauchy left_proc /\ is_Cauchy right_proc /\ process_equiv left_proc right_proc`
— процессы стоят под квантором существования и с `s` не связаны; посылка `bounded_seq` в доказательстве не
используется. Оба заключения доказываются для нулевого процесса без посылок и без допущений
(`process_BW_conclusion_free`, `bw_construction_conclusion_free` — `Closed under the global context`), тогда
как у самих теорем в выводе компилятора `classic` и `L4_witness`. Леммы о конкретных процессах концов
(`bw_left_increasing :84`, `bw_right_decreasing :94`, `bw_left_is_cauchy_process :64`,
`bw_right_is_cauchy_process :74`, `bw_endpoints_equiv :104`) честны, и фраза главы о них (стр. 871–874) верна.

Простыми словами: обе сводные теоремы утверждают только «существует процесс Коши» и «существует пара
монотонных эквивалентных процессов» — это верно для любой последовательности и без бисекции; о точке сгущения
в процессном файле не сказано ничего. Цена (L3 и L4) при этом названа верно.

**(а) Довести формализацию.** Возможно; набросок проверен (`_part05/ch02/CheckProcBW.v`, допущения — те же
`classic` и `L4_witness`):

```coq
Theorem bw_is_process_construction_strong : forall s a b,
  a < b -> bounded_seq s a b ->
    monotone_increasing (bw_left_process s a b) /\
    monotone_decreasing (bw_right_process s a b) /\
    ProcessCore.is_Cauchy (bw_left_process s a b) /\
    ProcessCore.is_Cauchy (bw_right_process s a b) /\
    process_equiv (bw_left_process s a b) (bw_right_process s a b) /\
    (forall n, infinitely_many_in s (bw_left_process s a b n) (bw_right_process s a b n)).
Proof.
  intros s a b Hab Hbnd.
  split; [| split; [| split; [| split; [| split]]]].
  - apply bw_left_increasing; assumption.
  - apply bw_right_decreasing; assumption.
  - apply bw_left_is_cauchy_process; assumption.
  - apply bw_right_is_cauchy_process; assumption.
  - apply ProcessBW.bw_endpoints_equiv; assumption.
  - intro n. unfold bw_left_process, bw_right_process.
    apply bw_infinitely_many; [lra | exact Hbnd].
Qed.

Theorem process_BW_strong : forall (s : nat -> Q) (a b : Q),
  a < b -> bounded_seq s a b ->
  exists L : RealProcess,
    ProcessCore.is_Cauchy L /\
    forall eps : Q, 0 < eps ->
      exists M0 : nat, forall M : nat, (M0 <= M)%nat ->
        forall N : nat, exists k : nat, (N <= k)%nat /\ Qabs (L M - s k) < eps.
```

(доказательство второй — то же, что у `bolzano_weierstrass_strong`, со свидетелем `bw_left_process s a b`).
Здесь посылка `bounded_seq` работает: она даёт «населённость» каждого интервала.

**(б) Поправить слова.** Стр. 875–877, стало:

> Теорема `bw_is_process_construction` записывает существование пары процессов с этими свойствами, а
> `bw_convergence_rate` называет скорость — $1/2$: интервал на каждом шаге уполовинивается.

Стр. 879–883, стало:

> Аксиомного основания процессная обёртка не меняет: свойства процессов концов стоят на тех же $L3$ и $L4$.
> Саму теорему о точке сгущения обёртка на язык процессов пока не переносит: `process_BW` утверждает лишь
> существование процесса Коши, без связи с последовательностью. Заголовок `ProcessBW.v` называет
> унаследованное: *«classic (inherited from BolzanoWeierstrass)»*.

## Расхождение 3. `bw_convergence_rate` — число, вписанное руками (стр. 876–877)

**Было:** «а `bw_convergence_rate` фиксирует скорость — $1/2$: интервал на каждом шаге уполовинивается»

Проверка. `Definition bw_convergence_rate : Q := 1 # 2.` (`ProcessBW.v:173`); единственная лемма о нём —
`bw_rate_valid : 0 < bw_convergence_rate /\ bw_convergence_rate < 1` (`:175`). С бисекцией константа не связана
ни одной леммой. Сам факт уполовинивания доказан: `bw_step_width` (`BolzanoWeierstrass.v:138`).

Простыми словами: «фиксирует скорость» здесь значит «названо число 1/2»; что это скорость именно этой бисекции,
в файле не утверждается.

**(а) Довести формализацию.** Одна лемма; набросок проверен (`CheckProcBW.v`, допущения `classic`,
`L4_witness` — от `bw_step` в утверждении):

```coq
Lemma bw_rate_is_step_ratio : forall s st,
  bw_right (bw_step s st) - bw_left (bw_step s st) ==
  bw_convergence_rate * (bw_right st - bw_left st).
Proof. intros s st. rewrite bw_step_width. unfold bw_convergence_rate. field. Qed.
```

**(б) Поправить слова** — как в расхождении 2 («называет скорость»), со ссылкой на `bw_step_width`.

## Расхождение 4. «Путь-достижимость» выполнена для всякого множества (стр. 944–945; задевает 936–942, 1007)

**Было:** «`interval_path_connected` даёт процессную достижимость для замкнутого интервала»

Проверка. `interval_path_connected` (`src/process/ProcessTopConnected.v:111`):
`lo < hi -> is_path_connected (fun x => lo <= x /\ x <= hi)` — верно. Но `is_path_connected` (`:106`) требует
лишь отображения `gamma : Q -> Q` с `gamma 0 == a`, `gamma 1 == b` и значениями в `S` при `0 <= t <= 1`. Без
непрерывности годится путь «`a` при `t < 1`, `b` при `t = 1`». Проверено компилятором
(`Closed under the global context`):

```coq
Lemma any_set_path_connected : forall S : Q -> Prop, is_path_connected S.
Proof.
  intros S a b Ha Hb.
  exists (fun t => if Qlt_le_dec t 1 then a else b).
  unfold PathIn. split; [| split].
  - destruct (Qlt_le_dec 0 1) as [H | H]; [reflexivity | lra].
  - destruct (Qlt_le_dec 1 1) as [H | H]; [lra | reflexivity].
  - intros t _ _. destruct (Qlt_le_dec t 1); assumption.
Qed.
```

Простыми словами: глава честно говорит, что непрерывность не требуется, но из этого следует больше, чем сказано:
свойство есть у любого множества, в том числе у двухточечного {0, 1}; теорема об интервале ничего об интервале
не сообщает.

**(а) Довести формализацию.** Возможно: потребовать от пути липшицевости по параметру (для линейного пути она
в файле уже доказана — `linear_path_lipschitz`). Набросок проверен (`_part05/ch02/CheckTop.v`, все три
утверждения — `Closed under the global context`):

```coq
Definition LipPathIn (S : Q -> Prop) (gamma : Q -> Q) (a b : Q) : Prop :=
  PathIn S gamma a b /\
  exists K : Q, 0 <= K /\ forall s t : Q, Qabs (gamma s - gamma t) <= K * Qabs (s - t).

Definition is_lip_path_connected (S : Q -> Prop) : Prop :=
  forall a b, S a -> S b -> exists gamma, LipPathIn S gamma a b.

Theorem interval_lip_path_connected : forall lo hi,
  lo < hi -> is_lip_path_connected (fun x => lo <= x /\ x <= hi).

Theorem two_points_not_lip_path_connected :
  ~ is_lip_path_connected (fun x => x == 0 \/ x == 1).
```

Первая — линейным путём с константой `Qabs (b - a)`. Вторая — шагом по сетке `k/(n+1)` при `n + 1 > K`: соседние
значения пути отличаются меньше чем на 1, поэтому из 0 в 1 путь перейти не может (вспомогательная лемма
`lip_no_jump`, индукция по `k`; полный текст — в пробном файле). С таким определением свойство различает
интервал и двухточечное множество.

**(б) Поправить слова.** Стр. 944–945, стало:

> пути обращаются и склеиваются; `interval_path_connected`
> даёт процессную достижимость для замкнутого интервала (в принятом определении, без требования
> непрерывности, достижимо всякое множество — путь вправе перескочить из $a$ в $b$ в последней точке
> параметра; содержание несут леммы о линейном пути: он остаётся в интервале и липшицев по $t$); процессная

## Расхождение 5. `process_path_cauchy`: сходимость к $b$ не записана (стр. 948–949)

**Было:** «`process_path_cauchy` показывает, что этот процесс есть Коши и сходится к $b$»

Проверка. `process_path_cauchy : forall a b, is_Cauchy (process_path a b)` (`ProcessTopConnected.v:258`) —
в утверждении только свойство Коши. Сходимость к `b` стоит в комментарии и видна внутри доказательства
(`|path(n) − b| = |a − b|/(n+1)`), отдельной леммы нет.

**(а) Довести формализацию.** Набросок проверен (`CheckTop.v`, `Closed under the global context`):

```coq
Lemma process_path_converges : forall a b eps, 0 < eps ->
  exists N : nat, forall n : nat, (N <= n)%nat -> Qabs (process_path a b n - b) < eps.
Proof.
  intros a b eps Heps.
  destruct (Qeq_dec a b) as [Hab | Hab].
  - exists 0%nat. intros n _.
    assert (E : process_path a b n - b == 0).
    { unfold process_path, linear_path. rewrite Hab. ring. }
    rewrite (Qabs_wd _ _ E). simpl. exact Heps.
  - assert (Habs_pos : 0 < Qabs (a - b)).
    { destruct (Qlt_le_dec (a - b) 0); [rewrite Qabs_neg | rewrite Qabs_pos]; lra. }
    destruct (archimedean_witness (Qabs (a - b)) eps Habs_pos Heps) as [N HN].
    exists N. intros n Hn.
    assert (Hn1 : 0 < inject_Z (Z.of_nat n) + 1) by (unfold Qlt; simpl; lia).
    assert (Hinv : 0 < / (inject_Z (Z.of_nat n) + 1)) by (apply Qinv_lt_0_compat; exact Hn1).
    assert (Hd : process_path a b n - b == (a - b) * / (inject_Z (Z.of_nat n) + 1)).
    { unfold process_path, linear_path. field. lra. }
    rewrite (Qabs_wd _ _ Hd). rewrite Qabs_Qmult.
    rewrite (Qabs_pos (/ (inject_Z (Z.of_nat n) + 1))) by lra.
    exact (HN n Hn).
Qed.
```

**(б) Поправить слова.** Стало: «`process_path_cauchy` показывает, что этот процесс есть Коши (из доказательства
видно и куда он сходится: расстояние до $b$ на шаге $n$ равно $|a-b|/(n+1)$)».

## Расхождение 6. «Число Лебега» — на деле более сильное условие (стр. 565–567, 598–600; те же слова на 553, 587–589, 594, 1009)

**Было (стр. 565–567):**

> радиусом. Радиусы не могут «выдохнуться» — у всех есть общая
> нижняя граница. Это и есть число Лебега: масштаб, на котором покрытие
> работает *равномерно* по всему интервалу.

**Было (стр. 598–600):**

> Это честный ремонт: теорема восстановлена на том классе покрытий, на
> котором она вообще верна над $ℚ$.

Проверка. `uniform_cover C a b delta := delta > 0 /\ forall x, a <= x <= b -> C x >= delta`
(`src/HeineBorel_ERR.v:84`) — общая нижняя граница радиусов. Число Лебега в том же файле определено отдельно:
`has_lebesgue_number` (`:118`) — у каждой точки `x` отрезка её `delta`-окрестность лежит в одном шаре покрытия;
в теореме оно не участвует (в `ProcessHB.v` о нём две служебные леммы). Проверено компилятором
(`_part05/ch02/CheckHB.v`, всё — `Closed under the global context`): `uniform_cover` влечёт
`has_lebesgue_number` с тем же `delta`; обратное неверно — у покрытия отрезка [0,1] с `C(0) = 10`,
`C(x) = |x|` при `x ≠ 0` число Лебега есть (`delta = 1`), а `uniform_cover` не выполнен ни при каком `delta`,
и конечное подпокрытие у него есть.

Простыми словами: теорема доказана для покрытий, у которых все радиусы не меньше δ; покрытий с числом Лебега
больше, и для них теорема тоже верна, но в формализации не записана. Слова «на том классе, на котором она вообще
верна» поэтому сильнее доказанного: условие достаточное, не необходимое.

**(а) Довести формализацию.** Возможно, без допущений; набросок проверен:

```coq
Lemma uniform_cover_has_lebesgue : forall C a b delta,
  uniform_cover C a b delta -> has_lebesgue_number C a b delta.

Lemma HB_lebesgue_by_depth : forall N C a b delta,
  has_lebesgue_number C a b delta ->
  forall a' b', a <= a' -> a' <= b' -> b' <= b ->
    (b' - a') / Qpow2 N < delta -> coverable C a' b'.
Proof.
  induction N as [|N IH]; intros C a b delta Hleb a' b' Haa Hab' Hbb Hw.
  - destruct Hleb as [Hd Hl].
    assert (E : (b' - a') / Qpow2 0 == b' - a') by (unfold Qpow2; simpl; field).
    rewrite E in Hw.
    destruct (Hl a' ltac:(split; lra)) as [c [_ Hc]].
    exists [c]. intros y [Hy1 Hy2]. simpl. left. apply Hc.
    rewrite Qabs_pos by lra. lra.
  - set (m := (a' + b') / 2).
    assert (Em : m == (a' + b') * (1#2)) by (unfold m; field).
    assert (Hm1 : a' <= m) by lra.
    assert (Hm2 : m <= b') by lra.
    assert (HwL : (m - a') / Qpow2 N < delta).
    { assert (E : (m - a') / Qpow2 N == (b' - a') / Qpow2 (S N)).
      { rewrite <- div_half_pow2. assert (E2 : m - a' == (b' - a') / 2) by (unfold m; field).
        rewrite E2. reflexivity. }
      rewrite E. exact Hw. }
    assert (HwR : (b' - m) / Qpow2 N < delta).
    { assert (E : (b' - m) / Qpow2 N == (b' - a') / Qpow2 (S N)).
      { rewrite <- div_half_pow2. assert (E2 : b' - m == (b' - a') / 2) by (unfold m; field).
        rewrite E2. reflexivity. }
      rewrite E. exact Hw. }
    apply coverable_concat with m.
    + apply (IH C a b delta Hleb a' m); lra.
    + apply (IH C a b delta Hleb m b'); lra.
Qed.

Theorem Heine_Borel_lebesgue : forall (C : OpenCover) (a b delta : Q),
  a < b ->
  has_lebesgue_number C a b delta ->
  exists centers : FiniteSubcover, covers_interval C centers a b.
Proof.
  intros C a b delta Hab Hleb.
  assert (Hd : 0 < delta) by (destruct Hleb as [Hd _]; exact Hd).
  assert (Hw : b - a > 0) by lra.
  destruct (pow2_eventually_large (b - a) delta Hw Hd) as [N HN].
  apply (HB_lebesgue_by_depth N C a b delta Hleb a b); [lra | lra | lra | exact HN].
Qed.
```

С этой теоремой слова «при наличии числа Лебега конечное подпокрытие существует» (стр. 587, 594, 1009)
становятся буквально верными, а `Heine_Borel_uniform` — её следствием. Слова стр. 598–600 править всё равно
нужно: и число Лебега — условие достаточное.

**(б) Поправить слова.** Стр. 565–567, стало:

> радиусом. Радиусы не могут «выдохнуться» — у всех есть общая
> нижняя граница. Такое $\delta$ служит числом Лебега покрытия: всякий кусок интервала уже $\delta$ целиком
> лежит в одном шаре. (Условие взято с запасом: число Лебега бывает и у покрытий, чьи радиусы от нуля не
> отделены; теорема доказана для равномерных.)

Стр. 598–600, стало:

> Это честный ремонт: теорема восстановлена на классе покрытий, для
> которого она над $ℚ$ заведомо верна.

## Расхождение 7. `hb_step` в выводе теоремы не участвует (стр. 575–577)

**Было:** «Этот вывод формализован в `HeineBorel_ERR.v` (бисекционный спуск — `hb_step`, `Qpow2`, `Heine_Borel_by_depth`)»

Проверка. `Heine_Borel_by_depth` (`HeineBorel_ERR.v:449`) делит отрезок прямой индукцией по глубине и на
`hb_step` (`:156`) не ссылается. `Print All Dependencies Heine_Borel_uniform` называет `Qpow2`,
`Heine_Borel_by_depth`, `pow2_eventually_large`, `coverable_concat`, `cover_concat`, `small_interval_coverable`,
`div_half_pow2`, `Qabs_diff_le_width` — и не называет `hb_step`, `hb_width`, `hb_step_halves`. Эти три
объявления — отдельная нить файла, на которую ничто не опирается. Место мелкое.

**(а)** Доводить нечего: теорема доказана, перестраивать доказательство ради имени незачем.

**(б) Стало:** «Этот вывод формализован в `HeineBorel_ERR.v` (спуск по глубине бисекции — `Qpow2`,
`pow2_eventually_large`, `Heine_Borel_by_depth`)».

## Расхождение 8. `p4_cover_finite` верна для любого списка (стр. 274–275, 365–366)

**Было (стр. 365–366):** «Существенно, что на каждом уровне покрытие *конечно* — список конечной длины; это устанавливает лемма `p4_cover_finite`.»

**Было (стр. 274–275):** «всякий его кадр конечен и обозрим (лемма `p4_cover_finite`)»

Проверка. `p4_cover_finite : forall (op : OpenProcess) n, op n = nil \/ exists b rest, op n = cons b rest`
(`src/process/ProcessTopOpen.v:258`). «Список пуст или имеет голову» верно для любого списка любого типа
(`any_list_nil_or_cons`, проверено). Конечность кадра дана типом `QBallCover := list (Q * Q)`; лемма к ней ничего
не добавляет (комментарий в файле это отчасти признаёт: прежняя формулировка названа там пустой).

**(а) Довести формализацию.** Содержательное следствие конечности кадра — он покрывает лишь ограниченное
множество (у бесконечного семейства шаров этого свойства нет). Набросок проверен (`CheckTop.v`,
`Closed under the global context`):

```coq
Lemma cover_frame_bounded : forall bc : QBallCover,
  exists M : Q, 0 < M /\ forall x, covered_by_balls bc x -> Qabs x < M.
Proof.
  induction bc as [| [c r] rest IH].
  - exists 1. split; [lra|]. intros x [p [Hin _]]. destruct Hin.
  - destruct IH as [M [HM HB]].
    exists (M + Qabs c + Qabs r). split.
    + pose proof (Qabs_nonneg c). pose proof (Qabs_nonneg r). lra.
    + intros x [p [Hin [Hpos Hball]]].
      pose proof (Qabs_nonneg c) as Hc. pose proof (Qabs_nonneg r) as Hr.
      destruct Hin as [Heq | Hin].
      * subst p. simpl in Hpos, Hball. unfold in_ball in Hball.
        assert (Htri : Qabs x <= Qabs (x - c) + Qabs c).
        { assert (E : x == (x - c) + c) by ring.
          rewrite (Qabs_wd _ _ E) at 1. apply Qabs_triangle. }
        assert (Hrr : r <= Qabs r) by apply Qle_Qabs.
        lra.
      * assert (Hx : Qabs x < M).
        { apply HB. exists p. split; [exact Hin | split; assumption]. }
        lra.
Qed.
```

Заодно первая лемма об `is_refining`, которых сейчас нет ни одной (проверена там же):
`refining_monotone : is_refining op -> (n <= m)%nat -> covered_by_balls (op n) x -> covered_by_balls (op m) x`.

**(б) Поправить слова.** Стр. 365–366, стало:

> Существенно, что на каждом уровне покрытие *конечно*: кадр `op n` — значение типа `QBallCover`, то есть
> конечный список (лемма `p4_cover_finite` лишь разворачивает это: список пуст либо имеет голову и хвост).

Стр. 274–275, стало: «всякий его кадр конечен и обозрим (кадр — конечный список, тип `QBallCover`)».

## Расхождение 9. Прообраз открытого: доказана одна сторона (стр. 186–189)

**Было:**

> `continuous_preserves_open_preimage`: прообраз открытого
> множества под непрерывным отображением открыт. Это топологическое
> *определение* непрерывности в эквивалентной форме; к нему
> подробно вернётся Глава 5.3.

Проверка. `continuous_preserves_open_preimage : forall f, continuous f -> forall S, is_open S -> is_open (fun x => S (f x))`
(`src/stdlib/Topology.v:235`). Обратной стороны в формализации нет (слово «preimage» в `src/stdlib` и
`src/analysis` встречается только здесь).

**(а) Довести формализацию.** Набросок проверен (`CheckTop.v`, `Closed under the global context`):

```coq
Lemma open_preimage_implies_continuous : forall f : Q -> Q,
  (forall S, is_open S -> is_open (fun x => S (f x))) -> continuous f.
Proof.
  intros f H x eps Heps.
  assert (Hb : is_open (open_ball (f x) eps)) by (apply open_ball_is_open; exact Heps).
  destruct (H _ Hb x (open_ball_center (f x) eps Heps)) as [delta [Hd Hin]].
  exists delta. split; [exact Hd|].
  intros y Hy. apply (Hin y). exact Hy.
Qed.

Theorem continuous_iff_open_preimage : forall f : Q -> Q,
  continuous f <-> (forall S, is_open S -> is_open (fun x => S (f x))).
```

**(б) Поправить слова.** Стало: «…открыт. Это одна сторона топологического *определения* непрерывности
(обратная — из открытости прообразов следует непрерывность — в файле не записана); к нему подробно вернётся
Глава 5.3.»

## Расхождение 10. Шар на классах замкнутый, назван открытым (стр. 202–203, 1021, 1060–1061)

**Было:** «там определён открытый шар на классах `rp_in_ball` (центр — точка, радиус — рациональное)»;
«открытый шар `rp_in_ball` с корректностью» (дважды).

Проверка. `rp_in_ball c r x := cauchy_le (rp_dist c x) (cauchy_const r)` (`src/RealPointTopology.v:75`):
расстояние не больше `r`. Сам файл называет шар замкнутым (строки 71–74). Проверено (`_part05/ch02/CheckRP.v`,
`Closed under the global context`): `rp_in_ball (cauchy_const 0) 1 (cauchy_const 1)` — точка на расстоянии
ровно 1 шару радиуса 1 принадлежит.

**(а) Довести формализацию.** Открытый шар определяется через замкнутый меньшего радиуса; набросок проверен,
все леммы — `Closed under the global context`:

```coq
Definition rp_in_open_ball (c : RealPoint) (r : Q) (x : RealPoint) : Prop :=
  exists q : Q, q < r /\ rp_in_ball c q x.

Lemma rp_in_open_ball_well_defined : forall (c : RealPoint) (r : Q) (x x' : RealPoint),
  x ~~ x' -> (rp_in_open_ball c r x <-> rp_in_open_ball c r x').

Lemma rp_in_open_ball_centre : forall (c : RealPoint) (r : Q), 0 < r -> rp_in_open_ball c r c.

Lemma rp_open_ball_excludes_boundary : ~ rp_in_open_ball (cauchy_const 0) 1 (cauchy_const 1).

(* открытый шар открыт: с каждой точкой он содержит шар положительного радиуса вокруг неё *)
Lemma rp_open_ball_is_open : forall (c : RealPoint) (r : Q) (x : RealPoint),
  rp_in_open_ball c r x ->
  exists e : Q, 0 < e /\ forall y : RealPoint, rp_in_ball x e y -> rp_in_open_ball c r y.
```

Последняя лемма — первый шаг к открытым множествам на классах, которые глава называет направлением дальнейшей
работы.

**(б) Поправить слова.** Во всех трёх местах «открытый шар» заменить на «замкнутый шар»; в стр. 202 можно
добавить: «(расстояние до центра не больше радиуса)».

## Расхождение 11. «Три лица»: теоремы формулировок не связывают (стр. 973–976)

**Было:**

> завершается за конечное число шагов. Три формулировки об одном; в
> `ProcessTopCompact.v` их единство закреплено теоремой
> `p4_compactness_summary`, а `compact_eq_noetherian`
> и `compact_eq_hb` связывают их попарно.

Проверка (`src/process/ProcessTopCompact.v`). `p4_compactness_summary` (`:234`) — конъюнкция трёх независимых
утверждений: `interval_compact a b` при `a < b`; ограниченная возрастающая цепь натуральных чисел
стабилизируется; стабилизировавшаяся цепь даёт процесс Коши. `compact_eq_noetherian` (`:218`) — нётеровость и
её следствие для процессов, о покрытиях в утверждении ничего нет. `compact_eq_hb` (`:228`) —
`a < b -> interval_compact a b`, то есть сама теорема Гейне — Бореля (`interval_compact` определён её
утверждением). Ни равносильности, ни следования одной формулировки из другой нигде нет; третий член сводки — не
«терминация построения». Допущения: `classic` у первой и второй (от нётеровости), `compact_eq_hb` — без допущений.
Следующий абзац главы (стр. 978–982) сам называет сводные теоремы конъюнкциями — это честно; расходятся только
слова «единство закреплено» и «связывают попарно».

**(а) Довести формализацию.** Честной теоремы о равносильности здесь нет: Гейне — Борель говорит о покрытиях
отрезка, нётеровость — о цепях натуральных чисел, общего объекта у утверждений нет, и связать их можно только
искусственной конструкцией. Связь «Гейне — Борель — это остановка бисекции на конечной глубине» в формализации
уже есть, но не в этих теоремах, а в самом доказательстве: `pow2_eventually_large` (нужная глубина существует)
и `Heine_Borel_by_depth` (на этой глубине отрезок покрыт).

**(б) Поправить слова.** Стало:

> завершается за конечное число шагов. Три формулировки глава читает как одно; в
> `ProcessTopCompact.v` они стоят рядом в теореме-конъюнкции
> `p4_compactness_summary`; `compact_eq_hb` повторяет Гейне–Бореля в терминах `interval_compact`,
> а `compact_eq_noetherian` — нётеровость вместе с её следствием для процессов.

## Расхождение 12. Теоремы о промежуточном значении и об экстремуме на компактность не опираются (стр. 1025–1026)

**Было:** «компактность интервала — инструмент, на котором будут стоять теоремы о промежуточном значении и об экстремуме»

Проверка. `IVT_ERR.v`, `IVT_CauchyReal.v`, `EVT_idx.v`, `EVT_ERR.v`, `process/ProcessIVT.v`,
`process/ProcessEVT.v` не подключают ни `HeineBorel_ERR.v`, ни `analysis/HeineBorelComplete.v`, ни
`analysis/BolzanoWeierstrass.v`. Файлы компактности подключают только `ProcessBW.v`, `ProcessHB.v`,
`ProcessTopCompact.v`, `ProcessTopUnified.v`. IVT идёт собственной бисекцией с архимедовостью, EVT — максимумом
по индексу сетки. Глава 5.3 сама говорит, что над ℚ опора на компактность не действует (её § о теореме
Кантора — Гейне).

**(а)** Доводить не нужно: обе теоремы доказаны независимо, и над ℚ это их естественный путь.

**(б) Стало:**

> **Готовит дальше.** Равномерная непрерывность, Липшицев аппарат,
> $\varepsilon$-сети — задел для Главы 5.3 о непрерывности;
> теоремы о промежуточном значении и об экстремуме пойдут там собственным путём — бисекцией и сеткой, —
> потому что на компактность над $ℚ$ опереться нельзя.

## Расхождение 13. Сноска 2: проверена другая конструкция; открытость покрытия не доказана (стр. 1071)

**Было:** «Эта конкретная конструкция теперь и машинно проверена — как *самостоятельная* 0-аксиомная теорема, а не только общий смысл препятствия. Для $[1,2]\capℚ$ задано явное открытое покрытие $U_k=\{x : |x^2-2| > 1/(k{+}1)\}$»

Проверка. В тексте главы (стр. 501–528) — шары радиуса ½|x − α| вокруг каждой точки отрезка [0,1], α = √2/2.
В `src/QIntervalNotCompact.v` — счётное семейство множеств `U k` на [1,2]; это покрытие другого вида, не функция
радиуса `OpenCover`, с которой работает положительная теорема. `covers` (`:74`), `no_finite_subcover` (`:99`),
`Q_interval_not_compact` (`:126`) названы и пересказаны верно; «5 Qed, 0 аксиом» верно (все 7 объявлений —
`Closed under the global context`). Открытость множеств `U k` в файле сказана комментарием (строки 6–10),
леммы нет.

Простыми словами: машинно проверено то же явление на родственном примере; слово «эта» и слово «открытое»
опережают доказанное.

**(а) Довести формализацию.** Возможно в обеих частях, без допущений; наброски проверены.

Открытость (`_part05/ch02/CheckUopen.v`, `Closed under the global context`):
`Lemma U_open : forall k : nat, is_open (U k).` — по точке `x` берётся радиус
`min(1, (|x² − 2| − 1/(k+1)) / (2|x| + 1))`; полный текст в пробном файле.

Контрпример в определениях самой теоремы Гейне — Бореля (`_part05/ch02/CheckGap.v`,
`Closed under the global context`):

```coq
Definition gap (x : Q) : Q := Qabs (x * x - 2).
Definition C_gap : OpenCover := fun x => Qmin 1 (gap x) * (1#8).

Lemma C_gap_valid : forall a b, valid_cover C_gap a b.

Lemma covered_far_from_gap : forall c y,
  1 <= y -> y <= 2 -> covered_by C_gap c y -> (3#8) * gap c < gap y.

Theorem C_gap_no_finite_subcover : forall centers : FiniteSubcover,
  ~ covers_interval C_gap centers 1 2.

Theorem classical_Heine_Borel_fails_over_Q :
  ~ (forall (C : OpenCover) (a b : Q), a < b -> valid_cover C a b ->
       exists centers : FiniteSubcover, covers_interval C centers a b).

Corollary C_gap_not_uniform : forall delta, ~ uniform_cover C_gap 1 2 delta.
```

Это конструкция главы в рациональном виде: радиус мельчает у разреза √2. Ход: точка, накрытая шаром с центром
`c`, отстоит от разреза больше чем на 3/8 зазора центра; у конечного набора центров наименьший зазор
положителен; приближение Пелля (`sqrt2_uncovered`) подходит к разрезу ближе. Центры допускаются любые, не только
из отрезка. Последняя теорема — тезис § 2.5 («классический Гейне — Борель над ℚ неверен») в тех же
определениях, что и `Heine_Borel`; сейчас он в них не записан.

**(б) Поправить слова.** Стало:

> Некомпактность рационального отрезка теперь и машинно проверена — на родственной конструкции, как
> *самостоятельная* 0-аксиомная теорема, а не только общий смысл препятствия. Для $[1,2]\capℚ$ задано явное
> покрытие множествами $U_k=\{x : |x^2-2| > 1/(k{+}1)\}$ (их открытость в файле оговорена комментарием): оно
> накрывает…

## Расхождение 14. `L3_informative` стоит на L3 и L4; место входа L4 не показано (стр. 823–824; обещание — стр. 784–786)

**Было:** «`L3_informative` и `classic` — технические Rocq-реализации $L3$. Выбор половины опирается на закон исключённого третьего ToS.»

Проверка. `Print Assumptions L3_informative` — `Classical_Prop.classic` и `ToS_Axioms.L4_witness`. В
доказательстве (`src/ToS_Axioms.v:119–130`) из `classic` получено «существует булево значение, верное для P»,
а само значение извлечено командой `destruct (L4_witness _ Hex)`. Это единственное место, где в бисекцию входит
L4; `infinite_pigeonhole` стоит только на `classic`. Итоговая цена теоремы в главе названа верно (L3 и L4), но
§ 2.7.2, обещавший показать, «где и почему законы логики вступают в дело», о L4 не говорит.

**(а) Довести формализацию до слов главы**, по-видимому, нельзя: разбор случаев по утверждению «P или не P»
в Rocq не даёт значения, по которому можно строить функцию (следующий интервал), — для этого и нужно
извлечение свидетеля. Что теорему нельзя получить из одного `classic` иным путём, компилятором не проверяется;
это оценка, а не доказанный факт.

**(б) Поправить слова.** Стало:

> По уговору § 2.1: `classic` — техническая Rocq-реализация $L3$, а `L3_informative` получена из неё
> извлечением свидетеля — `L4_witness`. Здесь и входит $L4$: чтобы по «верно одно из двух» *построить*
> следующий интервал, выбор нужно иметь на руках, а не только знать, что он есть. Выбор половины опирается
> на закон исключённого третьего ToS, а превращение этого знания в шаг процесса — на закон достаточного основания.

## Расхождение 15. «Остальные свойства бисекции конструктивны» (стр. 845–849)

**Было:**

> Остальные свойства бисекции конструктивны и отработаны подробно:
> каждый шаг сохраняет вложенность и «населённость» выбранной
> половины, ширина после $n$ шагов не превосходит $(b-a)/2^n$ и —
> через архимедовость (`bw_width_to_zero`) — стремится к
> нулю, а левые и правые концы образуют процессы Коши.

Проверка. Формулировки верны. Но `Print Assumptions` у `bw_step_nested_left`, `bw_step_nested_right`,
`bw_step_preserves_infinite`, `bw_width_bound`, `bw_width_to_zero`, `bw_left_cauchy`, `bw_right_cauchy` —
`classic` и `L4_witness`: леммы говорят о `bw_iter`, построенном на `bw_step`. Лемма о «населённости»
(`bw_step_preserves_infinite`, `:171`) к тому же сама обращается к `classic` через `infinite_pigeonhole`.

Простыми словами: новых обращений к законам логики в этих доказательствах (кроме «населённости») нет, но
«конструктивными» по компилятору они не являются.

**(а) Довести формализацию.** Факты о ширине и вложенности доказываются без допущений для бисекции с
произвольным выбором половины; выбор по L3 — частный случай. Набросок проверен (`_part05/ch02/CheckMisc.v`):
первые три леммы — `Closed under the global context`, связка — `classic`, `L4_witness`:

```coq
Definition gen_step (go_left : bool) (st : BWState) : BWState :=
  if go_left then mkBW (bw_left st) (bw_mid st) else mkBW (bw_mid st) (bw_right st).

Lemma gen_step_valid : forall g st,
  bw_left st <= bw_right st -> bw_left (gen_step g st) <= bw_right (gen_step g st).
Lemma gen_step_width : forall g st,
  bw_right (gen_step g st) - bw_left (gen_step g st) == (bw_right st - bw_left st) / 2.
Lemma gen_step_nested : forall g st, bw_left st <= bw_right st ->
  bw_left st <= bw_left (gen_step g st) /\ bw_right (gen_step g st) <= bw_right st.

Lemma bw_step_is_gen_step : forall s st,
  bw_step s st = gen_step (if L3_informative (bw_step_left s st) then true else false) st.
```

В `HeineBorel_ERR.v` такая бисекция уже есть (`hb_step`, `hb_width` — без допущений). «Населённость»
конструктивной не сделать: она и есть содержание выбора по L3.

**(б) Поправить слова.** Стало:

> Остальные свойства бисекции новых обращений к законам логики не добавляют и отработаны подробно:
> каждый шаг сохраняет вложенность и «населённость» выбранной
> половины, ширина после $n$ шагов не превосходит $(b-a)/2^n$ и —
> через архимедовость (`bw_width_to_zero`) — стремится к
> нулю, а левые и правые концы образуют процессы Коши. (В выводе `Print Assumptions` у этих лемм стоят те же
> `classic` и `L4_witness` — они унаследованы от шага `bw_step`, о котором леммы говорят.)

## Расхождение 16. Счёт файлов (стр. 99–100)

**Было:** «Опорных файлов одиннадцать — шесть основных и пять вспомогательных process-обёрток; все сверены с репозиторием дословно.»

Проверка. В обратных кавычках глава называет 12 файлов: `Topology.v`, `ProcessTopOpen.v`,
`ProcessTopConnected.v`, `RealPointTopology.v`, `HeineBorel_ERR.v`, `HeineBorelComplete.v`,
`BolzanoWeierstrass.v`, `ProcessBW.v`, `ProcessTopCompact.v`, `ProcessTopUnified.v`, `ProcessCompactness.v`,
`ToS_Axioms.v`; сноска 2 опирается ещё на `QIntervalNotCompact.v`, по имени не названный. Одиннадцать — это без
файла аксиом и без файла сноски. Деление «6 + 5» не сходится ни при каком чтении названного: обёрток и сводок
четыре, прочих семь; по именам — шесть файлов `Process*` и пять остальных. «6 + 5» сходится, если убрать
`RealPointTopology.v` (добавлен позже) и добавить `ProcessHB.v`, которого глава не называет. «Сверены
дословно» — верно: 16 блоков кода из 16 совпадают с исходниками.

**(б) Стало (предложение, счёт — за автором):**

> Опорных файлов одиннадцать — семь основных и четыре процессные обёртки и сводки; к ним — файл аксиом
> `ToS_Axioms.v` и файл контрпримера, на который опирается сноска 2; все сверены с репозиторием дословно.

## Оформление (вне пяти проверок)

Имя в обратных кавычках разорвано переводом строки и на странице показывается с пробелом внутри:
- стр. 32–33: `ProcessTop` / `Connected.v` → «ProcessTop Connected.v»;
- стр. 816–817: `L3_` / `informative` → «L3_ informative».

Лечится сборкой имени на одной строке. В ведомости обе записи стоят с вердиктом `missing-name`, оба имени
существуют.

## Сомнительные места (не расхождения)

- Стр. 44–45, 252–253, 286: «доказана без допущений» о теореме Гейне — Бореля значит «без аксиом»; у теоремы
  есть посылка — равномерность покрытия, названная в § 2.5. Читатель может понять «без условий»; точнее было бы
  «без аксиом (при условии равномерности, § 2.5)».
- Стр. 43–44: «локально на $L4$». L4 входит в одном месте, но наследуется 24 объявлениями файла из 34,
  включая главную теорему.
- Стр. 339–343: `is_open_process` — тот же предикат, что `is_open` из `Topology.v` (проверено:
  `is_open_process S <-> is_open S`), а `in_ball` — тот же `open_ball`. «Процессная форма» и «процессный язык»
  здесь — имена, а не другое определение; процессную идею несут `QBallCover` и `OpenProcess`, как глава и
  говорит ниже.
- Стр. 384–386, 1008: «доказаны её базовые свойства», «Построено и проверено … с уточнением по уровням». О
  покрытии доказаны две леммы (`single_ball_covers_center`, `append_covers_union`); об `OpenProcess` — только
  `p4_cover_finite`; об `is_refining` — ни одной. Построены определения.
- Стр. 177–179: «опора всей будущей теории компактности». `HeineBorel_ERR.v` файл `Topology.v` не подключает,
  леммы об интервалах в доказательствах компактности не участвуют; «опора» — по смыслу.
- Стр. 561–585: «конечное подпокрытие» формально — список центров `list Q` без требования лежать в отрезке
  (`covers_interval`), а `valid_cover` стесняет радиус только на отрезке. В доказательстве центры берутся из
  отрезка, но в утверждении этого нет. В теореме `Heine_Borel` посылка `valid_cover` лишняя (не используется).
- Стр. 712: «Противоречия с заголовком нет». Шапка `HeineBorelComplete.v` говорит «0 axioms», а одна теорема
  файла стоит на `classic`; глава это и разбирает — но слово «противоречия нет» мягче, чем положение дел: шапка
  неточна.
- Стр. 881–883: шапка `ProcessBW.v` называет только `classic`, компилятор — `classic` и `L4_witness`; строка 6
  той же шапки говорит «0 axioms». То же двоение («0 axioms» и «AXIOMS: classic») в шапках
  `ProcessTopCompact.v` и `ProcessTopUnified.v`, на которые глава ссылается на стр. 989–991.
- Стр. 864–866: `monotone_bounded_cauchy` и `decreasing_bounded_cauchy` стоят только на `classic`, без L4;
  глава цену здесь не называет.
- Стр. 226–228 и сноска 1: «дословная» разметка — перевод шапки `Topology.v`, в котором опущен четвёртый
  элемент («functions Q -> Q»).
- Стр. 901–905: «ℚ вполне несвязно» в формализации не доказано (только комментарий); кандидат в бэклог —
  разрез по √2 даёт два непустых открытых множества, в сумме всё ℚ.

## Вне главы (замечено по дороге)

- Комментарий `HeineBorel_ERR.v:533–535` приводит контрпримером `C(x) = |x - sqrt(2)|`. С таким радиусом
  конечное подпокрытие есть: шары вокруг концов отрезка сходятся к разрезу с двух сторон и вместе покрывают все
  рациональные точки. У главы радиус с множителем 1/2 — верно.
- Шапки файлов с отставшим числом Qed (глава этих чисел не приводит): `ProcessTopOpen.v` — 20 (в файле 14),
  `ProcessTopConnected.v` — 20 (16), `ProcessTopCompact.v` — 20 (16), `ProcessTopUnified.v` — 15 (10),
  `BolzanoWeierstrass.v` — 22 (26), `HeineBorelComplete.v` — 22 (28). Шапка `BolzanoWeierstrass.v`
  (строка 5) обещает «Cauchy subsequence»; доказана точка сгущения.
- `ProcessHB.v` (в главе не назван): `hb_terminates : forall n : nat, (n <= n)%nat` — утверждение, не связанное
  с Гейне — Борелем; `process_HB`, `process_HB_uniform` — повторы теорем `HeineBorel_ERR.v`.
- Комментарий к `interval_path_connected` (`ProcessTopConnected.v:110`) говорит «Open interval», теорема — о
  замкнутом.

## Пробные файлы

Папка `C:/Users/abary/tos-audit-build/_part05/ch02/`; все собираются на текущей сборке.

| файл | что проверено | допущения |
|---|---|---|
| `CheckBW.v` | слабость `is_cluster_point`; сильная форма и её инвариантность; `bolzano_weierstrass_strong`; цены `L3_informative`, `infinite_pigeonhole`, `bw_width_to_zero` и др. | контрпримеры и инвариантность — нет; теорема — `classic`, `L4_witness` |
| `CheckProcBW.v` | заключения `process_BW` и `bw_is_process_construction` без посылок; усиленные версии; `bw_rate_is_step_ratio` | первые два — нет; остальное — `classic`, `L4_witness` |
| `CheckTop.v` | `continuous_iff_open_preimage`; `any_set_path_connected`; липшицева путь-связность интервала и её отсутствие у {0, 1}; `process_path_converges`; `cover_frame_bounded`; `refining_monotone` | нет |
| `CheckTop2.v` | `is_open_process S <-> is_open S`; `in_ball` = `open_ball` | нет |
| `CheckHB.v` | `uniform_cover` ⇒ `has_lebesgue_number`, обратное неверно; `Heine_Borel_lebesgue` | нет |
| `CheckGap.v` | `C_gap_no_finite_subcover`; `classical_Heine_Borel_fails_over_Q`; `C_gap_not_uniform` | нет |
| `CheckUopen.v` | `U_open : forall k, is_open (U k)` | нет |
| `CheckRP.v` | `rp_in_ball` содержит границу; открытый шар на классах: корректность, центр, граница, открытость | нет |
| `CheckMisc.v` | бисекция с произвольным выбором (`gen_step_*`); пять точек — 1/4-сеть отрезка [0,1]; `Print All Dependencies Heine_Borel_uniform` | `gen_step_*`, сеть — нет; `bw_step_is_gen_step` — `classic`, `L4_witness` |

## Дополнительные проверки

- Блоки кода: 16 объявлений, все совпадают с исходниками (сверка инструмента).
- Допущения всех объявлений двенадцати файлов главы сверены по реестру `pa-all.tsv` и выборочно заново
  (`Print Assumptions` в пробных файлах): `Topology.v` 27 из 27 без допущений, `ProcessTopOpen.v` 21 из 21,
  `ProcessTopConnected.v` 20 из 20, `HeineBorel_ERR.v` 45 из 46 (одно — `classic`), `HeineBorelComplete.v` 32
  из 33 (одно — `classic`), `BolzanoWeierstrass.v` 7 без допущений, 3 на `classic`, 24 на `classic` и
  `L4_witness`, `ProcessBW.v` 3 и 9, `ProcessTopCompact.v` 14 без допущений и 4 на `classic`,
  `ProcessTopUnified.v` 11 и 1, `ProcessCompactness.v`, `RealPointTopology.v`, `QIntervalNotCompact.v` — все
  без допущений.
- Числа: «девятнадцать лемм `Topology.v`» — 19 Qed (18 нумерованных и вспомогательная `qabs_lt_of_bounds`);
  «5 Qed, 0 аксиом» в сноске 2 — верно. Файлы `src` главы совпадают с собранной копией побайтно.
- Таблица § 2.6 (5, 9, 17 точек): первая строка проверена компилятором со строгим неравенством; в формализации
  таблицы нет, глава называет её иллюстрацией.
- Перекрёстные ссылки: `process_space_complete` действительно разобрана в Главе 5.1 (стр. 625–627 той
  страницы); правило «цена — по теореме, а не по файлу» — в Главе 4.6.
