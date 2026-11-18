# Глава VII.2 «Уолш–Адамар: преобразование без трансцендентностей» — заметки к ведомости (15.11.2026)

Ведомость: `part07-ch02.json` — 52 ручные записи; `merge --dry` проходит без замечаний, список «без сверки»
пуст (инструмент добавляет одну автоматическую запись — упоминание файла `ProcessWalshConvolutionGeneral.v`).
Вердикты ручных записей: ok — 44, mismatch-statement — 7, wrong-number — 1. Расхождений цены и имён без
объявления нет.

Семь записей с расхождением формулировки относятся к двум местам: шесть — к расхождению 1 (вентиль Адамара:
посылка, которой не удовлетворяет ни одно рациональное число), одна — к расхождению 2 («буквально выполняется
вся абстрактная теория Главы 7.1»). Запись с неверным числом — расхождение 3.

Глава называет пять файлов каталога `src/process/`: `ProcessWalshHadamard.v` (12 `Qed`),
`ProcessWalshCharacter.v` (8), `ProcessFourierON.v` (5), `ProcessHadamardGate.v` (5),
`ProcessWalshConvolutionGeneral.v` (7). Все пять прочитаны целиком, как и определения, на которые они опираются
(`op_apply`, `op_symmetric`, `adjoint_inner` — `ProcessSelfAdjointSpectral.v`; `seq_inner` —
`ProcessCompactSpectral.v`; `dconv` — `ProcessWalshConvolution.v`; `q_sum` — `ProcessMCT.v`). Строк `Axiom`,
`Parameter`, `Admitted` в них нет. Для всех 37 утверждений пяти файлов снят `Print Assumptions` — каждое
«Closed under the global context» (`PA.v`). Исходники в репозитории и в собранной копии совпадают (`diff`).
Цена на странице («без единой аксиомы», «0 аксиом») названа верно всюду.

**Размеры.** Для каких размеров доказана каждая названная теорема и какие у неё посылки:

| теорема | файл:строка | размер | посылки |
|---|---|---|---|
| `had_sq` | `ProcessWalshHadamard.v:63` | всякое $k$, все $i,j$ | нет |
| `walsh_norm` | `:78` | всякое $k$, всякое $i$ | нет |
| `hadamard_orthogonal` | `:152` | всякое $k$ | $i,i'<2^k$ |
| `hadamard_2_orthogonal` | `:226` | $N=2$: три элемента из четырёх | — |
| `hadamard_4_orthogonal` | `:233` | $N=4$: четыре элемента из шестнадцати | — |
| `had_character` | `ProcessWalshCharacter.v:129` | всякое $k$ | $i,a,b<2^k$ |
| `xor_perm_q_sum` | `ProcessWalshConvolutionGeneral.v:125` | всякое $k$ | $m<2^k$ |
| `walsh_convolution` | `:193` | всякое $k$, все $f,g$ | $i<2^k$ |
| `had_symmetric` | `ProcessFourierON.v:44` | всякое $k$, все $i,j$ | нет |
| `walsh_HH` | `:61` | всякое $k$, всякое $f$ | $m<2^k$ |
| `parseval_walsh` | `:91` | всякое $k$, всякое $f$ | нет |
| `hadamard_2x2` | `ProcessHadamardGate.v:44` | $N=2$ | — |
| `hgate_involution` | `:76` | $N=2$ | рациональное $s$ с $s\cdot s\cdot 2=1$ — **невыполнима** |
| `hgate_superposition` | `:92` | $N=2$ | нет (всякое рациональное $s$) |

Слова главы о размере («для всех $2^k$», «Конкретные $N=2,4$», «случай $N=2$») этому соответствуют. Раздел с
посылкой (`Section … Hypothesis`) в пяти файлах один — `Gate` в `ProcessHadamardGate.v`; о нём расхождение 1.
Посылка `op_symmetric` теоремы `adjoint_inner`, которой пользуется `parseval_walsh`, выполнена
(`walsh_op_symmetric`, `ProcessFourierON.v:53`).

**Два имени без объявления** (сообщение инструмента):

- `Admitted` (сноска 1) — ключевое слово Rocq, не имя; сказанное («0 `Admitted`») верно;
- `lxor` (сноска 4) — страница пишет `Nat.lxor`: это функция стандартной библиотеки
  (`Corelib.Init.Nat.lxor : nat -> nat -> nat`, `Print Assumptions` — Closed under the global context), в `src`
  не объявлена и не должна быть. Инструмент разобрал запись как файл `Nat.v` и короткое имя `lxor` и по
  короткому имени показал `N.lxor` — другую функцию (на двоичных числах `N`); в `ProcessWalshCharacter.v`
  используется именно `Nat.lxor`. Расхождения нет.

Пробные файлы лежат в `C:/Users/abary/tos-audit-build/_part07/ch02/`:

- `status.txt` — вывод `tom-status.cjs chapter 07/02`;
- `PA.v`, `PA.out` — `Print Assumptions` всех утверждений пяти файлов, вид теорем раздела `Gate` после закрытия
  раздела, `Locate Nat.lxor`;
- `Calc.v`, `Calc.out` — вычисление матриц `had 1` и `had 2` (совпадают с $H_2$ и $H_4$ страницы);
- `Check.v`, `Check.out` — пробные доказательства, разделы 0–3 по местам главы. Собирается; все 26
  утверждений, для которых снят `Print Assumptions`, — «Closed under the global context».

В `src` и в собранной копии ничего не менялось; база связей не менялась (`merge` запускался только с `--dry`).

## Что проверить не удалось

- Отсылки к другим главам (7.1, 7.3, 7.5; Части II и IV) по содержанию не сверялись — это предмет их
  ведомостей. Сверены адреса: Глава 7.1 — «Ортонормированные системы и коэффициенты Фурье», Глава 7.3 —
  «Тригонометрия и комплексный DFT: где граница», Глава 7.5 — «Сжатие, быстрое преобразование, свёртка»; Части
  II и IV в томе есть («Натуральные числа», «Процессные действительные числа»).
- Как Глава 7.1 описывает ту же нормировку («вводится абстрактным параметром $s$ с условием $s^2=N$», стр.
  289–294 той главы) — предмет её ведомости. Расхождения 1 и 2 этой ведомости касаются тех же мест и должны
  решаться вместе с ней.
- Предложенные новые файлы как отдельные файлы `src/process/` не собирались: проверен их текст в `Check.v`.
  В `Check.v` расширение $ℚ[\sqrt2]$ взято подключением `stdlib/CliffordField.v`; вариант с повторением трёх
  определений внутри `process/` (как велит `CLAUDE.md` для файлов этого каталога) не собирался.
- Утверждение «у группы $(ℤ_2^{n},\oplus)$ характеров ровно $N$» (стр. 282) в пробном файле доказано наполовину:
  строки — характеры и попарно различны; что других характеров нет, не доказывалось.
- Что $1/\sqrt N$ иррационально при всяком нечётном $k$, не доказывалось (в `src` есть случай $k=1$:
  `no_rational_sqrt2`, `analysis/Sqrt2Irrational.v:200`).
- Сведения о классической математике и физике (секвентный порядок, алгоритмы Гровера и Дойча–Йожи) вне предмета
  аудита.
- Английская страница и LaTeX-исходник главы не смотрелись.

Всё остальное проверено по исходнику и компилятору.

## Расхождение 1. Инволюция нормированного вентиля доказана под посылкой, которой не удовлетворяет ни одно рациональное число (стр. 37–39, 41–44, 220–222, 224–225, 229–232; сноска 8)

**Было:**

> (37–39) Наконец, нормированный случай $N=2$, если вынести $1/\sqrt2$ в абстрактный параметр $s$ с
> соотношением $s^2\cdot2=1$, — это в точности квантовый вентиль Адамара.
>
> (41–44) Буквальная *ортонормированность* $\inner{e_i}{e_j}=\delta_{ij}$ требует множителя $1/\sqrt N$,
> рационального лишь когда $N$ — точный квадрат (для $N=2^k$ — лишь при чётном $k$); поэтому нормировка вводится
> абстрактным параметром, а не вычисляется.
>
> (220–222) Две его определяющие черты доказаны как рациональные факты, с единственной трансцендентностью —
> нормировкой — вынесенной в абстрактный параметр.
>
> (224–225) Во-первых, вентиль есть *инволюция*: $H^2=I$, применённый дважды он возвращает исходное состояние.
>
> (229–232) …Единственная иррациональность — нормировка $1/\sqrt N$ — отделена и помечена; структура вентиля
> (инволюция, суперпозиция) рациональна.
>
> (сноска 8) `hgate_involution` в `ProcessHadamardGate.v`: для нормированного вентиля
> $\texttt{hgate}(\texttt{hgate } f)=f$. Нормировка $1/\sqrt2$ введена абстрактным параметром $s$ с соотношением
> $s^2\cdot2=1$; тождество $H(Hf)=2f$ (частный случай $N=2$) тогда даёт $s^2\cdot 2\cdot f=f$.

**Проверка.** `src/process/ProcessHadamardGate.v:64–86`:

```coq
Section Gate.
Variable s2inv : Q.
Hypothesis Hs2 : s2inv * s2inv * 2 == 1.

Definition hgate (f : nat -> Q) : nat -> Q :=
  fun m => s2inv * op_apply (had 1) f (pow2 1) m.

Theorem hgate_involution : forall f m, (m < pow2 1)%nat ->
  hgate (hgate f) m == f m.
```

После закрытия раздела (`PA.out`):

```coq
hgate_involution : forall s2inv : Q, s2inv * s2inv * 2 == 1 ->
  forall (f : nat -> Q) (m : nat), (m < pow2 1)%nat -> hgate s2inv (hgate s2inv f) m == f m
hgate_superposition : forall s2inv : Q,
  hgate s2inv e0 0 == s2inv /\ hgate s2inv e0 1 == s2inv
```

`Print Assumptions` обеих: Closed under the global context. Цена названа верно.

Параметр `s2inv` имеет тип `Q` — это рациональное число. Рационального числа с $s^2\cdot 2=1$ нет: тогда
$(2s)^2=2$. Доказано (`Check.v`, раздел 1; Closed under the global context):

```coq
Lemma hgate_premise_unsat : forall s : Q, ~ (s * s * 2 == 1).
Proof.
  intros s H. apply (Sqrt2Irrational.no_rational_sqrt2 (2 * s)).
  assert (E : 2 * s * (2 * s) == 2 * (s * s * 2)) by ring.
  rewrite E, H. reflexivity.
Qed.
```

Следовательно, теорема `hgate_involution` не применима ни к одному значению параметра. Без посылки верно
другое (там же):

```coq
Lemma hgate_sq_scale : forall (s : Q) (f : nat -> Q) (m : nat), (m < pow2 1)%nat ->
  hgate s (hgate s f) m == (s * s * 2) * f m.

Lemma hgate_involution_iff : forall s : Q,
  (forall (f : nat -> Q) (m : nat), (m < pow2 1)%nat -> hgate s (hgate s f) m == f m)
  <-> s * s * 2 == 1.

Theorem hgate_never_involution_over_Q : forall s : Q,
  ~ (forall (f : nat -> Q) (m : nat), (m < pow2 1)%nat -> hgate s (hgate s f) m == f m).
```

То есть при всяком рациональном множителе дважды применённый вентиль есть умножение на $2s^2$ и тождественным
преобразованием не является. Посылкой не затронуты и содержательны: `hadamard_unnormalised_square` (`:59`,
$H(Hf)=2f$), `hadamard_2x2` (`:44`), `op_apply_scale` (`:49`) и `hgate_superposition` (`:92`; посылка в
доказательстве не используется, утверждение верно для всякого рационального $s$).

Параметр нормировки в формализации есть только здесь, для $N=2$; для общего $N=2^k$ его нет ни в одном из
файлов, подключающих `ProcessWalshHadamard.v` (поиск).

Нормированный вентиль без посылок в репозитории уже есть, но в другом файле, которого глава не называет:
`src/stdlib/CliffordField.v` строит расширение $ℚ[\sqrt2]$ парами рациональных координат $(a,b)=a+b\sqrt2$
(`RQ`, `rmul`, `:77–81`), элемент `s2 := (0, 1#2)` — это $\sqrt2/2=1/\sqrt2$ (`:110`), матрицу
`mH := (s2, s2, s2, ns2)` (`:112`) и доказывает `mH_invol : rm_eq (rm_mul mH mH) rm_id` (`:129`) — $H^2=I$ для
матрицы $2\times2$ над $ℚ[\sqrt2]$. `Print Assumptions mH_invol`: Closed under the global context.

**В чём расхождение.** Параметр нормировки в формализации — рациональное число, а рационального числа с
$s^2\cdot2=1$ нет; поэтому теорема об инволюции нормированного вентиля не имеет ни одного примера, и слова
«доказаны как рациональные факты» к ней не относятся: рационально доказаны $H(Hf)=2f$ и равенство двух
амплитуд.

**(а) Довести формализацию до слов главы.** Возможно, без аксиом. Соотношение $s^2\cdot2=1$ выполнимо в
расширении $ℚ[\sqrt2]$, где координаты остаются рациональными; там вентиль с амплитудами из $ℚ[\sqrt2]$ есть
инволюция без посылок. Предлагается новый файл `src/process/ProcessHadamardGateSqrt2.v` (существующие файлы не
трогаются). Набросок проверен: `Check.v`, раздел 1, все утверждения — Closed under the global context. Кроме
трёх лемм, приведённых выше, в файл идут:

```coq
(* Q[sqrt2]: пары (a, b) = a + b sqrt2; определения RQ, rmul, req, s2, r0, r1 —
   как в stdlib/CliffordField.v (в файле каталога process/ их следует повторить
   с пометкой «Replicated from CliffordField.v») *)
Definition rscale (q : Q) (z : RQ) : RQ := (q * fst z, q * snd z).
Definition rsum (g : nat -> RQ) (n : nat) : RQ :=
  (q_sum (fun j => fst (g j)) n, q_sum (fun j => snd (g j)) n).

(* (hgateR f)_m = (1/sqrt2) * Sum_{j<2} H_{mj} f_j, амплитуды f_j из Q[sqrt2] *)
Definition hgateR (f : nat -> RQ) : nat -> RQ :=
  fun m => rmul s2 (rsum (fun j => rscale (had 1 m j) (f j)) (pow2 1)).

Lemma s2_relation_holds : req (rmul (rmul s2 s2) (2, 0)) r1.     (* s^2 * 2 = 1 *)
Lemma s2_sq_half : req (rmul s2 s2) (1 # 2, 0).                  (* s^2 = 1/2 *)

Theorem hgateR_involution : forall (f : nat -> RQ) (m : nat),
  (m < pow2 1)%nat -> req (hgateR (hgateR f) m) (f m).
Proof.
  intros f m Hm.
  destruct hadamard_2x2 as [H00 [H01 [H10 H11]]].
  assert (Hm2 : (m < 2)%nat) by exact Hm.
  destruct m as [|[|m]]; [ | | lia ];
    unfold hgateR, rsum, rscale, req, rmul, s2;
    change (pow2 1) with 2%nat; cbn [q_sum fst snd];
    (split; rewrite ?H00, ?H01, ?H10, ?H11; ring).
Qed.

Definition e0R (j : nat) : RQ := if Nat.eqb j 0%nat then r1 else r0.

Theorem hgateR_superposition :
  req (hgateR e0R 0%nat) s2 /\ req (hgateR e0R 1%nat) s2.

(* Рациональная форма обратимости, все 2^k: H^{-1} = (1/N) H *)
Theorem walsh_inverse : forall k (f : nat -> Q) (m : nat), (m < pow2 k)%nat ->
  op_apply (had k)
           (fun j => / inject_Z (Z.of_nat (pow2 k)) * op_apply (had k) f (pow2 k) j)
           (pow2 k) m == f m.
Proof.
  intros k f m Hm. rewrite op_apply_scale. rewrite (walsh_HH k f m Hm).
  field. apply pow2Q_neq0.
Qed.
```

(В `Check.v` имена расширения записаны с приставкой `CliffordField.`; `pow2Q_neq0 : forall k,
~ inject_Z (Z.of_nat (pow2 k)) == 0` — вспомогательная лемма раздела 0 того же файла.) Квадрат амплитуды $s^2=\tfrac12$ рационален — это вероятность исхода. В тот же файл стоит
положить `hgate_premise_unsat` как объяснение, почему параметр вынесен в расширение. Довести дело, оставив
параметр рациональным, нельзя: `hgate_never_involution_over_Q`.

Второй путь — не добавлять файлов, а сослаться на уже доказанную `mH_invol` (`stdlib/CliffordField.v`); тогда
в формализации не будет суперпозиции над $ℚ[\sqrt2]$ и связи матрицы `mH` с `had 1`, но инволюция получает
настоящую опору.

**(б) Поправить слова.** Ход мысли автора сохраняется: меняется одно — «абстрактный параметр» получает имя
того, чем он является в формализации.

Если принят путь (а) с новым файлом:

> (37–39) Наконец, нормированный случай $N=2$, если вынести $1/\sqrt2$ в формальный элемент $s$ расширения
> $ℚ[\sqrt2]$ с соотношением $s^2\cdot2=1$, — это в точности квантовый вентиль Адамара.
>
> (41–44) …поэтому нормировка вводится формальным элементом расширения (в формализации — для $N=2$, элемент
> $s=\sqrt2/2$ в $ℚ[\sqrt2]$), а не вычисляется.
>
> (220–222) Две его определяющие черты доказаны как рациональные факты — в рациональных координатах расширения
> $ℚ[\sqrt2]$, — с единственной трансцендентностью — нормировкой — вынесенной в формальный элемент $s$ этого
> расширения.
>
> (229–232) …Единственная иррациональность — нормировка $1/\sqrt N$ — отделена и помечена; структура вентиля
> (инволюция, суперпозиция) записана в рациональных координатах.
>
> (сноска 8) `hgateR_involution` в `ProcessHadamardGateSqrt2.v`: для нормированного вентиля
> $\texttt{hgateR}(\texttt{hgateR } f)=f$. Нормировка $1/\sqrt2$ введена формальным элементом $s=\sqrt2/2$
> расширения $ℚ[\sqrt2]$ (пары рациональных координат) с соотношением $s^2\cdot2=1$ (`s2_relation_holds`);
> тождество $H(Hf)=2f$ (частный случай $N=2$, `hadamard_unnormalised_square`) тогда даёт $s^2\cdot 2\cdot f=f$.
> В самом ℚ такого $s$ нет (`hgate_premise_unsat`): при рациональном множителе дважды применённый вентиль есть
> умножение на $2s^2$ (`hgate_sq_scale`). Сами элементы $H_2$ — из $\{\pm1\}$ (`hadamard_2x2`).
>
> (сноска 9) `hgateR_superposition`: $\texttt{hgateR} e_0 = (s,s)$ — равные амплитуды на двух координатах,
> $s^2=\tfrac12$ (`s2_sq_half`). Это и есть переход от определённого состояния к суперпозиции, выполняемый
> вентилем Адамара.

Если новых файлов нет (опора на `mH_invol`), строки 37–39, 41–44, 220–222, 229–232 — те же, а сноски:

> (сноска 8) `mH_invol` в `CliffordField.v` (каталог `src/stdlib/`): матрица $\tfrac1{\sqrt2}H_2$ с элементами
> $\pm\sqrt2/2$ из расширения $ℚ[\sqrt2]$ (пары рациональных координат) в квадрате даёт единичную. Рациональная
> основа — тождество $H(Hf)=2f$ (частный случай $N=2$, `hadamard_unnormalised_square` в
> `ProcessHadamardGate.v`). Теорема `hgate_involution` того же файла записана для рационального параметра $s$ с
> соотношением $s^2\cdot2=1$, которому не удовлетворяет ни одно рациональное число, и примера не имеет. Сами
> элементы $H_2$ — из $\{\pm1\}$ (`hadamard_2x2`).
>
> (сноска 9) `hgate_superposition`: $\texttt{hgate} e_0 = (s,s)$ при всяком множителе $s$ — равные амплитуды на
> двух координатах. Это и есть переход от определённого состояния к суперпозиции, выполняемый вентилем Адамара.

Если формализация остаётся как есть и на `CliffordField.v` глава не ссылается, перечень доказанного приходится
сузить:

> (37–39) Наконец, случай $N=2$: рационально доказано $H(Hf)=2f$; нормированный вентиль Адамара получается
> вынесением $1/\sqrt2$ в параметр $s$ с соотношением $s^2\cdot2=1$, а этому соотношению в ℚ не удовлетворяет
> ни одно число, так что инволюция нормированного вентиля в формализации записана условно.
>
> (220–222) Рациональная основа двух его определяющих черт доказана — $H(Hf)=2f$ и равенство двух амплитуд, — а
> единственная трансцендентность — нормировка — вынесена в параметр $s$, которому в ℚ не отвечает ни одно
> число.

## Расхождение 2. «Буквально выполняется вся абстрактная теория Главы 7.1»: теоремы Главы 7.1 к системе Уолша в формализации не применены и по виду посылки не применимы (стр. 142–145)

**Было:**

> (142–145) Именно это и делает Уолша–Адамара точкой опоры рациональной гармонии: ортогональная система, на
> которой буквально выполняется вся абстрактная теория Главы 7.1 (коэффициенты, проекция, Бессель, Парсеваль),
> причём каждая её предпосылка — $\inner{e_i}{e_j}=N\delta_{ij}$ — не постулат, а доказанное равенство.

Та же мысль — во вступлении (стр. 9–13: «…завершилась обещанием предъявить *конкретную рациональную* систему,
на которой вся эта геометрия работает… Настоящая глава это обещание выполняет»); отдельной записью в ведомость
она не внесена.

**Проверка.** Посылка теорем Главы 7.1 (`src/process/ProcessL2BesselGeneral.v:119`, то же в
`ProcessL2Parseval.v:80` и `ProcessBestApproximation.v:70`):

```coq
Hypothesis Hon : forall i j, seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0).
```

Она требует квадрата нормы $1$ и, как установлено при проверке Части VI, при всех номерах невыполнима
(`on_all_indices_unsat`, `ProcessL2Orthonormal.v:134`). В выполнимой форме (раздел `ONB`,
`ProcessL2Orthonormal.v:184–320`: первые $K_0$ векторов) квадрат нормы тоже $1$. Строки Уолша удовлетворяют
другому равенству (`hadamard_orthogonal`, `ProcessWalshHadamard.v:152`): $N\cdot\delta_{ii'}$ при $i,i'<2^k$.
При $k\ge1$ это не пример посылки `Hon` ни в старой, ни в новой форме.

Что о системе Уолша доказано в `src` (поиск по файлам, подключающим `ProcessWalshHadamard.v`): ортогональность
(`hadamard_orthogonal`), обращение (`walsh_HH`), равенство Планшереля (`parseval_walsh`), оценка частичных сумм
$\sum_{i<K}(Hf)_i^2\le N\|f\|^2$ (`walsh_captured_le_energy`, `ProcessFourierCompression.v:79` — файл Главы
7.5; выведена из `parseval_walsh` и монотонности частичных сумм). Тождества остатка, ортогональности остатка
и свойства наилучшего приближения для системы Уолша в `src` нет; ни одна из теорем `bessel_general`,
`resid_norm`, `proj_ortho`, `parseval_iff_complete`, `best_approx_*`, `bessel_b`, `best_approx_b` к `had` не
применена.

**В чём расхождение.** Теоремы Главы 7.1 в формализации требуют $\inner{e_i}{e_j}=\delta_{ij}$, а система
Уолша удовлетворяет $\inner{\mathrm{w}_i}{\mathrm{w}_j}=N\delta_{ij}$; применения этих теорем к системе Уолша
нет, а проекция и наилучшее приближение для неё не доказаны вовсе.

**(а) Довести формализацию до слов главы.** Возможно, без аксиом и без корня: теория Главы 7.1 переносится на
ортогональную систему с общим квадратом нормы $c>0$ дословно, с коэффициентами $\inner{e_k}{f}/c$. Тогда
предпосылка — ровно та, что названа на странице ($c=N$), и она выполнена теоремой `hadamard_orthogonal`.
Предлагается новый файл `src/process/ProcessWalshExpansion.v`. Набросок проверен: `Check.v`, раздел 2, все
утверждения — Closed under the global context.

```coq
Section OrthoScaled.
Variable e : nat -> nat -> Q.
Variable N K0 : nat.
Variable c : Q.
Hypothesis Hc : 0 < c.
Hypothesis Hog : forall i j, (i < K0)%nat -> (j < K0)%nat ->
  seq_inner (e i) (e j) N == (if Nat.eqb i j then c else 0).
Variable f : nat -> Q.

(* Тождество остатка для произвольных коэффициентов a *)
Lemma gen_resid_c : forall (a : nat -> Q) (K : nat), (K <= K0)%nat ->
  seq_inner (fun m => f m - q_sum (fun k => a k * e k m) K)
            (fun m => f m - q_sum (fun k => a k * e k m) K) N
  == seq_inner f f N
     + q_sum (fun k => c * (a k * a k) - 2 * a k * seq_inner (e k) f N) K.

Definition coefc (k : nat) : Q := seq_inner (e k) f N / c.

Lemma resid_norm_c : forall K, (K <= K0)%nat ->
  c * seq_inner (fun m => f m - q_sum (fun k => coefc k * e k m) K)
                (fun m => f m - q_sum (fun k => coefc k * e k m) K) N
  == c * seq_inner f f N
     - q_sum (fun k => seq_inner (e k) f N * seq_inner (e k) f N) K.

Theorem bessel_c : forall K, (K <= K0)%nat ->
  q_sum (fun k => seq_inner (e k) f N * seq_inner (e k) f N) K <= c * seq_inner f f N.

Theorem best_approx_c : forall (a : nat -> Q) (K : nat), (K <= K0)%nat ->
  seq_inner (fun m => f m - q_sum (fun k => coefc k * e k m) K)
            (fun m => f m - q_sum (fun k => coefc k * e k m) K) N
  <= seq_inner (fun m => f m - q_sum (fun k => a k * e k m) K)
               (fun m => f m - q_sum (fun k => a k * e k m) K) N.

Theorem parseval_iff_complete_c : forall K, (K <= K0)%nat ->
  (q_sum (fun k => seq_inner (e k) f N * seq_inner (e k) f N) K == c * seq_inner f f N)
  <-> (forall m, (m < N)%nat -> q_sum (fun k => coefc k * e k m) K == f m).
End OrthoScaled.

(* Система Уолша: c = N = 2^k, K0 = N *)
Lemma walsh_rows_orthogonal : forall k i j, (i < pow2 k)%nat -> (j < pow2 k)%nat ->
  seq_inner (had k i) (had k j) (pow2 k)
  == (if Nat.eqb i j then inject_Z (Z.of_nat (pow2 k)) else 0).
Proof. intros k i j Hi Hj. exact (hadamard_orthogonal k i j Hi Hj). Qed.

Theorem walsh_bessel : forall k (f : nat -> Q) (K : nat), (K <= pow2 k)%nat ->
  q_sum (fun i => op_apply (had k) f (pow2 k) i * op_apply (had k) f (pow2 k) i) K
  <= inject_Z (Z.of_nat (pow2 k)) * seq_inner f f (pow2 k).

Theorem walsh_best_approx : forall k (f a : nat -> Q) (K : nat), (K <= pow2 k)%nat ->
  let c := inject_Z (Z.of_nat (pow2 k)) in
  let p := fun i => op_apply (had k) f (pow2 k) i / c in
  seq_inner (fun m => f m - q_sum (fun i => p i * had k i m) K)
            (fun m => f m - q_sum (fun i => p i * had k i m) K) (pow2 k)
  <= seq_inner (fun m => f m - q_sum (fun i => a i * had k i m) K)
               (fun m => f m - q_sum (fun i => a i * had k i m) K) (pow2 k).

(* Полнота: разложение по всем N строкам восстанавливает f *)
Theorem walsh_expansion : forall k (f : nat -> Q) (m : nat), (m < pow2 k)%nat ->
  q_sum (fun i => (op_apply (had k) f (pow2 k) i / inject_Z (Z.of_nat (pow2 k)))
                  * had k i m) (pow2 k) == f m.

(* Равенство Планшереля как следствие общей теории: Парсеваль <=> полнота *)
Theorem walsh_parseval_from_theory : forall k (f : nat -> Q),
  q_sum (fun i => op_apply (had k) f (pow2 k) i * op_apply (had k) f (pow2 k) i) (pow2 k)
  == inject_Z (Z.of_nat (pow2 k)) * seq_inner f f (pow2 k).

(* Нормированная форма без корня: Sum_i (Hf)_i^2 / N = ||f||^2 *)
Corollary walsh_parseval_normalised : forall k (f : nat -> Q),
  q_sum (fun i => op_apply (had k) f (pow2 k) i * op_apply (had k) f (pow2 k) i
                  / inject_Z (Z.of_nat (pow2 k))) (pow2 k)
  == seq_inner f f (pow2 k).

(* При чётном k = a + a нормированные строки рациональны и ортонормированы:
   пример к разделу ONB файла ProcessL2Orthonormal.v *)
Definition nwalsh (a i : nat) : nat -> Q :=
  fun m => had (a + a) i m / inject_Z (Z.of_nat (pow2 a)).

Theorem nwalsh_orthonormal : forall a i j,
  (i < pow2 (a + a))%nat -> (j < pow2 (a + a))%nat ->
  seq_inner (nwalsh a i) (nwalsh a j) (pow2 (a + a)) == (if Nat.eqb i j then 1 else 0).

Theorem nwalsh_bessel : forall a (f : nat -> Q) (K : nat), (K <= pow2 (a + a))%nat ->
  q_sum (fun k => seq_inner (nwalsh a k) f (pow2 (a + a))
                  * seq_inner (nwalsh a k) f (pow2 (a + a))) K
  <= seq_inner f f (pow2 (a + a)).
```

`gen_resid_c` доказывается индукцией по `K` теми же шагами, что `gen_resid` в `ProcessL2Orthonormal.v`
(`seq_inner_resid`, `seq_inner_sub_r`, `inner_proj_swap`); остальное следует из него в несколько строк.
Коэффициент $\inner{\mathrm{w}_i}{f}$ по определению совпадает с $(Hf)_i$ (`walsh_coef_is_transform`,
`reflexivity`). `walsh_expansion` следует из `walsh_HH` и `had_symmetric`. При $c=1$ раздел `OrthoScaled`
даёт раздел `ONB`.

**(б) Поправить слова.** Если принят путь (а), достаточно одного уточнения и сноски:

> (142–145) Именно это и делает Уолша–Адамара точкой опоры рациональной гармонии: ортогональная система, на
> которой буквально выполняется вся абстрактная теория Главы 7.1 (коэффициенты, проекция, Бессель, Парсеваль) —
> в форме для ортогональной системы с общим квадратом нормы $N$, без корня, — причём каждая её предпосылка —
> $\inner{e_i}{e_j}=N\delta_{ij}$ — не постулат, а доказанное равенство.[^новая]
>
> [^новая]: Файл `ProcessWalshExpansion.v`: теория для системы с $\inner{e_i}{e_j}=c\,\delta_{ij}$ при
> $i,j<K_0$ — `resid_norm_c`, `bessel_c`, `best_approx_c`, `parseval_iff_complete_c`; для строк Уолша
> ($c=N=2^k$) — `walsh_bessel`, `walsh_best_approx` и `walsh_expansion` (разложение по всем $N$ строкам
> восстанавливает $f$). При чётном $k$ нормированные строки рациональны и ортонормированы
> (`nwalsh_orthonormal`). 0 аксиом.

Если формализация остаётся как есть:

> (142–145) Именно это и делает Уолша–Адамара точкой опоры рациональной гармонии: ортогональная система, для
> которой предпосылка абстрактной теории Главы 7.1, взятая до нормировки, — $\inner{e_i}{e_j}=N\delta_{ij}$ —
> не постулат, а доказанное равенство. Сохранение энергии и обращение доказаны для неё напрямую (§ «Сохранение
> энергии и вентиль Адамара»); проекция и наилучшее приближение Главы 7.1 записаны для нормированной системы и
> для строк Уолша отдельно не выведены.

## Расхождение 3. Число: «`ProcessWalshCharacter.v` (7 утверждений)» (сноска 1)

**Было:**

> (сноска 1) …дополненный `ProcessFourierON.v` (5 утверждений), `ProcessWalshCharacter.v` (7 утверждений) и
> `ProcessHadamardGate.v` (5 утверждений).

**Проверка.** `grep -c 'Qed\.' src/process/ProcessWalshCharacter.v` — 8: `pow2_eq`, `testbit_high_pow2`,
`lt_pow2_of_high_bits`, `lxor_mod_pow2`, `leb_pow2_testbit`, `leb_pow2_lxor`, `had_character`,
`had_character_ex`. «7 Qed» стоит в шапке файла (`:26`). Остальные три числа сноски верны (12, 5, 5).

**В чём расхождение.** Страница повторяет число из шапки, а в файле доказанных утверждений восемь.

**(а)** Поправить шапку `ProcessWalshCharacter.v`: «STATUS: 8 Qed, 0 Admitted, 0 axioms» (правка комментария).

**(б)** «…`ProcessWalshCharacter.v` (8 утверждений)…».

## Сомнительные места, расхождением не являющиеся

- **Суперпозиция (стр. 225–227, сноска 9).** `hgate_superposition` верна для всякого рационального множителя
  $s$ и посылкой $s^2\cdot2=1$ не пользуется: по существу это $H e_0=(1,1)$, умноженное на $s$. Формула сноски
  («$\texttt{hgate} e_0=(s,s)$ — равные амплитуды») с утверждением совпадает, поэтому запись — ok. Слова текста
  «с равными амплитудами $1/\sqrt2$» называют значение, которого рациональный параметр не принимает; над
  $ℚ[\sqrt2]$ это `hgateR_superposition` (`Check.v`).
- **«Трансцендентность» о $1/\sqrt2$ (стр. 221; ср. стр. 231 — «иррациональность»).** Число $1/\sqrt2$
  иррационально, но алгебраично (корень $2x^2-1$); в формализации о нём доказана именно иррациональность
  (`no_rational_sqrt2`). Это слово автора, не утверждение о формализации; то же слово стоит в шапке
  `ProcessHadamardGate.v` (`:19`).
- **«Характеров ровно $N$, и все они предъявлены как строки» (стр. 282–283).** Раздел оговорён как осмысление
  без новых формальных утверждений (стр. 241–242). Доказано: каждая строка — характер (`had_character`). Что
  строки попарно различны как функции, следует из ортогональности (`Check.v`, `walsh_rows_distinct`); значение
  в нейтральном элементе равно 1 (`had_char_unit`); множество индексов замкнуто относительно $\oplus$
  (`lxor_lt_pow2`; в `src` это стоит внутри доказательства `leb_pow2_lxor`). Что других характеров у группы
  нет, в формализации не записано.
- **Секвентный порядок (стр. 46–48, 111–116).** В `src` нет ни упорядочения строк по числу знакоперемен, ни
  утверждения о перестановке строк (поиск). Страница доказанным это не называет; сказанное («перестановка не
  меняет ни ортогональности, ни сохранения энергии») верно, но опирается на рассуждение, а не на теорему.
- **«Обратное преобразование есть $H^{-1}=\tfrac1N H$» (стр. 209).** Отдельной теоремой не записано; следует из
  `walsh_HH` (`Check.v`, `walsh_inverse`). `walsh_invertible` в `ProcessFourierSynthesis.v:57` повторяет
  `walsh_HH`.
- **«Переход к нормированной системе… возвращает Парсеваль Главы 7.1» (стр. 210–213).** Теоремой не записано и
  доказанным не названо. Равенство $\sum_i (Hf)_i^2/N=\|f\|^2$ выводится без корня (`Check.v`,
  `walsh_parseval_normalised`). «Рационален лишь при чётном $k$»: что при чётном $k$ нормированные строки
  рациональны и ортонормированы, проверено (`nwalsh_orthonormal`); иррациональность при нечётном $k$ в `src`
  есть только для $k=1$.
- **«Энергию мы уже сохранили» (стр. 185–186).** Раздел о сохранении энергии стоит ниже (стр. 190 и далее). В
  формализации `parseval_walsh` выведена из ортогональности и симметрии матрицы (как и сказано в сноске 6), а
  не из характерного свойства; на `had_character` опирается только теорема о свёртке.
- **$H_N^{\mathsf T}H_N=N\cdot I$ и строки (стр. 33, 133).** `hadamard_orthogonal` говорит о суммах по столбцам
  для двух строк, то есть о $H_N H_N^{\mathsf T}$; вместе с `had_symmetric` это то же самое.
- **Примеры $N=2,4$ (сноска 3).** `hadamard_2_orthogonal` проверяет три элемента из четырёх (четвёртый — по
  симметрии), `hadamard_4_orthogonal` — четыре из шестнадцати. Страница называет их «конкретные $N=2,4$» и
  полноты не заявляет; общее утверждение — `hadamard_orthogonal`.
- **Формула сноски 4** опускает условия $i,a,b<2^k$; в тексте (стр. 164) они названы.
- **Алгоритмы Гровера и Дойча–Йожи (стр. 219–220).** Глава на формализацию здесь не ссылается; в `src/stdlib`
  есть файлы по этим темам (`DeutschAlgorithm.v` и другие), с главой не сверялись.

## Вне главы

- `ProcessHadamardGate.v`: шапка (`:12–14`, `:25–26`) называет параметр «abstract parameter» и нормировку
  «transcendental»; о том, что посылка `Hs2` для рационального `s2inv` невыполнима, в файле не сказано.
- `ProcessWalshCharacter.v`: шапка — «7 Qed» при 8; раздел «HONEST FRONTIER» (`:15–17`, `:23–24`) называет
  общую теорему о свёртке следующим шагом, хотя она доказана в `ProcessWalshConvolutionGeneral.v`.
- `ProcessWalshConvolution.v`: шапка (`:16–19`, `:25–26`) называет общую теорему «фронтиром» — то же.
- `ProcessWalshHadamard.v`: шапка (`:13–16`) говорит о «FULL orthogonality» и о Парсевале «concretely for N = 2
  and N = 4»; примеры проверяют выборочные элементы, а `parseval_walsh_4` — один вектор $e_0$ при $N=4$.
  Строка «Rules» называет равенство Парсеваля–Уолша, которое в общем виде доказано в `ProcessFourierON.v`.
  Комментарий `:225` — «all four entries» при трёх конъюнктах.
- `ProcessFourierSynthesis.v`: `walsh_invertible` (`:57`) дословно повторяет `walsh_HH`;
  `walsh_orthogonal_and_plancherel` (`:43`) — конъюнкция `hadamard_orthogonal` и `parseval_walsh`. Нового
  содержания эти две теоремы не добавляют; файл относится к другим главам Части VII.
- Глава 7.1 (стр. 289–294) говорит, что нормировка «в общем случае вводится *абстрактным параметром* $s$ с
  условием $s^2=N$». Такого параметра в файлах Уолша нет; для рационального $s$ и неквадратного $N$ условие
  невыполнимо по той же причине, что в расхождении 1. Сноска 4 той же главы называет «нормированный Уолш»
  системой, удовлетворяющей `Hon`; при чётном $k$ нормированные строки удовлетворяют выполнимой форме посылки
  (`nwalsh_orthonormal`), при нечётном — рациональной нормировки нет.
- `stdlib/CliffordField.v` (`mH_invol`, $ℚ[\sqrt2]$) и `process/ProcessHadamardGate.v` говорят об одном вентиле
  и между собой не связаны.
