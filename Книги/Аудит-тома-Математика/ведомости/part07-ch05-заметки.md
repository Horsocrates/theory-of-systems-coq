# Глава VII.5 «Сжатие, быстрое преобразование, свёртка» — заметки к ведомости (15.11.2026)

Ведомость: `part07-ch05.json` — 53 ручные записи; `merge --dry` проходит без замечаний, список «без сверки»
пуст. Вердикты: ok — 37, mismatch-statement — 15, wrong-number — 1. Расхождений цены и имён без объявления нет.

Пятнадцать записей с расхождением формулировки относятся к четырём местам: семь — к расхождению 1 (ошибка
сжатия), две — к расхождению 2 (восстановление без потерь; ещё одна запись, к стр. 93, общая с расхождением 1),
две — к расхождению 3 (оценка для Уолша), четыре — к расхождению 4 (итоги Глав 7.1 и 7.4 под невыполнимой
посылкой). Запись с неверным числом — расхождение 5.

Глава называет четыре файла каталога `src/process/`: `ProcessFourierCompression.v` (6 `Qed`),
`ProcessWalshCompaction.v` (2), `ProcessFastWalsh.v` (2), `ProcessWalshConvolutionGeneral.v` (7). Все четыре
прочитаны целиком, как и файлы, на которые они опираются (`ProcessWalshHadamard.v`, `ProcessFourierON.v`,
`ProcessWalshCharacter.v`, `ProcessWalshConvolution.v`). Строк `Axiom`, `Parameter`, `Admitted`, разделов
(`Section`) и посылок (`Hypothesis`, `Variable`) в четырёх файлах нет. `Print Assumptions` всех 19 объявлений
(17 `Qed`, определения `captured` и `fwht`) — «Closed under the global context». Исходники в репозитории и в
собранной копии совпадают (`diff`). Цена на странице («без аксиом», «0 аксиом», «без новых аксиом») названа
верно всюду.

**Для каких размеров доказаны названные теоремы.**

| имя | файл:строка | по чему стоит квантор |
|---|---|---|
| `truncation_error_eq` | `ProcessFourierCompression.v:61` | любая последовательность `c : nat -> Q`, любые `K <= N` (не только степени двойки; преобразование Уолша в утверждение не входит) |
| `captured_mono` | `:49` | любая `c`, любые `K <= K'` |
| `walsh_captured_le_energy` | `:79` | любое `k`, любая `f`, `K <= 2^k` |
| `walsh_compaction` | `ProcessWalshCompaction.v:41` | любая `c`, любые `K <= N` (преобразование Уолша в утверждение не входит) |
| `fwht_correct` | `ProcessFastWalsh.v:61` | любое `k`, любая `f`, `i < 2^k` |
| `walsh_convolution` | `ProcessWalshConvolutionGeneral.v:193` | любое `k`, любые `f`, `g`, `i < 2^k` |
| `had_character` | `ProcessWalshCharacter.v:129` | любое `k`, `i, a, b < 2^k` |

Примеры на одном размере стоят отдельно и общих теорем не подменяют: `compression_4_example` и
`compaction_4_example` (последовательности из четырёх чисел), `walsh_convolution_4`
(`ProcessWalshConvolution.v:47`, $N=4$, одна пара $f$, $g$). Слова страницы «для всех $2^k$» о быстром
преобразовании и о свёртке подтверждены общими теоремами.

**«Быстрое» в формализации** означает одно: рекурсивно заданная функция `fwht` в точках $i<2^k$ даёт те же
значения, что произведение матрицы на вектор `op_apply (had k)`. Утверждения о числе операций нет; страница
говорит это прямо (стр. 29–31, 110–111). Подробнее — в разделе сомнительных мест.

**«Сжатие» в формализации** означает расщепление конечной суммы квадратов произвольной последовательности на
первые $K$ слагаемых и остаток (общая теорема, не пример). Сигнала, его восстановления и ошибки восстановления
в файлах главы нет — расхождения 1 и 2.

**Посылки.** Теоремы четырёх файлов главы стоят без разделов; их условия — `K <= N`, `i < 2^k`, «`c i == 0`
при `K <= i < N`» — выполнимы (примеры есть в самих файлах). Невыполнимая посылка `Hon` касается не этих
файлов, а итогов Глав 7.1 и 7.4, которые глава перечисляет как доказанные, — расхождение 4.

**Имя без объявления.** Инструмент показывает одно: `Admitted` (сноска 1, «все 0 `Admitted`»). Это ключевое
слово Rocq, взятое на странице в обратные кавычки, а не имя объявления; в четырёх файлах оно встречается только
в строке `STATUS` шапки. Запись в ведомости — `ok`.

Пробные файлы лежат в `C:/Users/abary/tos-audit-build/_part07/ch05/`:

- `status.txt` — вывод `tom-status.cjs chapter 07/05`;
- `Check.v`, `Check.out` — пробные доказательства, разделы 0–6 по местам главы. Собирается; все 26
  утверждений, для которых снят `Print Assumptions`, — «Closed under the global context»;
- `PA2.v`, `PA2.out` — виды и `Print Assumptions` теорем Глав 7.1, 7.4 и файлов `ProcessHadamardGate.v`,
  `ProcessFourierSynthesis.v`, о которых глава говорит словами.

В `src` и в собранной копии ничего не менялось; база связей не менялась (`merge` запускался только с `--dry`).

## Что проверить не удалось

- Главы 7.1–7.4 по содержанию не сверялись — это предмет их ведомостей. Для итоговых абзацев настоящей главы
  (стр. 9–10, 187–206) проверено одно: под какой посылкой стоят теоремы, на которые эти главы ссылаются
  (`PA2.v`).
- Вариант исправления расхождения 4 «на месте» (замена посылки `Hon` в существующих файлах) не собирался;
  проверены дополнения новым текстом (`Check.v`, раздел 3).
- Счёт операций (`Check.v`, раздел 6) проверен для одной записи бабочки на списках и считает только сложения
  и вычитания рациональных чисел; шаги разбиения и склейки списков не считаются. Общего утверждения о
  сложности алгоритма в формализации нет и здесь не предлагается.
- Сведения о классической математике (оптимальность отбора наибольших коэффициентов, явление Гиббса,
  трансцендентность корней из единицы) вне предмета аудита.
- Английская страница и LaTeX-исходник главы не смотрелись.

Всё остальное проверено по исходнику и компилятору.

## Расхождение 1. «Ошибка сжатия есть отброшенная энергия»: в файлах главы — расщепление суммы квадратов, ошибки восстановления нет (стр. 22–23, 41, 57–69, 93–94, 154, 172, 202; сноска 2)

**Было:**

> (22–23) Доказано над ℚ, без аксиом. Ошибка усечения по первым $K$ коэффициентам равна сумме квадратов
> отброшенных и монотонна по $K$; …
>
> (41) Ошибка сжатия = сумма квадратов отброшенных коэффициентов (монотонна); …
>
> (57–69) Сжатие спектрального типа просто: вычислить спектр, оставить первые $K$ коэффициентов, отбросить
> остальные. Качество сжатия — это ошибка восстановления, и она в точности есть *отброшенная хвостовая
> энергия*: $\norm{f}^2 = \sum_{i<K} c_i^2 + \sum_{K\le i<N} c_i^2$, так что ошибка равна второй сумме — ровно
> тому, что усечение выкинуло.
>
> (93–94) *Ошибка сжатия = отброшенная энергия — точное рациональное тождество (для Уолша), …*
>
> (154) ошибка сжатия $=$ отброшенная энергия (монотонна по $K$); … (172) ошибка $=$ отброшенная энергия; …
>
> (202) … сжатие с точной ошибкой, …

**Проверка.** `src/process/ProcessFourierCompression.v:42, :61`:

```coq
Definition captured (c : nat -> Q) (K : nat) : Q := q_sum (fun i => c i * c i) K.

Lemma truncation_error_eq : forall (c : nat -> Q) (K N : nat),
  (K <= N)%nat ->
  captured c N == captured c K + q_sum (fun i => c (K + i)%nat * c (K + i)%nat) (N - K)%nat.
```

Доказательство — одно применение `q_sum_split` (разбиение конечной суммы в точке $K$). Предмет леммы —
произвольная последовательность `c`: ни сигнала $f$, ни преобразования, ни $\norm{f}^2$ в утверждении нет.
Слева стоит сумма квадратов самих коэффициентов, а в формуле страницы — $\norm{f}^2$; связывает их равенство
Парсеваля, которого в этом файле нет. Ни в одном из четырёх файлов главы не определены восстановленный по $K$
коэффициентам сигнал и разность между ним и $f$, так что «ошибка восстановления» объектом формализации не
является. О преобразовании Уолша в файле одно утверждение — оценка `walsh_captured_le_energy` (расхождение 3).

Теорема об ошибке восстановления для ортонормированных систем есть в Главе 7.4 — `fourier_error_eq`
(`ProcessFourierSeriesL2.v:57`: $\norm{f-P_K}^2=\norm{f}^2-$`captured`), но она стоит под посылкой `Hon`,
которой не удовлетворяет ни одна система (расхождение 4), и говорит о нормированной шкале; для сырого спектра
Уолша $(Hf)_i$, о котором говорит глава («для Уолша»), утверждения об ошибке восстановления нет нигде в `src`
(просмотрены все 19 файлов, где встречается слово «walsh»).

`Print Assumptions truncation_error_eq`, `captured_mono`: Closed under the global context. Цена названа верно.

**В чём расхождение.** Тождество, названное ошибкой восстановления, в формализации есть разбиение конечной
суммы на две части; что вторая часть равна квадрату расстояния от сигнала до его восстановления по первым $K$
коэффициентам, не доказано ни для Уолша, ни (под выполнимой посылкой) для ортонормированной системы.

**(а) Довести формализацию до слов главы.** Возможно, без аксиом. Предлагается новый файл
`src/process/ProcessWalshCompressionError.v` (существующие файлы не трогаются). Набросок проверен: `Check.v`,
разделы 0, 1, 3, 3b; все утверждения — Closed under the global context. Ниже `Nq k` — запись для
`inject_Z (Z.of_nat (pow2 k))`.

Сырая шкала Уолша, все $N=2^k$:

```coq
(* спектр, усечённый до первых K коэффициентов *)
Definition spec_trunc (c : nat -> Q) (K : nat) : nat -> Q :=
  fun i => if Nat.ltb i K then c i else 0.

(* восстановление по первым K сырым коэффициентам: f_K = (1/N) * H (усечённый спектр) *)
Definition walsh_rec (k K : nat) (f : nat -> Q) : nat -> Q :=
  fun m => op_apply (had k) (spec_trunc (op_apply (had k) f (pow2 k)) K) (pow2 k) m / Nq k.

(* оно же — частичная сумма разложения по функциям Уолша *)
Lemma walsh_rec_partial_sum : forall k f K m, (K <= pow2 k)%nat ->
  walsh_rec k K f m
  == q_sum (fun i => op_apply (had k) f (pow2 k) i * had k i m) K / Nq k.

Lemma dropped_energy : forall (c : nat -> Q) (K N : nat), (K <= N)%nat ->
  seq_inner (fun i => c i - spec_trunc c K i) (fun i => c i - spec_trunc c K i) N
  == q_sum (fun i => c (K + i)%nat * c (K + i)%nat) (N - K)%nat.

Lemma walsh_resid_as_transform : forall k f K m, (m < pow2 k)%nat ->
  f m - walsh_rec k K f m
  == op_apply (had k)
       (fun i => op_apply (had k) f (pow2 k) i - spec_trunc (op_apply (had k) f (pow2 k)) K i)
       (pow2 k) m / Nq k.
Proof.
  intros k f K m Hm. unfold walsh_rec.
  rewrite (op_apply_sub (had k) (op_apply (had k) f (pow2 k))
                        (spec_trunc (op_apply (had k) f (pow2 k)) K) (pow2 k) m).
  rewrite (walsh_HH k f m Hm).
  field. apply Nq_nz.
Qed.

(* N * ||f - f_K||^2 = сумма квадратов отброшенных коэффициентов *)
Theorem walsh_compression_error : forall k f K, (K <= pow2 k)%nat ->
  Nq k * seq_inner (fun m => f m - walsh_rec k K f m)
                   (fun m => f m - walsh_rec k K f m) (pow2 k)
  == q_sum (fun i => op_apply (had k) f (pow2 k) (K + i)%nat
                     * op_apply (had k) f (pow2 k) (K + i)%nat) (pow2 k - K)%nat.
Proof.
  intros k f K HK.
  pose proof (Nq_nz k) as Hnz.
  assert (Hd := dropped_energy (op_apply (had k) f (pow2 k)) K (pow2 k) HK).
  assert (Hp := parseval_walsh k
     (fun i => op_apply (had k) f (pow2 k) i - spec_trunc (op_apply (had k) f (pow2 k)) K i)).
  set (d := fun i => op_apply (had k) f (pow2 k) i - spec_trunc (op_apply (had k) f (pow2 k)) K i) in *.
  transitivity (Nq k * seq_inner (fun m => op_apply (had k) d (pow2 k) m / Nq k)
                                 (fun m => op_apply (had k) d (pow2 k) m / Nq k) (pow2 k)).
  { apply Qmult_comp; [ reflexivity | ].
    apply seq_inner_ext_bounded; intros m Hm; exact (walsh_resid_as_transform k f K m Hm). }
  transitivity (Nq k * ((1 / (Nq k * Nq k))
                        * seq_inner (op_apply (had k) d (pow2 k))
                                    (op_apply (had k) d (pow2 k)) (pow2 k))).
  { apply Qmult_comp; [ reflexivity | ].
    unfold seq_inner.
    rewrite <- (q_sum_scale (1 / (Nq k * Nq k))
                  (fun i => op_apply (had k) d (pow2 k) i * op_apply (had k) d (pow2 k) i)
                  (pow2 k)).
    apply q_sum_ext. intro i. field. exact Hnz. }
  rewrite Hp, Hd. field. exact Hnz.
Qed.

(* та же ошибка через энергию сигнала и захваченную энергию *)
Corollary walsh_compression_error_energy : forall k f K, (K <= pow2 k)%nat ->
  Nq k * seq_inner (fun m => f m - walsh_rec k K f m)
                   (fun m => f m - walsh_rec k K f m) (pow2 k)
  == Nq k * seq_inner f f (pow2 k) - captured (op_apply (had k) f (pow2 k)) K.

(* ошибка восстановления не возрастает при добавлении коэффициентов *)
Corollary walsh_compression_error_mono : forall k f K K',
  (K <= K')%nat -> (K' <= pow2 k)%nat ->
  seq_inner (fun m => f m - walsh_rec k K' f m) (fun m => f m - walsh_rec k K' f m) (pow2 k)
  <= seq_inner (fun m => f m - walsh_rec k K f m) (fun m => f m - walsh_rec k K f m) (pow2 k).
```

Ход доказательства главной теоремы: остаток $f-f_K$ есть $\tfrac1N H d$, где $d$ — отброшенная часть спектра
(`walsh_resid_as_transform`: линейность `op_apply` и обращение `walsh_HH`); равенство Планшереля
`parseval_walsh`, применённое к $d$, даёт $\norm{Hd}^2=N\norm{d}^2$; а $\norm{d}^2$ и есть сумма квадратов
отброшенных коэффициентов (`dropped_energy`). Вспомогательные леммы раздела 0 (`op_apply_ext_bounded`,
`op_apply_sub`, `seq_inner_ext_bounded`, `Nq_pos`, `Nq_nz`) — в `Check.v`. Имя `spec_trunc` взято, чтобы не
совпасть с `trunc` из `ProcessLadderRational.v`.

Нормированная шкала (формула стр. 61–67 дословно) — под выполнимой посылкой «первые $K_0$ векторов
ортонормированы» и при равенстве Парсеваля для этих $K_0$ векторов:

```coq
Section ONScale.
Variable e : nat -> nat -> Q.
Variable N K0 : nat.
Hypothesis Hon : forall i j, (i < K0)%nat -> (j < K0)%nat ->
  seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0).
Variable f : nat -> Q.

Local Notation cf := (fun k => seq_inner (e k) f N).
Local Notation Resid K := (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K).
Local Notation errK K := (seq_inner (Resid K) (Resid K) N).

Theorem on_error_eq_tail :
  captured cf K0 == seq_inner f f N ->
  forall K, (K <= K0)%nat ->
  errK K == q_sum (fun i => seq_inner (e (K + i)%nat) f N * seq_inner (e (K + i)%nat) f N)
                  (K0 - K)%nat.
Proof.
  intros Hpars K HK.
  rewrite (on_error_eq K HK).                 (* = resid_norm_b из ProcessL2Orthonormal.v *)
  pose proof (truncation_error_eq cf K K0 HK) as Hs. cbv beta in Hs.
  lra.
Qed.
End ONScale.
```

Обе посылки выполнимы; примеры проверены: стандартный базис при всяком $N$ (`std_error_eq_tail`) и
нормированный Уолш при рациональном $s$ с $s^2=N$ — то есть при чётном $k$:

```coq
Theorem walsh_normalised_on : forall k (s : Q), s * s == Nq k ->
  forall i j, (i < pow2 k)%nat -> (j < pow2 k)%nat ->
  seq_inner (fun m => had k i m / s) (fun m => had k j m / s) (pow2 k)
  == (if Nat.eqb i j then 1 else 0).

Theorem walsh_normalised_parseval : forall k (s : Q), s * s == Nq k ->
  forall f : nat -> Q,
  captured (fun i => seq_inner (fun m => had k i m / s) f (pow2 k)) (pow2 k)
  == seq_inner f f (pow2 k).

Theorem walsh_normalised_error_eq_tail : forall k (s : Q), s * s == Nq k ->
  forall (f : nat -> Q) (K : nat), (K <= pow2 k)%nat ->
  (* ||f - P_K||^2 = сумма квадратов отброшенных нормированных коэффициентов *) …

Lemma Nq_double : forall j, Nq j * Nq j == Nq (j + j).           (* k = 2j: годится s = 2^j *)
Example walsh4_error_eq_tail : …                                   (* N = 4, s = 2 *)
Lemma walsh_odd_no_rational_norm : forall j (s : Q), ~ s * s == Nq (S (j + j)).
```

Последняя лемма — вторая сторона слов «рациональна лишь при чётном $k$» (стр. 204): при нечётном $k$
рационального $s$ нет (через `no_rational_sqrt2`, `analysis/Sqrt2Irrational.v:200`); для целого корня то же
записано в `stdlib/QubitCeiling.v:97`.

**(б) Поправить слова.** Если принят путь (а), основной текст остаётся как есть; уточняется сноска 2 (она же
снимает расхождение 3):

> [^2]: В `ProcessFourierCompression.v`: `captured`$(c,K)=\sum_{i<K}c_i^2$; `truncation_error_eq` даёт баланс
> `captured`$(c,N)=$`captured`$(c,K)+$хвост; `captured_mono` — монотонность по $K$. Что хвост есть именно
> ошибка восстановления, доказано в `ProcessWalshCompressionError.v`: для сигнала $f_K$, собранного по первым
> $K$ сырым коэффициентам Уолша, $N\norm{f-f_K}^2$ равно сумме квадратов отброшенных коэффициентов
> (`walsh_compression_error`); в нормированной шкале, при равенстве Парсеваля, — `on_error_eq_tail`. Для Уолша
> полная энергия есть $N\norm{f}^2$ (Планшерель), так что отброшенная энергия равна
> $N\norm{f}^2-$`captured`$(Hf,K)$ — `walsh_tail_eq`. 0 аксиом.

и в сноске 1 добавляется файл: «…`ProcessWalshConvolutionGeneral.v` (7), `ProcessWalshCompressionError.v`; все
0 `Admitted`, 0 аксиом».

Если формализация остаётся как есть, слова об ошибке восстановления приходится заменить словами о балансе
энергии спектра (ход мысли сохраняется):

> (22–23) Доказано над ℚ, без аксиом. Энергия спектра расщепляется на захваченную первыми $K$ коэффициентами и
> сумму квадратов отброшенных, и захваченная часть монотонна по $K$; …
>
> (41) Энергия спектра = захваченная + сумма квадратов отброшенных коэффициентов (захваченная монотонна); …
>
> (57–69) Сжатие спектрального типа просто: вычислить спектр, оставить первые $K$ коэффициентов, отбросить
> остальные. Качество сжатия измеряется *отброшенной хвостовой энергией*:
> $$\sum_{i<N} c_i^2 \;=\; \underbrace{\sum_{i<K} c_i^2}_{\text{сохранено}} \;+\;
> \underbrace{\sum_{K\le i<N} c_i^2}_{\text{отброшено}} ,$$
> так что недобранная энергия равна второй сумме — ровно тому, что усечение выкинуло.[^2] Что левая часть есть
> $\norm{f}^2$, а вторая сумма — квадрат ошибки восстановления, дают равенство Парсеваля и тождество остатка
> Главы 7.4; в файлах настоящей главы доказан сам баланс сумм. Захваченная энергия монотонно растёт с $K$ …
>
> (93–94) *Энергия спектра = захваченная + отброшенная — точное рациональное тождество, …*
>
> (154) баланс энергии спектра: захваченная $+$ отброшенная (захваченная монотонна по $K$); …
>
> (172) баланс энергии: захваченная $+$ отброшенная; …
>
> (202) … сжатие с точным балансом энергии, …

## Расхождение 2. «Полосно-ограниченный сигнал восстанавливается без потерь»: теорема — о равенстве двух частичных сумм квадратов (стр. 24–25, 78–82, 93–95; сноска 3)

**Было:**

> (24–25) *полосно-ограниченный* сигнал (спектр в первых $K$ модах) восстанавливается *без потерь*.
>
> (78–82) Если спектр сигнала *сосредоточен* на первых $K$ модах (относительно выбранного порядка Уолша) — то
> есть $c_i=0$ при $i\ge K$,— то отброшенная энергия равна нулю, и первые $K$ коэффициентов восстанавливают
> сигнал *без потерь*: захваченная энергия совпадает с полной.
>
> (93–94) … а полосно-ограниченный сигнал сжимается без потерь.
>
> (сноска 3) … Точное рациональное сжатие полосно-ограниченного сигнала.

**Проверка.** `src/process/ProcessWalshCompaction.v:41`:

```coq
Theorem walsh_compaction : forall (c : nat -> Q) (K N : nat),
  (K <= N)%nat ->
  (forall i, (K <= i < N)%nat -> c i == 0) ->
  captured c N == captured c K.
```

Предмет теоремы — произвольная последовательность `c`; в утверждении и в доказательстве преобразование Уолша
не участвует (доказательство: `truncation_error_eq` и «сумма нулей равна нулю»). Заключение — равенство двух
частичных сумм квадратов. Пример `compaction_4_example` (`:58`) — последовательность $(5,7,0,0)$, не спектр
названного сигнала. Утверждения «сигнал, собранный по первым $K$ коэффициентам, совпадает с $f$» в
формализации нет. `Print Assumptions`: Closed under the global context. Формулу теоремы сноска 3 приводит
точно.

**В чём расхождение.** Доказано, что у последовательности с нулями от $K$ до $N$ сумма квадратов до $N$ равна
сумме до $K$; что первые $K$ коэффициентов Уолша восстанавливают сам сигнал, теоремой не записано.

**(а) Довести формализацию.** Возможно, без аксиом, и в обе стороны. Проверено (`Check.v`, раздел 2; Closed
under the global context):

```coq
Theorem walsh_bandlimited_lossless : forall k f K,
  (forall i, (K <= i < pow2 k)%nat -> op_apply (had k) f (pow2 k) i == 0) ->
  forall m, (m < pow2 k)%nat -> walsh_rec k K f m == f m.
Proof.
  intros k f K Hz m Hm. unfold walsh_rec.
  rewrite (op_apply_ext_bounded (had k) (spec_trunc (op_apply (had k) f (pow2 k)) K)
                                (op_apply (had k) f (pow2 k)) (pow2 k) m).
  - rewrite (walsh_HH k f m Hm). field. apply Nq_nz.
  - intros j Hj. unfold spec_trunc. destruct (Nat.ltb j K) eqn:E.
    + reflexivity.
    + apply Nat.ltb_ge in E. symmetry. apply Hz. lia.
Qed.

(* восстановление точно тогда и только тогда, когда спектр сосредоточен на первых K модах *)
Theorem walsh_lossless_iff : forall k f K, (K <= pow2 k)%nat ->
  (forall m, (m < pow2 k)%nat -> walsh_rec k K f m == f m)
  <-> (forall i, (K <= i < pow2 k)%nat -> op_apply (had k) f (pow2 k) i == 0).
```

Прямая сторона — усечённый спектр совпадает с полным, остаётся обращение `walsh_HH`. Обратная — из
`walsh_compression_error` (расхождение 1): нулевая ошибка даёт нулевую сумму квадратов отброшенных
коэффициентов, а по `q_sum_sq_zero` (`ProcessL2Parseval.v:52`) каждый из них равен нулю. Положить можно в тот
же новый файл.

**(б) Поправить слова.** После (а) основной текст остаётся; уточняется сноска:

> [^3]: `walsh_compaction` в `ProcessWalshCompaction.v`: при $c_i=0$ для $K\le i<N$ выполнено
> `captured`$(c,N)=$`captured`$(c,K)$ — хвост нулевой. Само восстановление — `walsh_bandlimited_lossless` в
> `ProcessWalshCompressionError.v`: если $(Hf)_i=0$ при $K\le i<N$, сигнал, собранный по первым $K$
> коэффициентам, совпадает с $f$ во всех $N$ точках; обратное — `walsh_lossless_iff`. 0 аксиом. Точное
> рациональное сжатие полосно-ограниченного сигнала.

Без (а):

> (24–25) у *полосно-ограниченного* сигнала (спектр в первых $K$ модах) первые $K$ коэффициентов несут всю
> энергию спектра.
>
> (78–82) Если спектр сигнала *сосредоточен* на первых $K$ модах (относительно выбранного порядка Уолша) — то
> есть $c_i=0$ при $i\ge K$,— то отброшенная энергия равна нулю: первые $K$ коэффициентов несут всю энергию
> спектра — захваченная энергия совпадает с полной.[^3]
>
> (93–94) … а у полосно-ограниченного спектра отброшенная энергия нулевая.
>
> (сноска 3, последняя фраза) Точный баланс энергии полосно-ограниченного спектра; теорема о восстановлении
> самого сигнала отдельно не записана.

## Расхождение 3. «Для Уолша ошибка контролируется равенством Планшереля»: названная теорема — оценка захваченной энергии сверху (стр. 23–24; сноска 2)

**Было:**

> (23–24) для Уолша она контролируется равенством Планшереля;
>
> (сноска 2) Для Уолша полная энергия есть $N\norm{f}^2$ (Планшерель), так что ошибка контролируется
> Парсевалем — `walsh_captured_le_energy`. 0 аксиом.

**Проверка.** `src/process/ProcessFourierCompression.v:79`:

```coq
Theorem walsh_captured_le_energy : forall k f K,
  (K <= pow2 k)%nat ->
  captured (op_apply (had k) f (pow2 k)) K
  <= inject_Z (Z.of_nat (pow2 k)) * seq_inner f f (pow2 k).
```

Утверждение: энергия первых $K$ коэффициентов Уолша не превосходит $N\norm{f}^2$ (неравенство Бесселя для
сырого спектра; получено из `captured_mono` и `parseval_walsh`). Ошибка — отброшенная энергия — в утверждение
не входит; равенства, которое выражало бы её через энергию сигнала, в файле нет. `Print Assumptions`: Closed
under the global context.

**В чём расхождение.** Словами названо управление ошибкой, а теорема даёт одностороннюю оценку другой
величины — захваченной энергии; из неё об ошибке следует только неотрицательность.

**(а) Довести формализацию.** Возможно, без аксиом: точное равенство следует из `truncation_error_eq` и
`parseval_walsh`. Проверено (`Check.v`, раздел 1; Closed under the global context):

```coq
Theorem walsh_tail_eq : forall k f K, (K <= pow2 k)%nat ->
  q_sum (fun i => op_apply (had k) f (pow2 k) (K + i)%nat
                  * op_apply (had k) f (pow2 k) (K + i)%nat) (pow2 k - K)%nat
  == Nq k * seq_inner f f (pow2 k) - captured (op_apply (had k) f (pow2 k)) K.
Proof.
  intros k f K HK.
  pose proof (truncation_error_eq (op_apply (had k) f (pow2 k)) K (pow2 k) HK) as Hs.
  unfold captured in Hs at 1.
  change (q_sum (fun i => op_apply (had k) f (pow2 k) i * op_apply (had k) f (pow2 k) i)
                (pow2 k))
    with (seq_inner (op_apply (had k) f (pow2 k)) (op_apply (had k) f (pow2 k)) (pow2 k)) in Hs.
  rewrite (parseval_walsh k f) in Hs. lra.
Qed.
```

Вместе с `walsh_compression_error` (расхождение 1) это даёт $N\norm{f-f_K}^2=N\norm{f}^2-$`captured`$(Hf,K)$
(`walsh_compression_error_energy`) — ошибка действительно определена равенством Планшереля.

**(б) Поправить слова.** После (а) — сноска 2 в редакции расхождения 1; основной текст остаётся. Без (а):

> (23–24) для Уолша захваченная энергия ограничена полной энергией сигнала по равенству Планшереля;
>
> (сноска 2) … Для Уолша полная энергия есть $N\norm{f}^2$ (Планшерель), так что захваченная энергия любых
> первых $K$ коэффициентов её не превосходит — `walsh_captured_le_energy`. 0 аксиом.

## Расхождение 4. Итоги Глав 7.1 и 7.4 названы доказанным ядром, а их теоремы стоят под посылкой, которой не удовлетворяет ни одна система (стр. 9–10, 187–189, 193–194, 199–203)

**Было:**

> (9–10) Глава 7.4 дала конечное ядро контроля усечений: ошибка усечения равна отброшенной хвостовой энергии,
> не возрастает при добавлении коэффициентов и зануляется при Парсевале.
>
> (187–189) *Глава 7.1* переформулировала L<sup>2</sup>-аппарат Части VI как теорию коэффициентов Фурье:
> ортонормированная система, проекция, Бессель, Парсеваль, наилучшее приближение.
>
> (193–194) *Глава 7.4* дала конечное ядро контроля усечений: ошибка усечения равна хвостовой энергии и
> монотонно не возрастает.
>
> (199–203) Доказанное рациональное ядро Части VII — над ℚ, без новых аксиом: … неравенство Бесселя и критерий
> Парсеваля, наилучшее приближение, конечное ядро контроля усечений, …

**Проверка.** Теоремы, на которые ссылаются Главы 7.1 и 7.4 (сноски 6–11 Главы 7.1 и 3–7 Главы 7.4), стоят в
разделах с посылкой

```coq
Hypothesis Hon : forall i j, seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0).
```

(`ProcessL2BesselGeneral.v:119`, `ProcessL2Parseval.v:80`, `ProcessBestApproximation.v:70`,
`ProcessFourierSeriesL2.v:47`). После закрытия раздела посылка входит в утверждение каждой из них — проверено
командой `Check` (`PA2.out`): `bessel_general` (`:175`), `parseval_iff_complete` (`:142`), `best_approx_ge`
(`:161`), `best_approx_unique` (`:176`), `fourier_error_eq` (`:57`), `fourier_error_monotone` (`:77`),
`fourier_error_zero_iff` (`:87`), `fourier_partial_best` (`:94`). `Print Assumptions` всех восьми: Closed under
the global context — цена названа верно.

Посылка требует ортонормированности при **всех** натуральных номерах на $N$ координатах и невыполнима ни при
каком $N$: `on_all_indices_unsat` (`src/process/ProcessL2Orthonormal.v:134`; находка проверки Части VI). Ни
нормированный Уолш, ни стандартный базис ей не удовлетворяют; теоремы под ней не имеют ни одного примера.

Собственные результаты Главы 7.2 этим не затронуты: `hadamard_orthogonal`, `parseval_walsh`, `walsh_HH`,
`had_character` доказаны без разделов и посылок, для всех $k$. Не затронуты и четыре файла настоящей главы.

**В чём расхождение.** В перечень доказанного ядра Части VII входят неравенство Бесселя, критерий Парсеваля,
наилучшее приближение и контроль усечений, а соответствующие теоремы в формализации верны впустую — их посылке
не удовлетворяет ни одна система векторов.

**(а) Довести формализацию.** Бо́льшая часть уже сделана новым файлом `ProcessL2Orthonormal.v` (посылка:
ортонормированы первые $K_0$ векторов, $K\le K_0$; примеры — `std_basis_on`, `rot_orthonormal`,
`parseval_std_all`):

| слова главы | теорема под выполнимой посылкой |
|---|---|
| неравенство Бесселя | `bessel_b` (`:243`) |
| критерий Парсеваля | `parseval_iff_resid_zero_b` (`:286`), `parseval_iff_complete_b` (`:296`) |
| наилучшее приближение | `best_approx_b` (`:256`) |
| ошибка усечения = энергия минус захваченная | `resid_norm_b` (`:231`), `energy_split_b` (`:276`) |
| ошибка зануляется при Парсевале | `parseval_iff_resid_zero_b` (`:286`) |

В новом файле нет двух вещей, которые глава называет: невозрастания ошибки при добавлении коэффициентов и
единственности наилучшего приближения. Обе дописываются без аксиом; проверено (`Check.v`, раздел 3, в разделе
с той же посылкой `Hon` для `i, j < K0`; Closed under the global context):

```coq
Lemma on_error_eq : forall K, (K <= K0)%nat ->
  errK K == seq_inner f f N - captured cf K.
Proof.
  intros K HK. rewrite (ProcessL2Orthonormal.resid_norm_b e N K0 Hon f K HK).
  unfold captured. reflexivity.
Qed.

Lemma on_error_monotone : forall K K', (K <= K')%nat -> (K' <= K0)%nat ->
  errK K' <= errK K.
Proof.
  intros K K' HKK HK'.
  rewrite (on_error_eq K' HK'), (on_error_eq K ltac:(lia)).
  pose proof (captured_mono cf K K' HKK) as Hm. lra.
Qed.

Lemma on_error_zero_iff : forall K, (K <= K0)%nat ->
  errK K == 0 <-> captured cf K == seq_inner f f N.

Theorem on_best_approx_gap : forall (a : nat -> Q) (K : nat), (K <= K0)%nat ->
  seq_inner (fun m => f m - q_sum (fun k => a k * e k m) K)
            (fun m => f m - q_sum (fun k => a k * e k m) K) N
  == errK K + q_sum (fun k => (a k - seq_inner (e k) f N) * (a k - seq_inner (e k) f N)) K.

Theorem on_best_approx_unique : forall (a : nat -> Q) (K : nat), (K <= K0)%nat ->
  seq_inner (fun m => f m - q_sum (fun k => a k * e k m) K)
            (fun m => f m - q_sum (fun k => a k * e k m) K) N
  == errK K ->
  forall k, (k < K)%nat -> a k == seq_inner (e k) f N.
```

Там же — пример, которого Главе 7.1 недостаёт: нормированный Уолш удовлетворяет выполнимой посылке при
рациональном $s$ с $s^2=N$ (`walsh_normalised_on`; при $k=2j$ годится $s=2^j$ — `walsh_even_normalised_on`), и
равенство Парсеваля для него выполнено при всяком $f$ (`walsh_normalised_parseval`).

**(б) Поправить слова.** Если дополнения приняты, слова настоящей главы остаются как есть: каждое названное в
итогах утверждение получает теорему под выполнимой посылкой; меняются имена в сносках Глав 7.1 и 7.4 (предмет
их ведомостей). Если формализация остаётся в положении на 15.11 (есть `ProcessL2Orthonormal.v`, нет
невозрастания ошибки и единственности), достаточно убрать недоказанное:

> (9–10) Глава 7.4 дала конечное ядро контроля усечений: ошибка усечения равна отброшенной хвостовой энергии и
> зануляется при Парсевале.
>
> (193–194) *Глава 7.4* дала конечное ядро контроля усечений: ошибка усечения равна хвостовой энергии.

Абзац стр. 208–212 повторяет тот же перечень без слова «доказано» и отдельной правки не требует.

## Расхождение 5. Число: `ProcessWalshCompaction.v` — «(1)» (сноска 1)

**Было:**

> (сноска 1) … `ProcessWalshCompaction.v` (1), …

**Проверка.** `grep -c 'Qed\.' src/process/ProcessWalshCompaction.v` — 2: теорема `walsh_compaction` (`:41`) и
пример `compaction_4_example` (`:58`). «1 Qed» стоит в шапке файла (`:25`). Для трёх других файлов страница
называет действительный счёт `Qed` вместе с примерами (6, 2, 7 — у `ProcessFourierCompression.v` шестое
утверждение есть пример `compression_4_example`).

**В чём расхождение.** Число повторяет устаревшую шапку; в файле два доказанных утверждения.

**(а)** Поправить шапку `ProcessWalshCompaction.v`: «STATUS: 2 Qed, 0 Admitted, 0 axioms» (правка комментария).

**(б)** «`ProcessWalshCompaction.v` (2),».

## Сомнительные места, расхождением не являющиеся

- **Что значит «быстрый» (стр. 15, 99–111, 159–160; сноска 4).** `fwht` (`ProcessFastWalsh.v:41`) —
  рекурсия на функциях `nat -> Q`: значение в одной точке раскрывается двумя рекурсивными вызовами на каждом
  уровне, то есть $2^k-1$ сложениями и вычитаниями; общих промежуточных значений определение не хранит. При
  вычислении всех $N$ значений прямо по определению получается порядка $N^2$ сложений — тот же порядок, что у
  матричного преобразования. Счёт $O(N\log N)$ относится к записи бабочки с хранением преобразованных половин
  (список, массив), которой в формализации нет. Расхождением не записано, потому что страница говорит прямо:
  доказано равенство, а не оценка стоимости (стр. 29–31, 110–111, 177–179, 206). Слова «тот же результат,
  меньшая стоимость» (стр. 160) стоят в разборе ролей, не в перечне доказанного.
  Если нужно, чтобы счёт операций стал теоремой, это делается без аксиом. Проверено (`Check.v`, раздел 6;
  Closed under the global context):

  ```coq
  (* результат и число выполненных сложений и вычитаний *)
  Fixpoint fwht_c (k : nat) (l : list Q) : list Q * nat :=
    match k with
    | O => (l, O)
    | S k' =>
        let ra := fwht_c k' (firstn (pow2 k') l) in
        let rb := fwht_c k' (skipn (pow2 k') l) in
        let s := zipw Qplus (fst ra) (fst rb) in
        let d := zipw Qminus (fst ra) (fst rb) in
        (s ++ d, (snd ra + snd rb + (length s + length d))%nat)
    end.

  Theorem fwht_c_ops : forall k l,
    length l = pow2 k -> snd (fwht_c k l) = (k * pow2 k)%nat.

  Theorem fwht_c_correct : forall k l, length l = pow2 k ->
    forall i, (i < pow2 k)%nat ->
    nth i (fst (fwht_c k l)) 0 == fwht k (fun j => nth j l 0) i.

  Theorem fwht_c_cost_and_value : forall k l, length l = pow2 k ->
    snd (fwht_c k l) = (k * pow2 k)%nat
    /\ forall i, (i < pow2 k)%nat ->
         nth i (fst (fwht_c k l)) 0 == op_apply (had k) (fun j => nth j l 0) (pow2 k) i.
  ```

  То есть бабочка на списке длины $N=2^k$ выполняет ровно $k\cdot 2^k=N\log_2 N$ сложений и вычитаний и даёт
  значения матричного преобразования (пример: $N=8$, 24 операции — `fwht_c_8`). Это счёт арифметических
  операций одной записи алгоритма, а не общая теория сложности; с такой оговоркой стр. 110–111 можно было бы
  усилить: «…Сама оценка — $N\log_2 N$ сложений и вычитаний для бабочки на списке — доказана отдельно
  (`fwht_c_cost_and_value`)».
- **«Совпадают как функции» (стр. 106–107).** Равенство доказано в точках $i<2^k$ и с точностью до `Qeq`. Вне
  этой области функции различны (при $k=0$: `fwht 0 f i = f i`, а `op_apply (had 0) f 1 i == f 0`). Для
  преобразования размера $N$ другой области нет, поэтому запись — `ok`.
- **Свёртка через преобразование (стр. 129–133).** Формула «преобразовать, перемножить, применить $H$,
  разделить на $N$» теоремой в `src` не записана; страница доказанной её не называет. Выведена из
  `walsh_convolution` и `walsh_HH` (`Check.v`, раздел 4; Closed):
  `walsh_convolution_inverse : Nq k * dconv f g (pow2 k) n == op_apply (had k) (fun i => (Hf) i * (Hg) i) (pow2 k) n`
  и `convolution_via_fwht : dconv f g (pow2 k) n == fwht k (fun i => fwht k f i * fwht k g i) n / Nq k`
  при $n<2^k$. Оценка $O(N\log N)$ для этого пути не доказывается (оговорено на стр. 29–31).
- **Имя `walsh_compaction`.** В утверждении преобразования Уолша нет (см. расхождение 2); сноска 3 приводит
  формулу точно, поэтому запись сноски — `ok`.
- **«Захваченная энергия монотонно растёт» (стр. 69).** `captured_mono` — неубывание (нестрогое). «Ошибка
  убывает» для хвоста при фиксированном $N$ — следствие `truncation_error_eq` и `captured_mono`, отдельной
  леммой не записанное; для ошибки восстановления — `walsh_compression_error_mono` (`Check.v`).
- **Формула в сырой шкале (стр. 72–74).** «Та же формула читается с масштабом $N$» — равенство
  $N\norm{f}^2=$ захвачено $+$ отброшено для $(Hf)_i$ теоремой не записано; следует из `truncation_error_eq`
  и `parseval_walsh` (`Check.v`, `walsh_tail_eq`).
- **«Рациональна лишь при чётном $k$» (стр. 204).** Стоит в перечне границ; в файлах Части VII теоремы нет.
  Целочисленная форма есть в `src/stdlib/QubitCeiling.v` (глава его не называет): `even_walsh_perfect_square`
  (`:88`, $2^{2m}$ — квадрат целого) и `odd_walsh_role_limit` (`:97`, $k\cdot k\ne 2^{2m+1}$ для целого $k$);
  там своё определение `pow2 : nat -> Z`. Для рационального $s$ обе стороны проверены в пробном файле:
  `Nq_double` (при $k=2j$ годится $s=2^j$) и `walsh_odd_no_rational_norm` (при нечётном $k$ рационального $s$
  с $s^2=N$ нет).
- **«Вентиль Адамара (Глава 7.2) уже есть мост в квантовые вычисления» (стр. 216–217).** Теоремы здесь не
  названы, слова «доказано» нет; предмет ведомости Главы 7.2. Замечено: в `ProcessHadamardGate.v` нормированный
  вентиль стоит в разделе с посылкой `Hs2 : s2inv * s2inv * 2 == 1` для рационального `s2inv` (`:69`); она
  невыполнима (`Check.v`, `hgate_premise_unsat`, через `no_rational_sqrt2`). Под ней стоит `hgate_involution`
  (`:76`); `hgate_superposition` (`:92`) посылкой не пользуется и после закрытия раздела её не несёт
  (`PA2.out`). Ненормированные утверждения ($H_2$ из $\pm1$, $H(Hf)=2f$) посылки не требуют.
- **«Преобразование как самосопряжённый оператор с сохранением энергии (Часть VI)» (стр. 217–218).** В
  формализации это `walsh_op_symmetric` (`ProcessFourierON.v:53`: матрица симметрична на первых $2^k$
  координатах) и `parseval_walsh` (`:91`); обе без посылок. Дальнейшее («ведёт к спектральным методам физики»)
  — анонс, с формализацией не сверялся.

## Вне главы

- Шапки устарели. `ProcessWalshCompaction.v:25` — «1 Qed» при двух. `ProcessWalshCharacter.v:26` — «7 Qed» при
  восьми (число повторено в сноске 1 Главы 7.2). `ProcessWalshConvolution.v:16–19, 25–26` называет общую
  теорему о свёртке «фронтиром», хотя она доказана в `ProcessWalshConvolutionGeneral.v`.
  `ProcessWalshHadamard.v:13–16` говорит, что полная ортогональность проверена для $N=2$ и $N=4$, а следующим
  абзацем (`:18–19`) — что доказана общая; верно второе (`hadamard_orthogonal`, `:152`).
- `ProcessFourierCompression.v`, шапка (`:10–14`): «the truncation error is controlled by Parseval» — в файле
  об Уолше одна оценка сверху (расхождение 3); заголовок раздела (`:76`) «captured energy of any K
  coefficients» — теорема о первых $K$.
- `ProcessFourierSynthesis.v` (глава его не называет): три «моста» — `walsh_orthogonal_and_plancherel` есть
  конъюнкция `hadamard_orthogonal` и `parseval_walsh`; `walsh_invertible` дословно совпадает с `walsh_HH`
  (доказательство — `exact walsh_HH`); `walsh_compression_within_energy` — `walsh_captured_le_energy` с правой
  частью, переписанной по `parseval_walsh`. Нового содержания файл не добавляет. Все три — Closed under the
  global context.
- Посылка `Hon` при всех номерах стоит в `ProcessBestApproximation.v:70` и `ProcessFourierSeriesL2.v:47`
  (Главы 7.1 и 7.4); сноска 4 Главы 7.1 называет нормированный Уолш системой, удовлетворяющей `Hon`, — в этой
  записи посылки ей не удовлетворяет ни одна система (расхождение 4). Выполнимой посылке нормированный Уолш
  удовлетворяет при чётном $k$ (`Check.v`, `walsh_normalised_on`, `walsh_even_normalised_on`).
- `ProcessHadamardGate.v:69`: посылка `s2inv * s2inv * 2 == 1` над ℚ невыполнима — см. сомнительные места;
  сказанное относится к сноскам 8–9 Главы 7.2.
