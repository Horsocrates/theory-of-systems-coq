# Глава VII.1 «Ортонормированные системы и коэффициенты Фурье» — заметки к ведомости (15.11.2026)

Ведомость: `part07-ch01.json` — 49 ручных записей + 4 автоматических (упоминания файлов
`ProcessBestApproximation.v`, `ProcessCompactSpectral.v`, `ProcessWalshHadamard.v`, `PythagoreanTriples.v`);
`merge --dry` проходит без замечаний, список «без сверки» пуст. Вердикты ручных записей: ok — 25,
mismatch-statement — 24. Расхождений цены, имён без объявления и неверных чисел нет.

Двадцать четыре записи с расхождением относятся к четырём местам: восемнадцать — к расхождению 1 (посылка
`Hon`), одна — к расхождению 2 (свидетель), четыре — к расхождению 3 (нормированная система Уолша и параметр
$s$), одна — к расхождению 4 (слово «ортонормированную» в анонсе).

Глава называет семь файлов: `ProcessL2BesselGeneral.v` (10 `Qed`), `ProcessL2Parseval.v` (7),
`ProcessBestApproximation.v` (9), `ProcessFourierON.v` (5), `ProcessWalshHadamard.v` (12) — прочитаны целиком;
`ProcessCompactSpectral.v` (6) и `stdlib/PythagoreanTriples.v` (21) — в тех частях, на которые глава ссылается.
Прочитаны также `ProcessL2Orthonormal.v` (36 `Qed`, файл шага 5 Части VI) и нужные объявления
`ProcessFubiniGeneral.v`. Строк `Axiom`, `Parameter`, `Admitted` в этих файлах нет. `Print Assumptions` снят для
всех объявлений пяти первых файлов и для всех названных главой имён — каждое «Closed under the global context».
Цена на странице («без единой аксиомы», «0 аксиом») названа верно всюду. Исходники в репозитории и в собранной
копии совпадают (`diff`).

Пять имён, которые инструмент показал без объявления: `ring`, `lra`, `vm_compute` — тактики; `Admitted` —
ключевое слово; `Hon` — посылка раздела (`Hypothesis`), после закрытия раздела — условие каждой теоремы, а не
объявление. Для каждого в ведомости есть запись; `Hon` — предмет расхождения 1.

Пробные файлы лежат в `C:/Users/abary/tos-audit-build/_part07/ch01/`:

- `status.txt` — вывод `tom-status.cjs chapter 07/01`;
- `Check.v`, `Check.out` — пробные доказательства, разделы 1–6 по местам главы (39 `Qed`). Собирается; все 29
  утверждений, для которых снят `Print Assumptions`, — «Closed under the global context».

В `src` и в собранной копии ничего не менялось; база связей не менялась (`merge` запускался только с `--dry`).

## Что проверить не удалось

- Первый абзац главы (стр. 9–14) пересказывает Часть VI (мера без Аксиомы Выбора, Рисс–Фишер, «изометрии
  квантовой динамики»); по содержанию не сверялся — это предмет ведомостей Части VI.
- Отсылки к Главам 7.2, 7.3, 7.4, к Части II, к Главам 4.3 и 4.4 по содержанию не сверялись. Сверены адреса:
  Глава 7.2 — «Уолш–Адамар: преобразование без трансцендентностей», 7.3 — «Тригонометрия и комплексный DFT:
  где граница», 7.4 — «Сходимость рядов Фурье в L²», 4.3 — «Точка как класс эквивалентности процессов», 4.4 —
  «Несчётность процессов»; Глава 5.7 («Теорема Фубини на процессах») действительно разбирает `q_sum_swap`.
- Вариант исправления расхождения 1 «на месте» (замена посылки `Hon` в существующих файлах) не собирался.
- Предлагаемые дополнения собраны как пробный файл поверх готовых модулей; как файл внутри `src` с записью в
  `_CoqProject` они не собирались.
- Сведения о классической математике (классическая формулировка неравенства Бесселя, равенство Планшереля) вне
  предмета аудита.
- Английская страница и LaTeX-исходник главы не смотрелись.

Всё остальное проверено по исходнику и компилятору.

## Расхождение 1. Теоремы главы доказаны под посылкой `Hon` «для всех номеров», которой не удовлетворяет ни одна система (стр. 35–41, 50–52, 106–110, 153–157, 168–170, 184–186, 202–203, 225–226, 232–233, 244–245, 266, 272–274; сноски 6, 8, 9)

**Было:**

> (35–41) Глава работает с *конечной* ортонормированной системой $\{e_k\}_{k<K}$ из $K$ векторов на $N$
> координатах над ℚ и доказывает о ней всё, что нужно для теории коэффициентов: … неравенство Бесселя … и
> равенство Парсеваля как *критерий полноты* — всё это *без единой аксиомы*.
>
> (50–52) *Первый* — конечная ортонормированная система на $N$ координатах: здесь Бессель, тождество энергии и
> критерий полноты доказаны точно над ℚ, без аксиом.
>
> (106–110) В коде это *гипотеза* `Hon` раздела об ортонормированных системах — явно предъявленное условие на
> конкретный набор $e$, а не существование «какого-то базиса». Система конечна и рациональна; никакого
> завершённого бесконечного базиса здесь нет и не требуется.
>
> (153–157) Сначала промежуточное: $K$-й вектор ортогонален оболочке первых $K$ … Следствие: для всех уже
> снятых направлений $j<K$ выполнено $\inner{e_j}{r_K}_N = c_j - c_j = 0$ …
>
> (168–170) Это *теорема Пифагора* для ортогонального разложения …
>
> (184–186) и это *доказанное тождество*, а не эвристика: … коэффициенты Фурье суть *единственный* минимум.
>
> (202–203) Энергия, захваченная любым числом $K$ направлений, не превосходит полной энергии функции.
>
> (225–226) Полная энергия функции в точности делится между тем, что схватило разложение, и тем, что осталось в
> невязке.
>
> (232–233, 244–245) *Парсеваль выполнен тогда и только тогда, когда норма остатка равна нулю*. … Это и есть
> честное конструктивное содержание формулы «Парсеваль $=$ критерий полноты».
>
> (266) Доказано конечное: критерий полноты на $N$ координатах.
>
> (272–274) Всё предыдущее говорилось об *абстрактной* ортонормированной системе, заданной гипотезой `Hon`.
>
> (сноска 6) `proj_ortho` … Отсюда `coef_e_resid` … Оба в `ProcessL2BesselGeneral.v`, 0 аксиом.
>
> (сноска 8) … `best_approx_eq`; … `best_approx_ge`; … `best_approx_unique` … Все — в
> `ProcessBestApproximation.v`, 0 аксиом.
>
> (сноска 9) `bessel_general` … Это общее неравенство Бесселя для произвольной конечной ортонормированной
> системы — не привязанное к конкретному базису.

**Проверка.** `src/process/ProcessL2BesselGeneral.v:115–119` (та же строка — `ProcessL2Parseval.v:80`,
`ProcessBestApproximation.v:70`):

```coq
Section ON.
Variable e : nat -> nat -> Q.
Variable N : nat.
Hypothesis Hon : forall i j, seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0).
```

`seq_inner a b N` есть $\sum_{m<N} a_m b_m$ (`ProcessCompactSpectral.v:51`). Посылка требует ортонормированности
векторов `e i` при **всех** натуральных `i`, `j` — бесконечного ортонормированного семейства на `N` координатах;
числа `K` в ней нет. После закрытия раздела она стоит условием каждой теоремы (`Check.v`, раздел 1, команды
`Check`), например:

```coq
bessel_general : forall (e : nat -> nat -> Q) (N : nat),
  (forall i j, seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0)) ->
  forall (f : nat -> Q) (K : nat),
  q_sum (fun k => seq_inner (e k) f N * seq_inner (e k) f N) K <= seq_inner f f N.
```

Посылка невыполнима ни при каком `N` — `src/process/ProcessL2Orthonormal.v:134`:

```coq
Theorem on_all_indices_unsat : forall (e : nat -> nat -> Q) (N : nat),
  ~ (forall i j, seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0)).
```

`Print Assumptions on_all_indices_unsat`: Closed under the global context. Стандартный базис ей не
удовлетворяет: $\langle e_N,e_N\rangle_N=0$ (`std_basis_fails_all_indices`, `:166`).

Места главы и теоремы:

| Место главы | Теорема страницы (под `Hon` для всех номеров) | То же с выполнимой посылкой |
|---|---|---|
| стр. 153–155, сн. 6 | `proj_ortho` (`ProcessL2BesselGeneral.v:123`) | `proj_ortho_b` (`ProcessL2Orthonormal.v:193`) |
| сн. 6 | `coef_e_resid` (`:139`) | в `src` нет; пробный файл — `coef_e_resid_b` |
| стр. 155–157 | имя не названо; это `resid_ortho` (`ProcessBestApproximation.v:87`) | в `src` нет; пробный файл — `resid_ortho_b` |
| стр. 161–170, сн. 7 | `resid_norm` (`:150`) | `resid_norm_b` (`:231`), общий вид — `gen_resid` (`:208`) |
| стр. 179–182, сн. 8 | `best_approx_eq` (`ProcessBestApproximation.v:141`) | в `src` нет; пробный файл — `best_approx_eq_b` |
| стр. 184–185, сн. 8 | `best_approx_ge` (`:161`) | `best_approx_b` (`:256`) |
| стр. 185–186, сн. 8 | `best_approx_unique` (`:176`) | в `src` нет; пробный файл — `best_approx_unique_b` |
| стр. 195–206, сн. 9 | `bessel_general` (`:175`) | `bessel_b` (`:243`) |
| стр. 216–227, сн. 10 | `energy_split` (`ProcessL2Parseval.v:91`) | `energy_split_b` (`:276`) |
| стр. 231–233 | имя не названо; это `parseval_iff_resid_zero` (`:98`) | `parseval_iff_resid_zero_b` (`:286`) |
| стр. 238–245, 266, сн. 11 | `parseval_iff_complete` (`:142`) | `parseval_iff_complete_b` (`:296`) |

Посылка правого столбца — раздел `ONB`, `ProcessL2Orthonormal.v:184–190`; гипотеза носит то же имя `Hon`:

```coq
Variable e : nat -> nat -> Q.
Variable N K0 : nat.
Hypothesis Hon : forall i j, (i < K0)%nat -> (j < K0)%nat ->
  seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0).
```

Она выполнима: `std_basis_on` (`:323`), `rot_orthonormal` (`:361`). Все теоремы правого столбца — Closed under
the global context.

Посылкой не затронуты и содержательны: `seq_inner` (определение), `seq_inner_sym`, `seq_inner_sub_r`,
`seq_inner_resid`, `inner_proj_swap` (`ProcessL2BesselGeneral.v:43, :58, :69, :81`), `q_sum_sq_zero`
(`ProcessL2Parseval.v:52`), `q_sum_swap`, `q_sum_scale` (`ProcessFubiniGeneral.v:78, :63`).

Слова стр. 155–157 («Следствие: для всех уже снятых направлений $j<K$ …») соответствуют лемме `resid_ortho`,
которой страница не называет; сноска 6 называет `coef_e_resid` — утверждение о следующем, $K$-м направлении.

**В чём расхождение.** Глава говорит о конечной системе из $K$ векторов, а названные ею теоремы доказаны под
условием ортонормированности при всех номерах, которому не удовлетворяет ни одна система: примеров у этих
теорем нет. Сами доказательства пользуются ортонормированностью только первых $K$ векторов, так что дело в
записи посылки, а не в рассуждении.

**(а) Довести формализацию до слов главы.** Большая часть уже сделана на шаге 5 Части VI
(`ProcessL2Orthonormal.v`, правый столбец таблицы). Недостаёт четырёх утверждений этой главы: «проекция не
трогает ещё не снятую координату», ортогональность остатка снятым направлениям, тождество наилучшего
приближения и единственность минимума. Все четыре доводятся без аксиом; набросок проверен (`Check.v`,
раздел 3; Closed under the global context). Положить их можно в новый файл Части VII (например,
`src/process/ProcessFourierCoefficients.v`), существующие файлы не трогаются:

```coq
Section ONB2.
Variable e : nat -> nat -> Q.
Variable N K0 : nat.
Hypothesis Hon : forall i j, (i < K0)%nat -> (j < K0)%nat ->
  seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0).
Variable f : nat -> Q.

(* <e_j, Sum_{k<K} coef_k e_k> = coef_j при j < K <= K0 *)
Lemma proj_coord_b : forall (coef : nat -> Q) (j K : nat),
  (j < K)%nat -> (K <= K0)%nat ->
  seq_inner (e j) (fun m => q_sum (fun k => coef k * e k m) K) N == coef j.
Proof.
  intros coef j K Hj HK.
  rewrite (inner_proj_swap e coef (e j) K N).
  transitivity (q_sum (fun k => (if (j =? k)%nat then 1 else 0) * coef k) K).
  { apply q_sum_ext_bounded. intros k Hk.
    rewrite (Hon j k ltac:(lia) ltac:(lia)). ring. }
  rewrite (q_sum_delta 1 coef j K Hj). ring.
Qed.

(* остаток ортогонален каждому уже снятому направлению (стр. 155–157) *)
Theorem resid_ortho_b : forall (j K : nat), (j < K)%nat -> (K <= K0)%nat ->
  seq_inner (e j) (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K) N == 0.
Proof.
  intros j K Hj HK.
  rewrite (seq_inner_sub_r (e j) f
             (fun m => q_sum (fun k => seq_inner (e k) f N * e k m) K) N).
  rewrite (proj_coord_b (fun k => seq_inner (e k) f N) j K Hj HK). ring.
Qed.

(* проекция не трогает ещё не снятую координату (сноска 6) *)
Lemma coef_e_resid_b : forall K, (K < K0)%nat ->
  seq_inner (e K) (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K) N
  == seq_inner (e K) f N.
Proof.
  intros K HK.
  rewrite (seq_inner_sub_r (e K) f
             (fun m => q_sum (fun k => seq_inner (e k) f N * e k m) K) N).
  rewrite (proj_ortho_b e N K0 Hon (fun k => seq_inner (e k) f N) K HK). ring.
Qed.

(* тождество наилучшего приближения (стр. 179–182) *)
Theorem best_approx_eq_b : forall (a : nat -> Q) (K : nat), (K <= K0)%nat ->
  seq_inner (fun m => f m - q_sum (fun k => a k * e k m) K)
            (fun m => f m - q_sum (fun k => a k * e k m) K) N
  == seq_inner (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K)
               (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K) N
     + q_sum (fun k => (a k - seq_inner (e k) f N) * (a k - seq_inner (e k) f N)) K.
Proof.
  intros a K HK.
  pose proof (gen_resid e N K0 Hon f a K HK) as Ha.
  pose proof (gen_resid e N K0 Hon f (fun k => seq_inner (e k) f N) K HK) as Hc.
  cbv beta in Hc.
  rewrite Ha, Hc.
  rewrite <- Qplus_assoc. apply Qplus_comp; [ reflexivity | ].
  rewrite <- q_sum_plus. apply q_sum_ext. intro k. ring.
Qed.

(* единственность минимума (стр. 184–186) *)
Theorem best_approx_unique_b : forall (a : nat -> Q) (K : nat), (K <= K0)%nat ->
  (seq_inner (fun m => f m - q_sum (fun k => a k * e k m) K)
             (fun m => f m - q_sum (fun k => a k * e k m) K) N
   == seq_inner (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K)
                (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K) N)
  <-> (forall k, (k < K)%nat -> a k == seq_inner (e k) f N).
Proof.
  intros a K HK. pose proof (best_approx_eq_b a K HK) as Hba. split.
  - intro Heq.
    assert (Hz :
      q_sum (fun k => (a k - seq_inner (e k) f N) * (a k - seq_inner (e k) f N)) K == 0)
      by lra.
    intros k Hk.
    pose proof (q_sum_sq_zero (fun k => a k - seq_inner (e k) f N) K Hz k Hk) as Hk0.
    cbn beta in Hk0. lra.
  - intro Hall.
    assert (Hz :
      q_sum (fun k => (a k - seq_inner (e k) f N) * (a k - seq_inner (e k) f N)) K == 0).
    { apply q_sum_zero_bounded. intros k Hk. rewrite (Hall k Hk). ring. }
    lra.
Qed.
End ONB2.
```

К словам «любым числом $K$ направлений» (стр. 202) в тот же файл стоит положить оценку числа векторов
(`Check.v`, раздел 4b; Closed under the global context):

```coq
Theorem on_count_le_dim : forall (e : nat -> nat -> Q) (N K0 : nat),
  (forall i j, (i < K0)%nat -> (j < K0)%nat ->
     seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0)) ->
  (K0 <= N)%nat.
```

Второй путь — заменить посылку `Hon` на ограниченную прямо в файлах, где она стоит
(`ProcessL2BesselGeneral.v:119`, `ProcessL2Parseval.v:80`, `ProcessBestApproximation.v:70`,
`ProcessFourierSeriesL2.v:47`, и условие теоремы в `ProcessL2HilbertSynthesis.v:101`), сохранив имена теорем;
тогда слова и сноски страницы остаются как есть, кроме текста посылки в сноске 4. Этот путь не собирался; на
шаге 5 Части VI выбран путь с новым файлом.

**(б) Поправить слова.** После (а) основной текст меняется в двух местах, остальное — сноски.

Стр. 106–108:

> В коде это *гипотеза* `Hon` раздела об ортонормированных системах — явно предъявленное условие на первые
> $K_0$ векторов конкретного набора $e$, а не существование «какого-то базиса».[^4]

Стр. 202–203:

> Энергия, захваченная любым числом $K$ направлений системы, не превосходит полной энергии функции.[^9]

Сноска 1:

> Опорные файлы — `ProcessL2Orthonormal.v` (каталог `src/process/` Rocq-репозитория ToS, 36 доказанных
> утверждений, 0 `Admitted`, 0 аксиом), `ProcessL2BesselGeneral.v` (10 утверждений, 0 аксиом),
> `ProcessL2Parseval.v` (7 утверждений, 0 аксиом) и `ProcessFourierCoefficients.v`. Имена лемм в сносках ниже —
> из них, из `ProcessFubiniGeneral.v` (перестановка сумм) и из `ProcessFourierON.v`.

Сноска 4:

> `Hypothesis Hon : forall i j, (i < K0)%nat -> (j < K0)%nat -> seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0)`
> — раздел `ONB` файла `ProcessL2Orthonormal.v`: ортонормированы первые $K_0$ векторов, и всюду ниже
> $K\le K_0$. Требовать того же при всех номерах $i,j$ нельзя: на $N$ координатах не бывает больше $N$
> ортонормированных векторов (`on_all_indices_unsat`, `on_count_le_dim`). Конкретные системы, удовлетворяющие
> `Hon`, — стандартный базис (`std_basis_on`) и повёрнутый рациональный базис (`rot_orthonormal`); о системе
> Уолша — § «Конкретная ортогональная система: Уолш–Адамар».

Сноска 6:

> `proj_ortho_b`: $\inner{e_K}{\sum_{k<K} c_k e_k}_N = 0$ при $K<K_0$. Отсюда `coef_e_resid_b`:
> $\inner{e_K}{f-P_K}_N = \inner{e_K}{f}_N$ — проекция не трогает ещё не снятую координату; для уже снятых
> направлений — `resid_ortho_b`: $\inner{e_j}{f-P_K}_N=0$ при $j<K\le K_0$. Первая — в
> `ProcessL2Orthonormal.v`, две другие — в `ProcessFourierCoefficients.v`; 0 аксиом.

Сноска 7:

> `resid_norm_b` в `ProcessL2Orthonormal.v` — частный случай тождества `gen_resid` для произвольных
> коэффициентов; оно доказывается индукцией по $K$ через тождество
> $\norm{F-cE}^2 = \norm{F}^2 - 2c\inner{E}{F} + c^2\norm{E}^2$ (`seq_inner_resid`) и ортогональность
> `proj_ortho_b`. 0 аксиом.

Сноска 8:

> Тождество наилучшего приближения — `best_approx_eq_b`; следствие-минимум
> $\norm{f-P_K}^2\le\norm{f-\sum a_k e_k}^2$ — `best_approx_b`; единственность (равенство $\Leftrightarrow$
> $a_k=c_k$) — `best_approx_unique_b` (через лемму «конечная сумма квадратов над ℚ равна нулю лишь когда каждое
> слагаемое нуль», `q_sum_sq_zero` в `ProcessL2Parseval.v`). `best_approx_b` — в `ProcessL2Orthonormal.v`, две
> другие — в `ProcessFourierCoefficients.v`; 0 аксиом. Единственность здесь — *конечная*, на фиксированном
> диапазоне $k<K$; сходимость бесконечного ряда — предмет Главы 7.4.

Сноска 9:

> `bessel_b` в `ProcessL2Orthonormal.v`: из `resid_norm_b` и неотрицательности нормы остатка одним шагом `lra`.
> 0 аксиом. Это общее неравенство Бесселя для произвольной конечной ортонормированной системы ($K\le K_0$
> векторов на $N$ координатах) — не привязанное к конкретному базису.

Сноска 10:

> `energy_split_b` в `ProcessL2Orthonormal.v`: прямое следствие `resid_norm_b` (один шаг `ring`). 0 аксиом.

Сноска 11:

> `parseval_iff_complete_b` в `ProcessL2Orthonormal.v`; опирается на `q_sum_sq_zero` («сумма квадратов нуль
> $\Rightarrow$ каждый член нуль» над ℚ, файл `ProcessL2Parseval.v`) и `resid_norm_b`. 0 аксиом.

Если формализацию не дополнять, имена `_b` из `ProcessL2Orthonormal.v` ставятся так же, а о трёх утверждениях
приходится сказать осторожнее: в сноске 6 — «`coef_e_resid` и ортогональность остатка снятым направлениям
записаны в прежних файлах под условием ортонормированности при всех номерах и ждут доводки посылки»; на
стр. 184–186 и в сноске 8 — доказан минимум (`best_approx_b`), а тождество и единственность
(`best_approx_eq`, `best_approx_unique`) записаны под тем же условием.

## Расхождение 2. Свидетель $f=(3,4)$ — вычисление, а не пример критерия (стр. 254–258; сноска 12)

**Было:**

> (254–258) Чтобы критерий не остался пустым, предъявлен явный свидетель достижения равенства: стандартный
> базис на $N=2$ координатах и функция $f=(3,4)$ дают $\sum_{k<2} c_k^2 = 3^2 + 4^2 = 25 = \norm{f}^2$ —
> полнота на двух координатах.
>
> (сноска 12) `parseval_std_concrete` в `ProcessL2Parseval.v`: проверяется `vm_compute`'ом — точной
> рациональной арифметикой.

**Проверка.** `src/process/ProcessL2Parseval.v:156`:

```coq
Example parseval_std_concrete :
  let e := fun i m => if Nat.eqb i m then 1 else 0 in
  let f := fun n => if Nat.eqb n 0 then 3 else 4 in
  q_sum (fun k => seq_inner (e k) f 2 * seq_inner (e k) f 2) 2 == seq_inner f f 2.
Proof. vm_compute. reflexivity. Qed.
```

Closed under the global context. Это равенство $25=25$, полученное вычислением. К критерию
`parseval_iff_complete` пример не применён и применён быть не может: стандартный базис посылке `Hon` не
удовлетворяет (`std_basis_fails_all_indices`). Восстановление $f$ («полнота на двух координатах») в примере не
записано.

**В чём расхождение.** Равенство на примере проверено, но критерий, о котором говорит страница, после этого
примера остаётся без единого случая применения.

**(а) Довести формализацию.** Для критерия с выполнимой посылкой свидетели уже есть:
`parseval_std_all` (`ProcessL2Orthonormal.v:337`) — равенство на стандартном базисе при всяком $N$ и всякой
$f$, выведенное из `parseval_iff_complete_b`; `parseval_rot` (`:377`). Пример страницы как следствие критерия,
вместе с восстановлением $f$, проверен (`Check.v`, раздел 4; Closed under the global context):

```coq
Example parseval_3_4_from_criterion :
  let f := fun n => if Nat.eqb n 0 then 3 else 4 in
  q_sum (fun k => seq_inner (delta k) f 2%nat * seq_inner (delta k) f 2%nat) 2%nat
  == seq_inner f f 2%nat
  /\ (forall m, (m < 2)%nat ->
        q_sum (fun k => seq_inner (delta k) f 2%nat * delta k m) 2%nat == f m).
Proof.
  intro f.
  pose proof (parseval_std_all f 2%nat) as HP. split; [ exact HP | ].
  exact (proj1 (parseval_iff_complete_b delta 2%nat 2%nat (std_basis_on 2%nat) f 2%nat
                  (le_n 2%nat)) HP).
Qed.
```

**(б) Поправить слова.** Основной текст остаётся; меняется сноска 12:

> `parseval_std_all` в `ProcessL2Orthonormal.v`: на стандартном базисе (посылка `Hon` для него —
> `std_basis_on`) равенство достигается при всяком $N$ и всякой $f$ — как следствие критерия
> `parseval_iff_complete_b`; числовой случай $f=(3,4)$ — `parseval_std_concrete` в `ProcessL2Parseval.v`,
> проверяется `vm_compute`'ом — точной рациональной арифметикой. (Это пифагорова тройка $3,4,5$ … —
> `PythagoreanTriples.v`.)

## Расхождение 3. Нормированная система Уолша «в смысле `Hon`» и «абстрактный параметр $s$» (стр. 43–46, 288–293; сноска 4)

**Было:**

> (43–46) Чего глава *не* делает: она … не вводит нормировку $1/\sqrt N$ иначе как абстрактным параметром (она
> иррациональна, если $N$ — не точный квадрат).
>
> (288–293) Чтобы получить из них ортонормированную систему в смысле `Hon` ($\inner{e_i}{e_j}=\delta_{ij}$),
> нужно нормировать: $e_k = H_k/\sqrt N$. И вот здесь — единственная иррациональность: множитель $1/\sqrt N$
> рационален лишь когда $N$ — точный квадрат (например $N=4$, $\sqrt N=2$), а в общем случае вводится
> *абстрактным параметром* $s$ с условием $s^2=N$, в полном согласии с приёмом Части VI (корень
> параметризуется, а в наблюдаемых величинах сокращается).
>
> (сноска 4) … Конкретная система, удовлетворяющая `Hon` (нормированный Уолш), — в § «Конкретная ортогональная
> система: Уолш–Адамар».

**Проверка.**

1. Посылке `Hon`, как она записана, не удовлетворяет никакая система (расхождение 1), в том числе
   нормированная система Уолша при любом множителе (`Check.v`, `normalized_walsh_not_Hon`). При $N=4$, $s=2$
   строка с номером 4 повторяет строку 2: `normalized_walsh4_fails_Hon` —
   `seq_inner (fun m => had 2 2 m / 2) (fun m => had 2 4 m / 2) 4 == 1`.
2. В опорных файлах главы нормированной системы нет ни в каком виде. Шапка `ProcessFourierON.v` (строки 15–18)
   относит нормировку к границе.
3. Параметр есть в одном файле — `ProcessHadamardGate.v:64–69` (файл Главы 7.2), только для $N=2$:

   ```coq
   Section Gate.
   Variable s2inv : Q.
   Hypothesis Hs2 : s2inv * s2inv * 2 == 1.
   ```

   Параметр имеет тип `Q`, а рационального числа с таким свойством нет (`Check.v`, `hgate_premise_unsat`,
   через `Sqrt2Irrational.no_rational_sqrt2`): теоремы раздела `Gate` стоят под невыполнимой посылкой.
4. Рациональное $s$ с $s^2=2^k$ существует в точности при чётном $k$ (`Check.v`, раздел 5; Closed under the
   global context):

   ```coq
   Theorem walsh_odd_no_rational_norm : forall (j : nat) (s : Q),
     ~ (s * s == inject_Z (Z.of_nat (pow2 (S (2 * j))))).
   Lemma walsh_even_norm_exists : forall j,
     inject_Z (Z.of_nat (pow2 j)) * inject_Z (Z.of_nat (pow2 j))
     == inject_Z (Z.of_nat (pow2 (2 * j))).
   ```

5. «Приём Части VI» в прежнем виде стоял под такой же невыполнимой посылкой (`ladder_premise_unsatisfiable`,
   `ProcessLadderRational.v:69`); после шага исправления место корня там занимают два рациональных веса с
   произведением $n$.

**В чём расхождение.** Системы, удовлетворяющей `Hon`, в формализации нет и быть не может; нормированная
система Уолша нигде не построена; параметр $s$ рационального типа с условием $s^2=N$ при нечётном $k$ не имеет
ни одного значения, так что теоремы «с параметром» были бы верны впустую.

**(а) Довести формализацию до слов главы.** Возможно, без аксиом, двумя дополнениями (в тот же новый файл).
Оба проверены: `Check.v`, разделы 5 и 6; все утверждения — Closed under the global context.

Первое — нормированная система Уолша там, где множитель рационален. Строки $H_i/s$ при $s^2=N$ ортонормированы
в смысле посылки раздела `ONB` ($K_0=N$), и к ним применимы теоремы `_b`:

```coq
Definition walsh_n (k : nat) (s : Q) : nat -> nat -> Q := fun i m => had k i m / s.

Theorem walsh_normalized_on : forall (k : nat) (s : Q),
  s * s == inject_Z (Z.of_nat (pow2 k)) ->
  forall i j, (i < pow2 k)%nat -> (j < pow2 k)%nat ->
  seq_inner (walsh_n k s i) (walsh_n k s j) (pow2 k) == (if Nat.eqb i j then 1 else 0).
Proof.
  intros k s Hs i j Hi Hj.
  pose proof (pow2_Q_pos k) as HN.
  assert (Hs0 : ~ s == 0).
  { intro H0. rewrite H0 in Hs. lra. }
  unfold seq_inner, walsh_n.
  transitivity (q_sum (fun m => / (s * s) * (had k i m * had k j m)) (pow2 k)).
  { apply q_sum_ext. intro m. field. exact Hs0. }
  rewrite q_sum_scale. rewrite (hadamard_orthogonal k i j Hi Hj).
  destruct (Nat.eqb i j).
  - rewrite Hs. field. lra.
  - ring.
Qed.

(* посылка выполнима: N = 4^j, s = 2^j *)
Theorem walsh_4j_orthonormal : forall j i i',
  (i < pow2 (2 * j))%nat -> (i' < pow2 (2 * j))%nat ->
  seq_inner (walsh_n (2 * j) (inject_Z (Z.of_nat (pow2 j))) i)
            (walsh_n (2 * j) (inject_Z (Z.of_nat (pow2 j))) i') (pow2 (2 * j))
  == (if Nat.eqb i i' then 1 else 0).

(* Бессель, Парсеваль и полнота для нормированной системы *)
Corollary walsh_normalized_bessel : forall (k : nat) (s : Q),
  s * s == inject_Z (Z.of_nat (pow2 k)) ->
  forall (f : nat -> Q) (K : nat), (K <= pow2 k)%nat ->
  q_sum (fun i => seq_inner (walsh_n k s i) f (pow2 k)
                  * seq_inner (walsh_n k s i) f (pow2 k)) K
  <= seq_inner f f (pow2 k).
Theorem walsh_normalized_parseval : forall (k : nat) (s : Q),
  s * s == inject_Z (Z.of_nat (pow2 k)) ->
  forall f : nat -> Q,
  q_sum (fun i => seq_inner (walsh_n k s i) f (pow2 k)
                  * seq_inner (walsh_n k s i) f (pow2 k)) (pow2 k)
  == seq_inner f f (pow2 k).
Corollary walsh_normalized_complete : forall (k : nat) (s : Q),
  s * s == inject_Z (Z.of_nat (pow2 k)) ->
  forall (f : nat -> Q) (m : nat), (m < pow2 k)%nat ->
  q_sum (fun i => seq_inner (walsh_n k s i) f (pow2 k) * walsh_n k s i m) (pow2 k) == f m.
```

Второе — та же теория для *ортогональной* системы, без корня и без параметра: первые $K_0$ векторов попарно
ортогональны с квадратами норм $d_k>0$, коэффициент разложения — $\inner{e_k}{f}/d_k$. Это и есть «корень в
наблюдаемых величинах сокращается», записанное теоремами; случай $d_k=1$ — раздел `ONB`.

```coq
Section OG.
Variable e : nat -> nat -> Q.
Variable N K0 : nat.
Variable d : nat -> Q.
Hypothesis Hd : forall k, (k < K0)%nat -> 0 < d k.
Hypothesis Hog : forall i j, (i < K0)%nat -> (j < K0)%nat ->
  seq_inner (e i) (e j) N == (if Nat.eqb i j then d i else 0).
Variable f : nat -> Q.

Definition cf (k : nat) : Q := seq_inner (e k) f N / d k.

Lemma gen_resid_og : forall (a : nat -> Q) (K : nat), (K <= K0)%nat ->
  seq_inner (fun m => f m - q_sum (fun k => a k * e k m) K)
            (fun m => f m - q_sum (fun k => a k * e k m) K) N
  == seq_inner f f N
     + q_sum (fun k => d k * (a k * a k) - 2 * a k * seq_inner (e k) f N) K.

Lemma resid_norm_og : forall K, (K <= K0)%nat ->
  seq_inner (fun m => f m - q_sum (fun k => cf k * e k m) K)
            (fun m => f m - q_sum (fun k => cf k * e k m) K) N
  == seq_inner f f N
     - q_sum (fun k => seq_inner (e k) f N * seq_inner (e k) f N / d k) K.

Theorem bessel_og : forall K, (K <= K0)%nat ->
  q_sum (fun k => seq_inner (e k) f N * seq_inner (e k) f N / d k) K <= seq_inner f f N.

Theorem best_approx_eq_og : forall (a : nat -> Q) (K : nat), (K <= K0)%nat ->
  seq_inner (fun m => f m - q_sum (fun k => a k * e k m) K)
            (fun m => f m - q_sum (fun k => a k * e k m) K) N
  == seq_inner (fun m => f m - q_sum (fun k => cf k * e k m) K)
               (fun m => f m - q_sum (fun k => cf k * e k m) K) N
     + q_sum (fun k => d k * ((a k - cf k) * (a k - cf k))) K.

Theorem parseval_iff_complete_og : forall K, (K <= K0)%nat ->
  (q_sum (fun k => seq_inner (e k) f N * seq_inner (e k) f N / d k) K == seq_inner f f N)
  <-> (forall m, (m < N)%nat -> q_sum (fun k => cf k * e k m) K == f m).
End OG.
```

Система Уолша удовлетворяет посылке при **всяком** $N=2^k$ ($d=N$, $K_0=N$; `walsh_og` — из
`hadamard_orthogonal`), и следствия не содержат ни корня, ни параметра:

```coq
Theorem walsh_bessel : forall (k : nat) (f : nat -> Q) (K : nat), (K <= pow2 k)%nat ->
  q_sum (fun i => seq_inner (had k i) f (pow2 k) * seq_inner (had k i) f (pow2 k)
                  / inject_Z (Z.of_nat (pow2 k))) K
  <= seq_inner f f (pow2 k).

Theorem walsh_parseval_divided : forall (k : nat) (f : nat -> Q),
  q_sum (fun i => seq_inner (had k i) f (pow2 k) * seq_inner (had k i) f (pow2 k)
                  / inject_Z (Z.of_nat (pow2 k))) (pow2 k)
  == seq_inner f f (pow2 k).

Theorem walsh_complete : forall (k : nat) (f : nat -> Q) (m : nat), (m < pow2 k)%nat ->
  q_sum (fun i => seq_inner (had k i) f (pow2 k) / inject_Z (Z.of_nat (pow2 k)) * had k i m)
        (pow2 k) == f m.
```

и `walsh_best_approx` (частичная сумма с коэффициентами $\inner{H_i}{f}/N$ — наилучшее приближение среди
комбинаций первых $K$ строк). `walsh_parseval_divided` — это слова стр. 303–304 («делит обе части на $N$»),
записанные теоремой; `walsh_complete` получена из критерия `parseval_iff_complete_og`.

Довести буквально слова «абстрактный параметр $s$ с условием $s^2=N$ в общем случае» нельзя: при нечётном $k$
такого рационального $s$ нет (`walsh_odd_no_rational_norm`), а иррациональный корень в формализации есть процесс,
а не число типа `Q`.

**(б) Поправить слова.**

Стр. 43–46:

> Чего глава *не* делает: она не строит завершённый *бесконечный* ортонормированный базис, не утверждает, что
> замкнутая оболочка системы есть всё пространство, и не вводит нормировку $1/\sqrt N$ там, где она
> иррациональна (то есть если $N$ — не точный квадрат): там разложение ведётся по ортогональной системе с
> коэффициентами $\inner{H_k}{f}/N$.

Стр. 288–293 (после дополнений (а)):

> Чтобы получить из них ортонормированную систему в смысле `Hon` ($\inner{e_i}{e_j}=\delta_{ij}$ при $i,j<N$),
> нужно нормировать: $e_k = H_k/\sqrt N$. И вот здесь — единственная иррациональность: множитель $1/\sqrt N$
> рационален лишь когда $N$ — точный квадрат (например $N=4$, $\sqrt N=2$; для $N=2^k$ — при чётном $k$), и
> тогда нормированная система Уолша есть рациональная ортонормированная система (`walsh_normalized_on`,
> `walsh_4j_orthonormal`). В общем случае корень не вводится: его место занимают ненормированный вектор $H_k$
> и коэффициент $\inner{H_k}{f}/N$, в полном согласии с приёмом Части VI (место корня занимают два
> рациональных множителя, и в наблюдаемых величинах корня нет) — неравенство Бесселя, наилучшее приближение и
> критерий полноты доказаны для ортогональной системы без нормировки (`bessel_og`, `best_approx_eq_og`,
> `parseval_iff_complete_og`; для Уолша при всяком $N=2^k$ — `walsh_bessel`, `walsh_complete`).

Сноска 4, последнее предложение — см. текст в расхождении 1.

Если формализацию не дополнять:

> (288–293) Чтобы получить из них ортонормированную систему ($\inner{e_i}{e_j}=\delta_{ij}$ при $i,j<N$), нужно
> нормировать: $e_k = H_k/\sqrt N$. И вот здесь — единственная иррациональность: множитель $1/\sqrt N$
> рационален лишь когда $N$ — точный квадрат (например $N=4$, $\sqrt N=2$); в общем случае рационального
> множителя нет, и нормированная система в формализации не строится — корень остаётся роль-пределом, а
> доказанное относится к ненормированной системе.
>
> (сноска 4, конец) Конкретные системы, удовлетворяющие `Hon`, — стандартный базис (`std_basis_on`) и
> повёрнутый рациональный базис (`rot_orthonormal`); система Уолша ортогональна, но не нормирована — § «Конкретная
> ортогональная система: Уолш–Адамар».

## Расхождение 4. «Конкретную рациональную ортонормированную систему» в анонсе следующей главы (стр. 386–390)

**Было:**

> Следующая глава предъявляет конкретную рациональную ортонормированную систему во всей полноте —
> преобразование Уолша–Адамара. Там абстрактная гипотеза `Hon` сменяется доказанным тождеством
> $H_N^{\mathsf T}H_N = N\cdot I$ …

**Проверка.** `hadamard_orthogonal` (`ProcessWalshHadamard.v:152`): сумма произведений двух строк равна $2^k$
при совпадении номеров и $0$ иначе; `walsh_norm` (`:78`): квадрат нормы каждой строки равен $2^k$. Система
ортогональна; ортонормированной она не является при $N>1$. Глава сама говорит это выше (стр. 275–278:
«Рациональная *ортогональная* система — да … Но буквальная *ортонормированность* … — следующий слой»).

**В чём расхождение.** Слово «ортонормированную» сильнее доказанного тождества $H^{\mathsf T}H=N\cdot I$ и
расходится с оговоркой самой главы.

**(а) Довести формализацию.** Для системы Уолша как она есть — нельзя: квадрат нормы строки равен $N$
(`walsh_norm`). Рациональная ортонормированная система получается при $N=4^j$ (`walsh_4j_orthonormal`,
расхождение 3).

**(б) Поправить слова.**

> Следующая глава предъявляет конкретную рациональную ортогональную систему во всей полноте — преобразование
> Уолша–Адамара. Там абстрактная гипотеза `Hon` сменяется доказанным тождеством
> $H_N^{\mathsf T}H_N = N\cdot I$, а сохранение энергии — дискретным равенством Планшереля
> $\norm{Hf}^2 = N\norm{f}^2$: Фурье, построенный без единой трансцендентности.

## Сомнительные места, расхождением не являющиеся

- **«Линейно по каждому аргументу … одним шагом `ring`» (стр. 94–96).** В названном файле линейность записана
  одной леммой — `seq_inner_sub_r` (разность во втором аргументе); в её доказательстве кроме `ring`
  использована `q_sum_minus`. Сноска 3 называет именно эту лемму, поэтому расхождением не записано. Вынесение
  множителя — `seq_inner_scale_r` (`ProcessL2Orthonormal.v:110`). Билинейность в полном виде выведена
  (`Check.v`, раздел 2, `seq_inner_bilinear_symmetric`: индукция по $N$ и `ring`; Closed).
- **Сноска 1, «Имена лемм в сносках ниже — из них и из `ProcessFourierON.v`».** Сноски называют ещё
  `ProcessCompactSpectral.v`, `ProcessBestApproximation.v`, `ProcessWalshHadamard.v`, `PythagoreanTriples.v`;
  без файла остаются `q_sum_swap` и `q_sum_scale` (сноска 5) — они объявлены в `ProcessFubiniGeneral.v`.
- **Сноска 8, «Все — в `ProcessBestApproximation.v`».** Слово «все» относится к трём теоремам; названная там же
  лемма `q_sum_sq_zero` объявлена в `ProcessL2Parseval.v:52`.
- **«Следствие» на стр. 155–157.** Ортогональность остатка снятым направлениям не следует из названных в
  сноске 6 лемм: она требует равенства $\inner{e_j}{P_K}=c_j$ при $j<K$ (`proj_coord`,
  `ProcessBestApproximation.v:74`). Учтено в расхождении 1.
- **«Столбцы матрицы Адамара» (стр. 280).** `hadamard_orthogonal` говорит о строках (сумма по второму индексу);
  сноска 14 приводит формулу для строк. Матрица симметрична (`had_symmetric`, `ProcessFourierON.v:44`), так что
  утверждения совпадают.
- **«В точности тогда» (стр. 234–235).** Леммой записана одна сторона (`q_sum_sq_zero`: сумма квадратов нуль
  $\Rightarrow$ каждый член нуль); обратная использована внутри `parseval_of_complete` без отдельной леммы.
  Сноски 8 и 11 называют одну сторону.
- **«Переход к нормированной системе делит обе части на $N$» (стр. 303–304).** Теоремой в `src` не записано;
  страница доказанным это не называет. Выведено: `walsh_parseval_divided` (всякое $k$, без корня) и
  `walsh_normalized_parseval` (при рациональном $s$).
- **«Любым числом $K$ направлений» (стр. 202).** Число ортонормированных векторов на $N$ координатах не больше
  $N$ (`Check.v`, `on_count_le_dim`); для $K\le K_0\le N$ слова верны.
- **«Малость примера здесь принципиальна» (стр. 257).** После шага 5 Части VI есть общий свидетель —
  `parseval_std_all` (всякое $N$, всякое $f$); числовой пример остаётся иллюстрацией.
- **Нумерация строк матрицы.** `had k i j` определена при всех натуральных `i`, `j`; при `i >= 2^k` строки
  повторяются (при $k=2$ строка 4 совпадает со строкой 2). Теоремы главы берут `i < 2^k`, на странице это не
  сказывается.
- **«Первые два уровня глава ведёт как доказанные» (стр. 56–57).** Второй уровень назван «процессными
  чтениями»; чтение теоремой не является. Статус первого уровня — расхождение 1.

## Вне главы

- Посылка `Hon` для всех номеров стоит также в `ProcessFourierSeriesL2.v:47` (Глава 7.4) и условием теоремы
  `orthonormal_expansion_synthesis` (`ProcessL2HilbertSynthesis.v:101`).
- `ProcessHadamardGate.v`, раздел `Gate` (`:64–69`, Глава 7.2): посылка `s2inv * s2inv * 2 == 1` для
  `s2inv : Q` невыполнима (`Check.v`, `hgate_premise_unsat`); теоремы `hgate_involution` и
  `hgate_superposition` стоят под ней.
- Шапки отстали или говорят сильнее доказанного: `ProcessL2BesselGeneral.v` (строки 14–16 — равенство
  Парсеваля названо «remain beyond», хотя файл `ProcessL2Parseval.v` его заявляет; строка 26 — «general Bessel
  PROVEN»); `ProcessL2Parseval.v` (строки 15–16 — «for a FINITE orthonormal system», при посылке для всех
  номеров); `ProcessBestApproximation.v` (строки 9–11 — «among ALL linear combinations … of a finite
  orthonormal system»).
- Шапка `ProcessFourierON.v` (строки 15–18) относит равенство $\sum\langle e_i,f\rangle^2=\|f\|^2$ к границе
  из-за $\sqrt N$; в разделённой на $N$ форме оно доказывается без корня при всяком $k$
  (`walsh_parseval_divided`).
- Шапка `ProcessWalshHadamard.v` (строки 14–19) сначала говорит о проверке полной ортогональности «для
  $N=2$ и $N=4$», затем — об общей теореме; в файле есть и то, и другое.
