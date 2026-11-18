# Глава VII.4 «Сходимость рядов Фурье в L²» — заметки к ведомости (15.11.2026)

Ведомость: `part07-ch04.json` — 43 ручные записи + 2 автоматические (упоминания файлов
`ProcessL2BesselGeneral.v`, `ProcessL2Parseval.v`); `merge --dry` проходит без замечаний, список «без сверки»
пуст. Вердикты ручных записей: ok — 16, mismatch-statement — 27. Расхождений цены, имён без объявления и
неверных чисел нет.

Двадцать семь записей с расхождением относятся к трём местам: двадцать четыре — к расхождению 1 (посылка
ортонормированности), три — к расхождению 2 (Рисс–Фишер); расхождение 3 (связь лемм в сносках 4 и 7) касается
двух записей из числа первых двадцати четырёх.

Глава называет пять файлов каталога `src/process/`: `ProcessFourierSeriesL2.v` (6 `Qed`),
`ProcessBestApproximation.v` (9), `ProcessL2BesselGeneral.v` (10), `ProcessL2Parseval.v` (7),
`ProcessL2RieszFischer.v` (6); определение `captured` и лемма `captured_mono` лежат в
`ProcessFourierCompression.v` (6). Все шесть прочитаны целиком, как и `ProcessL2Orthonormal.v` (36 `Qed`,
добавлен 15.11 при доводке Части VI). Строк `Axiom`, `Parameter`, `Admitted` в них нет. `Print Assumptions`
снят для всех 15 объявлений двух опорных файлов и для названных главой теорем Части VI (`PA.v`): каждое —
«Closed under the global context». Исходники в репозитории и в собранной копии совпадают (`diff`). Цена на
странице («без аксиом», «0 аксиом») названа верно всюду; числа «6 утверждений» и «9 утверждений» верны.

Пробные файлы лежат в `C:/Users/abary/tos-audit-build/_part07/ch04/`:

- `status.txt` — вывод `tom-status.cjs chapter 07/04`;
- `PA.v`, `PA.out` — утверждения после закрытия разделов (`Check`) и `Print Assumptions`; `PA2.v`, `PA2.out` —
  цена теоремы `L2_norm_cauchy` из `ProcessL2.v` (к разделу «Вне главы»);
- `Check.v`, `Check.out` — пробные доказательства, разделы 0–5 по местам главы. Собирается: 49 `Qed`; все 32
  утверждения, для которых снят `Print Assumptions`, — «Closed under the global context»;
- `checklines.cjs` — сверка номеров строк ведомости со страницей.

В `src` и в собранной копии ничего не менялось; база связей не менялась (`merge` запускался только с `--dry`).

## Что проверить не удалось

- Отсылки к другим главам (7.1, 7.3, 7.5, Часть VI) по содержанию не сверялись — это предмет их ведомостей.
  Сверены адреса: Глава 7.1 называет `bessel_general`, `parseval_iff_complete`, `best_approx_unique`; Глава 7.5
  называет `captured_mono`; Глава 7.3 — «Тригонометрия и комплексный DFT: где граница». Глава 7.1 на сегодня
  называет прежние теоремы (под посылкой для всех номеров); как она будет поправлена, здесь не учтено.
- Предложенный в расхождении 1 новый файл проверен как пробный файл поверх собранных модулей (`Check.v`); как
  файл `src` с записью в `_CoqProject` он не собирался. Второй путь — замена посылки на месте в двух
  существующих файлах — не собирался.
- Сходимость для бесконечной ортонормированной системы, отличной от стандартной (например, системы Уолша при
  растущем числе координат), не пробовалась: в разделе 4 пробного файла доказан только случай стандартной
  системы.
- Сведения о классической математике (теорема Дирихле, явление Гиббса, классическая теорема Рисса–Фишера) вне
  предмета аудита; в формализации о них ничего нет, и глава этого не утверждает.
- Английская страница и LaTeX-исходник главы не смотрелись.

Всё остальное проверено по исходнику и компилятору.

## Расхождение 1. Тождество ошибки, монотонность, наилучшее приближение и критерий нуля доказаны под посылкой, которой не удовлетворяет ни одна система (стр. 25–31, 41–42, 91–92, 103–106, 132–142, 153–158, 162–166; сноски 3–7)

**Было:**

> (25–31) Доказано над ℚ следующее (для конечной ортонормированной системы на $N$ координатах), и всё — без
> аксиом.[^1] Квадрат ошибки усечения равен полной энергии минус захваченная,
> $\norm{f-P_K}^2=\norm{f}^2-\sum_{k<K}c_k^2$; эта ошибка неотрицательна (Бессель) и *монотонно убывает* с
> ростом $K$; частичная сумма $P_K$ — наилучшее $K$-членное приближение; а ошибка обращается в нуль тогда и
> только тогда, когда выполнено равенство Парсеваля, то есть система полностью восстанавливает $f$.
>
> (41–42) *Первый* — конечная теория усечений (ошибка = хвост, монотонность, наилучшее приближение, критерий
> полноты): доказано над ℚ, 0 аксиом.
>
> (132–133) Квадрат ошибки усечения *в точности* равен отброшенной хвостовой энергии — той, что не схватили
> первые $K$ коэффициентов.[^3] Отсюда три следствия, и каждое доказано:
>
> (154–156) …среди всех $K$-членных линейных комбинаций системы $\{e_k\}$ частичная сумма Фурье $P_K$
> минимизирует L<sup>2</sup>-ошибку, и минимум этот единствен (Глава 7.1).
>
> (сноска 3) `fourier_error_eq` в `ProcessFourierSeriesL2.v`: … Прямое следствие `resid_norm` (Часть VI). 0
> аксиом.
>
> (сноска 5) `fourier_error_monotone`; опирается на монотонность захваченной энергии (`captured_mono`, Глава
> 7.5). 0 аксиом.
>
> (сноска 6) `fourier_partial_best` в `ProcessFourierSeriesL2.v` (она же `best_approx_ge` из
> `ProcessBestApproximation.v`): … для любых весов $a_k$; единственность минимума — `best_approx_unique`. 0
> аксиом.
>
> (сноска 7) `fourier_error_zero_iff`: …; опирается на критерий полноты `parseval_iff_complete` (Глава 7.1). 0
> аксиом.

Те же утверждения повторены на стр. 91–92 (Бессель), 103–106, 135–142, 156–158, 162–166 и в сноске 4.

**Проверка.** `src/process/ProcessFourierSeriesL2.v:43–48` (то же в `ProcessBestApproximation.v:66–71`,
`ProcessL2BesselGeneral.v:115–119`, `ProcessL2Parseval.v:76–81`):

```coq
Section ON.
Variable e : nat -> nat -> Q.
Variable N : nat.
Hypothesis Hon : forall i j, seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0).
Variable f : nat -> Q.
```

`seq_inner a b N` есть $\sum_{m<N}a_m b_m$ (`ProcessCompactSpectral.v:51`). Посылка требует ортонормированности
векторов `e i` при **всех** натуральных `i`, `j`, а скалярное произведение считает первые `N` координат.
После закрытия раздела (`PA.out`) её берут:

- в `ProcessFourierSeriesL2.v` — `fourier_error_eq` (`:57`), `fourier_energy_balance` (`:64`),
  `fourier_error_monotone` (`:77`), `fourier_error_zero_iff` (`:87`), `fourier_partial_best` (`:94`); не берёт
  одна `fourier_error_nonneg` (`:71`) — её утверждение `forall e N f K, 0 <= ‖f − P_K‖²` есть неотрицательность
  суммы квадратов и верно для любого семейства `e`;
- в `ProcessBestApproximation.v` — `proj_coord` (`:74`), `resid_ortho` (`:87`), `norm_comb` (`:110`),
  `gen_resid_norm` (`:123`), `best_approx_eq` (`:141`), `best_approx_ge` (`:161`), `best_approx_unique`
  (`:176`); не берут `seq_inner_expand_diff` (`:52`) и `inner_f_comb` (`:100`);
- названные главой теоремы Части VI — `resid_norm` (`ProcessL2BesselGeneral.v:150`), `bessel_general` (`:175`),
  `parseval_iff_complete` (`ProcessL2Parseval.v:142`).

Например:

```coq
fourier_error_monotone
     : forall (e : nat -> nat -> Q) (N : nat),
       (forall i j : nat, seq_inner (e i) (e j) N == (if i =? j then 1 else 0)) ->
       forall (f : nat -> Q) (K K' : nat), (K <= K')%nat ->
       seq_inner (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K')
                 (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K') N
       <= seq_inner (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K)
                    (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K) N
```

`Print Assumptions` всех перечисленных: Closed under the global context. Цена названа верно, формулы сносок
3, 5, 6, 7 совпадают с заключениями теорем.

Посылка невыполнима ни при каком `N` — это найдено при проверке Части VI и доказано в `src`
(`ProcessL2Orthonormal.v:134`, Closed under the global context):

```coq
Theorem on_all_indices_unsat : forall (e : nat -> nat -> Q) (N : nat),
  ~ (forall i j, seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0)).
```

Поэтому под этой посылкой с тем же успехом доказывается тождество ошибки с неверной правой частью (`Check.v`,
раздел 0, `fourier_error_eq_vacuous`: `ferr e f N K == seq_inner f f N + captured … K + 1`). Сама посылка при
этом нужна: без ортонормированности монотонность неверна (`Check.v`, `monotone_fails_without_on`: одна
координата, $e_0=(2)$, $f=(1)$; ошибка при $K=0$ равна $1$, при $K=1$ равна $9$).

В `ProcessL2Orthonormal.v` (раздел `ONB`, `:184`) часть утверждений главы уже доказана с выполнимой посылкой —
ортонормированы первые `K0` векторов, `K <= K0`:

| слова главы | прежняя теорема | с выполнимой посылкой в `src` |
|---|---|---|
| ошибка $=\|f\|^2-\sum_{k<K}c_k^2$ | `fourier_error_eq`, `resid_norm` | `resid_norm_b` (`:231`) |
| неравенство Бесселя | `bessel_general` | `bessel_b` (`:243`), пример `bessel_std` (`:330`) |
| наилучшее приближение | `fourier_partial_best`, `best_approx_ge` | `best_approx_b` (`:256`) |
| нуль $\Leftrightarrow$ Парсеваль | `fourier_error_zero_iff` | `parseval_iff_resid_zero_b` (`:286`) |
| Парсеваль $\Leftrightarrow$ восстановление $f$ | `parseval_iff_complete` | `parseval_iff_complete_b` (`:296`) |
| монотонность ошибки | `fourier_error_monotone` | не записана |
| единственность минимума | `best_approx_unique` | не записана |

Примеры, удовлетворяющие новой посылке: `std_basis_on` (`:323`), `rot_orthonormal` (`:361`),
`parseval_std_all` (`:337`).

**В чём расхождение.** Слова «доказано над ℚ» относятся к теоремам, посылке которых не удовлетворяет ни одна
система векторов: в названных главой файлах тождество ошибки, монотонность, наилучшее приближение с
единственностью и критерий нуля не имеют ни одного примера. Доказательства пользуются ортонормированностью
только первых $K$ векторов, так что дело в записи посылки, а не в рассуждении.

**(а) Довести формализацию до слов главы.** Возможно, без аксиом. Четыре утверждения из шести закрываются
теоремами `ProcessL2Orthonormal.v` (таблица выше). Недостающее — монотонность, единственность минимума,
критерий «ошибка нулевая $\Leftrightarrow$ восстановление» одним утверждением — предлагается дописать новым
файлом, например `src/process/ProcessFourierTruncation.v` (существующие файлы не трогаются). Набросок проверен:
`Check.v`, раздел 1, все утверждения — Closed under the global context.

```coq
(** Квадрат ошибки K-членной частичной суммы на N координатах. *)
Definition ferr (e : nat -> nat -> Q) (f : nat -> Q) (N K : nat) : Q :=
  seq_inner (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K)
            (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K) N.

Lemma q_sum_sq_diff : forall (a c : nat -> Q) (K : nat),
  q_sum (fun k => a k * a k - 2 * a k * c k) K
  == q_sum (fun k => c k * c k - 2 * c k * c k) K
     + q_sum (fun k => (a k - c k) * (a k - c k)) K.
Proof.
  intros a c K. induction K as [|K IH]; cbn [q_sum]; [ ring | rewrite IH; ring ].
Qed.

Section FourierB.
Variable e : nat -> nat -> Q.
Variable N K0 : nat.
Hypothesis Hon : forall i j, (i < K0)%nat -> (j < K0)%nat ->
  seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0).
Variable f : nat -> Q.
Local Notation cf := (fun k => seq_inner (e k) f N).

Lemma fourier_error_eq_b : forall K, (K <= K0)%nat ->
  ferr e f N K == seq_inner f f N - captured cf K.
Proof.
  intros K HK. unfold ferr. rewrite (resid_norm_b e N K0 Hon f K HK).
  unfold captured. reflexivity.
Qed.

(** Новый коэффициент уменьшает ошибку ровно на свой квадрат. *)
Lemma fourier_error_step_b : forall K, (S K <= K0)%nat ->
  ferr e f N (S K) == ferr e f N K - seq_inner (e K) f N * seq_inner (e K) f N.
Proof.
  intros K HK.
  pose proof (fourier_error_eq_b (S K) HK) as H1.
  pose proof (fourier_error_eq_b K ltac:(lia)) as H0.
  pose proof (captured_step cf K) as Hs. cbv beta in Hs.
  lra.
Qed.

Lemma fourier_error_monotone_b : forall K K', (K <= K')%nat -> (K' <= K0)%nat ->
  ferr e f N K' <= ferr e f N K.
Proof.
  intros K K' Hle HK'.
  pose proof (fourier_error_eq_b K' HK') as H1.
  pose proof (fourier_error_eq_b K ltac:(lia)) as H0.
  pose proof (captured_mono cf K K' Hle) as Hm.
  lra.
Qed.

Lemma fourier_error_zero_iff_b : forall K, (K <= K0)%nat ->
  ferr e f N K == 0 <-> captured cf K == seq_inner f f N.
Proof.
  intros K HK. pose proof (fourier_error_eq_b K HK) as H. split; intro Hx; lra.
Qed.

(** Ошибка нулевая <-> частичная сумма восстанавливает f на каждой координате. *)
Theorem fourier_error_zero_iff_recovers_b : forall K, (K <= K0)%nat ->
  ferr e f N K == 0
  <-> (forall m, (m < N)%nat -> q_sum (fun k => seq_inner (e k) f N * e k m) K == f m).
Proof.
  intros K HK.
  pose proof (fourier_error_zero_iff_b K HK) as H1. unfold captured in H1. cbv beta in H1.
  pose proof (parseval_iff_complete_b e N K0 Hon f K HK) as H2.
  split; intro H.
  - apply (proj1 H2). apply (proj1 H1). exact H.
  - apply (proj2 H1). apply (proj2 H2). exact H.
Qed.

Theorem fourier_partial_best_b : forall (a : nat -> Q) (K : nat), (K <= K0)%nat ->
  ferr e f N K
  <= seq_inner (fun m => f m - q_sum (fun k => a k * e k m) K)
               (fun m => f m - q_sum (fun k => a k * e k m) K) N.
Proof. intros a K HK. exact (best_approx_b e N K0 Hon f a K HK). Qed.

(** Ошибка произвольных коэффициентов больше ошибки Фурье ровно на Sum (a_k - c_k)^2. *)
Theorem best_approx_eq_b : forall (a : nat -> Q) (K : nat), (K <= K0)%nat ->
  seq_inner (fun m => f m - q_sum (fun k => a k * e k m) K)
            (fun m => f m - q_sum (fun k => a k * e k m) K) N
  == ferr e f N K
     + q_sum (fun k => (a k - seq_inner (e k) f N) * (a k - seq_inner (e k) f N)) K.
Proof.
  intros a K HK. unfold ferr.
  pose proof (gen_resid e N K0 Hon f a K HK) as Ha.
  pose proof (gen_resid e N K0 Hon f (fun k => seq_inner (e k) f N) K HK) as Hc.
  cbv beta in Hc.
  pose proof (q_sum_sq_diff a (fun k => seq_inner (e k) f N) K) as Hd. cbv beta in Hd.
  lra.
Qed.

(** Минимум достигается в точности на коэффициентах Фурье. *)
Theorem best_approx_unique_b : forall (a : nat -> Q) (K : nat), (K <= K0)%nat ->
  (seq_inner (fun m => f m - q_sum (fun k => a k * e k m) K)
             (fun m => f m - q_sum (fun k => a k * e k m) K) N
   == ferr e f N K)
  <-> (forall k, (k < K)%nat -> a k == seq_inner (e k) f N).
Proof.
  intros a K HK. pose proof (best_approx_eq_b a K HK) as Hba. split.
  - intros Heq k Hk.
    assert (Hz : q_sum (fun k => (a k - seq_inner (e k) f N)
                                 * (a k - seq_inner (e k) f N)) K == 0) by lra.
    pose proof (q_sum_sq_zero (fun k => a k - seq_inner (e k) f N) K Hz k Hk) as Hk0.
    cbv beta in Hk0. lra.
  - intro Hall.
    assert (Hz : q_sum (fun k => (a k - seq_inner (e k) f N)
                                 * (a k - seq_inner (e k) f N)) K == 0).
    { apply q_sum_zero_bounded. intros k Hk. cbv beta. rewrite (Hall k Hk). ring. }
    lra.
Qed.
End FourierB.
```

В тот же файл стоит положить ещё три утверждения (`Check.v`, разделы 2 и 3; тексты доказательств там же;
Closed under the global context):

```coq
(* На N координатах ортонормированных векторов не больше N. *)
Theorem orthonormal_count_le_dim : forall (e : nat -> nat -> Q) (N K0 : nat),
  (forall i j, (i < K0)%nat -> (j < K0)%nat ->
     seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0)) ->
  (K0 <= N)%nat.

(* Всякие N ортонормированных векторов на N координатах восстанавливают всякую f. *)
Theorem full_on_recovers :   (* посылка: ортонормированы e_0 … e_{N-1} *)
  forall (f : nat -> Q) (m : nat), (m < N)%nat ->
  q_sum (fun k => seq_inner (e k) f N * e k m) N == f m.

(* Процесс усечения полной системы: ошибка начинается с полной энергии,
   не возрастает и равна нулю при K = N. *)
Theorem fourier_truncation_ends_exactly : forall f : nat -> Q,
  ferr e f N 0 == seq_inner f f N
  /\ (forall K K', (K <= K')%nat -> (K' <= N)%nat -> ferr e f N K' <= ferr e f N K)
  /\ ferr e f N N == 0.
```

`orthonormal_count_le_dim` повторяет ход `on_all_indices_unsat` с `bessel_b` на месте `bessel_general`.
`full_on_recovers` доказывается так: из `bessel_b` для координатных векторов $\delta_m$ получается
$\sum_{k<N}e_k(m)^2\le1$; сумма по $m<N$ равна $N$ (перестановка сумм `q_sum_swap`), значит каждое неравенство
есть равенство, то есть равенство Парсеваля для $\delta_m$; по `parseval_iff_complete_b` отсюда
$\sum_{k<N}e_k(m)e_k(m')=[m=m']$, и разложение произвольной $f$ восстанавливает её покоординатно.

Второй путь — заменить посылку `Hon` на ограниченную прямо в `ProcessFourierSeriesL2.v:47` и
`ProcessBestApproximation.v:70`, добавив в утверждения условие `K <= K0` и сохранив имена теорем; тогда сноски
страницы остаются как есть. Других мест в `src`, где используются теоремы этих двух файлов, нет (поиск). Этот
путь не собирался.

**(б) Поправить слова.** Если принят путь (а) с новым файлом, основной текст остаётся: слова «для конечной
ортонормированной системы на $N$ координатах» новой посылке отвечают. Меняются сноски:

> (сноска 1) Опорные файлы — `ProcessFourierTruncation.v` и `ProcessL2Orthonormal.v`, оба в каталоге
> `src/process/` (0 аксиом), поверх L<sup>2</sup>-аппарата Части VI (`ProcessL2BesselGeneral.v`,
> `ProcessL2Parseval.v`, `ProcessL2RieszFischer.v`). Ортонормированность требуется от первых $K_0$ векторов
> системы, усечение берётся при $K\le K_0$; на $N$ координатах $K_0\le N$ (`orthonormal_count_le_dim`).
> Прежние `ProcessFourierSeriesL2.v` и `ProcessBestApproximation.v` требуют ортонормированности при всех
> номерах, чего на $N$ координатах не бывает (`on_all_indices_unsat`). Имена — в сносках ниже.
>
> (сноска 3) `fourier_error_eq_b` в `ProcessFourierTruncation.v`:
> $\norm{f-P_K}^2=\norm{f}^2-\texttt{captured}(c,K)$, где `captured`$(c,K)=\sum_{k<K}c_k^2$. Прямое следствие
> `resid_norm_b` (Часть VI). 0 аксиом.
>
> (сноска 4) `fourier_error_nonneg`; вместе с тождеством ошибки даёт `bessel_b` (Глава 7.1).
>
> (сноска 5) `fourier_error_monotone_b` (при $K\le K'\le K_0$); опирается на монотонность захваченной энергии
> (`captured_mono`, Глава 7.5). 0 аксиом.
>
> (сноска 6) `fourier_partial_best_b` в `ProcessFourierTruncation.v` (она же `best_approx_b` из
> `ProcessL2Orthonormal.v`): $\norm{f-P_K}^2\le\norm{f-\sum_{k<K}a_k e_k}^2$ для любых весов $a_k$;
> единственность минимума — `best_approx_unique_b`. 0 аксиом.
>
> (сноска 7) `fourier_error_zero_iff_b`: $\norm{f-P_K}^2=0 \Leftrightarrow \sum_{k<K}c_k^2=\norm{f}^2$;
> вместе с критерием полноты `parseval_iff_complete_b` (Глава 7.1) — `fourier_error_zero_iff_recovers_b`:
> ошибка нулевая тогда и только тогда, когда частичная сумма восстанавливает $f$ на каждой координате. 0
> аксиом.

Число утверждений нового файла для сноски 1 берётся по `grep -c 'Qed\.'` после сборки. Сноска 8 (чтение шапок)
переписывается по шапке нового файла.

Если формализация остаётся как есть на сегодня (опора — уже существующий `ProcessL2Orthonormal.v`), сужается
перечень доказанного:

> (25–31) Доказано над ℚ следующее (для конечной ортонормированной системы на $N$ координатах), и всё — без
> аксиом.[^1] Квадрат ошибки усечения равен полной энергии минус захваченная,
> $\norm{f-P_K}^2=\norm{f}^2-\sum_{k<K}c_k^2$; эта ошибка неотрицательна (Бессель); частичная сумма $P_K$ —
> наилучшее $K$-членное приближение; а ошибка обращается в нуль тогда и только тогда, когда выполнено
> равенство Парсеваля, то есть система полностью восстанавливает $f$. То, что ошибка *монотонно убывает* с
> ростом $K$, есть прямое следствие первого тождества; отдельной теоремой с выполнимой посылкой оно пока не
> записано, как и единственность наилучшего приближения.
>
> (41–42) *Первый* — конечная теория усечений (ошибка = хвост, наилучшее приближение, критерий полноты):
> доказано над ℚ, 0 аксиом; монотонность — следствие тождества ошибки.
>
> (133) …[^3] Отсюда три следствия:
>
> (сноска 1) Опорный файл — `ProcessL2Orthonormal.v` (каталог `src/process/`, 0 аксиом; Часть VI):
> ортонормированность требуется от первых $K_0$ векторов системы, усечение берётся при $K\le K_0$. Файлы
> `ProcessFourierSeriesL2.v` (6 утверждений) и `ProcessBestApproximation.v` (9 утверждений) записывают те же
> утверждения под посылкой ортонормированности при всех номерах; на $N$ координатах ей не удовлетворяет ни
> одна система (`on_all_indices_unsat`). Имена — в сносках ниже.
>
> (сноска 3) `resid_norm_b` в `ProcessL2Orthonormal.v`: $\norm{f-P_K}^2=\norm{f}^2-\sum_{k<K}c_k^2$ при
> $K\le K_0$. 0 аксиом.
>
> (сноска 4) Неотрицательность — `fourier_error_nonneg` (сумма квадратов); неравенство Бесселя — `bessel_b`
> (Глава 7.1).
>
> (сноска 5) Следует из `resid_norm_b` и монотонности захваченной энергии (`captured_mono`, Глава 7.5);
> отдельной теоремой не записано.
>
> (сноска 6) `best_approx_b` в `ProcessL2Orthonormal.v`: $\norm{f-P_K}^2\le\norm{f-\sum_{k<K}a_k e_k}^2$ для
> любых весов $a_k$ (при $K\le K_0$). 0 аксиом. Единственность минимума записана пока под прежней посылкой
> (`best_approx_unique`).
>
> (сноска 7) `parseval_iff_resid_zero_b`: $\sum_{k<K}c_k^2=\norm{f}^2 \Leftrightarrow \norm{f-P_K}^2=0$;
> критерий полноты — `parseval_iff_complete_b` (Глава 7.1). 0 аксиом.

## Расхождение 2. Рисс–Фишер: теорема при фиксированном усечении, её заключение совпадает с посылкой, к частичным суммам ряда Фурье она не применена (стр. 43–44, 110–112; сноска 2)

**Было:**

> (43–44) *Второй* — процессное чтение: ряд Фурье как процесс $K\mapsto P_K$ с убывающей ошибкой,
> L<sup>2</sup>-полнота по построению (Рисс–Фишер Части VI).
>
> (106–112) Для бесконечной системы требуется отдельный Коши-процесс по $K$ и доказательство исчезновения
> хвоста… Здесь и помогает Рисс–Фишер из Части VI: *если* такой Коши-процесс частичных сумм построен, его
> предел читается как L<sup>2</sup>-процесс (пространство L<sup>2</sup>-процессов Коши-полно по
> построению).[^2]
>
> (сноска 2) Процессное прочтение Рисса–Фишера — `l2_riesz_fischer` в `ProcessL2RieszFischer.v` (Часть VI):
> L<sup>2</sup>-пространство процессов Коши-полно по построению; это *мост* к носителю предела…

**Проверка.** `src/process/ProcessL2RieszFischer.v`:

```coq
Definition L2CauchySq (F : nat -> nat -> Q) (N : nat) : Prop :=          (* :87 *)
  forall eps, eps > 0 ->
  exists M, forall m n, (M <= m)%nat -> (M <= n)%nat ->
    seq_inner (fun i => F m i - F n i) (fun i => F m i - F n i) N <= eps.

Definition l2_limit (F : nat -> nat -> Q) : nat -> (nat -> Q) :=         (* :112 *)
  fun i s => F s i.

Theorem l2_riesz_fischer : forall (F : nat -> nat -> Q) (N : nat),       (* :134 *)
  L2CauchySq F N ->
  forall eps, eps > 0 ->
  exists M, forall n s, (M <= n)%nat -> (M <= s)%nat ->
    seq_inner (fun i => F n i - l2_limit F i s)
              (fun i => F n i - l2_limit F i s) N <= eps.
```

`Print Assumptions l2_riesz_fischer`: Closed under the global context. Три обстоятельства:

1. Теорема стоит при фиксированном конечном усечении `N`. Глава 6.5 это оговаривает; в Главе 7.4 оговорки нет,
   а теорема привлечена для случая бесконечной системы (стр. 106–112). На `N` координатах ортонормированных
   векторов не больше `N` (`Check.v`, `orthonormal_count_le_dim`), так что бесконечной ортонормированной
   системы при фиксированном `N` нет.
2. После развёртывания `l2_limit F i s = F s i` заключение теоремы дословно совпадает с посылкой
   (`Check.v`, раздел 5, `rf_conclusion_is_hypothesis`: равносильность доказана тождественной функцией). Это
   найдено при проверке Части VI; содержательная форма при фиксированном `N` с тех пор записана в `src` —
   `riesz_fischer_process_form` (`ProcessL2Orthonormal.v:618`): координаты предела — процессы Коши, расстояние
   до предела — процесс Коши, это расстояние стремится к нулю.
3. Ни `L2CauchySq`, ни `l2_riesz_fischer` в `src` не применены к частичным суммам $P_K$: эти имена встречаются
   только в `ProcessL2RieszFischer.v` и `ProcessL2Orthonormal.v` (поиск). Опорные файлы главы
   `ProcessL2RieszFischer.v` не подключают. «Мост» сноски 2 проведён в тексте, а не теоремой.

Слова главы о том, чего Рисс–Фишер *не* даёт (стр. 112–115: Коши-сходимость ряда к $f$ из одного Бесселя не
следует; гарантирован носитель, а не то, что предел есть $f$), формализации отвечают и расхождением не
являются.

**В чём расхождение.** Слова «пространство L<sup>2</sup>-процессов Коши-полно по построению» сказаны без
оговорки о фиксированном усечении и отнесены к бесконечной системе, тогда как названная теорема говорит о
векторах из `N` координат, её заключение есть её посылка, а к ряду Фурье она в формализации не приложена.

**(а) Довести формализацию.** При фиксированном `N` дописывать нечего: `riesz_fischer_process_form` уже в
`src`, достаточно назвать её в сноске. Мост к ряду Фурье без аксиом проводится для стандартной системы
$\delta_k$ при нефиксированном усечении. Проверено (`Check.v`, раздел 4; Closed under the global context):

```coq
(* При K <= N ошибка на N координатах есть энергия между K и N; при N <= K она нулевая. *)
Theorem std_error_is_tail : forall (f : nat -> Q) (N K : nat), (K <= N)%nat ->
  ferr delta f N K == captured f N - captured f K.
Theorem std_error_zero_beyond : forall (f : nat -> Q) (N K : nat), (N <= K)%nat ->
  ferr delta f N K == 0.

(* Остаток ряда Фурье стремится к нулю равномерно по усечению N тогда и только
   тогда, когда энергетический процесс K |-> Sum_{i<K} f_i^2 есть процесс Коши. *)
Theorem std_fourier_l2_convergence_iff : forall f : nat -> Q,
  is_Cauchy (fun n => captured f n)
  <-> (forall eps, 0 < eps -> exists M, forall K N, (M <= K)%nat ->
         ferr delta f N K < eps).

(* Частичные суммы образуют L2-Коши-последовательность; стадия M не зависит от N. *)
Definition std_psum (f : nat -> Q) (N : nat) : nat -> nat -> Q :=
  fun K m => q_sum (fun k => seq_inner (delta k) f N * delta k m) K.

Theorem std_partial_sums_cauchy : forall f : nat -> Q,
  is_Cauchy (fun n => captured f n) ->
  forall eps, 0 < eps -> exists M, forall N K K', (M <= K)%nat -> (M <= K')%nat ->
    seq_inner (fun i => std_psum f N K i - std_psum f N K' i)
              (fun i => std_psum f N K i - std_psum f N K' i) N <= eps.

Corollary std_partial_sums_L2CauchySq : forall (f : nat -> Q) (N : nat),
  is_Cauchy (fun n => captured f n) -> L2CauchySq (std_psum f N) N.

(* Координаты построенного предела — координаты f. *)
Lemma std_limit_is_f : forall (f : nat -> Q) (N m s : nat),
  (m < N)%nat -> (m < s)%nat -> l2_limit (std_psum f N) m s == f m.
```

Посылка выполнима: последовательность с конечным носителем (`finite_support_energy_cauchy`) и
последовательность с бесконечным числом ненулевых членов $f_i=2^{-i}$ (`geometric_energy_cauchy`; следствие
`geometric_fourier_converges`: остаток её ряда Фурье стремится к нулю). Завершённого предела эти утверждения
не вводят: говорится о стадиях процесса и об оценке, равномерной по усечению.

Для произвольной бесконечной ортонормированной системы такого утверждения нет, и просто его не получить:
сначала нужно определение ортонормированности семейства при растущем числе координат (при фиксированном `N`
оно невозможно). Это остаётся границей, как глава и говорит.

**(б) Поправить слова.**

> (43–44) *Второй* — процессное чтение: ряд Фурье как процесс $K\mapsto P_K$ с убывающей ошибкой,
> L<sup>2</sup>-полнота по построению при фиксированном усечении $N$ (Рисс–Фишер Части VI).
>
> (110–112) Здесь и помогает Рисс–Фишер из Части VI: *если* такой Коши-процесс частичных сумм построен, его
> предел читается как L<sup>2</sup>-процесс (при всяком фиксированном усечении $N$ пространство
> L<sup>2</sup>-процессов Коши-полно по построению: предел строится покоординатно).[^2]
>
> (сноска 2) Процессное прочтение Рисса–Фишера — `l2_riesz_fischer` в `ProcessL2RieszFischer.v` и
> `riesz_fischer_process_form` в `ProcessL2Orthonormal.v` (Часть VI): при фиксированном усечении $N$ предел
> Коши-последовательности строится покоординатно, его координаты — процессы Коши, расстояние до него стремится
> к нулю; это *мост* к носителю предела, см. § «Граница: завершённый ряд, поточечная сходимость, Гиббс». К
> частичным суммам ряда Фурье теорема в формализации не приложена.

Если принят путь (а), последняя фраза сноски заменяется:

> Для стандартной системы мост проведён в `ProcessFourierTruncation.v`: при Коши-энергии $f$ частичные суммы
> образуют L<sup>2</sup>-Коши-последовательность со стадией, не зависящей от $N$ (`std_partial_sums_cauchy`),
> остаток стремится к нулю (`std_fourier_l2_convergence_iff`), а координаты построенного предела суть
> координаты $f$ (`std_limit_is_f`).

## Расхождение 3. Сноски 4 и 7: связь лемм названа неточно (стр. 266, 269)

**Было:**

> (сноска 4) `fourier_error_nonneg`; эквивалентно `bessel_general` (Глава 7.1).
>
> (сноска 7) `fourier_error_zero_iff`: …; опирается на критерий полноты `parseval_iff_complete` (Глава 7.1). 0
> аксиом.

**Проверка.** `fourier_error_nonneg` (`ProcessFourierSeriesL2.v:71`) после закрытия раздела есть
`forall e N f K, 0 <= ‖f − P_K‖²` — без посылки; доказательство: `apply q_sum_nonneg; intro i; apply
q_sq_nonneg`. Неравенство Бесселя для неортонормированного семейства неверно, так что два утверждения
равносильны только вместе с тождеством ошибки `fourier_error_eq`. Основной текст (стр. 135–137) говорит точнее:
«Ошибка $\ge0$ — значит, $\sum c_k^2\le\|f\|^2$».

Доказательство `fourier_error_zero_iff` (`:89–91`): `pose proof (fourier_error_eq K) as H. split; intro Hx;
lra.` Теорема `parseval_iff_complete` в нём не участвует; `ProcessFourierSeriesL2.v` файл
`ProcessL2Parseval.v` напрямую не подключает. Слова основного текста «то есть когда система *полностью*
восстанавливает $f$» (стр. 163–164) получаются соединением двух теорем; одним утверждением в `src` это не
записано.

**В чём расхождение.** Сноска 4 называет равносильными утверждение без посылки и утверждение, требующее
ортонормированности; сноска 7 называет опорой леммы теорему, которой доказательство не пользуется.

**(а) Довести формализацию.** Соединяющее утверждение — `fourier_error_zero_iff_recovers_b` (расхождение 1,
проверено).

**(б) Поправить слова** (в прежних именах; в новых — см. расхождение 1):

> (сноска 4) `fourier_error_nonneg`; вместе с тождеством ошибки `fourier_error_eq` даёт `bessel_general`
> (Глава 7.1).
>
> (сноска 7) `fourier_error_zero_iff`: $\norm{f-P_K}^2=0 \Leftrightarrow \sum_{k<K}c_k^2=\norm{f}^2$; вместе
> с критерием полноты `parseval_iff_complete` (Глава 7.1) это и даёт «нулевая ошибка $\Leftrightarrow$ точное
> восстановление». 0 аксиом.

## Сомнительные места, расхождением не являющиеся

- **Что в формализации значит «сходимость ряда Фурье в L²».** Определения сходимости в названных файлах нет.
  Утверждения о стремлении остатка к нулю (вида «для всякого $\varepsilon$ найдётся $K$») нет. Утверждения о
  сходимости частичных сумм (условие Коши по $K$) нет. Есть монотонность остатка (`fourier_error_monotone`,
  нестрогая, под невыполнимой посылкой — расхождение 1) и критерий «остаток нулевой $\Leftrightarrow$
  Парсеваль» при данном $K$. Повтора посылки в заключении у теорем двух опорных файлов нет (он есть у
  `l2_riesz_fischer` — расхождение 2). Страница это называет сама: «сходимость — как *монотонное убывание
  ошибки*» (стр. 16–17), «это *ещё не* полная L<sup>2</sup>-сходимость к самой $f$» (стр. 101), «завершённый
  ряд… — роль-предел» (стр. 33–37); поэтому расхождением не записано. При выполнимой посылке и фиксированном
  `N` процесс $K\mapsto P_K$ имеет не более `N` содержательных шагов (`orthonormal_count_le_dim`), а для
  полной системы оканчивается точным восстановлением при $K=N$ (`fourier_truncation_ends_exactly`). Утверждение
  о стремлении остатка к нулю в собственном смысле доказано в пробном файле для стандартной системы при
  нефиксированном усечении (`std_fourier_l2_convergence_iff`, расхождение 2, пункт (а)).
- **«Конечная рациональная сумма, доводимая до любой нужной точности» (стр. 81–82).** Если читать это как
  свойство процесса $K\mapsto P_K$, то утверждения «ошибка становится меньше всякого $\varepsilon$» в названных
  файлах нет. Для полной конечной системы верно большее — нулевая ошибка при
  $K=N$; для бесконечного случая — см. предыдущий пункт. Фраза описательная, доказанной её страница не
  называет.
- **«Отброшенная хвостовая энергия» (стр. 19, 132–133).** В Rocq правая часть тождества — $\|f\|^2$ минус
  захваченная энергия. Суммой квадратов отброшенных коэффициентов $\sum_{K\le k<K_0}c_k^2$ она становится при
  полной системе (`Check.v`, `fourier_error_is_tail_b`: при равенстве Парсеваля на $K_0$ векторах); для
  неполной системы в неё входит и энергия вне оболочки системы. Формула страницы (стр. 124–130) записана
  точно.
- **«$K\le N$» в Элементах (стр. 65, 230) и в шапке файла.** В прежних теоремах усечение `K` не ограничено
  (`forall K`) — отсюда и невыполнимая посылка. При выполнимой посылке ограничение $K\le K_0\le N$ входит в
  утверждения; слова страницы отвечают именно им.
- **«Монотонно убывает» (стр. 28, 139–142).** Доказано нестрогое неравенство; страница так и говорит («не
  возрастает», «уменьшает (не увеличивает)»). Точный шаг — `fourier_error_step_b`: ошибка при $K+1$ меньше
  ошибки при $K$ ровно на $c_K^2$.
- **«Для стандартного полного $N$-направленного набора — точно при $K=N$» (стр. 166–169).** В названных главой
  файлах есть только числовой пример `parseval_std_concrete` (`ProcessL2Parseval.v:156`; $N=2$, $f=(3,4)$,
  прямое вычисление). Общее утверждение есть в `src`: `parseval_std_all` (`ProcessL2Orthonormal.v:337`);
  нулевая ошибка при $K=N$ — `std_truncation_ends_exactly` (`Check.v`). Верно и больше: то же для любых `N`
  ортонормированных векторов на `N` координатах (`fourier_truncation_ends_exactly`). Страница теоремы здесь не
  называет; имя стоит добавить.
- **«Доказуемое ядро» (стр. 18–20, 144–147, 199–201).** Записано `ok`: слово «доказуемое» верно — при
  выполнимой посылке всё перечисленное доказано (`Check.v`, раздел 1). Расхождением записаны места, где
  сказано «доказано» (стр. 25, 42, 133).
- **«Отсюда три следствия» (стр. 133).** Отдельными абзацами названы два — неотрицательность и монотонное
  убывание; третье (нуль ровно при Парсевале) стоит в итоговой фразе на стр. 144–146 и в следующем разделе.
- **Сноска 1, «поверх L²-аппарата Части VI (…, `ProcessL2RieszFischer.v`)».** Два опорных файла подключают
  `ProcessL2BesselGeneral.v` и `ProcessL2Parseval.v`; `ProcessL2RieszFischer.v` ни один из них не подключает.
- **Сноска 8, «Roles: $P_K$ — приближение».** В шапке `ProcessFourierSeriesL2.v` в строке Roles стоят
  `err(K)` (хвостовая энергия, дефект полноты) и `captured(K)`; $P_K$ как наилучшее приближение названа ролью
  в шапке `ProcessBestApproximation.v`. Остальное в сноске совпадает с шапками.
- **`captured` (сноска 3).** Определение лежит в `ProcessFourierCompression.v:42` (файл Главы 7.5), а не в
  `ProcessFourierSeriesL2.v`; страница места определения не называет.

## Вне главы

- Глава 7.1 называет те же прежние теоремы (`resid_norm`, `bessel_general`, `best_approx_eq`,
  `best_approx_ge`, `best_approx_unique`, `parseval_iff_complete`; сноски на стр. 400–404); сказанное в
  расхождении 1 относится и к ней.
- Шапка `ProcessFourierSeriesL2.v`: «Elements: … K ≤ N» и «for an orthonormal system … for a FIXED N» — в
  утверждениях ограничения `K ≤ N` нет, а посылка требует ортонормированности при всех номерах; отсылка «(cf.
  7.4)» в шапке файла самой Главы 7.4 указывает на себя. Шапка `ProcessBestApproximation.v`: «among ALL linear
  combinations … of a finite orthonormal system» — посылка говорит о бесконечном семействе.
- `ProcessBestApproximation.v` подключается только файлом `ProcessFourierSeriesL2.v`, а тот — ни одним файлом
  `src` (поиск по именам теорем и по `Require`): после появления утверждений с выполнимой посылкой оба можно
  пометить в шапке как прежнюю запись.
- `ProcessL2RieszFischer.v`, шапка (стр. 11–17): «Classical Riesz–Fischer (L²/ℓ² is complete) is proved here in
  its constructive P4 core» — при том, что заключение `l2_riesz_fischer` совпадает с посылкой; шапка
  `ProcessL2Orthonormal.v` называет содержательную форму (`riesz_fischer_process_form`).
- В `src/process/ProcessL2.v` есть процессное ℓ² с нефиксированным усечением: `norm_process` (`:39`), `in_L2`
  (`:63`) — ограниченность процесса нормы, и теорема `L2_norm_cauchy` (`:67`): ограниченный процесс нормы есть
  процесс Коши. Её цена — `Classical_Prop.classic` (`PA2.out`). Теоремы раздела 4 пробного файла берут
  посылкой само условие Коши для энергетического процесса (`is_Cauchy (fun n => captured f n)`) и аксиом не
  требуют; с `ProcessL2.v` они не связаны. При доводке стоит решить, на каком из двух определений строить
  бесконечный случай.
