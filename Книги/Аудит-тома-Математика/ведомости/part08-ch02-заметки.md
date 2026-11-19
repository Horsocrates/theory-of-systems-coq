# Глава VIII.2 «Метод Эйлера: решение на сетке» — заметки к ведомости (18.11.2026)

Ведомость: `part08-ch02.json` — 49 ручных записей, автоматических нет; `merge --dry` проходит без замечаний,
список «без сверки» пуст. Вердикты: ok — 44, mismatch-statement — 5. Расхождений цены, имён без объявления и
неверных чисел нет.

Пять записей с расхождением относятся к четырём местам: одна — к расхождению 1 (оценка сверху тройкой), две —
к расхождению 2 (точность для линейного уравнения), одна — к расхождению 3 (ошибка для квадратичного), одна —
к расхождению 4 (чтение шапки файла в сноске 10).

Глава называет два файла: `src/analysis/PicardLindelof.v` (23 `Qed`; шапка: 23) и
`src/process/ProcessExpProcess.v` (12 `Qed`; шапка: 12). Оба прочитаны целиком. Строк `Axiom`, `Parameter`,
`Admitted` в них нет; подключена только стандартная библиотека (`QArith`, `Qabs`, `Lia`, `ZArith`, `List`,
`Lqa`). `Print Assumptions` снят для всех 35 утверждений (`PA.v`): каждое — «Closed under the global context».
Исходники в репозитории и в собранной копии совпадают (`diff`). Цена на странице («без аксиом», «0 аксиом»)
названа верно всюду. Чисел `Qed` и числа файлов страница не называет.

Десять фрагментов кода главы (стр. 114; сноски 2, 3, 5, 6, 7, 9) сверены с исходником и совпадают; два
отличаются только пробелами (`3#4` при `3 # 4` в исходнике; `y*(1+h)` при `y * (1 + h)`). Формулы сносок 2 и 4
(`inject_Z(Z.of_nat k) / inject_Z(Z.of_nat N)`, `1/inject_Z(Z.of_nat N)`) совпадают с телом определений `grid`
и `euler_traj`. Блоков кода (огороженных) в главе нет.

Пробные файлы лежат в `C:/Users/abary/tos-audit-build/_part08/ch02/`:

- `status.txt` — вывод `tom-status.cjs chapter 08/02`;
- `PA.v`, `PA.out` — `Print Assumptions` всех утверждений двух файлов;
- `Check.v`, `Check.out` — пробные доказательства, разделы 0–5 по местам главы. Собирается: 42 `Qed`; все 22
  утверждения, для которых снят `Print Assumptions`, — «Closed under the global context». В файле нет `Axiom`,
  `Parameter`, `Admitted`, библиотеки `Reals`, функциональной экстенсиональности;
- `checklines.cjs` — сверка номеров строк ведомости со страницей (несовпадений нет).

В `src`, в собранной копии и на сайте ничего не менялось; база связей не менялась (`merge` запускался только с
`--dry`); ничего не коммитилось.

## Что проверить не удалось

- Отсылки к другим главам (8.1, 8.3, 8.5, Часть II, Глава 7.1) по содержанию не сверялись — это предмет их
  ведомостей. Сверены адреса: Глава 8.1 — «Задача Коши и решение как процесс», говорит о трёх уровнях строгости
  (стр. 60) и называет `euler_traj` (сноска 4); Глава 8.5 называет `ProcessExpProcess.v`, `exp1_is_euler`,
  `exp1_lower` (сноски 1, 4, 5); в Главе 7.1 есть слова «завершённая сумма» (стр. 48); в Части II —
  «роль-количество». Для отсылки к Главе 8.3 (стр. 268–272) прочитаны утверждение `picard_op_contraction` и
  определения `picard_op`, `picard_sum`, `Tlen` (`process/ProcessPicardOperator.v`), снят `Print Assumptions`;
  остальные теоремы того файла не смотрелись.
- Предложенные в пункте (а) дополнения проверены как пробный файл поверх собранных модулей (`Check.v`); как
  файл `src` с записью в `_CoqProject` они не собирались.
- Слова о точных решениях ($y(t) = t$, $y(t) = t^2$, $y(t) = e^t$) и о числе $e \approx 2{,}718$ с
  формализацией не сверялись: в двух названных файлах нет ни понятия решения, ни производной, ни числа $e$;
  леммы сравнивают значения траектории с числами. Проверена только арифметика: $625/256 = 2{,}44140625$.
- Сходимость лестницы $(1+1/N)^N$ (свойство Коши, модуль сходимости) не пробовалась: страница её не заявляет.
- Английская страница и LaTeX-исходник главы не смотрелись.

Всё остальное проверено по исходнику и компилятору.

## Расхождение 1. «Ограниченную снизу двойкой и сверху тройкой»: сверху оценены четыре стадии, а не вся последовательность (стр. 27–31)

**Было:**

> (27–31) Доказанное ядро — конкретное и арифметическое. Траектория Эйлера определена как рекурсия над ℚ; её
> значения на эталонных уравнениях вычислены точно: для линейного уравнения метод *точен*, для квадратичного
> даёт явную рациональную ошибку, для экспоненциального — последовательность $(1+1/N)^N$ рациональных
> приближений, ограниченную снизу двойкой и сверху тройкой.[^1]

**Проверка.** Оценка снизу доказана для всех стадий (`src/process/ProcessExpProcess.v:129`):

```coq
Lemma exp1_lower : forall N, 2 <= exp1_process N.
```

Оценка сверху доказана для четырёх стадий:

```coq
Lemma euler_traj_exp_converges : 625 # 256 < 3.                      (* PicardLindelof.v:120 *)
Lemma euler_exp_sandwich :                                           (* PicardLindelof.v:282 *)
  2 < euler_traj f_identity 1 4 4 /\ euler_traj f_identity 1 4 4 < 3.
Lemma exp1_below3 :                                                  (* ProcessExpProcess.v:152 *)
  exp1_process 0 < 3 /\ exp1_process 1 < 3 /\ exp1_process 2 < 3.
```

то есть для $N = 4$ и для $N = 1, 2, 3$. `Print Assumptions` всех четырёх: Closed under the global context.
Утверждения вида `forall N, … < 3` в `src` нет: имена `exp1_process` и `euler_yeqy` встречаются только в
`ProcessExpProcess.v`, имя `euler_traj` — только в `PicardLindelof.v`; в третьем файле с той же лестницей,
`analysis/PeanoExistence.v`, тоже только стадии $N = 1, 2, 4$ (`euler_e_bounded_N4`, `:159`). Шапка
`ProcessExpProcess.v` (`:21–25`) говорит то же: «Full monotonicity, the uniform bound < 3 for all N (binomial)
… left as the honest P4 frontier».

Страница сама называет эту границу ниже (стр. 185–190: «Полная монотонность для всех $N$ и оценка $< 3$ для
всех $N$ (через бином) в нашей формализации не доказаны… Доказано конкретное: … нижняя оценка ${}\ge 2$ для
всех $N$ и проверяемые верхние оценки для показанных стадий»). Расхождение — только в сводной фразе
стр. 30–31, где оценка сверху стоит рядом с оценкой снизу как свойство всей последовательности.

**В чём расхождение.** В перечне доказанного последовательность названа ограниченной сверху тройкой; доказано
это для четырёх стадий, а для всех $N$ — только оценка снизу.

**(а) Довести формализацию до слов главы.** Возможно, без аксиом и без бинома. Достаточно оценки
$(1+h)^k < 1 + kh + (kh)^2$ при $h > 0$, $k \ge 1$, $kh \le 1$ (индукция по $k$; шаг — тождество
$\bigl(1 + (m{+}1)h + ((m{+}1)h)^2\bigr) - (1+h)\bigl(1 + mh + (mh)^2\bigr) = h^2\bigl(1 + m(1 - mh)\bigr) \ge 0$);
при $h = 1/N$, $k = N$ правая часть равна $3$. Проверено в `Check.v`, раздел 4 (новый файл, существующие не
меняются; `qpow`, `exp1_process`, `exp1_pos_denom` — из `ProcessExpProcess.v`):

```coq
Lemma inj_S : forall k : nat,
  inject_Z (Z.of_nat (S k)) == inject_Z (Z.of_nat k) + 1.
Proof.
  intro k. rewrite Nat2Z.inj_succ, <- Z.add_1_r, inject_Z_plus. reflexivity.
Qed.

Lemma inj_nonneg : forall k : nat, 0 <= inject_Z (Z.of_nat k).
Proof. intro k. change 0 with (inject_Z 0). rewrite <- Zle_Qle. lia. Qed.

Lemma quad_step : forall h m P : Q,
  0 < h -> 0 <= m -> m * h <= 1 ->
  P < 1 + m * h + (m * h) * (m * h) ->
  (1 + h) * P < 1 + (m + 1) * h + ((m + 1) * h) * ((m + 1) * h).
Proof.
  intros h m P Hh Hm Hmh HP.
  assert (H1 : (1 + h) * P < (1 + h) * (1 + m * h + (m * h) * (m * h))).
  { apply Qmult_lt_l; [ lra | exact HP ]. }
  assert (Hd : 1 + (m + 1) * h + ((m + 1) * h) * ((m + 1) * h)
               - (1 + h) * (1 + m * h + (m * h) * (m * h))
               == h * h * (1 + m * (1 - m * h))) by ring.
  assert (Hnn : 0 <= h * h * (1 + m * (1 - m * h))).
  { apply Qmult_le_0_compat.
    - apply Qmult_le_0_compat; lra.
    - assert (0 <= m * (1 - m * h)) by (apply Qmult_le_0_compat; lra). lra. }
  lra.
Qed.

Lemma qpow_quad_strict : forall (h : Q) (k : nat),
  0 < h ->
  inject_Z (Z.of_nat (S k)) * h <= 1 ->
  qpow (1 + h) (S k) <
  1 + inject_Z (Z.of_nat (S k)) * h
    + (inject_Z (Z.of_nat (S k)) * h) * (inject_Z (Z.of_nat (S k)) * h).
Proof.
  intros h k Hh. induction k as [|k IH]; intro Hb.
  - cbn [qpow]. change (inject_Z (Z.of_nat 1)) with 1.
    assert (Hhh : 0 < h * h) by (apply Qmult_lt_0_compat; exact Hh).
    assert (He : 1 + 1 * h + 1 * h * (1 * h) - (1 + h) * 1 == h * h) by ring.
    lra.
  - pose proof (inj_S (S k)) as Hs.
    pose proof (inj_nonneg (S k)) as Hm.
    assert (Hmh : inject_Z (Z.of_nat (S k)) * h <= 1).
    { rewrite Hs in Hb.
      assert (Hx : (inject_Z (Z.of_nat (S k)) + 1) * h
                   == inject_Z (Z.of_nat (S k)) * h + h) by ring.
      rewrite Hx in Hb. lra. }
    specialize (IH Hmh).
    change (qpow (1 + h) (S (S k))) with ((1 + h) * qpow (1 + h) (S k)).
    rewrite Hs.
    apply quad_step; assumption.
Qed.

(* e-процесс ограничен сверху тройкой на всех стадиях *)
Theorem exp1_upper : forall N : nat, exp1_process N < 3.
Proof.
  intro N. unfold exp1_process.
  pose proof (exp1_pos_denom N) as Hd.
  remember (inject_Z (Z.of_nat (S N))) as d eqn:Hde.
  assert (Hh : 0 < 1 / d).
  { unfold Qdiv. rewrite Qmult_1_l. apply Qinv_lt_0_compat. exact Hd. }
  assert (Hdh : d * (1 / d) == 1) by (field; lra).
  pose proof (qpow_quad_strict (1 / d) N Hh) as HB.
  rewrite <- Hde in HB.
  assert (Hb : d * (1 / d) <= 1) by (rewrite Hdh; apply Qle_refl).
  specialize (HB Hb). rewrite Hdh in HB. lra.
Qed.
```

Чтобы оценка относилась к траектории самой главы (`euler_traj` из `PicardLindelof.v`), нужна связь двух
рекурсий — она сейчас теоремой не записана (сомнительное место 1). `Check.v`, раздел 3:

```coq
Theorem euler_traj_exp_closed : forall (y0 : Q) (N k : nat),
  euler_traj f_identity y0 N k == y0 * qpow (1 + 1 / inject_Z (Z.of_nat N)) k.
Proof.
  intros y0 N k. induction k as [|k IH].
  - cbn [euler_traj qpow]. ring.
  - cbn [euler_traj qpow]. rewrite euler_step_concrete, IH. ring.
Qed.

Theorem euler_traj_is_euler_yeqy : forall (y0 : Q) (N k : nat),
  euler_traj f_identity y0 N k == euler_yeqy (1 / inject_Z (Z.of_nat N)) y0 k.
Proof.
  intros y0 N k. rewrite euler_traj_exp_closed, euler_yeqy_closed. reflexivity.
Qed.

Theorem exp1_is_euler_traj : forall N : nat,
  exp1_process N == euler_traj f_identity 1 (S N) (S N).
Proof.
  intro N. rewrite euler_traj_exp_closed. unfold exp1_process. ring.
Qed.

(* 2 <= (1+1/N)^N < 3 для траектории главы при всех N >= 1 *)
Corollary euler_traj_exp_sandwich_all : forall N : nat,
  2 <= euler_traj f_identity 1 (S N) (S N) /\
  euler_traj f_identity 1 (S N) (S N) < 3.
Proof.
  intro N. rewrite <- exp1_is_euler_traj.
  split; [ apply exp1_lower | apply exp1_upper ].
Qed.
```

`Print Assumptions exp1_upper`, `exp1_is_euler_traj`, `euler_traj_exp_sandwich_all`: Closed under the global
context.

Тем же пробным файлом закрывается и вторая половина границы, названной на стр. 185–187, — монотонность для всех
$N$ (`Check.v`, раздел 5, стр. 293–450 файла). Ход: неравенство Бернулли при $x \ge -1$ (в `ProcessExpProcess.v`
оно есть только при $x \ge 0$), его строгая форма при показателе не меньше двух и $x \ne 0$, и разложение
$1 + \tfrac{1}{d+1} = \bigl(1 + \tfrac1d\bigr)\bigl(1 - \tfrac{1}{(d+1)^2}\bigr)$:

```coq
Lemma bernoulli_ge_m1 : forall (x : Q) (n : nat),
  -1 <= x -> 1 + inject_Z (Z.of_nat n) * x <= qpow (1 + x) n.
Lemma bernoulli_strict : forall (x : Q) (n : nat),
  -1 <= x -> ~ x == 0 ->
  1 + inject_Z (Z.of_nat (S (S n))) * x < qpow (1 + x) (S (S n)).
Theorem exp1_increasing : forall N : nat, exp1_process N < exp1_process (S N).
Corollary euler_traj_exp_increasing : forall N : nat,
  euler_traj f_identity 1 (S N) (S N) < euler_traj f_identity 1 (S (S N)) (S (S N)).
Theorem exp1_ladder : forall N : nat,
  2 <= exp1_process N /\ exp1_process N < exp1_process (S N) /\ exp1_process (S N) < 3.
```

Все — Closed under the global context. Предлагаемое оформление: один новый файл (например
`src/analysis/EulerTrajectoryGeneral.v`) с разделами 1–5 пробного файла; он подключает
`analysis.PicardLindelof` и `process.ProcessExpProcess`, оба — только на стандартной библиотеке.

После такого дополнения слова стр. 27–31 верны без правки, а стр. 181–190 и сноска 9 устаревают в другую
сторону («не доказаны»). Текст для них:

> (181–190) Это в точности тот же приём, что для $e$-процесса как решения $y' = y$ (Глава 8.5): тамошняя
> последовательность $(1+1/(N{+}1))^{N+1}$ — та же лестница рациональных стадий, и доказано, что она *есть*
> траектория Эйлера уравнения $y' = y$ при $t = 1$, ограничена снизу двойкой *для всех* $N$ (по неравенству
> Бернулли), сверху — тройкой *для всех* $N$ и растёт на каждой стадии.[^9] Честная граница данного слоя —
> завершённый предел: явное число $e$ как завершённая трансцендентность — роль-предел. Доказано конкретное:
> рациональные стадии, оценки $2 \le (1+1/N)^N < 3$ и рост для всех $N$; завершённое $e$ не строится.
>
> (сноска 9) `exp1_is_euler` (тождество «$e$-процесс${}={}$траектория Эйлера для $y'=y$ при $t=1$») и
> `exp1_lower` ($e$-процесс${}\ge 2$ *для всех* $N$, через Бернулли) — в `ProcessExpProcess.v` (Глава 8.5,
> батч C); `exp1_upper` ($e$-процесс${}< 3$ *для всех* $N$), `exp1_increasing` (рост *для всех* $N$) и
> `exp1_is_euler_traj` (та же лестница есть `euler_traj` этой главы при $k = N$) — в
> `EulerTrajectoryGeneral.v`; стадии $2, 9/4, 64/27$ (`exp1_0`, `_1`, `_2`) — конкретные. 0 аксиом (проверено
> `Print Assumptions`).

Имя файла в сноске — по тому, как он будет назван. Шапку `ProcessExpProcess.v` (строки о «HONEST FRONTIER»)
тогда тоже стоит поправить — это уже правка существующего файла, только комментария.

**(б) Поправить слова** (если формализацию не дополнять). Стр. 27–31:

> Доказанное ядро — конкретное и арифметическое. Траектория Эйлера определена как рекурсия над ℚ; её значения
> на эталонных уравнениях вычислены точно: для линейного уравнения метод *точен*, для квадратичного даёт явную
> рациональную ошибку, для экспоненциального — последовательность $(1+1/N)^N$ рациональных приближений,
> ограниченную снизу двойкой при всех $N$, а на показанных стадиях — и сверху тройкой.[^1]

(Слова «метод *точен*» в этой же фразе — расхождение 2.)

## Расхождение 2. «Для линейного уравнения метод точен», «для уравнений без кривизны метод… воспроизводит решение»: в названном файле — три узла одной сетки (стр. 28–29, 131–133; те же слова в E/R/R-чтении — стр. 54–56, 221–222)

**Было:**

> (28–29) …её значения на эталонных уравнениях вычислены точно: для линейного уравнения метод *точен*…
>
> (131–133) Причина точности проста: наклон постоянен, касательная *совпадает* с графиком, и шаг по касательной
> не накапливает ошибки. Для уравнений без кривизны метод Эйлера не приближает, а *воспроизводит* решение.
>
> (сноска 5) `euler_traj_linear_1`, `_2`, `_4` в `PicardLindelof.v`: `euler_traj f_const_one 0 4 k` даёт
> $1/4, 1/2, 1$ для $k = 1, 2, 4$. Точность — следствие отсутствия кривизны: правая часть постоянна.

**Проверка.** `src/analysis/PicardLindelof.v`:

```coq
Lemma euler_traj_linear_1 : euler_traj f_const_one 0 4 1 == 1 # 4.   (* :142 *)
Lemma euler_traj_linear_2 : euler_traj f_const_one 0 4 2 == 1 # 2.   (* :148 *)
Lemma euler_traj_linear_4 : euler_traj f_const_one 0 4 4 == 1.       (* :154 *)
Lemma euler_linear_exact_2 : euler_traj (f_const 3) 0 2 2 == 3.      (* :324 *)
```

Четыре значения: три узла сетки $N = 4$ для $y' = 1$, $y(0) = 0$ и один узел сетки $N = 2$ для $y' = 3$. Узел
$k = 3$ сетки $N = 4$ леммой не записан (значение $3/4$ вычислено в `Check.v`, `linear_node_3`). Утверждения
для произвольных $N$, $k$, начального значения или постоянной в файле нет. `Print Assumptions` четырёх лемм:
Closed under the global context. То, что глава говорит о самих значениях (стр. 129–131, первая фраза сноски 5),
совпадает с леммами точно.

Общее утверждение в формализации есть, но для другой рекурсии и в файле, который глава не называет
(`src/stdlib/ODE.v:139`, Closed under the global context):

```coq
Lemma euler_constant_explicit :
  forall x0 h c n,
    let sys := mkODE (fun _ _ => c) x0 h in
    euler_steps sys n == x0 + inject_Z (Z.of_nat n) * h * c.
```

Здесь `euler_steps` — рекурсия по записи `ODE` (правая часть, начальное значение, шаг $h$) из `stdlib/ODE.v`;
с `euler_traj` главы она теоремой не связана.

**В чём расхождение.** Общие слова («метод точен», «для уравнений без кривизны… воспроизводит решение») в
названном файле опираются на три вычисленных значения; общая лемма есть для другой рекурсии и на странице не
названа.

**(а) Довести формализацию до слов главы.** Возможно, без аксиом; посылка $N \ge 1$ не нужна (при $N = 0$ шаг и
узлы над ℚ равны нулю, равенство выполняется). `Check.v`, раздел 1 (`f_const`, `grid_0` — из
`PicardLindelof.v`; `inj_S` — как в расхождении 1):

```coq
Lemma inj_pos : forall k : nat, (0 < k)%nat -> 0 < inject_Z (Z.of_nat k).
Proof. intros k Hk. change 0 with (inject_Z 0). rewrite <- Zlt_Qlt. lia. Qed.

Lemma grid_NN : forall N : nat, (0 < N)%nat -> grid N N == 1.
Proof.
  intros N HN. unfold grid. pose proof (inj_pos N HN) as Hp.
  field. intro Hc. rewrite Hc in Hp. apply (Qlt_irrefl 0). exact Hp.
Qed.

(* любая постоянная правая часть, любое начальное значение, любая сетка, любой узел *)
Theorem euler_traj_const_exact : forall (a y0 : Q) (N k : nat),
  euler_traj (f_const a) y0 N k == y0 + a * grid N k.
Proof.
  intros a y0 N k. induction k as [|k IH].
  - cbn [euler_traj]. rewrite grid_0. ring.
  - cbn [euler_traj]. unfold euler_step, f_const. rewrite IH.
    unfold grid. rewrite (inj_S k). unfold Qdiv. ring.
Qed.

(* уравнение главы: y' = 1, y(0) = 0 -- ломаная совпадает с y(t) = t во всех узлах *)
Corollary euler_traj_linear_exact : forall N k : nat,
  euler_traj f_const_one 0 N k == grid N k.
Proof.
  intros N k. change f_const_one with (f_const 1).
  rewrite euler_traj_const_exact. ring.
Qed.

Corollary euler_traj_linear_end : forall N : nat, (0 < N)%nat ->
  euler_traj f_const_one 0 N N == 1.
Proof. intros N HN. rewrite euler_traj_linear_exact. apply grid_NN. exact HN. Qed.
```

`Print Assumptions` трёх утверждений: Closed under the global context. Правая часть `y0 + a * grid N k` есть
значение $y_0 + a\,t_k$ в узле. После дополнения слова страницы верны без правки; в сноску 5 достаточно добавить
имя: «в общем виде — `euler_traj_const_exact`: $y_k = y_0 + a\,t_k$ для любой постоянной правой части $a$, любой
сетки и любого узла».

**(б) Поправить слова** (если формализацию не дополнять). Ход мысли сохраняется, меняется только указание на
опору. Два способа.

Первый — сослаться на уже доказанную общую лемму. Стр. 131–133 без изменений; в сноску 5 после слов
«правая часть постоянна» добавить:

> В общем виде (любая постоянная правая часть $c$, любой шаг $h$, любое число шагов $n$: $x_n = x_0 + n h c$)
> точность доказана для рекурсии `euler_steps` — `euler_constant_explicit` в `stdlib/ODE.v`; для `euler_traj`
> общая лемма не записана — проверены три узла.

Второй — сузить слова. Стр. 28–29:

> …для линейного уравнения метод *точен* в проверенных узлах сетки $N = 4$…

Стр. 131–133:

> Причина точности проста: наклон постоянен, касательная *совпадает* с графиком, и шаг по касательной не
> накапливает ошибки. Для уравнений без кривизны метод Эйлера не приближает, а *воспроизводит* решение (в
> формализации это проверено в трёх узлах сетки $N = 4$; общая теорема для `euler_traj` не записана).

Те же слова на стр. 54–56 и 221–222 стоят в E/R/R-чтении, которое страница сама называет осмыслением, а не
формальным утверждением (стр. 203–208); отдельной правки они не требуют.

## Расхождение 3. «Мера этого отставания на каждой конкретной сетке вычислена точно»: вычислена на одной сетке (стр. 142–143)

**Было:**

> (140–145) Существенно, что ошибка — *конечное рациональное число*, а не туманное «стремится к нулю». Метод
> недооценивает решение (выпуклая кривая обгоняет свои касательные), и мера этого отставания на каждой
> конкретной сетке вычислена точно. Уменьшение ошибки — это *измельчение сетки*, рост $N$: следующее
> направление процесса, а не достроенный предел.

**Проверка.** `src/analysis/PicardLindelof.v`:

```coq
Lemma euler_traj_quadratic_4 : euler_traj f_two_t 0 4 4 == 3 # 4.          (* :165 *)
Lemma euler_quadratic_error : 1 - euler_traj f_two_t 0 4 4 == 1 # 4.       (* :172 *)
```

Обе — Closed under the global context. Других утверждений о `f_two_t` в `src` нет (поиск по имени и по записи
правой части): ошибка вычислена на сетке $N = 4$ в одном узле $k = 4$. То, что глава говорит об этой сетке
(стр. 139–140, сноска 6), совпадает с леммами точно. Что ошибка уменьшается с ростом $N$, в формализации не
проверено ни на одной паре сеток (вторая сетка для этого уравнения не вычислялась).

**В чём расхождение.** Сказано «на каждой конкретной сетке вычислена»; вычислена на одной сетке в одном узле.

**(а) Довести формализацию до слов главы.** Возможно, без аксиом. Траектория имеет замкнутый вид
$y_k = t_k^2 - t_k h$, $h = 1/N$: отставание в узле равно $t_k h$, в момент $t = 1$ — шагу сетки $1/N$.
`Check.v`, раздел 2 (`f_two_t`, `grid_0` — из `PicardLindelof.v`; `inj_S`, `inj_pos`, `grid_NN` — как выше):

```coq
Theorem euler_traj_quadratic_closed : forall N k : nat,
  euler_traj f_two_t 0 N k ==
  grid N k * grid N k - grid N k * (1 / inject_Z (Z.of_nat N)).
Proof.
  intros N k. induction k as [|k IH].
  - cbn [euler_traj]. rewrite grid_0. ring.
  - cbn [euler_traj]. unfold euler_step, f_two_t. rewrite IH.
    unfold grid. rewrite (inj_S k). unfold Qdiv. ring.
Qed.

Corollary euler_quadratic_defect : forall N k : nat,
  grid N k * grid N k - euler_traj f_two_t 0 N k ==
  grid N k * (1 / inject_Z (Z.of_nat N)).
Proof. intros N k. rewrite euler_traj_quadratic_closed. ring. Qed.

(* в конечный момент t = 1 ошибка равна шагу сетки *)
Corollary euler_quadratic_error_general : forall N : nat, (0 < N)%nat ->
  1 - euler_traj f_two_t 0 N N == 1 / inject_Z (Z.of_nat N).
Proof.
  intros N HN. rewrite euler_traj_quadratic_closed, (grid_NN N HN). ring.
Qed.

(* метод недооценивает решение *)
Corollary euler_quadratic_underestimates : forall N : nat, (0 < N)%nat ->
  euler_traj f_two_t 0 N N < 1.
Proof.
  intros N HN. pose proof (euler_quadratic_error_general N HN) as He.
  pose proof (inj_pos N HN) as Hp.
  assert (Hq : 0 < 1 / inject_Z (Z.of_nat N)).
  { unfold Qdiv. rewrite Qmult_1_l. apply Qinv_lt_0_compat. exact Hp. }
  lra.
Qed.

(* измельчение сетки уменьшает ошибку *)
Corollary euler_quadratic_error_decreases : forall N : nat, (0 < N)%nat ->
  1 - euler_traj f_two_t 0 (S N) (S N) < 1 - euler_traj f_two_t 0 N N.
Proof.
  intros N HN.
  rewrite (euler_quadratic_error_general N HN).
  rewrite (euler_quadratic_error_general (S N)) by lia.
  rewrite (inj_S N). pose proof (inj_pos N HN) as Hp.
  set (n := inject_Z (Z.of_nat N)) in *.
  assert (Hd : 1 / n - 1 / (n + 1) == 1 / (n * (n + 1))) by (field; split; lra).
  assert (Hpos : 0 < 1 / (n * (n + 1))).
  { unfold Qdiv. rewrite Qmult_1_l. apply Qinv_lt_0_compat.
    apply Qmult_lt_0_compat; lra. }
  lra.
Qed.
```

Все пять — Closed under the global context. После дополнения слова страницы верны без правки; три следующие за
ними утверждения абзаца («недооценивает», «уменьшение ошибки — измельчение сетки») получают опору. В сноску 6
можно добавить: «в общем виде — `euler_traj_quadratic_closed` ($y_k = t_k^2 - t_k h$) и
`euler_quadratic_error_general` (в момент $t = 1$ ошибка равна $1/N$)».

**(б) Поправить слова** (если формализацию не дополнять). Стр. 142–143:

> Метод недооценивает решение (выпуклая кривая обгоняет свои касательные), и мера этого отставания на сетке
> $N = 4$ вычислена точно.

Слова стр. 222–223 («мера которой на каждой сетке вычислима») правки не требуют: там сказано «вычислима».

## Расхождение 4. Сноска 10: разметка ролей приведена не так, как в шапке файла (стр. 285)

**Было:**

> [^10]: Шапка `PicardLindelof.v` даёт разметку прямо: Elements — правая часть $f$, узлы сетки $t_k$, значения
> траектории $y_k$; Roles — шаг как приближение, траектория как процесс-решение; Rules —
> $y_{k+1} = y_k + h f(t_k,y_k)$.

**Проверка.** Шапка `src/analysis/PicardLindelof.v`, строки 6 и 10–15:

```
(*  Euler/Picard step on rational grid: y_{k+1} = y_k + h*f(t_k,y_k).       *)
…
(*  Elements: ODE rhs f, grid points t_k, trajectory values y_k             *)
(*  Roles:    f -> VectorField, y_k -> Approximation, h -> StepSize          *)
(*  Rules:    Euler recurrence (constitution), Lipschitz contraction (bound)  *)
(*                                                                           *)
(*  P4 connection: Euler trajectory IS a process (nat -> Q), convergence     *)
(*  of (1+1/N)^N to e is a process limit.                                    *)
```

Строка Elements пересказана точно. В строке Roles три роли: $f$ — векторное поле, $y_k$ — приближение, $h$ —
размер шага. На странице приближением назван шаг, а не значение $y_k$; поле $f$ пропущено; «траектория как
процесс» взята из строки «P4 connection», а не из Roles, и слова «решение» там нет. В строке Rules два правила:
рекуррентность Эйлера и «Lipschitz contraction (bound)»; на странице — только первое (формула взята из строки 6
шапки).

**В чём расхождение.** Сказано «даёт разметку прямо», а роли и правила приведены иначе, чем записаны в шапке.

**(а) Довести формализацию.** Теоремы здесь нет — речь о комментарии. Привести шапку к словам страницы значило
бы править существующий файл; предлагается поправить слова.

**(б) Поправить слова.**

> [^10]: Шапка `PicardLindelof.v` даёт разметку прямо: Elements — правая часть $f$, узлы сетки $t_k$, значения
> траектории $y_k$; Roles — $f$ как векторное поле, $y_k$ как приближение, $h$ как размер шага; Rules —
> рекуррентность Эйлера $y_{k+1} = y_k + h f(t_k,y_k)$ и липшицева оценка. Траектория как процесс (`nat -> Q`)
> названа там же, в строке о связи с P4.

Разбор ролей в самой главе (стр. 58–62, 227–232: роль-разрешение, роль-стадия, роль-приращение, роль-процесс,
роль-дефект, роль-предел) — чтение автора; он шире шапки и с ней не сверялся.

## Сомнительные места (расхождением не являются)

1. **Две рекурсии Эйлера для $y' = y$ (стр. 157–158, 181–185, сноски 7 и 9).** Глава работает с `euler_traj`
   (`PicardLindelof.v:36`), а тождество `exp1_is_euler` (`ProcessExpProcess.v:81`) говорит о локальной
   рекурсии того файла — `euler_yeqy h y0 M` (`:40`, шаг $y + h\,y$, без сетки и без аргумента $N$):
   `exp1_process N == euler_yeqy (1 / inject_Z (Z.of_nat (S N))) 1 (S N)`. По содержанию это траектория Эйлера
   уравнения $y' = y$ с шагом $1/(N{+}1)$ за $N{+}1$ шагов, слова страницы ему соответствуют. Но теоремы,
   связывающей `euler_yeqy` с `euler_traj`, в `src` нет: «та же лестница» подтверждена совпадением значений при
   $N = 1, 2$ (`euler_traj_exp_1` и `exp1_0`; `euler_traj_exp_2` и `exp1_1`); стадия $64/27$ есть только для
   `exp1_process`, стадия $625/256$ — только для `euler_traj`. Так же замкнутый вид «после $N$ шагов —
   $(1+1/N)^N$» (стр. 157–158) доказан для `euler_yeqy` (`euler_yeqy_closed`, `:71`), а для `euler_traj` — при
   $N = 1, 2, 4$; сноска 7 называет лемму об одном шаге. Связь доказана в `Check.v`, раздел 3
   (`euler_traj_exp_closed`, `euler_traj_is_euler_yeqy`, `exp1_is_euler_traj`; текст — в расхождении 1); с ней
   нижняя оценка `exp1_lower` переносится на траекторию главы (`euler_traj_exp_lower_all`).
2. **Граница стр. 185–187 («не доказаны») может быть снята.** На 18.11 слова страницы верны. Оба утверждения
   доказаны в пробном файле без аксиом (`exp1_upper`, `exp1_increasing`); при переносе в `src` фразу и сноску 9
   нужно переписать — текст дан в расхождении 1, пункт (а). Слова «(через бином)» тогда уходят: бином не
   понадобился.
3. **Сноска 1, «(`vm_compute` или `ring`)».** Цена и слова «точная рациональная арифметика» верны. Перечень
   тактик неполон: из трёх названных теорем `vm_compute` закрывает одну (`euler_traj_exp_4`), а
   `euler_traj_linear_4` и `euler_quadratic_error` закрыты тактикой `field`; `ring` закрывает
   `euler_step_concrete`, `euler_step_additive`, `euler_step_scaling`, `grid_0`; сравнения чисел — `lia`.
   Возможная замена: «(`vm_compute`, `field` или `ring`)».
4. **Сноска 8, `euler_traj_exp_lower` и `euler_traj_exp_converges`.** Обе леммы — сравнения двух чисел
   (`2 < 625 # 256`, `625 # 256 < 3`); траектория в их утверждения не входит, с ней их связывает
   `euler_traj_exp_4`, а в одном утверждении — `euler_exp_sandwich` (`:282`), которую глава не называет. Имя
   `euler_traj_exp_converges` говорит о сходимости, утверждение — об одной оценке; страница пересказывает
   утверждение верно и сходимости не заявляет.
5. **Стр. 166–167, «для показанных стадий проверены… оценки».** Двусторонняя оценка $2 < \cdot < 3$ в
   `PicardLindelof.v` есть для стадии $N = 4$; для $N = 1$ значение равно $2$, и нижняя оценка там нестрогая
   (`exp1_lower` — со знаком `<=`). Страница приводит пример именно для $625/256$.
6. **Стр. 268–272, отсылка к Главе 8.3.** `picard_op_contraction` (`ProcessPicardOperator.v:102`) — оценка
   $|\Phi(y)_k - \Phi(z)_k| \le (L\cdot T)\,D$ при липшицевости $f$, $h \ge 0$ и равномерной оценке $D$ на узлах
   $j \le N$; сжатием она становится при $L\cdot T < 1$. В этой фразе условие не названо, Глава 8.3 его называет
   (её стр. 146–154, 208). Сверка по существу — в ведомости Главы 8.3.
7. **«Совпадающие с решением», «точное значение — 1» (стр. 129–131, 139–140).** В леммах значения траектории
   сравниваются с числами ($1/4$, $1/2$, $1$; $1 - \ldots = 1/4$); функции-решения $y(t) = t$, $y(t) = t^2$ в
   файле не объявлены. В предлагаемых общих теоремах правая часть записана через узел сетки (`grid N k`,
   `grid N k * grid N k`), то есть как значение решения в узле.
8. **«Первые два глава ведёт как доказанные» (стр. 43–44).** Второй уровень назван «процессными чтениями»;
   чтение теоремой не является. В Rocq доказан первый уровень и сверх него два общих утверждения
   (`exp1_lower`, `exp1_is_euler`).
9. **Слово «сходимость» (стр. 178–179, сноска 4).** «Сходимость — это свойство процесса (монотонный рост,
   ограниченность сверху)» и «Сходимость $(1+1/N)^N \to e$ — это рост $N$ при $k = N$» — описание режима;
   теоремы о сходимости в названных файлах нет, и страница её не заявляет (стр. 33–37, 185–190). Монотонность
   и ограниченность сверху для всех $N$ на сегодня тоже не доказаны — страница это говорит.
10. **Стр. 116–118, «для линейного и квадратичного — продвигаем $k$ по фиксированной сетке $N = 4$».** Для
    линейного уравнения в файле три узла ($k = 1, 2, 4$), для квадратичного — один ($k = 4$).
11. **Сетка при $N = 0$ и узлы за концом интервала.** `grid 0 k` и шаг `1 / inject_Z (Z.of_nat 0)` над ℚ равны
    нулю, траектория при $N = 0$ постоянна (`Check.v`, `traj_N0_constant`); определение не ограничивает $k$
    числом $N$. Страница берёт $N \ge 1$ и $k = 0, 1, …, N$ (стр. 71–75) — оговорка стоит.
12. **«Система сформирована корректно… нет самоотнесения (P1)» (стр. 248–249).** Формального объекта `System`
    для этой конструкции нет, и проверки P1 в коде нет; страница говорит это сама (стр. 203–208: «содержательная
    интерпретация… а не приписывание коду новых формальных утверждений»).
13. **Одноимённые объявления.** `euler_step` объявлен в четырёх файлах: `PicardLindelof.v:33`;
    `process/ProcessODE.v:44` — с другим порядком аргументов (`f t y h`); два в `navier_stokes/`
    (`InvariantRegion.v:463`, `ResolutionRegularity.v:44`) — шаг для модальных состояний. `lipschitz_const` и
    `lipschitz_identity` объявлены ещё и в `analysis/FTC.v` (`:61`, `:73`). Глава всюду называет
    `PicardLindelof.v`; путаницы на странице нет.

## Вне главы (к исходникам, не к странице)

- **Комментарии `PicardLindelof.v` шире утверждений под ними.** «Theorem 8: … Euler gives y_k = k/N (exact for
  linear)» (`:138–139`) — под ним три частных значения; «Theorem 20: euler_linear_exact. Euler is exact for
  f(t,y)=a (constant): y_N = y0 + a» (`:318–319`) — под ним одна лемма `euler_linear_exact_2` для $a = 3$,
  $N = 2$; «Theorem 15: grid_bounds. 0 <= grid N k <= 1 when k <= N» (`:244–245`) — под ним лемма `grid_0`
  (`grid N 0 == 0`), оценок узла в файле нет; «Theorem 14: … scales identity-ODE trajectory» (`:232–233`) — под
  ним лемма об одном шаге.
- **Шапка `PicardLindelof.v`.** Заголовок «ODE Existence via Picard/Euler Iteration over Q», строка «Rules: …
  Lipschitz contraction (bound)» и слова «convergence of (1+1/N)^N to e is a process limit» не имеют под собой
  утверждений в файле: теоремы существования, сжатия или сходимости в нём нет. Лемма
  `picard_contraction_rate` (`:209`) выводит `0 < L * T /\ L * T < 1` из `0 < L`, `0 < T`, `L * T < 1`: второй
  член заключения совпадает с третьей посылкой. Глава VIII.2 на эту лемму не ссылается.
- **Имя `euler_traj_exp_converges`** (`:120`) при утверждении `625 # 256 < 3`.
- **`analysis/PeanoExistence.v`** (глава его не называет): `euler_linear_exact_any_N` (`:284`) при имени «any N»
  есть одно значение — `euler_pe (f_const_a 5) 2 3 3 == 7`; `euler_matches_Qpow` (`:270`) — одно значение при
  $N = 4$. Файл повторяет определения `PicardLindelof.v` под другими именами (`euler_pe`, `grid_pe`).
- **Три рекурсии Эйлера без связующих теорем:** `euler_traj` (`analysis/PicardLindelof.v`), `euler_yeqy`
  (`process/ProcessExpProcess.v`), `euler_steps` (`stdlib/ODE.v`); четвёртая — `euler_pe`
  (`analysis/PeanoExistence.v`), пятая — `euler_method` (`process/ProcessODE.v`). Связь первой со второй
  доказана в пробном файле (раздел 3).
- **Шапка `ProcessExpProcess.v`** (`:21–25`, «HONEST FRONTIER») на сегодня верна; при переносе в `src` теорем
  `exp1_upper` и `exp1_increasing` она устареет.
- Шапки `STATUS` обоих файлов (23 и 12 `Qed`) совпадают с действительным счётом.
