# Глава V.4 «Производная» — заметки к ведомости (12.11.2026)

Ведомость: `part05-ch04.json` — 105 ручных записей + 12 автоматических; `merge --dry` проходит без замечаний,
список «без сверки» пуст. Вердикты: ok — 105, mismatch-statement — 8 (три предмета: липшицевость — 5 мест,
`continuous_at` — 2 места, `derivative_is_process_construction` — 1), wrong-number — 3 (два числа),
missing-name — 1 (сокращённое имя).

По цене расхождений нет. `Print Assumptions` всех 53 утверждений трёх опорных файлов (`Differentiation.v` — 18,
`process/ProcessDerivative.v` — 17, `MeanValueTheorem.v` — 18) даёт `Closed under the global context`. Пять блоков
кода главы совпадают с исходниками.

Пробные файлы (компилируются против собранной копии, `src` не меняют):
`C:/Users/abary/tos-audit-build/_part05/ch04/Check1.v` (9 утверждений) и `Check2.v` (6 утверждений); у всех
пятнадцати `Print Assumptions` — `Closed under the global context`.

## Что проверить не удалось

Все утверждения главы о формализации проверены по исходнику и компилятору. Оговорки:

- английская страница и LaTeX-исходник главы не смотрелись;
- у `partial_sum_tail` вывода `Print Assumptions` нет по существу дела: объявление снято командой `Abort`,
  имени в окружении нет (глава именно это и сообщает);
- отсылки главы к § 5.1 (архимедовость как «топливо»), к Части I и к Главе 4.6 сверялись только там, где от них
  зависит утверждение о формализации: сверены две отсылки к § 5.3 (`continuous_at`, липшицевость) — обе дали
  расхождение (ниже).

## Расхождение 1. Липшицевость «из ограниченной производной» (стр. 276–278, 869–889, 934, 1023–1024)

**Было (стр. 869–874, 882–889):**

> ### Липшицевость из ограниченной производной
>
> Третье следствие — липшицевость. Лемма
> `bounded_deriv_lipschitz_local` даёт локальную оценку:
> вблизи точки $|f(x+h)-f(x)| \le (|L|+1)\cdot|h|$ — приращение
> функции пропорционально шагу с постоянным коэффициентом. […]
>
> Здесь стоит отметить, как замкнулся круг. В § 5.3 липшицевость
> вводилась *как условие* — конструктивная замена равномерной
> непрерывности, которую над $ℚ$ нельзя получить даром. Теперь
> липшицевость *выводится* — из ограниченной производной. […] То, что
> в главе о непрерывности приходилось требовать, глава о производной
> доказывает.

То же утверждение повторено на стр. 276–278 («липшицевость § 4.7.3 показывает, как Rules производной *порождают*
то, что в § 5.3 приходилось требовать»), в итоге на стр. 934 («монотонность с липшицевостью как дальнейшие
следствия») и на стр. 1023–1024 («её следствия — монотонность и липшицевость»).

**Проверка.** `bounded_deriv_lipschitz_local` (`src/MeanValueTheorem.v:633`):

```coq
Lemma bounded_deriv_lipschitz_local : forall (f : Q -> Q) (x L : Q),
  has_derivative f x L ->
  exists delta : Q, 0 < delta /\
  forall h : Q, 0 < Qabs h -> Qabs h < delta ->
    Qabs (f (x + h) - f x) <= (Qabs L + 1) * Qabs h.
```

`Print Assumptions`: `Closed under the global context`. Три обстоятельства:

1. посылка — производная в одной точке `x`; ограниченности производной на отрезке в утверждении нет (вопреки
   заголовку раздела и имени леммы);
2. лемма не следует из главной теоремы § 4.6.4: её доказательство — `step_upper_bound` при `eps = 1`
   (`MeanValueTheorem.v:640`), то есть прямо определение производной;
3. оценка отсчитывается от одной точки `x` при малых `h`. Условие § 5.3 иное — `Lipschitz_on f a b K`
   (`src/analysis/Continuity.v:55`, дословно то же в `analysis/HeineBorelComplete.v:72`):
   `K > 0 /\ forall x y, a <= x <= b -> a <= y <= b -> Qabs (f x - f y) <= K * Qabs (x - y)` — для всех пар
   точек отрезка.

Теоремы «равномерная дифференцируемость и ограниченная производная влекут `Lipschitz_on`» в `src` нет (поиск по
`udiff_on` и `Lipschitz_on`: в `analysis/FTC.v` лемма `udiff_approx_lipschitz` (:554) — та же сеточная оценка
между концами, что и главная теорема). Та же формула стоит в шапке `MeanValueTheorem.v` (стр. 10: «Lipschitz
condition from bounded derivative»).

**Одной фразой:** глава говорит, что условие Липшица из § 5.3 теперь выведено из ограниченной производной, а в
формализации выведена только оценка приращения от одной точки, без ограниченной производной и без пар точек.

**(а) Довести формализацию до слов главы — возможно, без аксиом; набросок проверен компилятором** (`Check2.v`).
Препятствие одно: конец сетки `Qeq`-равен `b`, но не совпадает с `b` как терм, а функция `f : Q -> Q` не обязана
уважать `Qeq`. Его снимает лемма: функция, непрерывная (в смысле `Differentiation.v`) в двух `Qeq`-равных точках,
принимает в них `Qeq`-равные значения — потому что к обеим точкам можно прибавить `Qeq`-равные малые шаги так,
что суммы совпадут лейбницево. После этого оценка главной теоремы переносится с конца сетки на точку `b`, а
поправка `eps` исчезает (она произвольна).

```coq
Lemma Qabs_pos_of_neq : forall q : Q, ~ q == 0 -> 0 < Qabs q.
Proof.
  intros q Hq.
  destruct (Qlt_le_dec q 0).
  - rewrite Qabs_neg; lra.
  - rewrite Qabs_pos; [| lra].
    destruct (Qlt_le_dec 0 q); [lra | exfalso; apply Hq; lra].
Qed.

(* Непрерывная в двух Qeq-равных точках функция принимает в них Qeq-равные значения. *)
Lemma continuous_at_qeq_values : forall (f : Q -> Q) (x x' : Q),
  x == x' -> continuous_at f x -> continuous_at f x' -> f x == f x'.
Proof.
  intros f x x' Hxx Hc Hc'.
  destruct (Qeq_dec (f x) (f x')) as [E | NE]; [exact E |].
  exfalso.
  assert (Hgap : 0 < Qabs (f x - f x')).
  { apply Qabs_pos_of_neq. intro Hz. apply NE. lra. }
  set (eps := Qabs (f x - f x') * (1#2)).
  assert (Heps : 0 < eps) by (unfold eps; lra).
  destruct (Hc eps Heps) as [d1 [Hd1 Hb1]].
  destruct (Hc' eps Heps) as [d2 [Hd2 Hb2]].
  set (d := Qmin d1 d2).
  assert (Hd : 0 < d).
  { unfold d. destruct (Q.min_spec d1 d2) as [[_ ->] | [_ ->]]; lra. }
  assert (Hdd1 : d <= d1) by (unfold d; apply Q.le_min_l).
  assert (Hdd2 : d <= d2) by (unfold d; apply Q.le_min_r).
  assert (Hk : exists k : positive, 1 # k < d).
  { destruct d as [dn dd]. unfold Qlt in Hd. simpl in Hd.
    exists (Pos.succ dd). unfold Qlt. simpl.
    rewrite Pos2Z.inj_succ. nia. }
  destruct Hk as [k Hk].
  destruct x as [p q]. destruct x' as [p' q'].
  unfold Qeq in Hxx. simpl in Hxx.
  set (h := Z.pos q' # (q' * k)).
  set (h' := Z.pos q # (q * k)).
  assert (Hh1 : h == 1 # k).
  { unfold h, Qeq. simpl. rewrite Pos2Z.inj_mul. ring. }
  assert (Hh1' : h' == 1 # k).
  { unfold h', Qeq. simpl. rewrite Pos2Z.inj_mul. ring. }
  assert (Hkpos : 0 < 1 # k) by reflexivity.
  assert (Ah : Qabs h == 1 # k).
  { qabs_rw Hh1. apply Qabs_pos. lra. }
  assert (Ah' : Qabs h' == 1 # k).
  { qabs_rw Hh1'. apply Qabs_pos. lra. }
  (* лейбницево равенство сдвинутых точек *)
  assert (Hleib : (p # q) + h = (p' # q') + h').
  { unfold h, h', Qplus. simpl.
    f_equal.
    - rewrite !Pos2Z.inj_mul. nia.
    - rewrite !Pos.mul_assoc. rewrite (Pos.mul_comm q q'). reflexivity. }
  assert (P1 : Qabs (f ((p # q) + h) - f (p # q)) < eps).
  { apply Hb1; rewrite Ah; lra. }
  assert (P2 : Qabs (f ((p' # q') + h') - f (p' # q')) < eps).
  { apply Hb2; rewrite Ah'; lra. }
  rewrite Hleib in P1.
  assert (Edec : f (p # q) - f (p' # q') ==
                 (f ((p' # q') + h') - f (p' # q')) + - (f ((p' # q') + h') - f (p # q))) by ring.
  assert (T := Qabs_triangle (f ((p' # q') + h') - f (p' # q'))
                             (- (f ((p' # q') + h') - f (p # q)))).
  rewrite Qabs_opp in T.
  assert (W := Qabs_wd _ _ Edec).
  unfold eps in *. lra.
Qed.

(* То же, что udiff_sub_interval в analysis/FTC.v:622. *)
Lemma udiff_on_sub : forall (f f' : Q -> Q) (a b c d : Q),
  udiff_on f f' a b -> a <= c -> c < d -> d <= b -> udiff_on f f' c d.
Proof.
  intros f f' a b c d [Hab Hu] Hac Hcd Hdb.
  split; [exact Hcd |].
  intros eps Heps. destruct (Hu eps Heps) as [delta [Hdelta Hbd]].
  exists delta. split; [exact Hdelta |].
  intros x h Hcx Hxd Hp Hl. apply Hbd; lra.
Qed.

(* Оценка приращения между КОНЦАМИ отрезка — без сетки и без eps. *)
Theorem bounded_deriv_increment_exact :
  forall (f f' : Q -> Q) (a b M : Q),
  udiff_on f f' a b ->
  (forall x : Q, a <= x -> x <= b -> Qabs (f' x) <= M) ->
  Qabs (f b - f a) <= M * (b - a).
Proof.
  intros f f' a b M Hu HM.
  assert (Hab : a < b) by (destruct Hu; assumption).
  destruct (Qlt_le_dec (M * (b - a)) (Qabs (f b - f a))) as [Hgt | Hle]; [| exact Hle].
  exfalso.
  set (gap := Qabs (f b - f a) - M * (b - a)).
  assert (Hgap : 0 < gap) by (unfold gap; lra).
  assert (Hba : 0 < b - a) by lra.
  set (eps := gap * (1#2) * / (b - a)).
  assert (Heps : 0 < eps).
  { unfold eps. apply Qmult_lt_0_compat; [lra | apply Qinv_lt_0_compat; exact Hba]. }
  destruct (bounded_deriv_bounded_increment f f' a b M eps Hu HM Heps) as [N HN].
  cbv zeta in HN.
  set (we := walk_point a ((b - a) / inject_Z (Z.of_nat (S N))) (S N)) in *.
  assert (Hwe : we == b) by (unfold we; apply walk_endpoint_qeq; exact Hab).
  assert (Hin : a <= we /\ we <= b).
  { unfold we. apply (walk_point_in_interval a b N (S N) Hab). apply Nat.le_refl. }
  destruct Hin as [Hlo Hhi].
  assert (Hcw : continuous_at f we) by (apply (udiff_continuous_at f f' a b we Hu); assumption).
  assert (Hcb : continuous_at f b) by (apply (udiff_continuous_at f f' a b b Hu); lra).
  assert (Hval : f we == f b) by (apply continuous_at_qeq_values; assumption).
  assert (Hrw : f b - f a == f we - f a) by lra.
  assert (W := Qabs_wd _ _ Hrw).
  assert (Hmul : (M + eps) * (b - a) == M * (b - a) + gap * (1#2)).
  { unfold eps. field. lra. }
  unfold gap in *. lra.
Qed.

(* Липшицевость на всём отрезке с константой M. *)
Theorem bounded_deriv_lipschitz :
  forall (f f' : Q -> Q) (a b M : Q),
  udiff_on f f' a b ->
  (forall x : Q, a <= x -> x <= b -> Qabs (f' x) <= M) ->
  forall x y : Q, a <= x -> x <= b -> a <= y -> y <= b ->
    Qabs (f y - f x) <= M * Qabs (y - x).
Proof.
  intros f f' a b M Hu HM x y Hax Hxb Hay Hyb.
  destruct (Qlt_le_dec x y) as [Hxy | Hyx].
  - assert (Hu' : udiff_on f f' x y) by (apply (udiff_on_sub f f' a b x y Hu); lra).
    assert (HM' : forall z : Q, x <= z -> z <= y -> Qabs (f' z) <= M).
    { intros z Hz1 Hz2. apply HM; lra. }
    assert (H := bounded_deriv_increment_exact f f' x y M Hu' HM').
    assert (A : Qabs (y - x) == y - x) by (apply Qabs_pos; lra).
    rewrite A. exact H.
  - destruct (Qlt_le_dec y x) as [Hlt | Hle].
    + assert (Hu' : udiff_on f f' y x) by (apply (udiff_on_sub f f' a b y x Hu); lra).
      assert (HM' : forall z : Q, y <= z -> z <= x -> Qabs (f' z) <= M).
      { intros z Hz1 Hz2. apply HM; lra. }
      assert (H := bounded_deriv_increment_exact f f' y x M Hu' HM').
      assert (A : Qabs (y - x) == x - y) by (rewrite Qabs_neg; lra).
      assert (E : f y - f x == - (f x - f y)) by ring.
      qabs_rw E. rewrite Qabs_opp. rewrite A. exact H.
    + assert (Hxy : x == y) by lra.
      assert (Hcx : continuous_at f x) by (apply (udiff_continuous_at f f' a b x Hu); assumption).
      assert (Hcy : continuous_at f y) by (apply (udiff_continuous_at f f' a b y Hu); assumption).
      assert (Hv : f x == f y) by (apply continuous_at_qeq_values; assumption).
      assert (E : f y - f x == 0) by lra.
      assert (E2 : y - x == 0) by lra.
      qabs_rw E. qabs_rw E2.
      assert (Z : Qabs 0 == 0) by reflexivity.
      rewrite Z. lra.
Qed.

(* В терминах канона § 5.3 (analysis/Continuity.v). *)
Corollary bounded_deriv_Lipschitz_on :
  forall (f f' : Q -> Q) (a b M : Q),
  0 < M ->
  udiff_on f f' a b ->
  (forall x : Q, a <= x -> x <= b -> Qabs (f' x) <= M) ->
  Continuity.Lipschitz_on f a b M.
Proof.
  intros f f' a b M HMpos Hu HM. split; [exact HMpos |].
  intros x y [Hax Hxb] [Hay Hyb].
  exact (bounded_deriv_lipschitz f f' a b M Hu HM y x Hay Hyb Hax Hxb).
Qed.
```

Заголовок файла: `From ToS Require Import CauchyReal Differentiation MeanValueTheorem.` и
`From ToS Require analysis.Continuity.` `Print Assumptions` у всех утверждений — `Closed under the global context`.
Место для них — конец `MeanValueTheorem.v` (или отдельный файл рядом; `analysis/Continuity.v` в самом
`MeanValueTheorem.v` импортировать не обязательно — следствие в терминах `Lipschitz_on` можно положить в
`analysis/Continuity.v` или в новый файл). Старую лемму `bounded_deriv_lipschitz_local` менять не нужно: вне своего
файла она не используется.

В том же пробном файле проверены ещё два следствия той же леммы — на случай, если автор захочет усилить § 4.7.1
и § 4.7.2 (расхождением нынешние слова там не являются, см. «Сомнительные места»):

```coq
Theorem zero_deriv_constant :
  forall (f f' : Q -> Q) (a b : Q),
  udiff_on f f' a b ->
  (forall x : Q, a <= x -> x <= b -> f' x == 0) ->
  forall x y : Q, a <= x -> x <= b -> a <= y -> y <= b -> f x == f y.

Theorem pos_deriv_strictly_increasing :
  forall (f f' : Q -> Q) (a b c : Q),
  udiff_on f f' a b ->
  (forall x : Q, a <= x -> x <= b -> c <= f' x) ->
  0 < c ->
  forall x y : Q, a <= x -> x < y -> y <= b -> f x < f y.
```

**(б) Поправить слова** (если формализацию не трогать).

Стр. 869–874, «стало»:

> ### Локальная оценка липшицева вида
>
> Третье следствие — оценка приращения в точке. Лемма
> `bounded_deriv_lipschitz_local` получает её прямо из определения
> производной: если $L$ — производная $f$ в точке $x$, то вблизи этой
> точки $|f(x+h)-f(x)| \le (|L|+1)\cdot|h|$ — приращение, отсчитанное от
> точки $x$, пропорционально шагу с постоянным коэффициентом.

Стр. 882–889, «стало»:

> Здесь стоит отметить, насколько замкнулся круг. В § 5.3 липшицевость
> вводилась *как условие* — оценка $|f(x)-f(y)|\le K|x-y|$ для всех пар
> точек отрезка, конструктивная замена равномерной непрерывности,
> которую над $ℚ$ нельзя получить даром. Глава о производной подводит к
> этому условию с двух сторон: точечной оценкой
> `bounded_deriv_lipschitz_local` (от одной точки, при малых шагах) и
> сеточной оценкой § 4.6.4 (между концами сетки, с поправкой
> $\varepsilon$). Само условие § 5.3 — оценка для всех пар точек
> отрезка — из ограниченной производной в опорных файлах ещё не
> выведено; это ближайший шаг формализации.

Стр. 276–278, «стало»: «А оценки § 4.7.3 показывают, как Rules производной подводят к тому, что в § 5.3
приходилось требовать для непрерывности.»

Стр. 934, «стало»: «`bounded_deriv_bounded_increment` — сеточное следствие теоремы о среднем — и дальнейшие
следствия: знак приращения при знакопостоянной производной и локальная оценка липшицева вида.»

Стр. 1023–1024, «стало»: «сеточная теорема о среднем и её следствия — знак приращения и локальная оценка
липшицева вида.»

Если выбран путь (а), слова главы остаются почти без изменений: в § 4.7.3 к локальной лемме добавляется фраза
«На всём отрезке то же даёт теорема `bounded_deriv_Lipschitz_on`: при равномерной дифференцируемости и
$|f'|\le M$ на $[a,b]$ функция липшицева с константой $M$ в смысле § 5.3».

## Расхождение 2. `continuous_at` главы — не определение § 5.3 (стр. 106–108, 424–426)

**Было (стр. 106–108):** «Тот же приём применялся к `continuous_at` в § 5.3; это сознательная деталь, не
недосмотр.»

**Было (стр. 422–426):** «…если функция дифференцируема в точке, то она в этой точке непрерывна. В
`Differentiation.v` это `deriv_implies_continuous`: из `has_derivative f x L` следует `continuous_at f x`, где
`continuous_at` — определение непрерывности из § 5.3.»

**Проверка.** В формализации два одноимённых определения.

- § 5.3 (стр. 114–120 той главы) приводит `continuous_at` из `src/stdlib/Topology.v:45`:
  `forall eps, 0 < eps -> exists delta, 0 < delta /\ forall y, Qabs (y - x) < delta -> Qabs (f y - f x) < eps` —
  по всем точкам `y` окрестности, без условия ненулевого шага.
- `deriv_implies_continuous` (`src/Differentiation.v:210`) заключает к местному определению
  `src/Differentiation.v:43`:
  `forall eps, 0 < eps -> exists delta, 0 < delta /\ forall h, 0 < Qabs h -> Qabs h < delta -> Qabs (f (x + h) - f x) < eps` —
  через приращение, в проколотой окрестности.

Моста между ними в `src` нет. Они не равносильны: из определения § 5.3 местное следует (проверено:
`topo_continuous_implies_punctured`), обратное неверно. Свидетель — функция, различающая записи одного числа:

```coq
Definition rep_fn (y : Q) : Q := match Qden y with xO _ => 0 | _ => 1 end.

Theorem derivative_does_not_give_topo_continuity :
  exists (f : Q -> Q) (x L : Q),
    has_derivative f x L /\ ~ Topology.continuous_at f x.
(* f := rep_fn, x := 2#2, L := 0;  Print Assumptions: Closed under the global context *)
```

(в точке `2#2` все значения `rep_fn ((2#2) + h)` равны `0`, а `rep_fn 1 = 1` при `1 == 2#2`).
`Print Assumptions deriv_implies_continuous`: `Closed under the global context`.

**Одной фразой:** глава называет непрерывность, к которой приходит теорема, определением § 5.3, а в формализации
это другое, более слабое определение из самого `Differentiation.v`; и приём «ненулевого шага» применён именно в
нём, а не в определении § 5.3.

**(а) Довести формализацию до слов главы.** В полной общности нельзя: контрпример выше машинно проверен. Честно
доводится при условии, что функция уважает `Qeq` (для функций, заданных арифметическими выражениями, оно
выполнено). Набросок проверен (`Check1.v`):

```coq
From ToS Require stdlib.Topology.

Lemma topo_continuous_implies_punctured : forall (f : Q -> Q) (x : Q),
  Topology.continuous_at f x -> continuous_at f x.
Proof.
  intros f x H eps Heps.
  destruct (H eps Heps) as [delta [Hd Hb]].
  exists delta. split; [exact Hd |].
  intros h _ Hh. apply Hb.
  assert (E : x + h - x == h) by ring.
  qabs_rw E. exact Hh.
Qed.

Theorem deriv_implies_topo_continuous : forall (f : Q -> Q) (x L : Q),
  (forall u v : Q, u == v -> f u == f v) ->
  has_derivative f x L -> Topology.continuous_at f x.
Proof.
  intros f x L Hresp Hd eps Heps.
  destruct (deriv_implies_continuous f x L Hd eps Heps) as [delta [Hdelta Hb]].
  exists delta. split; [exact Hdelta |].
  intros y Hy.
  destruct (Qeq_dec (y - x) 0) as [Hz | Hnz].
  - assert (Hyx : y == x) by lra.
    assert (E : f y - f x == 0) by (rewrite (Hresp y x Hyx); ring).
    qabs_rw E. rewrite Qabs_pos; lra.
  - assert (Hpos : 0 < Qabs (y - x)).
    { destruct (Qlt_le_dec (y - x) 0).
      - rewrite Qabs_neg; lra.
      - rewrite Qabs_pos; [| lra].
        destruct (Qlt_le_dec 0 (y - x)); [lra | exfalso; apply Hnz; lra]. }
    specialize (Hb (y - x) Hpos Hy).
    assert (Hxy : x + (y - x) == y) by ring.
    assert (E : f y - f x == f (x + (y - x)) - f x).
    { rewrite (Hresp (x + (y - x)) y Hxy). reflexivity. }
    qabs_rw E. exact Hb.
Qed.
```

С этими двумя утверждениями слова главы можно оставить, добавив условие: «для функции, уважающей `Qeq`,
`continuous_at` § 5.3 следует из производной (`deriv_implies_topo_continuous`)».

**(б) Поправить слова.**

Стр. 106–108, «стало»: «Тот же приём применён к местному определению `continuous_at` в `Differentiation.v`
(§ 4.3.1); это сознательная деталь, не недосмотр.»

Стр. 422–426, «стало»:

> …если функция дифференцируема в точке, то она в этой точке непрерывна. В
> `Differentiation.v` это `deriv_implies_continuous`: из
> `has_derivative f x L` следует `continuous_at f x`, где
> `continuous_at` — определение непрерывности через приращение,
> записанное в самом `Differentiation.v`: при $0<|h|<\delta$ имеем
> $|f(x+h)-f(x)|<\varepsilon$. Оно родственно определению § 5.3
> (`Topology.v`) и следует из него; обратный переход требует, чтобы
> функция уважала равенство `Qeq`, и в опорных файлах не записан.

Заодно на стр. 424–425 код `has_derivative f x L` разорван переносом строки внутри обратных кавычек — стоит
собрать на одной строке.

## Расхождение 3. `derivative_is_process_construction`: заключение верно без посылки (стр. 171–173)

**Было:** «`derivative_is_process_construction` (производная предъявляется как Коши-процесс, эквивалентный
постоянному $L$ — E/R/R-форма результата)».

**Проверка.** `src/process/ProcessDerivative.v:270`:

```coq
Theorem derivative_is_process_construction : forall f x L,
  has_derivative f x L ->
  exists proc : RealProcess,
    is_Cauchy proc /\
    process_equiv proc (const_process L).
```

`Print Assumptions`: `Closed under the global context`. В заключении нет ни `f`, ни `deriv_process`: существование
процесса Коши, эквивалентного постоянному `L`, верно для любого `L` — свидетелем служит сам `const_process L`.
Проверено (`Check1.v`):

```coq
Lemma construction_conclusion_free : forall L : Q,
  exists proc : RealProcess, is_Cauchy proc /\ process_equiv proc (const_process L).
Proof.
  intro L. exists (const_process L). split.
  - apply const_is_Cauchy.
  - apply process_equiv_refl.
Qed.
```

В доказательстве исходной теоремы свидетель — `deriv_process f x`, но утверждение этого не фиксирует.

**Одной фразой:** теорема названа предъявлением производной как процесса, а её формулировка о производной ничего
не сообщает — заключение выполнено и без условия дифференцируемости.

**(а) Довести формализацию до слов главы — возможно; набросок проверен** (`Check1.v`):

```coq
Theorem derivative_is_deriv_process : forall (f : Q -> Q) (x L : Q),
  has_derivative f x L ->
  is_Cauchy (deriv_process f x) /\
  process_equiv (deriv_process f x) (const_process L).
Proof.
  intros f x L H. split.
  - exact (deriv_process_cauchy f x L H).
  - exact (deriv_process_converges f x L H).
Qed.
```

Этой формулировкой можно заменить заключение `derivative_is_process_construction` (вне своего файла теорема не
используется) либо добавить её рядом.

**(б) Поправить слова.** «…и `derivative_is_process_construction` — запись того же в E/R/R-форме: существует
Коши-процесс, эквивалентный постоянному $L$ (в доказательстве это сам процесс разностных отношений; в
формулировке теоремы процесс не назван).»

Замечание вне главы: в `src/process/` одиннадцать теорем с тем же окончанием имени (`integral_…`, `ftc_…`,
`ivt_…`, `evt_…`, `series_…`, `taylor_…` и др.) — их формулировки стоит проверить на тот же случай в своих главах.

## Расхождение 4. Числа (стр. 200–201 и 969–970; стр. 517)

**4а. «16 Qed» в `ProcessDerivative.v`.** Было (стр. 200–201): «`ProcessDerivative.v` в шапке заявляет
« 0 axioms, 16 Qed »»; (стр. 969–970): «(`ProcessDerivative.v` — « 0 axioms, 16 Qed »)».

Проверка: шапка файла действительно называет 16 (`STATUS: 16 Qed, 0 Admitted, 0 axioms`, стр. 6 и 22);
действительный счёт — 17 (`grep -c 'Qed\.'`): `inject_Z_Sn_pos`, `deriv_step_pos`, `deriv_step_Qabs`,
`deriv_process_unfold`, `deriv_process_const`, `deriv_process_id`, `nat_above_Q`, `Qinv_le_compat_local`,
`deriv_step_vanishes`, `deriv_process_converges`, `deriv_process_cauchy`, `deriv_process_unique`,
`deriv_sum_process`, `deriv_scale_process`, `deriv_product_process`, `derivative_is_process_construction`,
`deriv_rate_valid`.

Одной фразой: страница повторяет устаревшее число шапки.

(а) Поправить шапку файла: `STATUS: 17 Qed, 0 Admitted, 0 axioms` (две строки комментария, стр. 6 и 22) — тогда
слова главы после замены числа останутся точной цитатой.
(б) «стало» (оба места): «« 0 axioms, 16 Qed » (действительный счёт — 17 `Qed`: шапка отстала на одну лемму)»;
после правки шапки — просто «« 0 axioms, 17 Qed »».

**4б. Длина доказательства `deriv_product`.** Было (стр. 516–518): «самое длинное доказательство файла
(`SECTION 4`, около ста пятидесяти строк)».

Проверка: `Proof.` на стр. 287, `Qed.` на стр. 487 файла — 201 строка (из них около 30 — комментарии). «Самое
длинное» верно: следующее по длине, `local_min_zero_deriv`, — 89 строк.

(а) Не требуется. (б) «стало»: «(`SECTION 4`, около двухсот строк)».

## Расхождение 5. Сокращённое имя `udiff` (стр. 259)

**Было:** «| равномерная дифференцируемость (`udiff`) | усиление для среднего | Rule |».

Проверка: объявления `udiff` в формализации нет (`Locate`: No object of basename udiff); определение называется
`udiff_on` (`src/MeanValueTheorem.v:46`), и в остальных местах главы стоит полное имя.

(а) Не требуется. (б) «стало»: «| равномерная дифференцируемость (`udiff_on`) | усиление для среднего | Rule |».

## Мелочи (вердикт ok, в ведомости отмечены в пометках)

- Стр. 351–353: «Эти два правила — `deriv_const` и `deriv_id` — послужат базой индукции в § 4.4.3». В
  доказательстве `deriv_power_succ` (`Differentiation.v:493–518`) база — одна `deriv_id`; `deriv_const` там не
  применяется, и § 4.4.3 главы называет базой именно `deriv_id`. Предложение: «Второе из них, `deriv_id`,
  послужит базой индукции в § 4.4.3, где из него и правила произведения вырастет степенное правило.»
- Стр. 165–167: «лемма `deriv_step_vanishes` находит уровень $N$, начиная с которого $h_n<\delta$». Лемма даёт
  один уровень (`exists N, deriv_step N < delta`); что неравенство держится при всех `n >= N`, устанавливается
  внутри доказательства моста. Предложение: «…находит уровень $N$ с $h_N<\delta$, а шаг дальше только убывает».
- Стр. 716: `argmax` в обратных кавычках — слово-понятие; объявления с таким именем нет (в `EVT_idx.v` —
  `argmax_idx`, `argmax_on_grid`, `argmax_process`). Можно снять кавычки или написать `argmax_idx`.
- Стр. 994–995: код `Print Assumptions` разорван переносом строки внутри обратных кавычек (как и на
  стр. 424–425).

## Сомнительные места (расхождением не являются)

1. **Квантор по сетке в главной теореме (стр. 796–805, 830–837, 857–861).** В Rocq: для всякого `eps > 0`
   *существует* число делений `N` (зависящее от `eps`), при котором оценка верна для конца именно этой сетки.
   На странице «конец сетки» стоит без квантора; читается и как «любой сетки». Слова «сеточный результат»
   это отчасти покрывают. Уточнение одной вставкой: «…найдётся число делений $N$, при котором полное приращение
   от $a$ до конца сетки оценивается так».
2. **«Монотонность» (заголовок § 4.7.2, стр. 934, 1023).** `pos_deriv_increases` и `neg_deriv_decreases`
   утверждают знак приращения между `a` и концом сетки — для одной пары точек; текст § 4.7.2 описывает это точно,
   слово «монотонность» в заголовках шире доказанного. Монотонность по всем парам точек доказуема
   (`pos_deriv_strictly_increasing`, `Check2.v`).
3. **«Почти постоянство» (стр. 842–852).** Статус назван честно: полная форма «не доказывается». Она доказуема
   без аксиом и без «дополнительных мостов», кроме одной леммы (`zero_deriv_constant`, `Check2.v`, — следствие
   теоремы из Расхождения 1а). Если формализацию дополнят, абзац можно заменить утверждением о постоянстве.
4. **`mvt_quadratic_midpoint` (стр. 897–907).** Формула страницы совпадает с леммой, но лемма — алгебраическое
   тождество, доказанное одним `ring`; функции, производной и условия «середина внутри отрезка» в ней нет.
   Глава для `gradient_step_uses_derivative` такую оговорку делает (стр. 683–692), здесь — нет. Единое
   утверждение проверено (`Check1.v`): `mvt_quadratic_exact : a < b -> exists c, a < c /\ c < b /\
   has_derivative (fun w => w * w) c (2 * c) /\ 2 * c * (b - a) == b * b - a * a`. Вариант слов: добавить
   «(сама лемма — алгебраическое тождество; связь с производной квадрата даёт `deriv_square`)».
5. **Цена названа отсылкой, а не результатом (стр. 200–204, 661–665, 914–916, 978–995).** Глава несколько раз
   говорит, что статус теоремы даёт только `Print Assumptions`, и ни разу не сообщает вывод. Вывод получен: у всех 53 утверждений
   трёх файлов — `Closed under the global context`. Готовая фраза для конца § 4.8.3: «Проверка выполнена для
   всех утверждений трёх опорных файлов (18, 17 и 18): каждое замкнуто в глобальном контексте — ни `classic`, ни
   `L4_witness` главе о производной не понадобились.»
6. **Путь классического слоя (стр. 970–975).** Импорты названы верно. Уточнения: `MonotoneConvergence.v` аксиому
   не объявляет, а получает `classic` из стандартной библиотеки через `ToS_Axioms`; у `ProcessDerivative.v` есть
   и прямой путь — `ProcessArithmetic.v` импортирует `Classical`.
7. **«Полная теория содержится в `GradientDescent.v`» (стр. 947).** Файл посвящён одной модели — квадратичной
   потере с множителем сжатия `1 - 2 * eta`; «полная» верно в этих пределах. Вариант: «теория для квадратичной
   потери содержится в `GradientDescent.v`».
8. **`gd_weight` (стр. 669–692).** Определён через сжатие ошибки (`wstar + gd_error …`), не через производную;
   лемма сверяет только первый шаг и `has_derivative` не упоминает. Глава это называет сама; расхождения нет.
9. **Нулевой шаг (стр. 98–104).** «При $h=0$ оценка обращается в $0<0$ слева и истинна тривиально» — верно для
   импликации с условием `0 < Qabs h`. Стоит иметь в виду, что без этого условия критерий невыполним ни для какой
   функции (при `h == 0` правая часть равна нулю, а неравенство строгое) — проверено:
   `criterion_without_puncture_unsatisfiable`, `Check1.v`. То есть условие ненулевого шага не только
   содержательно, но и необходимо для непустоты определения.
10. **Вне главы: `deriv_convergence_rate` (`ProcessDerivative.v:288`).** Число `1 # 2`, вписанное руками, с
    комментарием «Convergence rate: h_n = 1/(n+1) -> 0» и леммой `deriv_rate_valid` (`0 < 1/2 < 1`); со скоростью
    убывания шага оно не связано. Глава его не называет; это семнадцатый `Qed` файла.
11. **Вне главы: шапка `MeanValueTheorem.v`** (стр. 10) говорит «Lipschitz condition from bounded derivative» —
    источник формулировки Расхождения 1.

## Дополнительные проверки

- Пример `|x|` (стр. 190–192, 464–479): глава подаёт его как интуицию без Rocq-теоремы — верно, в `src` его нет.
  Оба утверждения проверены компилятором без аксиом (`Check1.v`):
  `abs_right_quotients : process_equiv (deriv_process Qabs 0) (const_process 1)` и
  `abs_no_derivative_at_0 : forall L, ~ has_derivative Qabs 0 L`. При желании пример можно сделать теоремой.
- Ход доказательств, пересказанный в главе, сверен с исходниками и совпадает: `deriv_sum` (`eps/2`),
  `deriv_sub` (через `deriv_neg`, `deriv_sum` и экстенсиональные леммы), `deriv_implies_continuous`
  (`min(delta_d, eps/(|L|+1))`), `continuous_bounded_near` (`M = |f x| + 1`), `deriv_square` (`delta = eps`),
  `deriv_product` (три слагаемых по `eps/3`), `deriv_power_succ` (индукция), `deriv_unique` (`eps = |L − L'|/4`),
  `local_min_zero_deriv` (`eps = |L|/2`, знак шага), `gradient_step_uses_derivative` (`unfold …; ring`),
  `bounded_deriv_bounded_increment` (индукция с `eps/2`), `walk_step_small` (через `Archimedean_nat`),
  `udiff_continuous_at` (через `udiff_pointwise`).
- «Честные факты из глубины цепи» (стр. 997–1006) подтверждены: `Abort` в `SeriesConvergence.v:320`, `Restart` в
  `MonotoneConvergence.v:306`.
- Сверка 12.11 (`sverka-2026-11-12`) главу V.4 не затрагивала; слова о цене в ней прежде не правились.
