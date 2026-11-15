// Часть VI, шаг 3, страницы (2026-11-15, слово автора «Делай»): 7 правок глав VI.3 и VI.5 внесены
// (VI.3: абзац о совпадении Лебега с Риманом, сноски 1, 2, 4, 5, 7; VI.5: сноска 2).
// Формализация — новый src/process/ProcessL1Integrable.v; прежние файлы не менялись.
// Запуск: node patch-p06-step-03-pages.cjs  (затем relocate + merge по part06-ch03, part06-ch05). Скрипт повторяем.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 15.11 (Часть VI, шаг 3, слово автора)';
const BYF = DONE + ' (формализацией; текст страницы не менялся)';
const CL = 'Closed under the global context';
const L1I = 'src/process/ProcessL1Integrable.v';
const SIV = 'src/analysis/StepIntegral.v';
const L1S = 'src/analysis/L1Space.v';
const BS = String.fromCharCode(92);
const AND = '/' + BS;
const norm = (s) => (s || '').replace(/\s+/g, ' ').trim();

function open(name) {
  const p = path.join(__dirname, name + '.json');
  const j = JSON.parse(fs.readFileSync(p, 'utf8'));
  let n = 0, added = 0, noted = 0;
  const pick = (prefix, th) => {
    const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix) && (th === undefined || (th === null ? !r.theorem : r.theorem === th)));
    if (hit.length > 1) throw new Error(name + ': не одна запись: ' + prefix + ' / ' + th);
    return hit[0];
  };
  const fix = (prefix, th, fields) => { const r = pick(prefix, th); if (!r) return; Object.assign(r, { verdict: 'ok' }, fields); n++; };
  const note = (prefix, th, text) => {
    const r = pick(prefix, th);
    if (!r) throw new Error(name + ': запись для примечания не найдена: ' + prefix + ' / ' + th);
    if (r.note !== text) { r.note = text; noted++; }
  };
  const add = (rec) => {
    if (j.records.some((r) => (r.theorem || null) === (rec.theorem || null) && norm(r.claim) === norm(rec.claim))) return;
    j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); added++;
  };
  const save = () => { fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n'); console.log(name + '.json: изменено ' + n + ', примечаний ' + noted + ', добавлено ' + added + ', всего ' + j.records.length); };
  return { j, fix, note, add, save };
}

// утверждения нового файла (номера строк — src/process/ProcessL1Integrable.v)
const N_EVAL = 'Fixpoint step_eval (f : SI.StepFun) (x : Q) : Q (:99) — значение в точке x функции, записанной списком f: сумма step_val s * indicator (step_left s) (step_right s) x по ступеням; склейка списков — поточечная сумма (step_eval_app, :143).';
const N_SCALE = 'step_fun_integral_scale : forall c f, SI.step_fun_integral (SI.step_fun_scale c f) == c * SI.step_fun_integral f (:312) — для списка ступеней. ' + CL + '.';
const N_MONO = 'step_integral_monotone : forall f g : SI.StepFun, (forall x, step_eval f x <= step_eval g x) -> SI.step_fun_integral f <= SI.step_fun_integral g (:350) — сравнение значений во всех рациональных точках; условий на разбиения нет. Доказательство: оба списка лежат в некотором отрезке (inside_exists, :185), на достаточно мелкой сетке суммы Римана близки к ступенчатым интегралам (step_riemann_equiv, :266) и сравнимы (riemann_process_monotone). ' + N_EVAL + ' ' + CL + '.';
const N_DEP = 'step_integral_depends_on_function : forall f g : SI.StepFun, (forall x, step_eval f x == step_eval g x) -> SI.step_fun_integral f == SI.step_fun_integral g (:362). ' + CL + '.';
const N_RIEM = 'step_riemann_equiv : forall f a b, a < b -> inside a b f -> riemann_process (step_eval f) a b ~~ const_process (SI.step_fun_integral f) (:266); оценка стадии — step_eval_riemann_close (:220): отклонение не больше (сумма |v_i|) * integral_step a b n; оценка одной ступени — measure_process_rate (process/ProcessMeasureIntervals.v). ' + CL + '.';
const N_AGREE = 'lebesgue_step_agrees : forall a b f (Hf : inside a b f), a < b -> PL.lebesgue_process (step_eval f) a b ~~ on_integral (step_to_l1_on a b f Hf) (:608); то же для вложения step_to_l1 файла L1Space.v — lebesgue_step_agrees_l1space (:963). ' + CL + '.';
const N_CLOSE = 'Definition l1_close (a b : Q) (f g : SI.StepFun) (eps : Q) : Prop := exists h : SI.StepFun, inside a b h ' + AND + ' (forall x, step_eval h x == step_eval f x - step_eval g x) ' + AND + ' SI.step_fun_norm h < eps (:450). Близость влечёт близость интегралов без условий на разбиения — l1_close_integral (:458); рефлексивность, симметрия, сложение оценок — l1_close_refl, l1_close_sym, l1_close_trans (:474, :481, :490). ' + CL + '.';
const N_L1ON = 'Record L1On (a b : Q) (:521): on_seq : nat -> SI.StepFun; on_inside : forall n, inside a b (on_seq n); on_cauchy : forall eps, 0 < eps -> exists N, forall m n, N <= m -> N <= n -> l1_close a b (on_seq m) (on_seq n) eps. ' + N_CLOSE;
const N_ONINT = 'Definition on_integral {a b : Q} (F : L1On a b) : RealProcess := fun n => SI.step_fun_integral (on_seq F n) (:534).';
const N_CAUCHY = 'l1_on_integral_is_Cauchy : forall a b (F : L1On a b), a < b -> is_Cauchy (on_integral F) (:538). ' + CL + '.';
const N_EQV = 'Definition l1_on_equiv {a b : Q} (F G : L1On a b) : Prop := forall eps, 0 < eps -> exists N, forall n, N <= n -> l1_close a b (on_seq F n) (on_seq G n) eps (:549).';
const N_EQUIV = 'l1_on_equiv_equivalence : forall a b, (forall F : L1On a b, l1_on_equiv F F) ' + AND + ' (forall F G, l1_on_equiv F G -> l1_on_equiv G F) ' + AND + ' (forall F G K, l1_on_equiv F G -> l1_on_equiv G K -> l1_on_equiv F K) (:554). ' + CL + '.';
const N_EQINT = 'l1_on_equiv_integral : forall a b (F G : L1On a b), a < b -> l1_on_equiv F G -> on_integral F ~~ on_integral G (:576). ' + CL + '.';
const N_EMB = 'Definition step_to_l1_on (a b : Q) (f : SI.StepFun) (Hf : inside a b f) : L1On a b (:586, Defined) — постоянная последовательность; on_integral (step_to_l1_on a b f Hf) n = SI.step_fun_integral f (step_to_l1_on_integral, :592); списки, записывающие одну функцию, вкладываются в один класс (step_to_l1_on_ext, :597).';
const N_SERIES = 'Definition series_l1 (a b : Q) (s : nat -> SI.Step) (Hin : forall k, a <= SI.step_left (s k) ' + AND + ' SI.step_right (s k) <= b) (Hsum : summable s) : L1On a b (:769, Defined): стадии — первые n ступеней (prefix, :723); summable s (:763): для всякого eps > 0 норма списка ступеней с номерами от n до n + d меньше eps при всех достаточно больших n и всех d.';
const N_STAIR = 'Definition staircase : L1On 0 1 := series_l1 0 1 stair_step stair_inside stair_summable (:842); stair_step k — ступень высоты (1/2)^k на [0, (1/2)^k] (:796); суммируемость — stair_summable (:830) через оценку хвоста stair_tail_bound (:814).';
const N_BEYOND = 'staircase_beyond_every_stage : forall n, ~ l1_on_equiv staircase (step_to_l1_on 0 1 (prefix stair_step n) (inside_prefix 0 1 stair_step stair_inside n)) (:872). Не доказано: что лестница не эквивалентна никакой ступенчатой функции вообще. ' + CL + '.';
const N_POINT = 'point_differs_but_equivalent : forall a b c (Hcc : c <= c) (Ha : a <= c) (Hb : c <= b), l1_on_equiv (step_to_l1_on a b [SI.mkStep 1 c c Hcc] (inside_point a b c Hcc Ha Hb)) (zero_on a b) ' + AND + ' step_eval [SI.mkStep 1 c c Hcc] c == 1 ' + AND + ' step_eval [] c == 0 (:699). ' + CL + '.';
const N_ONE = 'one_not_equiv_zero : ~ l1_on_equiv (step_to_l1_on 0 1 (const_step 1) (inside_const_step 1)) (zero_on 0 1) (:677), где const_step v — постоянная v на [0, 1] (:622). ' + CL + '.';
const N_SAME = 'l1_close_same_function : forall a b f g eps, 0 < eps -> (forall x, step_eval f x == step_eval g x) -> l1_close a b f g eps (:507) — два списка, записывающие одну функцию точки, близки с любой оценкой; интеграл зависит только от функции — step_integral_depends_on_function (:362). ' + CL + '.';
const N_ALIGNED = 'l1_integral_cauchy_aligned : forall f : L1.L1Process, l1_aligned f -> is_Cauchy (L1.l1_integral_approx f) (:1008), где l1_aligned f := forall m n, L1_aligned (L1.l1_seq f m) (L1.l1_seq f n) (:1004) — все стадии записаны на одном разбиении. На общем разбиении отношение — эквивалентность, сохраняющая интеграл: l1_equiv_al_equivalence (:1092), l1_equiv_al_integral (:1117). ' + CL + '.';
const N_UNB = 'l1_process_integral_unbounded : exists f : L1.L1Process, (forall M : nat, inject_Z (Z.of_nat M) <= L1.l1_integral_approx f M) ' + AND + ' ~ is_Cauchy (L1.l1_integral_approx f) (:1162) — ступень высоты 1 на [0, n]; l1_equiv_not_transitive (:1184) — отношение l1_equiv без общего разбиения не транзитивно. ' + CL + '.';
const N_OLD = 'Record L1Process (analysis/L1Space.v:86): условие Коши записано через step_fun_norm (step_fun_diff (l1_seq m) (l1_seq n)); step_fun_diff (:54) вычитает значения ступеней с одинаковыми номерами, концы берёт у первого списка, длинный список обрезает.';

// ------------------------------------------------------------------ VI.3
{
  const { fix, note, add, save } = open('part06-ch03');
  const P34 = '*доказано без аксиом* — ступенчатый интеграл и его свойства, интеграл-процесс на ограниченных функциях,';
  const P198 = 'Доказанная часть — ступенчатый интеграл и его свойства, интеграл Лебега как процесс,';

  // --- основной текст, не менялся (места 3.3, 3.4)
  fix(P34, 'l1_integral_approx', { theorem: 'l1_on_integral_is_Cauchy', file: L1I,
    note: BYF + ': было — «L¹-интеграл как предел» опирался на определение l1_integral_approx типа L1Process, для которого последовательность интегралов не обязана быть последовательностью Коши. ' + N_CAUCHY + ' Тип — L1On (:521).' });
  fix(P34, 'l1_equiv', { theorem: 'l1_on_equiv_equivalence', file: L1I,
    note: BYF + ': было — о l1_equiv доказана одна рефлексивность. ' + N_EQUIV + ' ' + N_EQINT });
  fix('*Интегрируемая функция* — это Коши-последовательность ступенчатых функций по норме', 'L1Process', { theorem: 'L1On', file: L1I,
    note: BYF + ', сноска 4 переписана: было — тип L1Process с разностью по месту в списке. ' + N_L1ON });
  fix('Её интеграл — предел интегралов приближающих ступенчатых функций; он определён как процесс и доказуемо устойчив.', 'l1_integral_approx', { theorem: 'l1_on_integral_is_Cauchy', file: L1I,
    note: BYF + ', сноска 5 переписана: было — устойчивость доказана только для постоянных последовательностей, для типа L1Process неверна. ' + N_ONINT + ' ' + N_CAUCHY + ' Независимость от представителя — ' + N_EQINT });
  fix('*Пополнение встроено в самый тип: L¹-объект уже является Коши-процессом ступенчатых функций,', 'L1Process', { theorem: 'L1On', file: L1I,
    note: 'Условие Коши — поле on_cauchy записи L1On (:521); теоремы о полноте (о пределе последовательности интегрируемых функций) нет, и страница говорит это сама. Представители, не сводящиеся к своим стадиям, строятся напрямую: ' + N_SERIES + ' ' + N_STAIR });
  fix('две L¹-функции эквивалентны, если интеграл модуля их разности сходится к нулю', 'l1_equiv', { theorem: 'l1_on_equiv', file: L1I,
    note: N_EQV + ' Формула страницы; близость l1_close — запись к сноске 4. О свойствах отношения — запись к стр. 148.' });
  fix('Как и в Главе 4.3, формально заданы *представители* (тип L¹-процессов) и *отношение* эквивалентности', 'l1_equiv', { theorem: 'l1_on_equiv_equivalence', file: L1I,
    note: BYF + ', сноска 7 переписана: было — отношением эквивалентности l1_equiv не доказано, а на типе L1Process оно не транзитивно. ' + N_EQUIV + ' Что фактор-тип не строится — верно.' });
  fix(P198, 'l1_integral_approx', { theorem: 'l1_on_integral_is_Cauchy', file: L1I,
    note: BYF + ': «L¹-интеграл как предел» — ' + N_CAUCHY });
  fix(P198, 'l1_equiv', { theorem: 'l1_on_equiv_equivalence', file: L1I,
    note: BYF + ': «его классы» — ' + N_EQUIV + ' ' + N_EQINT });

  // --- место 3.1: основной текст не менялся
  const P67 = '*однородность* (вынос постоянного множителя) и *монотонность* (если одна ступенчатая функция всюду не больше другой,';
  fix(P67, 'integral_scale', { theorem: 'step_fun_integral_scale', file: L1I,
    note: BYF + ', сноска 2 переписана: было — integral_scale (StepIntegral.v:136) об одной ступени. ' + N_SCALE });
  fix(P67, 'integral_monotone_step', { theorem: 'step_integral_monotone', file: L1I,
    note: BYF + ', сноска 2 переписана: было — integral_monotone_step (StepIntegral.v:145) о двух ступенях с равными концами; значение функции в точке не было определено. ' + N_MONO });
  note('Здесь нет ни аксиом, ни предельных переходов — только конечная рациональная арифметика.', null,
    'В StepIntegral.v нет строк Axiom, Parameter, Admitted; подключена только стандартная библиотека; пределов и последовательностей в утверждениях нет. Монотонность для списков (step_integral_monotone, ' + L1I + ':350) — утверждение конечное и без аксиом; доказана она сравнением двух конечных сумм на одной достаточно мелкой сетке, а не общим измельчением разбиений; способ назван в сноске 2.');
  note('В основании — интеграл ступенчатой функции (точная сумма $' + BS + 'sum v_i w_i$) и его свойства', null,
    'Перечень свойств без уточнения. Аддитивность — integral_app (StepIntegral.v:127), для списков; однородность и монотонность для списков — step_fun_integral_scale (:312) и step_integral_monotone (:350) файла ' + L1I + ' (шаг 3, 15.11); для одной ступени — integral_scale, integral_monotone_step (StepIntegral.v).');

  // --- правка 1: место 3.2
  const C90 = 'Совпадение же Лебега с Риманом на ступенчатом уровне доказано точно: процесс Римана ступенчатой функции сходится к её ступенчатому интегралу (`step_riemann_equiv`), а значит, называет ту же точку, что и L¹-интеграл её вложения (`lebesgue_step_agrees`); для более широкого класса «хороших» функций оно остаётся ожидаемой следующей теоремой, а не опорным результатом этой главы.';
  fix('Совпадение же Лебега с Риманом на ступенчатом уровне доказано точно (вложение `step_to_l1`)', 'step_to_l1', {
    theorem: 'step_riemann_equiv', file: L1I, claim: C90,
    note: DONE + ': было «доказано точно (вложение `step_to_l1`)» — интеграла Римана в L1Space.v нет, связи ступенчатого интеграла с суммами Римана не было. ' + N_RIEM });
  add({ theorem: 'lebesgue_step_agrees', file: L1I, claim: C90, note: N_AGREE });

  // --- правка 2: сноска 1, число (место 3.6)
  const P1 = 'Тип ступенчатой функции и `step_integral` (площадь одной ступени), `step_fun_integral` (сумма) в `StepIntegral.v`';
  const C1 = 'Тип ступенчатой функции и `step_integral` (площадь одной ступени), `step_fun_integral` (сумма) в `StepIntegral.v` (каталог `src/analysis/`, 17 доказанных утверждений, 0 `Admitted`, 0 аксиом).';
  fix(P1, 'step_integral', { claim: C1 });
  fix(P1, 'step_fun_integral', { claim: C1 });
  fix(P1, 'Admitted', { claim: C1 });
  fix(P1, null, { claim: C1,
    note: DONE + ': было «20 доказанных утверждений». В файле 17 строк Qed (grep -c \'Qed' + BS + '.\'); шапка файла исправлена с 20 на 17 12.11.2026 (коммит 2ae17c2). «0 Admitted, 0 аксиом» верно: строк Admitted, Axiom, Parameter нет.' });

  // --- правка 3: сноска 2 (место 3.1)
  const P2 = '`integral_app` (аддитивность по конкатенации)';
  const C2a = '`integral_app` (аддитивность по конкатенации) в `StepIntegral.v`; там же для одной ступени — `integral_scale`, `integral_monotone_step`, `step_integral_nonneg`.';
  fix(P2, 'integral_app', { claim: C2a });
  fix(P2, 'integral_scale', { claim: C2a,
    note: 'Объявление есть (StepIntegral.v:136), файл назван верно. Утверждение — об одной ступени; сноска так и говорит (исправлено 15.11, шаг 3).' });
  fix(P2, 'integral_monotone_step', { claim: C2a,
    note: 'Объявление есть (StepIntegral.v:145), файл назван верно. Утверждение — о двух ступенях с равными концами; сноска называет её леммой об одной ступени (исправлено 15.11, шаг 3).' });
  fix(P2, 'step_integral_nonneg', { claim: C2a });
  add({ theorem: 'step_fun_integral_scale', file: L1I,
    claim: 'Для списков ступеней (файл `ProcessL1Integrable.v`, каталог `src/process/`): однородность — `step_fun_integral_scale`;',
    note: DONE + ' (добавлено): ' + N_SCALE });
  add({ theorem: 'step_integral_monotone', file: L1I,
    claim: 'монотонность — `step_integral_monotone`: если значение одной ступенчатой функции в каждой точке не больше значения другой, то и интеграл не больше, какими бы разбиениями они ни были записаны (доказано сравнением сумм на одной достаточно мелкой сетке).',
    note: DONE + ' (добавлено): ' + N_MONO });
  add({ theorem: 'step_integral_depends_on_function', file: L1I,
    claim: 'Следствие — интеграл зависит только от функции, а не от списка ступеней, которым она записана (`step_integral_depends_on_function`).',
    note: N_DEP });

  // --- правка 4: сноска 4 (место 3.3)
  const C4a = 'Тип `L1On` (файл `ProcessL1Integrable.v`, каталог `src/process/`, 0 аксиом): последовательность ступенчатых функций на отрезке, у которой разность двух далёких стадий — как функция точки — записывается списком ступеней сколь угодно малой нормы (`l1_close`; норма — `step_fun_norm` из `StepIntegral.v`).';
  const C4b = 'Такая близость не зависит от того, какими разбиениями записаны стадии.';
  const C4c = 'Прежний тип `L1Process` (`L1Space.v`, каталог `src/analysis/`, 16 доказанных утверждений, 0 `Admitted`, 0 аксиом) вычитает ступени по месту в списке;';
  const C4d = 'сказанное в этом разделе верно для него, когда все стадии записаны на общем разбиении (`l1_integral_cauchy_aligned`), а без этого условия — нет (`l1_process_integral_unbounded`).';
  const P4 = 'Тип `L1Process` и норма `step_fun_norm` в `L1Space.v`';
  fix(P4, 'step_fun_norm', { file: SIV, claim: C4a, page_price: '0 аксиом',
    note: 'Definition step_fun_norm (f : StepFun) : Q := step_fun_integral (step_fun_abs f) (StepIntegral.v:92) — сумма |v_i| * w_i; в l1_close стоит именно она (SI.step_fun_norm). Одноимённая копия — L1Space.v:51.' });
  fix(P4, null, { file: L1S, claim: C4c, page_price: '0 Admitted, 0 аксиом',
    note: DONE + ': было «25 доказанных утверждений». В файле 16 строк Qed (grep -c \'Qed' + BS + '.\') и одно Defined (step_to_l1); число 25 стоит в шапке файла и устарело. «0 Admitted, 0 аксиом» верно.' });
  add({ theorem: 'L1On', file: L1I, claim: C4a, page_price: '0 аксиом', note: DONE + ': ' + N_L1ON });
  add({ theorem: 'l1_close', file: L1I, claim: C4a, page_price: '0 аксиом', note: N_CLOSE });
  add({ theorem: 'l1_close_same_function', file: L1I, claim: C4b, note: N_SAME });
  add({ theorem: 'L1Process', file: L1S, claim: C4c, note: N_OLD });
  add({ theorem: 'l1_integral_cauchy_aligned', file: L1I, claim: C4d, note: N_ALIGNED });
  add({ theorem: 'l1_process_integral_unbounded', file: L1I, claim: C4d, note: N_UNB });

  // --- правка 5: сноска 5 (место 3.3)
  const C5a = '`on_integral` — интеграл интегрируемой функции как процесс интегралов её стадий; `l1_on_integral_is_Cauchy` — этот процесс есть процесс Коши; `l1_on_equiv_integral` — у эквивалентных функций он называет одну точку.';
  const C5b = '`step_to_l1_on` — вложение ступенчатой функции; `series_l1` — ряд ступеней с суммируемыми нормами есть интегрируемая функция; пример — `staircase`: бесконечно много ступеней, сгущающихся к нулю; она не эквивалентна ни одной из своих стадий (`staircase_beyond_every_stage`).';
  const P5 = '`l1_integral_approx` — интеграл L¹-функции как приближающий процесс;';
  fix(P5, 'l1_integral_approx', { theorem: 'on_integral', file: L1I, claim: C5a,
    note: DONE + ': было — имена типа L1Process (l1_integral_approx, step_to_l1, l1_constant_integral). ' + N_ONINT });
  fix(P5, 'step_to_l1', { theorem: 'step_to_l1_on', file: L1I, claim: C5b, note: N_EMB });
  fix(P5, 'l1_constant_integral', { theorem: 'series_l1', file: L1I, claim: C5b, note: N_SERIES });
  add({ theorem: 'l1_on_integral_is_Cauchy', file: L1I, claim: C5a, note: N_CAUCHY });
  add({ theorem: 'l1_on_equiv_integral', file: L1I, claim: C5a, note: N_EQINT });
  add({ theorem: 'staircase', file: L1I, claim: C5b, note: N_STAIR });
  add({ theorem: 'staircase_beyond_every_stage', file: L1I, claim: C5b, note: N_BEYOND });
  add({ theorem: null, file: L1I, claim: 'Все — в файле `ProcessL1Integrable.v`, 0 аксиом.', page_price: '0 аксиом',
    note: 'Print Assumptions для всех 108 объявлений файла (83 доказательства и 25 определений) — ' + CL + ' (tos-audit-build/_p06step3/Verify.out).' });

  // --- правка 6: сноска 7 (место 3.4)
  const F7 = '$' + BS + 'forall' + BS + 'varepsilon>0' + BS + ' ' + BS + 'exists N' + BS + ' ' + BS + 'forall n' + BS + 'ge N:' + BS + ' ' + BS + '|f_n-g_n' + BS + '|_1<' + BS + 'varepsilon$';
  const C7a = '`l1_on_equiv` в `ProcessL1Integrable.v`: ' + F7 + '.';
  const C7b = 'Доказано, что это отношение эквивалентности (`l1_on_equiv_equivalence`) и что оно сохраняет интеграл (`l1_on_equiv_integral`).';
  const C7c = 'Пример: функция, равная единице в одной точке и нулю в остальных, эквивалентна нулевой (`point_differs_but_equivalent`), а постоянная единица — нет (`one_not_equiv_zero`).';
  const C7d = 'Это L¹-смысл равенства почти всюду; полностью поточечное «различаются лишь на множестве меры нуль» — содержательное чтение поверх этого ядра.';
  fix('`l1_equiv` в `L1Space.v`:', 'l1_equiv', { theorem: 'l1_on_equiv', file: L1I, claim: C7a,
    note: DONE + ': было «`l1_equiv` в `L1Space.v`» — норма разности по месту в списке. ' + N_EQV + ' Формула сноски совпадает с определением, где норма разности — близость l1_close (:450).' });
  add({ theorem: 'l1_on_equiv_equivalence', file: L1I, claim: C7b, note: N_EQUIV });
  add({ theorem: 'l1_on_equiv_integral', file: L1I, claim: C7b, note: N_EQINT });
  add({ theorem: 'point_differs_but_equivalent', file: L1I, claim: C7c, note: N_POINT });
  add({ theorem: 'one_not_equiv_zero', file: L1I, claim: C7c, note: N_ONE });
  add({ theorem: null, file: null, claim: C7d,
    note: 'Статус честный: «различаются на множестве меры нуль ⇒ эквивалентны» в общем виде не доказано; доказан пример с одной точкой (point_differs_but_equivalent, ' + L1I + ':699).' });

  // --- сноска 6 (шаг 2): примечание о типе
  note('Для функций ту же роль несёт интегрируемость (§ «Интегрируемая функция как предел ступенчатых»);', null,
    'Типа прообраз-измеримой функции в src нет — верно. Интегрируемость — тип L1On (' + L1I + ':521, шаг 3). Предиката различимости для функций в src нет; страница так и говорит.');

  save();
}

// ------------------------------------------------------------------ VI.5
{
  const { fix, note, add, save } = open('part06-ch05');

  // --- основной текст, не менялся (место 5.3)
  fix('$L^1$ — это пополнение ступенчатых функций по интегральной норме', null, { theorem: 'L1On', file: L1I,
    note: BYF + ', сноска 2 переписана: было — тип L1Process с разностью по месту в списке, для которого условие Коши интеграл не удерживает. ' + N_L1ON + ' ' + N_CAUCHY });
  fix('*интегрируемая функция есть предел ступенчатых функций по интегральной норме*', 'L1Process', { theorem: 'L1On', file: L1I,
    note: BYF + ', сноска 2 переписана: ' + N_L1ON + ' ' + N_CAUCHY });
  fix('Само пространство $L^1$ — это тип таких Коши-процессов, с точностью до отношения «совпадать в среднем»', 'l1_equiv', { theorem: 'l1_on_equiv_equivalence', file: L1I,
    note: BYF + ', сноска 2 переписана: было — отношением эквивалентности l1_equiv не являлось. ' + N_EQV + ' ' + N_EQUIV + ' ' + N_EQINT });
  note('Полнота $L^1$ при этом — не отдельная теорема, а *свойство построения*:', null,
    'Статус честный: теоремы о полноте (о пределе последовательности интегрируемых функций) нет, и страница её не заявляет. Тип — L1On (' + L1I + ':521); представители сверх ступенчатых функций строятся напрямую — series_l1 (:769), staircase (:842).');

  // --- правка 7: сноска 2 (места 5.3, 5.5)
  const C2a = 'Файл `ProcessL1Integrable.v` (каталог `src/process/`, 83 доказанных утверждения, 0 аксиом): `L1On` (представители), `l1_close` (близость по интегральной норме), `on_integral`, `l1_on_equiv` ($' + BS + '|f-g' + BS + '|_1' + BS + 'to0$; что это отношение эквивалентности — `l1_on_equiv_equivalence`), `step_to_l1_on`.';
  const C2b = 'Прежний файл `L1Space.v` (каталог `src/analysis/`, 16 доказанных утверждений): тип `L1Process` — для стадий на общем разбиении.';
  const P2 = 'Файл `L1Space.v` (каталог `analysis/`, 25 Qed по шапке):';
  fix(P2, null, { file: L1I, claim: C2a, page_price: '0 аксиом',
    note: DONE + ': было «Файл `L1Space.v` (каталог `analysis/`, 25 Qed по шапке)». В новом файле 83 строки Qed (grep -c \'Qed' + BS + '.\'); Print Assumptions для всех 108 объявлений — ' + CL + '.' });
  fix(P2, 'step_fun_norm', { theorem: 'l1_close', file: L1I, claim: C2a, page_price: '0 аксиом', note: N_CLOSE });
  fix(P2, 'l1_integral_approx', { theorem: 'on_integral', file: L1I, claim: C2a, page_price: '0 аксиом', note: N_ONINT + ' Что это процесс Коши — ' + N_CAUCHY });
  fix(P2, 'step_to_l1', { theorem: 'step_to_l1_on', file: L1I, claim: C2a, page_price: '0 аксиом', note: N_EMB });
  add({ theorem: 'L1On', file: L1I, claim: C2a, page_price: '0 аксиом', note: N_L1ON });
  add({ theorem: 'l1_on_equiv', file: L1I, claim: C2a, page_price: '0 аксиом', note: N_EQV });
  add({ theorem: 'l1_on_equiv_equivalence', file: L1I, claim: C2a, page_price: '0 аксиом', note: N_EQUIV });
  add({ theorem: 'L1Process', file: L1S, claim: C2b,
    note: DONE + ' (добавлено): в L1Space.v 16 строк Qed и одно Defined. ' + N_OLD + ' Для стадий на общем разбиении — ' + N_ALIGNED });

  save();
}
