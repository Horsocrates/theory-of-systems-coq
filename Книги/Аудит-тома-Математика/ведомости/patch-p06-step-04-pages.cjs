// Часть VI, шаг 4, страницы (2026-11-15, слово автора «Делай»): 7 правок глав VI.4 и VI.1 внесены
// (VI.4: новый абзац о месте границы, фраза о Фату, сноски 3, 6, 7 и новые сноски 8–10; VI.1: сноски 12 и 13).
// Формализация — новый src/process/ProcessConvergenceTheorems.v; прежние файлы не менялись.
// Запуск: node patch-p06-step-04-pages.cjs  (затем relocate + merge по part06-ch04, part06-ch01). Скрипт повторяем.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 15.11 (Часть VI, шаг 4, слово автора)';
const BYF = DONE + ' (формализацией; текст страницы не менялся)';
const CL = 'Closed under the global context';
const CT = 'src/process/ProcessConvergenceTheorems.v';
const PFV = 'src/process/ProcessFatou.v';
const BS = String.fromCharCode(92);
const AND = '/' + BS;
const DOM_NEW = '$' + BS + 'forall k,' + BS + ' ' + BS + 'forall x' + BS + 'in[a,b]:' + BS + ' |f_k(x)|' + BS + 'le g(x)$';
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

// утверждения нового файла (номера строк — src/process/ProcessConvergenceTheorems.v)
const N_FINF = 'process_fatou_inf : forall (fs : nat -> Q -> Q) (a b : Q) (n s : nat), a < b -> PL.lebesgue_process (fun x => PF.q_min_seq (fun k => fs k x) n) a b s <= PF.q_min_seq (fun k => PF.integral_sequence fs a b k s) n (:111) — на стадии s интеграл минимума функций fs 0 … fs n не больше минимума их интегралов. ' + CL + '.';
const N_FTAIL = 'process_fatou_tail (:124) — то же для минимума по k из [m, m + n] (хвост последовательности). ' + CL + '.';
const N_GFAT = 'grid_fatou : forall fs pts w N n, 0 <= w -> MCT.riemann_sum (fun x => PF.q_min_seq (fun k => fs k x) n) pts w N <= PF.q_min_seq (fun k => MCT.riemann_sum (fs k) pts w N) n (:98) — на фиксированной сетке узлов. ' + CL + '.';
const N_FBG = 'process_fatou_bounded_g : forall fs g a b n, a < b -> (forall k x, Qabs (fs k x) <= g x) -> Qabs (PF.q_min_seq (fun k => PF.integral_sequence fs a b k n) n) <= PL.lebesgue_process g a b n (:155) — оценка интегралом самой мажоранты на стадии n, без постоянной M; через lebesgue_abs_le_majorant (:138). ' + CL + '.';
const N_DIBG = 'dominated_integral_bound_g : forall f1 f2 g a b s, a < b -> (forall x, Qabs (f1 x) <= g x) -> (forall x, Qabs (f2 x) <= g x) -> Qabs (PL.lebesgue_process f1 a b s - PL.lebesgue_process f2 a b s) <= PL.lebesgue_process (fun x => 2 * g x) a b s (:167). ' + CL + '.';
const N_GRES = 'grid_residual_from_pointwise : forall fs f pts w N, (forall i, i < N -> (fun n => fs n (pts i)) ~~ const_process (f (pts i))) -> (fun n => MCT.riemann_sum (fun x => Qabs (fs n x - f x)) pts w N) ~~ const_process 0 (:258) — без мажоранты. ' + CL + '.';
const N_GPT = 'grid_pointwise_from_residual : то же в обратную сторону при 0 < w (:302): на фиксированной сетке посылка process_dct равносильна поточечной сходимости в узлах. ' + CL + '.';
const N_GDCT = 'grid_dct_pointwise : forall fs f pts w N, 0 <= w -> (forall i, i < N -> (fun n => fs n (pts i)) ~~ const_process (f (pts i))) -> (fun n => MCT.riemann_sum (fs n) pts w N) ~~ const_process (MCT.riemann_sum f pts w N) (:278) — на фиксированной сетке обмен верен при одной поточечной сходимости. ' + CL + '.';
const N_ENG = 'lebesgue_engine : forall f1 f2 a b s, a < b -> Qabs (PL.lebesgue_process f1 a b s - PL.lebesgue_process f2 a b s) <= PL.lebesgue_process (fun x => Qabs (f1 x - f2 x)) a b s (:332). ' + CL + '.';
const N_ENV = 'lebesgue_envelope : forall f1 f2 g a b s, a < b -> (forall x, Qabs (f1 x - f2 x) <= 2 * g x) -> PL.lebesgue_process (fun x => Qabs (f1 x - f2 x)) a b s <= PL.lebesgue_process (fun x => 2 * g x) a b s (:354); переход от |f1| <= g и |f2| <= g к посылке — envelope_from_domination (:191). ' + CL + '.';
const N_IC = 'Definition integrals_converge (I : nat -> RealProcess) (J : RealProcess) : Prop := forall eps, 0 < eps -> exists K, forall k, K <= k -> exists S0, forall s, S0 <= s -> Qabs (I k s - J s) < eps (:366) — сначала предел по сетке (по s), затем по k.';
const N_DCTL = 'process_dct_lebesgue : forall fs f a b, a < b -> integrals_converge (fun k => PL.lebesgue_process (fun x => Qabs (fs k x - f x)) a b) (const_process 0) -> integrals_converge (fun k => PL.lebesgue_process (fs k) a b) (PL.lebesgue_process f a b) (:374). ' + N_IC + ' Здесь посылка о невязках — утверждение о пределе по сетке. ' + CL + '.';
const N_CEX = 'pointwise_dominated_not_enough (:561): exists fs f g, (forall k x, fs k x <= fs (S k) x) ' + AND + ' (forall k x, Qabs (fs k x) <= g x) ' + AND + ' (forall x, (fun k => fs k x) ~~ const_process (f x)) ' + AND + ' (forall k, PL.lebesgue_process (fs k) 0 1 ~~ const_process 0) ' + AND + ' PL.lebesgue_process g 0 1 ~~ const_process 1 ' + AND + ' PL.lebesgue_process f 0 1 ~~ const_process 1. Свидетели: fs = first_ind enum_Q (:434 — индикатор первых k членов нумерации рациональных чисел), f = g = 1; интеграл индикатора равен нулю, потому что каждая точка стоит не больше шага сетки (first_ind_integral_null, :522). ' + CL + '.';
const N_FAIL = 'dct_fails_on_rational_grid : ~ integrals_converge (fun k => PL.lebesgue_process (first_ind enum_Q k) 0 1) (PL.lebesgue_process (fun _ => 1) 0 1) (:582). ' + CL + '.';
const N_AUR = 'almost_uniform_residual (:613): при a < b, forall n x, Qabs (fs n x - f x) <= 2 * g x и условии «для всякого delta > 0 есть множество bad : Q -> bool и стадия S0 такие, что PL.lebesgue_process (fun x => if bad x then 2 * g x else 0) a b s < delta при s >= S0, а вне bad сходимость равномерна» невязки сходятся к нулю в смысле integrals_converge. ' + CL + '.';
const N_DAU = 'dominated_almost_uniform_convergence (:664): при a < b, forall n x, Qabs (fs n x) <= g x, forall x, Qabs (f x) <= g x и том же условии почти равномерной сходимости — integrals_converge (fun k => PL.lebesgue_process (fs k) a b) (PL.lebesgue_process f a b). Мажоранта несёт оценку на «плохом» множестве. ' + CL + '.';
const N_UNI = 'uniform_convergence_integral (:687): при forall n x, Qabs (fs n x - f x) <= e n и e ~~ const_process 0 интегралы сходятся равномерно по стадии сетки; uniform_is_almost_uniform (:715): равномерная сходимость удовлетворяет условию почти равномерной с пустым «плохим» множеством. ' + CL + '.';

// ------------------------------------------------------------------ VI.4
{
  const { fix, note, add, save } = open('part06-ch04');

  // --- основной текст, не менялся (места 4.1, 4.3)
  fix('сходимости невязок; лемма Фату на процессном уровне.', 'process_fatou_nonneg', { theorem: 'process_fatou_inf', file: CT,
    note: BYF + ': было — в ProcessFatou.v неравенства Фату не было ни в какой форме. ' + N_FINF + ' ' + N_FTAIL });
  fix('*Остаётся честной границей*: сам шаг «поточечная сходимость плюс мажоранта влечёт сходимость невязок к нулю»', 'process_dct', { theorem: 'process_dct_lebesgue', file: CT,
    note: BYF + '; в § «Мажорированная сходимость как редукция» добавлен абзац о месте границы: было — посылка process_dct говорила о сумме на фиксированной сетке, где шаг доказуем без мажоранты. ' + N_DCTL + ' Что на этом уровне шаг внутри системы не выводится — ' + N_CEX });
  fix('ToS берёт *её* как явную гипотезу-вход, а не доказывает внутри системы:', 'process_dct', { theorem: 'process_dct_lebesgue', file: CT,
    note: BYF + ', следом добавлен абзац о месте границы: ' + N_DCTL + ' Движок и конверт для процесса интегралов — lebesgue_engine (:332), lebesgue_envelope (:354).' });
  fix('Лемму Фату — что интеграл нижнего предела не превосходит нижнего предела интегралов — ToS удерживает на процессном уровне:', 'process_fatou_nonneg', { theorem: 'process_fatou_inf', file: CT,
    note: DONE + ' (формализацией; продолжение фразы дополнено): ' + N_FINF + ' Нижнего предела в утверждении нет: конечный минимум на стадии; хвостовая форма — process_fatou_tail (:124).' });
  fix('Это конечно-процессное ядро Фату: на каждой стадии $n$ величины определены и удовлетворяют нужным неравенствам.', null, { theorem: 'process_fatou_inf', file: CT,
    note: BYF + ': среди доказанных неравенств теперь есть само неравенство Фату для конечного минимума. ' + N_FINF });
  fix('Процессное ядро доказано; завершённый объект не актуализируется.', null, { theorem: 'process_fatou_inf', file: CT,
    note: BYF + ': ' + N_FINF });
  fix('Мажорированная сходимость *редуцирована*: её арифметическая машина (движок и конверт) доказана без аксиом,', 'process_dct', { theorem: 'process_dct_lebesgue', file: CT,
    note: BYF + ': ' + N_DCTL + ' Цена названа верно.' });
  fix('Доказанная часть — монотонная сходимость, движок и конверт мажорированной, процессное ядро Фату', null, { theorem: 'process_fatou_inf', file: CT,
    note: BYF + ': «процессное ядро Фату» — ' + N_FINF });
  note('Это монотонность интеграла, применённая к доменно-явной мажоранте.', 'dct_dom_bound',
    'dct_dom_bound (ProcessDCT.v:99): посылка forall x, Qabs (f1 x - f2 x) <= 2 * g x взята прямо, доказательство — riemann_sum_monotone. Переход от |f_n| <= g и |f| <= g к этой посылке — envelope_from_domination (' + CT + ':191, шаг 4); для процесса интегралов конверт — lebesgue_envelope (:354).');

  // --- правка 1: новый абзац о месте границы
  const CA = 'На фиксированной сетке узлов границы нет: там стремление невязки к нулю равносильно поточечной сходимости в узлах и доказывается без мажоранты.';
  const CB = 'Граница появляется при переходе к процессу интегралов — к пределу по сетке: там посылка о невязках уже не следует из поточечной сходимости и мажоранты.';
  const CC = 'Пример: индикаторы первых $k$ точек нумерации рациональных чисел растут к единице в каждой рациональной точке и ограничены мажорантой $g' + BS + 'equiv 1$; интеграл каждого равен нулю, а интеграл предела — единице.';
  const CD = 'И там же посылка снимается, если недостающее предъявлено как данные, подобно мажоранте: сходимость равномерна вне множества, на котором интеграл мажоранты сколь угодно мал, — тогда невязки стремятся к нулю, и сходимость интегралов доказана без аксиом.';
  add({ theorem: 'grid_residual_from_pointwise', file: CT, claim: CA, page_price: 'без мажоранты', note: DONE + ' (добавлено): ' + N_GRES });
  add({ theorem: 'grid_pointwise_from_residual', file: CT, claim: CA, note: N_GPT });
  add({ theorem: 'dct_fails_on_rational_grid', file: CT, claim: CB, note: N_FAIL });
  add({ theorem: 'pointwise_dominated_not_enough', file: CT, claim: CC, note: DONE + ' (добавлено): ' + N_CEX });
  add({ theorem: 'almost_uniform_residual', file: CT, claim: CD, page_price: 'без аксиом', note: DONE + ' (добавлено): ' + N_AUR });
  add({ theorem: 'dominated_almost_uniform_convergence', file: CT, claim: CD, page_price: 'без аксиом', note: N_DAU });

  // --- правка 2: фраза о Фату (места 4.1, 4.2)
  const C2a = 'на каждой стадии интеграл нижней огибающей конечного набора функций не превосходит нижней огибающей их интегралов;';
  const C2b = 'для неотрицательных функций нижняя огибающая последовательности интегралов неотрицательна, а при доминировании ограничена интегралом мажоранты.';
  add({ theorem: 'process_fatou_inf', file: CT, claim: C2a, note: DONE + ' (добавлено): ' + N_FINF });
  add({ theorem: 'process_fatou_tail', file: CT, claim: C2a, note: N_FTAIL });
  fix('для неотрицательных функций нижняя огибающая последовательности интегралов неотрицательна, а при доминировании ограничена.', 'process_fatou_bounded', {
    theorem: 'process_fatou_bounded_g', file: CT, claim: C2b,
    note: DONE + ': было «при доминировании ограничена» — process_fatou_bounded (ProcessFatou.v:199) требует ещё g x <= M и даёт оценку M·(b − a). ' + N_FBG });
  add({ theorem: 'process_fatou_nonneg', file: PFV, claim: C2b,
    note: 'Первая половина фразы: process_fatou_nonneg (:187): a < b -> (forall k x, 0 <= fs k x) -> 0 <= q_min_seq (fun k => integral_sequence fs a b k n) n. ' + CL + '.' });

  // --- правка 3: сноска 3 (место 4.4)
  fix('Предикат `dominated` в `ProcessFatou.v`:', 'dominated', {
    claim: 'Предикат `dominated` в `ProcessFatou.v`: ' + DOM_NEW + ', где $g$ и отрезок $[a,b]$ — параметры.',
    note: DONE + ': было «$' + BS + 'forall k x$ … где $g$ — параметр» — без условия на отрезок. dominated (:41): forall k x, a <= x -> x <= b -> Qabs (fs k x) <= g x; fs, g, a, b — аргументы.' });

  // --- правка 4: сноска 6
  const C6 = 'Это утверждения о сумме на фиксированной сетке узлов; для процесса интегралов (предел по сетке) те же три звена — `lebesgue_engine`, `lebesgue_envelope`, `process_dct_lebesgue` (файл `ProcessConvergenceTheorems.v`, 0 аксиом).';
  add({ theorem: 'lebesgue_engine', file: CT, claim: C6, page_price: '0 аксиом', note: DONE + ' (добавлено): ' + N_ENG });
  add({ theorem: 'lebesgue_envelope', file: CT, claim: C6, page_price: '0 аксиом', note: N_ENV });
  add({ theorem: 'process_dct_lebesgue', file: CT, claim: C6, page_price: '0 аксиом', note: N_DCTL });

  // --- правка 5: сноска 7 и новые сноски 8–10
  const C7a = 'Неравенство — `process_fatou_inf` (по хвосту последовательности — `process_fatou_tail`, на сетке узлов — `grid_fatou`);';
  const C7b = 'оценки через мажоранту-функцию — `process_fatou_bounded_g` (нижняя огибающая интегралов не больше интеграла $g$) и `dominated_integral_bound_g` (разность интегралов не больше интеграла $2g$).';
  const C7c = 'В `ProcessFatou.v` (0 аксиом): `process_fatou_nonneg`, а также `process_fatou_bounded` и `dominated_integral_bound` — оценки с постоянной $M$ на месте мажоранты-функции.';
  fix('`process_fatou_nonneg` и `process_fatou_bounded` в `ProcessFatou.v` (0 аксиом);', 'process_fatou_nonneg', { claim: C7c,
    note: 'Цена: Print Assumptions process_fatou_nonneg и process_fatou_bounded — ' + CL + '. process_fatou_nonneg (:187) — знак минимума интегралов неотрицательных функций.' });
  fix('`dominated_integral_bound` — оценка разности интегралов через мажоранту.', 'dominated_integral_bound', { claim: C7c, page_price: '0 аксиом',
    note: DONE + ': было «оценка разности интегралов через мажоранту» — в dominated_integral_bound (:234) обе функции ограничены одной постоянной M, оценка 2 * M * (b - a); сноска теперь так и говорит. Оценка с мажорантой-функцией — dominated_integral_bound_g (' + CT + ':167). ' + CL + '.' });
  add({ theorem: 'process_fatou_bounded', file: PFV, claim: C7c, page_price: '0 аксиом',
    note: 'process_fatou_bounded (:199): при forall k x, Qabs (fs k x) <= g x, forall x, g x <= M, 0 <= M, a < b — Qabs (q_min_seq …) <= M * (b - a): оценка с постоянной M. ' + CL + '.' });
  add({ theorem: 'process_fatou_inf', file: CT, claim: C7a, page_price: '0 аксиом', note: N_FINF });
  add({ theorem: 'process_fatou_tail', file: CT, claim: C7a, page_price: '0 аксиом', note: N_FTAIL });
  add({ theorem: 'grid_fatou', file: CT, claim: C7a, page_price: '0 аксиом', note: N_GFAT });
  add({ theorem: 'process_fatou_bounded_g', file: CT, claim: C7b, page_price: '0 аксиом', note: N_FBG });
  add({ theorem: 'dominated_integral_bound_g', file: CT, claim: C7b, page_price: '0 аксиом', note: N_DIBG });
  add({ theorem: null, file: CT, claim: 'Все — в `ProcessConvergenceTheorems.v`, 0 аксиом.', page_price: '0 аксиом',
    note: 'Print Assumptions для всех 40 объявлений файла (37 доказательств и 3 определения) — ' + CL + ' (tos-audit-build/_p06step4/Verify.out).' });
  const C8 = '`grid_residual_from_pointwise`, `grid_pointwise_from_residual`, `grid_dct_pointwise` в `ProcessConvergenceTheorems.v` (0 аксиом).';
  add({ theorem: 'grid_residual_from_pointwise', file: CT, claim: C8, page_price: '0 аксиом', note: N_GRES });
  add({ theorem: 'grid_pointwise_from_residual', file: CT, claim: C8, page_price: '0 аксиом', note: N_GPT });
  add({ theorem: 'grid_dct_pointwise', file: CT, claim: C8, page_price: '0 аксиом', note: N_GDCT });
  const C9a = '`pointwise_dominated_not_enough` и `dct_fails_on_rational_grid` в `ProcessConvergenceTheorems.v` (0 аксиом).';
  const C9b = 'Точки, в которых заданы функции, — рациональные; последовательность к тому же возрастает, так что пример касается и монотонной сходимости в полном виде.';
  add({ theorem: 'pointwise_dominated_not_enough', file: CT, claim: C9a, page_price: '0 аксиом', note: N_CEX });
  add({ theorem: 'dct_fails_on_rational_grid', file: CT, claim: C9a, page_price: '0 аксиом', note: N_FAIL });
  add({ theorem: 'pointwise_dominated_not_enough', file: CT, claim: C9b,
    note: 'Первый член заключения теоремы — forall k x, fs k x <= fs (S k) x (first_ind_mono). Функции имеют тип Q -> Q; сходимость утверждается в каждой рациональной точке (Q_countable). Теорема главы о монотонной сходимости (process_mct) говорит о другом — что процесс интегралов есть процесс Коши, — и примером не затронута.' });
  const C10a = '`almost_uniform_residual` и `dominated_almost_uniform_convergence` в `ProcessConvergenceTheorems.v` (0 аксиом); равномерная сходимость — частный случай (`uniform_convergence_integral`, `uniform_is_almost_uniform`).';
  add({ theorem: 'almost_uniform_residual', file: CT, claim: C10a, page_price: '0 аксиом', note: N_AUR });
  add({ theorem: 'dominated_almost_uniform_convergence', file: CT, claim: C10a, page_price: '0 аксиом', note: N_DAU });
  add({ theorem: 'uniform_convergence_integral', file: CT, claim: C10a, page_price: '0 аксиом', note: N_UNI });
  add({ theorem: 'uniform_is_almost_uniform', file: CT, claim: C10a, page_price: '0 аксиом', note: N_UNI });
  add({ theorem: null, file: null,
    claim: 'Классически переход от поточечной сходимости к равномерной вне множества малой меры даёт теорема Егорова — над завершённой мерой.',
    note: 'Классическое сравнение; теоремы Егорова в src нет (и по примеру pointwise_dominated_not_enough для процесса интегралов над рациональными узлами она в таком виде неверна). Пример почти равномерной, но не равномерной сходимости в src не предъявлен.' });

  save();
}

// ------------------------------------------------------------------ VI.1
{
  const { fix, add, save } = open('part06-ch01');

  // стр. 251: основной текст не менялся (место 1.3)
  fix('В Главе 6.4 он несёт всю теорему о мажорированной сходимости:', 'process_dct', { theorem: 'dominated_almost_uniform_convergence', file: CT,
    note: BYF + ', сноска 13 переписана: было — в process_dct мажоранты нет, сходимость выводится из одной посылки о невязках на фиксированной сетке. ' + N_DAU + ' Посылка о невязках и её место названы в сноске 13.' });

  // правка 6: сноска 12
  fix('В коде доминирование — предикат `dominated`, берущий мажоранту $g$ явным аргументом:', 'dominated', {
    claim: 'В коде доминирование — предикат `dominated`, берущий мажоранту $g$ явным аргументом: ' + DOM_NEW + '. Это и есть «доменно-явная мажоранта».',
    note: DONE + ': формула дополнена условием на отрезок. Definition dominated (fs : nat -> Q -> Q) (g : Q -> Q) (a b : Q) : Prop := forall k x, a <= x -> x <= b -> Qabs (fs k x) <= g x (ProcessFatou.v:41). Файл на странице не назван; одноимённое определение есть в analysis/DominatedConvergence.v:80.' });

  // правка 7: сноска 13
  const C13a = 'Редукция мажорированной сходимости — `process_dct` (`ProcessDCT.v`) на фиксированной сетке узлов и `process_dct_lebesgue` (`ProcessConvergenceTheorems.v`) для процесса интегралов, 0 аксиом: движок и «конверт»-мажоранта доказаны конструктивно, а сходимость невязок к нулю вынесена в явную гипотезу-вход.';
  const C13b = 'На фиксированной сетке эта гипотеза равносильна поточечной сходимости в узлах; для процесса интегралов она из поточечной сходимости и мажоранты не следует (`pointwise_dominated_not_enough`) и снимается, когда сходимость равномерна вне множества с малым интегралом мажоранты, — там мажоранта и несёт оценку (`dominated_almost_uniform_convergence`).';
  fix('Редукция мажорированной сходимости — `process_dct` (`ProcessDCT.v`), 0 аксиом:', 'process_dct', { claim: C13a,
    note: DONE + ': было «единственный неконструктивный шаг (сходимость невязок к нулю) вынесен в явную гипотезу-вход» без различения уровней. process_dct (ProcessDCT.v:123) — о сумме на фиксированной сетке; движок dct_diff_bound (:73), конверт dct_dom_bound (:99). ' + CL + '.' });
  add({ theorem: 'process_dct_lebesgue', file: CT, claim: C13a, page_price: '0 аксиом', note: N_DCTL });
  add({ theorem: 'grid_pointwise_from_residual', file: CT, claim: C13b, note: N_GRES + ' ' + N_GPT });
  add({ theorem: 'pointwise_dominated_not_enough', file: CT, claim: C13b, note: N_CEX });
  add({ theorem: 'dominated_almost_uniform_convergence', file: CT, claim: C13b, note: N_DAU });

  save();
}
