// Часть V, шаг 10, страницы (2026-11-12, слово автора «Да — вносим семнадцать мест»): глава V.3.
// Запуск: node patch-p5-step-10-pages.cjs   (затем tom-links.cjs relocate + merge по ведомостям главы V.3)
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 12.11 (Часть V, шаг 10, слово автора)';
const norm = (s) => (s || '').replace(/\s+/g, ' ');
function open(name) {
  const p = path.join(__dirname, name);
  const j = JSON.parse(fs.readFileSync(p, 'utf8'));
  let n = 0, added = 0;
  return {
    set(prefix, fields) {
      const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix));
      if (hit.length !== 1) throw new Error(name + ': ожидалась одна запись «' + prefix + '», найдено ' + hit.length);
      Object.assign(hit[0], fields); n++;
    },
    add(rec) {
      if (j.records.some((r) => r.theorem === rec.theorem && norm(r.claim) === norm(rec.claim))) return;
      j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); added++;
    },
    save() { fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n'); console.log(name + ': изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length); },
  };
}
const IDX = 'src/EVT_idx.v', ANC = 'src/EVT_ArgmaxNotCauchy.v', UC = 'src/UniformConvergence.v';
const a = open('part05-ch03.json');
a.set('Опорных файлов девять, все сверены с репозиторием дословно.', {
  claim: 'Опорных файлов девять; к ним примыкают головной файл `analysis/Continuity.v` и смежная заготовка `ProcessContinuity.v`. Блоки кода сверены с репозиторием дословно.',
  verdict: 'ok',
  note: DONE + ': девять файлов несут материал главы (Topology, UniformConvergence, HeineBorelComplete, IVT_ERR, ProcessIVT, IVT_CauchyReal, EVT_ERR, EVT_idx, ProcessEVT); два названных рядом — примыкающие. Три блока кода, отличавшиеся от исходника записью (continuous_at, continuous_preserves_open_preimage, lipschitz_uniform_cont), приведены к исходнику; у третьего в исходнике снята лишняя посылка a <= b.' });
a.set('`continuous_at_comp` и отправные `identity_ continuous`', {
  claim: '`continuous_at_comp` и отправные `identity_continuous`, `constant_continuous`), такого звена нет', verdict: 'ok',
  note: DONE + ': имя было разорвано переносом строки («identity_ continuous»); собрано на одной строке. Объявление существует (Topology.v).' });
a.set('искомый объект — корень или максимизатор — играет роль *Cauchy-процесса', {
  claim: 'корень играет роль *Cauchy-процесса в $[a,b]$*, сходящегося к перемене знака; у максимума эту роль несёт процесс *значений*, приближающий супремум, а процесс позиций лишь лежит в $[a,b]$.[^2]',
  verdict: 'ok',
  note: DONE + ': было — максимизатор назван Cauchy-процессом в отрезке; доказана только принадлежность отрезку (argmax_in_interval), а свойства Коши у процесса позиций в общем случае нет (EVT_ArgmaxNotCauchy.v). Шапка ProcessEVT.v, откуда взята ролевая разметка, исправлена так же.' });
a.set('(с этим файлом глава встречалась в § 2.6) теоремой:', {
  verdict: 'ok',
  note: DONE + ': блок кода теперь совпадает с исходником — у lipschitz_uniform_cont (analysis/HeineBorelComplete.v) снята неиспользуемая посылка a <= b; на странице имя константы приведено к исходнику (K). Closed under the global context.' });
a.set('И аксиом этот уровень не вносит: `process_IVT`, как и теорема `IVT_ERR`', {
  claim: 'И аксиом этот уровень не вносит: `process_IVT`, как и теорема `IVT_process`, доказана без допущений.' });
a.set('как и теорема `IVT_ERR`, доказана без допущений.', {
  theorem: 'IVT_process', file: 'src/IVT_ERR.v',
  claim: 'как и теорема `IVT_process`, доказана без допущений.', page_price: 'без допущений', verdict: 'ok',
  note: DONE + ': было «теорема IVT_ERR» — это имя файла; теорема называется IVT_process. Closed under the global context.' });
a.set('Главная теорема `ivt_cauchy_real` и её следствие `ivt_cauchy_real_equiv`', {
  claim: 'Главная теорема `ivt_cauchy_real` обходится без неё — её заключение записано прямо, через $|f(c_n)| < \\varepsilon$.',
  verdict: 'ok',
  note: DONE + ': было «главная теорема и её следствие стоят на этой лемме» — доказательство ivt_cauchy_real (IVT_CauchyReal.v) применяет bisection_cauchy_seq, bisection_cauchy_in_interval, bisection_f_converges_to_zero; леммы continuous_compose_cauchy в нём нет.' });
a.set('её следствие `ivt_cauchy_real_equiv` (которое выражает результат через', {
  claim: 'На этой лемме стоит следствие `ivt_cauchy_real_equiv` (которое выражает результат через `cauchy_equiv` с постоянным нулём)',
  note: 'Следствие применяет лемму через compose_cauchy_seq (IVT_CauchyReal.v); слова приведены к этому шагом 10 Части V.' });
a.set('*Позиция* максимума — `argmax`, тот узел', {
  theorem: 'argmax_on_grid', file: 'src/EVT_ERR.v',
  claim: '*Позиция* максимума — `argmax_on_grid`, тот узел, на котором это наибольшее значение достигается.', verdict: 'ok',
  note: DONE + ': было «argmax» — такого имени в формализации нет; позицию даёт argmax_on_grid (EVT_ERR.v; в index-версии — одноимённое определение EVT_idx.v).' });
a.set('Но и детерминированности мало: даже с однозначно выбираемой позицией процесс `argmax_process`', {
  theorem: 'argmax_process_need_not_be_Cauchy', file: ANC,
  claim: 'Но и детерминированности мало: даже с однозначно выбираемой позицией процесс `argmax_process` Cauchy быть не обязан. Если у функции два равноценных максимума, сетки разных шагов попадают то в один, то в другой, и позиция перескакивает между ними, сколько бы шагов ни прошло: для функции с двумя равными пиками в $1/3$ и $1/2$ это доказано (`argmax_process_need_not_be_Cauchy`, файл `EVT_ArgmaxNotCauchy.v`).',
  verdict: 'ok',
  note: DONE + ': было — утверждение без теоремы и с неверным доводом (приближение к иррациональной точке свойству Коши не мешает). Новый файл EVT_ArgmaxNotCauchy.v: exists f, uniformly_continuous_on f 0 1 /\\ ~ is_Cauchy (argmax_process f 0 1) — функция two_peaks. Closed under the global context.' });
a.set('теорема `EVT_strong_process`: процесс значений супремума есть Коши', {
  claim: 'теорема `EVT_strong_process`: процесс значений супремума есть Коши, процесс позиций лежит в $[a,b]$, на каждом шаге значение супремума совпадает с $f$ от позиции, и всякое значение функции на отрезке в конце концов не превосходит значения процесса с любым зазором (`EVT_idx_majorant`).',
  note: DONE + ' — в теорему внесён четвёртый член, мажоранта: forall x из отрезка, forall eps > 0, exists N, forall n > N, f x <= sup_process f a b n + eps. Closed under the global context.' });
a.set('То же честное содержание, что и в `EVT_complete` (§ 3.6.4)', {
  verdict: 'ok',
  note: DONE + ' — слова те же, доведена формализация: в EVT_strong_process не было мажорирующего свойства; теперь оно — четвёртый член (EVT_idx_majorant), и содержание действительно то же, что у EVT_complete.' });
a.set('о процессе позиций комментарий `EVT_idx.v` прямо повторяет', {
  theorem: 'argmax_process_need_not_be_Cauchy', file: ANC,
  claim: 'процесс позиций Коши быть не обязан — при двух равноценных максимумах он перескакивает между ними (`argmax_process_need_not_be_Cauchy`).',
  note: DONE + ': было «его предел может оказаться иррациональным» — довод неверен и снят (и в комментарии EVT_idx.v тоже); названа теорема-контрпример.' });
a.set('Третий файл — `ProcessEVT.v` (190 строк)', {
  claim: 'Третий файл — `ProcessEVT.v` (194 строки)',
  note: DONE + ': после шага 10 в файле 194 строки (шапка выросла на четыре строки), 10 Qed.' });
// вторая запись с той же цитатой (о dini_monotone) — найти по теореме
{
  const j = a; // доступ к записи через set невозможен (одинаковое начало) — правим вручную ниже
}
a.save();
// записи с одинаковым началом цитаты и остальные — вручную
{
  const p = path.join(__dirname, 'part05-ch03.json');
  const j = JSON.parse(fs.readFileSync(p, 'utf8'));
  const find = (pred, what) => { const h = j.records.filter(pred); if (h.length !== 1) throw new Error('ожидалась одна запись: ' + what + ', найдено ' + h.length); return h[0]; };
  Object.assign(find((r) => !r.theorem && norm(r.claim).startsWith('Файл `UniformConvergence.v` — шире этой одной теоремы'), 'UniformConvergence шире'), {
  theorem: 'integral_limit_exchange', file: UC,
  claim: 'Файл `UniformConvergence.v` — шире этой одной теоремы: в нём есть обмен предела с интегралом (для сумм Римана), оценки приращений при равномерной сходимости и сеточная лемма о конечном числе узлов.',
  verdict: 'ok',
  note: DONE + ': было «и обмен с производной, и теорема Дини» — у derivative_limit_exchange предельная производная в заключение не входит (оценка приращений), у dini_monotone нет монотонности в условии (лемма о конечном числе узлов). Довести до прежних слов нельзя: теорема Дини над Q в классической форме, по оценке, неверна (как Кантор — Гейне); обмен предела с производной — горизонт главы о производной.' });
  Object.assign(find((r) => r.theorem === 'dini_monotone', 'dini_monotone'), {
    claim: 'оценки приращений при равномерной сходимости и сеточная лемма о конечном числе узлов.',
    verdict: 'ok',
    note: DONE + ': было «теорема Дини» — dini_monotone (UniformConvergence.v): если в каждом из конечного числа узлов сетки значения становятся меньше eps, то есть общий номер для всех узлов; монотонности в условии нет. Слова приведены к содержанию.' });
  Object.assign(find((r) => norm(r.claim).startsWith('Шапка файла `UniformConvergence.v` объявляет'), 'шапка UniformConvergence'), {
    claim: '`UniformConvergence.v` подключает результаты о монотонной сходимости, стоящие на `classic`, но этой теореме они не нужны.',
    file: UC,
    note: DONE + ': шапка файла исправлена («AXIOMS: none»); файл подключает MonotoneConvergence.v (в нём q_inc_bounded_cauchy и др. на classic), но в обходе допущений ни одного утверждения UniformConvergence.v нет.' });
  Object.assign(find((r) => r.theorem === 'uniform_limit_continuous_on' && r.verdict !== 'ok', 'цена uniform_limit_continuous_on'), {
    claim: 'проверка `Print Assumptions` отвечает: «Closed under the global context» — теорема о равномерном пределе доказана без допущений, как и остальные утверждения файла.',
    page_price: 'без допущений', verdict: 'ok',
    note: DONE + ': было — цена «оставлена проверке»; проверка проведена: uniform_limit_continuous_on — Closed under the global context, как и все утверждения файла.' });
  Object.assign(find((r) => r.theorem === 'continuous_on' && r.verdict !== 'ok', 'continuous_on'), {
    file: UC,
    claim: '(`continuous_at`, `continuous` в `Topology.v`; `continuous_on` в `UniformConvergence.v`), алгебра непрерывных функций, прообраз открытого открыт; конструктивно, без аксиом.',
    verdict: 'ok',
    note: DONE + ': было — continuous_on приписано Topology.v; объявлено оно в UniformConvergence.v (и, в другой записи, в analysis/Continuity.v).' });
  Object.assign(find((r) => norm(r.claim).startsWith('Сходимость процесса *позиций* максимума: над $ℚ$ `argmax_process`'), 'итог о позициях'), {
    theorem: 'argmax_process_need_not_be_Cauchy', file: ANC,
    claim: 'Сходимость процесса *позиций* максимума: над $ℚ$ `argmax_process` не обязан быть Коши (контрпример — `argmax_process_need_not_be_Cauchy`) — доказана сходимость лишь процесса *значений*.',
    note: DONE + ' — к словам добавлена теорема-контрпример.' });
  Object.assign(find((r) => norm(r.claim).startsWith('интегралом и производной (остальная часть `Uniform Convergence.v`)'), 'остальная часть UniformConvergence'), {
    file: UC,
    claim: 'интегралом (остальная часть `UniformConvergence.v`) — материал одной из последующих глав.', verdict: 'ok',
    note: DONE + ': имя файла было разорвано переносом строки; собрано. Слова «и производной» сняты: теоремы об обмене предела с производной в файле нет.' });
  // новые имена
  const add = (rec) => { if (!j.records.some((r) => r.theorem === rec.theorem && norm(r.claim) === norm(rec.claim))) j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); };
  add({ theorem: 'EVT_idx_majorant', file: IDX,
    claim: 'и всякое значение функции на отрезке в конце концов не превосходит значения процесса с любым зазором (`EVT_idx_majorant`).',
    note: 'Новая теорема шага 10: a < b -> uniformly_continuous_on f a b -> forall x из отрезка, forall eps > 0, exists N, forall n > N, f x <= sup_process f a b n + eps. Closed under the global context.' });
  fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
  console.log('part05-ch03.json: дополнительно изменено 7, всего ' + j.records.length);
}
const b = open('sverka-2026-11-12/V-3.json');
b.set('`process_IVT`, как и теорема `IVT_ERR`, доказана без допущений', {
  claim: '`process_IVT`, как и теорема `IVT_process`, доказана без допущений' });
b.save();
