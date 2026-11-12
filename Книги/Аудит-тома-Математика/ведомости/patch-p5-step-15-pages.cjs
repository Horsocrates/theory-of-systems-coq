// Часть V, шаг 15, страницы (2026-11-12, слово автора «А — снимаем, вносим четырнадцать мест»): глава V.7.
// Запуск: node patch-p5-step-15-pages.cjs   (затем tom-links.cjs relocate + merge по ведомости главы V.7)
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 12.11 (Часть V, шаг 15, слово автора)';
const norm = (s) => (s || '').replace(/\s+/g, ' ');
const p = path.join(__dirname, 'part05-ch07.json');
const j = JSON.parse(fs.readFileSync(p, 'utf8'));
let n = 0, added = 0;
function set(prefix, fields) {
  const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix));
  if (hit.length !== 1) throw new Error('ожидалась одна запись «' + prefix + '», найдено ' + hit.length);
  Object.assign(hit[0], fields); n++;
}
function add(rec) {
  if (j.records.some((r) => r.theorem === rec.theorem && norm(r.claim) === norm(rec.claim))) return;
  j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); added++;
}
const FP = 'src/analysis/FubiniProcess.v', DC = 'src/analysis/DominatedConvergence.v', HB = 'src/analysis/HeineBorelComplete.v',
  PFG = 'src/process/ProcessFubiniGeneral.v', SI = 'src/analysis/StepIntegral.v';
set('Но именно этот скромный уровень показывает *первый закон порядка наблюдения*', {
  theorem: 'integral_2d_perm', file: FP, verdict: 'ok',
  note: DONE + ' — слова те же, доведена формализация: о перестановке вкладов леммы не было (менялся только порядок сомножителей внутри вклада). Добавлена integral_2d_perm : Permutation f g -> integral_2d f == integral_2d g (и integral_2d_app_comm, fubini_step_perm). Closed under the global context.' });
set('Повторный интеграл по одному прямоугольнику можно взять в двух порядках', {
  claim: 'Повторный интеграл по одному прямоугольнику можно взять в двух порядках: сперва по $x$, потом по $y$ — или наоборот. На прямоугольном вкладе каждый из них сводится к готовому произведению; ToS записывает оба сразу в этом виде и доказывает их равенство.',
  verdict: 'ok',
  note: DONE + ': было «ToS записывает оба» — iterated_xy и iterated_yx суть одно произведение с двумя порядками сомножителей (iterated_xy совпадает с rect_integral по определению). Слова приведены к этому; повторный интеграл из двух одномерных построен отдельно (nested_xy, nested_yx).' });
set('порядок сложения вкладов и порядок интегрирования внутри вклада', {
  theorem: 'integral_2d_perm', file: FP,
  claim: 'порядок сложения вкладов (`integral_2d_perm`) и порядок интегрирования внутри вклада — оба безразличны.',
  verdict: 'ok',
  note: DONE + ': к словам о порядке сложения вкладов добавлена лемма, которой раньше не было.' });
set('Доказанное `fubini_step` — конечный **прототип** закона порядка', {
  claim: 'Доказанное `fubini_step` — конечный **прототип** закона порядка; настоящая Фубини начинается за ним. Между ступенью и пределом есть ещё одна доказанная ступень — перестановка двойной суммы на произвольной конечной сетке (§ 7.5).*' });
set('Файл `StepIntegral.v` (20 Qed, 0 аксиом)', {
  file: SI,
  claim: 'Файл `StepIntegral.v` (17 Qed, 0 аксиом) даёт точный интеграл ступенчатых функций над ℚ',
  verdict: 'ok', note: DONE + ': в файле 17 Qed (в шапке стояло 20; исправлено шагом 12).' });
set('`DominatedConvergence.v` (20 Qed, 0 аксиом)', {
  file: DC,
  claim: '`DominatedConvergence.v` (26 Qed, 0 аксиом)',
  note: DONE + ': после шага 15 в файле 26 Qed (добавлено восемь утверждений, сняты теорема-вывеска dominated_convergence_step и пример example_dct); все утверждения — Closed under the global context.' });
set('даёт основания *ступенчатого* уровня: доминирование, $L^1$-сходимость, сходимость интегралов, скелет', {
  theorem: 'l1_convergence_integral', file: DC,
  claim: 'даёт основания *ступенчатого* уровня: доминирование, $L^1$-сходимость, сходимость интегралов — и теорему, которая на этом уровне действительно верна: на общем разбиении $L^1$-сходимость влечёт сходимость интегралов (`l1_convergence_integral`',
  verdict: 'ok',
  note: DONE + ': было «скелет теоремы о доминированной сходимости» — заключение dominated_convergence_step дословно повторяло третью посылку, мажоранта не работала; теорема снята (вариант А, слово автора). Добавлена l1_convergence_integral : (forall n, aligned (seq n) limit) -> l1_converges seq limit -> integral_converges seq (step_fun_integral limit). Closed under the global context.' });
set('Файл сам честно отмечает, что на ступенчатом уровне эта теорема почти тривиальна', {
  theorem: 'l1_convergence_alone_is_not_enough', file: DC,
  claim: 'Без общего разбиения это неверно, и контрпример проверен (`l1_convergence_alone_is_not_enough`). Мажоранта на общем конечном разбиении ничего не добавляет; её содержание возникает при переходе к $L^1$-пополнению.',
  verdict: 'ok',
  note: DONE + ': было — довод файла «L1-сходимость уже влечёт сходимость интегралов» в его определениях без общего разбиения неверен (step_fun_diff обрезает списки по более короткому). Контрпример внесён теоремой; заметка в конце файла исправлена.' });
set('*Компактность — с ограничением ℚ.* Файл `HeineBorelComplete.v` (22 Qed, 0 аксиом)', {
  file: HB,
  claim: '*Компактность — с ограничением ℚ.* Файл `HeineBorelComplete.v` (28 Qed; собственных аксиом нет',
  verdict: 'ok', note: DONE + ': в файле 28 Qed (в шапке стояло 22; шапка исправлена).' });
set('`HeineBorelComplete.v` (22 Qed, 0 аксиом)', {
  claim: 'одна лемма — `mono_bounded_is_cauchy` — опирается на $L3$, см. Главу 5.2)',
  page_price: 'L3 (classic) у одной леммы',
  verdict: 'ok',
  note: DONE + ': было «0 аксиом» — mono_bounded_is_cauchy стоит на Classical_Prop.classic; остальные 27 утверждений закрыты. Цена названа.' });
set('Итак, непрерывная Фубини есть *программа*, не теорема: каркас трёх', {
  claim: 'Итак, непрерывная Фубини есть *программа*, не теорема. Равенство двух порядков доказано на каждой конечной сетке; открытым остаётся шаг к пределу — сходимость сеточных сумм непрерывной функции к двойному интегралу',
  verdict: 'ok',
  note: DONE + ': было — непрерывный случай назван программой целиком; равенство порядков на любой конечной сетке доказано (ProcessFubiniGeneral.v: q_sum_swap, fubini_iterated_eq), открыта только сходимость к двойному интегралу (горизонт; не доказана и не пробовалась).' });
set('В рабочей карте формализации (см. итог тома) эта задача стоит явным пунктом.', {
  claim: 'В рабочем списке задач формализации он стоит отдельным пунктом: равенство порядка на конечной сетке закрыто, сходимость к двойному интегралу открыта.',
  verdict: 'ok',
  note: DONE + ': было «в рабочей карте формализации (см. итог тома)» — в Части XX пункта нет; он стоит в рабочем списке вне тома (Книги/FORMALIZATION-BACKLOG.md, F-1).' });
set('ToS построит там интегрирование *без внешней сет-теоретической аксиомы выбора*', {
  claim: 'ToS строит там интегрирование *без внешней сет-теоретической аксиомы выбора*, с явной локальной маркировкой $L3$ и $L4$ там, где они понадобятся. Непрерывная Фубини и после Части VI остаётся программой: её предельный шаг в формализации ещё не собран.',
  verdict: 'ok',
  note: DONE + ': было «и тогда непрерывная Фубини … получит своё полное доказательство» — в Части VI теорема упомянута только отсылками назад, доказательства нет.' });
set('Доказан ступенчатый прототип; непрерывный случай — программа на трёх условиях', {
  theorem: 'fubini_iterated_eq', file: PFG,
  claim: 'Доказаны ступенчатый прототип и равенство повторных сумм на произвольной конечной сетке (`fubini_iterated_eq`); сходимость к двойному интегралу для непрерывной функции — программа на трёх условиях',
  verdict: 'ok',
  note: DONE + ': итог приведён к действительному состоянию: fubini_iterated_eq : forall f wx wy N M, iter_xy f wx wy N M == iter_yx f wx wy N M. Closed under the global context.' });
set('ступенчатая Фубини есть её конечный прототип, а полное доказательство ждёт меры Части VI.', {
  claim: 'ступенчатая Фубини есть её конечный прототип, а полное доказательство остаётся горизонтом — за пределами доказанного в этом томе.',
  verdict: 'ok', note: DONE + ': было «полное доказательство ждёт меры Части VI» — Часть VI его не даёт; назван горизонт.' });
set('Опорный файл — `FubiniProcess.v` Rocq-репозитория ToS', {
  file: FP,
  claim: 'Опорный файл — `FubiniProcess.v` Rocq-репозитория ToS (каталог `src/analysis/`), 30 доказанных утверждений, 0 `Admitted`, 0 аксиом. Имена, приводимые ниже, — из него.',
  note: DONE + ': после шага 15 в файле 30 Qed (было 20); все утверждения — Closed under the global context.' });
set('В предварительном плане главы доказательство непрерывного случая было ошибочно отнесено', {
  file: FP,
  claim: 'Отдельного файла для непрерывного случая в формализации нет; опорный файл главы — `FubiniProcess.v` — доказывает ступенчатый случай',
  verdict: 'ok', note: DONE + ': сноска переписана — имя несуществующего файла Fubini.v убрано.' });
set('фактический файл — `FubiniProcess.v` — доказывает ступенчатый случай. Здесь это исправлено.', {
  file: PFG,
  claim: 'а `ProcessFubiniGeneral.v` — равенство повторных сумм на произвольной конечной сетке.',
  note: 'Файл существует (src/process/ProcessFubiniGeneral.v, 8 Qed); сноска переписана шагом 15 Части V.' });
// новые имена
add({ theorem: 'nested_xy_eq_iterated', file: FP,
  claim: 'доказано отдельно (`nested_xy_eq_iterated`, `nested_yx_eq_iterated`)',
  note: 'Новая лемма шага 15: nested_xy r == iterated_xy r, где nested_xy — интеграл по y от ступени, значение которой есть одномерный step_integral сечения по x. Closed under the global context.' });
add({ theorem: 'nested_yx_eq_iterated', file: FP,
  claim: '`nested_yx_eq_iterated`), как и равенство',
  note: 'Новая лемма шага 15 (то же для порядка «сперва y, потом x»). Closed under the global context.' });
add({ theorem: 'fubini_rectangle_nested', file: FP,
  claim: 'как и равенство двух порядков для них (`fubini_rectangle_nested`).',
  note: 'Новая теорема шага 15: nested_xy r == nested_yx r; для списков — fubini_step_nested. Closed under the global context.' });
add({ theorem: 'l1_cauchy_integral_cauchy', file: DC,
  claim: 'для последовательностей Коши — `l1_cauchy_integral_cauchy`)',
  note: 'Новая теорема шага 15: (forall m n, aligned (seq m) (seq n)) -> l1_cauchy seq -> integral_cauchy seq. Closed under the global context.' });
add({ theorem: 'q_sum_swap', file: PFG,
  claim: 'доказывает перестановку двойной конечной суммы для сетки любого размера $N\\times M$ (`q_sum_swap`)',
  note: 'q_sum_swap : forall (f : nat -> nat -> Q) (N M : nat), dsum_xy f N M == dsum_yx f N M. Closed under the global context.' });
add({ theorem: 'fubini_iterated_eq', file: PFG,
  claim: 'равенство двух повторных сеточных сумм для любой функции, заданной значениями в узлах (`fubini_iterated_eq`).',
  note: 'fubini_iterated_eq : forall f wx wy N M, iter_xy f wx wy N M == iter_yx f wx wy N M. Closed under the global context. Сходимости к двойному интегралу файл не доказывает.' });
fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
console.log('part05-ch07.json: изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length);
