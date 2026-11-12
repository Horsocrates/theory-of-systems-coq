// Часть V, шаг 8, страницы (2026-11-12, слово автора «Да — вносим десять мест»): глава V.2, строки 4–9 таблицы.
// Запуск: node patch-p5-step-08-pages.cjs   (затем tom-links.cjs relocate + merge по ведомости главы V.2)
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 12.11 (Часть V, шаг 8, слово автора)';
const norm = (s) => (s || '').replace(/\s+/g, ' ');
const p = path.join(__dirname, 'part05-ch02.json');
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
const TOP = 'src/stdlib/Topology.v', OPEN = 'src/process/ProcessTopOpen.v', HB = 'src/HeineBorel_ERR.v', CON = 'src/process/ProcessTopConnected.v';
set('`continuous_preserves_open_preimage`: прообраз открытого множества под непрерывным отображением открыт.', {
  claim: '`continuous_preserves_open_preimage`: прообраз открытого множества под непрерывным отображением открыт. Вместе с обратной стороной (`continuous_iff_open_preimage`) это топологическое *определение* непрерывности в эквивалентной форме',
  verdict: 'ok',
  note: DONE + ': было «в эквивалентной форме» при одной доказанной стороне. Добавлены open_preimage_implies_continuous и continuous_iff_open_preimage : continuous f <-> (forall S, is_open S -> is_open (fun x => S (f x))). Closed under the global context.' });
set('«целое» открытого множества потенциально, но всякий его кадр конечен и обозрим', {
  theorem: 'cover_frame_bounded', file: OPEN,
  claim: 'всякий его кадр конечен и обозрим (кадр — конечный список и потому покрывает лишь ограниченное множество: лемма `cover_frame_bounded`)',
  verdict: 'ok',
  note: DONE + ': было «(лемма p4_cover_finite)» — та лемма («список пуст или имеет голову») верна для любого списка. Названа новая cover_frame_bounded : forall bc : QBallCover, exists M, 0 < M /\\ forall x, covered_by_balls bc x -> Qabs x < M. Closed under the global context.' });
set('Существенно, что на каждом уровне покрытие *конечно* — список конечной длины; это устанавливает', {
  claim: 'Существенно, что на каждом уровне покрытие *конечно* — список конечной длины: это дано самим типом кадра (`p4_cover_finite` лишь разворачивает его — список пуст либо имеет голову).',
  verdict: 'ok',
  note: DONE + ': было «это устанавливает лемма p4_cover_finite». p4_cover_finite : op n = nil \\/ exists b rest, op n = cons b rest — верно для любого списка; конечность дана типом QBallCover := list (Q * Q). Слова приведены к этому; содержание конечности — в cover_frame_bounded.' });
set('Радиусы не могут «выдохнуться» — у всех есть общая нижняя граница. Это и есть число Лебега', {
  theorem: 'uniform_cover_has_lebesgue', file: HB,
  claim: 'Такое $\\delta$ служит числом Лебега покрытия — масштабом, на котором покрытие работает *равномерно* по всему интервалу: всякий кусок уже $\\delta$ целиком лежит в одном шаре (лемма `uniform_cover_has_lebesgue`).',
  verdict: 'ok',
  note: DONE + ': было «Это и есть число Лебега» — uniform_cover (все радиусы не меньше delta) сильнее has_lebesgue_number; обратное неверно (пример в пробном файле). Добавлена uniform_cover_has_lebesgue : uniform_cover C a b delta -> has_lebesgue_number C a b delta. Closed under the global context.' });
set('Этот вывод формализован в `HeineBorel_ERR.v` (бисекционный спуск', {
  theorem: 'Heine_Borel_by_depth', file: HB,
  claim: 'формализован в `HeineBorel_ERR.v` (спуск по глубине бисекции — `Qpow2`, `pow2_eventually_large`, `Heine_Borel_by_depth`)',
  verdict: 'ok',
  note: DONE + ': было «(бисекционный спуск — hb_step, Qpow2, Heine_Borel_by_depth)» — hb_step в доказательство Heine_Borel_uniform не входит (Print All Dependencies); названы леммы, на которых вывод стоит.' });
set('При наличии числа Лебега конечное подпокрытие *существует*. Теорема `Heine_Borel`', {
  claim: 'При равномерном покрытии конечное подпокрытие *существует*. Теорема `Heine_Borel` — то же утверждение с гипотезой «найдётся такое $\\delta$».',
  note: DONE + ' — слова уточнены: Heine_Borel : a < b -> valid_cover C a b -> (exists delta, uniform_cover C a b delta) -> exists centers, covers_interval C centers a b; гипотеза — равномерность, а не число Лебега в собственном смысле.' });
set('Доказана *равномерная* версия Гейне–Бореля — для покрытий, обладающих числом Лебега.', {
  theorem: 'Heine_Borel_lebesgue', file: HB,
  claim: 'Доказан Гейне–Борель для покрытий, обладающих числом Лебега (`Heine_Borel_lebesgue`), и его *равномерная* версия (`Heine_Borel_uniform`).',
  note: DONE + ': новая теорема Heine_Borel_lebesgue : a < b -> has_lebesgue_number C a b delta -> exists centers, covers_interval C centers a b; с ней слова «для покрытий, обладающих числом Лебега» верны буквально. Closed under the global context.' });
set('Это честный ремонт: теорема восстановлена на том классе покрытий', {
  claim: 'Это честный ремонт: теорема восстановлена на классе покрытий, для которого она над $ℚ$ заведомо верна; число Лебега — условие достаточное.',
  verdict: 'ok',
  note: DONE + ': было «на том классе покрытий, на котором она вообще верна» — сильнее доказанного: доказано, что числа Лебега достаточно; необходимость не доказана.' });
set('`interval_path_connected` даёт процессную достижимость для замкнутого интервала', {
  verdict: 'ok',
  note: DONE + ': слова те же, цена определения названа рядом новым абзацем: без требования непрерывности достижимо всякое множество (any_set_path_connected); содержание несёт липшицева достижимость (interval_lip_path_connected, two_points_not_lip_path_connected).' });
set('`process_path_cauchy` показывает, что этот процесс есть Коши и сходится', {
  claim: '`process_path_cauchy` показывает, что этот процесс есть Коши, а `process_path_converges` — что он сходится к $b$.',
  verdict: 'ok',
  note: DONE + ': было — оба утверждения приписаны process_path_cauchy, в которой только свойство Коши. Добавлена process_path_converges : forall a b eps, 0 < eps -> exists N, forall n, N <= n -> Qabs (process_path a b n - b) < eps. Closed under the global context.' });
set('Гейне–Борель в равномерной версии (`Heine_Borel_uniform`)', {
  claim: 'Гейне–Борель для покрытий с числом Лебега (`Heine_Borel_lebesgue`) и его равномерная версия (`Heine_Borel_uniform`); доказан бисекцией.',
  note: DONE + ' — итог приведён к двум теоремам: Heine_Borel_lebesgue (число Лебега) и Heine_Borel_uniform (радиусы не меньше delta).' });
// новые имена на странице
add({ theorem: 'continuous_iff_open_preimage', file: TOP,
  claim: 'Вместе с обратной стороной (`continuous_iff_open_preimage`)',
  note: 'Новая теорема шага 8: continuous f <-> (forall S, is_open S -> is_open (fun x => S (f x))). Closed under the global context.' });
add({ theorem: 'cover_frame_bounded', file: OPEN,
  claim: 'Что конечность даёт, говорит лемма `cover_frame_bounded`: конечный кадр покрывает лишь ограниченное множество.',
  note: 'Новая лемма шага 8 (индукция по списку шаров). Closed under the global context.' });
add({ theorem: 'pow2_eventually_large', file: HB,
  claim: '`Qpow2`, `pow2_eventually_large`, `Heine_Borel_by_depth`)',
  note: 'Лемма существует (HeineBorel_ERR.v): для ширины и delta найдётся глубина N с (b - a) / Qpow2 N < delta; на неё опирается Heine_Borel_uniform (и новая Heine_Borel_lebesgue). Closed under the global context.' });
add({ theorem: 'Heine_Borel_lebesgue', file: HB,
  claim: 'А теорема `Heine_Borel_lebesgue` доказывает его и при числе Лебега в собственном смысле (`has_lebesgue_number`: у каждой точки её $\\delta$-окрестность лежит в одном шаре покрытия)',
  note: 'Новая теорема шага 8. has_lebesgue_number C a b delta := delta > 0 /\\ forall x из отрезка, exists c из отрезка, forall y, |y - x| < delta -> covered_by C c y. Доказательство — тот же спуск по глубине (HB_lebesgue_by_depth). Closed under the global context.' });
add({ theorem: 'process_path_converges', file: CON,
  claim: 'а `process_path_converges` — что он сходится к $b$.',
  note: 'Новая лемма шага 8: расстояние до b на шаге n равно |a - b|/(n+1). Closed under the global context.' });
add({ theorem: 'any_set_path_connected', file: CON,
  claim: 'в нём достижимо *всякое* множество (`any_set_path_connected`) — путь вправе перескочить из $a$ в $b$ в последней точке параметра.',
  note: 'Новая лемма шага 8: forall S, is_path_connected S (путь «a при t < 1, b при t = 1»). Closed under the global context.' });
add({ theorem: 'interval_lip_path_connected', file: CON,
  claim: 'интервал связывается липшицевым путём (`interval_lip_path_connected`)',
  note: 'Новая теорема шага 8: lo < hi -> is_lip_path_connected (fun x => lo <= x /\\ x <= hi) — линейным путём с константой |b - a|. Closed under the global context.' });
add({ theorem: 'two_points_not_lip_path_connected', file: CON,
  claim: 'а двухточечное множество $\\{0,1\\}$ — нет (`two_points_not_lip_path_connected`).',
  note: 'Новая теорема шага 8: ~ is_lip_path_connected (fun x => x == 0 \\/ x == 1); по сетке мельче 1/K значения липшицева пути не могут перейти из 0 в 1 (lip_no_jump). Closed under the global context.' });
fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
console.log('part05-ch02.json: изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length);
