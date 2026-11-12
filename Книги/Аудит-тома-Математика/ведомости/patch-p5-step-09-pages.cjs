// Часть V, шаг 9, страницы (2026-11-12, слово автора «Да — вносим двенадцать мест»): глава V.2, строки 10–16.
// Запуск: node patch-p5-step-09-pages.cjs   (затем tom-links.cjs relocate + merge по ведомости главы V.2)
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 12.11 (Часть V, шаг 9, слово автора)';
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
const RPT = 'src/RealPointTopology.v', QN = 'src/QIntervalNotCompact.v', BW = 'src/analysis/BolzanoWeierstrass.v';
set('Этот слой над $ℚ$ строится *полностью и конструктивно*. Опорные файлы топологического слоя', {
  claim: 'Этот слой над $ℚ$ строится *полностью и конструктивно*. Опорные файлы топологического слоя — `Topology.v`, `ProcessTopOpen.v`, `ProcessTopConnected.v` — не используют ни одной аксиомы.' });
set('`ProcessTop Connected.v`', {
  claim: '`ProcessTopConnected.v` — не используют ни одной аксиомы.', file: 'src/process/ProcessTopConnected.v', verdict: 'ok',
  note: DONE + ': имя файла было разорвано переносом строки («ProcessTop Connected.v»); собрано на одной строке.' });
set('Опорных файлов одиннадцать — шесть основных и пять', {
  claim: 'Опорных файлов одиннадцать — семь основных и четыре процессные обёртки и сводки; к ним — файл аксиом `ToS_Axioms.v` и файл контрпримера `QIntervalNotCompact.v`, на который опирается сноска 2; все сверены с репозиторием дословно.',
  verdict: 'ok',
  note: DONE + ': было «шесть основных и пять вспомогательных process-обёрток» при двенадцати названных файлах. Основные: Topology, ProcessTopOpen, ProcessTopConnected, RealPointTopology, HeineBorel_ERR, HeineBorelComplete, BolzanoWeierstrass; обёртки и сводки: ProcessBW, ProcessTopCompact, ProcessTopUnified, ProcessCompactness.' });
set('там определён открытый шар на классах `rp_in_ball`', {
  claim: 'там определён шар на классах `rp_in_ball` — замкнутый, расстояние до центра не больше радиуса (центр — точка, радиус — рациональное)',
  verdict: 'ok',
  note: DONE + ': было «открытый шар» — rp_in_ball c r x := cauchy_le (rp_dist c x) (cauchy_const r), шар замкнутый (rp_in_ball_contains_boundary: точка на расстоянии ровно 1 принадлежит шару радиуса 1). Открытый шар добавлен отдельно — rp_in_open_ball.' });
set('Здесь и вступает `L3_ informative`', {
  claim: 'Здесь и вступает `L3_informative` — информативная форма закона исключённого третьего', verdict: 'ok',
  note: DONE + ': имя было разорвано переносом строки («L3_ informative»); собрано на одной строке.' });
set('`L3_informative` и `classic` — технические Rocq-реализации $L3$.', {
  claim: '`classic` — техническая Rocq-реализация $L3$, а `L3_informative` получена из неё извлечением свидетеля — `L4_witness`. Здесь и входит $L4$',
  page_price: 'classic (L3) и L4_witness (L4)', verdict: 'ok',
  note: DONE + ': было «L3_informative и classic — технические Rocq-реализации L3» — Print Assumptions L3_informative: Classical_Prop.classic и ToS_Axioms.L4_witness (значение извлекается командой destruct (L4_witness _ Hex), ToS_Axioms.v). Место входа L4 в бисекцию теперь названо; bw_step_is_gen_step показывает, что допущения входят только через этот выбор.' });
set('Остальные свойства бисекции конструктивны и отработаны подробно', {
  claim: 'Остальные свойства бисекции отработаны подробно: каждый шаг сохраняет вложенность и «населённость» выбранной половины, ширина после $n$ шагов не превосходит $(b-a)/2^n$ и — через архимедовость (`bw_width_to_zero`) — стремится к нулю, а левые и правые концы образуют процессы Коши.',
  page_price: '', verdict: 'ok',
  note: DONE + ': было «конструктивны» — у лемм о bw_iter в допущениях classic и L4_witness (унаследованы от шага bw_step). Слово снято; рядом названо, что от выбора не зависит и доказано без допущений (gen_step_nested, gen_step_width).' });
set('Три формулировки об одном; в `ProcessTopCompact.v` их единство закреплено', {
  claim: 'Три формулировки глава читает как одно; в `ProcessTopCompact.v` они стоят рядом в теореме-конъюнкции `p4_compactness_summary`',
  verdict: 'ok',
  note: DONE + ': было «их единство закреплено теоремой» — p4_compactness_summary есть конъюнкция трёх независимых утверждений (interval_compact; ограниченная возрастающая цепь стабилизируется; стабилизировавшаяся цепь даёт процесс Коши). Довести формализацию до прежних слов нельзя: общего объекта у утверждений нет.' });
set('а `compact_eq_noetherian` и `compact_eq_hb` связывают их попарно', {
  claim: '`compact_eq_noetherian` — нётеровость вместе с её следствием для процессов.',
  verdict: 'ok',
  note: DONE + ': было «связывают их попарно» — compact_eq_noetherian : forall B, (цепь, ограниченная B, стабилизируется) /\\ (она же даёт процесс Коши); о покрытиях в утверждении ничего нет.' });
set('`compact_eq_hb` связывают их попарно', {
  claim: '`compact_eq_hb` повторяет Гейне–Бореля в терминах `interval_compact`',
  verdict: 'ok',
  note: DONE + ': было «связывают их попарно» — compact_eq_hb : a < b -> interval_compact a b, то есть сама теорема Гейне — Бореля.' });
set('Классический Гейне–Борель без оговорки о равномерности — он над $ℚ$ *ложен*', {
  theorem: 'classical_Heine_Borel_fails_over_Q', file: QN,
  claim: 'Классический Гейне–Борель без оговорки о равномерности — он над $ℚ$ *ложен*, и это математический факт, а не пробел: теорема `classical_Heine_Borel_fails_over_Q`.',
  note: DONE + ' — к словам добавлена теорема: ~ (forall C a b, a < b -> valid_cover C a b -> exists centers, covers_interval C centers a b), в определениях HeineBorel_ERR.v; свидетель — покрытие C_gap. Closed under the global context.' });
set('(Базис метрической топологии на классах — открытый шар `rp_in_ball` с корректностью', {
  claim: '(Базис метрической топологии на классах — шары `rp_in_ball` (замкнутый) и `rp_in_open_ball` (открытый) с корректностью — построен отдельно, в `RealPointTopology.v`; см. § 2.2.3.)',
  verdict: 'ok', note: DONE + ': было «открытый шар rp_in_ball» — он замкнутый; названы оба шара.' });
set('компактность интервала — инструмент, на котором будут стоять', {
  claim: 'теоремы о промежуточном значении и об экстремуме пойдут там собственным путём — бисекцией и сеткой, — потому что на компактность над $ℚ$ опереться нельзя.',
  verdict: 'ok',
  note: DONE + ': было «компактность интервала — инструмент, на котором будут стоять теоремы…» — файлы IVT_ERR, IVT_CauchyReal, EVT_idx, EVT_ERR, ProcessIVT, ProcessEVT не подключают ни HeineBorel_ERR, ни HeineBorelComplete, ни BolzanoWeierstrass (проверено поиском).' });
set('На фактор-классах `RealPoint` построен *базис* метрической топологии — открытый шар', {
  claim: 'На фактор-классах `RealPoint` построен *базис* метрической топологии — шары `rp_in_ball` (замкнутый) и `rp_in_open_ball` (открытый) с корректностью (`RealPointTopology.v`, § 2.2.3)',
  verdict: 'ok', note: DONE + ': было «открытый шар rp_in_ball» — он замкнутый; названы оба шара.' });
set('Эта конкретная конструкция теперь и машинно проверена', {
  theorem: 'C_gap_no_finite_subcover', file: QN,
  claim: 'А конструкция главы — радиус, мельчающий у разреза, — записана в определениях самой теоремы Гейне–Бореля: у покрытия `C_gap` с радиусом $\\min(1,|x^2-2|)/8$ конечного подпокрытия нет (`C_gap_no_finite_subcover`), и потому классический Гейне–Борель над $ℚ$ ложен (`classical_Heine_Borel_fails_over_Q`).',
  verdict: 'ok',
  note: DONE + ': было «Эта конкретная конструкция теперь и машинно проверена» — проверена была родственная конструкция (семейство U_k), а открытость U_k стояла в комментарии. Добавлены U_open и конструкция главы в определениях HeineBorel_ERR.v: C_gap, C_gap_no_finite_subcover, classical_Heine_Borel_fails_over_Q. Closed under the global context.' });
set('Вместе — `Q_interval_not_compact`; свидетелем служат Pell-приближения', {
  claim: 'Вместе — `Q_interval_not_compact`; свидетелем служат Pell-приближения $\\sqrt2$.',
  note: 'Q_interval_not_compact — Closed under the global context. После шага 9 Части V в файле 15 Qed, 0 аксиом (на странице число приведено).' });
// новые имена
add({ theorem: 'rp_open_ball_is_open', file: RPT,
  claim: 'он тоже корректен на классах и *открыт*: вместе с каждой точкой содержит шар положительного радиуса вокруг неё (`rp_open_ball_is_open`).',
  note: 'Новая лемма шага 9: rp_in_open_ball c r x -> exists e, 0 < e /\\ forall y, rp_in_ball x e y -> rp_in_open_ball c r y; корректность на классах — rp_in_open_ball_well_defined. Closed under the global context.' });
add({ theorem: 'gen_step_nested', file: BW,
  claim: 'для бисекции с произвольным выбором они доказаны без допущений (`gen_step_nested`, `gen_step_width`)',
  note: 'Новая лемма шага 9: при bw_left st <= bw_right st шаг с любым выбором половины не выводит концы наружу. Closed under the global context.' });
add({ theorem: 'gen_step_width', file: BW,
  claim: '`gen_step_width`), а шаг `bw_step` — её частный случай',
  note: 'Новая лемма шага 9: ширина после шага с любым выбором половины равна половине прежней. Closed under the global context.' });
add({ theorem: 'bw_step_is_gen_step', file: BW,
  claim: 'с выбором, который называет `L3_informative` (`bw_step_is_gen_step`).',
  page_price: 'выбор — по L3_informative',
  note: 'Новая лемма шага 9: bw_step s st = gen_step (if L3_informative (bw_step_left s st) then true else false) st. В допущениях classic и L4_witness — они стоят в самой формулировке (bw_step, L3_informative).' });
add({ theorem: 'U_open', file: QN,
  claim: '(открытость — `U_open`)',
  note: 'Новая лемма шага 9: forall k, is_open (U k) в смысле stdlib/Topology.v. Closed under the global context.' });
add({ theorem: 'classical_Heine_Borel_fails_over_Q', file: QN,
  claim: 'и потому классический Гейне–Борель над $ℚ$ ложен (`classical_Heine_Borel_fails_over_Q`). Машинно проверено, 15 Qed, 0 аксиом.',
  page_price: '0 аксиом',
  note: 'Новая теорема шага 9; в файле QIntervalNotCompact.v 15 Qed. Closed under the global context.' });
fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
console.log('part05-ch02.json: изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length);
