// sverka-2026-11-12.cjs -- первые записи базы связей: результаты сверки цены 12.11.2026 по страницам вне Части IV.
// Запуск: node sverka-2026-11-12.cjs  -> пишет ведомости sverka-2026-11-12/*.json; затем каждую внести:
//   node ../tools/tom-links.cjs merge <ведомость>
// Вердикт этих записей относится к ЦЕНЕ (то, что сверялось 12.11); формулировки сверяются при аудите своей части.
// Записи по главам IV.4, IV.5, IV.6 идут в ведомостях аудита Части IV (part04-ch0N.json).
const fs = require('fs'); const path = require('path');
const out = path.join(__dirname, 'sverka-2026-11-12'); fs.mkdirSync(out, { recursive: true });
const NOTE = 'сверена цена; формулировка — при аудите части';
const FIX = 'исправлено 12.11; ' + NOTE;
const UIU = { theorem: 'unit_interval_uncountable_trisect_v2', file: 'src/ShrinkingIntervals_ERR.v' };
const PCH = { theorem: 'process_continuum_hypothesis', file: 'src/ProcessContinuumHypothesis.v' };
const BPNE = { theorem: 'binary_processes_not_enumerable', file: 'src/ProcessDiagonal.v' };
const pages = [
  { name: 'III-4', chapter: '03 От натуральных к рациональным/04 От позиции к процессу.md', records: [
    { ...UIU, claim: 'по `Print Assumptions` замкнуты — аксиома `classic` в их доказательствах не применяется', page_price: 'без допущений', verdict: 'ok', note: FIX },
    { theorem: 'shrinking_interval_Cauchy', file: 'src/ShrinkingIntervals_ERR.v', claim: 'теоремы файла, на которые ссылается глава (`shrinking_interval_Cauchy`)', page_price: 'без допущений', verdict: 'ok', note: FIX + '; одноимённая теорема есть и в Archimedean_ERR.v:158, тоже без допущений' },
  ] },
  { name: 'V-2', chapter: '05 Топология и анализ процессов/02 Топология и компактность.md', records: [
    { theorem: 'Heine_Borel', file: 'src/HeineBorel_ERR.v', claim: 'восстановленная теорема Гейне–Бореля в\n`HeineBorel_ERR.v` доказана без допущений (§ 2.5)', page_price: 'без допущений', verdict: 'ok', note: FIX },
    { theorem: 'not_coverable_half', file: 'src/HeineBorel_ERR.v', claim: 'импортирует `ToS_Axioms.v` и эта лемма пользуется `classic`', page_price: 'classic (L3)', verdict: 'ok', note: NOTE + '; теоремы Гейне — Бореля от этой леммы не зависят' },
    { theorem: 'Heine_Borel_uniform', file: 'src/HeineBorel_ERR.v', claim: 'для `Heine_Borel` и `Heine_Borel_uniform`\nкоманда `Print Assumptions` отвечает «Closed under the global\ncontext» — допущений нет', page_price: 'без допущений', verdict: 'ok', note: FIX },
    { theorem: null, file: 'src/analysis/BolzanoWeierstrass.v', claim: 'бисекция Больцано–Вейерштрасса опирается на $L3$ (`classic`, `L3_informative`) и дополнительно — на $L4$ (`L4_witness`)', page_price: 'L3 и L4', verdict: 'not-checked', note: '12.11 не проверялось; очередь — аудит Части V' },
  ] },
  { name: 'V-3', chapter: '05 Топология и анализ процессов/03 Непрерывность.md', records: [
    { theorem: 'IVT_process', file: 'src/IVT_ERR.v', claim: 'Команда `Print Assumptions` для\n`IVT_process` отвечает «Closed under the global context»', page_price: 'без допущений', verdict: 'ok', note: FIX },
    { theorem: null, file: 'src/Archimedean_ERR.v', claim: 'архимедовость $ℚ$, а она доказана конструктивно: в\n`Archimedean_ERR` аксиом нет', page_price: 'в файле аксиом нет', verdict: 'ok', note: FIX + '; в файле нет объявлений Axiom и Parameter' },
    { theorem: 'process_IVT', file: 'src/process/ProcessIVT.v', claim: '`process_IVT`, как и теорема `IVT_ERR`, доказана без допущений', page_price: 'без допущений', verdict: 'ok', note: FIX },
    { theorem: 'ivt_cauchy_real', file: 'src/IVT_CauchyReal.v', claim: 'Теорема о промежуточном значении доказана без допущений (`IVT_process`, `process_IVT`, `ivt_cauchy_real`)', page_price: 'без допущений', verdict: 'ok', note: FIX },
    { theorem: 'EVT_strong_process', file: 'src/EVT_idx.v', claim: 'теорема об экстремуме — на $L3$: `classic` приходит в `EVT_ERR` и `EVT_idx` напрямую', page_price: 'classic (L3)', verdict: 'ok', note: 'цена сверена при заведении базы (12.11 не проверялось): аксиома `EVT_idx.classic`, объявленная в самом файле; формулировка — при аудите Части V' },
  ] },
  { name: 'X-2', chapter: '10 Теория множеств без аксиомы выбора/02 Счётность конструктивна; несчётность — правило о процессах.md', records: [
    { ...BPNE, claim: '`binary_processes_not_enumerable` и `cantor_for_processes` доказываются\nчистым применением 0-аксиомной `diagonal_differs`, без L3', page_price: '0 аксиом', verdict: 'ok', note: NOTE },
    { theorem: 'cantor_for_processes', file: 'src/ProcessDiagonal.v', claim: 'Над\n$2^{ℕ}$ всё конструктивно, включая квантор $\\forall f$', page_price: '0 аксиом', verdict: 'ok', note: NOTE },
    { theorem: 'diagonal_differs', file: 'src/ProcessDiagonal.v', claim: '(`diagonal_differs`, 0 аксиом на шаге)', page_price: '0 аксиом', verdict: 'ok', note: NOTE },
    { ...UIU, claim: 'Несчётность $[0,1]$: `unit_interval_uncountable_trisect_v2` (`ShrinkingIntervals_ERR.v`) — `Print Assumptions` даёт «Closed under the global context».', page_price: 'без допущений', verdict: 'ok', note: FIX },
    { ...PCH, claim: 'Дихотомия: `process_continuum_hypothesis` (`ProcessContinuumHypothesis.v`) — `classic` (L3) и `L4_witness`.', page_price: 'classic (L3) и L4_witness', verdict: 'ok', note: FIX },
    { theorem: null, file: 'src/Countability_Q.v', claim: '`Countability_Q.v` даже не подключает\nклассическую логику', page_price: '0 аксиом', verdict: 'ok', note: 'в файле нет импорта классического модуля (шапка: «AXIOMS: NONE»); теоремы файла — при аудите Части X' },
  ] },
  { name: 'X-6', chapter: '10 Теория множеств без аксиомы выбора/06 Синтез Части X что доказуемо без выбора, и карта границ.md', records: [
    { ...UIU, claim: '| 0 аксиом | счётность ℚ (Калкин–Уилф); диагональ (`diagonal_differs`); несчётность $[0,1]$ (трисекция)', page_price: 'ярус «0 аксиом»', verdict: 'ok', note: 'исправлено 12.11 (перенесено из яруса classic); ' + NOTE },
    { theorem: 'kruskal_chains', file: 'src/settheory/KruskalTree.v', claim: 'Кантор–Бендиксон; Крускал (конкретные семейства)', page_price: 'ярус «0 аксиом»', verdict: 'ok', note: 'исправлено 12.11 (перенесено из яруса classic); `kruskal_forks` (KruskalTree.v:276) — тоже без допущений' },
    { theorem: 'S_finite_scattered', file: 'src/settheory/CantorBendixsonFull.v', claim: 'общий Кантор $X\\to(X\\to\\mathtt{bool})$; Кантор–Бендиксон', page_price: 'ярус «0 аксиом»', verdict: 'ok', note: 'речь о производной множества в CantorBendixsonFull.v (не о процессной континуум-гипотезе главы IV.5); `CB_omega_finite_empty`, `CB_omega_accumulation_in_parent` — тоже без допущений' },
    { theorem: null, file: 'src/settheory/HigmanLemma.v', claim: '| classic (L3) | Хигман; конечная детерминированность |', page_price: 'classic (L3)', verdict: 'not-checked', note: '12.11 не проверялось; сводная страница «Формализация» для `higman_unit` называет «нет», для `dickson_pair` — исключённое третье: сверить при аудите Части X' },
  ] },
  { name: 'XV-3', chapter: '15 Вычисления и граница финитизации/03 Одна диагональ halting, Райс, Кантор, Колмогоров.md', records: [
    { ...BPNE, claim: 'Несчётность — `ProcessDiagonal.binary_processes_not_enumerable` и `ShrinkingIntervals_ERR.unit_interval_uncountable_trisect_v2`: 0 аксиом', page_price: '0 аксиом', verdict: 'ok', note: FIX },
    { ...UIU, claim: 'Так же без допущений доказана и несчётность отрезка — и над двоичными\nпроцессами, и в трисекционной версии над $[0,1]$', page_price: 'без допущений', verdict: 'ok', note: FIX },
    { ...PCH, claim: 'Дихотомия завершённой стороны — `ProcessContinuumHypothesis.process_continuum_hypothesis`: слой L3 (classic)${}+{}$L4', page_price: 'L3 (classic) + L4', verdict: 'ok', note: NOTE },
  ] },
  { name: 'XV-7', chapter: '15 Вычисления и граница финитизации/07 Синтез одна диагональ, один дискриминант.md', records: [
    { ...PCH, claim: '**classic (L3)${}+{}$L4 — только одна грань.**  *Дихотомия завершённого\nконтинуума*', page_price: 'classic (L3) + L4', verdict: 'ok', note: FIX },
    { ...UIU, claim: 'Кантор-над-предикатами и сама несчётность отрезка classic *не* требуют', page_price: 'без classic', verdict: 'ok', note: FIX },
  ] },
  { name: 'XX-1', chapter: '20 Заключительный синтез/01 Граница финитизации.md', records: [
    { ...UIU, claim: 'Сама\nнесчётность отрезка доказана без допущений.', page_price: 'без допущений', verdict: 'ok', note: FIX },
    { ...PCH, claim: 'дихотомия замкнутых совокупностей процессов в текущей формализации\n*наследуют* Закон Исключённого Третьего ($L3$) и связанный свидетельный параметр', page_price: 'L3 и свидетельный параметр (L4_witness)', verdict: 'ok', note: FIX },
    { theorem: null, file: null, claim: 'спектральная дихотомия и дихотомия замкнутых совокупностей процессов', page_price: 'L3 и свидетельный параметр', verdict: 'not-checked', note: 'спектральная дихотомия 12.11 не проверялась; очередь — аудит Части XX' },
  ] },
  { name: 'XX-6', chapter: '20 Заключительный синтез/06 Что доказано, что наблюдение, что горизонт.md', records: [
    { ...UIU, claim: 'сама несчётность отрезка доказана без допущений', page_price: 'без допущений', verdict: 'ok', note: FIX },
  ] },
  { name: 'Формализация', root: 'library', chapter: 'Формализация.md', records: [
    { ...UIU, claim: '`unit_interval_uncountable_trisect_v2` (ShrinkingIntervals_ERR.v) | нет |', page_price: 'нет', verdict: 'ok', note: NOTE },
    { ...BPNE, claim: '`binary_processes_not_enumerable` (ProcessDiagonal.v) | нет |', page_price: 'нет', verdict: 'ok', note: NOTE },
    { ...PCH, claim: '`process_continuum_hypothesis` (ProcessContinuumHypothesis.v) | исключённое третье (стандартная библиотека), извлечение свидетеля', page_price: 'исключённое третье (стандартная библиотека), извлечение свидетеля', verdict: 'ok', note: NOTE },
    { theorem: 'IVT_process', file: 'src/IVT_ERR.v', claim: '`IVT_process` (IVT_ERR.v); `ivt_cauchy_real` (IVT_CauchyReal.v) | нет |', page_price: 'нет', verdict: 'ok', note: NOTE },
    { theorem: 'ivt_cauchy_real', file: 'src/IVT_CauchyReal.v', claim: '`ivt_cauchy_real` (IVT_CauchyReal.v) | нет |', page_price: 'нет', verdict: 'ok', note: NOTE },
    { theorem: 'Heine_Borel', file: 'src/HeineBorel_ERR.v', claim: '`Heine_Borel` (HeineBorel_ERR.v) | нет |', page_price: 'нет', verdict: 'ok', note: NOTE },
    { theorem: 'kruskal_chains', file: 'src/settheory/KruskalTree.v', claim: '`kruskal_chains`, `kruskal_forks` (KruskalTree.v)', page_price: 'нет', verdict: 'ok', note: NOTE },
    { theorem: 'kruskal_forks', file: 'src/settheory/KruskalTree.v', claim: '`kruskal_forks` (KruskalTree.v)', page_price: 'нет', verdict: 'ok', note: NOTE },
    { theorem: 'depth1_wqo', file: 'src/settheory/KruskalFull.v', claim: '`depth1_wqo`, `L5_from_kruskal` (KruskalFull.v) | нет |', page_price: 'нет', verdict: 'ok', note: NOTE },
    { theorem: 'L5_from_kruskal', file: 'src/settheory/KruskalFull.v', claim: '`L5_from_kruskal` (KruskalFull.v) | нет |', page_price: 'нет', verdict: 'ok', note: NOTE },
    { theorem: 'EVT_strong_process', file: 'src/EVT_idx.v', claim: '`EVT_strong_process` (EVT_idx.v) | исключённое третье (EVT_idx.v) |', page_price: 'исключённое третье (EVT_idx.v)', verdict: 'ok', note: 'цена сверена при заведении базы (12.11 не проверялось): `EVT_idx.classic`; формулировка — при аудите Части V' },
  ] },
  { name: 'Математика-index', root: 'library', chapter: 'Направления/Математика/index.md', records: [
    { ...UIU, claim: 'Несчётность и промежуточное значение доказаны без допущений, экстремум — с исключённым третьим', page_price: 'без допущений', verdict: 'ok', note: NOTE },
    { theorem: 'IVT_process', file: 'src/IVT_ERR.v', claim: 'Несчётность и промежуточное значение доказаны без допущений', page_price: 'без допущений', verdict: 'ok', note: NOTE },
    { theorem: 'EVT_strong_process', file: 'src/EVT_idx.v', claim: 'экстремум — с исключённым третьим', page_price: 'исключённое третье', verdict: 'ok', note: 'цена сверена при заведении базы (12.11 не проверялось): `EVT_idx.classic`' },
  ] },
];
for (const p of pages) {
  const rv = { batch: 'sverka-2026-11-12', chapter: p.chapter, checked: '2026-11-12', auto: false, records: p.records };
  if (p.root) rv.root = p.root;
  fs.writeFileSync(path.join(out, p.name + '.json'), JSON.stringify(rv, null, 1) + '\n');
}
console.log('ведомостей: ' + pages.length + ', записей: ' + pages.reduce((a, p) => a + p.records.length, 0));
