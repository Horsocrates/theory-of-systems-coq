// Часть V, шаг 1 (2026-11-12, слово автора «Да — вносим»): теорема об экстремуме без classic.
// Записи семи ведомостей, цитаты которых изменились, приводятся к новым словам страниц.
// Запуск: node patch-p5-step-01.cjs   (затем tom-links.cjs relocate + merge по каждой ведомости)
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 12.11 (Часть V, шаг 1, слово автора)';
const PA = 'после правки формализации 12.11 (x_between_grid_points доказана вычислением; местная Axiom classic из EVT_idx.v снята) Print Assumptions для EVT_strong_process (EVT_idx.v), EVT_complete (EVT_ERR.v) и всей цепочки — Closed under the global context';
const norm = (s) => (s || '').replace(/\s+/g, ' ');

function run(file, edits) {
  const p = path.join(__dirname, file);
  const j = JSON.parse(fs.readFileSync(p, 'utf8'));
  let n = 0;
  for (const e of edits) {
    const hit = j.records.filter((r) => norm(r.claim).startsWith(e.was));
    if (hit.length !== 1) throw new Error(file + ': ожидалась одна запись «' + e.was + '», найдено ' + hit.length);
    Object.assign(hit[0], e.set); n++;
  }
  fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
  console.log(file + ': записей изменено ' + n + ', всего ' + j.records.length);
}

run('part05-ch03.json', [
  { was: 'Доказательство теоремы об экстремуме *использует', set: {
      theorem: 'EVT_strong_process', file: 'src/EVT_idx.v',
      claim: 'Обе большие теоремы этой главы — о промежуточном значении и об экстремуме — как показала проверка `Print Assumptions`, обходятся без допущений.',
      page_price: 'обе теоремы — без допущений', verdict: 'ok',
      note: DONE + ': было «Доказательство теоремы об экстремуме использует аксиому classic»; ' + PA } },
  { was: 'Топологический слой непрерывности и теорема о промежуточном значении', set: {
      claim: 'Топологический слой непрерывности, теорема о промежуточном значении и теорема об экстремуме — без аксиом.',
      page_price: 'без аксиом', verdict: 'ok',
      note: DONE + ': было «теорема об экстремуме — с явно учтённым L3»; ' + PA } },
  { was: 'Аксиомы понадобятся дальше', set: {
      claim: 'Без аксиом обойдутся и две большие теоремы анализа, к которым глава переходит дальше.',
      page_price: 'обе большие теоремы — без аксиом', verdict: 'ok',
      note: DONE + ': было «Аксиомы понадобятся дальше — когда глава перейдёт к двум большим теоремам анализа» (строка 10 таблицы главы V.3 в отчёте 03); IVT_process, ivt_cauchy_real, EVT_strong_process, EVT_complete — Closed under the global context' } },
  { was: '| равномерность как требование', set: {
      claim: '| равномерность как требование (Кантор–Гейне над $ℚ$ неверна) | усиление правила | Rule (неполнота) |',
      page_price: '', verdict: 'ok',
      note: DONE + ': была пометка «Rule (неполнота, L3)» (строка 11 таблицы главы V.3 в отчёте 03); всё названное в строке — без допущений' } },
  { was: 'Файл `EVT_idx.v` устроен в отношении аксиом', set: {
      theorem: 'x_between_grid_points', file: 'src/EVT_idx.v',
      claim: 'Этот поиск вычислим — ячеек конечное число, а сравнение рациональных чисел разрешимо, — и теперь лемма `x_between_grid_points` доказана перебором ячеек, а локальное объявление аксиомы из файла снято.',
      page_price: 'без допущений', verdict: 'ok',
      note: DONE + ': абзац о местной аксиоме переписан; в EVT_idx.v лемма x_between_grid_points доказана через x_between_aux (индукция по числу ячеек, Qlt_le_dec), строки `Axiom classic` в файле больше нет; ' + PA } },
  { was: 'Теорема о промежуточном значении доказана без допущений', set: {
      theorem: 'EVT_complete', file: 'src/EVT_ERR.v',
      claim: 'Теорема о промежуточном значении и теорема об экстремуме доказаны без допущений (`IVT_process`, `process_IVT`, `ivt_cauchy_real`; `EVT_strong_process`, `EVT_complete`): и выбор половины в бисекции, и поиск ячейки сетки вычислимы.',
      page_price: 'IVT и EVT — без допущений', verdict: 'ok',
      note: DONE + ': было «теорема об экстремуме — на L3: classic приходит в EVT_ERR и EVT_idx напрямую»; ' + PA } },
  { was: 'Теорема о промежуточном значении — без допущений; теорема об экстремум', set: {
      claim: 'Теорема о промежуточном значении и теорема об экстремуме — без допущений: выбор половины и поиск ячейки сетки вычислимы.',
      page_price: 'IVT и EVT — без допущений', verdict: 'ok',
      note: DONE + ': было «теорема об экстремуме — на L3, законе исключённого третьего ToS»; ' + PA } },
]);

run('part05-ch04.json', [
  { was: 'Кроме того, `MeanValueTheorem.v` импортирует', set: {
      theorem: null, file: 'src/EVT_idx.v',
      claim: 'Кроме того, `MeanValueTheorem.v` импортирует `EVT_idx.v` (этот файл разбирался в § 5.3; его теоремы допущений не имеют).',
      page_price: 'теоремы EVT_idx.v — без допущений', verdict: 'ok',
      note: DONE + ': было «в EVT_idx.v аксиома classic объявлена локально»; объявление снято; ' + PA } },
  { was: 'Это не значит, что каждая теорема о среднем', set: {
      claim: 'Импорт классического слоя не значит, что каждая теорема о среднем зависит от `classic` — значит лишь, что для конкретной теоремы нужно смотреть `Print Assumptions`.',
      note: DONE + ': начало фразы изменено вслед за предыдущей; все 18 утверждений MeanValueTheorem.v — Closed under the global context' } },
]);

run('part05-ch05.json', [
  { was: 'Ядра — `ProcessIntegral.v`', set: {
      theorem: null, file: 'src/EVT_idx.v',
      claim: 'Ядра — `ProcessIntegral.v`, `RiemannIntegration.v`, `IntegralApplications.v` — в шапках заявляют « none » или « 0 axioms », но импортируют слои, в которых встречается классическая логика: `EVT_idx.v` (подключает `ToS_Axioms.v`; сам допущений не использует, § 5.3) и `ProcessArithmetic.v` (см. ниже).',
      note: DONE + ': было «EVT_idx.v (с локальным classic, из § 5.3)»; EVT_idx.v подключает ToS_Axioms.v, местное объявление аксиомы снято, все его теоремы — Closed under the global context' } },
]);

run('part05-ch06.json', [
  { was: 'Но *некоторые* из этих файлов', set: {
      claim: 'Но *некоторые* из этих файлов импортируют слои, где встречается классическая логика: например, `ProcessArithmetic.v`, где `classic` используется в `monotone_bounded_Cauchy`.',
      note: DONE + ': из примера убран «EVT_idx.v с локальным classic» — объявление снято; monotone_bounded_Cauchy (ProcessArithmetic.v) — Classical_Prop.classic' } },
  { was: '`EVT_idx.v` с локальным', set: {
      theorem: 'monotone_bounded_Cauchy', file: 'src/process/ProcessArithmetic.v',
      claim: '`ProcessArithmetic.v`, где `classic` используется в `monotone_bounded_Cauchy`',
      page_price: 'classic в monotone_bounded_Cauchy', verdict: 'ok',
      note: DONE + ': прежняя запись была о местной аксиоме EVT_idx.v, её на странице больше нет; Print Assumptions monotone_bounded_Cauchy — Classical_Prop.classic' } },
]);

run('sverka-2026-11-12/V-3.json', [
  { was: 'Теорема о промежуточном значении доказана без допущений', set: {
      claim: 'Теорема о промежуточном значении и теорема об экстремуме доказаны без допущений (`IVT_process`, `process_IVT`, `ivt_cauchy_real`',
      note: 'исправлено 12.11 (сверка цены); 12.11 вечером фраза расширена шагом 1 Части V; ivt_cauchy_real — Closed under the global context' } },
  { was: 'теорема об экстремуме — на', set: {
      claim: '`EVT_strong_process`, `EVT_complete`): и выбор половины в бисекции, и поиск ячейки сетки вычислимы.',
      page_price: 'без допущений', verdict: 'ok',
      note: DONE + ': было «теорема об экстремуме — на L3: classic приходит в EVT_ERR и EVT_idx напрямую»; ' + PA } },
]);

run('sverka-2026-11-12/Формализация.json', [
  { was: '`EVT_strong_process` (EVT_idx.v) | исключённое', set: {
      claim: '`EVT_strong_process` (EVT_idx.v) | нет |',
      page_price: 'нет', verdict: 'ok',
      note: DONE + ': было «исключённое третье (EVT_idx.v)»; ' + PA } },
]);

run('sverka-2026-11-12/Математика-index.json', [
  { was: 'Несчётность и промежуточное значение доказаны без допущений, экстремум', set: {
      claim: 'Несчётность, промежуточное значение и экстремум доказаны без допущений',
      note: DONE + ': было «…, экстремум — с исключённым третьим»; строка создаётся генератором из tools/highlights-vitrina.md, источник поправлен; unit_interval_uncountable_trisect_v2 — Closed under the global context' } },
  { was: 'Несчётность и промежуточное значение доказаны без допущений', set: {
      claim: 'Несчётность, промежуточное значение и экстремум доказаны',
      note: 'IVT_process — Closed under the global context; фраза изменена шагом 1 Части V (12.11)' } },
  { was: 'экстремум — с исключённым', set: {
      claim: 'экстремум доказаны без допущений',
      page_price: 'без допущений', verdict: 'ok',
      note: DONE + ': было «экстремум — с исключённым третьим»; ' + PA } },
]);
