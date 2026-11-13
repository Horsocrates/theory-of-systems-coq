// Часть I, шаг 9, страницы (2026-11-13, слово автора «Вноси; вноси»): 5 правок главы I.6 (места 11, 13, 14) внесены;
// формализация — src/foundation/StatusMechanism.v.
// Запуск: node patch-p01-step-09-pages.cjs  (затем relocate + merge по part01-ch06). Скрипт повторяем.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 13.11 (Часть I, шаг 9, слово автора)';
const SM = 'src/foundation/StatusMechanism.v';
const CL = 'Closed under the global context';
const norm = (s) => (s || '').replace(/\s+/g, ' ');
const p = path.join(__dirname, 'part01-ch06.json');
const j = JSON.parse(fs.readFileSync(p, 'utf8'));
let n = 0, added = 0;
const fix = (prefix, th, fields) => { const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix) && (th === undefined || (th === null ? !r.theorem : r.theorem === th))); if (!hit.length) return; if (hit.length !== 1) throw new Error('не одна запись: ' + prefix); Object.assign(hit[0], { verdict: 'ok' }, fields); n++; };
const add = (rec) => { if (j.records.some((r) => (r.theorem || null) === (rec.theorem || null) && norm(r.claim) === norm(rec.claim))) return; j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); added++; };

// ---- место 13: механизм статуса
const C1 = 'Полный механизм статуса, описанный в § 6.6, — с состоянием вида «действующий максимум плюс список повторных максимумов», с шаг-функцией, со сбросом повторов при смене максимума — формализован отдельным файлом-автоматом `StatusMechanism.v`: записаны состояние стадии и шаг-функция;';
fix('Полный механизм статуса, описанный в § 6.6, — с состоянием вида', null, { claim: C1,
  note: DONE + ': было «в текущем репозитории отдельным файлом-автоматом не формализован». Файл src/foundation/StatusMechanism.v: StatusState, status_step, status_run; 20 Qed, ' + CL + '.' });
const C2 = 'доказаны единственность носителя статуса максимума на каждой стадии (`status_maximum_unique`), сброс повторов при смене максимума (`status_reset_on_new_max`), передача статуса только при строгом превосходстве (`status_holder_changes_only_on_strict_excess`) и инвариант — действующий максимум есть наибольшее из пройденных значений, а повторы суть в точности равные ему позднейшие позиции (`status_run_inv`).';
for (const [th, note] of [['status_maximum_unique', 'status_of st j = RoleMaximum <-> j = st_max_pos st.'], ['status_reset_on_new_max', ''], ['status_holder_changes_only_on_strict_excess', ''], ['status_run_inv', 'status_run p n = Some st -> status_inv p n st.']])
  add({ theorem: th, file: SM, claim: C2, note: (note ? note + ' ' : '') + CL + '.' });
const C3 = 'Разобранная по шагам последовательность $1,3,2,5,4,5,7,7$ воспроизведена вычислением, стадия за стадией (от `example_stage_0` до `example_stage_8`), включая утрату статуса шестым элементом на шаге 7 (`example_sixth_gains_and_loses`).';
fix('Разобранная по шагам последовательность $1,3,2,5,4,5,7,7$ — точная иллюстрация этой схемы', null, { theorem: 'example_stage_0', file: SM, claim: C3,
  note: DONE + ': было «машинно-проверенной регистрацией всего механизма она пока не подкреплена». Девять стадий примера — example_stage_0 … example_stage_8, каждая доказана вычислением (reflexivity); ' + CL + '.' });
add({ theorem: 'example_stage_8', file: SM, claim: C3, note: 'status_run chapter_example 8 = Some (mkStatusState 7 7 [8]). ' + CL + '.' });
add({ theorem: 'example_sixth_gains_and_loses', file: SM, claim: C3, note: 'Шестой элемент — повторный максимум на шаге 6 и только базовый на шаге 7. ' + CL + '.' });
fix('Глава 6 завершила *формальное* измерение Части I: разобран аппарат', null, {
  claim: 'Этот аппарат построен; формально проверено в нём то, что названо в главе по именам, — производные принципы из двух объявлений, разрешение списка по порядку $L5$, выбор как правило, условный запрет завершённого графа и механизм статуса § 6.6. Два Закона — $L3$ и $L4$ — зарегистрированы объявлениями.',
  note: DONE + ': было «Этот аппарат построен и формально проверен». Механизм статуса формализован (StatusMechanism.v); L3 и L4 в Rocq — объявления (classic, L4_witness).' });

// ---- место 11: уровни и универсы
fix('В репозитории иерархия уровней ToS[^14] строится поверх универсной', 'Level', {
  claim: 'В репозитории иерархия уровней ToS[^14] задана рядом с универсной иерархией CIC, отдельной разметкой: типом меток `Level` с порядком `level_lt`, для которого невозможность самовключения доказана теоремой (`P1_no_self_membership`).',
  note: DONE + ': было «строится поверх универсной иерархии CIC». Level — индуктивный тип меток (Core_ERR:59); все System L лежат в одном универсе. Связь меток с уровнями универсов теоремой не записывается — горизонт.' });
fix('формальная иерархия ToS строится поверх универсной иерархии CIC.', 'Level', {
  claim: 'Системы всех уровней лежат в одном универсе; уровень области задаётся полем-меткой `crit_level_witness` записи `Criterion`.',
  note: DONE + ': было «формальная иерархия ToS строится поверх универсной иерархии CIC».' });
add({ theorem: 'P1_no_self_membership', file: 'src/TheoryOfSystems_Core_ERR.v',
  claim: 'Тип `Level` и отношение `level_lt` в файле `src/TheoryOfSystems_Core_ERR.v`; иррефлексивность порядка — `P1_no_self_membership`.', note: CL + '.' });

// ---- место 14: сноска 15
const C5 = 'Процессная природа бесконечности представлена в репозитории теоремами: всякая стадия процесса общего вида продолжается следующей, и никакой конечный список не вмещает всех его стадий (`gen_process_stage_extends`, `gen_process_never_completed`, файл `src/foundation/StatusMechanism.v`).';
fix('Процессная природа бесконечности зафиксирована в файле `src/foundation/ProcessP4Synthesis.v`', 'process_p4_grand_synthesis', {
  theorem: 'gen_process_never_completed', file: SM, claim: C5,
  note: DONE + ': было «зафиксирована… в формулировке „бесконечность есть процесс, не объект“» — та формулировка стоит комментарием. gen_process_never_completed : forall A (p : GenProcess A) (l : list A), exists n, length l < length (gp_prefix p n). ' + CL + '.' });
add({ theorem: 'gen_process_stage_extends', file: SM, claim: C5, note: 'gp_prefix p (S n) = gp_prefix p n ++ [gp_observe p n]. ' + CL + '.' });
fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
console.log('part01-ch06.json: изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length);
