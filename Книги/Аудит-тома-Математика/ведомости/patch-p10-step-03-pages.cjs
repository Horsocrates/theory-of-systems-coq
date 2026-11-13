// Часть X, шаг 3, страницы (2026-11-13, слово автора «делай»): шесть мест главы X.2 внесены;
// строка 3 таблицы («и всё это без выбора») закрыта шагом 1 без правки страницы.
// Запуск: node patch-p10-step-03-pages.cjs   (затем tom-links.cjs relocate + merge ведомости/part10-ch02.json)
// Скрипт повторяем: запись, уже приведённая к новым словам, пропускается.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 13.11 (Часть X, шаг 3, слово автора)';
const UG = 'src/UnitIntervalUncountableGeneral.v';
const norm = (s) => (s || '').replace(/\s+/g, ' ');
const p = path.join(__dirname, 'part10-ch02.json');
const j = JSON.parse(fs.readFileSync(p, 'utf8'));
let n = 0, added = 0;
function fix(prefix, fields, keepVerdict) {
  let hit = j.records.filter((r) => norm(r.claim).startsWith(prefix));
  if (hit.length > 1) hit = hit.filter((r) => r.verdict !== 'ok');
  if (hit.length === 0) return;
  if (hit.length !== 1) throw new Error('ожидалась одна запись «' + prefix + '», найдено ' + hit.length);
  Object.assign(hit[0], keepVerdict ? {} : { verdict: 'ok' }, fields); n++;
}
function add(rec) {
  if (j.records.some((r) => r.theorem === rec.theorem && norm(r.claim) === norm(rec.claim))) return;
  j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); added++;
}
const MOD = 'unit_interval_uncountable_modulated : forall E mu, valid_modulated_enumeration E mu -> exists D, is_Cauchy D /\\ (forall m, 0 <= D m <= 1) /\\ (forall n, not_equiv D (E n)) — Closed under the global context; теорема ShrinkingIntervals_ERR.v (регулярные перечисления) — её частный случай (regular_is_modulated).';
const GEN = 'unit_interval_uncountable_general_definite: то же для valid_enumeration (произвольные процессы Коши в [0,1]) из двух посылок — исключённого третьего и извлечения единственного свидетеля (наименьшая скорость) — Closed under the global context; unit_interval_uncountable_general: без исключённого третьего, Axioms: ToS_Axioms.L4_witness.';

fix('Для действительных чисел работает тот же приём в непрерывной форме — *трисекция*: по любому перечислению', { theorem: 'unit_interval_uncountable_general_definite', file: UG,
  claim: 'Для действительных чисел работает тот же приём в непрерывной форме — *трисекция*: по перечислению точек $[0,1]$ строится вложенная последовательность отрезков, отсекающая каждую перечисленную точку, и определяемый ею процесс лежит в $[0,1]$, но вне перечисления.',
  note: DONE + ': было «по любому перечислению… и её предел лежит в [0,1]» при теореме, требовавшей регулярности. Теперь слова о перечислении общие, а цена названа следующими фразами. ' + MOD + ' ' + GEN + ' Теоремы дают процесс Коши со значениями в [0,1]; рационального предела не утверждают.' });
fix('Конструктивна и *вещественная* трисекционная версия: формальная теорема несчётности', {
  claim: 'Конструктивна и *вещественная* трисекционная версия: при заданной скорости сходимости перечисленных процессов формальная теорема несчётности $[0,1]$ проверена командой `Print Assumptions` и не опирается ни на одно допущение',
  note: DONE + ': добавлено условие «при заданной скорости сходимости». unit_interval_uncountable_trisect_v2 (регулярные перечисления) и unit_interval_uncountable_modulated (любая заданная скорость) — Closed under the global context. Устойчивость зазора для процессов Коши — not_equiv_stable_gap (UnitIntervalUncountableGeneral.v), Closed.' }, true);
fix('«процессы сопротивляются всякому перечислению». Это правило конструктивно целиком — и над двоичными процессами, и над процессами отрезка;', { theorem: 'unit_interval_uncountable_modulated', file: UG, page_price: '0 аксиом при заданной скорости',
  claim: '«процессы сопротивляются всякому перечислению». Это правило конструктивно целиком — и над двоичными процессами, и над процессами отрезка с заданной скоростью сходимости;',
  note: DONE + ': было «и над процессами отрезка» без условия. ' + MOD });
fix('закон исключённого третьего нужен лишь там, где завершённая сторона классифицируется', { theorem: 'unit_interval_uncountable_general_definite', file: UG,
  claim: 'закон исключённого третьего нужен там, где скорость приходится извлекать, и там, где завершённая сторона классифицируется *целиком*.',
  note: DONE + ': было «нужен лишь там, где завершённая сторона классифицируется целиком». ' + GEN + ' Необходимость исключённого третьего (или L4) для произвольных перечислений не доказана: это цена нынешних доказательств.' }, true);
fix('*Несчётность — роль «сопротивляться перечислению»: для любого обхода правило-диагональ порождает процесс вне его. Оно конструктивно целиком (0 аксиом) — над $2^{ℕ}$ и над отрезком;', { theorem: 'unit_interval_uncountable_modulated', file: UG, page_price: '0 аксиом при заданной скорости',
  claim: '*Несчётность — роль «сопротивляться перечислению»: для любого обхода правило-диагональ порождает процесс вне его. Оно конструктивно целиком (0 аксиом) — над $2^{ℕ}$ и над отрезком при заданной скорости сходимости; классична (L3) дихотомия завершённой стороны.',
  note: DONE + ': было «над 2^ℕ и над отрезком» без условия. ' + MOD });
fix('Шрёдер–Бернштейн делает это $\\le$ антисимметричным с точностью до биекции, а общая теорема Кантора', { theorem: 'cardinal_antisym_definite', file: 'src/settheory/CardinalityWithoutChoice.v', page_price: 'без выбора',
  note: 'закрыто 13.11 (Часть X, шаг 1): страница не менялась, слова «без выбора» теперь опираются на теорему. cardinal_antisym_definite : ExcludedMiddle -> UniqueWitness -> forall A B, injects A B -> injects B A -> bijects A B — Closed under the global context; cardinal_antisym — её частный случай (classic + L4_witness). no_maximal_cardinality — Closed.' });
fix('Используется только инволютивность `flip` (булева отрицания);', { theorem: 'flip_neq', file: 'src/ProcessDiagonal.v', page_price: '0 аксиом',
  claim: 'Используется только то, что `flip` (булево отрицание) не оставляет на месте ни одно значение (`flip_neq`: $\\texttt{flip}\\ b \\neq b$); **0 аксиом** — файл это печатает.',
  note: DONE + ': было «используется только инволютивность flip» — доказательство diagonal_differs применяет flip_neq : forall b, flip b <> b; одной инволютивности недостаточно (тождественная функция инволютивна). Closed under the global context.' });
fix('`unit_interval_uncountable_trisect_v2` (`ShrinkingIntervals_ERR.v`) — главная теорема файла: $[0,1]$ несчётен.', { page_price: '0 допущений',
  claim: '`unit_interval_uncountable_trisect_v2` (`ShrinkingIntervals_ERR.v`) — главная теорема файла: никакое *регулярное* перечисление (каждый член — процесс в $[0,1]$ с оценкой $|R_m - R_k| \\le 1/m + 1/k$) не исчерпывает процессы отрезка.',
  note: DONE + ': было «[0,1] несчётен» без условия. unit_interval_uncountable_trisect_v2 : forall E, valid_regular_enumeration E -> exists D, is_Cauchy D /\\ (forall m, 0 <= D m <= 1) /\\ (forall n, not_equiv D (E n)). Closed under the global context.' });

add({ theorem: 'unit_interval_uncountable_modulated', file: UG, page_price: '0 аксиом',
  claim: 'Любая заданная скорость сходимости — `unit_interval_uncountable_modulated`, 0 аксиом.',
  note: 'Новая теорема шага 3. ' + MOD });
add({ theorem: 'unit_interval_uncountable_general_definite', file: UG, page_price: '0 аксиом (посылки вместо аксиом)',
  claim: 'Произвольные сходящиеся процессы — `unit_interval_uncountable_general_definite` (из исключённого третьего и извлечения единственного свидетеля как посылок, 0 аксиом)',
  note: 'Новая теорема шага 3. ' + GEN + ' При classic и L4_definite — unit_interval_uncountable_general_L3_L4 (classic + L4_witness).' });
add({ theorem: 'unit_interval_uncountable_general', file: UG, page_price: 'один L4_witness',
  claim: '`unit_interval_uncountable_general` (без исключённого третьего; цена — один `L4_witness`).',
  note: 'Новая теорема шага 3: forall E, valid_enumeration E -> exists D, … ; скорость каждого члена извлекается L4_witness из условия Коши (свидетель не единствен). Axioms: ToS_Axioms.L4_witness.' });
add({ theorem: 'least_witness_exists', file: UG, page_price: '',
  claim: 'с исключённым третьим извлекается *наименьшая* скорость — свидетель единственный; без исключённого третьего берётся какая-нибудь, и это стоит L4 в полную силу.',
  note: 'least_witness_exists : (forall P, P \\/ ~ P) -> forall P : nat -> Prop, (exists n, P n) -> exists! n, P n /\\ forall m, m < n -> ~ P m. Closed under the global context. На ней стоит unit_interval_uncountable_general_definite.' });
add({ theorem: 'unit_interval_uncountable_modulated', file: UG, page_price: '0 допущений',
  claim: 'Если скорость дана, допущений нет.',
  note: MOD });

fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
console.log('part10-ch02.json: изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length);
