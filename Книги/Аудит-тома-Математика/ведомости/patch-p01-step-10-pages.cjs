// Часть I, шаг 10, страницы (2026-11-13, слово автора «Делай»): 6 правок главы I.7 внесены; формализация —
// src/settheory/ListModes.v и src/foundation/GraphTransitionN2.v.
// Запуск: node patch-p01-step-10-pages.cjs  (затем relocate + merge по part01-ch07). Скрипт повторяем.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 13.11 (Часть I, шаг 10, слово автора)';
const F = 'src/foundation/';
const LM = 'src/settheory/ListModes.v';
const GT = F + 'GraphTransitionN2.v';
const CD = F + 'DistinctionCoDefinition.v';
const CL = 'Closed under the global context';
const norm = (s) => (s || '').replace(/\s+/g, ' ');
const p = path.join(__dirname, 'part01-ch07.json');
const j = JSON.parse(fs.readFileSync(p, 'utf8'));
let n = 0, added = 0;
const fix = (prefix, th, fields) => { const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix) && (th === undefined || (th === null ? !r.theorem : r.theorem === th))); if (!hit.length) return; if (hit.length !== 1) throw new Error('не одна запись: ' + prefix); Object.assign(hit[0], { verdict: 'ok' }, fields); n++; };
const add = (rec) => { if (j.records.some((r) => (r.theorem || null) === (rec.theorem || null) && norm(r.claim) === norm(rec.claim))) return; j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); added++; };

// место 1
const C1 = 'формально это разобрано в файле `TheoryOfSystems_Core_ERR.v`, где теорема `russell_paradox_blocked` устанавливает для уровня `L2` невозможность критерия-свидетеля на собственном уровне через иррефлексивность отношения `level_lt`; для всякого уровня то же утверждает `criterion_label_never_own_level` (`TransfiniteInductionLevel.v`).';
fix('формально это разобрано в файле `TheoryOfSystems_Core_ERR.v`, где теорема `russell_paradox_blocked`', 'russell_paradox_blocked', { claim: C1,
  note: DONE + ': добавлено «для уровня L2» и названа общая теорема. russell_paradox_blocked — утверждение об одном уровне L2; ' + CL + '.' });
add({ theorem: 'criterion_label_never_own_level', file: F + 'TransfiniteInductionLevel.v', claim: C1,
  note: 'criterion_label_never_own_level : forall (L : Level) (C : Criterion L), crit_level_witness L C <> L. ' + CL + '.' });
// место 2
const C2 = 'Сама схема записана теоремами: множество получается из списка двумя ступенями — мультимножество забывает порядок и только его, множество забывает ещё и кратность (`first_step_forgets_exactly_order`, `support_from_mult`, `second_step_well_defined`, файл `ListModes.v`).';
fix('В репозитории ToS это отражено прямо: формализация теоретико-множественных', null, {
  claim: 'Слой же теоретико-множественных конструкций[^2] на эту схему пока не опирается: множества в нём заданы предикатами и типами, а списки служат рабочим материалом — позициями игр, словами, наборами поддеревьев.',
  note: DONE + ': было «располагается поверх списочного аппарата, как производный слой». В 11 файлах src/settheory/ множества заданы предикатами и типами с отображениями; схема «список → множество» записана отдельным файлом ListModes.v. Перевод слоя на эту схему — горизонт.' });
for (const [th, note] of [['first_step_forgets_exactly_order', 'same_multiset l1 l2 <-> Permutation l1 l2.'], ['support_from_mult', 'support l x <-> mult l x > 0.'], ['second_step_well_defined', 'same_multiset l1 l2 -> same_set l1 l2.']])
  add({ theorem: th, file: LM, claim: C2, note: note + ' ' + CL + '.' });
// место 5
fix('| операциональная делимость | `Level`, `System` $L$, `Criterion` в `Core_ERR.v`', null, {
  claim: '| операциональная делимость | `Level`, `System` $L$, `Criterion` в `TheoryOfSystems_Core_ERR.v` | формализовано как иерархия уровней |',
  note: DONE + ': было `Core_ERR.v` — файла с таким именем нет.' });
// место 4
const C4 = 'Позитивная онтология имеет прямой формальный след: запись `Distinction` с её полями задана в Rocq, и о ней доказано, что каждая сторона всякого различения есть в точности отрицание другой и что стороны различны (`sides_codetermined`, `sides_distinct`, без аксиом); канонический экземпляр `distinction_of` построен ценой аксиомы `classic`.';
fix('Позитивная онтология имеет прямой формальный след: запись `Distinction` с её полями машинно', 'Distinction', { claim: C4,
  note: DONE + ': было «запись Distinction с её полями машинно проверена». Названо, что именно доказано о записи и какова цена построения экземпляра.' });
add({ theorem: 'sides_codetermined', file: CD, page_price: 'без аксиом', claim: C4, note: CL + '.' });
add({ theorem: 'sides_distinct', file: CD, page_price: 'без аксиом', claim: C4, note: CL + '.' });
// место 3
const C3a = '`ConnectionClosesGap.v` проверяет на примерах три звена Barandes-style correspondence и сводит проверки в одну теорему; само соответствие между distinction graph, doubly stochastic / unistochastic transitions и path-dependence приведено в нём таблицей в комментарии.';
fix('`ConnectionClosesGap.v` собирает Barandes-style correspondence', 'grand_synthesis', { claim: C3a,
  note: DONE + ': было «собирает Barandes-style correspondence». grand_synthesis — конъюнкция трёх числовых проверок; ' + CL + '.' });
const C3b = 'Для графа из двух узлов цепочка проведена теоремами целиком (`GraphTransitionN2.v`): матрица графа, её преобразование Кэли, ортогональность, унистохастическая и потому дважды стохастическая матрица переходов — при любом весе связи (`cayley_2_is_cayley_transform`, `graph_transition_unistochastic`); и неделимость — переход за два шага не равен произведению переходов за один (`two_step_transition_indivisible`).';
for (const [th, note] of [['cayley_2_is_cayley_transform', 'U (I - M/2) = I + M/2 для всякого рационального theta.'], ['graph_transition_unistochastic', 'forall theta, is_unistochastic (Gamma_graph theta) 2.'], ['two_step_transition_indivisible', '49/625 против 337/625 (two_step_values).']])
  add({ theorem: th, file: GT, claim: C3b, note: note + ' ' + CL + '.' });
fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
console.log('part01-ch07.json: изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length);
