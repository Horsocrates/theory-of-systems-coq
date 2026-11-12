// Шаг 4 (2026-11-12, слово автора «А»): записи ведомости главы IV.1 о файле P4ProhibitsAC.v
// приводятся к новому содержанию файла (график -- совокупность пар) и новой фразе страницы.
// Запуск: node patch-step-04.cjs   (затем tom-links.cjs relocate + merge)
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 12.11 (шаг 4, слово автора «А»)';
const p = path.join(__dirname, 'part04-ch01.json');
const j = JSON.parse(fs.readFileSync(p, 'utf8'));
let n = 0;
function one(prefix) {
  const hit = j.records.filter((r) => (r.claim || '').startsWith(prefix));
  if (hit.length !== 1) throw new Error('ожидалась одна запись «' + prefix + '», найдено ' + hit.length);
  return hit[0];
}
function set(prefix, fields) { Object.assign(one(prefix), fields); n++; }
function insertAfter(prefix, rec) {
  if (j.records.some((r) => r.claim === rec.claim)) return;
  const i = j.records.indexOf(one(prefix)); j.records.splice(i + 1, 0, rec); n++;
}

set('такая функция выбора есть *сама по себе* завершённый бесконечный объект', {
  verdict: 'ok',
  note: DONE + ' — правка формализации, слова главы не менялись: теперь Definition choice_graph (f : nat -> nat) : nat -> nat -> Prop := fun n m => m = f n — совокупность пар «индекс, значение»; тотальность — лемма choice_graph_completed : forall f, CompletedInfSet (graph_indices (choice_graph f)), где graph_indices G n := exists m, G n m; было choice_graph f := fun n => True (от f не зависел)' });
set('Теорема `ac_implies_completed` доказывает это', {
  verdict: 'ok',
  note: DONE + ' — правка формализации, слова главы не менялись: теперь ac_implies_completed : AC_on_nat -> forall F, (forall n, F n <> nil) -> exists f, (forall n m, choice_graph f n m -> In m (F n)) /\\ CompletedInfSet (graph_indices (choice_graph f)) — функция выбора привязана к семейству, посылка в доказательстве используется; Print Assumptions: Closed under the global context. Граница доказанного названа в самом файле: AC_on_nat_as_rule (посылка есть теорема) и completed_graph_contradicts_P4 (то же для графика любой функции)' });
insertAfter('Теорема `ac_implies_completed` доказывает это', {
  line: 830, theorem: 'ac_completed_graph_contradicts_P4', file: 'src/foundation/P4ProhibitsAC.v',
  claim: 'Всё рассуждение собрано и одной теоремой — `ac_completed_graph_contradicts_P4`.',
  page_price: '', verdict: 'ok',
  note: DONE + ' — фраза добавлена: AC_on_nat -> forall F, (forall n, F n <> nil) -> forall actual, P4_stage_bounded actual -> (forall f, (forall n, In (f n) (F n)) -> bridge (graph_indices (choice_graph f)) actual) -> False; Closed under the global context' });
insertAfter('Всё рассуждение собрано и одной теоремой', {
  line: 832, theorem: 'completed_graph_contradicts_P4', file: 'src/foundation/P4ProhibitsAC.v',
  claim: 'то же противоречие даёт график *любой* всюду определённой функции, взятый как завершённое целое (`completed_graph_contradicts_P4`)',
  page_price: '', verdict: 'ok',
  note: DONE + ' — фраза добавлена: forall f actual, P4_stage_bounded actual -> bridge (graph_indices (choice_graph f)) actual -> False; Closed under the global context' });
insertAfter('то же противоречие даёт график *любой* всюду определённой функции', {
  line: 834, theorem: 'AC_on_nat_as_rule', file: 'src/foundation/P4ProhibitsAC.v',
  claim: 'а сам выбор из непустых списков есть теорема — голова списка (`AC_on_nat_as_rule`).',
  page_price: '', verdict: 'ok',
  note: DONE + ' — фраза добавлена: Lemma AC_on_nat_as_rule : AC_on_nat, свидетель fun n => L5_choose (F n) 0; Closed under the global context; то же утверждение — P4_Eliminates_AC.AC_is_L5' });
set('Файл `P4ProhibitsAC.v` *не* доказывает замкнутого утверждения', {
  note: 'статус назван честно: замкнутого отрицания в файле нет; после шага 4 файл говорит это сам — AC_on_nat_as_rule доказывает AC_on_nat, а противоречие (ac_completed_graph_contradicts_P4) условно: стадийная ограниченность и мост' });
set('`P4ProhibitsAC.v` (каталог `src/foundation/`), 10 доказанных утверждений', {
  note: 'после шага 4 (12.11) в файле 12 Qed (7 лемм и 5 теорем), 0 аксиом; до шага было 8; число 10 на странице неверно и до, и после — правится шагом о числах в сносках (строка 8 таблицы)' });
set('Файл доказывает `P4_prohibits_three`', {
  note: 'сомнительное: три конъюнкта (:30) — условная несовместимость завершённого множества; AC_gives_completed_graph (после шага 4: функция выбора с графиком из выбранных пар, содержащим пару на всяком индексе); противоречивость множества Рассела, в которой P4 не участвует (лемма названа russell_contradiction_without_P1); «несовместимость с полной аксиомой выбора» — прочтение: сам выбор из непустых списков есть теорема (AC_on_nat_as_rule), несовместимо чтение функции выбора как завершённого графика' });

fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
console.log('part04-ch01.json: записей изменено или добавлено ' + n + ', всего ' + j.records.length);
