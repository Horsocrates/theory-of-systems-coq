// Шаг 12 (2026-11-12, слово автора «А — дополняем рассказ»): где в процессной континуум-гипотезе работает L4.
// Запуск: node patch-step-12.cjs   (затем tom-links.cjs relocate + merge по обеим ведомостям)
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 12.11 (шаг 12, слово автора «А»)';
const F = 'src/ProcessContinuumHypothesis.v';
const PA2 = 'Print Assumptions pick_dir: Classical_Prop.classic и ToS_Axioms.L4_witness; countable_union_enum: только L4_witness';

function load(file) { const p = path.join(__dirname, file); return { p, j: JSON.parse(fs.readFileSync(p, 'utf8')) }; }
function one(j, prefix) {
  const hit = j.records.filter((r) => (r.claim || '').startsWith(prefix));
  if (hit.length !== 1) throw new Error('ожидалась одна запись «' + prefix + '», найдено ' + hit.length);
  return hit[0];
}
function save(x, file, n) { fs.writeFileSync(x.p, JSON.stringify(x.j, null, 1) + '\n'); console.log(file + ': записей изменено или добавлено ' + n + ', всего ' + x.j.records.length); }

{
  const x = load('part04-ch05.json'); const j = x.j; let n = 0;
  const r1 = one(j, 'Стоит сказать, *где* появляется $L4$');
  Object.assign(r1, {
    theorem: 'countable_union_enum',
    claim: 'Стоит сказать, *где* появляется $L4$, потому что места эти поучительны. Их два. Первое: доказательство берёт *счётное объединение* перечислимых совокупностей',
    page_price: 'L4 в двух местах', verdict: 'ok',
    note: DONE + ': было «место это поучительное… в одном месте»; мест два — countable_union_enum (:70–78, L4_witness применён напрямую) и pick_dir (:272–275, через L3_informative); ' + PA2 }); n++;
  const add = {
    line: r1.line + 16, theorem: 'pick_dir', file: F,
    claim: 'Второе место — сама главная цепь. Функция `pick_dir` на каждом шаге смотрит на одно из двух продолжений узла: если путей через него неперечислимо много, цепь идёт туда, иначе — в другую сторону.',
    page_price: 'classic + L4_witness', verdict: 'ok',
    note: DONE + ' — абзац добавлен: pick_dir T sigma := if L3_informative (perf_subtree T (sigma ++ [false])) then false else true; perf_subtree T s := T s /\\ ~ is_enumerable (paths_extending T s); L3_informative : forall P, {P} + {~P} (ToS_Axioms.v:119) стоит на classic + L4_witness; ' + PA2 };
  if (!j.records.some((r) => r.claim === add.claim)) { j.records.splice(j.records.indexOf(r1) + 1, 0, add); n++; }
  Object.assign(one(j, 'Центральная теорема опирается на две аксиомы — законы логики $L3$ и $L4$'), {
    claim: 'Центральная теорема опирается на две аксиомы — законы логики $L3$ и $L4$ ($L4$ — для счётного объединения перечислимых классов и для выбора направления главной цепи).',
    verdict: 'ok',
    note: DONE + ': добавлено второе место L4 — выбор направления главной цепи (pick_dir через L3_informative); Print Assumptions process_continuum_hypothesis: classic + L4_witness' }); n++;
  save(x, 'part04-ch05.json', n);
}
{
  const x = load('part04-ch06.json'); const j = x.j; let n = 0;
  Object.assign(one(j, 'дихотомия Кантора–Бендиксона для замкнутых совокупностей бинарных'), {
    claim: 'дихотомия Кантора–Бендиксона для замкнутых совокупностей бинарных процессов (Глава 4.5; $L4$ — в счётном объединении и в выборе направления главной цепи)',
    note: DONE + ': цена совпадает (classic + L4_witness); названы оба места L4 — countable_union_enum и pick_dir (через L3_informative)' }); n++;
  Object.assign(one(j, 'В Главе 4.5 этот закон прямо работает'), {
    claim: 'В Главе 4.5 этот закон прямо работает — в счётном объединении перечислимых семейств (`countable_union_enum`) он извлекает для каждого класса его перечислитель, а в построении главной цепи (`pick_dir`) — определённый ответ на вопрос «да или нет».',
    note: DONE + ': добавлено второе место; countable_union_enum применяет L4_witness к каждому F n (:76–78), Print Assumptions — только L4_witness; pick_dir — classic + L4_witness через L3_informative' }); n++;
  save(x, 'part04-ch06.json', n);
}
