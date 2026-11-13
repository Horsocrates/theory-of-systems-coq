// Часть X, шаг 2, страницы (2026-11-13, слово автора «делай»): четыре места главы X.1 внесены;
// строка 4 таблицы («без выбора») закрыта шагом 1 без правки страницы.
// Запуск: node patch-p10-step-02-pages.cjs   (затем tom-links.cjs relocate + merge ведомости/part10-ch01.json)
// Скрипт повторяем: запись, уже приведённая к новым словам, пропускается.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 13.11 (Часть X, шаг 2, слово автора)';
const TIL = 'src/foundation/TransfiniteInductionLevel.v';
const PPI = 'src/foundation/P4ProhibitsImpredicative.v';
const norm = (s) => (s || '').replace(/\s+/g, ' ');
const p = path.join(__dirname, 'part10-ch01.json');
const j = JSON.parse(fs.readFileSync(p, 'utf8'));
let n = 0, added = 0;
function fix(prefix, fields) {
  let hit = j.records.filter((r) => norm(r.claim).startsWith(prefix));
  if (hit.length > 1) hit = hit.filter((r) => r.verdict !== 'ok');   // одна цитата у нескольких записей: берётся запись с расхождением
  if (hit.length === 0) return;
  if (hit.length !== 1) throw new Error('ожидалась одна запись «' + prefix + '», найдено ' + hit.length);
  Object.assign(hit[0], { verdict: 'ok' }, fields); n++;
}
function add(rec) {
  if (j.records.some((r) => r.theorem === rec.theorem && norm(r.claim) === norm(rec.claim))) return;
  j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); added++;
}
const SBD = 'После шага 1 Части X слова «без выбора» опираются на теорему: Schroeder_Bernstein_definite (SchroederBernstein_ERR.v) выводит заключение из двух посылок — исключённого третьего и извлечения единственного свидетеля — и допущений не имеет (Closed under the global context); Schroeder_Bernstein — её частный случай при classic и L4_definite (classic + L4_witness). Страница не менялась.';

fix('сравнение мощностей без выбора (10.3)', { theorem: 'Schroeder_Bernstein_definite', file: 'src/SchroederBernstein_ERR.v', page_price: 'без выбора',
  note: 'закрыто 13.11 (Часть X, шаг 1). ' + SBD });
fix('Глава 10.3: сравнение мощностей без выбора — Шрёдер–Бернштейн и общая теорема Кантора.', { theorem: 'Schroeder_Bernstein_definite', file: 'src/SchroederBernstein_ERR.v', page_price: 'без выбора',
  note: 'закрыто 13.11 (Часть X, шаг 1). ' + SBD + ' Общая теорема Кантора (cantor_no_surjection) — Closed under the global context.' });
fix('иррефлексивность $\\ll$ гарантирует отсутствие $\\in$-циклов *по построению*.', { theorem: 'tos_hierarchy_models_meta_pair', file: 'src/foundation/MetaPairStrength.v',
  claim: 'фундированность $\\ll$ исключает циклы по уровням и бесконечный спуск *по построению*.',
  note: DONE + ': было «иррефлексивность гарантирует отсутствие ∈-циклов». tos_hierarchy_models_meta_pair (MetaPairStrength.v): для порядка уровней нет петли, есть асимметрия, нет циклов любой длины (~ clos_trans Level level_lt L L) и нет бесконечного спуска — всё из level_lt_wf. Closed under the global context. Утверждения — о порядке уровней, а не об отношении element_at.' });
fix('**Что даёт.** Фундирование $\\to$ теорема (`level_lt_irrefl`);', { theorem: 'level_lt_wf', file: TIL,
  claim: '**Что даёт.** Фундирование $\\to$ теорема (`level_lt_wf`: порядок уровней фундирован; в форме самой аксиомы — `level_foundation_form`);',
  note: DONE + ': было «Фундирование → теорема (level_lt_irrefl)» — иррефлексивность запрещает только петлю. level_lt_wf : well_founded level_lt. Closed under the global context.' });
fix('`russell_paradox_blocked` (`TheoryOfSystems_Core_ERR.v`): расселова совокупность не может быть построена', { theorem: 'russell_blocked_every_level', file: TIL,
  claim: '`russell_blocked_every_level` (`foundation/TransfiniteInductionLevel.v`): ни на каком уровне нет системы, собирающей в точности те системы этого уровня, что не входят в себя, — каким бы ни было отношение принадлежности.',
  note: DONE + ': было «russell_paradox_blocked: расселова совокупность не может быть построена ни на каком уровне» — та теорема доказана для L2 и говорит о метке уровня критерия. russell_blocked_every_level : forall L (mem : System L -> System L -> Prop), ~ exists R, forall X, mem X R <-> ~ mem X X. Closed under the global context. Диагональ уровня не использует: то же верно на любом носителе.' });
fix('См. также `P4ProhibitsImpredicative.v`: импредикативное определение', { theorem: 'russell_collector_escapes', file: PPI,
  claim: 'См. также `P4ProhibitsImpredicative.v`: собиратель расселова условия по области сам в эту область не входит (`russell_collector_escapes`), поэтому область, у которой такой собиратель есть, не завершена (`russell_needs_incomplete_range`).',
  note: DONE + ': было «импредикативное определение R требует завершённой тотальности всех множеств, которую P4 не допускает» — в файле это стояло только в комментариях. russell_collector_escapes : (forall x, T x -> (mem x r <-> ~ mem x x)) -> ~ T r (любой носитель). Closed under the global context.' });
fix('`P4ProhibitsImpredicative.v`: $R$ требует completed totality; P1${}+{}$P4 её исключают.', { theorem: 'staged_russell_collector_exists', file: PPI,
  claim: '`P4ProhibitsImpredicative.v`: по каждой конечной стадии собиратель расселова условия существует, лежит вне стадии и появляется на следующей (`staged_russell_collector_exists`);',
  note: DONE + ': было «R требует completed totality; P1 + P4 её исключают» — теорем об этом в файле не было. staged_russell_collector_exists : forall stage, exists r, (forall x, nat_staged_actual stage x -> (x < r <-> ~ x < x)) /\\ ~ nat_staged_actual stage r /\\ nat_staged_actual (S stage) r. Closed under the global context. Пример стадий — для отношения x < y на nat.' });

add({ theorem: 'criterion_label_never_own_level', file: TIL,
  claim: 'Про сам критерий — `criterion_label_never_own_level`: уровень критерий-домена никогда не равен уровню системы (для $L_2$ это `russell_paradox_blocked` в `TheoryOfSystems_Core_ERR.v`).',
  note: 'Новая теорема шага 2: forall (L : Level) (C : Criterion L), crit_level_witness L C <> L — из поля crit_level_valid (P2) и иррефлексивности. Closed under the global context. russell_paradox_blocked (Core_ERR.v) — то же для L2, с посылкой о домене, которую доказательство не использует.' });
add({ theorem: 'russell_needs_incomplete_range', file: PPI,
  claim: 'поэтому область, у которой такой собиратель есть, не завершена (`russell_needs_incomplete_range`).',
  note: 'Новая теорема шага 2: (forall x, T x -> (mem x r <-> ~ mem x x)) -> ~ CompletedInfSet T, где CompletedInfSet T := forall n, T n. Closed under the global context.' });
add({ theorem: 'russell_requires_completed_totality', file: PPI,
  claim: 'противоречие возникает, только когда область обязана содержать собственный собиратель, то есть быть завершённой (`russell_requires_completed_totality`).',
  note: 'Новая теорема шага 2 — сводка трёх фактов: стадии ограничены (nat_staged_bounded); по каждой стадии собиратель есть и лежит вне её; область с собирателем не завершена. Closed under the global context.' });
add({ theorem: 'completed_inf_contradicts_P4', file: 'src/foundation/P4CompletedInfinity.v', page_price: 'при условии bridge',
  claim: 'Что P4 исключает завершённую область — `completed_inf_contradicts_P4` (`P4CompletedInfinity.v`), при условии `bridge`: все члены области актуальны уже на начальной стадии (см. Главу 4.1).',
  note: 'completed_inf_contradicts_P4 : CompletedInfSet S -> P4_stage_bounded actual -> bridge S actual -> False; bridge S actual := forall n, S n -> actual 0 n. Условие на странице названо. Closed under the global context.' });
add({ theorem: 'level_foundation_form', file: TIL,
  claim: 'в форме самой аксиомы — `level_foundation_form`',
  note: 'Новая теорема шага 2: forall P : Level -> Prop, (exists l, P l) -> ~ (forall l, P l -> exists l\', P l\' /\\ l\' << l) — в непустой совокупности уровней есть член, ниже которого её членов нет. Closed under the global context.' });

fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
console.log('part10-ch01.json: изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length);
