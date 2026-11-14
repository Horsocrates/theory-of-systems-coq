// Часть III, шаг 3, страницы (2026-11-14, слово автора «Вноси»): 7 правок главы III.3 и 1 правка главы III.2
// (место 2.3) внесены. Формализация — новый src/CountabilityQValues.v; Countability_Q.v не менялся.
// Запуск: node patch-p03-step-03-pages.cjs  (затем relocate + merge по part03-ch03 и part03-ch02). Скрипт повторяем.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 14.11 (Часть III, шаг 3, слово автора)';
const CL = 'Closed under the global context';
const CV = 'src/CountabilityQValues.v';
const CQ = 'src/Countability_Q.v';
const BS = String.fromCharCode(92);
const AND = '/' + BS;
const LR = '$ℕ ' + BS + 'leftrightarrow ℚ$';
const LRT = '$' + BS + 'leftrightarrow$';
const norm = (s) => (s || '').replace(/\s+/g, ' ').trim();

function open(name) {
  const p = path.join(__dirname, name + '.json');
  const j = JSON.parse(fs.readFileSync(p, 'utf8'));
  let n = 0, added = 0;
  const fix = (prefix, th, fields) => {
    const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix) && (th === undefined || (th === null ? !r.theorem : r.theorem === th)));
    if (!hit.length) return;
    if (hit.length !== 1) throw new Error(name + ': не одна запись: ' + prefix + ' / ' + th);
    Object.assign(hit[0], { verdict: 'ok' }, fields); n++;
  };
  const add = (rec) => {
    if (j.records.some((r) => (r.theorem || null) === (rec.theorem || null) && norm(r.claim) === norm(rec.claim))) return;
    j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); added++;
  };
  const save = () => { fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n'); console.log(name + '.json: изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length); };
  return { j, fix, add, save };
}
const N_QBV = 'Q_bijection_values : (forall n, index_of_Q (enum_Q n) = n) ' + AND + ' (forall q, enum_Q (index_of_Q q) == q) ' + AND + ' (forall q q\', q == q\' <-> index_of_Q q = index_of_Q q\') ' + AND + ' (forall n m, enum_Q n == enum_Q m <-> n = m). ' + CL + '.';

// ---------------------------------------------------------------- III.3
{
  const { fix, add, save } = open('part03-ch03');
  fix('Это *полная биекция ' + LR + ' с вычислимым обращением*', 'Q_bijection', {
    note: DONE + ' (формализацией): слова получили опору — биекция значений в полном виде записана теоремой Q_bijection_values (' + CV + '). Q_bijection (Countability_Q.v:759) — два круговых обхода; ' + CL + '.' });
  const C1 = 'Сами две формулы дают взаимную обратность прямого и обратного хода; до биекции *значений* их доводит третье — номер зависит только от значения дроби (`index_of_Q_Qeq`), — и в полном виде биекция записана теоремой `Q_bijection_values` (файл `CountabilityQValues.v`, тоже без аксиом).';
  add({ theorem: 'index_of_Q_Qeq', file: CV, claim: C1,
    note: 'index_of_Q_Qeq : forall q q\' : Q, q == q\' -> index_of_Q q = index_of_Q q\' (через Qred_complete). ' + CL + '. Что из двух обходов это не следует — roundtrips_do_not_force_value_injectivity.' });
  add({ theorem: 'Q_bijection_values', file: CV, claim: C1, page_price: 'без аксиом', note: N_QBV });
  fix('Потому `index_of_Q_enum_id` точна на $ℕ$ (равенство номеров)', 'Q_bijection', {
    theorem: 'Q_bijection_values', file: CV,
    claim: 'Потому `index_of_Q_enum_id` точна на $ℕ$ (равенство номеров), а `enum_Q_index_id` — с точностью до `Qeq` на $ℚ$; вместе с тем, что равные дроби получают один номер (`index_of_Q_Qeq`), это и есть биекция рациональных *значений* (`Q_bijection_values`).',
    note: DONE + ' (формализацией): было «вместе это и есть биекция значений» при двух обходах. ' + N_QBV });
  fix('и теорема `Q_bijection` доказывает их взаимную обратность — полную биекцию', 'Q_bijection', {
    theorem: 'Q_bijection_values', file: CV,
    claim: 'и теорема `Q_bijection` доказывает их взаимную обратность, а теорема `Q_bijection_values` — полную биекцию ' + LR + ' (с точностью до `Qeq`, 0 аксиом) уже для всего $ℚ$.',
    page_price: '0 аксиом',
    note: DONE + ' (формализацией): полная биекция отнесена к Q_bijection_values. ' + CL + '.' });
  fix('Оговорка о статусе теперь снята: для всего $ℚ$ доказана *полная* биекция', 'Q_bijection', {
    theorem: 'Q_bijection_values', file: CV,
    claim: 'Оговорка о статусе теперь снята: для всего $ℚ$ доказана *полная* биекция ' + LR + ' с вычислимым обращением — две круговые теоремы `enum_Q_index_id` и `index_of_Q_enum_id` и лемма о том, что равные дроби получают один номер (`index_of_Q_Qeq`; сводная теорема `Q_bijection_values`, файл `CountabilityQValues.v`), 0 аксиом',
    page_price: '0 аксиом',
    note: DONE + ' (формализацией): названо третье утверждение, без которого биекции значений нет. ' + CL + '.' });
  fix('И правило канона: несократимость (`enum_coprime`) — всякое рациональное *значение* встречается ровно раз', 'enum_coprime', {
    theorem: 'enum_QPos_each_value_once', file: CV,
    claim: 'И правило канона: несократимость (`enum_coprime`) — в обходе стоят только несократимые пары, и потому всякое положительное рациональное *значение* встречается ровно раз (`enum_QPos_each_value_once`), $2/4$ не появляется отдельно от $1/2$ (§ 3.3).',
    note: DONE + ' (формализацией): enum_QPos_each_value_once : forall q, 0 < q -> exists n, qpos_to_Q (enum_QPos n) == q ' + AND + ' forall m, qpos_to_Q (enum_QPos m) == q -> m = n. ' + CL + '. enum_coprime (Countability_Q.v:189) — взаимная простота пар обхода.' });
  fix('| навигация ' + LRT + ' номер; обратимость | биекция `nat` ' + LRT + ' `QPos` | Rule |', 'QPos', {
    theorem: 'enum_QPos_bijection_coprime', file: CV,
    claim: '| навигация ' + LRT + ' номер; обратимость | биекция `nat` ' + LRT + ' несократимые пары `QPos` (`enum_QPos_bijection_coprime`) | Rule |',
    note: DONE + ': было «биекция nat ↔ QPos». Обход взаимно однозначен с несократимыми парами: enum_QPos_bijection_coprime (три конъюнкта). Пара (2, 4) не достигается — enum_QPos_misses_2_4. ' + CL + '.' });
  fix('| несократимость (`enum_coprime`) | каждое значение однажды | Rule |', 'enum_coprime', {
    theorem: 'enum_QPos_each_value_once', file: CV,
    claim: '| несократимость (`enum_coprime`) | каждое значение однажды (`enum_QPos_each_value_once`) | Rule |',
    note: DONE + ' (формализацией): «каждое значение однажды» — теорема enum_QPos_each_value_once. ' + CL + '.' });
  save();
}
// ---------------------------------------------------------------- III.2 (место 2.3)
{
  const { fix, add, save } = open('part03-ch02');
  fix('*полная* биекция ' + LR + ' с вычислимым обращением доказана не только для положительных', 'Q_bijection', {
    note: DONE + ' (формализацией, шаг 3): биекция значений в полном виде — Q_bijection_values (' + CV + '); страница называет её ниже в том же абзаце. Q_bijection (Countability_Q.v:759) — два круговых обхода; ' + CL + '.' });
  fix('теорема `Q_bijection` доказывает — тоже без аксиом, — что они взаимно обратны (с точностью до `Qeq`: $2/4$', 'Q_bijection', {
    claim: 'теорема `Q_bijection` доказывает — тоже без аксиом, — что они взаимно обратны (с точностью до `Qeq`);',
    page_price: 'без аксиом',
    note: 'Взаимная обратность: первая формула — равенством номеров, вторая — с точностью до Qeq. ' + CL + '.' });
  add({ theorem: 'Q_bijection_values', file: CV,
    claim: 'что равные дроби — $2/4$ и $1/2$ — получают один номер и что обход не повторяет значений, доказано отдельно (теорема `Q_bijection_values`, файл `CountabilityQValues.v`).',
    note: N_QBV });
  save();
}
