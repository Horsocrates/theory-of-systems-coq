// Часть X, шаг 5, страницы (2026-11-13, слово автора «А, вноси»): шесть мест главы X.5 внесены;
// четыре заготовки TransfiniteInduction.v сняты (вариант А).
// Запуск: node patch-p10-step-05-pages.cjs   (затем tom-links.cjs relocate + merge ведомости/part10-ch05.json)
// Скрипт повторяем: запись, уже приведённая к новым словам, пропускается.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 13.11 (Часть X, шаг 5, слово автора)';
const OO = 'src/foundation/OrdinalOrders.v';
const norm = (s) => (s || '').replace(/\s+/g, ' ');
const p = path.join(__dirname, 'part10-ch05.json');
const j = JSON.parse(fs.readFileSync(p, 'utf8'));
let n = 0, added = 0;
function fix(pred, fields, keepVerdict) {
  const hit = j.records.filter(pred);
  if (hit.length === 0) return;
  if (hit.length !== 1) throw new Error('ожидалась одна запись, найдено ' + hit.length + ': ' + JSON.stringify(fields).slice(0, 80));
  Object.assign(hit[0], keepVerdict ? {} : { verdict: 'ok' }, fields); n++;
}
const starts = (prefix, th) => (r) => norm(r.claim).startsWith(prefix) && (th === undefined || r.theorem === th);
function add(rec) {
  if (j.records.some((r) => r.theorem === rec.theorem && norm(r.claim) === norm(rec.claim))) return;
  j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); added++;
}
const BELOW = 'ord_below := clos_trans ord_sub, где ord_sub a (OSucc a) и ord_sub (f n) (OLim f) — порядок построения. wf_ord_below : well_founded ord_below; structural_transfinite_ind : (forall a, (forall b, ord_below b a -> P b) -> P a) -> forall a, P a. Closed under the global context.';
const OLD = 'Прежнее отношение ord_lt слева допускает только конечные нотации (ord_lt_left_numeral: ord_lt a b -> exists n, a = nat_to_ord n); lim_not_lt, below_epsilon_0_iff_below_omega — Closed.';

fix(starts('На каждой стадии $n$ актуально лишь конечное'), { theorem: 'tower_stage_is_limit', file: OO,
  claim: 'На каждой стадии $n$ предъявлена одна нотация: для $\\omega$ — конечная, $\\mathrm{OSucc}^n(\\mathrm{OZero})$; для $\\varepsilon_0$ — ступень башни, сама заданная как предел процесса.',
  note: DONE + ': было «на каждой стадии n актуально лишь конечное (OSucc^n(OZero))» — верно для ω, неверно для ε₀. tower_stage_is_limit : forall n, exists g, omega_tower n = OLim g. Closed under the global context.' });
fix(starts('Это даёт трансфинитную индукцию и рекурсию *по нотациям* — без аксиом.', 'transfinite_ind'), { theorem: 'structural_transfinite_ind', file: OO, page_price: 'без аксиом',
  note: DONE + ': слова страницы прежние; теперь они опираются на порядок построения. ' + BELOW + ' Рекурсия — ord_rec с уравнением ord_rec_eq. ' + OLD });
fix(starts('Отношение $\\mathrm{ord\\_lt}$ фундировано, и из этого следуют принципы индукции'), { theorem: 'wf_ord_below', file: OO,
  claim: 'Порядок здесь — порядок построения: ниже нотации лежат её стадии — предшественник успешника и всякая стадия предела (`ord_below`). Он фундирован, и по нему идут индукция, в предельном шаге опирающаяся на все стадии, рекурсия с доказанным уравнением и индукция вплоть до $\\omega$, по ступеням башни и ниже $\\varepsilon_0$.[^2]',
  note: DONE + ': было «отношение ord_lt фундировано, и из этого следуют принципы индукции вплоть до ω, башни и ε₀». ' + OLD + ' ' + BELOW + ' induction_below_epsilon_0, tower_induction, nat_below_omega, tower_below_epsilon_0 — Closed.' });
fix(starts('**Что даёт.** Трансфинитная индукция/рекурсия по нотациям — `wf_ord_lt`'), { theorem: 'structural_transfinite_ind', file: OO, page_price: '0 аксиом',
  claim: '**Что даёт.** Трансфинитная индукция/рекурсия по нотациям — `wf_ord_below`, `structural_transfinite_ind`, `ord_rec_eq` (0 аксиом).',
  note: DONE + ': было «wf_ord_lt, transfinite_ind». ' + BELOW });
fix(starts('Ординалы оказались процессами: $\\mathrm{OLim}$ — предел процесса'), { theorem: 'wf_ord_below', file: OO, page_price: '0 аксиом',
  claim: 'Ординалы оказались процессами: $\\mathrm{OLim}$ — предел процесса, $\\varepsilon_0$ — предел башни, а трансфинитная индукция по конструктивным нотациям структурна и 0-аксиомна (`wf_ord_below`, `structural_transfinite_ind`).',
  note: DONE + ': было «(wf_ord_lt, transfinite_ind)». ' + BELOW });
// три записи с одной прежней цитатой сноски 2
const FN = '`TransfiniteInduction.v`: `wf_ord_lt` (`well_founded ord_lt`), `transfinite_ind`, `transfinite_rec`';
fix(starts(FN, 'transfinite_rec'), { theorem: 'ord_rec_eq', file: OO, page_price: '0 аксиом',
  claim: 'рекурсия `ord_rec` с уравнением `ord_rec_eq`;',
  note: DONE + ': было имя transfinite_rec — теорема без уравнения рекурсии (её тип населён и без фундированности); снята из TransfiniteInduction.v по слову автора (вариант А). ord_rec := Fix wf_ord_below …; ord_rec_eq : (шаг уважает поточечное равенство) -> forall a, ord_rec T step a = step a (fun b _ => ord_rec T step b). Closed under the global context.' });
fix(starts(FN, 'omega_tower_induction'), { theorem: 'tower_induction', file: OO, page_price: '0 аксиом',
  claim: 'индукция по ступеням башни `tower_induction` и ниже $\\varepsilon_0$ — `induction_below_epsilon_0`;',
  note: DONE + ': было имя omega_tower_induction — дословно индукция по ℕ; снята из TransfiniteInduction.v по слову автора (вариант А). tower_induction : P omega -> (forall n, P (omega_tower n) -> P (omega_tower (S n))) -> forall n, P (omega_tower n). Closed under the global context.' });
fix((r) => norm(r.claim).startsWith(FN) && r.theorem !== 'transfinite_rec' && r.theorem !== 'omega_tower_induction', {
  claim: 'Прежнее отношение `ord_lt` (`Ordinal.v`) тоже фундировано (`wf_ord_lt`, `transfinite_ind` в `TransfiniteInduction.v`), но ниже любой нотации по нему лежат только конечные нотации (`ord_lt_left_numeral`): $\\omega$ по нему не ниже $\\omega+1$ и не ниже $\\varepsilon_0$.',
  note: 'wf_ord_lt : well_founded ord_lt; transfinite_ind — индукция по ord_lt. Обе — Closed under the global context. ' + OLD }, true);
fix(starts('(сверено `Print Assumptions`: `wf_ord_lt` и `transfinite_ind` закрыты'), {
  claim: '**0 аксиом** (сверено `Print Assumptions`).',
  note: 'Все утверждения OrdinalOrders.v и TransfiniteInduction.v — Closed under the global context. Шапка TransfiniteInduction.v, прежде называвшая classic и L4_witness, исправлена 13.11.' }, true);

add({ theorem: 'wf_ord_below', file: OO, page_price: '0 аксиом',
  claim: '`OrdinalOrders.v`: порядок построения `ord_below` и его фундированность `wf_ord_below`; индукция `structural_transfinite_ind`;',
  note: 'Новый файл шага 5. ' + BELOW });
add({ theorem: 'induction_below_epsilon_0', file: OO, page_price: '0 аксиом',
  claim: 'индукция по ступеням башни `tower_induction` и ниже $\\varepsilon_0$ — `induction_below_epsilon_0`;',
  note: 'induction_below_epsilon_0 : (forall a, ord_below a epsilon_0 -> (forall b, ord_below b a -> P b) -> P a) -> forall a, ord_below a epsilon_0 -> P a. Closed under the global context.' });
add({ theorem: 'wf_olt', file: OO, page_price: '0 аксиом',
  claim: 'порядок Брауэра `olt` — `wf_olt`, `olt_trans`, `olt_omega_epsilon_0`.',
  note: 'ole — порядок, в котором OLim f есть верхняя грань стадий; olt a b := ole (OSucc a) b. wf_olt : well_founded olt. Closed under the global context.' });
add({ theorem: 'olt_trans', file: OO, page_price: '0 аксиом',
  claim: 'порядок Брауэра `olt` — `wf_olt`, `olt_trans`, `olt_omega_epsilon_0`.',
  note: 'olt_trans : olt a b -> olt b c -> olt a c. Closed under the global context.' });
add({ theorem: 'olt_omega_epsilon_0', file: OO, page_price: '0 аксиом',
  claim: 'Фундирован и порядок сравнения, в котором предел есть верхняя грань стадий (порядок Брауэра, `olt`): в нём $\\omega<\\omega+1$ и $\\omega<\\varepsilon_0$.',
  note: 'olt_omega_succ_omega : olt omega (OSucc omega); olt_omega_epsilon_0 : olt omega epsilon_0. Closed under the global context. Согласованность двух порядков: ord_below_ole — стадия построения не больше.' });
add({ theorem: 'ord_lt_left_numeral', file: OO, page_price: '',
  claim: 'ниже любой нотации по нему лежат только конечные нотации (`ord_lt_left_numeral`)',
  note: 'ord_lt_left_numeral : forall b a, ord_lt a b -> exists n, a = nat_to_ord n. Closed under the global context. Следствия: omega_not_lt_succ_omega, omega_not_lt_epsilon_0, below_epsilon_0_iff_below_omega.' });

fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n');
console.log('part10-ch05.json: изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length);
