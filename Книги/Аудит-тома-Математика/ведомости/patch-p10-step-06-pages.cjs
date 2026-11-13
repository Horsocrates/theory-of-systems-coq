// Часть X, шаг 6, страницы (2026-11-13, слово автора «Делай»): семь мест главы X.5, по одному месту
// глав X.6 и I.6, два места главы IV.1 и одно место страницы «Формализация» внесены.
// Запуск: node patch-p10-step-06-pages.cjs   (затем relocate + merge по part10-ch05, part10-ch06, part04-ch01)
// Скрипт повторяем: запись, уже приведённая к новым словам, пропускается.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 13.11 (Часть X, шаг 6, слово автора)';
const F = 'src/foundation/';
const norm = (s) => (s || '').replace(/\s+/g, ' ');
function open(name) {
  const p = path.join(__dirname, name);
  const j = JSON.parse(fs.readFileSync(p, 'utf8'));
  let n = 0, added = 0;
  return {
    fix(prefix, th, fields, keepVerdict) {
      const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix) && (th === undefined || r.theorem === th));
      if (hit.length === 0) return;
      if (hit.length !== 1) throw new Error(name + ': ожидалась одна запись «' + prefix.slice(0, 50) + '» / ' + th + ', найдено ' + hit.length);
      Object.assign(hit[0], keepVerdict ? {} : { verdict: 'ok' }, fields); n++;
    },
    add(rec) {
      if (j.records.some((r) => r.theorem === rec.theorem && norm(r.claim) === norm(rec.claim))) return;
      j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); added++;
    },
    // запись о переменной раздела: сторож её с компилятором не сверяет («не применимо …»)
    sectionVar(name, assumptions) {
      for (const r of j.records) if (r.theorem === name && r.external) r.assumptions = assumptions;
    },
    save() { fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n'); console.log(name + ': изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length); },
  };
}
const SEC = 'С 13.11 eval_program — переменная раздела Section Codes (а не Parameter): все утверждения файла верны для любой таблицы Program -> nat -> nat; в выводе Print Assumptions её нет.';
const PI = 'P4_eliminates_Pi11 : forall eval_program phi n, P4_forall_functions eval_program phi n <-> (forall f, (exists c, f = eval_program c) -> phi f n). Closed under the global context.';

// ------------------------------------------------------------------ глава X.5
const a = open('part10-ch05.json');
const WHAT = 'ATR$_0$/$\\Pi^1_1$/Бесконечность/импредикативность — переинтерпретированы (`P4_eliminates_ATR0`,';
const WHATNEW = 'ATR$_0$/$\\Pi^1_1$/Бесконечность/импредикативность — переинтерпретированы (`P4_eliminates_ATR0`, `P4_eliminates_Pi11`, `P4_eliminates_Infinity`, `russell_requires_completed_totality`; всё — 0 аксиом).';
a.fix(WHAT, 'P4_eliminates_ATR0', { claim: WHATNEW }, true);
a.fix(WHAT, 'P4_eliminates_Pi11', { claim: WHATNEW, page_price: '0 аксиом', note: PI + ' ' + SEC }, true);
a.fix(WHAT, 'P4_eliminates_Infinity', { claim: WHATNEW, page_price: '0 аксиом',
  note: 'P4_eliminates_Infinity (после шага 6): индукция /\\ (forall l : list nat, exists n, ~ In n l) /\\ (forall n, exists m, n < m). Closed under the global context.' }, true);
a.fix(WHAT, 'P4ProhibitsImpredicative', { claim: WHATNEW, theorem: 'russell_requires_completed_totality', file: F + 'P4ProhibitsImpredicative.v', page_price: '0 аксиом',
  note: DONE + ': было имя файла `P4ProhibitsImpredicative` в перечне теорем; теперь названа теорема russell_requires_completed_totality (шаг 2). Closed under the global context.' });
a.fix(WHAT, 'eval_program', { theorem: 'no_table_covers_all_functions', file: F + 'P4_Eliminates_Pi11.v', page_price: '',
  claim: 'никакая таблица кодов не содержит всех функций — диагональная функция в неё не входит, — и квантор по кодам строго слабее квантора по функциям (`no_table_covers_all_functions`, `codes_reading_is_weaker`).',
  note: DONE + ': запись прежде относилась к словам «при примитиве eval_program» (сняты: ' + SEC + '). no_table_covers_all_functions : forall eval_program, ~ (forall f, exists c, f = eval_program c). Closed under the global context.' }, true);
a.fix('Арифметика ($+,\\cdot,{}^\\wedge$) — структурной рекурсией, но часть её лемм', undefined, { theorem: 'ord_add_zero_l', file: F + 'Ordinal.v', page_price: 'все 24 леммы закрыты',
  claim: 'Арифметика ($+,\\cdot,{}^\\wedge$) — структурной рекурсией; два тождества, проходящие через предел (`ord_add_zero_l`, `ord_mul_one_r`), записаны с точностью до постадийного равенства `ord_eq`, и функциональная экстенсиональность не привлекается: все 24 леммы файла закрыты.',
  note: DONE + ': было «часть её лемм опирается на функциональную экстенсиональность» — устарело после правки 12.11. ord_add_zero_l : forall a, ord_eq (ord_add OZero a) a. Closed under the global context; в Ordinal.v 24 Qed.' });
a.fix('`P4_Eliminates_ATR.v`: `CB_transfinite` — трансфинитная итерация (производная', 'CB_transfinite', { theorem: 'CB_transfinite_succ_stage', file: F + 'P4_Eliminates_ATR.v',
  claim: 'Пример `CB_transfinite` взят для модельного оператора `CB_step` (точка остаётся, если у неё есть сосед на расстоянии 1) — дискретного подобия производной Кантора–Бендиксона; его итерация стоит на месте уже после первого шага (`CB_transfinite_succ_stage`, `CB_transfinite_omega`).',
  note: DONE + ': было «CB_transfinite — трансфинитная итерация (производная Кантора–Бендиксона)». CB_transfinite_succ_stage : CB_transfinite X (OSucc a) n <-> CB_step X n; CB_transfinite_omega — то же на стадии omega. Closed under the global context.' });
a.fix('15 Qed, 0 аксиом (сверено `Print Assumptions`: Closed).', undefined, {
  claim: '22 Qed, 0 аксиом (сверено `Print Assumptions`: Closed).',
  note: DONE + ': было 15; в P4_Eliminates_ATR.v 22 Qed (17 прежних и пять новых шага 6).' });
a.fix('`P4_Eliminates_Pi11.v`: `Program := nat`, `P4_forall_functions` (квантор по функциям через коды', undefined, {
  claim: '`P4_Eliminates_Pi11.v`: `Program := nat`; `P4_forall_functions` — квантор по кодам;' }, true);
a.fix('итог — `P4_eliminates_Pi11`.', 'P4_eliminates_Pi11', { page_price: '0 аксиом',
  claim: 'Итог — `P4_eliminates_Pi11`: квантор по кодам есть квантор по функциям, *заданным кодами*.',
  note: DONE + ': прежде обе стороны равносильности совпадали по определению; теорема переписана. ' + PI });
a.fix('По `Print Assumptions` — 0 логических аксиом, но зависит от `eval_program`', 'eval_program', { theorem: 'P4_forall_functions', file: F + 'P4_Eliminates_Pi11.v', page_price: '0 аксиом',
  claim: 'таблица кодов `eval_program` — переменная раздела без каких-либо свойств, так что все утверждения верны для любой таблицы.',
  note: DONE + ': было «зависит от eval_program (Parameter — вычислительный примитив универсальной машины)». ' + SEC + ' Definition P4_forall_functions eval_program phi n := forall c : Program, phi (eval_program c) n.' });
a.fix('`P4_Eliminates_Infinity.v`: `converges` (сходимость приближений)', 'converges', { theorem: 'converges_unique', file: F + 'P4_Eliminates_Infinity.v',
  claim: '`converges` — сходимость последовательности натуральных чисел: это стабилизация, и предел единствен (`converges_iff_stabilizes`, `converges_unique`).',
  note: DONE + ': определение converges усилено до строгого неравенства (прежде постоянная последовательность 1 «сходилась» к 0, 1 и 2). converges_unique : converges a L1 -> converges a L2 -> L1 = L2. Closed under the global context.' });
a.fix('итог — `P4_eliminates_Infinity`.', 'P4_eliminates_Infinity', { page_price: '0 аксиом',
  claim: '`P4_Eliminates_Infinity.v`: итог — `P4_eliminates_Infinity`: правило индукции; никакая конечная стадия не исчерпывает натуральных чисел (`no_finite_stage_exhausts_nat`); за всяким числом есть большее.',
  note: DONE + ': прежде итог соединял четыре факта, не связанных с бесконечностью (индукция, n < n+1, 5! = 120, 0+1+2+3 = 6); теорема переписана. Closed under the global context.' });
a.fix('12 Qed, 0 аксиом.', undefined, { claim: '13 Qed, 0 аксиом.', note: DONE + ': было 12; в P4_Eliminates_Infinity.v 13 Qed.' });
a.fix('`P4ProhibitsImpredicative.v`: P1${}+{}$P4 исключают завершённую тотальность', undefined, { theorem: 'russell_collector_escapes', file: F + 'P4ProhibitsImpredicative.v',
  claim: '`P4ProhibitsImpredicative.v`: собиратель расселова условия по области сам в эту область не входит (`russell_collector_escapes`); по каждой конечной стадии он существует и лежит вне стадии (`staged_russell_collector_exists`); область, у которой он есть, не завершена (`russell_needs_incomplete_range`).',
  note: DONE + ': было «P1 + P4 исключают завершённую тотальность» — теоремы не было; три теоремы добавлены на шаге 2. Closed under the global context.' });
a.fix('10 Qed, 0 аксиом.', undefined, { claim: '11 Qed, 0 аксиом.', note: DONE + ': было 10; в P4ProhibitsImpredicative.v 11 Qed (7 прежних и четыре шага 2).' });
a.add({ theorem: 'iterate_pred', file: F + 'P4_Eliminates_ATR.v',
  claim: '`P4_Eliminates_ATR.v`: `iterate_pred` — итерация произвольного оператора на подмножествах $ℕ$ вдоль нотации как `Fixpoint` на `Ord`;',
  note: 'Fixpoint iterate_pred (P : (nat -> Prop) -> (nat -> Prop)) (alpha : Ord) (base : nat -> Prop) — структурная рекурсия по локальной копии типа Ord.' });
a.add({ theorem: 'CB_ord_omega', file: 'src/settheory/CantorBendixsonFull.v', page_price: '0 аксиом',
  claim: 'Настоящая производная итерируется вдоль нотаций в `CantorBendixsonFull.v`: `CB_ord`, на конечных нотациях совпадающая с `CB_iter`, на $\\omega$ — с `CB_omega` (`CB_ord_nat`, `CB_ord_omega`).',
  note: 'Новое шага 6: Fixpoint CB_ord (X : PointSet) (a : Ord); CB_ord_nat : CB_ord X (nat_to_ord n) = CB_iter X n; CB_ord_omega : CB_ord X omega x <-> CB_omega X x. Closed under the global context. Множество, у которого стадии выше первой различны, не строилось.' });
a.add({ theorem: 'pi11_hierarchy_collapse', file: F + 'P4_Eliminates_Pi11.v', page_price: '0 аксиом',
  claim: 'Совпадение с квантором по всем функциям имеет место ровно при условии «всякая функция имеет код» (`pi11_hierarchy_collapse`), а оно не выполняется ни для какой таблицы (`no_table_covers_all_functions`).',
  note: 'pi11_hierarchy_collapse (после шага 6): (forall f, exists c, f = eval_program c) -> forall n, (forall f, phi f n) <-> P4_forall_functions eval_program phi n. Closed under the global context. Слово «ровно»: обратное — что без этого условия совпадения нет — показывает codes_reading_is_weaker.' });
a.add({ theorem: 'pi11_negation', file: F + 'P4_Eliminates_Pi11.v', page_price: 'classic',
  claim: 'По `Print Assumptions` — 0 аксиом; одна лемма файла, `pi11_negation`, стоит на `classic`.',
  note: 'pi11_negation: Axioms: Classical_Prop.classic. Остальные утверждения файла — Closed under the global context.' });
const EV = { theorem: 'eval_program', file: F + 'P4_Eliminates_Pi11.v', external: true,
  assumptions: 'не применимо (переменная раздела Section Codes, не объявление верхнего уровня)',
  note: 'С 13.11 eval_program — переменная раздела файла P4_Eliminates_Pi11.v: Variable eval_program : Program -> nat -> nat. Прежде — Parameter.' };
a.add(Object.assign({ claim: 'таблица кодов `eval_program` — переменная раздела без каких-либо свойств, так что все утверждения верны для любой таблицы.' }, EV));
a.add({ theorem: 'codes_reading_is_weaker', file: F + 'P4_Eliminates_Pi11.v', page_price: '0 аксиом',
  claim: 'квантор по кодам строго слабее квантора по функциям (`no_table_covers_all_functions`, `codes_reading_is_weaker`).',
  note: 'codes_reading_is_weaker : forall eval_program, exists phi, (forall n, P4_forall_functions eval_program phi n) /\\ ~ (forall n f, phi f n). Closed under the global context.' });
a.add({ theorem: 'ord_mul_one_r', file: F + 'Ordinal.v', page_price: 'закрыта',
  claim: 'два тождества, проходящие через предел (`ord_add_zero_l`, `ord_mul_one_r`), записаны с точностью до постадийного равенства `ord_eq`',
  note: 'ord_mul_one_r : forall a, ord_eq (ord_mul a (OSucc OZero)) a. Closed under the global context.' });
a.add({ theorem: 'CB_ord_nat', file: 'src/settheory/CantorBendixsonFull.v', page_price: '0 аксиом',
  claim: '`CB_ord`, на конечных нотациях совпадающая с `CB_iter`, на $\\omega$ — с `CB_omega` (`CB_ord_nat`, `CB_ord_omega`).',
  note: 'CB_ord_nat : forall X n, CB_ord X (nat_to_ord n) = CB_iter X n. Closed under the global context.' });
a.add({ theorem: 'CB_transfinite_omega', file: F + 'P4_Eliminates_ATR.v', page_price: '0 аксиом',
  claim: 'его итерация стоит на месте уже после первого шага (`CB_transfinite_succ_stage`, `CB_transfinite_omega`).',
  note: 'CB_transfinite_omega : forall X n, CB_transfinite X omega n <-> CB_step X n. Closed under the global context.' });
a.add({ theorem: 'converges_iff_stabilizes', file: F + 'P4_Eliminates_Infinity.v', page_price: '0 аксиом',
  claim: 'это стабилизация, и предел единствен (`converges_iff_stabilizes`, `converges_unique`).',
  note: 'converges_iff_stabilizes : converges a L <-> exists N, forall n, n >= N -> a n = L. Closed under the global context.' });
a.add({ theorem: 'no_finite_stage_exhausts_nat', file: F + 'P4_Eliminates_Infinity.v', page_price: '0 аксиом',
  claim: 'никакая конечная стадия не исчерпывает натуральных чисел (`no_finite_stage_exhausts_nat`);',
  note: 'no_finite_stage_exhausts_nat : forall l : list nat, exists n, ~ In n l. Closed under the global context.' });
a.add({ theorem: 'completed_inf_contradicts_P4', file: F + 'P4CompletedInfinity.v', page_price: 'при условии bridge',
  claim: 'Что P4 исключает завершённую область — `completed_inf_contradicts_P4`, при условии `bridge` (Глава 10.4).',
  note: 'completed_inf_contradicts_P4 : CompletedInfSet S -> P4_stage_bounded actual -> bridge S actual -> False. Условие названо. Closed under the global context.' });
a.add({ theorem: 'russell_needs_incomplete_range', file: F + 'P4ProhibitsImpredicative.v', page_price: '0 аксиом',
  claim: 'область, у которой он есть, не завершена (`russell_needs_incomplete_range`).',
  note: 'russell_needs_incomplete_range : (forall x, T x -> (mem x r <-> ~ mem x x)) -> ~ CompletedInfSet T. Closed under the global context.' });
a.add({ theorem: 'staged_russell_collector_exists', file: F + 'P4ProhibitsImpredicative.v', page_price: '0 аксиом',
  claim: 'по каждой конечной стадии он существует и лежит вне стадии (`staged_russell_collector_exists`);',
  note: 'staged_russell_collector_exists : forall stage, exists r, (условие Рассела по стадии) /\\ ~ nat_staged_actual stage r /\\ nat_staged_actual (S stage) r. Closed under the global context.' });
a.sectionVar('eval_program', EV.assumptions);
a.save();

// ------------------------------------------------------------------ глава X.6, строка таблицы
const b = open('part10-ch06.json');
const ROWOLD = '| вычислительный примитив | $\\Pi^1_1$-переинтерпретация';
const ROWNEW = '| 0 аксиом, для любой таблицы кодов | $\\Pi^1_1$-переинтерпретация: `eval_program` — переменная раздела без свойств, не параметр |';
b.fix(ROWOLD, 'P4_eliminates_Pi11', { claim: ROWNEW, page_price: '0 аксиом', note: DONE + '. ' + PI + ' ' + SEC + ' Одна лемма файла, pi11_negation, стоит на classic.' }, true);
b.fix(ROWOLD, 'eval_program', { claim: ROWNEW, theorem: 'P4_forall_functions', file: F + 'P4_Eliminates_Pi11.v', page_price: '0 аксиом', note: DONE + '. ' + SEC }, true);
b.add(Object.assign({ claim: ROWNEW }, EV));
b.sectionVar('eval_program', EV.assumptions);
b.save();

// ------------------------------------------------------------------ глава IV.1
const c = open('part04-ch01.json');
c.fix('а функция восстанавливается через параметр `eval_program`', 'eval_program', { theorem: 'P4_forall_functions', file: F + 'P4_Eliminates_Pi11.v',
  claim: 'а функция восстанавливается через таблицу кодов `eval_program`',
  note: DONE + ': было «через параметр eval_program». ' + SEC }, true);
c.fix('И `eval_program` здесь — не доказанное утверждение и не определённая функция, а *неинтерпретированный', 'eval_program', { theorem: 'P4_forall_functions', file: F + 'P4_Eliminates_Pi11.v',
  claim: 'И `eval_program` здесь — не доказанное утверждение и не определённая функция, а *переменная раздела*: произвольная таблица, сопоставляющая коду функцию, без каких-либо свойств.',
  note: DONE + ': было «неинтерпретированный объявленный параметр… соответствующая универсальной машине Тьюринга». ' + SEC }, true);
c.fix('прочие три файла слоя ненужности обходятся вовсе без подобных объявлений.', undefined, { theorem: 'pi11_negation', file: F + 'P4_Eliminates_Pi11.v', verdict: 'mismatch-price', page_price: 'допущений не имеют',
  claim: 'Все утверждения файла верны для любой такой таблицы и допущений не имеют.',
  note: 'Фраза внесена 13.11 (Часть X, шаг 6) с неточностью, моей: одна лемма файла, pi11_negation, стоит на Classical_Prop.classic; остальные — Closed under the global context. Поправка слов показана автору со следующим шагом.' }, true);
c.add({ theorem: 'no_table_covers_all_functions', file: F + 'P4_Eliminates_Pi11.v', page_price: '0 аксиом',
  claim: 'Доказано и то, что ни одна таблица не содержит всех функций: диагональная функция в неё не входит (`no_table_covers_all_functions`).',
  note: 'Фраза добавлена 13.11 (Часть X, шаг 6, слово автора). no_table_covers_all_functions : forall eval_program, ~ (forall f, exists c, f = eval_program c). Closed under the global context.' });
c.add(Object.assign({ claim: 'а функция восстанавливается через таблицу кодов `eval_program`' }, EV));
c.sectionVar('eval_program', EV.assumptions);
c.save();
