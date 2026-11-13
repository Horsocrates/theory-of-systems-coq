// Часть X, шаг 4, страницы (2026-11-13, слово автора «Делай»): десять мест главы X.4 и одно место
// главы IV.1 внесены.
// Запуск: node patch-p10-step-04-pages.cjs   (затем tom-links.cjs relocate + merge по part10-ch04 и part04-ch01)
// Скрипт повторяем: запись, уже приведённая к новым словам, пропускается.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 13.11 (Часть X, шаг 4, слово автора)';
const AC = 'src/foundation/P4ProhibitsAC.v';
const CI = 'src/foundation/P4CompletedInfinity.v';
const EA = 'src/foundation/P4_Eliminates_AC.v';
const PS = 'src/foundation/P4ProhibitionSynthesis.v';
const CW = 'src/settheory/CardinalityWithoutChoice.v';
const norm = (s) => (s || '').replace(/\s+/g, ' ');
function open(name) {
  const p = path.join(__dirname, name);
  const j = JSON.parse(fs.readFileSync(p, 'utf8'));
  let n = 0, added = 0;
  return {
    // одна запись; при нескольких с той же цитатой берётся запись с расхождением
    fix(prefix, fields, keepVerdict) {
      let hit = j.records.filter((r) => norm(r.claim).startsWith(prefix));
      if (hit.length > 1) hit = hit.filter((r) => r.verdict !== 'ok');
      if (hit.length === 0) return;
      if (hit.length !== 1) throw new Error(name + ': ожидалась одна запись «' + prefix + '», найдено ' + hit.length);
      Object.assign(hit[0], keepVerdict ? {} : { verdict: 'ok' }, fields); n++;
    },
    // все записи с этой цитатой: меняется только цитата
    reclaim(prefix, claim) {
      for (const r of j.records) if (norm(r.claim).startsWith(prefix)) { r.claim = claim; n++; }
    },
    add(rec) {
      if (j.records.some((r) => r.theorem === rec.theorem && norm(r.claim) === norm(rec.claim))) return;
      j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); added++;
    },
    save() { fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n'); console.log(name + ': изменено ' + n + ', добавлено ' + added + ', всего ' + j.records.length); },
  };
}
const STR = 'completed_reading_strictly_stronger : (forall S actual, bridge S actual -> rule_reading S actual) /\\ (forall f, exists actual, P4_stage_bounded actual /\\ rule_reading (graph_indices (choice_graph f)) actual /\\ ~ bridge (graph_indices (choice_graph f)) actual). Closed under the global context.';
const CUT = 'P4_cuts_completed_keeps_rule : для семейства непустых списков F — (1) для всякой функции выбора f и всякой стадийно ограниченной актуальности мост для графика f невозможен; (2) есть функция выбора и ограниченная актуальность, при которой график читается как правило (rule_reading). Closed under the global context.';

const a = open('part10-ch04.json');
// --- записи с расхождением ---
a.fix('но появляется в переходе сюръекция${}\\to{}$инъекция и в требовании линейности кардинальной шкалы', { theorem: 'surjects_injects_back', file: CW,
  note: 'закрыто 13.11 (Часть X, шаг 1): страница не менялась. Выбор действительно входит в переходе «сюръекция → вложение»: surjects_injects_back выводится из L4_witness, применённого к слою (свидетель не единствен); Шрёдеру — Бернштейну хватает единственного свидетеля (Schroeder_Bernstein_definite, Closed). Теоремы о линейности порядка вложений в формализации нет.' });
a.fix('Из той же конечности следует и «конечная лемма Цорна»: в непустом конечном списке есть максимальный элемент', { theorem: 'finite_zorn_general', file: EA, page_price: 'без выбора',
  note: DONE + ': страница не менялась; слова «максимальный элемент» теперь опираются на теорему для любого типа и любого разрешимого транзитивного отношения: finite_zorn_general : forall A (le : A -> A -> bool), транзитивность -> forall l, l <> nil -> exists m, In m l /\\ forall n, In n l -> le m n = true -> le n m = true. Closed under the global context. Прежняя finite_zorn — наибольшее число в списке натуральных.' });
a.fix('А P4 (конечная актуальность) требует, чтобы на каждой стадии было актуально лишь конечное. Завершённая бесконечная', { page_price: 'условная теорема: при мосте',
  claim: 'А P4 (конечная актуальность) требует, чтобы на каждой стадии было актуально лишь конечное. График с парой на всяком индексе, стадийная ограниченность и мост вместе дают противоречие.[^4] Теорема условная: без моста противоречия нет.',
  note: DONE + ': было «завершённая бесконечная совокупность нарушает эту ограниченность — противоречие» без третьей посылки. completed_inf_contradicts_P4 : CompletedInfSet S -> P4_stage_bounded actual -> bridge S actual -> False. Closed under the global context. Без моста первые две посылки совместны.' });
a.fix('ToS не запрещает бесконечные *процессы*: потенциальная бесконечность с P4 вполне совместима.[^5]', { theorem: 'potential_process_compatible_with_P4', file: CI,
  note: DONE + ': страница не менялась; слова теперь опираются на теорему о процессе: potential_process_compatible_with_P4 : exists actual, P4_stage_bounded actual /\\ (стадии вложены) /\\ (всякое число достигается) /\\ (ни одна стадия не содержит всего). Closed under the global context.' });
a.fix('Два уровня — не одно и то же, и их связь сама есть теорема.', { theorem: 'completed_reading_strictly_stronger', file: AC,
  claim: 'Их связь выражена теоремой о двух чтениях графика: чтение «завершённое целое» требует строго больше, чем чтение «правило по запросу»; P4 отсекает первое и оставляет второе (`completed_reading_strictly_stronger`, `P4_cuts_completed_keeps_rule`).',
  note: DONE + ': было «их связь сама есть теорема» со ссылкой на prohibition_implies_reinterpretation, которая посылку не использует. ' + STR });
a.fix('В формальном синтезе запрет *даёт* переинтерпретацию (если завершённый объект невозможен', { theorem: 'P4_cuts_completed_keeps_rule', file: AC,
  claim: 'Отсюда и соотношение уровней: если завершённый объект невозможен, он тем более не нужен как постулат, тогда как наличие замены само по себе невозможности исходного не даёт — в этом смысле запрет сильнее.[^6]',
  note: DONE + ': было «в формальном синтезе запрет даёт переинтерпретацию… одна переинтерпретация противоречия не даёт» со ссылкой на две сводные теоремы. Соотношение уровней — рассуждение; теоремой выражено соотношение двух чтений графика. ' + CUT });
a.fix('Поэтому результаты 10.3 (Шрёдер–Бернштейн, антисимметрия) используют L4, но *не* выбор: L4 обращает', { theorem: 'Schroeder_Bernstein_definite', file: 'src/SchroederBernstein_ERR.v',
  claim: 'Поэтому результаты 10.3 (Шрёдер–Бернштейн, антисимметрия) используют L4, но *не* выбор: в их доказательствах L4 извлекает только *единственного* свидетеля, и это закреплено теоремой — им хватает исключённого третьего и извлечения единственного свидетеля (`Schroeder_Bernstein_definite`).',
  note: DONE + ': было «L4 обращает единственное, а выбор отбирал бы по слоям» — по компилятору аксиома делает и то, и другое. Schroeder_Bernstein_definite: заключение из двух посылок (исключённое третье; извлечение единственного свидетеля) — Closed under the global context.' });
a.fix('(в 10.3 он применялся через `L4_definite`); его цена учитывается *отдельно* от выбора.', { theorem: 'surjects_injects_back', file: CW, page_price: 'L4_witness',
  claim: 'Сама аксиома `L4_witness` записана без условия единственности и, применённая к каждому слою, такой отбор даёт (`surjects_injects_back`): граница между L4 и выбором проходит по тому, единствен ли свидетель.',
  note: DONE + ': было «(в 10.3 он применялся через L4_definite)» — путей было два; после шага 1 доказательство перестроено на посылки. surjects_injects_back : surjects A B -> injects B A; Axioms: ToS_Axioms.L4_witness.' });
a.fix('Полная форма — запрещена (`P4_prohibits_AC`, `completed_inf_contradicts_P4`).', { theorem: 'AC_on_nat_as_rule', file: AC,
  claim: 'Полная форма как утверждение совпадает с ядром и тоже доказана (`AC_on_nat_as_rule`); запрещено её чтение — график функции выбора как завершённое целое (`ac_completed_graph_contradicts_P4`, при мосте).',
  note: DONE + ': было «полная форма — запрещена». AC_on_nat_as_rule : AC_on_nat (утверждение совпадает с AC_is_L5). Closed under the global context. Несовместимо с P4 чтение графика как завершённого целого: ac_completed_graph_contradicts_P4, при посылке bridge.' });
a.fix('Связь — `prohibition_implies_reinterpretation` (запрет сильнее).', { theorem: 'P4_cuts_completed_keeps_rule', file: AC,
  claim: 'Связь — `P4_cuts_completed_keeps_rule` и `completed_reading_strictly_stronger`: чтение-график несовместимо с P4, чтение-правило совместимо, и первое требует строго больше второго.',
  note: DONE + ': было «связь — prohibition_implies_reinterpretation (запрет сильнее)». ' + CUT + ' ' + STR });
a.fix('и запрет строго сильнее переинтерпретации (`prohibition_implies_reinterpretation`).', { theorem: 'P4_cuts_completed_keeps_rule', file: AC,
  claim: 'и запрет сильнее переинтерпретации: P4 отсекает завершённое чтение графика и оставляет чтение-правило (`P4_cuts_completed_keeps_rule`).',
  note: DONE + ': было «запрет строго сильнее переинтерпретации (prohibition_implies_reinterpretation)». ' + CUT });
a.fix('`P4_prohibits_AC`. И `P4CompletedInfinity.v`: `CompletedInfSet` против `P4_stage_bounded`, итог', { page_price: '0 аксиом; три посылки',
  claim: 'И `P4CompletedInfinity.v`: `CompletedInfSet`, `P4_stage_bounded` и мост `bridge` (всякий член совокупности актуален уже на начальной стадии); итог — `completed_inf_contradicts_P4`: три посылки вместе противоречивы.',
  note: DONE + ': было «CompletedInfSet против P4_stage_bounded, итог — completed_inf_contradicts_P4» без третьей посылки. bridge S actual := forall n, S n -> actual 0 n. Closed under the global context.' });
a.fix('`P4CompletedInfinity.v`: `potential_compatible_with_P4` — потенциальная бесконечность не противоречит P4.', { theorem: 'potential_process_compatible_with_P4', file: CI,
  claim: '`P4CompletedInfinity.v`: `potential_process_compatible_with_P4` — есть процесс стадий, ограниченный на каждой стадии, вложенный, достигающий всякого числа и ни на одной стадии не содержащий всего.',
  note: DONE + ': было «potential_compatible_with_P4 — потенциальная бесконечность не противоречит P4» (та лемма соединяет два независимых факта и выполняется на пустой актуальности). Новая теорема — о процессе стадий. Closed under the global context.' });
a.fix('`P4ProhibitionSynthesis.v`: `prohibition_implies_reinterpretation` (запрет влечёт переинтерпретацию)', { theorem: 'prohibition_implies_reinterpretation', file: PS,
  claim: 'теорема `prohibition_implies_reinterpretation` там — тоже сводка: посылку она не использует (см. Главу 4.1).',
  note: DONE + ': было «prohibition_implies_reinterpretation (запрет влечёт переинтерпретацию)». Доказательство: intros _. exact potential_inf_exists. — посылка не используется; страница это теперь говорит. Closed under the global context.' });
a.fix('`reinterpretation_weaker` (обратное неверно)', { theorem: 'completed_reading_strictly_stronger', file: AC,
  claim: '`P4ProhibitsAC.v`: `completed_reading_strictly_stronger` — мост влечёт чтение-правило, а для графика любой функции есть стадийно ограниченная актуальность, при которой чтение-правило выполнено, а мост — нет;',
  note: DONE + ': было «reinterpretation_weaker (обратное неверно)» — та лемма утверждает одну потенциальную бесконечность, а обратная импликация в Rocq доказуема; имя со страницы снято. ' + STR });
// --- записи с вердиктом «верно», чьи цитаты изменились ---
a.reclaim('Ключевой момент: такая $f$, взятая разом по *всем* $n$ как готовый объект',
  'Ключевой момент: график такой $f$ (в коде это `choice_graph` — совокупность пар «индекс, значение») содержит пару на всяком индексе.');
a.reclaim('**Что даёт.** Допустимое ядро — теорема (`AC_is_L5`, `P4_eliminates_AC_finite`, `finite_zorn`; 0 аксиом).',
  '**Что даёт.** Допустимое ядро — теорема (`AC_is_L5`, `P4_eliminates_AC_finite`, `finite_zorn_general`; 0 аксиом).');
a.reclaim('`finite_zorn` (`P4_Eliminates_AC.v`): $\\forall l\\neq\\varnothing',
  'Частный случай для натуральных чисел — `finite_zorn`: $\\forall l\\neq\\varnothing,\\ \\exists m\\in l,\\ \\forall n\\in l,\\ n\\le m$. 0 аксиом.');
a.reclaim('`ac_implies_completed` (AC даёт завершённый граф)',
  '`ac_implies_completed` (AC даёт функцию, график которой имеет пару на всяком индексе)');
a.reclaim('`CompletedInfSet` против `P4_stage_bounded`',
  '`CompletedInfSet`, `P4_stage_bounded` и мост `bridge`');
a.reclaim('`P4_is_prohibition`. 0 аксиом.',
  '`P4ProhibitionSynthesis.v` собирает оба уровня в сводках `P4_prohibits_three`, `P4_preserves_three`, `P4_is_prohibition`;');
a.reclaim('По силе они сопоставимы (`l4_statement_gives_functional_choice`); различие',
  'По силе: из неё выводятся выбор функции по семейству (`l4_statement_gives_functional_choice`) и переход «сюръекция → вложение» (`surjects_injects_back`, Глава 10.3); различие — в категории: правило против завершённого объекта.');
// --- новые записи ---
a.add({ theorem: 'finite_zorn_general', file: EA, page_price: '0 аксиом',
  claim: '`finite_zorn_general` (`P4_Eliminates_AC.v`): для любого типа и любого разрешимого транзитивного отношения в непустом списке есть максимальный элемент — такой $m$, что всякий $n$ из списка, лежащий не ниже $m$, лежит и не выше $m$.',
  note: 'Новая теорема шага 4. Closed under the global context. Частный случай при Nat.leb — finite_zorn_nat_from_general.' });
a.add({ theorem: 'P4_cuts_completed_keeps_rule', file: AC, page_price: '0 аксиом',
  claim: '`P4_cuts_completed_keeps_rule` — для семейства непустых списков завершённое чтение графика всякой функции выбора несовместимо с P4, а чтение-правило совместимо.',
  note: 'Новая теорема шага 4. ' + CUT });
a.add({ theorem: 'ac_completed_graph_contradicts_P4', file: AC, page_price: '0 аксиом; при мосте',
  claim: '`ac_completed_graph_contradicts_P4` (всё рассуждение одной теоремой)',
  note: 'ac_completed_graph_contradicts_P4 (P4ProhibitsAC.v): из AC_on_nat, стадийной ограниченности и моста для графика функции выбора — противоречие. Closed under the global context.' });
a.add({ theorem: 'completed_graph_contradicts_P4', file: AC, page_price: '0 аксиом',
  claim: 'То же противоречие даёт график любой всюду определённой функции (`completed_graph_contradicts_P4`), а выбор из непустых списков как правило есть теорема (`AC_on_nat_as_rule`).',
  note: 'completed_graph_contradicts_P4 : forall f actual, P4_stage_bounded actual -> bridge (graph_indices (choice_graph f)) actual -> False. AC_on_nat_as_rule : AC_on_nat. Обе — Closed under the global context.' });
a.add({ theorem: 'bridge', file: CI,
  claim: 'Взять его разом, как готовый объект, значит считать все эти пары актуальными на одной стадии; в формализации это отдельная посылка — *мост* (`bridge`).',
  note: 'Definition bridge (S : nat -> Prop) (actual : nat -> nat -> Prop) := forall n, S n -> actual 0 n (P4CompletedInfinity.v).' });
a.add({ theorem: 'P4_prohibits_AC', file: AC, page_price: '0 аксиом',
  claim: '`P4_prohibits_AC` (сводка)',
  note: 'P4_prohibits_AC — конъюнкция трёх утверждений: ac_implies_completed; completed_inf_contradicts_P4 (при мосте); finite_choice_works. Противоречия из AC_on_nat она не выводит; страница называет её сводкой. Closed under the global context.' });
a.add({ theorem: 'P4_prohibits_three', file: PS, page_price: '0 аксиом',
  claim: '`P4ProhibitionSynthesis.v` собирает оба уровня в сводках `P4_prohibits_three`, `P4_preserves_three`, `P4_is_prohibition`;',
  note: 'P4_prohibits_three — сводная конъюнкция трёх теорем несовместимости (завершённая бесконечность при мосте; график выбора; расселова совокупность). Closed under the global context.' });
a.add({ theorem: 'P4_preserves_three', file: PS, page_price: '0 аксиом',
  claim: '`P4ProhibitionSynthesis.v` собирает оба уровня в сводках `P4_prohibits_three`, `P4_preserves_three`, `P4_is_prohibition`;',
  note: 'P4_preserves_three — сводная конъюнкция трёх сохранённых форм (потенциальная бесконечность; конечный выбор; стадийная ограниченность nat). Closed under the global context.' });
a.save();

const b = open('part04-ch01.json');
b.add({ theorem: 'completed_reading_strictly_stronger', file: AC,
  claim: 'Теоремой оно выражено в другом месте — для двух чтений графика функции: `completed_reading_strictly_stronger` (`P4ProhibitsAC.v`, Глава 10.4).',
  note: 'Фраза добавлена 13.11 (Часть X, шаг 4, слово автора). ' + STR });
b.save();
