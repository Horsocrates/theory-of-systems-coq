// Часть X, шаг 8, страницы (2026-11-13, слово автора «Да»): десять мест главы X.6 и два места страницы
// «Формализация» внесены. Таблица расхождений Части X закрыта.
// Запуск: node patch-p10-step-08-pages.cjs   (затем relocate + merge по part10-ch06 и двум ведомостям сверки)
// Скрипт повторяем: запись, уже приведённая к новым словам, пропускается.
const fs = require('fs');
const path = require('path');
const DONE = 'исправлено 13.11 (Часть X, шаг 8, слово автора)';
const S = 'src/settheory/';
const F = 'src/foundation/';
const norm = (s) => (s || '').replace(/\s+/g, ' ');
function open(name) {
  const p = path.join(__dirname, name);
  const j = JSON.parse(fs.readFileSync(p, 'utf8'));
  let n = 0, added = 0, dropped = 0;
  return {
    // th: undefined — любая запись; null — запись без теоремы; строка — запись с этой теоремой
    fix(prefix, th, fields, keepVerdict) {
      const hit = j.records.filter((r) => norm(r.claim).startsWith(prefix) &&
        (th === undefined || (th === null ? !r.theorem : r.theorem === th)));
      if (hit.length === 0) return;
      if (hit.length !== 1) throw new Error(name + ': ожидалась одна запись «' + prefix.slice(0, 50) + '» / ' + th + ', найдено ' + hit.length);
      Object.assign(hit[0], keepVerdict ? {} : { verdict: 'ok' }, fields); n++;
    },
    drop(prefix, th) {
      const before = j.records.length;
      j.records = j.records.filter((r) => !(norm(r.claim).startsWith(prefix) && r.theorem === th));
      dropped += before - j.records.length;
    },
    add(rec) {
      if (j.records.some((r) => r.theorem === rec.theorem && norm(r.claim) === norm(rec.claim))) return;
      j.records.push(Object.assign({ line: 0, page_price: '', verdict: 'ok', note: '' }, rec)); added++;
    },
    each(pred, fields) { for (const r of j.records) if (pred(r)) { Object.assign(r, fields); n++; } },
    save() { fs.writeFileSync(p, JSON.stringify(j, null, 1) + '\n'); console.log(name + ': изменено ' + n + ', добавлено ' + added + ', снято ' + dropped + ', всего ' + j.records.length); },
  };
}
const SBD = 'Schroeder_Bernstein_definite (SchroederBernstein_ERR.v): заключение из двух посылок — исключённого третьего и извлечения единственного свидетеля; Closed under the global context. Schroeder_Bernstein, cardinal_antisym — те же теоремы на двух аксиомах: classic + L4_witness.';
const REG = 'Реестр ChoicePriceMap.v переписан 13.11 и сверен с Print Assumptions построчно; ярусы: PZero, PL3, PL4, PL3_L4, PHorizon (не построено), PBoundary (запрещённый завершённый объект).';

const a = open('part10-ch06.json');
// ---- записи, закрытые шагами 1–7 без правки страницы
a.fix('Глава 10.3 свела сравнение мощностей к предпорядку вложений (Шрёдер–Бернштейн, Кантор) — без выбора.', 'Schroeder_Bernstein',
  { theorem: 'Schroeder_Bernstein_definite', file: 'src/SchroederBernstein_ERR.v', page_price: 'без выбора', note: 'закрыто 13.11 (Часть X, шаг 1): страница не менялась. ' + SBD });
a.fix('Содержательные теоремы выжили: Шрёдер–Бернштейн и общая теорема Кантора без выбора', 'Schroeder_Bernstein',
  { theorem: 'Schroeder_Bernstein_definite', file: 'src/SchroederBernstein_ERR.v', page_price: 'без выбора', note: 'закрыто 13.11 (Часть X, шаг 1): страница не менялась. ' + SBD });
a.fix('Доказуемое без выбора простирается до Шрёдера–Бернштейна, bool-варианта теоремы Кантора', null,
  { theorem: 'Schroeder_Bernstein_definite', file: 'src/SchroederBernstein_ERR.v', page_price: 'без выбора', note: 'закрыто 13.11 (Часть X, шаги 1 и 7): страница не менялась. ' + SBD + ' Кантор, Кантор — Бендиксон (производная, ядро при стабилизации), wqo — Closed under the global context.' });
a.fix('Все результаты Части X выстраиваются по *цене аксиом*.', 'price', { note: DONE + ': страница не менялась. ' + REG });
a.fix('импредикативная тотальность-в-себе (P1${}+{}$P4). Это не «пока не доказано», а', null,
  { theorem: 'russell_requires_completed_totality', file: F + 'P4ProhibitsImpredicative.v', note: 'закрыто 13.11 (Часть X, шаг 2): страница не менялась; теорема появилась. russell_collector_escapes, russell_needs_incomplete_range, russell_requires_completed_totality — Closed under the global context; запрет завершённой области — completed_inf_contradicts_P4, при условии bridge.' });
// ---- текст вокруг таблицы
a.fix('Это оформлено как разрешимая таблица: каждому результату сопоставлен ярус, и доказан итог', 'proven_results_below_boundary', { theorem: 'price', file: S + 'ChoicePriceMap.v',
  claim: 'Это оформлено как таблица-реестр: каждому результату сопоставлен ярус, сверенный с выводом `Print Assumptions` его теоремы.[^5]',
  note: DONE + ': было «доказан итог — ни один доказанный результат не требует полной аксиомы выбора» — тот итог был конъюнкцией десяти True по таблице. ' + REG });
a.fix('Главное наблюдение: содержательное ядро теории множеств — от счётности до Кантора–Бендиксона', null, { theorem: 'surjects_injects_back', file: S + 'CardinalityWithoutChoice.v',
  claim: 'Главное наблюдение: содержательное ядро теории множеств — от счётности до Кантора–Бендиксона и wqo — живёт на ярусе «0 аксиом». Выбор из многих свидетелей входит только там, где L4 берётся в полную силу: в мосте от сюръекции к вложению, в дихотомии замкнутых совокупностей, в играх с бесконечным числом ходов.',
  note: DONE + ': было «живёт на ярусах 0 / L3 / L3 + L4, и ни один доказанный результат не требует полной аксиомы выбора». Три места: surjects_injects_back (L4_witness), process_continuum_hypothesis и zermelo_determinacy (classic + L4_witness). Ещё одно место яруса L4 — unit_interval_uncountable_general (в таблице названо). l4_statement_gives_functional_choice — Closed.' });
a.fix('каждый результат несёт ярус (0 / L3 / L3${}+{}$L4), и доказано, что доказанное', 'proven_results_below_boundary', { theorem: 'price', file: S + 'ChoicePriceMap.v',
  claim: 'каждый результат несёт ярус (0 / L3 / L4 / L3${}+{}$L4), сверенный с компилятором; где входит выбор из многих свидетелей — названо.',
  note: DONE + ': было «и доказано, что доказанное не требует полной AC». ' + REG });
a.fix('обратный мост сюръекция${}\\to{}$инъекция (это сам выбор)', null, { page_price: 'не построено',
  claim: 'лемма Хигмана для алфавита из двух и более букв;',
  note: DONE + ': на этом месте списка «не привлечено» прежде стоял «обратный мост сюръекция → инъекция (это сам выбор)» — он доказан ценой L4_witness (surjects_injects_back) и перенесён в таблицу цен. Лемма Хигмана для двух и более букв в формализации не доказана (строка реестра RHigmanGeneralAlphabet, PHorizon).' });
a.fix('при разборе оказывается ZFC-*упаковкой*, а не стеной: содержание достигается', 'former_walls_are_artifacts', {
  claim: 'при разборе оказывается ZFC-*упаковкой*, а не стеной: для степени содержание достигается *без* завершённого объекта, для Крускала и Бореля без него построены нижние ступени.',
  note: DONE + ': было «содержание достигается без завершённого объекта» для всех трёх. FormerWallsLedger.status: WPowersetObject — ReachedFreely; WMinimalBadSequence и WBorelTower — PartiallyReached. former_walls_are_artifacts — свойство таблицы; Closed under the global context.' });
a.fix('(процессные формы полного Крускала и Мартина, мост выбора, линейность шкалы', null, {
  claim: '(процессные формы полного Крускала и Мартина, линейность шкалы — открыто)',
  note: DONE + ': из перечня открытого убран «мост выбора» — он доказан (surjects_injects_back, L4_witness). Теоремы о линейности порядка вложений в формализации нет.' });
a.fix('Теория множеств перестроена без аксиомы выбора и без завершённой бесконечности', null, { theorem: 'l4_statement_gives_functional_choice', file: S + 'ChoicePriceMap.v',
  claim: 'Теория множеств перестроена без аксиомы выбора как постулата и без завершённой бесконечности',
  note: DONE + ': было «без аксиомы выбора». Аксиома выбора не объявлена; но из записи L4_witness выбор по семейству следует (l4_statement_gives_functional_choice, Closed), и три результата берут L4 в полную силу — они названы в таблице цен.' });
a.fix('дихотомия Кантора–Бендиксона', 'process_continuum_hypothesis', { page_price: 'L3 и L4',
  claim: 'дихотомия замкнутых совокупностей (ценой L3 и L4)',
  note: DONE + ': было «дихотомия Кантора–Бендиксона» среди доказанного без выбора. process_continuum_hypothesis (ProcessContinuumHypothesis.v): Axioms: Classical_Prop.classic, ToS_Axioms.L4_witness.' });
// ---- сноски 5 и 7
a.fix('`AxiomPrice` (`PZero`/`PL3`/`PL3_L4`/`PBoundary`)', 'AxiomPrice', {
  claim: '`AxiomPrice` (`PZero`/`PL3`/`PL4`/`PL3_L4`/`PHorizon`/`PBoundary`)',
  note: DONE + ': было четыре конструктора из пяти. Inductive AxiomPrice := PZero | PL3 | PL4 | PL3_L4 | PHorizon | PBoundary (ChoicePriceMap.v, после шага 8).' });
const P5 = 'функция `price` и `proven_results_below_boundary` — строки реестра, не лежащие ниже границы, суть в точности пять: три непостроенные и две запрещённые.';
a.fix('функция `price`, и `proven_results_below_boundary` — каждый доказанный результат', 'price', { claim: P5 }, true);
a.fix('функция `price`, и `proven_results_below_boundary` — каждый доказанный результат', 'proven_results_below_boundary', { claim: P5,
  note: DONE + ': прежде лемма была конъюнкцией десяти True. Теперь: forall r, below_boundary (price r) <-> ~ In r [RFullKruskal; RBorelDeterminacy; RHigmanGeneralAlphabet; RPowerSetObject; RCompletedChoiceGraph]. Свойство таблицы; Closed under the global context.' });
a.fix('Это аудит-слой, фиксирующий сверенные `Print Assumptions` статусы, а не новая', undefined, {
  claim: 'Это аудит-слой: таблица записана рукой и сверена с `Print Assumptions` построчно; свойство таблицы — не теорема о результатах.' }, true);
a.fix('ровно завершённая бесконечность запрещена, три «стены» откатываются (`ReachedFreely`', null, {
  claim: 'ровно завершённая бесконечность запрещена, три «стены» откатываются: степень — полностью (`ReachedFreely`), Крускал и Борель — частично (`PartiallyReached`)',
  note: DONE + ': было «(ReachedFreely / NotYetBuilt)» — статус NotYetBuilt в таблице никому не присвоен; у двух стен стоит PartiallyReached.' });
// ---- строки таблицы цен
a.fix('несчётность $[0,1]$ (трисекция)', 'unit_interval_uncountable_trisect_v2', { claim: 'несчётность $[0,1]$ при заданной скорости сходимости (трисекция)' }, true);
a.fix('Кантор–Бендиксон; Крускал (конкретные семейства)', 'S_finite_scattered', { theorem: 'finite_set_scattered', file: S + 'CantorBendixsonFull.v',
  claim: 'Кантор–Бендиксон (производная, ядро при стабилизации, конечные множества)' }, true);
const ORD = 'ординалы — порядок построения, `wf_ord_below`, `structural_transfinite_ind` (сверено `Print Assumptions`: Closed)';
a.fix('ординалы, $\\varepsilon_0$, `wf_ord_lt`, `transfinite_ind` (сверено', 'wf_ord_lt', { theorem: 'wf_ord_below', file: F + 'OrdinalOrders.v', claim: ORD, page_price: '0 аксиом', note: DONE + ': было «wf_ord_lt, transfinite_ind» — прежнее отношение сравнивает только конечные обозначения (шаг 5). wf_ord_below — Closed under the global context.' }, true);
a.fix('ординалы, $\\varepsilon_0$, `wf_ord_lt`, `transfinite_ind` (сверено', 'transfinite_ind', { theorem: 'structural_transfinite_ind', file: F + 'OrdinalOrders.v', claim: ORD, page_price: '0 аксиом', note: DONE + '. structural_transfinite_ind — Closed under the global context.' }, true);
const P4C = 'переинтерпретации P4 — выбор-правило, ATR, Бесконечность, импредикативность, $\\Pi^1_1$';
const P4OLD = '`P4_Eliminates`/`Prohibits`-кластер — ATR, Бесконечность, импредикативность';
a.fix(P4OLD, 'P4_eliminates_ATR0', { claim: P4C }, true);
a.fix(P4OLD, 'P4_Eliminates', { theorem: 'P4_eliminates_Infinity', file: F + 'P4_Eliminates_Infinity.v', claim: P4C, page_price: '0 аксиом',
  note: DONE + ': было `P4_Eliminates` — часть имён файлов, не объявление. P4_eliminates_Infinity — Closed under the global context.' });
a.fix(P4OLD, 'Prohibits', { theorem: 'russell_requires_completed_totality', file: F + 'P4ProhibitsImpredicative.v', claim: P4C, page_price: '0 аксиом',
  note: DONE + ': было `Prohibits` — часть имён файлов, не объявление. russell_requires_completed_totality — Closed under the global context.' });
const PIOLD = '| 0 аксиом, для любой таблицы кодов | $\\Pi^1_1$-переинтерпретация';
a.fix(PIOLD, 'P4_eliminates_Pi11', { claim: P4C }, true);
a.drop(PIOLD, 'P4_forall_functions');
a.drop(PIOLD, 'eval_program');
const HIG = 'Хигман (однобуквенный алфавит) и лемма Диксона';
const CLOLD = '| classic (L3) | Хигман; конечная детерминированность |';
a.fix(CLOLD, 'higman_synthesis', { claim: HIG, page_price: '0 аксиом' }, true);
a.fix(CLOLD, 'higman_unit', { claim: HIG, page_price: '0 аксиом',
  note: DONE + ': прежде «Хигман» стоял в ярусе classic. higman_unit, dickson_pair, higman_synthesis — Closed under the global context (лемма Диксона доказана конструктивно, шаг 7).' });
a.fix(CLOLD, 'weak_determinacy', { claim: '| classic (L3) | `weak_determinacy`: у первого игрока выигрышная стратегия либо есть, либо её нет |', page_price: 'classic (L3)' }, true);
const L34OLD = '| classic ${}+{}$ L4 | Шрёдер–Бернштейн; антисимметрия мощностей';
const L34NEW = 'Шрёдер–Бернштейн и антисимметрия мощностей в записи на двух аксиомах (`cardinal_antisym`)';
a.fix(L34OLD, 'Schroeder_Bernstein', { claim: L34NEW }, true);
a.fix(L34OLD, 'cardinal_antisym', { claim: L34NEW }, true);
a.fix('завершённый актуально-бесконечный *объект* — единственный P4-запрет (вкл.', null, {
  claim: 'завершённый актуально-бесконечный *объект* — единственный P4-запрет: завершённый граф выбора и $\\mathcal{P}(\\mathbb{N})$ как Element (правило-ядро выбора у нас — L5)' }, true);
a.fix('процессные формы высоких теорем (полный wqo Крускала, борелевская детерминированность)', null, {
  claim: '| **Горизонт (`PHorizon`)** | не построено: полная теорема Крускала; борелевская детерминированность; лемма Хигмана для алфавита из двух и более букв |',
  note: DONE + ': «не построено» вынесено из строки «Граница» в отдельный ярус PHorizon (строки реестра RFullKruskal, RBorelDeterminacy, RHigmanGeneralAlphabet).' }, true);
// ---- новые записи о строках таблицы
a.add({ theorem: 'Schroeder_Bernstein_definite', file: 'src/SchroederBernstein_ERR.v', page_price: '0 аксиом',
  claim: 'Шрёдер–Бернштейн из исключённого третьего и единственного свидетеля, взятых посылками (`Schroeder_Bernstein_definite`)', note: SBD });
a.add({ theorem: 'finite_game_strategically_determined', file: F + 'FiniteGameDeterminacy.v', page_price: '0 аксиом',
  claim: 'детерминированность конечных деревьев игры', note: 'finite_game_strategically_determined — Closed under the global context (шаг 7).' });
a.add({ theorem: 'surjects_injects_back', file: S + 'CardinalityWithoutChoice.v', page_price: 'L4',
  claim: '| L4 | мост «сюръекция → вложение» (`surjects_injects_back`);', note: 'surjects_injects_back — Axioms: ToS_Axioms.L4_witness (шаг 1).' });
a.add({ theorem: 'unit_interval_uncountable_general', file: 'src/UnitIntervalUncountableGeneral.v', page_price: 'L4',
  claim: 'несчётность $[0,1]$ для произвольных сходящихся процессов без исключённого третьего', note: 'unit_interval_uncountable_general — Axioms: ToS_Axioms.L4_witness (шаг 3). С исключённым третьим и единственным свидетелем (посылками) — unit_interval_uncountable_general_definite, Closed.' });
a.add({ theorem: 'process_continuum_hypothesis', file: 'src/ProcessContinuumHypothesis.v', page_price: 'classic + L4',
  claim: 'дихотомия замкнутых совокупностей (`process_continuum_hypothesis`)', note: 'process_continuum_hypothesis — Axioms: Classical_Prop.classic, ToS_Axioms.L4_witness.' });
a.add({ theorem: 'zermelo_determinacy', file: S + 'ZermeloDeterminacy.v', page_price: 'classic + L4',
  claim: 'детерминированность игр конечной длины (`zermelo_determinacy`)', note: 'zermelo_determinacy — Axioms: BorelDeterminacy.classic, ToS_Axioms.L4_witness (шаг 7).' });
a.add({ theorem: 'l4_statement_gives_functional_choice', file: S + 'ChoicePriceMap.v', page_price: '0 аксиом (L4 — посылкой)',
  claim: 'Из самой записи L4 выбор по семейству следует (`l4_statement_gives_functional_choice`); карта это называет.',
  note: 'l4_statement_gives_functional_choice : L4_statement -> forall I X R, (forall i, exists x, R i x) -> exists f, forall i, R i (f i). Closed under the global context.' });
a.save();

// ------------------------------------------------------------------ сверка 12.11, глава X.6
const b = open('sverka-2026-11-12/X-6.json');
b.fix('| 0 аксиом | счётность ℚ (Калкин–Уилф); диагональ (`diagonal_differs`); несчёт', 'unit_interval_uncountable_trisect_v2', {
  claim: '| 0 аксиом | счётность ℚ (Калкин–Уилф); диагональ (`diagonal_differs`); несчётность $[0,1]$ при заданной скорости сходимости (трисекция)' }, true);
b.fix('Кантор–Бендиксон; Крускал (конкретные семейства)', 'kruskal_chains', { claim: 'Крускал (конкретные семейства)' }, true);
b.fix('общий Кантор $X\\to(X\\to\\mathtt{bool})$; Кантор–Бендиксон', 'S_finite_scattered', { theorem: 'finite_set_scattered', file: S + 'CantorBendixsonFull.v',
  claim: 'Кантор–Бендиксон (производная, ядро при стабилизации, конечные множества)' }, true);
b.fix(CLOLD, 'higman_synthesis', { claim: HIG, page_price: '0 аксиом',
  note: 'закрыто 13.11 (Часть X, шаги 7 и 8): лемма Диксона для пар доказана конструктивно, higman_synthesis — Closed under the global context; на странице «Хигман» перенесён в ярус «0 аксиом». Детерминированность: деревья игры — 0 аксиом (finite_game_strategically_determined), weak_determinacy — classic, zermelo_determinacy — classic + L4_witness; каждая стоит в своём ярусе таблицы.' });
b.save();

// ------------------------------------------------------------------ сверка 12.11, «Формализация»
const c = open('sverka-2026-11-12/Формализация.json');
c.each((r) => r.theorem === 'dickson_pair', { page_price: 'нет',
  note: 'С 13.11 (Часть X, шаг 7) dickson_pair доказана конструктивно — Closed under the global context; цена на странице исправлена («исключённое третье» → «нет») по слову автора (шаг 8).' });
c.add({ theorem: 'dickson_pair', file: S + 'HigmanLemma.v', page_price: 'нет',
  claim: '| Лемма Диксона для пар | `dickson_pair` (HigmanLemma.v) | нет |',
  note: 'Цена исправлена 13.11 (Часть X, шаг 8, слово автора): было «исключённое третье (стандартная библиотека)». С шага 7 dickson_pair доказана конструктивно — Closed under the global context.' });
c.add({ theorem: 'Schroeder_Bernstein_definite', file: 'src/SchroederBernstein_ERR.v', page_price: 'нет: оба принципа взяты посылками',
  claim: '| Та же теорема из исключённого третьего и извлечения единственного свидетеля, взятых посылками | `Schroeder_Bernstein_definite` (SchroederBernstein_ERR.v); `cardinal_antisym_definite` (CardinalityWithoutChoice.v) | нет: оба принципа взяты посылками |',
  note: 'Строка добавлена 13.11 (Часть X, шаг 8, слово автора). ' + SBD });
c.add({ theorem: 'cardinal_antisym_definite', file: S + 'CardinalityWithoutChoice.v', page_price: 'нет: оба принципа взяты посылками',
  claim: '`cardinal_antisym_definite` (CardinalityWithoutChoice.v) | нет: оба принципа взяты посылками |',
  note: 'cardinal_antisym_definite : ExcludedMiddle -> UniqueWitness -> forall A B, injects A B -> injects B A -> bijects A B. Closed under the global context.' });
c.save();
